# Hardware-Software Co-Verification of Masked Cores: Coco/CocoAlma, Coco-Ibex, OpenTitan AES/KMAC/OTBN, Switched-Capacitor Equalizers, and Randomized Clocking

## Summary

Masked software proved secure under an ISA-level $d$-probing model routinely leaks secrets at **first order** when executed on real microarchitectures because CPUs share physical datapaths, multiplexer trees, hidden pipeline registers, and memory buses across architecturally disjoint instructions and registers. Direct RTL inspection and exhaustive discrete probing demonstrate five concrete mechanisms where the ISA-to-netlist gap breaks masked software: (1) a standard binary-mux register file (`rf_reg[raddr]`) combines all 32 architectural registers inside a single combinational glitch fan-in cone ($I(s; \mathrm{cone}) = 1.000000\text{ bit}$); (2) consecutive reads of two shares on a shared read port or compiler register reuse create Hamming-distance transition leakage $\mathrm{HD}(s_0, s_1) = \mathrm{HW}(s)$ ($I = 1.000000\text{ bit}$); (3) hidden Load-Store Unit registers (`rdata_q` in unhardened Ibex) retain stale shares across loads ($I = 1.000000\text{ bit}$); (4) unblanked ALU/shifter/multiplier inputs switch on every instruction even when their outputs are discarded; and (5) even in a hardened RAM (`ram_1p_secure.v`), placing two shares at the same in-block offset across distinct blocks leaks $I = 1.000000\text{ bit}$ through the combinational inter-block multiplexer tree.

Closing this gap requires **hardware-software co-design paired with execution-aware gate-level co-verification**:

1. **Coco and CocoAlma (`isec-tugraz/coco-alma`, USENIX Security 2021 & FMCAD 2021)** formally verify concrete masked assembly binaries directly against synthesized CPU gate-level netlists under both **glitch** and **transition** probing. By simulating the assembly execution in Verilator to obtain a concrete VCD control trace and propagating per-cycle signal stability (`SatChecker.py:__make_stability_info`), CocoAlma eliminates the false positives of control-unaware static netlist verifiers (such as REBECCA) while proving first- and higher-order security (via CaDiCaL/Kissat SAT) over multi-hundred-thousand-gate cores.
2. **Coco-Ibex (`isec-tugraz/coco-ibex`)** eliminates eight microarchitectural leakage sources in the 32-bit RISC-V Ibex core at ~9.9% core area overhead (`20.2 kGE -> 22.2 kGE`, excluding SRAM) by pre-decoding and registering glitch-free one-hot read/write enables in the IF stage (`REGREAD_SECURE`, `REGWRITE_SECURE`), gating ALU adder/shifter, multiplier/divider, and CSR inputs (`ADDER_SECURE`, `SHIFT_SECURE`, `MD_SECURE`, `CSR_SECURE`), unconditionally clearing hidden LSU `rdata_q`, and replacing flat SRAM with one-hot in-block gated `ram_1p_secure.v` (`MEM_SECURE`). Crucially, hardware hardening does **not** free software or compilers from share-disjoint register allocation, neutral separation cycles, and distinct in-block memory offsets.
3. **OpenTitan (`lowRISC/opentitan`)** applies a hybrid silicon architecture: dedicated **DOM-masked hardware crypto cores** for AES (`SecSBoxImpl = SBoxImplDom`, 5-cycle DOM-dep S-box, 28 PRD bits, PRNG register clearing) and KMAC/SHA-3 (`keccak_2share.sv`, 2-phase split + 5 pipelined `prim_dom_and_2share` half-sheets); **blanking-hardened bignum processor OTBN** (`otbn_predecode.sv` prefetch pre-decoding driving flopped `prim_blanker` gates per WDR write path, `prim_onehot_mux` read ports, redundant decode checks, ALU/MAC datapath blanking, Secure Wipe, and a Masking Accelerator Interface verified in-tree with **both CocoAlma and PROLEAD**); and an explicit architectural boundary warning that **OTBN's 32-bit base register file (`x1..x31`) has NO blanking** and upstream **`SecureIbex`** provides timing/fault hardening (`DataIndTiming`, `DummyInstructions`, `RegFileECC`) rather than Coco-Ibex's share-isolation gating.
4. **Analog and clock-domain hiding countermeasures**—**switched-capacitor current equalizers** (Tokunaga & Blaauw, IEEE JSSC 2010: `7.2%` area, `33%` power, `2x` performance penalty, `>10M` MTD on the supply pin) and **randomized clocking** (OpenTitan `clkmgr.jitter_en_o`, Güneysu & Moradi CHES 2011)—cannot substitute for masking and netlist co-verification. SC-CEs attenuate *external supply-pin* leakage exponentially in the discharge ratio $k = T_{\text{dis}} / (R_{\text{on}} C)$ (`8.69 dB` at $1\tau$ to `173.72 dB` at $20\tau$) yet leave **local on-die EM current signatures completely unattenuated (`0 dB`)**, while randomized clocking collapses under landmark/elastic alignment (van Woudenberg et al., CT-RSA 2011: at $J = 16$ samples jitter and $N = 1000$ traces/class, naive unaligned TVLA shows `|t| = 2.86` below the `4.5` threshold, whereas landmark alignment immediately recovers **`|t| = 12.40`** with zero extra traces).

## Applicability

This report characterizes hardware-software co-verification of masked software on embedded RISC-V cores, production silicon Root-of-Trust SCA architectures, and analog/clock-domain hiding limits across the pinned upstream repositories and peer-reviewed specifications listed in `REPORT.json`:

- **Co-verification tool and hardened RISC-V research core:** `isec-tugraz/coco-alma` (`95c80df5d6d704bf525f47ef6e58e98e27fedf97`) and `isec-tugraz/coco-ibex` (`1ac262929d900d63d5ed702cd40edca1602a79c9`, forked from Ibex commit `863fb56eb166d`), together with Gigerl et al. (USENIX Security 2021, ePrint `2020/1294`) and Hadžić and Bloem (FMCAD 2021, DOI `10.34727/2021/isbn.978-3-85448-046-4_9`).
- **Production silicon Root of Trust and upstream Ibex core:** `lowRISC/opentitan` (`1e061997389b1c257043b0dbd2388a19a6c2f6f1` — specifically `hw/ip/aes/`, `hw/ip/kmac/`, `hw/ip/otbn/`, `hw/ip/prim/`, and `hw/top_earlgrey/ip_autogen/clkmgr/`) and `lowRISC/ibex` (`9b91b3a1195aecb0d80cf2de5b852e0b5f68cc6c`), plus OpenTitan's in-tree PROLEAD integration targeting `ChairImpSec/PROLEAD` (`2c8c8486d84f58b121b7198fc267ce520d29d39a`).
- **Software-leakage and analog/clock hiding literature:** Papagiannopoulos and Veshchikov (COSADE 2017, ePrint `2017/345`), Shelton et al. (Rosita, NDSS 2021, DOI `10.14722/ndss.2021.23137`), Tokunaga and Blaauw (IEEE JSSC 2010, DOI `10.1109/JSSC.2009.2034081`), Güneysu and Moradi (CHES 2011, DOI `10.1007/978-3-642-23951-9_3`), and van Woudenberg, Witteman, and Bakker (CT-RSA 2011, DOI `10.1007/978-3-642-19074-2_8`).

**Scope and target architecture constraints:** CocoAlma's formal guarantee applies to **data-independent control-flow masked execution** (i.e., branch decisions, memory addresses, and opcode streams are independent of secret shares, so one concrete VCD simulation captures the exact control-signal schedule for all secret inputs). The co-design patterns apply primarily to in-order, deterministic-pipeline microcontrollers and cryptographic co-processors (2-stage Ibex, 1-cycle-execute + prefetch OTBN); out-of-order speculative superscalar cores with shared caches, dynamic register renaming, and branch predictors fall outside CocoAlma's deterministic-trace assumption.

## Findings

### 1. Why ISA-Level Masked Software Proofs Break on Physical CPU Microarchitectures

`Basis: normative + source + execution`

Software masking verifiers operating at C, LLVM IR, or ISA assembly level (e.g., `maskVerif`, `Tornado`, `scverif`) prove that no combination of up to $d$ architectural register values or instruction outputs reveals secret shares. Empirical silicon measurements on ARM Cortex-M and AVR cores (Papagiannopoulos and Veshchikov, COSADE 2017, ePrint `2017/345`; Shelton et al., `Rosita`, NDSS 2021, DOI `10.14722/ndss.2021.23137`) and gate-level analysis on RISC-V Ibex (Gigerl et al., USENIX Security 2021, ePrint `2020/1294`) establish that ISA-verified masked assembly breaks at **first order** via six microarchitectural leakage channels invisible at the ISA boundary:

1. **Register-file read multiplexer fan-in and address-transition glitches:** A standard Verilog register file `assign rdata_a_o = rf_reg[raddr_a_i];` (`coco-ibex/rtl/ibex_register_file_ff.sv:101`) synthesizes into a 32-to-1 combinational binary MUX tree. Every architectural register `rf_reg[1..31]` lies inside the combinational fan-in cone of `rdata_a_o`, and skewed transitions on `raddr_a_i` (e.g., `x1` `00001` $\to$ `x2` `00010` passing transiently through `00000` or `00011`) glitch across multiple registers simultaneously. Even if two shares $s_0, s_1$ never appear in the same instruction, a single glitch probe on `rdata_a_o` observes $(s_0, s_1)$ ($I = 1.000000\text{ bit}$, Sub-probe 2A).
2. **Temporal Hamming-distance transitions on shared buses and overwritten registers:**
   - Reading `x1` ($s_0$) on port `A` in cycle $t$ and `x2` ($s_1$) on port `A` in cycle $t+1$ drives `rdata_a_o` from $s_0$ to $s_1$, leaking $\mathrm{HD}(s_0, s_1) = \mathrm{HW}(s_0 \oplus s_1) = \mathrm{HW}(s)$ (`1.000000 bit`, Sub-probe 2A) even with glitch-free one-hot read gating!
   - If a compiler's register allocator reuses physical register `x1` (currently holding $s_0$) to store $s_1$, the flip-flop bank transitions $s_0 \to s_1$ (`1.000000 bit`, Sub-probe 2A).
3. **Hidden pipeline, forwarding, and Load-Store Unit (`LSU`) registers:** In unhardened Ibex, the LSU retains upper bytes of previously loaded words in `rdata_q[31:8]` (`ibex_load_store_unit.sv:80, 194`) to assemble misaligned loads. Loading share $s_0$ followed by share $s_1$ overwrites `rdata_q` from $s_0 \to s_1$ (`1.000000 bit`, Sub-probe 2A) even when software stores the two shares in completely disjoint architectural registers!
4. **Unblanked ALU sub-units (adder, barrel shifter, multiplier/divider, CSR):** In standard RISC-V datapaths, `operand_a_i` and `operand_b_i` fan out unconditionally into the carry-propagate adder, barrel shifter, multiplier/divider, and CSR logic simultaneously; an output MUX selects the active result while unused units still toggle on secret operands and combine previous-cycle stale inputs with current-cycle operands.
5. **Memory/SRAM shared read/write multiplexers and bus precharging:** Loading or storing shares through a single-port SRAM combines words across bitlines, column multiplexers, or output registers.
6. **Optimizing compiler transformations:** Standard `clang`/`gcc`/`rustc` passes (common subexpression elimination, register coalescing, instruction scheduling placing share-0 and share-1 loads back-to-back, and stack-spill slot reuse) violate share separation even if source code was carefully masked—explaining why `Rosita` (NDSS 2021) requires iterative empirical leakage-guided assembly rewriting and why Coco verifies the **final assembled machine-code binary** executing on the gate-level netlist.

---

### 2. Coco and CocoAlma: Execution-Aware Gate-Level Co-Verification Architecture

`Basis: normative + source + execution`

`isec-tugraz/coco-alma` (`95c80df5d6d704bf525f47ef6e58e98e27fedf97`; Hadžić and Bloem, FMCAD 2021, DOI `10.34727/2021/isbn.978-3-85448-046-4_9`; Gigerl et al., USENIX Security 2021, ePrint `2020/1294`) bridges the gap between software assembly and gate-level hardware by verifying the **joint execution** of a concrete masked program on a synthesized CPU netlist across a 4-stage pipeline (`coco-alma/readme.md:67–231`):

1. **Stage 1 — Synthesis & Parsing (`parse.py`):** Invokes Yosys ($\ge 0.15$, with `sv2v` for SystemVerilog frontends such as OpenTitan OTBN) to synthesize the CPU/accelerator RTL into a gate-level Verilog netlist (`circuit.v`), JSON graph (`circuit.json`), and a bit-level port/register label template (`labels.txt`).
2. **Stage 2 — Secret & Randomness Labeling (`labels.txt`):** Annotates individual register/RAM/port bits (`readme.md:108–145`) as:
   - `secret <id>` (identifying multiple bit-level shares of the same secret index);
   - `static_random` (single fresh random bit initialized at cycle 0, e.g., initial register/RAM mask);
   - `volatile_random` (fresh random bit supplied on *every* clock cycle, modeling a streaming RNG/PRNG port);
   - `unimportant` (public control/data/constants).
3. **Stage 3 — Concrete Control-Trace Simulation (`trace.py`):** Compiles the Yosys netlist with a Verilator testbench loading the target masked assembly binary into IMEM/DMEM and records a full cycle-by-cycle VCD waveform (`circuit.vcd`). Under data-independent control flow, all public control signals (PC, instruction words, decoded MUX selects, write enables, branch conditions) are concrete and deterministic in the VCD trace.
4. **Stage 4 — SAT-Based Probing Verification (`verify.py`, `SatChecker.py`):** Builds a propositional correlation formula over the unrolled cycle-by-cycle netlist and checks satisfiability via `CaDiCaL` (in-process) or exported DIMACS CNF with `Kissat` (`--export-cnf --kissat`).

#### Exact Verification Semantics in `SatChecker.py` (`isec-tugraz/coco-alma`)

Direct inspection of `SatChecker.py:13–620, 944–1070` establishes four key mechanisms that distinguish CocoAlma from pure-hardware tools like REBECCA:

- **Three tracked symbolic correlation sets per cycle (`SatChecker.py:16–18`):**
  1. `node_vars_stable[t][n]`: steady-state linear/nonlinear correlation set of node $n$ at cycle $t$.
  2. `node_vars_trans[t][n]`: glitch-and-transition-extended correlation set (`--mode transient`).
  3. `node_vars_diff[t][n]`: explicit Hamming-distance transition XOR `prev_stable[n] ^ curr_stable[n]` (`__build_hamming`, lines 603–612).
- **Execution-aware signal stability propagation (`__make_stability_info`, lines 477–513):**
  - A node is initially marked `stable` iff its concrete VCD value is binary (`0` or `1`) and unchanged from cycle $t-1$ (`prev_val == curr_val`).
  - For combinational gates, `XOR`/`XNOR`/`NOT` (and `AND == 1`, `OR == 0`) are stable iff **all** predecessors are stable. Crucially, for **controlling values** (`AND == 0`, `OR == 1`, lines 494–499), the gate output is stable iff **at least one controlling predecessor is stable**! This is the exact formal rule that proves `prim_blanker` (`data & en_q` with flopped `en_q == 0`) blocks combinational glitches from propagating out of `data`!
  - For a `MUX` (lines 408–423, 500–513), if the concrete `select` signal is public (not in `all_stable_nodes`) **and** `stability[select] == True`, `__proc_mux` propagates **only** the selected input `mux_ins[int(value)]`! If `select` toggles (`prev_val != curr_val`), `stability[select]` becomes `False`, triggering `__make_mux_sel_not_stable` which conservatively combines *both* `mux_ins[0]` and `mux_ins[1]`—immediately catching transition glitches across MUX switches (reproduced in Sub-probe 2B!).
- **Register transition modeling (`__proc_trans_reg`, lines 453–470):** In `--probing-model time-constrained` (default), a register node $r$ transitions from `prev_stable[r]` to `curr_stable[r]`, combining both cycles via `make_simple(AND_TYPE, prev[r], curr[r])` (strict mode) or `make_choice(prev[r], curr[r])` (loose mode), directly catching register-overwrite Hamming-distance leaks `HD(s0, s1)`.
- **`time-constrained` vs. `classic` probing models and `per-location` vs. `per-secret` checking (`readme.md:217–221`, `SatChecker.py:944–1070`):**
  - In `time-constrained` probing, each of the $d$ probes observes a single gate in a **single clock cycle** (matching transient physical power peaks); in `classic` probing, a probe records a wire's entire execution trace across all cycles.
  - `per-location` builds one formula per potentially leaking probe location (faster for first-order verification on huge CPU netlists such as OTBN's 234,238-node graph); `per-secret` builds one formula per secret (faster for higher-order $d \ge 2$).

---

### 3. Coco-Ibex Co-Design: Microarchitectural Hardening and Software/Memory Contracts

`Basis: source + documentation + execution`

Gigerl et al. (USENIX Security 2021, ePrint `2020/1294`) co-designed **`isec-tugraz/coco-ibex`** (`1ac262929d900d63d5ed702cd40edca1602a79c9`, based on lowRISC Ibex commit `863fb56eb166d`) by iteratively running Coco against masked RISC-V cryptographic gadgets (e.g., DOM/ISW Keccak, AES, Ascon) and fixing every hardware leak exposed by the SAT counterexample traces. Total reported area overhead is **~9.9%** (`20.2 kGE -> 22.2 kGE`, excluding SRAM).

#### Complete Inventory of Coco-Ibex Hardware Fixes (`rtl/secure.sv` & RTL Modules)

| Control Macro / Fix | Pinned Source Location | Microarchitectural Leakage Fixed | Exact RTL Mechanism |
| :--- | :--- | :--- | :--- |
| **`REGREAD_SECURE`** | `rtl/ibex_if_stage.sv:251–289`, `rtl/ibex_register_file_ff.sv:26–39, 88–99` | Binary MUX tree combining all 31 registers in one glitch cone | Pre-decodes 32-bit one-hot `rf_read_enable_a/b` in IF stage (including compressed instructions), registers across IF/ID, and gates `rdata_a_o[b] = OR_r (rf_reg[r][b] & read_enable_a_i[r])` |
| **`REGWRITE_SECURE`** | `rtl/ibex_if_stage.sv:259`, `rtl/ibex_register_file_ff.sv:42–44, 70–75` | Write-data fan-out and glitching into unselected register write ports | Registers one-hot `write_enable_secure_i[31:0]` in IF stage; AND-gates `wdata_a_i[b] & write_enable_secure_i[r]` per register |
| **`ADDER_SECURE`** | `rtl/ibex_if_stage.sv:274`, `rtl/ibex_alu.sv:26–28, 79–90` | Adder carry-chain glitches combining operands during non-add instructions | Flopped `adder_enable_i` AND-gates `adder_in_a` (`operand_a_i & {32{adder_enable_i}}`) and `adder_in_b` |
| **`SHIFT_SECURE`** | `rtl/ibex_if_stage.sv:269`, `rtl/ibex_alu.sv:23–25, 189–193, 257–267` | Barrel shifter cross-bit mixing of shares during non-shift instructions | Flopped `shift_enable_i` AND-gates `shift_operand_a/b` and `operand_a_rev` |
| **`MD_SECURE`** | `rtl/ibex_if_stage.sv:264`, `rtl/ibex_ex_block.sv`, `rtl/ibex_multdiv_*.sv` | Multiplier/divider combinational tree mixing operands when inactive | Flopped `md_enable` gates multiplier/divider inputs |
| **`CSR_SECURE`** | `rtl/ibex_if_stage.sv:279`, `rtl/ibex_cs_registers.sv` | CSR read/write path exposing stale operands | Flopped `csr_enable` gates CSR datapath |
| **Unconditional LSU Clear** | `rtl/ibex_load_store_unit.sv:190–198` (`README.md:28`) | Hidden misaligned-load register `rdata_q[31:8]` retaining prior loaded share | Unconditionally executes `rdata_q <= 0;` whenever `rdata_update` is inactive (no disable macro) |
| **`MEM_SECURE`** | `shared/rtl/ram_1p_secure.v:1–218` | SRAM read/write muxing combining shares stored in adjacent memory words | Hierarchical $2^b$ blocks $\times$ $2^a$ words (`a=3, b=4` default) with registered one-hot `OH_in_reg` in-block AND-OR read/write gating + registered `inter_block_addr_reg` mux tree |

#### Subtle RTL-to-Software Contract Discovered in `ram_1p_secure.v`

`Basis: source + execution`

Direct inspection of `isec-tugraz/coco-ibex/shared/rtl/ram_1p_secure.v:103–155` exposes a critical memory-layout constraint that software and linkers MUST obey on Coco-Ibex:
- On every rising clock edge, lines 109–117 compute `rdata_OR[blk]` for **all** $2^b = 16$ blocks using the **single shared in-block one-hot mask `OH_in_reg`**:
  ```verilog
  rdata_OR_tmp = rdata_OR_tmp | (mem[read_mem_block_id][read_mem_id] & {32{OH_in_reg[read_mem_id]}} & {32{~we}});
  ```
- Lines 133–154 then select one block's `rdata_OR[blk]` via a **combinational binary multiplexer tree** controlled by `inter_block_addr_reg`.
- **Consequence (verified in Sub-probe 2A):**
  - If share $s_0$ is placed at `(block=0, offset=2)` and share $s_1$ is placed at `(block=1, offset=2)` (**same in-block offset** `addr[4:2]`, different blocks), reading `(block=0, offset=2)` sets `OH_in_reg[2] = 1` across **every** block simultaneously, loading `rdata_OR[0] = s0` AND `rdata_OR[1] = s1` into the same combinational inter-block MUX tree—leaking **`I(s; mux_cone) = 1.000000 bit`** under glitches!
  - If shares of the same secret are placed at **distinct in-block offsets** (e.g., `(block=0, offset=2)` and `(block=0, offset=3)`), `OH_in_reg` activates only one share's offset and forces the other share's word to `0` across all blocks—reducing leakage to **`0.000000` bits**.

#### Mandatory Software & Compiler Co-Design Constraints on Hardened Cores

Even with all eight Coco-Ibex hardware mitigations active, masked software remains insecure unless the compiler/assembler enforces four invariants (all confirmed by Sub-probe 2A):
1. **Share-disjoint architectural register allocation:** Never overwrite a register holding share $s_i$ with share $s_j$ ($j \neq i$) without first zeroing/randomizing the register (`HD(s0, s1) = 1.000000 bit`).
2. **Non-consecutive share reads on the same register-file port (or neutral/blanked intervening cycles):** Back-to-back reads of $s_0$ then $s_1$ on `rdata_a_o` create a transition leak (`1.000000 bit`) unless an intervening instruction blanks the port (`en = 0`) or reads a public/random register (`0.000000` bits).
3. **Memory share-offset separation (`ram_1p_secure`):** Shares of the same secret must occupy distinct in-block offsets (`addr[a+1:2]`).
4. **No secret-combining compiler optimizations:** Common subexpression elimination, register coalescing, instruction rescheduling across blanking NOPs, and shared stack-spill slots must be disabled or formally re-verified post-compilation on the final binary via CocoAlma.

---

### 4. OpenTitan Hardened Silicon Architecture: AES, KMAC, OTBN, and Upstream `SecureIbex`

`Basis: source + documentation`

Direct inspection of `lowRISC/opentitan` (`1e061997389b1c257043b0dbd2388a19a6c2f6f1`) and `lowRISC/ibex` (`9b91b3a1195aecb0d80cf2de5b852e0b5f68cc6c`) shows how a production open-source silicon Root of Trust combines **hardware-masked symmetric accelerators**, a **blanking-hardened asymmetric/bignum co-processor (OTBN)**, and a **timing/fault-hardened control CPU (`SecureIbex`)**:

#### A. OpenTitan AES (`hw/ip/aes/`)
- **First-order DOM masking (`aes_cipher_core.sv:99–105`, `aes_sbox_dom.sv:5–50`):** Enabled by default (`SecMasking = 1`, `SecSBoxImpl = SBoxImplDom`, `NumShares = 2`). Uses 16 DOM-dep S-boxes for `SubBytes` and 4 for `KeyExpand` (5-cycle latency, 28 PRD bits/evaluation, verified in transient mode using CocoAlma per `aes_sbox_dom.sv:23–29`), taking `56/66/72` cycles per block in AES-128/192/256 (`aes/doc/theory_of_operation.md:313`).
- **PRNG register clearing (`aes_cipher_core.sv:139–140, 249–253`, `aes_prng_clearing.sv`):** To eliminate Hamming-distance transitions between consecutive cipher blocks or keys, `STATE_CLEAR` overwrites internal state and key registers with fresh pseudo-random data (`prd_clearing_state_i`, `prd_clearing_key_i`) rather than zeros, and `KEY_TOUCH_FORCES_RESEED` forces EDN reseeding on sideload key changes (`aes/doc/theory_of_operation.md:281`).

#### B. OpenTitan KMAC / SHA-3 (`hw/ip/kmac/rtl/keccak_2share.sv`)
- **Two-stage glitch-isolated Keccak round (`keccak_2share.sv:102–259`):** When `EnMasking = 1` (`Share = 2`), each round splits into a **linear stage** (`phase1_in`/`phase1_out`: $\theta, \rho, \pi$ computed independently on both shares and latched back into the 1600-bit dual-share state register) and a **nonlinear stage** (`phase2_in`/`phase2_out`: $\chi$ executed over 3 clock cycles using 5 half-sheet `prim_dom_and_2share #(.DW(WSheetHalf), .Pipeline(1))` multipliers, followed by $\iota$ XORing round constants onto share 0 only, lines 139–141).
- **Randomness reuse vs. `ForceRandExt` (`keccak_2share.sv:23–25, 227–239`):** By default (`ForceRandExt = 0`), the upper half-sheet reuses rotated reshared DOM intermediates `out_prd[rot_int(x, 5)]` from non-adjacent rows (which do not share inputs with row $x, x+1, x+2$) to cut PRNG bandwidth; setting `ForceRandExt = 1` forces fresh external entropy on every half-sheet.

#### C. OpenTitan OTBN (OpenTitan Big Number Accelerator, `hw/ip/otbn/`)
Unlike AES/KMAC, OTBN is a **programmable 256-bit bignum processor** running software asymmetric/PQC cryptography (RSA, ECDSA, Dilithium/ML-DSA, Kyber/ML-KEM). Rather than masking the entire 256-bit multiplier/ALU in hardware, OTBN implements **systematic Coco-style pre-decoded blanking + register-file isolation + a dedicated hardware Masking Accelerator Interface (MAI)**:
1. **Prefetch Pre-Decoding and Glitch-Free Blanking (`hw/ip/otbn/README.md:1264–1283`, `otbn_predecode.sv`, `prim_blanker.sv`):**
   - OTBN inserts a non-speculative **instruction prefetch stage** (`otbn/doc/theory_of_operation.md:49–53`) that pre-decodes one-hot register enables (`rf_bignum_predec_i.{rf_ren_a, rf_ren_b, rf_we}`) and datapath enables into **flip-flops**, guaranteeing glitch-free control signals when the instruction enters execution.
   - The execution stage performs a **redundant full decode** (`otbn_rf_bignum.sv:131–136`, `SEC_CM: CTRL.REDUN`); any mismatch raises a fatal `BAD_INTERNAL_STATE` error (preventing fault-induced blanking bypass).
   - Every blanker wraps `prim_and2` (`prim_blanker.sv:8–20`), forcing disabled paths to `0` across synthesis boundaries.
2. **Wide Register File (`otbn_rf_bignum.sv:26–193`, `otbn_rf_bignum_ff.sv:18–144`):**
   - Stores 32 × 312-bit (`ExtWLEN`) registers (256-bit data + 8 × 7-bit inverted `(39,32)` Hsiao SECDED integrity bits, Hamming distance 4).
   - **Per-register write blanking (`otbn_rf_bignum_ff.sv:49–53`):** Instantiates **32 separate 312-bit `prim_blanker` modules** (one per WDR, *not* a single shared input blanker) gated by `rf_bignum_predec_i.rf_we[i]`, backed by SVA `BlankingBignumRegWData_A` (line 68) and `prim_onehot_check` spurious-WE glitch detection (`lines 116–129`).
   - **Two-level one-hot read muxes (`otbn_rf_bignum_ff.sv:71–92`):** Uses `prim_onehot_mux` on both read ports with formal SVAs `BlankingBignumRegReadA_A`/`B_A` (`otbn_rf_bignum.sv:181–187`) proving `rd_data_a/b_intg_o == '0` whenever `!rd_en_a/b_i`.
3. **Bignum ALU and MAC Datapath Blanking (`otbn_alu_bignum.sv`, `otbn_mac_bignum.sv`):**
   - `otbn_alu_bignum.sv` instantiates dedicated `prim_blanker` cells on `adder_x_op_a/b`, `adder_y_op_a/shifter`, `logical_op_a/shifter_res`, `vec_transposer_op_a/b`, `unpack_input`, and ISPR/keymgr write paths (`lines 673–1514`).
   - `otbn_mac_bignum.sv` blanks `operand_a`, `operand_b`, `mod`, `half_mul_res`, `mul_res_merger`, `mul_res_shift`, `reg_c`, and `acc_add` (`lines 271–451`).
4. **Critical Unblanked Base-Side Boundary (`hw/ip/otbn/README.md:1283`):**
   - OpenTitan explicitly documents: *"Note there is no blanking on the base side (save for the CSRs as these provide access to WDRs such as ACC)."* Consequently, **masked OTBN assembly MUST never place secret shares in the 32-bit base register file (`x1..x31`)**; all secret shares must stay strictly in `w0..w31` / WSRs.
5. **Two-Step Secure Wipe & Masking Accelerator Interface (`otbn/doc/theory_of_operation.md:625–696, 941–1011`):**
   - DMEM and IMEM secure wipes rotate their memory scrambling keys; internal-state secure wipe overwrites all WDRs, base GPRs, `MOD`, `ACC`, and WSRs in two steps (first with URND randomness, then zeros/valid ECC).
   - The **Masking Accelerator Interface (MAI)** offloads side-channel-critical masked primitives (e.g., `mask_acc_b2a` Boolean-to-Arithmetic conversion) to a heavily pipelined first-order masked + shuffled hardware accelerator accessed via `MAI_INx_Sy` / `MAI_RES_S0..S1` WSRs.
6. **In-Tree Formal & Statistical Pre-Silicon Co-Verification (`hw/ip/otbn/pre_sca/{alma,prolead}/README.md`):**
   - OpenTitan integrates **both** **CocoAlma** (on the full 234,238-node synthesized `otbn_top_coco` netlist: `22,351` linear, `107,502` nonlinear, `21,338` registers, `41,352` muxes, catching real masked-assembly leaks in `34.31 s` at cycle 3!) and **PROLEAD** (evaluating MAI gadgets like `mask_acc_b2a` under robust probing!).

#### D. Architectural Comparison: Upstream `SecureIbex` vs. `Coco-Ibex` vs. OpenTitan `OTBN`

| Hardening Mechanism | `lowRISC/ibex` (`SecureIbex=1`) | `isec-tugraz/coco-ibex` | `lowRISC/opentitan` `OTBN` (Bignum Side) |
| :--- | :---: | :---: | :---: |
| **Data-independent timing (`DataIndTiming`)** | Yes (`ibex_core.sv:195`) | Inherited (basic RV32IM) | Yes (fixed-cycle bignum ISA) |
| **LFSR dummy instructions (`DummyInstructions`)** | Yes (`ibex_dummy_instr.sv:12–158`: `ADD`/`MUL`/`DIV`/`AND` to `x0`) | No | No (uses blanking + SW masking + MAI) |
| **Registered one-hot RF read gating** | **No** (binary MUX) | **Yes** (`REGREAD_SECURE`) | **Yes** (`prim_onehot_mux`, bignum WDRs only) |
| **Per-register RF write-data blanking** | **No** | **Yes** (`REGWRITE_SECURE`) | **Yes** (32 × 312b `prim_blanker`, WDRs only) |
| **ALU/Shifter/MAC input blanking** | **No** | **Yes** (`ADDER`/`SHIFT`/`MD`/`CSR_SECURE`) | **Yes** (`otbn_alu_bignum.sv`, `otbn_mac_bignum.sv`) |
| **Hidden LSU/pipeline clearing** | **No** | **Yes** (`rdata_q <= 0`) | Dedicated bignum load/store + Secure Wipe |
| **SECDED ECC / Glitch FI Detection** | Yes (`RegFileECC`, `PCIncrCheck`, lockstep) | No | Yes (`(39,32)` Hsiao ECC, `CTRL.REDUN`, `prim_onehot_check`) |
| **Formally verified for glitch-safe masked SW** | **No** (timing/FI focus, not share-isolated) | **Yes** (CocoAlma transient) | **Yes** (bignum side via CocoAlma; MAI via CocoAlma + PROLEAD) |

**Engineering takeaway:** Enabling `SecureIbex = 1` on upstream `lowRISC/ibex` does **not** make Ibex safe for masked software! Its `ibex_dummy_instr.sv` injects random `ADD`/`MUL`/`DIV`/`AND` instructions targeting `rd = x0` (lines 38–43, 152) to obfuscate control/power traces (hiding), while its register file and ALU retain unblanked binary MUXes and shared operand paths.

---

### 5. Analog and Clock-Domain Hiding: Switched-Capacitor Current Equalizers and Randomized Clocking

`Basis: normative + source + derived + execution`

Because masking multiplies area/randomness and co-verification constrains software, hardware designers frequently evaluate circuit-level **hiding** countermeasures—specifically **Switched-Capacitor Current Equalizers (SC-CE)** and **Randomized Clocking / Clock Jitter**. Both obey sharp physical boundaries that prevent them from replacing provable masking.

#### A. Switched-Capacitor Current Equalizers (Tokunaga and Blaauw, IEEE JSSC 2010)

Tokunaga and Blaauw (IEEE JSSC, Vol. 45, No. 1, pp. 23–31, Jan. 2010, DOI `10.1109/JSSC.2009.2034081`) isolate a cryptographic core from the external $V_{DD}$ supply rail using an interleaved array of on-chip capacitors cycling through three phases:
1. **Charge:** Capacitor $C$ charges to external $V_{DD}$.
2. **Supply (isolated):** Disconnected from external $V_{DD}$, $C$ powers the cryptographic core for one evaluation cycle, losing secret-dependent charge $\Delta Q_{\text{core}}(s)$ so its voltage drops to $V_{\text{after}}(s) = V_{DD} - \Delta Q_{\text{core}}(s)/C$.
3. **Discharge-Reset:** Before reconnecting to $V_{DD}$, $C$ discharges through an on-resistance $R_{\text{on}}$ toward a fixed floor $V_{\text{reset}}$ for duration $T_{\text{dis}}$, ending at:
   $$V_{\text{end}}(s) = V_{\text{reset}} + \big(V_{\text{after}}(s) - V_{\text{reset}}\big) \cdot e^{-T_{\text{dis}} / (R_{\text{on}} C)}.$$

When recharged to $V_{DD}$, the external supply delivers $Q_{\text{ext}}(s) = C(V_{DD} - V_{\text{end}}(s))$, so the secret-dependent external charge delta shrinks exponentially with the reset time-constant ratio $k = T_{\text{dis}} / (R_{\text{on}} C)$:
$$\Delta Q_{\text{ext}} = \big(\Delta Q_{\text{core}}(s_1) - \Delta Q_{\text{core}}(s_0)\big) \cdot e^{-k}.$$

In $0.13\,\mu\text{m}$ CMOS, Tokunaga and Blaauw achieved **$>10\text{ million}$ Measurements-to-Disclosure (MTD)** against external supply-pin DPA at **`7.2%` area overhead**, **`33%` power overhead**, and **`2x` performance degradation**.

**Three hard physical boundaries of SC-CE (quantified in Sub-probe 2C):**
1. **Incomplete-reset exponential floor:** Reducing $k = T_{\text{dis}} / (R_{\text{on}} C)$ to recover throughput leaks directly into the supply rail: `k = 1.0` yields only `8.69 dB` attenuation (`4.41 pC` residual out of `12.00 pC`); `k = 5.0` yields `43.43 dB`; `k = 10.0` yields `86.86 dB`; `k = 20.0` yields `173.72 dB`.
2. **Zero attenuation against near-field Electromagnetic Analysis (EMA) and substrate coupling:** During the Supply phase, the full secret-dependent current $\Delta Q_{\text{local}} = 12.00\text{ pC}$ still flows from the local on-die MIM capacitor into the crypto core through upper-metal power meshes and the capacitor top-plates (acting as magnetic/electric radiators). Sub-probe 2C highlights that even at `173.72 dB` supply-pin attenuation, **local EM leakage remains `0.00 dB` unattenuated**. Mitigating local EM requires pairing current-domain signature attenuation (CDSA / ASNI) with **lower-metal-stack routing burial** (e.g., STELLAR) to suppress top-metal antenna radiation.
3. **Inter-phase switching noise & area/energy tax:** Continuous discharge-to-$V_{\text{reset}}$ dissipates $\frac{1}{2} C (V_{\text{after}} - V_{\text{reset}})^2$ as wasted heat every cycle, imposing the ~33% power tax and $2\times$ frequency limit.

#### B. Randomized Clocking / Clock Jitter and Elastic Alignment Breakdown

OpenTitan's Clock Manager (`hw/top_earlgrey/ip_autogen/clkmgr/rtl/clkmgr.sv:94, 982–983`, `SEC_CM: JITTER.CONFIG.MUBI`) exposes a multi-bit-encoded `jitter_en_o` control driving the Analog Sensor Top (AST) jittery clock generator to randomize clock period durations dynamically (conceptually related to Güneysu and Moradi, CHES 2011, DOI `10.1007/978-3-642-23951-9_3`, and complemented by Ibex's `ibex_dummy_instr.sv` LFSR instruction insertion).

**Fundamental cryptographic limitation (verified in Sub-probe 2C):**
- Clock randomization and dummy instructions are **hiding** countermeasures: they spread a first-order leakage peak of amplitude $a$ across a temporal window of width $J + 1$ samples without reducing the underlying signal-to-noise ratio of each switching event.
- **Unaligned point-by-point attacks degrade only polynomially** ($\mathrm{SNR}_{\text{point}} \propto 1/(J+1)^2$, requiring $O(J^2)$ traces); **window-sum integration** over the jitter window reduces trace scaling to $O(J)$ ($\mathrm{SNR}_{\text{win}} \propto 1/(J+1)$).
- **Elastic Alignment (Dynamic Time Warping, van Woudenberg, Witteman, and Bakker, CT-RSA 2011, DOI `10.1007/978-3-642-19074-2_8`) and landmark alignment collapse jitter completely:** Whenever power/EM traces contain a visible clock edge, instruction-fetch pattern, or round-boundary landmark, aligning traces to that landmark restores the full unjittered SNR with **zero extra traces**!
- **Execution witness (Sub-probe 2C, $N = 1000$ traces/class, secret amplitude `0.5`, $\sigma = 1.0$, TVLA threshold `|t| = 4.5`):**

| Uniform Jitter Span $J$ (samples) | Naive Unaligned `max \|t\|` | Window-Sum Integration `\|t\|` | Landmark-Aligned `\|t\|` | Assessment |
| :---: | :---: | :---: | :---: | :--- |
| `J = 0` | `9.17` | `9.17` | `9.17` | Immediate TVLA fail |
| `J = 4` | `3.22` | `3.20` | **`11.05`** | Unaligned masked; aligned fails severely |
| `J = 8` | `2.43` | `1.73` | **`11.80`** | Unaligned masked; aligned fails severely |
| `J = 16` | `2.86` | `4.52` | **`12.40`** | **100% alignment recovery at `N = 1000`** |

Consequently, randomized clocking and dummy instructions are effective **multiplicative noise/alignment barriers** layered *on top of* masking (pushing higher-order $d$-variate attacks from practical to infeasible), but **provably unsound as standalone first-order defenses**.

## Boundaries

- **Known not to apply — Upstream `lowRISC/ibex` (`SecureIbex = 1`) as a glitch-safe masked-software host:** Upstream Ibex does not implement Coco-Ibex's `REGREAD_SECURE`/`REGWRITE_SECURE` one-hot gating or ALU/LSU blanking; its `SecureIbex` mode targets timing side channels (`DataIndTiming`) and fault injection (`RegFileECC`, `PCIncrCheck`, lockstep, `DummyInstructions`).
- **Known not to apply — OpenTitan OTBN blanking to the 32-bit base register file (`x1..x31`):** Explicitly excluded in `lowRISC/opentitan/hw/ip/otbn/README.md:1283`; masked OTBN software must confine all secret shares to the 256-bit bignum side (`w0..w31`, `ACC`, `MOD`, `MAI_*` WSRs).
- **Known not to apply — Coco-Ibex `ram_1p_secure.v` to arbitrary share placement:** Shares placed at identical in-block offsets (`addr[a+1:2]`) across distinct blocks leak `1.000000 bit` through the combinational inter-block MUX tree (`ram_1p_secure.v:109–154`; Sub-probe 2A).
- **Known not to apply — Hardware gating alone without compiler/software compliance:** Register-file overwriting and back-to-back share reads on the same port still produce `1.000000`-bit Hamming-distance transition leakage on Coco-Ibex and OTBN (`Sub-probe 2A`).
- **Known not to apply — Switched-capacitor current equalizers to near-field EM attacks and randomized clocking to elastic alignment:** SC-CE attenuates only the external supply pin while leaving local core/capacitor EM emissions unattenuated (`Sub-probe 2C`); clock jitter collapses from `|t| = 2.86` to `|t| = 12.40` under landmark/elastic alignment (`Sub-probe 2C`).
- **Unsupported — CocoAlma on secret-dependent control flow or speculative out-of-order CPUs:** CocoAlma freezes public control signals from a single concrete VCD execution trace (`SatChecker.py:412–416, 477–513`). Secret-dependent branches, secret-indexed memory addresses, dynamic caches, or out-of-order issue queues violate its deterministic-trace soundness precondition.
- **Not examined — Live Yosys + Verilator + CaDiCaL execution of CocoAlma on full `otbn_top_coco` or physical silicon TVLA measurements of OpenTitan Earl Grey tapeout silicon:** This investigation verified RTL source, CocoAlma's SAT encoder, OpenTitan's recorded CocoAlma log (`hw/ip/otbn/pre_sca/alma/README.md`), and standalone discrete/statistical Python probes; full EDA synthesis and lab oscilloscope TVLA traces on fabricated silicon were not executed.
- **Unknown — Physical capacitive wire-coupling ($c$-probing) margins on OpenTitan OTBN/AES post-P&R metal layouts:** Both CocoAlma (`SatChecker.py`) and RTL-level blanking model glitch and transition defaults at the netlist gate level; post-place-and-route interconnect crosstalk between adjacent WDR bit-slices depends on foundry metal spacing and shielding rules not present in public RTL.

## Evidence

### Pinned Upstream Repositories and Source Citations (Observed 2026-11-19)

- **`isec-tugraz/coco-alma` @ `95c80df5d6d704bf525f47ef6e58e98e27fedf97`** (resolved via `git -c protocol.version=0 ls-remote`):
  - `readme.md:65–231` — 4-stage flow (`parse.py`, `labels.txt` `secret`/`static_random`/`volatile_random`, `trace.py` Verilator, `verify.py` CaDiCaL/Kissat, `--probing-model`, `--checking-mode`).
  - `SatChecker.py:13–180` — `Formula` symbolic structures (`node_vars_stable`, `node_vars_trans`, `node_vars_diff`), `make_simple`, `assure_biased`.
  - `SatChecker.py:408–548, 603–612` — `__proc_mux` (VCD concrete-select specialization), `__proc_trans_reg` (transition leakage), `__make_stability_info` (controlling-value stability for `AND==0`/`OR==1`), `__build_trans`, `__build_hamming`.
- **`isec-tugraz/coco-ibex` @ `1ac262929d900d63d5ed702cd40edca1602a79c9`**:
  - `README.md:5, 15–35` — base Ibex commit `863fb56eb166d`, 7 toggleable hardening macros + unconditional LSU clearing + `ram_1p_secure.v` `(a, b)` parameters.
  - `rtl/secure.sv:1–7` — `REGREAD_SECURE`, `REGWRITE_SECURE`, `MEM_SECURE`, `MD_SECURE`, `SHIFT_SECURE`, `ADDER_SECURE`, `CSR_SECURE`.
  - `rtl/ibex_if_stage.sv:251–315` — IF-stage pre-decoding of one-hot read/write and functional-unit enables.
  - `rtl/ibex_register_file_ff.sv:26–104` — registered one-hot `read_enable_a/b_i` AND-OR read mux and `write_enable_secure_i` write gating.
  - `rtl/ibex_alu.sv:23–28, 79–90, 189–193, 257–267` — `adder_enable_i` and `shift_enable_i` operand blanking.
  - `rtl/ibex_load_store_unit.sv:80, 190–198` — unconditional `rdata_q <= 0` clearing.
  - `shared/rtl/ram_1p_secure.v:19–218` — one-hot in-block `OH_in_reg` gating (lines 109–117) feeding combinational inter-block binary MUX tree (lines 133–154).
- **`lowRISC/opentitan` @ `1e061997389b1c257043b0dbd2388a19a6c2f6f1`**:
  - `hw/ip/prim/rtl/prim_blanker.sv:8–20` — `prim_and2`-backed blanking cell.
  - `hw/ip/aes/rtl/aes_cipher_core.sv:99–144, 249–322`, `hw/ip/aes/rtl/aes_sbox_dom.sv:5–50`, `hw/ip/aes/doc/theory_of_operation.md:191–200, 281, 303–319` — 5-cycle DOM-dep AES S-box (28 PRD bits), PRNG clearing, `KEY_TOUCH_FORCES_RESEED`.
  - `hw/ip/kmac/rtl/keccak_2share.sv:22–26, 102–259` — 2-phase split Keccak round, 5 × `prim_dom_and_2share #(.Pipeline(1))`, `ForceRandExt` PRD muxing.
  - `hw/ip/otbn/README.md:1264–1283`, `hw/ip/otbn/doc/theory_of_operation.md:49–53, 625–696, 941–1011` — prefetch predecode blanking, unblanked base-side boundary, two-step Secure Wipe, MAI.
  - `hw/ip/otbn/rtl/otbn_rf_bignum.sv:26–193`, `hw/ip/otbn/rtl/otbn_rf_bignum_ff.sv:18–144` — 32 × 312b per-WDR `prim_blanker`, `prim_onehot_mux`, `(39,32)` Hsiao SECDED, `CTRL.REDUN`, `prim_onehot_check`, SVAs `BlankingBignumRegReadA/B_A`, `BlankingBignumRegWData_A`.
  - `hw/ip/otbn/rtl/otbn_alu_bignum.sv:673–1514` and `hw/ip/otbn/rtl/otbn_mac_bignum.sv:271–451` — datapath `prim_blanker` instances.
  - `hw/ip/otbn/pre_sca/alma/README.md` and `hw/ip/otbn/pre_sca/prolead/README.md` — in-tree CocoAlma (`234,238`-node `otbn_top_coco` netlist) and PROLEAD (`mask_acc_b2a`, targeting `ChairImpSec/PROLEAD`) pre-SCA harnesses.
  - `hw/top_earlgrey/ip_autogen/clkmgr/rtl/clkmgr.sv:94, 982–983` — `SEC_CM: JITTER.CONFIG.MUBI` `jitter_en_o`.
- **`lowRISC/ibex` @ `9b91b3a1195aecb0d80cf2de5b852e0b5f68cc6c`**:
  - `rtl/ibex_core.sv:45–49, 195–197` — `SecureIbex`, `DummyInstructions`, `RegFileECC`, `DataIndTiming`, `PCIncrCheck`.
  - `rtl/ibex_dummy_instr.sv:12–158` — LFSR-driven `DUMMY_ADD`/`MUL`/`DIV`/`AND` injection to `rd = x0`.

### Normative Papers and DOIs

- Gigerl et al. (USENIX Security 2021, Coco): `https://eprint.iacr.org/2020/1294`
- Hadžić and Bloem (FMCAD 2021, CocoAlma): `10.34727/2021/isbn.978-3-85448-046-4_9`
- Papagiannopoulos and Veshchikov (COSADE 2017, Mind the Gap): `https://eprint.iacr.org/2017/345`
- Shelton et al. (NDSS 2021, Rosita): `10.14722/ndss.2021.23137`
- Tokunaga and Blaauw (IEEE JSSC 2010, Switched-Capacitor Current Equalizer): `10.1109/JSSC.2009.2034081`
- Güneysu and Moradi (CHES 2011, Randomized Clocking): `10.1007/978-3-642-23951-9_3`
- van Woudenberg, Witteman, Bakker (CT-RSA 2011, Elastic Alignment): `10.1007/978-3-642-19074-2_8`

### Reproducible Execution Micro-Probe (Observed 2026-11-19, Python 3)

Command:

```bash
python3 - <<'PY'
import itertools, math, random
from collections import Counter

def mi(pairs):
    n = len(pairs)
    px, py, pxy = Counter(x for x, _ in pairs), Counter(y for _, y in pairs), Counter(pairs)
    return max(0.0, sum((c / n) * math.log2((c / n) / ((px[x] / n) * (py[y] / n))) for (x, y), c in pxy.items()))

def welch_t(xs, ys):
    mx, my = sum(xs)/len(xs), sum(ys)/len(ys)
    vx = sum((x-mx)**2 for x in xs)/(len(xs)-1)
    vy = sum((y-my)**2 for y in ys)/(len(ys)-1)
    return (mx - my) / math.sqrt(vx/len(xs) + vy/len(ys))

# 2A: Microarchitectural leakage on unhardened Ibex vs Coco-Ibex / OTBN
s2 = list(itertools.product([0, 1], repeat=2))
print("RF unhardened binary mux:", f"{mi([(a^b, (a,b)) for a,b in s2]):.6f}")
print("RF one-hot single-cycle :", f"{mi([(a^b, (a,0)) for a,b in s2]):.6f}")
print("RF one-hot back2back HD :", f"{mi([(a^b, a^b) for a,b in s2]):.6f}")
print("RF one-hot w/ blank cyc :", f"{mi([(a^b, a^0) for a,b in s2]):.6f}")
print("LSU uncleared rdata_q   :", f"{mi([(a^b, a^b) for a,b in s2]):.6f}")
print("LSU Coco-Ibex cleared   :", f"{mi([(a^b, a^0) for a,b in s2]):.6f}")
print("ram_1p_secure same off  :", f"{mi([(a^b, (a,b)) for a,b in s2]):.6f}")
print("ram_1p_secure diff off  :", f"{mi([(a^b, (a,0)) for a,b in s2]):.6f}")

# 2B: CocoAlma stability propagation on 2-to-1 MUX (s0, s1)
for name, p, c in [("static_no_vcd", None, None), ("alma_stable_0->0", 0, 0), ("alma_toggle_0->1", 0, 1)]:
    corr = ["s0"] if (p is not None and p == c and c == 0) else ["s0", "s0^s1", "s1"]
    print(f"Mux {name:18s}: leak={'s0^s1' in corr} corr={corr}")

# 2C: SC-CE external attenuation vs local EM & Randomized Clocking vs Alignment
for k in [1.0, 5.0, 10.0, 20.0]:
    dq_ext = 12.0 * math.exp(-k)
    print(f"SC-CE k={k:4.1f}: dQ_ext={dq_ext:.4e} pC ({20*math.log10(12.0/dq_ext):6.2f} dB), dQ_local=12.00 pC (0.00 dB)")

rng = random.Random(20261119)
for J in [0, 4, 8, 16]:
    c0, c1 = [], []
    for _ in range(1000):
        j0, j1 = rng.randint(0, J), rng.randint(0, J)
        t0 = [rng.gauss(0.0, 1.0) for _ in range(40)]; t0[8+j0] += 6.0; c0.append(t0)
        t1 = [rng.gauss(0.0, 1.0) for _ in range(40)]; t1[8+j1] += 6.0; t1[10+j1] += 0.5; c1.append(t1)
    u = max(abs(welch_t([t[i] for t in c0], [t[i] for t in c1])) for i in range(10, 10+J+1))
    w = abs(welch_t([sum(t[10:10+J+1]) for t in c0], [sum(t[10:10+J+1]) for t in c1]))
    al = abs(welch_t([t[max(range(8, 8+J+1), key=lambda i: t[i])+2] for t in c0],
                     [t[max(range(8, 8+J+1), key=lambda i: t[i])+2] for t in c1]))
    print(f"Jitter J={J:2d}: unaligned={u:5.2f}, window={w:5.2f}, aligned={al:5.2f}")
PY
```

Recorded output (`exit 0`):

```text
RF unhardened binary mux: 1.000000
RF one-hot single-cycle : 0.000000
RF one-hot back2back HD : 1.000000
RF one-hot w/ blank cyc : 0.000000
LSU uncleared rdata_q   : 1.000000
LSU Coco-Ibex cleared   : 0.000000
ram_1p_secure same off  : 1.000000
ram_1p_secure diff off  : 0.000000
Mux static_no_vcd     : leak=True corr=['s0', 's0^s1', 's1']
Mux alma_stable_0->0  : leak=False corr=['s0']
Mux alma_toggle_0->1  : leak=True corr=['s0', 's0^s1', 's1']
SC-CE k= 1.0: dQ_ext=4.4146e+00 pC (  8.69 dB), dQ_local=12.00 pC (0.00 dB)
SC-CE k= 5.0: dQ_ext=8.0855e-02 pC ( 43.43 dB), dQ_local=12.00 pC (0.00 dB)
SC-CE k=10.0: dQ_ext=5.4480e-04 pC ( 86.86 dB), dQ_local=12.00 pC (0.00 dB)
SC-CE k=20.0: dQ_ext=2.4734e-08 pC (173.72 dB), dQ_local=12.00 pC (0.00 dB)
Jitter J= 0: unaligned= 9.17, window= 9.17, aligned= 9.17
Jitter J= 4: unaligned= 3.22, window= 3.20, aligned=11.05
Jitter J= 8: unaligned= 2.43, window= 1.73, aligned=11.80
Jitter J=16: unaligned= 2.86, window= 4.52, aligned=12.40
```

## Revalidation

1. **Microarchitectural, stability, SC-CE, and jitter-alignment probes (seconds):** Rerun the inline Python 3 probe under **Evidence** to re-verify all mutual-information, stability, attenuation, and Welch $t$-test statistics without external dependencies.
2. **Upstream RTL and verifier drift checks:**
   - Diff `lowRISC/opentitan` `hw/ip/otbn/rtl/{otbn_rf_bignum_ff.sv,otbn_alu_bignum.sv,otbn_mac_bignum.sv}`, `hw/ip/otbn/README.md` (`## Blanking`), `hw/ip/otbn/pre_sca/{alma,prolead}/README.md`, `hw/ip/aes/rtl/aes_sbox_dom.sv`, and `hw/ip/kmac/rtl/keccak_2share.sv` against commit `1e061997389b1c257043b0dbd2388a19a6c2f6f1` to verify whether OTBN base-side blanking was added, whether `ForceRandExt` defaults changed, or whether MAI verification harnesses moved to newer CocoAlma/PROLEAD commits.
   - Diff `lowRISC/ibex` `rtl/ibex_register_file_ff.sv` and `rtl/ibex_core.sv` against commit `9b91b3a1195aecb0d80cf2de5b852e0b5f68cc6c` to check whether upstream `SecureIbex` adopted Coco-Ibex's registered one-hot read/write gating or ALU blanking.
   - Diff `isec-tugraz/coco-alma` `SatChecker.py` against commit `95c80df5d6d704bf525f47ef6e58e98e27fedf97` to check for changes to `__make_stability_info` or transition-probing semantics.
3. **Full end-to-end co-verification sign-off for any concrete masked binary:** Synthesize the target core (`syn_yosys.sh` in OpenTitan OTBN or Yosys on `coco-ibex`), assemble the target masked program, generate its Verilator VCD via `trace.py`, and run `verify.py --mode transient --probing-model time-constrained` in CocoAlma (and `evaluate.sh` in PROLEAD for MAI hardware gadgets). Any compiler upgrade, register-allocator change, or RTL synthesis flag change requires re-running this netlist co-verification step.
