# Host-Decoupled FPGA Simulation, Open Bitstream Place-and-Route Safety, and Lockstep RVFI/Coroutine RTL Cosimulation

## Summary

Hardware verification and FPGA-accelerated architecture simulation bridge three distinct semantic boundaries, each governed by a strict synchronization or exclusivity invariant whose violation silently corrupts determinism, silicon safety, or architectural soundness:

1. **Host–Target Time Decoupling (`FireSim` / `Golden Gate` `FAME-1`):** Compiling synthesizable RTL into a Latency-Insensitive Bounded Dataflow Network (`LI-BDN`) decouples target architectural time from nondeterministic host PCIe/DRAM latency by gating every target clock buffer with `CE = enableReg ∧ targetCycleFinishing ∧ ¬hostReset` and tracking per-channel token consumption via a host-clocked `firedReg` (`sim/midas/src/main/scala/midas/passes/fame/FAMETransform.scala:62–202, 351–359`). Target-cycle determinism holds **if and only if** every bridge channel is *token-irrevocable* (`AssertTokenIrrevocable`, `Channel.scala:49–67`). Furthermore, in rational multi-clock hubs, two slower clock domains (e.g., periods $3$ and $4$, each having intra-domain Minimum Firing-Margin Ratio $\mathrm{MFMR} = 2$) can still fire on **consecutive host cycles**, forbidding clock-divider STA constraints across inter-domain paths (`FAMETransform.scala:208–240`).
2. **Open FPGA Place-and-Route & Bitstream PIP Exclusivity (`nextpnr` + `Project X-Ray`):** `nextpnr` couples `HeAP` analytical Conjugate-Gradient bound-to-bound placement (`common/place/placer_heap.cc:61–134, 901–1021`) with `PathFinder`/`CRoute` negotiated-congestion rip-up routing (`common/route/router2.cc:798–850, 1226–1280`). Lowering routed `FASM` features through `Project X-Ray` (`prjxray/fasm_assembler.py:81–124`) detects bit-level `FasmInconsistentBits` collisions **only** when one feature sets a frame bit (`1`) that another explicitly clears (`!bit -> 0`). Because many Xilinx 7-series interconnect Programmable Interconnect Points (`PIPs`) use two-hot crossbar encodings *without* `!` zero-bit guards—such as `INT_L.WW2BEG0.LOGIC_OUTS_L12` (`11_14 12_14`) and `INT_L.WW2BEG0.LOGIC_OUTS_L4` (`09_14 15_14`) in `utils/test_data/db/segbits_int_l.db:7,13`—an unvalidated FASM file can enable two drivers on `WW2BEG0` with zero assembler errors, creating a 4-path CMOS pass-transistor contention short alongside `FPGAhammer`-class combinational ring-oscillator power droops.
3. **Tandem Architectural Lockstep (`RVFI` + `Dromajo`) & Stratified Coroutine Cosimulation (`cocotb`):** `RVFI` (`docs/source/rvfi.rst:26–252`) projects out-of-order execution onto `NRET` retirement channels ordered by gap-free `rvfi_order`, but `riscv-formal`'s `checks/rvfi_dmem_check.sv:37,39` omits the `channel_idx * RISCV_FORMAL_XLEN` bit offset on `rvfi_mem_rdata` and `rvfi_mem_wdata`, causing spurious formal failures or unsound shadow updates on superscalar (`NRET > 1`) cores. Downstream, `Dromajo` (`src/dromajo_cosim.cpp:120–157, 234–244, 434–453`) intentionally omits `mstatus` checks, skips instruction-word comparison whenever the emulator fetches a 16-bit RVC parcel (`(emu_insn & 3) != 3`), and overrides `rd` from the DUT on failed `SC.W`/`SC.D`, MMIO loads, and `mcycle`/`mip`/`sip` CSR reads. In Python-driven RTL testbenches, `cocotb` (`src/cocotb/handle.py:804–911`, `_gpi_triggers.py:181–244`, `verilator.cpp:174–231`) eliminates zero-delay Active-region write/read races by batching `Deposit` assignments into a deduplicated `_write_calls` dictionary flushed at `cbReadWriteSynch` and forbidding signal mutation during `cbReadOnlySynch`, at the cost of a ~`20–150 kHz` C-to-Python VPI callback throughput ceiling.

## Applicability

This report characterizes the exact source implementations, formal interfaces, and composition boundaries of the six pinned upstream revisions recorded in `REPORT.json`:

- **`firesim/firesim` (`9db588176c19e7252ed3027b2028bc21095f863a`):** Applies to Golden Gate (`sim/midas/`) FIRRTL-to-FPGA `FAME-1` single-threaded host-decoupled transforms, `FAME-5` threaded memory/instance transforms (`MultiThreadFAME5Models.scala`), and `FASED` AXI4 DRAM timing models (`FASEDMemoryTimingModel.scala`) targeting Xilinx UltraScale+ shells (e.g., AWS EC2 F1/F2 and VCU118).
- **`YosysHQ/nextpnr` (`0f387c6a522a4e3aefe54b4d066e37548ccf9546`) & `f4pga/prjxray` (`c9f02d8576042325425824647ab5555b1bc77833`):** Applies to `nextpnr`'s architecture-independent `HeAPPlacer`, `Router1`, and `Router2` engines and `Project X-Ray`'s Xilinx 7-series (Artix-7, Kintex-7, Zynq-7000) `segbits_*.db` databases and `FasmAssembler` frame generator (101 words $\times$ 32 bits per frame). UltraScale+ and Lattice ECP5/iCE40 share `nextpnr`'s `common/` algorithms, while frame geometry and PIP `segbits` encodings are specific to Xilinx 7-series.
- **`YosysHQ/riscv-formal` (`c992aa61fdfe0846c5ed90324c596202a1c69b76`) & `chipsalliance/dromajo` (`8c0c1e3afd5cdea65d1b35872e395f988b0ec449`):** Applies to RV32I/RV64GC processor cores exposing `RVFI` (and optional `RISCV_FORMAL_ROLLBACK`, `RISCV_FORMAL_MEM_FAULT`, `RISCV_FORMAL_ALTOPS`, `RVFI_BUS`) or linked in-process via C++/DPI-C against `libdromajo_cosim` (`dromajo_cosim_init`, `dromajo_cosim_step`, `dromajo_cosim_raise_trap`, `dromajo_cosim_override_mem`).
- **`cocotb/cocotb` (`c1faa6f710c8b389a659fd5d712422ea0739136a`):** Applies to Python 3 coroutine testbenches driving SystemVerilog, Verilog, or VHDL simulators over `cocotb` 2.x's Generic Procedural Interface (`GPI`) backed by IEEE 1800/1364 `VPI` (`VpiImpl.cpp`), `VHPI`, `FLI`, or Verilator's `VerilatedVpi` main loop (`verilator.cpp`).

The six subjects form a vertical hardware-assurance stack: `cocotb` and `RVFI`/`Dromajo` verify core/peripheral RTL in event-driven or compiled C++ simulation before synthesis; `FireSim` accelerates full-SoC/cluster RTL deterministically on cloud FPGAs via `FAME-1`; and `nextpnr` + `Project X-Ray` expose the physical placement, routing, and bitstream-mux invariants that vendor and open FPGA flows must enforce to prevent silicon contention and multi-tenant power attacks.

## Findings

### 1. Host–Target Time Decoupling in FireSim / Golden Gate (`FAME-1`, `LI-BDN`, and `FASED`)

#### 1.1 `FAME-1` FIRRTL Transformation and `firedReg` Reset Asymmetry
`Basis: source + execution`

In `firesim/firesim` (`sim/midas/src/main/scala/midas/passes/fame/WrapTop.scala:17–47` and `FAMETransform.scala:123–376`), Golden Gate wraps the target hierarchy inside `FAMETop`, injects `hostClock` and `hostReset`, excises inter-model and bridge channels (`ChannelExcision.scala:35–149`), and rewrites each target module via `FAMEModuleTransformer` into a synchronous `LI-BDN` actor clocked solely by `hostClock`.

For every excised target input channel $i \in \mathcal{I}$ (`portName = "${name}_sink"`) and output channel $o \in \mathcal{O}$ (`portName = "${name}_source"`), `FAMEModuleTransformer` synthesizes a 1-bit host-clocked state register `firedReg` (`isFired`) alongside the combinational cycle-completion signal `targetCycleFinishing` (`finishing`):

$$\begin{aligned}
\mathrm{isFiring}(c) &= c.\mathrm{ready} \land c.\mathrm{valid} \\
\mathrm{isFiredOrFiring}(c) &= \mathrm{isFired}(c) \lor \mathrm{isFiring}(c) \\
\forall o \in \mathcal{O}:\quad o.\mathrm{valid} &= \Big(\bigwedge_{i \in \mathrm{ccDeps}(o)} i.\mathrm{valid}\Big) \land \neg \mathrm{isFired}(o) \\
\mathrm{allFiredOrFiring} &= \Big(\bigwedge_{o \in \mathcal{O}} \mathrm{isFiredOrFiring}(o)\Big) \land \Big(\bigwedge_{i \in \mathcal{I}} i.\mathrm{valid}\Big) \\
\mathrm{finishing} &= \mathrm{allFiredOrFiring} \land \mathrm{clockChannel.valid} \\
\forall i \in \mathcal{I}:\quad i.\mathrm{ready} &= \mathrm{finishing} \land \neg \mathrm{isFired}(i)
\end{aligned}$$

Three implementation details in `FAMETransform.scala` are load-bearing for deadlock-free and deterministic startup:

1. **Asymmetric `firedReg` Reset (`FAMETransform.scala:278–286`):** In multi-clock hubs, `firedReg` resets to **`1` ("already fired") on input channels** (`resetVal = UIntLiteral(if (isInput) 1 else 0)`) and **`0` ("unfired") on output channels**. Resetting output channels to `0` lets time-0 combinational outputs resolve before the first clock token is dequeued, while resetting input channels to `1` prevents premature input-token dequeues until the first clock token establishes which clock domains are active.
2. **One-Stage Pipelined Input vs. Output Domain Enables (`FAMETransform.scala:67–69, 172–202, 272–276`):** On `hostClock` rising edges, `isFired(c)` updates via:
   $$\mathrm{isFired}'(c) = \begin{cases} \neg \mathrm{clockDomainEnable}(c) & \text{if } \mathrm{finishing} = 1 \\ \mathrm{isFired}(c) \lor \mathrm{isFiring}(c) & \text{if } \mathrm{finishing} = 0 \end{cases}$$
   Crucially, `inputChannelEnable` reads the *incoming* `clockChannel` bit combinationally, whereas `outputChannelEnable` reads the registered `enableReg` (which also gates the `DefineAbstractClockGate` buffer via `CE = enableReg ∧ finishing ∧ ¬hostReset`, `L198–201`). Thus input tokens for target edge $k$ are dequeued synchronously with the launch of target clock edge $k$, while output tokens settle across the ensuing target cycle.
3. **Combinational Dependency Filtering (`ccDeps`, `FAMETransform.scala:114–116, 311–319`):** An output channel $o$ may depend combinationally on a subset of input channels $\mathrm{ccDeps}(o) \subseteq \mathcal{I}$. Gating $o.\mathrm{valid}$ only on $\bigwedge_{i \in \mathrm{ccDeps}(o)} i.\mathrm{valid}$ (rather than waiting for `finishing`) allows downstream models to consume $o$'s token in earlier host cycles when sink buffers backpressure unrelated channels, avoiding combinational `ready`/`valid` loops across cut boundaries.

#### 1.2 Token Irrevocability and Bidirectional `SimReadyValidIO` Bifurcation
`Basis: source + execution`

Target RTL interfaces that use `ReadyValidIO` (`DecoupledIO`) cannot be mapped directly onto a single host `Decoupled` stream without conflating *host* backpressure (empty PCIe DMA ring or host DDR4 refresh) with *target* backpressure (full L1 MSHR). In `sim/midas/src/main/scala/midas/core/Channel.scala:90–229`, `SimReadyValidIO` bifurcates one target `Decoupled` bundle into **two independent host token streams**:
- **Forward channel (`fwd`):** Host handshake `(fwd.hValid, fwd.hReady)` carrying payload `{target.valid, target.bits}` (`ValidIO[T]`). Notice that an idle target cycle (`target.valid == 0`) *still* transmits an explicit host token with `bits.valid = false`!
- **Reverse channel (`rev`):** Host handshake `(rev.hValid, rev.hReady)` carrying a 1-bit payload `target.ready`.

`Channel.scala:49–67` defines `AssertTokenIrrevocable`, enforcing two LTL safety invariants on every host token stream:
$$\square \big((\mathrm{valid}_{t-1} \land \neg \mathrm{fire}_{t-1}) \implies (\mathrm{valid}_t \land \mathrm{bits}_t = \mathrm{bits}_{t-1})\big)$$
Because an output channel can fire several host cycles *before* `targetCycleFinishing` asserts (`out4_fired` latches `1` while the module stalls waiting for a slow input channel), any bridge or model that retracts `hValid` or mutates `bits` based on host cycle count leaks host-timing jitter into target architectural state. Probe 1A (`## Evidence`) confirms exact bit-for-bit state identity (`reg3 = 0x000042ea`, `reg4 = 0xf3779a68`) across `199` vs. `1,946` host cycles when irrevocability holds, and immediate state divergence (`0xca5db22b` vs. `0x115a6bf0`) when violated.

#### 1.3 Multi-Clock `MFMR` XDC Multicycle Relaxation vs. Cross-Domain Single-Cycle Paths
`Basis: source + execution + derived`

When a `FAME-1` hub hosts multiple rational target clocks with periods $(T_1, \dots, T_m)$, the clock bridge emits tokens only at target timestamps where at least one clock has a rising edge. The Minimum Firing-Margin Ratio ($\mathrm{MFMR}_k \ge 1$) of clock $k$ is the minimum number of emitted clock tokens between two consecutive firings of clock $k$.

As documented and implemented in `FAMETransform.scala:208–240`, for target clock periods $(2, 3, 4)$:

| Token index | `0` | `1` | `2` | `3` | `4` | `5` | Intra-domain $\mathrm{MFMR}$ |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| Target time $t$ | `0` | `2` | `3` | `4` | `6` | `8` | — |
| `clk_2` (period 2) | `1` | `1` | `0` | `1` | `1` | `1` | `1` host cycle |
| `clk_3` (period 3) | `1` | `0` | `1` | `0` | `1` | `0` | `2` host cycles |
| `clk_4` (period 4) | `1` | `0` | `0` | `1` | `0` | `1` | `2` host cycles |

Although both `clk_3` and `clk_4` have $\mathrm{MFMR} = 2$ (neither fires in back-to-back tokens), **token `2` (`t = 3`, `clk_3 = 1`) and token `3` (`t = 4`, `clk_4 = 1`) fire on consecutive host cycles ($\Delta h = 1$)** when no host stalls intervene (confirmed by Probe 1A: `intra_dh = (1, 2)` for `(clk_3, clk_4)` on the `(3, 4)` schedule, `cross_dh = 1`). Defining generated clocks with Vivado `-divide_by 2` would falsely grant 2 host cycles of setup margin to synchronous CDC paths between `clk_3` and `clk_4`. Consequently, `FAMEModuleTransformer` (`L231–237`) emits `-divide_by 1` on every gated clock buffer and restricts `set_multicycle_path $clockMFMR -setup` and `set_multicycle_path ${clockMFMR - 1} -hold` **strictly to intra-domain paths** (`-from [get_clocks $clockName] -to [get_clocks $clockName]`).

#### 1.4 Split Functional/Timing Memory Models (`FASED`)
`Basis: documentation + source`

`FASEDMemoryTimingModel` (`sim/midas/src/main/scala/midas/models/dram/FASEDMemoryTimingModel.scala:30–250`, Biancolin et al., FPGA 2019, `DOI: 10.1145/3289602.3293894`) separates *functional data storage* (backed by physical host FPGA DDR4 over `AXI4MasterNode` `toHostDRAMNode`) from *target cycle-timing calculation* (synthesized bank/rank/row-buffer FSMs or `LatencyBandwidthPipe` in FPGA LUTs/BRAMs). If host DDR4 takes 80 host cycles during refresh while the simulated target DDR3 timing model dictates 12 target cycles, `FASED` withholds its FAME-1 output token (`hValid = 0`), stalling target clocks across the entire SoC with zero target-time distortion. Conversely, `BaseParams` (`L30–35`) warns that *underprovisioning* `maxReads`/`maxWrites` in the host functional tracker causes the functional model to assert backpressure early, throttling simulated target AXI4 bandwidth unless `relaxFunctionalModel` (`L209`) or full diplomatic `AXI4EdgeSummary` bounds (`L102–150`) are provisioned.

---

### 2. Analytical Placement (`HeAP`), Negotiated Routing (`PathFinder`), and Bitstream PIP Safety (`nextpnr` & `Project X-Ray`)

#### 2.1 `HeAP` Bound-to-Bound Conjugate-Gradient Placement & BEL Legalization (`nextpnr`)
`Basis: source + documentation`

`YosysHQ/nextpnr` (`common/place/placer_heap.cc:18–32, 61–260, 901–1050`; Shah et al., FCCM 2019, `DOI: 10.1109/FCCM.2019.00010`) adapts Gort & Anderson's Heterogeneous Analytical Placer (`HeAP`) with two architectural modifications for commercial fabrics:
1. **Timing-Weighted Bound-to-Bound Clique Decomposition (`placer_heap.cc:922–980`):** Rather than adding quadratic edges between all $\binom{p}{2}$ pin pairs of a $p$-pin net, `build_equations` identifies the extremal lower-bound pin $l$ (`lbpos`) and upper-bound pin $u$ (`ubpos`) along each axis ($x$ and $y$ solved concurrently via `Eigen::ConjugateGradient<SparseMatrix<double>, Lower | Upper>`, `L126–128`) and connects each pin $i$ only to $\{l, u\}$ with linearized HPWL weight:
   $$w_{i,b} = \frac{1 + w_{\text{tmg}} \cdot \mathrm{crit}(i)^{\gamma}}{(|U_{\text{net}}|) \cdot \max\big(1,\; s_{\text{axis}} \cdot |x_i - x_b|\big)}$$
   where default $w_{\text{tmg}} = 10$, $\gamma = 2$ (`L31, 965–967`). In iteration $t \ge 0$, each movable cell $i$ also receives a diagonal spreading anchor $w_{\text{legal}} = \frac{\alpha \cdot t}{\max(1, s_{\text{axis}} |x_i^{\text{legal}} - x_i|)}$ pulling the analytical solution toward the coarse-spread legal location (`L981–994`).
2. **BEL-Granular Strict Legalization & Control-Set Accounting (`placer_heap.cc:27–31, 136–157, 581–615`):** Because `nextpnr` places individual Basic Elements (`BELs`: LUTs, FFs, MUXFs, CARRY4s, DSP48s, RAMBs) rather than pre-packed CLBs, `ControlSetState` tracks slice-level FF clock/reset/CE compatibility (`NPNR_ASSERT(this->ctrl_set == ctrl_set)`, `L145`) and `StrictLegaliser` (`L1048`) resolves overlaps over `FastBels` buckets in expanding neighborhoods until `solved_hpwl > 0.8 * legal_hpwl` or 5 stalled iterations elapse (`L250`).

#### 2.2 `PathFinder` / `CRoute` Bidirectional Negotiated-Congestion Routing (`nextpnr`)
`Basis: source`

`nextpnr` provides two PathFinder-derived (McMurchie & Ebeling, FPGA 1995) routers: `Router1` (`common/route/router1.cc`) and connection-based bidirectional A* `Router2` (`common/route/router2.cc`, adapted from Vercruyce et al. `CRoute`, FCCM 2019, `DOI: 10.1109/FCCM.2019.00017`). In `Router2`:
- **Initial Overlap & Wire Reservation (`router2.cc:67–115, 596–720`):** Before negotiation begins, `find_all_reserved_wires` computes a fixed point reserving mandatory single-choice uphill sink paths and downhill driver paths (`wd.reserved_net = net->udata`), raising an immediate `log_error` if two nets require the same dedicated BEL pin wire (`L617–620, 667–670`).
- **Historical Congestion Escalation & Group Resource Exclusivity (`router2.cc:1226–1280`):** During early iterations, multiple nets may bind the same `WireId` (`wd.curr_cong > 1`) or conflicting values of an architecture `GroupId` resource (`rd.value_count.size() > 1`, modeling shared tile mux select lines or LUT-thru ports). After each pass, `update_congestion` escalates historical penalties:
  $$h_w^{(t+1)} = \min\!\big(10^9,\; h_w^{(t)} + (\mathrm{curr\_cong}_w - 1) \cdot w_{\text{hist}}\big), \qquad h_r^{(t+1)} = \min\!\big(10^9,\; h_r^{(t)} + (|\mathrm{values}_r| - 1) \cdot w_{\text{hist}}\big)$$
  Every 3rd routing failure on a net expands its search bounding box (`if ((net_data.fail_count % 3) == 0) ctx->expandBoundingBox(net_data.bb)`, `L1275–1278`). Critical arcs (`crit > 0.95`, `L820, 830`) clamp congestion weight `crit_weight = max(0.05, 1 - crit^2)` and bypass mode-0 local-tree seeding to take minimum-delay paths. Finally, `bind_and_check` (`L1282–1350`) commits routes through `ctx->checkWireAvail` and `ctx->checkPipAvailForNet`, certifying single-net ownership in `nextpnr`'s in-memory graph.

#### 2.3 `Project X-Ray` `segbits`, Silent Two-Hot PIP Contention Shorts, and `FPGAhammer` Voltage Droops
`Basis: source + execution + documentation`

In `f4pga/prjxray` (`docs/dev_database/common/segbits.rst:40–113` and `prjxray/fasm_assembler.py:25–164`), Xilinx 7-series configuration frames consist of `101` 32-bit words (`bitstream.FRAME_WORD_COUNT = 101`; word 50 holds the horizontal clock row and frame ECC). Each `segbits_<tile>.db` rule maps a FASM feature `<tile_type>.<dst_wire>.<src_wire>` to space-separated bit tokens `<frame_offset>_<bit_pos>` (set to `1`) and `!<frame_offset>_<bit_pos>` (cleared to `0`).

Inspection of `FasmAssembler` (`fasm_assembler.py:81–124`) alongside `utils/test_data/db/segbits_int_l.db:1–13` exposes a critical **verification gap between FASM assembly and silicon electrical safety**:

- **What `FasmAssembler` checks:** `frame_set` (`L90–98`) and `frame_clear` (`L111–120`) maintain `self.frames[(frame_addr, word_addr, bit_index)] ∈ {0, 1}` and raise `FasmInconsistentBits` **if and only if** one feature sets a bit to `1` and another feature explicitly clears that *exact* bit via `!` to `0`.
- **Where `FasmAssembler` is blind (Two-Hot Switch-Matrix Crossbars):** In `segbits_int_l.db`, input-mux PIPs such as `INT_L.IMUX_L1.EE2END0 !22_09 !23_09 !25_09 18_08 24_09` (`L1`) include `!` zero-bit guards across their 1-of-4 stage, so enabling a competing sibling on `IMUX_L1` triggers `FasmInconsistentBits` (verified in Probe 1B: 2 bit conflicts on `22_09` and `24_09`). However, interconnect wire drivers such as lines `7` and `13`:
  ```text
  INT_L.WW2BEG0.LOGIC_OUTS_L12 11_14 12_14
  INT_L.WW2BEG0.LOGIC_OUTS_L4  09_14 15_14
  ```
  encode a two-stage pass-transistor crossbar (1 row bit + 1 column bit) with **zero `!` cleared-bit tokens**. As proven by Probe 1B (`## Evidence`), feeding both features into `FasmAssembler` produces **zero `FasmInconsistentBits` exceptions** and sets all four bits `{'09_14', '11_14', '12_14', '15_14'}` in word 0 of frames `9, 11, 12, 15`. Electrically, setting two row selects and two column selects in an unbuffered CMOS pass-transistor mux simultaneously closes **four** paths—the two requested PIPs plus two phantom cross-product paths `(09_14, 12_14)` and `(11_14, 15_14)`—shorting `VDD` to `GND` across opposing logic drivers!
- **Dynamic Power-Distribution-Network (`PDN`) Attacks (`FPGAhammer`):** Even when static PIP driver exclusivity holds, Krautter, Gnad, and Tahoori (*TCHES* 2018, `DOI: 10.13154/tches.v2018.i3.44-68`) demonstrated that instantiating thousands of combinational LUT inverter rings (`Ring Oscillators`, toggling at `400–900 MHz` uncontrolled by any clock tree) or synchronous high-fanout glitch amplifiers induces steep $L \frac{dI}{dt}$ + $IR$ voltage droops across shared cloud-FPGA PDNs, injecting setup-time bit flips into co-tenant AES cores for Differential Fault Analysis. Cloud FPGA shells (such as AWS EC2 F1) therefore reject raw user bitstreams, accepting only post-route netlists/DCPs vetted by Vivado `[DRC LUTLP-1]` (combinational loop ban), latch/oscillator screens, and partial-reconfiguration boundary isolation. Open toolchains (`nextpnr` -> `fasm2frames` -> `xc7frames2bit`) perform **no standalone bitstream-level electrical DRC** once FASM leaves `nextpnr`'s `bind_and_check`.

---

### 3. Lockstep Retirement (`RVFI` + `Dromajo`) and Stratified Coroutine Cosimulation (`cocotb`)

#### 3.1 `RVFI` Normative Retirement Contract & `rvfi_dmem_check.sv` Superscalar Bug
`Basis: normative + source + execution`

The RISC-V Formal Interface (`YosysHQ/riscv-formal`, `docs/source/rvfi.rst:7–350`) collapses arbitrary pipelined, superscalar, or out-of-order microarchitectures into `NRET` purely observational output channels per clock edge:

| Signal Group | Width (per `NRET` bundle) | Normative Invariant (`rvfi.rst`) |
| :--- | :--- | :--- |
| Metadata | `valid[1]`, `order[64]`, `insn[ILEN]`, `trap[1]`, `halt[1]`, `intr[1]`, `mode[2]`, `ixl[2]` | `rvfi_order` is strictly unique and gap-free ($0, 1, 2, \dots$). Reordered retirement is legal iff register/memory write-before-read causality holds (`L41–45`). `rvfi_intr` marks the *first instruction of a trap handler* whose `pc_rdata != prev.pc_wdata` (`L67–69`). |
| Integer Regs | `rs1_addr[5]`, `rs2_addr[5]`, `rs1_rdata[XLEN]`, `rs2_rdata[XLEN]`, `rd_addr[5]`, `rd_wdata[XLEN]` | If `rs1_addr == 0`, `rs1_rdata` **must** be `0` (`L95–96`). Instructions not writing `rd` **must** drive `rd_addr = 0`, and whenever `rd_addr == 0`, `rd_wdata` **must** be `0` (`L103–109`). Same-cycle WAW conflicts across `NRET > 1` are won by the **highest channel index** (`L10–12`). |
| Memory & Faults | `mem_addr[XLEN]`, `mem_rmask[XLEN/8]`, `mem_wmask[XLEN/8]`, `mem_rdata[XLEN]`, `mem_wdata[XLEN]` | Byte lanes $b$ are valid iff `rmask[b]` / `wmask[b]` is `1`. Under `RISCV_FORMAL_MEM_FAULT`, faulting loads/stores suppress `wmask`/`rd_addr` and emit attempted masks on `rvfi_mem_fault_{r,w}mask` (`L259–273`). |
| Speculative Rollback | `rvfi_rollback_valid[1]`, `rvfi_rollback_order[64]` | Invalidates all *prior-cycle* RVFI packets with `rvfi_order >= rvfi_rollback_order`; same-cycle packets belong to the restarted stream (`L234–251`). |
| `ALTOPS` (`M` ext) | 64-bit XOR masks | Replaces intractable BMC multiplier/divider cones with `(rs1 ± rs2) ^ MASK`, e.g., `MUL -> (a + b) ^ 0x2cdf52a55876063e`, `DIV -> (a - b) ^ 0x29bbf66f7f8529ec` (64-bit MD5 prefixes, `L164–200`). |

**Primary-Source Defect in `checks/rvfi_dmem_check.sv` (`Basis: source + execution`):**
Comparing `checks/rvfi_reg_check.sv:32–34` against `checks/rvfi_dmem_check.sv:34–42` in `YosysHQ/riscv-formal` @ `c992aa61fdfe0846c5ed90324c596202a1c69b76` reveals an unindexed slice defect on superscalar (`RISCV_FORMAL_NRET > 1`) cores:
```systemverilog
// checks/rvfi_dmem_check.sv:34-41
if (rvfi_valid[channel_idx] && rvfi_mem_addr[channel_idx*`RISCV_FORMAL_XLEN +: `RISCV_FORMAL_XLEN] == dmem_addr && `rvformal_addr_valid(dmem_addr)) begin
    for (i = 0; i < `RISCV_FORMAL_XLEN/8; i = i+1) begin
        if (enable && rvfi_mem_rmask[channel_idx*`RISCV_FORMAL_XLEN/8 + i] && dmem_written[i])
            assert(dmem_shadow[i*8 +: 8] == rvfi_mem_rdata[i*8 +: 8]); // MISSING channel_idx*`RISCV_FORMAL_XLEN!
        if (rvfi_mem_wmask[channel_idx*`RISCV_FORMAL_XLEN/8 + i]) begin
            dmem_shadow[i*8 +: 8] = rvfi_mem_wdata[i*8 +: 8];         // MISSING channel_idx*`RISCV_FORMAL_XLEN!
```
While `rvfi_valid`, `rvfi_mem_addr`, `rvfi_mem_rmask`, and `rvfi_mem_wmask` properly advance by `channel_idx`, `rvfi_mem_rdata[i*8 +: 8]` and `rvfi_mem_wdata[i*8 +: 8]` hardcode channel `0`'s `[XLEN-1:0]` slice! Because `rvfi.rst:37–39, 150–155` explicitly permits unmasked/invalid channel-0 `wdata` bytes to hold arbitrary values, any store retired on channel $\ge 1$ latches channel `0`'s garbage into `dmem_shadow` (confirmed in Probe 1C: 8 byte-lane assertion failures on a compliant 2-wide RV64 core).

#### 3.2 `Dromajo` Tandem Cosimulation Divergences & Override Semantics
`Basis: source`

While `riscv-formal` performs bounded model checking (typically $k \le 20$–$40$ cycles), `chipsalliance/dromajo` (`include/dromajo_cosim.h:61–79`, `src/dromajo_cosim.cpp:101–519`) runs billions of dynamic instructions (including full SMP Linux boots) in lockstep with Verilator or VCS via DPI-C. Direct inspection of `dromajo_cosim.cpp` establishes five exact boundary semantics that integrators frequently misconfigure:

1. **RVC 16-Bit Encoding Blind Spot (`dromajo_cosim.cpp:234–235, 441`):** `dromajo_cosim_step` masks compressed instructions in the emulator to 16 bits (`if ((emu_insn & 3) != 3) emu_insn &= 0xFFFF;`), but assumes the DUT supplies *post-expansion* 32-bit encodings. Line 441 therefore evaluates `emu_insn != dut_insn && (emu_insn & 3) == 3`—**completely skipping instruction-bits verification on every compressed instruction**! Bridging an unexpanded `RVFI` `rvfi_insn` port directly into `dromajo_cosim_step` works for `C` instructions only because the check is skipped, whereas `handle_dut_overrides` (`L141–151`) explicitly pattern-matches unexpanded `c.ld` (`0x6000`) and `c.lw` (`0x4000`)!
2. **Intentional Omission of `mstatus` Verification (`dromajo_cosim.cpp:434–453`):** Even though `dut_mstatus` is a mandatory parameter of `dromajo_cosim_step` and `emu_mstatus` is read on line 434, **neither is compared in the mismatch predicate (`L441–442`)** because OoO cores inconsistently report pre-commit vs. post-commit `mstatus.FS`/`SD` dirty bits on FP instructions versus `CSR` instructions (`L437–440`).
3. **Microarchitectural `SC.W`/`SC.D` Failure Override (`dromajo_cosim.cpp:237–244`):** If an RTL L1 cache eviction clears an `LR` reservation so the DUT's `SC` fails (`dut_wdata != 0`), Dromajo suppresses executing `SC` in its own RAM, writes `dut_wdata` to `rd`, and advances `pc <- emu_pc + 4`. Thus Dromajo catches *spurious `SC` successes* (`dut_wdata == 0` when `emu_wdata == 1`), but trusts *any* DUT `SC` failure without verifying liveness.
4. **CSR & Non-RAM MMIO Copy-Through (`dromajo_cosim.cpp:101–157`):** `handle_dut_overrides` overwrites Dromajo's `rd` with `dut_wdata` on reads (`rd != 0`) of `0xB00..0xB1F` (`mcycle`/`minstret`/`mhpmcounter*`), `0xC00..0xC1F` (`cycle`/`time`/`instret`), `0x344` (`mip`), `0x144` (`sip`), and any load/AMO whose physical address `pa` satisfies `riscv_cpu_pmp_access_ok` and `!get_phys_mem_range(s->mem_map, pa)`. DMA/accelerator writes into RAM require explicit `dromajo_cosim_override_mem` calls (`L468–519`).
5. **`GOLDMEM_INORDER` `LR`/`SC` Abort (`dromajo_cosim.cpp:354–366`):** Compiling `libdromajo_cosim` with `-DGOLDMEM_INORDER` enables strict load/store value checking, but `func5 == 0x02` (`lr`) and `func5 == 0x03` (`sc`) execute `fprintf(dromajo_stderr, "FIXME: implement ll/sc in goldmem\n"); exit(-3);`, terminating simulation immediately on atomic spinlocks.

#### 3.3 `cocotb` Stratified VPI/GPI Scheduling and Delta-Cycle Race Elimination
`Basis: source`

Hardware description languages execute a stratified event queue within each discrete timestep $t$. In `cocotb/cocotb` (`src/cocotb/share/lib/verilator/verilator.cpp:174–231`, `src/cocotb/_gpi_triggers.py:181–244`, and `src/cocotb/handle.py:752–911`), Python coroutines synchronize with RTL through four VPI callback phases (`VpiImpl.cpp:19–33`):

```text
Timestep t start
  ├─► cbNextSimTime        ──► cocotb NextTimeStep()
  ├─► cbAfterDelay         ──► cocotb Timer(...) [drives clock edges before iterative eval]
  ├─► Active / NBA loop:
  │     top->eval_step() -> doInertialPuts() -> VerilatedVpi::callValueCbs() [RisingEdge/ValueChange]
  ├─► cbReadWriteSynch     ──► cocotb ReadWrite(): flushes handle._apply_scheduled_writes() -> re-loops if evalNeeded()
  ├─► top->eval_end_step()
  └─► cbReadOnlySynch      ──► cocotb ReadOnly(): all signals stable; handle.value = x raises RuntimeError!
```

Two design mechanisms in `cocotb` 2.x govern Python-to-RTL determinism:
1. **Untrusted Simulator Inertial Queueing (`handle.py:788–846`):** Unless `COCOTB_TRUST_INERTIAL_WRITES=1` is set, assigning `dut.sig.value = x` (default `_GPISetAction.DEPOSIT`) after `await RisingEdge(dut.clk)` (which wakes during `cbValueChange` mid-Active region!) does **not** immediately mutate VPI signal memory. If it did, an RTL `always_ff @(posedge clk)` block not yet evaluated in that Active turn would sample the *new* `x` instead of the *old* pre-edge `x` (the classic Verilog `#0` hold-time race). Instead, `_schedule_write` buffers `(write_func, DEPOSIT, value)` in `_write_calls[handle]` (deduplicating multiple writes in the same timestep so last-write-wins) and primes a internal `ReadWrite()` callback whose `_do_callbacks()` (`_gpi_triggers.py:216–220`) flushes `_apply_scheduled_writes()` inside `cbReadWriteSynch` *after* Active clock-edge sampling completes. By contrast, `dut.sig.value = Immediate(x)` (`_GPISetAction.NO_DELAY`, `handle.py:752–775`) writes immediately in place, re-exposing nondeterminism across concurrent `always` blocks.
2. **Strict Phase Monotonicity (`_gpi_triggers.py:196–201, 222–227`; `handle.py:902–903`):** Once `await ReadOnly()` enters `cbReadOnlySynch`, `cocotb` enforces terminal stability in software: any `dut.sig.value = ...` raises `RuntimeError("Attempting settings a value during the ReadOnly phase.")`, and awaiting `ReadOnly()` or `ReadWrite()` from `ReadOnly` raises `RuntimeError("Attempted illegal transition: ...")`. A monitor coroutine sampling in `ReadOnly()` must `await RisingEdge(clk)`, `await Timer(...)`, or `await NextTimeStep()` before driving stimulus again.

---

### 4. Multi-Level Performance and Resource Footprint Analysis (`L1`–`L6`)
`Basis: documentation + source + execution + derived`

Across the hardware simulation, open place-and-route, formal BMC, and lockstep cosimulation stacks, performance and resource consumption trade off sharply across six engineering levels:

| Metric Level | `FireSim` (`FAME-1` + `FASED` on UltraScale+) | `Yosys` + `nextpnr` + `Project X-Ray` (XC7A35T–XC7K325T) | `riscv-formal` (`RVFI` + SymbiYosys / Boolector) | `Verilator` + `Dromajo` (C++/DPI Lockstep) | `cocotb` 2.x + `Verilator` (`GPI`/`VPI` Coroutines) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **(L1) Authoring & Maintenance Velocity** | Low extra RTL for standard SoCs (FIRRTL pass is automatic); custom C++/Chisel `BridgeModule` costs `300–1,200 LoC` (`~1–2` eng-weeks) and strict irrevocability proofs/tests. | Zero RTL change for portable HDL; adding a new FPGA family database costs `5k–25k LoC` of fuzzers (`prjxray/fuzzers/*`). | `RVFI` tracer wrapper costs `150–600 LoC` SV (`~0.1–0.3x` small-core LoC; tricky on OoO ROBs due to `mem_rdata`/CSR shadows). | DPI-C commit hook costs `80–250 LoC` C++/SV; maintaining custom CSR/MMIO address maps in `dromajo` costs `50–300 LoC` per SoC change. | High testbench velocity: Python coroutines + `scipy`/`scapy` cut UVM boilerplate by `3–8x` (`100–400 LoC` vs `1.5k+ LoC` SV-UVM); ideal for LLM/agent authoring (`<2k` tokens/test). |
| **(L2) Framework & Toolchain Build Time** | Heavy: Chisel/Scala/FIRRTL + C++ driver build takes `3–10 min` cold (`30–90 s` incremental); FPGA shell + Vivado synthesis/PnR takes **`2.5–6.5 hours`** per AFI. | Moderate: C++17 + Eigen + Boost `nextpnr` build takes `3–8 min` cold (`<5 s` ninja incremental); full `prjxray` fuzzing takes hours/days once per chip family, cached in `.db` text files (`<10 s` parse). | Fast: SystemVerilog/Yosys/SymbiYosys + `boolector`/`bitwuzla` C++ build takes `2–6 min` cold; `.sby` script generation takes `<1 s`. | Moderate: `Dromajo` builds in `15–40 s`; `Verilator` C++ generation + multi-threaded `clang++`/`g++` build takes `1–12 min` for Rocket/BOOM SoCs. | Fast Python side (`pip install` / `pygpi` C++ extension `<20 s`); dominated by simulator compile (`10 s` Icarus to `2–12 min` Verilator `--vpi`). |
| **(L3) Compilation, Elaboration & Synthesis Latency** | Golden Gate FIRRTL `FAMETransform` elaborates SoCs in `1–4 min`; physical Vivado place/route dominates (`150–390 min` batch latency, zero interactive loop). | `HeAP` CG solve + `Router2` completes `5k–50k` LUT designs in **`3–90 s`** (`5–15x` faster than vendor flows on small/mid designs); pathological >85% utilization congestion tails hit `5–20 min`. | Per-check SMT BMC (`k = 15–30` steps) finishes in `2–120 s` for `reg`/`pc` checks (`RISCV_FORMAL_ALTOPS`), but hits **exponential SMT `rlimit`/timeout cliffs (`>1 hr`)** on real 64-bit multipliers or deep OoO scoreboards. | Elaboration is `Verilator` Verilation (`10–90 s`) + C++ link (`20–300 s`); zero per-test synthesis when loading new RISC-V ELF binaries dynamically (`<10 ms`). | Zero Python compilation (`<100 ms` module import + VPI hierarchy discovery, cached via `_HierarchyObjectBase._discovered`, `handle.py:268–306`). |
| **(L4) Execution Throughput & Boundary Latency** | **`100–160 MHz`** single-node target rate (`~150 MHz` Rocket Chip); **`~3.4 MHz`** global barrier-synchronized 1,000-node datacenter simulation (`100–1,000x` faster than software RTL). | Native silicon speed once configured (`50–250 MHz` on 7-Series depending on critical-path slack; typically `10–25%` lower $f_{\max}$ than Vivado). | Static symbolic exploration (explores $2^{64}$ inputs implicitly up to depth $k$; equivalent explicit random coverage unreachable in centuries). | **`0.5–5 MHz`** RTL cycle rate (`1–15 MIPS` lockstep on single-core Rocket/BOOM); standalone `Dromajo` checkpoint generation runs at **`20–60 MIPS`**, DPI-C call costs `~5–15 ns`/retire. | **`20–150 kHz`** simulated clock when Python awaits `RisingEdge(clk)` every cycle (`~2–10 µs` per VPI->`pygpi`->Python coroutine switch + `_write_calls` flush); rises to `>1 MHz` only when clocks run in HDL/C++ and Python awaits coarse `Timer`/IRQ events. |
| **(L5) Verification / Certificate / DRC Checking Speed** | Runtime hardware `AssertTokenIrrevocable` & `SynthesizedAssertions` check at full `150 MHz` FPGA rate (`0` host overhead unless triggered). | `archcheck.cc` / `bind_and_check` validates net/wire/PIP exclusivity in **`<50 ms`** (`O(|W| + |P|)`), whereas `fasm2frames` checks `~10^5` FASM lines in `0.2–1.5 s` (missing unguarded two-hot shorts!). | Unsat BMC proofs are not exported as standalone kernel certificates by default (`boolector`/`bitwuzla` trusted); counterexample `.vcd` witness replay takes **`<50 ms`** in `gtkwave`/Icarus. | `dromajo_cosim_step` checks retired `(PC, insn, rd_wdata)` at **`5–20M` instructions/sec** per host core (`~50–180 ns`/insn interpreter + shadow sync); parallelizable across independent shards via snapshots. | Python scoreboard assertions check `10^4–10^5` transactions/sec (`~5–50 µs`/packet in pure Python). |
| **(L6) RAM, Disk & Silicon / Power Footprints** | Vivado build requires **`32–96 GB` Peak RSS**; `.afi`/bitstream is `30–90 MB`; FPGA host draws `40–120 W` per UltraScale+ card (`FAME-5` threaded BRAM cuts FPGA BRAM/LUT footprint by `2–4x` at proportional throughput cost). | `nextpnr` consumes **`0.4–4.5 GB` Peak RSS** (`flat_wires` preallocates `PerWireData` per chip wire, `router2.cc:207–239`); uncompressed XC7A35T `.bit` is **`2.19 MB`** (`17,536,096` bits; `101` words/frame). | `boolector`/`z3` BMC consumes **`0.5–16 GB` Peak RSS** per parallel `.sby` worker; `.vcd` failure traces are `0.2–5 MB`. | `Verilator` SoC binary is `5–40 MB` `.text` (`4–16 GB` C++ compile RSS on large `-O3` designs); `Dromajo` allocates guest RAM (`128 MB–4 GB` mmap) + `~15 MB` emulator state. | CPython + `libcocotbvpi` adds `40–120 MB` RSS overhead; `--trace-fst` waveform dumps grow at `5–100 MB/Mcycles` (`--trace-flush` degrades speed by `3–10x`, `verilator.cpp:137–138`). |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

#### 5.1 `(C1)` Human Comprehensibility and Mental-Model Ergonomics
`Basis: source + derived`

Evaluating human cognitive load—separately from how easily an LLM can emit syntactic boilerplate—exposes sharp ergonomic contrasts across these four interfaces:

- **Stratified Event Queues (`cocotb` / IEEE 1800) vs. Kahn Token Firing (`FAME-1`):** Although an LLM or human can write a `cocotb` coroutine in 15 lines of Python, **auditing delta-cycle race freedom requires holding 5–7 coupled concepts in human working memory simultaneously**: Active vs. NBA vs. `cbValueChange` vs. `cbReadWriteSynch` vs. `cbReadOnlySynch`, `Deposit` deferred queueing vs. `Immediate` writes, and whether `COCOTB_TRUST_INERTIAL_WRITES` is enabled (`handle.py:788–846`). When `ReadOnly` raises `RuntimeError`, the stack trace names the illegal phase transition cleanly (`_gpi_triggers.py:198–200`), making illegal post-stabilization writes highly legible—whereas an `Immediate` write during `RisingEdge` fails *silently* by shifting data by one clock cycle depending on simulator evaluation order. Conversely, `FAME-1`'s single-clock model requires just **two local concepts** (token availability and irrevocability), *except* at the multi-clock hub (`FAMETransform.scala:183–240`), where asymmetric `firedReg` resets (`1` vs. `0`), pipelined `enableReg` vs. combinational `inputChannelEnable`, and `MFMR` XDC exceptions create a steep nonlocal reasoning burden.
- **Counterexample Legibility (`RVFI` BMC vs. `Dromajo` Silent Overrides):** `riscv-formal` produces minimal, human-auditable `10–25`-cycle `.vcd` waveforms pinpointing the exact `rvfi_order` and shadow-register discrepancy—yet the bug in `rvfi_dmem_check.sv:37,39` illustrates a classic **specification-audit footgun**: packed flat vectors `[NRET * XLEN - 1 : 0]` force manual bit-slice arithmetic (`channel_idx * XLEN + i * 8 +: 8`) at every use site, so omitting the stride compiles cleanly without a width warning! Meanwhile, `Dromajo`'s `handle_dut_overrides` (`dromajo_cosim.cpp:120–157`) and skipped `mstatus`/RVC checks (`L437–442`) optimize for *uninterrupted Linux boot velocity* at the expense of **human auditability**: an engineer seeing `exit_code == 0` naturally assumes `mstatus` and compressed instruction words were verified, when both were silently ignored.

#### 5.2 `(C2)` Conceptual Simplicity, Orthogonality, and Universal Model Refinement
`Basis: derived`

Applying Ousterhout's *deep-module* test (small interface hiding rich guarantees) and Felleisen's *macro-expressibility* test (eliminating redundant primitives without pushing nonlocal adapter encodings onto consumers) separates genuine semantic invariants from realization-medium accidents:

1. **`LI-BDN` Token Channels as a Deep Module—and Where Clock-Tree Medium Quirk Leaks In:** Carloni's Latency-Insensitive Design and Tan's `FAME-1` achieve near-ideal conceptual unification: host DRAM stalls, PCIe DMA rings, and cross-FPGA Ethernet links all collapse into **one primitive**—the bounded irrevocable Kahn FIFO channel. The multi-clock `MFMR` XDC machinery (`FAMETransform.scala:208–240`) is *not* an essential semantic concept; it is an **FPGA clock-tree realization accident** caused by mapping rational target edges onto a shared physical `host_clock` net instead of synthesizing explicit per-domain token actors linked by synchronous CDC token FIFOs.
2. **Unifying `RVFI` and `Dromajo` via Explicit Non-Determinism Witness Channels:** `Dromajo` hardcodes ad-hoc opcode/CSR tables (`0xB00..0xB1F`, `0x344`, `is_store_conditional`, PMP-checked non-RAM loads) to guess when the DUT legitimately diverges from deterministic ISA execution, while `RVFI` uses flat bit-concatenated buses (`[NRET*XLEN-1:0]`) plus macro flags (`RISCV_FORMAL_ROLLBACK`, `RISCV_FORMAL_MEM_FAULT`). A **minimal, orthogonal retirement interface** replaces both ad-hoc opcode overrides and flat bit-slicing with an array of typed `RetirementPacket[NRET]` records carrying an explicit **environment-input witness sum type** `EnvEffect ∈ {Pure | ExternalLoad(pa, val) | FailedSC | AsyncInterrupt(cause) | CounterRead(csr, val)}`. Under this refinement:
   - Every deterministic instruction checks `(pc, raw_parcel_bits, arch_post_state)` uniformly (including 16-bit RVC parcels and post-commit `mstatus`, once FP dirty updates are architecturally specified);
   - Non-deterministic external inputs become **explicit, auditable environment transitions** verified against PMA/MMIO capability ranges rather than silent `rd` overwrites; and
   - Typed array indexing `pkt[ch].mem_wdata[b]` makes the `rvfi_dmem_check.sv` channel-0 bit-slice bug unrepresentable by construction.
3. **Refining `FASM` from Untyped Bit-Toggle Sets to Exclusive-Mux Algebraic Variants:** `FASM` treats every bitstream feature as an untyped set of bit assertions, forcing `segbits` authors to manually encode mutual exclusion via $O(N)$ negated `!bit` guards—and silently failing on two-hot crossbars (`WW2BEG0`) when `!` guards are omitted. Modeling each physical mux `Tile.DstWire` as a **single algebraic enum assignment** `Tile.DstWire := Off | Src(SrcWire)` in the bitstream IR makes multi-driver PIP contention syntactically impossible without inflating `segbits` files with quadratic negative bit lists.

## Boundaries

- **Multi-FPGA Switch Partitioning & `FAME-5` Register File Threading (`not examined`):** While `MultiThreadFAME5Models.scala` was inspected in the `firesim/firesim` tree, quantitative timing closure and cross-slot Aurora/QSFP switch-model token credit sizing across multi-FPGA deployments were `not examined` via hardware execution.
- **Vendor Bitstream DRC Completeness on UltraScale+ (`unknown`):** Xilinx UltraScale+ frame layouts and proprietary Vivado `[DRC]` bit-level checks used by AWS EC2 F1/F2 AFI ingestion are closed-source; whether all undocumented UltraScale+ two-hot interconnect mux combinations are rejected if crafted via post-route TCL `ROUTE` property edits remains `unknown` from public primary sources.
- **Superscalar `rvfi_dmem_check.sv` Bug Scope (`known not to apply` to `NRET == 1`):** The missing `channel_idx * RISCV_FORMAL_XLEN` bit offset in `checks/rvfi_dmem_check.sv:37,39` is **known not to apply** to single-issue cores (`RISCV_FORMAL_NRET == 1`), where `channel_idx == 0` identically reduces `0 * XLEN + i * 8` to `i * 8`.
- **RVV Vector & Hypervisor Lockstep in Upstream `Dromajo` (`unsupported`):** At `chipsalliance/dromajo` revision `8c0c1e3afd5cdea65d1b35872e395f988b0ec449`, `dromajo_cosim_step` (`include/dromajo_cosim.h:61–62`) passes a single scalar 64-bit `dut_wdata` per retired instruction; multi-register RISC-V Vector (`RVV 1.0`) writebacks and `-DGOLDMEM_INORDER` `LR`/`SC` atomics (`dromajo_cosim.cpp:360–365`, `exit(-3)`) are `unsupported` without extending the C ABI.
- **Zero-Overhead Per-Cycle Python Clocking in `cocotb` (`known not to apply`):** Claims that `cocotb` achieves native `Verilator` multi-megahertz simulation speeds **do not apply** when Python coroutines wake on `RisingEdge(clk)` every clock cycle; per-edge VPI callback marshaling and `_write_calls` scheduling cap throughput to `~20–150 kHz` unless clock generation and cycle-level transactors remain in HDL/C++.

## Evidence

### Primary Upstream Repositories and Normative Specifications

1. **`firesim/firesim` @ `9db588176c19e7252ed3027b2028bc21095f863a`** (observed `2026-11-19`):
   - `sim/midas/src/main/scala/midas/passes/fame/FAMETransform.scala:25–117, 123–376` — `FAME1Channel`, `FAME1InputChannel`, `FAME1OutputChannel`, `FAMEModuleTransformer` (`firedReg` reset asymmetry `L284–286`, multi-clock `(2, 3, 4)` `MFMR` counterexample and intra-domain `InternalXDCAnnotation` `L208–240`, `allFiredOrFiring` / `targetCycleFinishing` `L351–359`).
   - `sim/midas/src/main/scala/midas/passes/fame/WrapTop.scala:10–70` & `ChannelExcision.scala:12–149` — `FAMETop` wrapper and model-to-model / bridge-fanout channel port excision.
   - `sim/midas/src/main/scala/midas/core/Channel.scala:17–67, 106–229` — `PipeChannel`, `AssertTokenIrrevocable`, `SimReadyValidIO` (`fwd`/`rev` bifurcation), and `ReadyValidChannel`.
   - `sim/midas/src/main/scala/midas/models/dram/FASEDMemoryTimingModel.scala:30–250` — `BaseParams`, `AXI4EdgeSummary`, `FuncModelProgrammableRegs`, and `FASEDMemoryTimingModel`.
2. **`YosysHQ/nextpnr` @ `0f387c6a522a4e3aefe54b4d066e37548ccf9546`** (observed `2026-11-19`):
   - `common/place/placer_heap.cc:61–158, 175–260, 581–620, 901–1050` — `EquationSystem::solve` (`Eigen::ConjugateGradient`), `ControlSetState`, `HeAPPlacer::build_equations` bound-to-bound weights and spreading anchors, `StrictLegaliser`.
   - `common/route/router1.cc:78–175` & `common/route/router2.cc:51–260, 595–850, 1132–1350` — `Router2` wire reservation, criticality weighting `max(0.05, 1 - crit^2)`, `update_congestion` historical cost escalation and 3-failure bounding-box expansion, and `bind_and_check`.
3. **`f4pga/prjxray` @ `c9f02d8576042325425824647ab5555b1bc77833`** (observed `2026-11-19`):
   - `prjxray/fasm_assembler.py:25–164` — 101-word frame initialization (`word_addr >= 101` check), `frame_set`/`frame_clear` `FasmInconsistentBits` detection strictly on `1` vs. `0` collisions.
   - `docs/dev_database/common/segbits.rst:40–119` & `utils/test_data/db/segbits_int_l.db:1–13` — `segbits` syntax and actual `INT_L.WW2BEG0.LOGIC_OUTS_L12` (`11_14 12_14`) vs. `INT_L.WW2BEG0.LOGIC_OUTS_L4` (`09_14 15_14`) unguarded two-hot PIP rules.
4. **`YosysHQ/riscv-formal` @ `c992aa61fdfe0846c5ed90324c596202a1c69b76`** (observed `2026-11-19`):
   - `docs/source/rvfi.rst:1–350` — normative `RVFI`, `RISCV_FORMAL_ALTOPS`, `RISCV_FORMAL_ROLLBACK`, `RISCV_FORMAL_MEM_FAULT`, and `RVFI_BUS` specifications.
   - `checks/rvfi_reg_check.sv:15–55` vs. `checks/rvfi_dmem_check.sv:15–47` — properly offset `channel_idx * RISCV_FORMAL_XLEN` register check vs. unoffset `rvfi_mem_rdata[i*8 +: 8]` / `rvfi_mem_wdata[i*8 +: 8]` bug at lines `37` and `39`.
5. **`chipsalliance/dromajo` @ `8c0c1e3afd5cdea65d1b35872e395f988b0ec449`** (observed `2026-11-19`):
   - `include/dromajo_cosim.h:37–86` & `src/dromajo_cosim.cpp:101–531` — `is_mmio_load`, `handle_dut_overrides`, `dromajo_cosim_raise_trap`, `dromajo_cosim_step` (RVC skip `L234–235, 441`, `SC` override `L237–244`, `GOLDMEM_INORDER` `LR`/`SC` `exit(-3)` `L360–365`, omitted `mstatus` check `L434–442`), and `dromajo_cosim_override_mem`.
6. **`cocotb/cocotb` @ `c1faa6f710c8b389a659fd5d712422ea0739136a`** (observed `2026-11-19`):
   - `src/cocotb/_gpi_triggers.py:34–245`, `src/cocotb/handle.py:752–911`, `src/cocotb/share/lib/gpi/vpi/VpiImpl.cpp:19–33, 896–980`, and `src/cocotb/share/lib/verilator/verilator.cpp:174–231` — VPI callback mapping, `_write_calls` `ReadWrite` deferred flush, and `ReadOnly` write prohibition.

### Peer-Reviewed Literature

- Z. Tan et al., *"A Case for FAME: FPGA Architecture Model Execution,"* ISCA 2010, `DOI: 10.1145/1815961.1816002`.
- S. Karandikar et al., *"FireSim: FPGA-Accelerated Cycle-Exact Scale-Out System Simulation in the Public Cloud,"* ISCA 2018, `DOI: 10.1109/ISCA.2018.00014`.
- D. Biancolin et al., *"FASED: FPGA-Accelerated Simulation and Evaluation of DRAM,"* ACM/SIGDA FPGA 2019, `DOI: 10.1145/3289602.3293894`.
- A. Magyar et al., *"Golden Gate: Bridging The Resource-Efficiency Gap Between ASICs and FPGA Prototypes,"* ICCAD 2019, `DOI: 10.1109/ICCAD45719.2019.8942129`.
- D. Shah et al., *"Yosys+nextpnr: An Open Source Framework from Verilog to Bitstream for Commercial FPGAs,"* IEEE FCCM 2019, `DOI: 10.1109/FCCM.2019.00010`.
- D. Vercruyce, E. Vansteenkiste, and D. Stroobandt, *"CRoute: A Fast High-quality Timing-driven Connection-based FPGA Router,"* IEEE FCCM 2019, `DOI: 10.1109/FCCM.2019.00017`.
- J. Krautter, D. R. E. Gnad, and M. B. Tahoori, *"FPGAhammer: Remote Voltage Fault Attacks on Shared FPGAs, suitable for DFA on AES,"* IACR TCHES 2018(3), pp. 44–68, `DOI: 10.13154/tches.v2018.i3.44-68`.

### Reproducible Execution Micro-Probes

Running the self-contained Python 3 probe below reproduces (1A) `FAME-1` target-state invariance under `0` vs. `0..12`-cycle random host stalls, non-determinism under non-irrevocable bridges, and $\Delta h = 1$ back-to-back cross-clock firing on periods `(3, 4)`; (1B) `FasmAssembler`'s `0`-conflict acceptance of the multi-driver `WW2BEG0` PIP short from `prjxray`'s `segbits_int_l.db`; and (1C) the 8 byte-lane false failures triggered by `rvfi_dmem_check.sv` on a compliant `NRET = 2` superscalar store-then-load trace:

```python
#!/usr/bin/env python3
import random

# 1A: FAME-1 Multi-Clock Decoupling, Irrevocability & MFMR Cross-Domain Hazard
def run_fame1_sim(seed: int, max_stall: int, irrevocable: bool, n_target_tokens: int = 200):
    rng = random.Random(seed)
    schedule = [(t, t % 3 == 0, t % 4 == 0) for t in range(1, 400) if (t % 3 == 0 or t % 4 == 0)][:n_target_tokens]
    reg3 = reg4 = 0
    in3_fired, out4_fired = 1, 0  # FAMETransform.scala L285: input=1, output=0
    clk3_enabled_reg = clk4_enabled_reg = 0
    tok_idx = in3_token_idx = stall_cnt = host_cycle = 0
    last3 = last4 = -100
    min_intra3 = min_intra4 = min_cross = 999

    while tok_idx < len(schedule):
        host_cycle += 1
        _, c3_flag, c4_flag = schedule[tok_idx]
        if stall_cnt > 0:
            stall_cnt -= 1
            in3_valid = 0 if irrevocable else (host_cycle & 1)
        else:
            in3_valid = 1
        in3_bits = ((in3_token_idx + 1) * 17) & 0xFF if irrevocable else ((host_cycle * 17) & 0xFF)
        out4_ready = 1 if rng.randint(0, max_stall) == 0 else 0
        out4_valid = int(not out4_fired)
        out4_firing = out4_valid and out4_ready
        finishing = bool((out4_fired or out4_firing) and (in3_valid or in3_fired))
        in3_firing = bool(in3_valid and finishing and (not in3_fired))

        ce3 = bool(clk3_enabled_reg and finishing)
        ce4 = bool(clk4_enabled_reg and finishing)
        if ce3 and host_cycle - last4 == 1: min_cross = 1
        if ce4 and host_cycle - last3 == 1: min_cross = 1
        if ce3:
            min_intra3 = min(min_intra3, host_cycle - last3); last3 = host_cycle
            reg3 = (reg3 + in3_bits) & 0xFFFFFFFF
        if ce4:
            min_intra4 = min(min_intra4, host_cycle - last4); last4 = host_cycle
            reg4 = ((reg4 * 33) ^ reg3) & 0xFFFFFFFF
        if in3_firing:
            in3_token_idx += 1; stall_cnt = rng.randint(0, max_stall)

        in3_fired = (not c3_flag) if finishing else (in3_fired or in3_firing)
        out4_fired = (not bool(clk4_enabled_reg)) if finishing else (out4_fired or out4_firing)
        if finishing:
            clk3_enabled_reg, clk4_enabled_reg = int(c3_flag), int(c4_flag)
            tok_idx += 1
    return reg3, reg4, host_cycle, min_intra3, min_intra4, min_cross

r0 = run_fame1_sim(1, 0, True); r12 = run_fame1_sim(42, 12, True)
ba = run_fame1_sim(1, 3, False); bb = run_fame1_sim(2, 9, False)
print(f"[1A] Irrevocable stall=0 : reg3={r0[0]:#010x} reg4={r0[1]:#010x} host_cycles={r0[2]} intra_dh=({r0[3]},{r0[4]}) cross_dh={r0[5]}")
print(f"[1A] Irrevocable stall=12: reg3={r12[0]:#010x} reg4={r12[1]:#010x} host_cycles={r12[2]} exact_match={r0[:2]==r12[:2]}")
print(f"[1A] Non-irrevocable A vs B: reg4_A={ba[1]:#010x} vs reg4_B={bb[1]:#010x} deterministic={ba[:2]==bb[:2]}")

# 1B: Project X-Ray FasmAssembler on segbits_int_l.db (f4pga/prjxray @ c9f02d8576042325425824647ab5555b1bc77833)
seg_db = {
    "INT_L.IMUX_L1.EE2END0": [("22_09", 0), ("23_09", 0), ("25_09", 0), ("18_08", 1), ("24_09", 1)],
    "INT_L.IMUX_L1.EL1END0_SYNTH": [("22_09", 1), ("23_09", 0), ("24_09", 0), ("25_09", 0), ("18_03", 1)],
    "INT_L.WW2BEG0.LOGIC_OUTS_L12": [("11_14", 1), ("12_14", 1)],  # segbits_int_l.db:7
    "INT_L.WW2BEG0.LOGIC_OUTS_L4":  [("09_14", 1), ("15_14", 1)],  # segbits_int_l.db:13
}
def check_fasm(feats):
    frames, conflicts = {}, []
    for f in feats:
        for b, v in seg_db[f]:
            if b in frames and frames[b] != v: conflicts.append(b)
            else: frames[b] = v
    return conflicts, sorted(k for k, v in frames.items() if v == 1)

c_ww2, b_ww2 = check_fasm(["INT_L.WW2BEG0.LOGIC_OUTS_L12", "INT_L.WW2BEG0.LOGIC_OUTS_L4"])
c_imux, _ = check_fasm(["INT_L.IMUX_L1.EE2END0", "INT_L.IMUX_L1.EL1END0_SYNTH"])
print(f"[1B] Multi-driver PIP short on WW2BEG0: FasmInconsistentBits={len(c_ww2)}, active_bits={b_ww2}")
print(f"[1B] Zero-guarded 1-of-4 mux collision on IMUX_L1: FasmInconsistentBits={len(c_imux)} -> {c_imux[0]}")

# 1C: riscv-formal checks/rvfi_dmem_check.sv:37,39 superscalar (NRET=2) slice check
def sim_rvfi_dmem(buggy_upstream: bool):
    shadow, written, fails = [0]*8, [False]*8, []
    cycles = [
        {"valid": [1, 1], "addr": [0, 0x80001000], "rmask": [0, 0], "wmask": [0, 0xFF],
         "rdata": 0, "wdata": (0x0123456789ABCDEF << 64) | 0xDEADBEEFCAFEBABE},
        {"valid": [1, 0], "addr": [0x80001000, 0], "rmask": [0xFF, 0], "wmask": [0, 0],
         "rdata": 0x0123456789ABCDEF, "wdata": 0},
    ]
    for cyc, c in enumerate(cycles):
        for ch in range(2):
            if c["valid"][ch] and c["addr"][ch] == 0x80001000:
                for i in range(8):
                    off = (i * 8) if buggy_upstream else (ch * 64 + i * 8)
                    if ((c["rmask"][ch] >> i) & 1) and written[i]:
                        if shadow[i] != ((c["rdata"] >> off) & 0xFF):
                            fails.append((cyc, ch, i, hex(shadow[i]), hex((c["rdata"] >> off) & 0xFF)))
                    if (c["wmask"][ch] >> i) & 1:
                        shadow[i] = (c["wdata"] >> off) & 0xFF; written[i] = True
    return fails, bytes(shadow).hex()

fb, sb = sim_rvfi_dmem(True); ff, sf = sim_rvfi_dmem(False)
print(f"[1C] Upstream rvfi_dmem_check.sv (NRET=2): shadow={sb}, failures={len(fb)} first={fb[0]}")
print(f"[1C] Channel-offset fixed check  (NRET=2): shadow={sf}, failures={len(ff)}")
```

Recorded execution output on Linux `x86_64` (Python 3.13.5, `2026-11-19`):

```text
[1A] Irrevocable stall=0 : reg3=0x000042ea reg4=0xf3779a68 host_cycles=199 intra_dh=(1,2) cross_dh=1
[1A] Irrevocable stall=12: reg3=0x000042ea reg4=0xf3779a68 host_cycles=1946 exact_match=True
[1A] Non-irrevocable A vs B: reg4_A=0xca5db22b vs reg4_B=0x115a6bf0 deterministic=False
[1B] Multi-driver PIP short on WW2BEG0: FasmInconsistentBits=0, active_bits=['09_14', '11_14', '12_14', '15_14']
[1B] Zero-guarded 1-of-4 mux collision on IMUX_L1: FasmInconsistentBits=2 -> 22_09
[1C] Upstream rvfi_dmem_check.sv (NRET=2): shadow=bebafecaefbeadde, failures=8 first=(1, 0, 0, '0xbe', '0xef')
[1C] Channel-offset fixed check  (NRET=2): shadow=efcdab8967452301, failures=0
```

## Revalidation

To cheaply determine whether these findings still hold on newer upstream commits or target configurations without repeating full place-and-route or AFI synthesis:

1. **`FireSim` `FAME-1` Multi-Clock & Irrevocability Check (`<5 s`):** Diff `sim/midas/src/main/scala/midas/passes/fame/FAMETransform.scala` around `FAMEModuleTransformer` (`updateFiredReg`, `InternalXDCAnnotation`, and `genMetadata`) and `sim/midas/src/main/scala/midas/core/Channel.scala` (`AssertTokenIrrevocable`). Verify that generated clocks still carry `-divide_by 1` with intra-domain-only `set_multicycle_path`.
2. **`Project X-Ray` Unguarded Two-Hot PIP Short Check (`<2 s`):** Inspect `prjxray/fasm_assembler.py` (`frame_set` / `frame_clear`) to check whether destination-wire exclusivity (`<tile>.<dst_wire>.*`) has been added above raw bit collision checking, and grep any `segbits_int_*.db` file for pairs of lines sharing `<tile>.<dst_wire>.` that contain zero `!` tokens.
3. **`riscv-formal` `rvfi_dmem_check.sv` Superscalar Slice Check (`<1 s`):** Inspect `checks/rvfi_dmem_check.sv` lines `35–42`; if `rvfi_mem_rdata` and `rvfi_mem_wdata` still index `[i*8 +: 8]` without `channel_idx * \`RISCV_FORMAL_XLEN +`, the superscalar `NRET > 1` bug remains active.
4. **`Dromajo` & `cocotb` Contract Check (`<5 s`):** In `chipsalliance/dromajo/src/dromajo_cosim.cpp`, inspect `dromajo_cosim_step`'s final mismatch `if` statement and `handle_dut_overrides` to verify whether `dut_mstatus` or compressed `(emu_insn & 3) != 3` encodings are compared, and whether `#ifdef GOLDMEM_INORDER` still exits `-3` on `func5 == 2 || func5 == 3`. In `cocotb/src/cocotb/handle.py`, verify `_schedule_write` still defers `DEPOSIT` writes to `ReadWrite()` when `_trust_inertial` is false.
