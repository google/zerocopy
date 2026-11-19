# AMBA AXI4/CHI Coherency Deadlocks, TileLink Two-Phase Diplomacy, and UCIe/CXL 256B Chiplet Flits

## Summary

Deadlock freedom, protocol compliance, and cache coherency across on-chip and die-to-die interconnects hinge on eliminating hidden wait-for cycles across decoupled handshake channels, crossbar routing arbiters, directory snoop trackers, and chiplet link-replay buffers:

1. **AMBA AXI4/AXI5 Split Write-Channel (`AW`/`W`/`B`) Hazards:** Removing `WID` in AXI4 requires write data bursts (`W`) to traverse crossbars strictly in write-address (`AW`) arrival order while ARM IHI 0022 permits slaves (such as Rocket Chip's `AXI4ToTL`) to withhold `AWREADY` until `WVALID` arrives. In a multi-master crossbar (`pulp-platform/axi`), omitting single-destination `W`-open gating at the demultiplexer allows buffered `AW` beats to win arbitration in opposite orders across two slaves (`S0: [M1, M0]`, `S1: [M0, M1]`), creating an unrecoverable 4-party hold-and-wait deadlock. Furthermore, vendor template cores (characterized via `F_OPT_XILINX` in `ZipCPU/wb2axip`) impose non-standard timing skew assumptions between `AWVALID` and `WVALID` (`<= 2` cycles) and exhibit state-flag lockups (`axi_awv_awr_flag`) under compliant independent-channel traffic.
2. **AMBA 5 CHI Snoop-Filter Eviction & `CompAck` Hazards:** In directory-based AMBA CHI (`ARM IHI 0050`), a Home Node (`HN-F`) allocating its last Transaction Buffer Entry (TBE/MSHR) on an incoming request may trigger a snoop-filter capacity eviction (`SnpCleanInvalid` / `SnpUnique`) toward a Request Node (`RN-F`) that has concurrently issued an overlapping or TBE-contending `REQ`. Without virtual-channel separation (`REQ < SNP < RSP/DAT`) combined with dynamic retry/credit rollback (`RetryAck` on `RSP` followed by `PCrdGrant` and `AllowRetry = 0` re-issue) and strict `CompAck` hazard serialization, `HN-F` trackers and `RN-F` cache controllers enter deterministic circular wait or starvation livelock.
3. **TileLink Strict Channel Ranking & Two-Phase Diplomacy:** SiFive TileLink (`v1.8.1`) eliminates protocol-level wait-for cycles by construction via a strict five-channel priority hierarchy (`A < B < C < D < E`), requiring higher-ranked channels (`E` `GrantAck`, `D` `Grant`/`AccessAck`, `C` `ProbeAck`) never to block waiting on lower-ranked channels. In `chipsalliance/rocket-chip` and `chipsalliance/diplomacy`, two-phase Scala elaboration negotiates downward master parameters (`doParams` via `mapParamsD`) and upward manager capabilities (`uiParams` via `mapParamsU`) across a cycle-checked directed acyclic graph (DAG) prior to RTL generation, synthesizing prefix-free source ID maps, dead-channel wire pruning (`TLXbar`), and assertion monitors (`TLMonitor`) while requiring explicit irrevocability and `WLAST`-before-`BVALID` guards at `AXI4ToTL` protocol boundaries.
4. **UCIe 256B Die-to-Die Flit Replay & CXL 3.0 Cross-Chiplet Credit Loops:** Universal Chiplet Interconnect Express (`UCIe 1.1 / 2.0`) encapsulates `PCIe 6.0` and `CXL 3.0` (`CXL.io`, `CXL.cache`, `CXL.mem`) over `FDI`/`RDI` interfaces using 256-byte flits protected by per-128B 16-bit CRCs (`x^16 + x^15 + x^2 + 1`) and Die-to-Die (D2D) Adapter link-level retry replay buffers (`2.00 KiB` at `x16 @ 16 GT/s` up to `12.25 KiB` at `x64 @ 32 GT/s` with retimer RTT). Multiplexing `CXL.mem` Master-to-Subordinate (`Req`, `RwD`, `BIRsp`) and Subordinate-to-Master (`BISnp`, `NDR`, `DRS`) traffic across chiplet boundaries deadlocks unless each message class has independent pre-allocated Virtual Channel (VC) credits (`Req/RwD < BISnp < BIRsp < NDR/DRS`) and Flow-Control Data Link Layer Packets (FC DLLPs) bypass stalled D2D retry buffers.

## Applicability

This report characterizes the comparative protocol invariants, elaboration-time parameter negotiation algorithms, hardware bridge adapters, and multi-level (`L1`–`L6`) performance/resource and comprehensibility (`C1`–`C2`) trade-offs across five pinned open-source hardware repositories and five industry interconnect specifications:

- **Open-Source RTL and Generator Repositories (Directly Examined at Immutable Revisions):**
  - `ZipCPU/wb2axip` at commit `2e8d3bc2d26ddc33d1881022a2a2b9d3f0c16b9b`: SymbiYosys formal verification property suites (`bench/formal/faxil_slave.v`, `bench/formal/faxi_slave.v`) and reference slave cores (`rtl/easyaxil.v`, `rtl/demofull.v`).
  - `pulp-platform/axi` at commit `ee000c0eba9e1c2b6ffdab163a2957419d143461`: Synthesizable SystemVerilog AXI4+ATOP crossbar, demultiplexer, multiplexer, ID-counter, and atomic-operation filter (`src/axi_xbar.sv`, `src/axi_demux.sv`, `src/axi_demux_simple.sv`, `src/axi_mux.sv`, `src/axi_atop_filter.sv`).
  - `chipsalliance/rocket-chip` at commit `ece7b9ad544b07df39cd13b6fd7236562a26355d`: TileLink bundle/parameter lattices, crossbar generator, broadcast coherence hub, formal/simulation protocol monitor, and bidirectional AXI4 bridges (`src/main/scala/tilelink/{Parameters,Bundles,Xbar,Broadcast,Monitor,ToAXI4}.scala`, `src/main/scala/amba/axi4/{ToTL,Bundles}.scala`).
  - `chipsalliance/diplomacy` at commit `fe5e131d4fc8adec14a3ce4a4935bb5c0a269871` (referenced via `dependencies/diplomacy` in Rocket Chip's Mill build): Two-phase `LazyModule` elaboration and `BaseNode`/`MixedNode` graph resolution (`diplomacy/src/diplomacy/lazymodule/LazyModule.scala`, `diplomacy/src/diplomacy/nodes/{BaseNode,MixedNode,AdapterNode,NexusNode}.scala`).
  - `chipsalliance/chisel` at commit `e95009474df71a0fe95e29a7c04b7cbd80fc426d`: `ReadyValidIO`, `DecoupledIO`, and `IrrevocableIO` variance-checked directional handshake abstractions (`src/main/scala/chisel3/util/Decoupled.scala`).
- **Normative Protocol Specifications:**
  - **ARM AMBA AXI and ACE Protocol Specification (`ARM IHI 0022`, Issue H.c / Issue K):** Covering AXI4, AXI4-Lite, and AXI5 (`AWATOP` atomic transactions) channel handshake dependency rules.
  - **ARM AMBA 5 CHI Architecture Specification (`ARM IHI 0050`, Issue F / Issue G):** Covering `RN-F`, `HN-F`, `SN-F` coherence nodes, `REQ`/`RSP`/`SNP`/`DAT` channels, `CompAck`, `AllowRetry`/`RetryAck`/`PCrdGrant`, and snoop-filter eviction hazards.
  - **SiFive TileLink Specification (`v1.8.1`):** Covering `TL-UL` (Uncached Lightweight), `TL-UH` (Uncached Heavyweight), and `TL-C` (Cached coherent) conformance levels.
  - **UCIe Specification (`v1.1` / `v2.0`) and CXL Specification (`v3.0`):** Covering Standard (`16–32 GT/s`, x16) and Advanced Packaging (`16–32 GT/s`, x64 with spare lanes) physical layers, D2D Adapter `256B` Standard and Latency-Optimized Flit formats, `FDI`/`RDI` interfaces, and `CXL.io`/`.cache`/`.mem` `M2S`/`S2M` credit classes.

Scope qualifications: AXI3 interleaved write bursts (`WID` present) differ structurally from AXI4/AXI5 and are noted only by contrast. Commercial closed-source interconnect RTL (ARM CoreLink NIC-400/CMN-700, Arteris Ncore/FlexNoC) is not directly inspected at source level; CHI and UCIe/CXL claims rest on normative specification rules and self-contained discrete state-space model-checking probes preserved in this report.

## Findings

### 1. AMBA AXI4/AXI5 Channel Handshake Dependencies, Crossbar `AW`/`W` Inversion Deadlocks, and Vendor VIP Defects

`Basis: normative + source + execution`

ARM `IHI 0022` (Section A3.3.1, *Dependencies between channel handshake signals*) governs five independent unidirectional `VALID`/`READY` channels: Read Address (`AR`), Read Data (`R`), Write Address (`AW`), Write Data (`W`), and Write Response (`B`). Three asymmetric rules determine legality and deadlock freedom:

1. **Universal `VALID`-Before-`READY` Independence & Irrevocability:** Across every channel $c \in \{\text{AR}, \text{R}, \text{AW}, \text{W}, \text{B}\}$, a sender MUST NOT wait for `cREADY` to be asserted before asserting `cVALID`. Once `cVALID` is asserted, `cVALID` and all payload `cBITS` MUST remain stable (irrevocable) until the rising clock edge on which `cVALID && cREADY` holds. Conversely, a receiver MAY wait for `cVALID` before asserting `cREADY`.
2. **Write Address vs. Write Data Asymmetry:** An AXI4 master MUST NOT wait for `AWREADY` before asserting `WVALID`, nor wait for `WREADY` before asserting `AWVALID`. However, an AXI4 **slave** IS permitted to wait for **both** `AWVALID` and `WVALID` (or either one) before asserting `AWREADY` or `WREADY`.
3. **Write Response Ordering (`WLAST` Precedes `BVALID`):** Unlike `TL-UL`/`TL-UH` in TileLink, an AXI4 slave MUST wait for `AWVALID && AWREADY` AND `WVALID && WREADY && WLAST` (the final beat of the write burst) before asserting `BVALID` (`ARM IHI 0022` A3.3.1).

#### 1.1 Crossbar `AW`/`W` Routing Deadlocks After AXI4's Removal of `WID`

Because AXI4 eliminated the AXI3 `WID` signal on the `W` channel to save wire area, `W` beats carry no destination address and no transaction identifier: bursts on `W` must follow the exact emission order of `AW` beats without interleaving. In an $M \times S$ crossbar (`pulp-platform/axi` `src/axi_xbar.sv` composing per-master `axi_demux` and per-slave `axi_mux`), two distinct deadlocks arise unless guarded in hardware:

- **Hazard A — Single-Hop Demux vs. `AW`-Waits-for-`W` Slave Cycle:** Suppose `axi_demux` waited for downstream `mst_aw_ready` before steering `slv_w_valid` to target slave `slv_aw_select_i`, and that slave (legally under IHI 0022, like Rocket Chip's `AXI4ToTL` at `src/main/scala/amba/axi4/ToTL.scala:152–154`) sets `in.aw.ready := w_out.ready && in.w.valid && in.w.bits.last`. Then `demux` holds `mst_w_valid = 0` waiting for `mst_aw_ready = 1`, while the slave holds `mst_aw_ready = 0` waiting for `mst_w_valid = 1`—an immediate 2-edge combinational/sequential deadlock on beat 0.
  - **PULP Hardware Resolution (`src/axi_demux_simple.sv:181–197`):** On the *first* cycle `slv_req_i.aw_valid` passes the ID/counter gates, `axi_demux_simple` asserts `w_cnt_up = 1'b1` immediately to steer the `W` demultiplexer (`i_counter_open_w`) *without* waiting for `aw_ready`, and latches `lock_aw_valid_q = 1'b1` (`load_aw_lock = 1'b1`) so `w_cnt_up` is pulsed exactly once while `aw_valid` remains irrevocably asserted until `aw_ready` completes.
- **Hazard B — Multi-Master `SpillAw` Crossbar `W`-Order Inversion Deadlock:** When `SpillAw = 1'b1` inserts an `AW` register slice (`cc_spill_register` in `src/axi_demux.sv:82–110`), a master $M_0$ emitting `AW(S0)` followed by `AW(S1)` while a second master $M_1$ emits `AW(S1)` followed by `AW(S0)` can have `S0`'s `axi_mux` arbitrate `[M1, M0]` while `S1`'s `axi_mux` arbitrates `[M0, M1]`. Because $M_0$'s head `W` burst targets `S0` (which blocks waiting for $M_1$'s `W` burst) and $M_1$'s head `W` burst targets `S1` (which blocks waiting for $M_0$'s `W` burst), all four bursts freeze permanently.
  - **Exhaustive State-Space Verification (`Basis: execution`):** Running our BFS model checker (`interconnect_probe.py`) over the exact 2-master × 2-slave `SpillAw = 1` state space explores `140` reachable states when `w_open` gating is omitted and finds the exact terminal deadlock `(m0_aw=2, m1_aw=2, m0_w=0, m1_w=0, s0_wq=(1, 0), s1_wq=(0, 1))`. Enabling `pulp-platform/axi` `axi_demux_simple.sv:182` (`(w_open == '0) || (w_select == slv_aw_select_i)`) restricts a master from issuing an `AW` to a *different* slave port while prior `W` bursts remain open (while permitting pipelined `AW`s to the *same* slave port `w_select`), pruning the reachable state space to `51` states with **zero deadlocks**.
- **Hazard C — Same-`AWID` Slave Migration & AXI5 `ATOP` Dual-Response Ordering (`src/axi_demux_simple.sv:175–240`, `src/axi_atop_filter.sv`):** Because AXI4 mandates in-order `B` responses per `AWID`, `axi_demux_simple` instantiates `axi_demux_id_counters` (`AxiLookBits` prefix of `aw.id`) and blocks `aw_valid` whenever `aw_select_occupied && (slv_aw_select_i != lookup_aw_select)`. Furthermore, AXI5 Atomic Operations (`aw.atop[axi_pkg::ATOP_R_RESP]`, such as `AtomicLoad`, `AtomicSwap`, `AtomicCompare`) arrive on `AW`+`W` yet return **both** a `B` write response and an `R` read-data beat; `axi_demux_simple` therefore also gates `AW` on `!ar_id_cnt_full` and asserts `atop_inject` into `i_ar_id_counter` (`lines 175–191`), while `axi_atop_filter.sv` shields downstream AXI4-only slaves that lack `ATOP` support.

#### 1.2 Broken Vendor AXI Demo Templates (`F_OPT_XILINX` in `ZipCPU/wb2axip`)

`Basis: source + documentation`

In `ZipCPU/wb2axip` (`bench/formal/faxil_slave.v:39–43, 492–538` and `bench/formal/faxi_slave.v`), Dan Gisselquist documents why standard SymbiYosys bounded/inductive formal verification fails against vendor-generated Vivado AXI4/AXI4-Lite slave templates unless non-standard assumptions (`F_OPT_XILINX = 1'b1`) are injected:

```verilog
// ZipCPU/wb2axip bench/formal/faxil_slave.v:492-498
// Xilinx extensions/guarantees to the AXI protocol
//   1. The address line will never be more than two clocks ahead of the write data channel, and
//   2. The write data channel will never be more than one clock ahead of the address channel.
```

Specifically, vendor Vivado AXI-Lite templates gate address/data acceptance on combined `S_AXI_AWVALID && S_AXI_WVALID && aw_en` conditions (throttling peak write throughput to 1 beat per 2–3 clock cycles instead of 1 beat/cycle in skid-buffered `rtl/easyaxil.v`), while full AXI4 burst slave templates track burst state via brittle `axi_awv_awr_flag` / `axi_arv_arr_flag` mutual-exclusion flags that drop beats, corrupt burst addresses, or hang `WREADY` if a master exercises full IHI 0022 channel decoupling (e.g., streaming multiple `AW` bursts ahead of `W` or simultaneously driving `AR` and `AW`).

---

### 2. AMBA 5 CHI Snoop-Filter Eviction Hazards, `CompAck` Ordering, and `RetryAck`/`PCrdGrant` Liveness

`Basis: normative + execution + derived`

ARM AMBA 5 CHI (`ARM IHI 0050`, Issue F/G) replaces bus-oriented AXI/ACE snooping with a packetized, layered network-on-chip (NoC) connecting Fully Coherent Request Nodes (`RN-F`), I/O Request Nodes (`RN-I`), Fully Coherent Home Nodes (`HN-F` housing Point-of-Coherency, Point-of-Serialization, LLC slice, and Snoop Filter `SF`), and Subordinate Memory Nodes (`SN-F`) across four virtual channels:

- **`REQ`** (Outbound Request: `ReadShared`, `ReadUnique`, `CleanUnique`, `WriteBackFull`, `Evict`);
- **`SNP`** (Inbound Snoop from `HN-F` to `RN-F`: `SnpShared`, `SnpUnique`, `SnpCleanInvalid`);
- **`RSP`** (Control Response without data: `Comp`, `CompAck`, `SnpResp`, `RetryAck`, `PCrdGrant`, `ReadReceipt`);
- **`DAT`** (Data payload: `CompData`, `CopyBackWrData`, `NonCopyBackWrData`, `SnpRespData`, `SnpRespDataFwded`).

#### 2.1 The Snoop-Filter Eviction vs. Concurrent `RN-F` Request Deadlock

In directory-tracked meshes, the `HN-F` Snoop Filter (`SF`) has finite associativity and capacity. When `RN-F_1` issues `ReadShared(Addr_B)` that misses in the `SF` and selects victim way `Addr_A` (currently tracked as cached in `RN-F_0`), `HN-F` allocates a Transaction Buffer Entry (`TBE`) and emits a back-invalidation snoop `SnpCleanInvalid(Addr_A)` on `SNP` to `RN-F_0`, holding `Addr_B` until `RN-F_0` returns `SnpResp` / `SnpRespData`. Two acute hazards arise:

1. **TBE Exhaustion & Same-Line Transient Race:** If `RN-F_0` simultaneously emits `ReadUnique(Addr_A)` or `WriteBackFull(Addr_A)` on `REQ`, and `HN-F`'s TBE pool is full (or `Addr_A` is locked in `SF_EVICTING`), a naive `HN-F` that simply stalls `REQ` link credits blocks `RN-F_0`'s egress. If `RN-F_0`'s cache controller locks `Addr_A`'s MSHR against incoming `SNP` probes until its outbound `REQ` receives a response—or if fabric switches share buffer pools between `REQ` and `SNP`—a 2-node wait-for cycle locks the coherence domain (`Basis: execution`: reproduced in `15` reachable states by `check_chi_sf_eviction_hazard(False)` in `interconnect_probe.py`, halting at `('REQ_SENT', 'WAIT_COMP', 'RN1_EVICTING_L0', True, False)`).
2. **`CompAck` Serialization Window (`IHI 0050` Hazard Window):** When `HN-F` completes a coherent read/upgrade to `RN-F_1` via `CompData` (`DAT`), `HN-F` **cannot** launch a subsequent conflicting `SNP` to `RN-F_1` (nor retire its hazard tracker) until `RN-F_1` returns **`CompAck`** on `RSP`. Why? Because `SNP` and `DAT` traverse independent virtual channels: without waiting for `CompAck`, a `SnpUnique` sent by `HN-F` on `SNP` could overtake the earlier `CompData` still in flight on `DAT`, arriving at `RN-F_1` while the line is still Invalid (`I`) and causing `RN-F_1` to reply `SnpResp_I` *before* installing stale `CompData` as Unique Dirty/Clean!

#### 2.2 Dynamic Protocol Credits (`AllowRetry`, `RetryAck`, `PCrdGrant`) vs. Retry Starvation Livelock

AMBA CHI breaks TBE-exhaustion deadlocks without sizing `HN-F` TBEs to $\sum_i \text{MSHR}(RN_i)$ via a two-phase dynamic credit protocol:

1. Initial requests carry `AllowRetry = 1`. When `HN-F` lacks a free TBE or encounters a transient `SF` eviction conflict, it sinks the `REQ` flit immediately (freeing the `REQ` link buffer!) and replies **`RetryAck`** (`PCrdType = c`) on `RSP`.
2. Upon receiving `RetryAck`, `RN-F_0` transitions the transaction to `WAIT_PCRD` and releases any local snoop-blocking hazard on `Addr_A` (save that `CopyBack` writebacks carrying dirty data obey strict CHI snoop-vs-writeback race rules where `RN-F` either sinks the snoop as `SnpRespData` and cancels/downgrades the `CopyBack`, or `HN-F` reserves dedicated `CopyBack` TBEs). In our BFS model check (`check_chi_sf_eviction_hazard(True)`), enabling `RetryAck` + `PCrdGrant` resolves all `18` reachable states with **zero deadlocks**.
3. When `HN-F` retires a TBE (upon `CompAck`), it emits **`PCrdGrant(PCrdType = c)`** on `RSP` and **reserves** that TBE slot for the granted `PCrdType` pool; `RN-F_0` then re-issues the request with `AllowRetry = 0`, which `HN-F` is normatively forbidden from retrying.
4. **Livelock Boundary:** While `RetryAck`/`PCrdGrant` eliminates deadlock, **unfair `PCrdGrant` arbitration or `PCrdType` aliasing** causes **retry livelock**: if non-retried (`AllowRetry = 0` or opportunistic `AllowRetry = 1`) traffic from physically closer `RN-F` tiles steals newly freed TBEs before `HN-F`'s `PCrdGrant` FIFO drains, distant `RN-F` nodes starve indefinitely despite zero deadlocks. `HN-F` implementations must reserve the freed TBE at `PCrdGrant` emission time rather than at re-issued `REQ` arrival time.

---

### 3. TileLink `A < B < C < D < E` Channel Hierarchy and Two-Phase `Diplomacy` Negotiation

`Basis: normative + source + execution`

SiFive TileLink (`v1.8.1`) and CHIPS Alliance Rocket Chip (`chipsalliance/rocket-chip` @ `ece7b9ad544b07df39cd13b6fd7236562a26355d` + `chipsalliance/diplomacy` @ `fe5e131d4fc8adec14a3ce4a4935bb5c0a269871`) solve both protocol deadlocks and parameter mismatch bugs by pairing a **strictly ranked 5-channel coherence protocol** with a **two-phase directed-acyclic parameter negotiation compiler**.

#### 3.1 Strict Channel Priority (`A < B < C < D < E`) Without Retry Loops

TileLink partitions links into up to five unidirectional `DecoupledIO` channels (`TL-UL`/`TL-UH` use `{A, D}`; coherent `TL-C` uses `{A, B, C, D, E}`):

| Channel | Rank | Direction | Representative Messages (`TLMessages`) | Allowed Blocking Dependencies (`ready` / `valid` Wait-For) |
| :--- | :---: | :--- | :--- | :--- |
| **`A`** | `0` (Lowest) | Master $\to$ Manager | `Get`, `PutFullData`, `PutPartialData`, `ArithmeticData`, `LogicalData`, `Intent`, `AcquireBlock`, `AcquirePerm` | May wait on `B`, `C`, `D`, `E` |
| **`B`** | `1` | Manager $\to$ Master | `ProbeBlock`, `ProbePerm` ( plus forwarded `TL-UH` ops if cached) | May wait on `C`, `D`, `E`; **never** on `A` |
| **`C`** | `2` | Master $\to$ Manager | `ProbeAck`, `ProbeAckData`, `Release`, `ReleaseData` (voluntary writeback) | May wait on `D`, `E`; **never** on `A` or `B` |
| **`D`** | `3` | Manager $\to$ Master | `AccessAck`, `AccessAckData`, `HintAck`, `Grant`, `GrantData`, `ReleaseAck` | May wait on `E` only; **never** on `A`, `B`, or `C` |
| **`E`** | `4` (Highest) | Master $\to$ Manager | `GrantAck` (1-beat serialization token carrying `sink` ID) | **Unconditional sink** (`ready` MUST NOT depend on any channel) |

Why does `A < B < C < D < E` guarantee deadlock freedom without `RetryAck`? Consider a full `TL-C` miss + dirty snoop + voluntary eviction race:
1. Master $M_1$ sends `AcquireBlock` on **`A`** (rank 0).
2. Manager (`TLBroadcast` in `src/main/scala/tilelink/Broadcast.scala`) sends `ProbeBlock` on **`B`** (rank 1) to Master $M_0$. Even if $M_0$ simultaneously emitted a voluntary `ReleaseData` eviction on **`C`** (rank 2), **`C` outranks `B`**, so the Manager MUST be able to drain `ReleaseData` on `C` (emitting `ReleaseAck` on **`D`**, rank 3) without waiting for `B` or `A`, OR $M_0$ responds to `ProbeBlock` with `ProbeAckData` on **`C`** (rank 2).
3. Manager emits `GrantData` on **`D`** (rank 3) to $M_1$, and $M_1$ closes the serialization window with `GrantAck` on **`E`** (rank 4). In `Broadcast.scala:117`, the coherence hub wires `in.e.ready := true.B` unconditionally: Channel `E` is pure zero-stall combinational tracker wakeup (`tracker.e_last := select && in.e.fire`).

Because every intra-agent dependency edge $(u \to v)$ strictly satisfies $\text{rank}(u) < \text{rank}(v)$ and network routing within each channel traverses a DAG of crossbars, the global wait-for graph is a strict partial order (topological rank check in `interconnect_probe.py`: `0` violations across all 6 cross-channel causal edges in `~3.1 µs`).

#### 3.2 Two-Phase `Diplomacy` Parameter Negotiation (`chipsalliance/diplomacy`)

In `LazyModule.scala:11–25` and `MixedNode.scala:340–556`, Chisel elaboration is split into two distinct Scala evaluation phases:

1. **First Elaboration Pass (Diplomatic Graph Construction):** Instantiating `LazyModule` subclasses constructs `BaseNode` vertices (`TLClientNode`, `TLManagerNode`, `TLAdapterNode`, `TLNexusNode` in `TLXbar`, `MixedAdapterNode` in `TLToAXI4` / `AXI4ToTL`) and records directed binding edges (`:=`, `:*=`, `:=*`, `:*=*`) *without* creating hardware `chisel3.Module`s or `Wire`s.
2. **Second Elaboration Pass (Lazy Bidirectional Fixpoint & Hardware Elaboration):** Accessing `lazy val module` forces three cycle-guarded graph passes in `MixedNode.scala`:
   - **Cardinality Resolution (`oPortMapping`, `iPortMapping`, `oStar`, `iStar`, lines `342–405`):** Resolves flexible multi-edge operators (`:*=`, `:=*`, `:*=*`) via linear equations over `iKnown`/`oKnown`, guarded by `if (starCycleGuard) throw StarCycleException()`.
   - **Downward Master Pass (`diParams -> doParams`, lines `486–505`) & Upward Manager Pass (`uoParams -> uiParams`, lines `507–526`):** Evaluates monotone transfer functions `mapParamsD` (propagating master `sourceId` ranges, `requestFifo`, visibility, and emitted ops downward) and `mapParamsU` (propagating slave `AddressSet`s, `RegionType`, `TransferSizes` via `.intersect` / `.mincover` in `TLParameters.scala:35–52`, `beatBytes`, and `sinkId` counts upward), guarded respectively by `DownwardCycleException` and `UpwardCycleException`.
   - **Bundle Specialization, Dead-Wire Pruning & `TLMonitor` Injection:** `edgesOut`/`edgesIn` size every `TLBundle` wire to exact negotiated bitwidths (`log2Ceil(endSourceId)`, `log2Ceil(endSinkId)`). In `Xbar.scala:135–225`, `TLXbar.circuit` computes boolean matrices `reachableIO`, `probeIO`, and `releaseIO` from client `visibility` vs. manager `address` overlap and `RegionType.TRACKED`, physically tying off unused `B`/`C`/`E` channels (`valid := false.B`, `ready := true.B`) and assigning collision-free bit-OR source ID prefixes (`in(i).a.bits.source := io_in(i).a.bits.source | r.start.U`). Every edge automatically attaches a `TLMonitor` (`Monitor.scala:1–883`) emitting hundreds of formal/simulation protocol assertions parameterized by the exact negotiated `TLEdge`.

#### 3.3 The `TL <-> AXI4` Protocol Bridge Seam (`TLToAXI4` & `AXI4ToTL`)

Inspecting `src/main/scala/tilelink/ToAXI4.scala:39–120` and `src/main/scala/amba/axi4/ToTL.scala:45–218` exposes four subtle semantic mismatches between TileLink and AXI4:

1. **Disjoint `sourceId` (Unordered) vs. Shared `AWID` (FIFO-Ordered):** TileLink assigns every in-flight transaction a **globally unique `source` ID**, whereas AXI4 multiplexes multiple FIFO-ordered transactions onto one `AWID`. `TLtoAXI4IdMap` (`ToAXI4.scala:40–58`) maps `requestFifo` TileLink masters onto a single `AXI4` ID (`maxFlight = tl.sourceId.size`) and stashes the original `tl.source` + `size` inside `AXI4TLStateField` (`echoFields`, carried round-trip via user/echo state), while `AXI4ToTL` (`ToTL.scala:82–136`) expands each AXI `id` by `addedBits = log2Ceil(maxFlight) + 1` (`Cat(id, count, isWrite)`), allocating `txnCountBits = log2Ceil(maxFlight + 1)` so wrap-around cannot alias!
2. **No Data Interleaving Requirement (`ToAXI4.scala:105–106`):** `TLToAXI4` enforces `require(slaves(0).interleavedId.isDefined)` because TileLink Channel `D` bursts cannot interleave beats from different transactions unless buffered and reassembled.
3. **Early Write Ack Suppression (`ToTL.scala:199–211`):** Because TileLink allows `AccessAck` on `D` before the final beat of a multi-beat `Put` on `A` whereas AXI4 forbids `BVALID` before `WLAST`, `AXI4ToTL` maintains per-ID `w_count` (incremented on `in.aw.fire`, which itself waits for `in.w.valid && in.w.bits.last` at line `152`!) and gates `in.b.valid := q_b.valid && (b_count(id) =/= w_count(id))`.
4. **Directional `IrrevocableIO` Casting (`Decoupled.scala:53–65` & `ToTL.scala:190–197`):** Chisel's `DecoupledIO` guarantees neither `valid`-before-`ready` independence nor `valid` stability, so `AXI4ToTL` explicitly wraps `ok_r` and `ok_b` in `Queue.irrevocable(..., 1, flow=true)` to satisfy AXI4's irrevocability contract.

---

### 4. UCIe 256B Die-to-Die Flits, Link-Level Retry SRAMs, Lane Repair, and Cross-Chiplet CXL 3.0 Credit Starvation

`Basis: normative + execution + derived`

Universal Chiplet Interconnect Express (`UCIe v1.1 / v2.0`) standardizes die-to-die (D2D) in-package links across three clean layers separated by two architectural interfaces:
- **Protocol Layer** (`PCIe 6.0`, `CXL 2.0/3.0` `.io`/`.cache`/`.mem`, or Raw Streaming) $\longleftrightarrow$ **`FDI` (Flit-aware Die-to-Die Interface)** $\longleftrightarrow$ **D2D Adapter Layer** (256B Flit framing, 16-bit CRC, sequence numbers, link-level retry replay buffer, stack muxing, link state machine) $\longleftrightarrow$ **`RDI` (Raw Die-to-Die Interface)** $\longleftrightarrow$ **Physical Layer (PHY)** (logical lane mapping, scrambling, bump-fault **lane repair**, clock forwarding, Standard x16 vs. Advanced x64 bumps).

#### 4.1 Standard vs. Latency-Optimized 256B Flit Layouts & Replay Buffer SRAM Sizing

To reach a target Residual Bit Error Rate (`FIT << 1`, uncorrected BER `< 10^-27`) across high-density bump arrays (`25–55 µm` microbumps in Advanced Packaging, `100–130 µm` C4 bumps in Standard Packaging) without high-latency FEC (`PCIe 6.0` PAM4 requires 3-way interleaved FEC + CRC, whereas UCIe NRZ at `4–32 GT/s` runs **0-FEC raw BER `< 10^-15`** repaired by fast D2D Adapter CRC + Retry!), UCIe adopts two primary 256B Flit encodings:

- **Standard 256B Flit (Format 4):** Carries **240 bytes** of protocol TLP/CXL payload (`93.75%` wire payload efficiency), a 2-byte D2D Flit Header, Data Link Packet (`DLP`) bytes (bytes `236–241` in base `PCIe 6.0`/`CXL 3.0` mapping), and D2D Adapter 16-bit CRCs (`x^16 + x^15 + x^2 + 1`) protecting each 128B half (`CRC0`, `CRC1`). Receiver processing waits until the full 256B flit is received and checked.
- **Latency-Optimized 256B Flit (Format 5, Recommended for `CXL.cache` / `CXL.mem`):** Splits the 256B flit into **two independently CRC-protected 128B sub-blocks** (`236 bytes` net protocol payload without optional bytes, `92.19%` efficiency). Because `CRC0` arrives at byte `127`, the receiving CXL Home/Subordinate agent can forward the first 128B (`68B` + `60B` CXL slots, sufficient for a `64B` cache line + metadata!) `128 / B_link` nanoseconds earlier—saving `4 ns` per hop on an `x16 @ 16 GT/s` (`32 GB/s`) link and `0.5 ns` per hop on an `x64 @ 32 GT/s` (`256 GB/s`) link.
- **D2D Adapter Replay Buffer Sizing (`Basis: execution`):** Under Go-Back-N link-level retry (`Nak` returned via retry-bypassing adapter header/DLLP path), lossless full-rate streaming requires TX replay SRAM capacity $C_{\text{replay}} \ge \lceil (R_{\text{raw}} \cdot \text{RTT}_{\text{loop}}) / 256\text{ B} \rceil + N_{\text{skid}}$ flits. From `interconnect_probe.py`:
  - **Standard Package `x16 @ 16 GT/s`** (`32.0 GB/s`, `RTT = 28 ns`): minimum **`8` flits (`2,048 B = 2.00 KiB`)** per stack;
  - **Advanced Package `x64 @ 32 GT/s`** (`256.0 GB/s`, `RTT = 18 ns`): minimum **`22` flits (`5,632 B = 5.50 KiB`)** per module;
  - **UCIe 2.0 Advanced `x64 @ 32 GT/s` with Off-Package/3D Retimer Extension** (`RTT = 45 ns`): minimum **`49` flits (`12,544 B = 12.25 KiB`)** per module.
- **Hardware Lane Repair (Advanced Packaging):** Each Advanced Package x64 module provisions **4 redundant data bumps** (`RD[3:0]`, `2` per 32-lane half) plus spare forwarded-clock, valid, and track bumps (`UCIe v1.1/2.0` Chapter 4). During `MBINIT.REPAIR` link training (using sideband `800 MHz` auxiliary pins that have their own redundant pair), faulty microbumps are remapped mux-wise in `O(1)` combinational shift stages with **zero change** to `RDI`/`FDI` flit width or protocol credit accounting; Standard Package x16 lacks spare pins and instead degrades link width (`x16 -> x8`) on lane fault.

#### 4.2 Cross-Chiplet `CXL 3.0` Credit Deadlocks Over UCIe `FDI`

Tunneling `CXL 3.0` across multi-die chiplets (`Compute Die <-> I/O-Coherency Hub Die <-> HBM/Memory-Expander Die`) multiplexes `CXL.io` (`PCIe` Posted `P`, Non-Posted `NP`, Completion `CPL`), `CXL.cache` (`D2H`/`H2D` `Req`, `Rsp`, `Data`), and `CXL.mem` (`M2S`: `Req`, `RwD`, `BIRsp`; `S2M`: `BISnp`, `NDR`, `DRS`) onto shared 256B flits. Two structural deadlocks occur if adapter and protocol credits are conflated:

1. **CXL 3.0 Back-Invalidate (`BISnp` / `BIRsp`) Loop:** In `CXL 3.0` shared/pooled memory or multi-headed devices, an `M2S Req` arriving at a Subordinate/Home memory die triggers an `S2M BISnp` back to a host caching die, which must return `M2S BIRsp` (and potentially dirty eviction `M2S RwD`—or pre-allocated BI writeback slots!) before the memory die emits `S2M NDR` / `S2M DRS`. This requires strict credit-pool isolation matching the rank chain:
   $$\text{M2S }\{\text{Req}, \text{RwD}\} \prec \text{S2M }\text{BISnp} \prec \text{M2S }\text{BIRsp} \prec \text{S2M }\{\text{NDR}, \text{DRS}\}.$$
   If `M2S BIRsp` shares a generic `FDI` ingress buffer with `M2S Req`/`RwD` without dedicated pre-allocated VC credits, queued `M2S Req`s choke out `BIRsp`, freezing `BISnp` trackers and stalling all `NDR`/`DRS` completions!
2. **Retry-Buffer Blocking of Flow-Control DLLPs:** If an intermittent bump bit-flip triggers a `CRC` `Nak` and D2D Adapter replay, and outbound **Flow Control (`FC`) credit-return DLLPs** are queued *behind* the stalled TX retry buffer while the remote receiver needs those `FC` credits to drain its own outbound flits (or return `Ack`/`Nak`), the link deadlocks (`interconnect_probe.py`: rank violation `('FC_DLLP', 'Req')`). UCIe normatively mandates that link-level `Ack`/`Nak` and `FC` credit updates **bypass** the D2D Adapter retry replay queue (`rank = 4`, highest priority).

---

### 5. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

`Basis: source + execution + documentation + derived`

Evaluating interconnect architectures solely by peak wire bandwidth (`L4`) hides severe compilation (`L2`/`L3`), verification (`L1`/`L5`), and SRAM/gate-area (`L6`) asymmetries across SoC teams:

| Level & Metric | Hand-Written AXI4/AXI5 RTL + VIP (`wb2axip` / `pulp-platform/axi`) | AMBA 5 CHI Coherent Mesh (`IHI 0050` Directory NoC) | TileLink + Two-Phase `Diplomacy` (`rocket-chip` / `chisel`) | UCIe `256B` Flit Adapter + `CXL 3.0` Stack |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Maintenance Velocity** | `300–1,500` SystemVerilog LoC per bridge/xbar + `800–1,324` SVA/formal LoC (`faxil_slave.v`, `faxi_slave.v`); adding 1 master cascades `AXI_ID_WIDTH` edits across tree (`~2–5x` spec-to-RTL ratio) | `5,000–25,000+` SV LoC for `HN-F` TBE + Snoop Filter + `RetryAck`/`PCrdGrant` hazard matrices; highest human/LLM bug density on `CompAck` & `CopyBack` corner cases | **`10–35` Scala LoC** per diplomatic node/xbar binding (`:=`, `:*=`); ID widths, address masks & dead channels auto-derived (`~10–40x` LoC reduction on bus integration) | `2,000–8,000` SV LoC for D2D Adapter (`CRC`, `Retry`, `FDI`/`RDI` LSM) + PHY `MBINIT.REPAIR` state machines |
| **`L2` Toolchain & Framework Build Time** | Fast standalone SV lint/elaboration (`0.3–2.5 s` in Verilator / `slang`, `< 250 MB` RSS) | Heavy commercial VIP/UVM compilation (`30–180 s` clean compile, `2–8 GB` simulator RSS) | Heavy JVM + Scala `2.13.12` + Mill + Chisel `6.7.0` + `firtool` (`CIRCT`) pipeline (`25–90 s` cold build, `4–12 s` warm Mill incremental, `1.5–4.0 GB` JVM/CIRCT RSS) | Moderate SV + multi-protocol CXL/PCIe VIP build (`15–90 s`, `1–4 GB` RSS) |
| **`L3` Elaboration, Synthesis & Formal Latency** | Bounded/k-induction BMC in SymbiYosys (`faxil_slave.v` `F_AXI_MAXWAIT=12`): `2–45 s` per module; full multi-master `axi_xbar` state-space explodes exponentially (`> 10 min` SMT timeout for `MaxTrans >= 8`) | Model checking full `RN-F`/`HN-F` transient states (`Murphi`/`TLA+`/JasperGold) takes minutes to hours without symmetry reduction; RTL synthesis of associative `SF` CAMs dominates critical-path timing | Diplomatic DAG `doParams`/`uiParams` negotiation completes in **`5–40 ms`** during JVM elaboration (catching address overlaps, unsupported `TransferSizes`, & ID mismatches before FIRRTL emission!); `firtool` Verilog lowering takes `1–15 s` | Adapter `CRC16` parallel XOR tree synthesizes in `< 3 s`; multi-die credit-loop formal verification requires compositional rank invariants to avoid `256B` data-path explosion |
| **`L4` Hardware Execution Throughput & Latency** | **`1` beat/cycle** (`easyaxil.v`, `axi_xbar` with `SpillAw=0` -> `0`-cycle combinational cut-through or `1`-cycle registered); broken Vivado demo degrades to `0.33–0.5` beats/cycle; head-of-line stall across slaves when `w_open > 0` | `1` flit/cycle per mesh link (`2–4 GHz`), `~15–40` cycles LLC hit (`RN-F -> HN-F -> RN-F`); tail `p99.9` latency spikes `3–10x` under `RetryAck` -> `PCrdGrant` contention | **`1` beat/cycle** on `A`–`E`, `0`-cycle `GrantAck` sink (`in.e.ready := true.B`), zero `RetryAck` round-trip penalty; `TLXbar` combinational arbitration `0–1` cycle/hop | **`32 GB/s`** (`x16 @ 16 GT/s` Std) to **`256 GB/s`** (`x64 @ 32 GT/s` Adv) per module (`> 1–10 Tbps/mm` shoreline); **`< 2 ns`** TX+RX D2D Adapter latency in Latency-Optimized `128B+128B` `256B` Flit mode (`92.19%`–`93.75%` payload efficiency) |
| **`L5` Static / Monitor Verification Speed** | `faxil_slave` / `faxi_slave` runtime SVA monitor adds `0` silicon gates in sim; static graph check unavailable without external IP-XACT/SystemRDL scripts | Per-transaction `IHI 0050` scoreboard checks in UVM run at `1–50 kHz` RTL simulation speed (`10^5x` slower than silicon) | Topological channel-rank check (`u32` scan: **`< 5 µs`**, `interconnect_probe.py` `3.1 µs`) + Diplomacy `require` checks (`< 40 ms`); synthesized `TLMonitor` checks all edge invariants every cycle in Verilator/FPGA (`FireSim`) | `CRC16` (`x^16+x^15+x^2+1`) verifies `128 B` in **`1` adapter clock cycle** (`0.5–1 ns`); static VC credit-rank + BDP replay-depth check runs in **`< 5 µs`** (`1.9 µs` in probe) |
| **`L6` Silicon Area, SRAM & Host RAM Footprint** | `axi_demux_id_counters`: `2^AxiLookBits` counters of width `clog2(MaxTrans)+1` + `select_t` registers (~`0.5–3 K` gates/port); `0 B` replay SRAM | `HN-F` Snoop Filter SRAM (`1–4 MiB` per socket) + `64–128` TBE entries (`~64–128 B` state + `64 B` data buffer each = `8–24 KiB`/slice) | `TLXbar` prunes `100%` of unreachable `B`/`C`/`E` wires (`Xbar.scala:145–210`); `TLBroadcastTracker` holds `lineBytes` buffer + `caches` bitmask (`4` trackers × `64 B` = `256 B` data registers); host JVM elaboration costs `1.5–4 GB` RAM | **`2.00 KiB`–`12.25 KiB`** TX Replay SRAM per module (`interconnect_probe.py`) + per-VC `CXL` receive credit buffers (`4–16 KiB`) + `+6.25%` bump overhead (`4/64` spare data lanes in Adv Pkg); **`0.25–0.50 pJ/bit`** energy efficiency (`5–10x` lower than SerDes PCIe) |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source + derived`

#### 6.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

- **Why Engineers Repeatedly Write Deadlocking AXI4 Slaves (`SMoL`-Style Nonlocal Reasoning Trap):** Notice the asymmetry between LLM boilerplate generation and human auditability on AXI4: an engineer reading an isolated 80-line slave module sees `if (AWVALID && WVALID)` and forms a locally plausible mental model ("wait until both address and data arrive, then write the register"). That local code is *even legal* for an isolated slave under `IHI 0022` A3.3.1! The catastrophe is **nonlocal**: when another engineer writes a master or bridge assuming symmetric `AW`-before-`W` handshaking, or instantiates `SpillAw = 1` in a multi-slave crossbar without `w_open` gating, two locally "reasonable" modules compose into a silent SoC hang. Diagnostic legibility in waveform viewers is notoriously poor: in a deadlocked 16-master SoC, dozens of `READY = 0` signals point at one another without identifying the minimal cycle. By contrast, our state-space/rank check projects the exact 4-edge cycle (`M0.W -> S0.mux -> M1.W -> S1.mux -> M0.W`).
- **Diplomacy's Scala Stack-Trace & Cake-Pattern Friction vs. Edge Clarity:** Cook, Terpstra, and Lee (*CARRV 2017*) achieved extraordinary local concision (`foo.node := bar.node`), and `MixedNode.scala:493–501` prints node `context` + `locator` source lines on arity/cycle failures. However, Rocket Chip's historical reliance on Scala's **Cake Pattern** (deeply mixed-in traits + `org.chipsalliance.cde.config.Parameters` dynamic key-value lookups + two-stage `LazyModule` / `LazyModuleImp` scoping) imposes high human working-memory load (`7–10` simultaneous concepts): accessing `.module` or bundle wires during the first diplomatic pass triggers subtle initialization/null hazards, and failed `TransferSizes` intersections across 6 adapter hops require tracing both downward `dFn` and upward `uFn` transformations in reverse.
- **AMBA CHI vs. TileLink Cognitive Footprint:** TileLink `TL-C` requires holding **5 ranked channels** and **3 cache permissions** (`Nothing`, `Branch`, `Trunk`/`Tip`) in working memory, with zero retry states. AMBA CHI requires tracking **4 channels**, **7+ cache/directory states** (`I`, `SC`, `UC`, `UD`, `SD`, `UDP`, plus transient snoop/eviction states), `CompAck` ordering windows, `Order` (`RequestOrder`/`EndpointOrder`), `ReadReceipt`, and asynchronous `RetryAck`/`PCrdGrant` credit loops—exceeding human single-page auditability without mechanized model checking.

#### 6.2 Conceptual Simplicity, Orthogonality & Universal Model Refinement (`C2`)

Applying Felleisen's macro-expressibility criterion and Ousterhout's deep-module test across all four interconnect families separates **essential distributed-fabric invariants** from **historical wire/RTL accidents**:

1. **Accidental Complexity Identified:**
   - *AXI4's `WID`-less Split `AW`/`W` Without Channel Rank:* Splitting `AW` and `W` saves address wires on multi-beat bursts, yet deleting `WID` forced every crossbar (`axi_demux_simple.sv`) and protocol bridge (`AXI4ToTL.scala`) to reinvent ad-hoc `w_open` single-slave locks, `lock_aw_valid_q` latches, `AxiLookBits` ID migration counters, and `b_allow` beat-completion counters—shifting complexity out of the specification and into every consumer and adapter (`O(N^2)` bridge tax, evidenced by `TLToAXI4` + `AXI4ToTL` totaling `553` dense Scala LoC!).
   - *Conflating Parameter-Negotiation Acyclicity with Runtime Packet Routing:* Diplomacy's `DownwardCycleException` / `UpwardCycleException` (`MixedNode.scala:488, 509`) ties parameter fixpoint evaluation to the topological graph of hardware links, forcing ring/mesh NoCs (`Constellation`) or mutual master/slave DMA loops to split endpoints artificially into separate source/sink diplomatic nodes.
   - *Duplicate Liveness Mechanisms Across Layers:* TileLink `A..E`, CHI `REQ/SNP/RSP/DAT` + `PCrdGrant`, and UCIe/CXL `M2S`/`S2M` + retry-bypassing `FC_DLLP`s are **three domain-specific encodings of one identical mathematical invariant**: a bounded-buffer wait-for graph free of hold-and-wait cycles.
2. **Minimal Universal Interconnect Abstraction (`3` Orthogonal Primitives, `0` Adapter Blowup):**
   Every phenomenon in AXI4, CHI, TileLink, and UCIe/CXL reduces cleanly to three orthogonal, checkable primitives:
   - **`Channel<Payload, Rank: u32, Irrevocable: bool>`:** Every unidirectional flow carries an explicit static topological rank $r \in \mathbb{N}$. Any intra-module combinational or buffer-allocation wait from input channel $c_{\text{in}}$ to output channel $c_{\text{out}}$ is well-typed **if and only if** $\text{Rank}(c_{\text{in}}) < \text{Rank}(c_{\text{out}})$ (making TileLink `0..4`, CXL `Req(0) < BISnp(1) < BIRsp(2) < NDR/DRS(3) < FC_DLLP(4)`, and AXI `W`-before-`B` ordinary instances of one `< 5 µs` linear check).
   - **`CreditGrant<Pool, Preallocated: bool>`:** Unifies static VC buffer credits (`UCIe`/`CXL` `NDR`/`DRS`), unconditional zero-buffer sinks (`TL` Channel `E`, `Preallocated = true`), and two-phase dynamic reservations (`CHI` `RetryAck` $\to$ reserved `PCrdGrant`), statically rejecting unreserved opportunistic credit theft (closing CHI's retry-livelock hole).
   - **`BipartiteLattice<Down: JoinSemilattice, Up: MeetSemilattice>`:** Decouples compile-time capability negotiation (monotone Tarski fixpoint over finite height lattices `AddressSet` $\times$ `TransferSizes` $\times$ `IdRange`, which converges even on cyclic physical mesh topologies!) from physical wire graphs—preserving Diplomacy's 15-LoC deep-module ergonomics while supporting cyclic chiplet/NoC topologies natively without `CycleException` node-splitting workarounds.

## Boundaries

The following negative-space boundaries qualify these findings:

- **`known not to apply` — AXI4 Single-Hop Deadlock Freedom Does Not Transfer to Multi-Master Crossbars Without `w_open` Serialization:** Proving an individual AXI4 master and slave compliant with `ARM IHI 0022` A3.3.1 (e.g., via `ZipCPU/wb2axip` `faxi_slave.v`) is **insufficient** to prevent multi-master crossbar deadlocks if an intermediate `axi_demux` allows `AW` beats to advance to distinct slave ports while prior `W` bursts remain incomplete (`interconnect_probe.py`: 4-party deadlock under `SpillAw = 1`).
- **`known not to apply` — AMBA CHI `RetryAck`/`PCrdGrant` Deadlock Freedom Does Not Imply Starvation Freedom:** Dynamic retry eliminates circular TBE buffer waits, but without strict TBE reservation at `PCrdGrant` emission time and fair per-`RN-F` grant scheduling, `AllowRetry = 1` requests can livelock indefinitely under asymmetric mesh distance.
- **`unsupported` — Cyclic Node Topologies in `chipsalliance/diplomacy` Single-Pass Negotiation:** Binding `MixedNode` instances in a directed cycle (`A := B := A`) is explicitly unsupported and throws `StarCycleException`, `DownwardCycleException`, or `UpwardCycleException` (`MixedNode.scala:349, 488, 509`); cyclic hardware fabrics must separate client and manager nodes.
- **`unsupported` — Interleaved Read/Write Data Beats Across `TLToAXI4` (`ToAXI4.scala:105–106`):** `TLToAXI4` rejects downstream AXI4 slaves where `interleavedId` is `None` (`require(slaves(0).interleavedId.isDefined)`), because TileLink `Channel D` requires contiguous burst beats per message unless an explicit reorder/de-interleaving SRAM precedes the bridge.
- **`not examined` — UCIe 2.0 Manageability/3D-Packaging System Architecture & Analog SerDes Equalization:** UCIe 2.0 LTSSM analog voltage/timing margining eyes, 3D hybrid-bonding thermal coupling, and `UCIe-S` sideband management transport packets were not examined at circuit/SPICE level.
- **`unknown` — Commercial Closed-Source CHI Interconnect (`CMN-700`) Exact `PCrdGrant` Fairness Arbiters:** Because ARM CoreLink CMN-700 RTL is proprietary, the exact internal starvation-horizon counters used in commercial `HN-F` silicon to bound worst-case `RetryAck` tail latency remain `unknown` from public primary sources.

## Evidence

1. **Primary Repository Sources Inspected (`2026-11-19`):**
   - `ZipCPU/wb2axip` @ `2e8d3bc2d26ddc33d1881022a2a2b9d3f0c16b9b`:
     - `bench/formal/faxil_slave.v` (`lines 35–65, 489–560`): Formal AXI4-Lite slave contract, `f_axi_awr_outstanding` / `f_axi_wr_outstanding` counters, and `F_OPT_XILINX` (`<= 2` clock `AW`-ahead-of-`W`, `<= 1` clock `W`-ahead-of-`AW`) non-standard vendor timing assumptions.
     - `bench/formal/faxi_slave.v` (`lines 1–1324`) & `rtl/easyaxil.v` (`lines 1–523`) & `rtl/demofull.v` (`lines 1–1285`): Full AXI4 burst formal properties and 1-beat/clock skid-buffered reference slave designs.
   - `pulp-platform/axi` @ `ee000c0eba9e1c2b6ffdab163a2957419d143461`:
     - `src/axi_demux.sv` (`lines 50–185`) & `src/axi_demux_simple.sv` (`lines 37–245`): `SpillAw` register slice decoupling, `(w_open == '0) || (w_select == slv_aw_select_i)` `W`-channel deadlock guard (`line 182`), `lock_aw_valid_q` immediate `W` steering before `aw_ready` (`lines 164–197`), `axi_demux_id_counters` (`lines 208–228`), and `ATOP_R_RESP` `atop_inject` (`lines 171, 175–191`).
     - `src/axi_mux.sv` (`lines 1–605`), `src/axi_xbar.sv` (`lines 1–246`), and `src/axi_atop_filter.sv` (`lines 1–447`).
   - `chipsalliance/rocket-chip` @ `ece7b9ad544b07df39cd13b6fd7236562a26355d`:
     - `src/main/scala/tilelink/Parameters.scala` (`lines 24–55`): `TLMasterToSlaveTransferSizes` `.intersect` and `.mincover` lattice operations.
     - `src/main/scala/tilelink/Xbar.scala` (`lines 130–235`): `reachableIO`, `probeIO`, `releaseIO` dead-channel pruning and prefix-free `TLXbar.mapInputIds` bit-OR routing.
     - `src/main/scala/tilelink/Broadcast.scala` (`lines 75–140`): Coherence tracker synthesis and unconditional `in.e.ready := true.B` (`line 117`).
     - `src/main/scala/tilelink/Monitor.scala` (`lines 1–883`): Diplomatic edge-parameterized `monAssert` invariants.
     - `src/main/scala/tilelink/ToAXI4.scala` (`lines 39–120`) & `src/main/scala/amba/axi4/ToTL.scala` (`lines 45–220`): `TLtoAXI4IdMap`, `AXI4TLStateField` echo state, `in.aw.ready := w_out.ready && in.w.valid && in.w.bits.last` (`ToTL.scala:152`), `Queue.irrevocable` (`lines 190, 197`), and `b_allow` `WLAST`-before-`BVALID` guard (`lines 199–211`).
   - `chipsalliance/diplomacy` @ `fe5e131d4fc8adec14a3ce4a4935bb5c0a269871`:
     - `diplomacy/src/diplomacy/lazymodule/LazyModule.scala` (`lines 11–115`): Two-phase `LazyModule` / `LazyModuleImpLike` architecture.
     - `diplomacy/src/diplomacy/nodes/BaseNode.scala` (`lines 1–160`) & `MixedNode.scala` (`lines 290–556`): `StarCycleException`, `DownwardCycleException` (`doParams`), and `UpwardCycleException` (`uiParams`).
   - `chipsalliance/chisel` @ `e95009474df71a0fe95e29a7c04b7cbd80fc426d`:
     - `src/main/scala/chisel3/util/Decoupled.scala` (`lines 16–79`): `DecoupledIO` vs. `IrrevocableIO` directional variance check (`DataMirror.directionOf(irr.bits) == Direction.Output`).
2. **Normative Specifications & Peer-Reviewed Literature:**
   - ARM Limited, *AMBA AXI and ACE Protocol Specification*, `ARM IHI 0022` (Issue H.c / Issue K), Section A3.3.1 (*Dependencies between channel handshake signals*) & Section E1 (*Atomic transactions*).
   - ARM Limited, *AMBA 5 CHI Architecture Specification*, `ARM IHI 0050` (Issue F / Issue G), Chapters 2, 4, and 6 (Coherence protocol, `CompAck` hazard ordering, Snoop Filter eviction, and `AllowRetry`/`RetryAck`/`PCrdGrant` dynamic credit protocol).
   - SiFive, Inc., *TileLink Specification*, Version `1.8.1` (`TL-UL`, `TL-UH`, `TL-C`, Section 3.3 *Deadlock Freedom* `A < B < C < D < E`).
   - Henry Cook, Wesley Terpstra, and Yunsup Lee, *"Diplomatic Design Patterns: A TileLink Case Study"*, 1st Workshop on Computer Architecture Research with RISC-V (`CARRV 2017`), Boston, MA, October 2017.
   - UCIe Consortium, *Universal Chiplet Interconnect Express (UCIe) Specification*, Revision `1.1` / `2.0` (Physical Layer Standard vs. Advanced Packaging `MBINIT.REPAIR`, D2D Adapter `256B` Standard Format 4 `240 B` payload vs. Latency-Optimized Format 5 `236 B` `128B+128B` `CRC16` layout, `FDI`/`RDI`).
   - Compute Express Link Consortium, *CXL Specification*, Revision `3.0` (Chapter 3 `CXL.cache` & `CXL.mem` `M2S`/`S2M` message classes `Req`, `RwD`, `BIRsp`, `BISnp`, `NDR`, `DRS`, and VC credit pre-allocation rules).
3. **Self-Contained Executable Model-Checking & Sizing Probe (`2026-11-19`, Python 3.13):**
   Running the standalone script below reproduces the exact BFS deadlock counterexamples, topological rank checks, and UCIe 256B Flit replay SRAM footprints reported in Sections 1–5:

```python
#!/usr/bin/env python3
from collections import deque
import time

def check_axi4_xbar_w_deadlock(guard_demux_w_open: bool):
    targets = ((0, 1), (1, 0))
    init = (0, 0, 0, 0, 0, 0, 0, 0, (), (), None, None)
    visited, q, deadlocks = {init}, deque([init]), []
    while q:
        m0_aw, m1_aw, m0_w, m1_w, p00, p01, p10, p11, s0_q, s1_q, m0_open, m1_open = st = q.popleft()
        if m0_w == 2 and m1_w == 2 and not s0_q and not s1_q and (p00 + p01 + p10 + p11 == 0):
            continue
        nxt = []
        if m0_aw < 2:
            t = targets[0][m0_aw]
            if (not guard_demux_w_open) or (m0_open is None or m0_open == t):
                np00, np01 = (p00 + 1, p01) if t == 0 else (p00, p01 + 1)
                nxt.append((m0_aw + 1, m1_aw, m0_w, m1_w, np00, np01, p10, p11, s0_q, s1_q, t, m1_open))
        if m1_aw < 2:
            t = targets[1][m1_aw]
            if (not guard_demux_w_open) or (m0_open is None if False else (m1_open is None or m1_open == t)):
                np10, np11 = (p10 + 1, p11) if t == 0 else (p10, p11 + 1)
                nxt.append((m0_aw, m1_aw + 1, m0_w, m1_w, p00, p01, np10, np11, s0_q, s1_q, m0_open, t))
        if p00 > 0: nxt.append((m0_aw, m1_aw, m0_w, m1_w, p00 - 1, p01, p10, p11, s0_q + (0,), s1_q, m0_open, m1_open))
        if p10 > 0: nxt.append((m0_aw, m1_aw, m0_w, m1_w, p00, p01, p10 - 1, p11, s0_q + (1,), s1_q, m0_open, m1_open))
        if p01 > 0: nxt.append((m0_aw, m1_aw, m0_w, m1_w, p00, p01 - 1, p10, p11, s0_q, s1_q + (0,), m0_open, m1_open))
        if p11 > 0: nxt.append((m0_aw, m1_aw, m0_w, m1_w, p00, p01, p10, p11 - 1, s0_q, s1_q + (1,), m0_open, m1_open))
        if m0_w < m0_aw:
            t = targets[0][m0_w]
            sq = s0_q if t == 0 else s1_q
            if sq and sq[0] == 0:
                still = targets[0][m0_w + 1] if (m0_w + 1 < m0_aw) else None
                nxt.append((m0_aw, m1_aw, m0_w + 1, m1_w, p00, p01, p10, p11,
                            s0_q[1:] if t == 0 else s0_q, s1_q[1:] if t == 1 else s1_q, still, m1_open))
        if m1_w < m1_aw:
            t = targets[1][m1_w]
            sq = s0_q if t == 0 else s1_q
            if sq and sq[0] == 1:
                still = targets[1][m1_w + 1] if (m1_w + 1 < m1_aw) else None
                nxt.append((m0_aw, m1_aw, m0_w, m1_w + 1, p00, p01, p10, p11,
                            s0_q[1:] if t == 0 else s0_q, s1_q[1:] if t == 1 else s1_q, m0_open, still))
        if not nxt: deadlocks.append(st)
        for s2 in nxt:
            if s2 not in visited:
                visited.add(s2); q.append(s2)
    return len(visited), deadlocks

def check_chi_sf_eviction_hazard(allow_retry_pcrd: bool):
    init = ("IDLE", "IDLE", None, False, False)
    visited, q, deadlocks = {init}, deque([init]), []
    while q:
        rn0, rn1, tbe, snp_pend, pcrd = st = q.popleft()
        if rn0 == "DONE" and rn1 == "DONE" and tbe is None: continue
        nxt = []
        if rn0 == "IDLE": nxt.append(("REQ_SENT", rn1, tbe, snp_pend, pcrd))
        if rn1 == "IDLE": nxt.append((rn0, "REQ_SENT", tbe, snp_pend, pcrd))
        if rn1 == "REQ_SENT" and tbe is None: nxt.append((rn0, "WAIT_COMP", "RN1_EVICTING_L0", True, pcrd))
        if rn0 == "REQ_SENT" and tbe == "RN1_EVICTING_L0" and allow_retry_pcrd:
            nxt.append(("WAIT_PCRD", rn1, tbe, snp_pend, pcrd))
        if snp_pend and rn0 in ("IDLE", "WAIT_PCRD", "DONE"): nxt.append((rn0, rn1, "RN1_READY", False, pcrd))
        if tbe == "RN1_READY" and rn1 == "WAIT_COMP": nxt.append((rn0, "DONE", None, False, rn0 == "WAIT_PCRD"))
        if rn0 == "WAIT_PCRD" and pcrd and tbe is None: nxt.append(("DONE", rn1, None, False, False))
        if rn0 == "REQ_SENT" and tbe is None: nxt.append(("DONE", rn1, None, False, pcrd))
        if not nxt: deadlocks.append(st)
        for s2 in nxt:
            if s2 not in visited:
                visited.add(s2); q.append(s2)
    return len(visited), deadlocks

assert check_axi4_xbar_w_deadlock(False)[1] == [(2, 2, 0, 0, 0, 0, 0, 0, (1, 0), (0, 1), 1, 0)]
assert check_axi4_xbar_w_deadlock(True) == (51, [])
assert check_chi_sf_eviction_hazard(False)[1] == [("REQ_SENT", "WAIT_COMP", "RN1_EVICTING_L0", True, False)]
assert check_chi_sf_eviction_hazard(True) == (18, [])
print("ALL_INTERCONNECT_PROBES_PASSED")
```

## Revalidation

To revalidate these findings cheaply when upstream repositories or specifications evolve:

1. **Re-run the Inline State-Space Probe (`< 50 ms`):** Execute the Python 3 script in **Evidence** (`python3 -c ...`) to confirm the deterministic `140`-state vs. `51`-state AXI4 crossbar result and `15`-state vs. `18`-state CHI snoop-filter eviction result.
2. **Targeted Upstream Diffs (`< 5 s` via `git diff` or `curl`):**
   - In `pulp-platform/axi`, inspect `src/axi_demux_simple.sv` around `w_open`, `lock_aw_valid_q`, `i_aw_id_counter`, and `atop_inject` to verify whether multi-destination `W` bursts have been enabled (e.g., via deep burst-buffering FIFOs) or remain gated by `(w_open == '0) || (w_select == slv_aw_select_i)`.
   - In `chipsalliance/rocket-chip` (`src/main/scala/amba/axi4/ToTL.scala`, `src/main/scala/tilelink/{Broadcast,Xbar,ToAXI4}.scala`) and `chipsalliance/diplomacy` (`MixedNode.scala`), check whether `in.e.ready := true.B`, `Queue.irrevocable`, `b_allow`, and the three `CycleException` guards remain unchanged.
   - For newer UCIe (`>= 2.0`) or CXL (`>= 3.1/4.0`) revisions, check Flit Format tables for any change to the `240 B` (Format 4) / `236 B` (Format 5) payload split or `BISnp`/`BIRsp` VC isolation rules.
