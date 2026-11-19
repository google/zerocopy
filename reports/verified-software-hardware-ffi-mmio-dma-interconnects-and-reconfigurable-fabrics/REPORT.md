# Verified Software-Hardware FFI: MMIO, DMA, Interconnects, Interrupts, and Reconfigurable Fabrics

## Summary

The software-hardware foreign function interface (FFI) is a concurrent protocol seam connecting CPU instructions to stateful peripheral automata, multi-channel interconnects, non-coherent memory hierarchies, asynchronous preemption controllers, and reconfigurable fabrics. Untyped C `volatile`, raw physical-address integers, inline assembly, and imperative `ioctl` loaders leave five classes of failures outside compiler and verifier reach:

1. **MMIO protocol & width violations**: Hardware registers attach side effects (`W1C`, pop-on-read FIFOs, multi-word latches) requiring non-tearing width preservation and `Device-nGnRnE` ordering. **`Bedrock2` + `Kami`** (`mit-plv/bedrock2`, PLDI 2021) and **`Pancake`** (`CakeML/cakeml`, PLOS 2023 / `arXiv:2501.08249`) close this seam by isolating MMIO domains (`isMMIOAddr` / `sh_memaddrs`) and emitting explicit width-preserving external trace events (`MMIOREAD`/`MMIOWRITE` $\to$ single RV32I `Lw`/`Sw`; `ShMemLoad`/`ShMemStore` $\to$ CakeML `SharedMem` FFI oracle).
2. **Interconnect deadlocks & coprocessor opacity**: **ARM AMBA `AXI4`** (`ARM IHI 0022` §A3.3.1, §A3.4.1) requires `VALID` never to wait on `READY` (including cross-channel `WVALID -> AWREADY`) and forbids `INCR` bursts crossing 4 KiB boundaries. Cache-coherent **TileLink (`TL-C`)** guarantees timeout-free deadlock freedom via strict channel priority ($A \ll B \ll C \ll D \ll E$); sharing a FIFO across `A` and `C` or `E` induces a provable MSHR head-of-line deadlock. **`CIRCT ESI`** (`llvm/circt`) provides single-consumer latency-insensitive typed channels, while **`RISC-V RoCC`** (`chipsalliance/rocket-chip`) shares the core's L1 D-cache (`HellaCacheIO`) and Page Table Walker (`TLBPTWIO`), requiring modular ISA + coprocessor effect semantics rather than opaque inline `asm`.
3. **Non-coherent DMA false-sharing tearing & speculative prefetching**: Safe non-coherent DMA requires five linear invariants (pinning, `IOMMU`/`CHERI-DMA` bounds, exclusive ownership surrender, cache maintenance + cache-line exclusivity, completion fence + revocation). Exhaustive state-space verification (`support/verify_mmio_dma_axi_and_dpr.py`) proves that when an unaligned `DMA_FROM_DEVICE` buffer shares a 64B cache line with a concurrently written CPU variable, **every** ARMv8 op (`DC CIVAC`, `DC IVAC`, `DC CVAC`) corrupts reachable executions; even with `CacheLineAligned` linear ownership and pre-`DC CIVAC`, omitting post-DMA `DC IVAC` permits stale reads via hardware speculative prefetching (`3/9` failures vs. `0/6` across `56` states with post-`DC IVAC`). **`CXL 2.0/3.0` (`CXL.cache`/`CXL.mem`)** removes software cache flushes via hardware coherence but still requires linear ownership against data races.
4. **Preemptive IRQ races & edge-IRQ lost wakeups**: Baker's **Stack Resource Policy (`SRP`)** (1991), enforced statically in **`RTIC`** (`rtic-rs/rtic`) via `BASEPRI` ceiling locks (`basepri_max::write` + `isb` + compiler fence + restore), guarantees deadlock-free single-stack race freedom (`0` races across `40` states vs. `3` unprotected). Preventing edge-IRQ lost wakeups additionally requires masked-poll-then-`WFI` product-automaton liveness (`0` deadlocks across `14` states vs. `1` unmasked deadlock).
5. **RTL $\sqsubseteq$ TLM stuttering refinement & typed FPGA `DPR`**: Pipelined RTL refines TLM specs via stuttering simulation (`Kami` `traceRefines`, `Bedrock2` `kstep1_sound`, `Kôika` `OneRuleAtATime`, `Filament` timeline types, plus Namjoshi/Manolios well-founded progress ranks for liveness). Live FPGA `DPR` requires draining in-flight AXI bursts through **`AMD PG377`** (`AXI Shutdown Manager`, returning `SLVERR` to new arrivals) *before* clamping **`AMD PG375`** (`DFX Decoupler`), coupled with linear ABI handles (`0` wedges, `0` glitch leaks, `0` ABI mismatches across `37` states).

## Applicability

This report synthesizes **14 directly examined primary subjects** (pinned in `REPORT.json` by 40-character Git commit SHAs, DOIs, and specification codes) across four coupled layers:

| Subject Group | Examined Primary Artifacts | Relationship in This Report |
|---|---|---|
| **Verified SW↔HW & driver stacks** | `mit-plv/bedrock2` (`0005c47b5eaa`), `mit-plv/kami` (`9217329eb4e1`), `mit-plv/koika` (`8921e30434d9`), `CakeML/cakeml` (`2874b664e109`), `cucapra/filament` (`3c17db5ce85c`) | Mechanized Coq/HOL4 semantics connecting source drivers, verified compilers, rule-based/timeline-typed hardware, and MMIO/I/O traces. |
| **Interconnect & coprocessor norms/RTL** | `ARM IHI 0022` (`AXI4`), `TileLink v1.8.1/v1.9.3`, `chipsalliance/rocket-chip` (`ece7b9ad544b`), `llvm/circt` (`203f159ce10d`) | Normative causality rules paired with Chisel RTL (`TLMonitor`, `LazyRoCC`) and MLIR latency-insensitive channels (`ESI`). |
| **DMA, coherence, isolation & IRQs** | `torvalds/linux` (`4405c18c95d2`), `Baker 1991` / `rtic-rs/rtic` (`fed0fa5e9d74`), `Thunderclap` (NDSS 2019) & `CHERI-DMA` (HASP 2020), `CXL 2.0/3.0` | Production ARM64 cache-maintenance assembly (`cache.S`), embedded Rust `BASEPRI` SRP locking, and capability/coherent alternatives. |
| **Refinement & reconfigurable silicon** | `Namjoshi 1997` / `Manolios 2000`, `AMD PG374`/`PG375`/`PG377`/`UG909`, `torvalds/linux` (`fpga-region.c`) | Stuttering-simulation foundations linked to live FPGA AXI quiescence, decoupling, and linear typestate ABI handoff. |

### Cross-References to Adjacent Corpus Packages

- **`sail-isa-models-lean-backend-and-rv64d-decoding-framing`**: Owns Sail ISA formalizations, Lean 4 extraction, CHERI Sail specs, and RV64D decoding/framing; this report covers only the tightly coupled `RISC-V RoCC` extension seam.
- **`anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`**: Owns Rust `read_volatile`/`write_volatile` tables, `global_asm!`/naked-function ABIs, linker scripts, and CPU-to-CPU weak-memory models (`herdtools7`, `IMM`, CompCert); this report does not duplicate Rust volatile tables and focuses on hardware MMIO automata, non-coherent DMA caches, bus causality, IRQs, and FPGA DPR.
- **`anneal-cps-robotics-aerospace-eda-and-quantum-survey`**: Surveys the broader HDL/EDA tool landscape; this report extracts the formal SW↔HW boundary invariants and refinement theorems.

### Scope Constraints

- **Coherence domain**: Explicit `DC CVAC`/`DC IVAC`/`DC CIVAC` + `DSB SY` obligations apply to **non-coherent DMA** (ARMv8/RISC-V SoCs without ACE/CHI I/O snooping). Snooped x86 PCIe and `CXL.cache` paths omit software cache flushes while retaining pinning, IOMMU/capability bounds, linear ownership, and ordering fences.
- **Preemption model**: Baker SRP and RTIC `BASEPRI` single-stack guarantees apply to **single-core priority-preemptive scheduling**; SMP requires multi-core ceiling protocols.
- **Finite-state probe**: `support/verify_mmio_dma_axi_and_dpr.py` exhaustively checks bounded models (1–2 cache lines, 5-channel AXI4/TL-C graphs, 2-client TL-C MSHR, bounded DPR bursts, 3-task SRP, single edge-IRQ). Counterexamples reflect genuine protocol bugs; zero-violation results hold strictly under the modeled assumptions.

## Findings

### 1. Memory-Mapped I/O (MMIO) Semantics and End-to-End HW+SW Verification

#### 1.1 Failure Modes of Untyped `volatile` at the Hardware Register Seam

Basis: normative + documentation + derived

MMIO exposes stateful peripheral transitions through loads and stores targeting non-RAM physical windows. Beyond Rust-level volatile semantics documented in `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`, untyped `volatile` fails at the hardware boundary in four ways:

1. **Tearing and widening**: Peripheral registers bind side effects to exact bus transfer widths (e.g., 32-bit-only APB/AXI4-Lite registers returning `SLVERR` on byte strobes, or 32-bit registers whose upper bits clear on read). Lowering bitfields or unaligned aggregates can split one source access into multiple beats (*tearing*) or widen a narrow store into read-modify-write (*widening*), clearing unrelated write-1-to-clear (`W1C`) interrupt bits.
2. **Unchecked register FSM protocols**: Registers enforce `RO`, `WO`, `RC` (read-clear), `W1C`, FIFO pop-on-read, and multi-word latch orderings (`COUNT_LO` latches `COUNT_HI`; `DMA_DESC_ADDR` must precede `DMA_DOORBELL`). Untyped pointers permit reading `WO` registers or issuing out-of-state writes.
3. **Hardware speculation**: Mapping MMIO with Normal/cacheable attributes allows speculative loads along mispredicted branches to pop FIFOs or clear `RC` flags. ARMv8 requires **`Device-nGnRnE`** (non-Gathering, non-Reordering, no Early Write Acknowledgement) attributes for side-effecting MMIO windows.
4. **PDF/header/RTL drift**: Maintaining register offsets separately in datasheets, C `#define` headers, and Verilog `case (addr)` decoders lets bitfield offsets and reserved-bit polarities diverge silently.

#### 1.2 `Bedrock2` + `Kami` End-to-End Hardware-Software Co-Verification

Basis: source + documentation

Erbsen, Gruetter, Choi, Wood, and Chlipala (PLDI 2021, DOI `10.1145/3453483.3454069`) proved in `mit-plv/bedrock2@0005c47b5eaa720bdcb9b94aceaca9f42726b861` a single Coq theorem composing an IoT lightbulb application, SPI/Ethernet MMIO drivers, a verified compiler, `riscv-coq`, and a 4-stage pipelined processor (`p4mm`) in **Kami** (`mit-plv/kami@9217329eb4e1d751f28ab175ebab230b1e8fd4da`):

- **Disjoint RAM and MMIO domains**: `processor/src/processor/KamiRiscv.v:491-496` proves `riscv_init_memory_undef_on_MMIO : map.undef_on riscvMemInit isMMIOAddr` via `mmio_mem_disjoint`. RAM accesses stay in the separation-logic heap; MMIO accesses occur solely via `cmd.interact` external calls `"MMIOREAD"` and `"MMIOWRITE"` (`end2end/src/end2end/Bedrock2SemanticsForKami.v:10-11`).
- **Single-instruction width-preserving compilation**: `compiler/src/compiler/MMIO.v:40-94` defines `compile_interact`, lowering `"MMIOWRITE"` to `[[ Sw addr val 0 ]]` and `"MMIOREAD"` to `[[ Lw res addr 0 ]]`, with `compile_interact_length` (at most 1 instruction) and `compile_interact_emits_valid` guaranteeing valid RV32I encoding without tearing or hoisting.
- **Three-tier trace relation**: `end2end/src/end2end/End2EndLightbulb.v:49-57,136-159` relates high-level SPI events (`ioh`) to mid-level `RiscvMachine.LogItem` (`iomid`) via `SPI.mmio_trace_abstraction_relation`, and to low-level hardware events (`KamiRiscvStep.Event`) via `KamiRiscvStep.traces_related` (`iohi_to_iolo`, `kami_and_lightbulb_abstract_bedrockTrace_the_same_way`).
- **Top-level prefix-safety theorem**: Instantiating generic `end2end` (`End2EndPipeline.v:274-301`), `End2EndLightbulb.v:167-175` proves:
  ```coq
  Theorem end2end_lightbulb: forall mem0 t state,
    bytes_at (instrencode lightbulb_insts) 0 mem0 ->
    Semantics.Behavior (p4mm mem0) state t ->
    exists t': list (string * bits 32 * bits 32),
      KamiRiscv.KamiLabelSeqR t t' /\
      prefix_of t' goodHlTrace.
  ```
  where `prefix_of l P := exists completion, P (completion ++ l)` (left-growing traces). Every finite execution of `p4mm` emits exclusively valid prefixes of `goodHlTrace` (safety); liveness/non-stalling is deliberately not proved.

#### 1.3 `Pancake` Verified Device-Driver Compilation on `CakeML`/`seL4`

Basis: source + documentation

**Pancake** (Åman Pohjola et al., PLOS 2023, DOI `10.1145/3623759.3624544`; Zhao et al., `arXiv:2501.08249`, 2025) in `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb` compiles GC-free systems code with HOL4 soundness proofs to x86-64, ARMv8, and RISC-V64 machine code for **seL4 / LionsOS** (`sDDF`) Ethernet and serial drivers:

1. **First-class width-indexed shared/MMIO ops (`pancake/panLangScript.sml:67-69,95-96`)**:
   ```sml
   Datatype: opsize = Op8 | OpW | Op32 | Op16 End
   | ShMemLoad  opsize varkind varname exp
   | ShMemStore opsize exp exp
   ```
   State separates `s.memaddrs` (private RAM) from `s.sh_memaddrs` (MMIO and shared rings, `panSemScript.sml:56-57`).
2. **Observable FFI semantics (`pancake/semantics/panSemScript.sml:511-555`)**: `sh_mem_load` and `sh_mem_store` enforce membership in `s.sh_memaddrs` and invoke `call_FFI s.ffi (SharedMem MappedRead|MappedWrite) [n2w nb] ...` with `nb_op` mapping `Op8 -> 1`, `Op16 -> 2`, `Op32 -> 4`, `OpW -> 0` (word width). Because MMIO accesses are observable FFI calls, every compiler pass (`panLang -> crepLang -> loopLang -> wordLang -> stackLang -> labLang -> target`) preserves exact order and width.
3. **Machine-code soundness + static `stack_max` (`pancake/proofs/pan_to_targetProofScript.sml:1285-1328`)**: `pan_to_target_compile_semantics` proves `machine_sem mc ffi ms ⊆ extend_with_resource_limit' ... {semantics_decls s start pan_code}` under `pan_installed ... s.memaddrs s.sh_memaddrs`, simultaneously certifying static stack usage (`compile_prog_max`).
4. **Deductive driver proofs**: Pancake pairs HOL4 compiler verification with automated transpilation to the **Viper** SMT verifier (`arXiv:2501.08249`), Interaction-Tree decompilation (`pancake/decompiler/`, `pan_itreeEquivProofScript.sml`), and high-fidelity device specifications (Murphy et al., PLOS 2025, DOI `10.1145/3764860.3768335`).

#### 1.4 Comparative Architecture of MMIO Boundary Disciplines

Basis: source + derived

| Mechanism | Domain Separation | Non-Tearing Width | Register FSM / Access Typing | Drift Protection | Mechanized Proof Extent |
|---|---|---|---|---|---|
| **C `volatile` / raw pointers** | None (flat) | Weak (bitfields/aggregates may tear/widen) | None (`RO`/`WO`/`W1C` unchecked) | None (manual PDF $\to$ `.h` + RTL) | None |
| **`Bedrock2` + `Kami` (PLDI 2021)** | Disjoint (`isMMIOAddr`) | Single RV32I `Lw`/`Sw` (`compile_interact`) | Trace predicate (`mmio_trace_abstraction_relation`) | Shared Coq trace relation | SW + compiler + ISA + pipelined RTL (prefix safety) |
| **`Pancake` (`CakeML`/`seL4`)** | Disjoint (`memaddrs` vs. `sh_memaddrs`) | `Op8`/`Op16`/`Op32`/`OpW` via `SharedMem` FFI | Viper SMT / ITrees + device spec | External FFI oracle; RTL separate | Full compiler + `stack_max` to x64/ARM8/RV64 |
| **Unified Register Schema (synthesis)** | Region/capability handle | Schema-derived width-indexed ops | Linear/typestate `RO`/`WO`/`W1C`/latch FSMs | Single source $\to$ SW handles + `Kôika`/`CIRCT` RTL | Eliminates offset/width drift by construction |

---

### 2. On-Chip Interconnect Causality (`AXI4`, `TileLink-C`, `CIRCT ESI`) and Tightly Coupled Coprocessors (`RISC-V RoCC`)

#### 2.1 ARM AMBA `AXI4` Handshake Causality and 4 KiB Boundary Rules

Basis: normative + execution + derived

ARM AMBA `AXI4` (`ARM IHI 0022`) uses five independent unidirectional channels (`AW`, `W`, `B`, `AR`, `R`), transferring one beat per rising clock edge when `VALID && READY` holds. Three normative rules govern deadlock freedom and legality:

1. **Asymmetric handshake causality (`ARM IHI 0022` §A3.3.1)**:
   - Sources (`AWVALID`, `WVALID`, `ARVALID` on masters; `BVALID`, `RVALID` on slaves) must **never** wait on `READY` before asserting `VALID`, and must hold `VALID` and payload stable until `READY` is sampled high.
   - Receivers (`AWREADY`, `WREADY`, `ARREADY` on slaves; `BREADY`, `RREADY` on masters) **may** wait for `VALID` before asserting `READY`.
   - **Cross-channel write rule**: Because a legal slave may wait for *both* `AWVALID` and `WVALID` before raising `AWREADY` or `WREADY`, a master must **never** make `WVALID` depend on `AWREADY` (nor `AWVALID` on `WREADY`).
   - **Response causality**: `BVALID` must wait for both the `AW` handshake and the final `W` beat (`WLAST`); `RVALID` must wait for the `AR` handshake; neither may wait on `BREADY`/`RREADY`.
2. **4 KiB burst address boundary (`ARM IHI 0022` §A3.4.1)**: An `INCR` burst of `AxLEN + 1` beats of width `2^AxSIZE` must satisfy $\lfloor \text{StartAddr} / 4096 \rfloor = \lfloor (\text{AlignedStart} + (\text{AxLEN} + 1)\cdot 2^{\text{AxSIZE}} - 1) / 4096 \rfloor$, ensuring bursts never cross slave decode boundaries and bounding slave address incrementers to 12 bits. Multi-page DMA transfers must split bursts at 4 KiB boundaries.
3. **ID ordering (`ARM IHI 0022` §A5.3)**: Same-`AxID` transactions return responses in issue order; distinct-`AxID` transactions may reorder arbitrarily.

**Probe verification (`support/verify_mmio_dma_axi_and_dpr.py`, Part 2)**: Composing the maximally-waiting legal slave and legal master dependency graphs from §A3.3.1 proves:
- Compliant pair: **acyclic** (`cycle = None`).
- Buggy master (`AWVALID -> AWREADY`): cycle `['AWREADY', 'AWVALID', 'AWREADY']`.
- Buggy master (`WVALID -> AWREADY`, cross-channel deadlock): cycle `['AWREADY', 'WVALID', 'AWREADY']`.
- Buggy slave (`BVALID -> BREADY`): cycle `['BREADY', 'BVALID', 'BREADY']`.
- 4 KiB burst boundary: `0x10000f80` + 128B (`AxSIZE=3`, `AxLEN=15`) $\implies$ `legal=True`; + 136B (`AxLEN=16`, crosses `0x10001000`) $\implies$ `legal=False`.

#### 2.2 `TileLink` (`TL-UL`/`TL-UH`/`TL-C`) Acyclic Channel Priority Hierarchy

Basis: normative + source + execution

SiFive / CHIPS Alliance **TileLink** (`v1.8.1`/`v1.9.3`, implemented in `chipsalliance/rocket-chip@ece7b9ad544b07df39cd13b6fd7236562a26355d`) stratifies into `TL-UL` (uncached `A`/`D`), `TL-UH` (atomics/bursts), and cache-coherent **`TL-C`** over five channels (`A`–`E`):

- **Permission lattice (`src/main/scala/tilelink/Bundles.scala:35-129`)**: Cache states follow **Trunk (`T`) $>$ Branch (`B`) $>$ None (`N`)**. `AcquireBlock`/`AcquirePerm` (`A`) carry `Grow` (`NtoB`/`NtoT`/`BtoT`); `Probe` (`B`) and `Grant`/`GrantData` (`D`) carry `Cap` (`toT`/`toB`/`toN`); `ProbeAck`/`Release` (`C`) carry `Shrink`/`Report` transitions; `GrantAck` (`E`) retires manager trackers.
- **Deadlock-freedom invariant ($A \ll B \ll C \ll D \ll E$)**: Coherence transactions follow causal chains `Acquire(A) -> Probe(B) -> ProbeAck(C) -> Grant(D) -> GrantAck(E)` and `Release(C) -> ReleaseAck(D)`. TileLink guarantees deadlock freedom across DAG fabrics *without timeouts* by enforcing strict priority $\text{A} \ll \text{B} \ll \text{C} \ll \text{D} \ll \text{E}$: lower-priority channel congestion must never block higher-priority channels, so every causal edge $u \to v$ satisfies $\text{prio}(u) < \text{prio}(v)$.
- **Formal/simulation assertion bridge (`Monitor.scala:35-100`)**: `TLMonitor` checks opcode/param legality, power-of-two `edge.isAligned(bundle.address, bundle.size)`, source visibility, and full masks via dual simulation/formal `monAssert`/`assume` hooks.

**Probe verification (`support/verify_mmio_dma_axi_and_dpr.py`, Part 2)**:
- Compliant `TL-C` graph: strictly acyclic and priority-monotonic (`A < B < C < D < E`).
- Merging `A` and `C` into a shared queue (reverse edge `C -> A`) creates cycle `['A', 'B', 'C', 'A']`; merging `A` and `E` creates `['A', 'B', 'C', 'D', 'E', 'A']`.
- In the 2-client + 1-directory finite-state model (Client 0 holds `Trunk(X)` and queues `Acquire(Y)` on `A`; Client 1's `Acquire(X)` occupies the single directory MSHR awaiting `ProbeAck(C)` from Client 0): separate `A`/`C` channels complete across `5` states (`0` deadlocks), whereas a shared `A`/`C` FIFO immediately deadlocks at state `1` (`deadlock_count = 1`, `completed_states = 0`).

#### 2.3 `CIRCT ESI`: Latency-Insensitive Typed SW↔HW Channels

Basis: source + documentation

**Elastic Silicon Interconnects (`ESI`)** in `llvm/circt@203f159ce10d78940df4264327d5f3fc8b902112` lifts SW↔HW links above raw bus wires:

- **Single-consumer typed channels (`include/circt/Dialect/ESI/ESIChannels.td:33-139`)**: `!esi.channel<inner, ValidReady|FIFO(d)|ValidOnly>` parameterizes payload type, wire signaling, and read delay `dataDelay`. `ChannelType::verifyChannel` / `hasOneConsumer` enforces linear single-consumer token absorption; non-absorbing observers must use explicit `esi.snoop.vr`.
- **Windowed variable-length lists (`ESITypes.td:24-37`)**: `!esi.list<T>` maps a runtime-sized software memory slice to multi-cycle windowed hardware streams.
- **Hierarchical service bubbling (`ESIServices.td:23-130`, `ESIStdServices.td:15-120`)**: `esi.service.decl`, `esi.service.instance`, and standard services (`esi.mem.ram`, `esi.service.std.{channel,func,call}`) bubble descendant connectivity up to top-level `esi.service.impl_req` independently of PCIe/AXI/cosim transport.
- **Software ABI caveat (`docs/Dialects/ESI/software_api.md:1-24`)**: The document analyzes interface-hash vs. self-describing manifest strategies against SW↔HW ABI drift while explicitly marking auto-generated software APIs as `unimplemented` (recorded under **Boundaries**).

#### 2.4 Tightly Coupled Coprocessors: `RISC-V RoCC` and Modular ISA Composition

Basis: source + derived

In `chipsalliance/rocket-chip@ece7b9ad544b07df39cd13b6fd7236562a26355d`:

- **Opcode dispatch (`src/main/scala/rocket/IDecode.scala:526-552`, `src/main/scala/tile/LazyRoCC.scala:24-45`)**: `RoCCDecode` maps `CUSTOM0..CUSTOM3` across `{xs1, xs2, xd}` variants into `RoCCCommand(RoCCInstruction, rs1, rs2, MStatus)`.
- **Core pipeline entanglement (`LazyRoCC.scala:47-115`)**: `RoCCIO` attaches directly to (1) core L1 D-cache (`mem: HellaCacheIO` via `SimpleHellaCacheIF`), (2) core Page Table Walker (`ptw: Vec(nPTWPorts, TLBPTWIO)`), (3) coherent `atlNode`, incoherent `tlNode`, and slave `stlNode` TileLink ports, and (4) `busy` (stalling core `fence`), `interrupt`, `exception`, custom CSRs, and FPU ports.
- **Why inline `asm` fails verification**: `asm volatile(".insn r ...")` hides L1-coherent vs. incoherent `tlNode` memory writes, private accelerator scratchpads/key slots, and `ptw` TLB dependencies (`sfence.vma`).
- **Modular composition**: Composing a base `Sail` ISA (`sail-isa-models-lean-backend-and-rv64d-decoding-framing`) with a `Kôika`/`Filament` coprocessor factors state as `(CoreState, RoCCState)` coupled by explicit typed effect signatures `(ReadMem, WriteMem, CoherenceDomain, HiddenStateDelta, FenceObligation)`.

#### 2.5 Interconnect and Coprocessor Boundary Comparison

Basis: normative + source + derived

| Interface | Channels / Ports | Deadlock-Freedom Mechanism | Coherence Model | SW↔HW Verification Seam |
|---|---|---|---|---|
| **ARM AMBA `AXI4`** | 5 (`AW`/`W`/`B`/`AR`/`R`) | Asymmetric `VALID`/`READY` (§A3.3.1); 4 KiB burst limit (§A3.4.1) | Non-coherent (ACE/CHI for snoop) | Causality graph + DMA cache-maintenance contract |
| **TileLink `TL-C`** | 5 (`A`–`E`) | Strict priority $A \ll B \ll C \ll D \ll E$ + DAG; no timeouts | Native `T > B > N` directory coherence | `TLMonitor` assertions + channel-isolation proofs |
| **`CIRCT ESI`** | `!esi.channel` + services | Single-consumer linearity + latency-insensitive backpressure | Transport-agnostic | Typed channel ABI + service manifest |
| **`RISC-V RoCC`** | `cmd`/`resp` + `HellaCacheIO` + `PTW` + `TL` | `Decoupled` + `busy` core-fence stall | Mixed: L1-coherent (`mem`/`atlNode`) or incoherent (`tlNode`) | Modular `Sail` ISA + typed effect intrinsics |

---

### 3. Cache-Incoherent DMA Ownership Handoff, `IOMMU`/`CHERI-DMA`, `CXL`, and Preemptive IRQ Concurrency

#### 3.1 The Five-Invariant Linear DMA Protocol

Basis: normative + derived

Safe DMA over non-coherent interconnects requires five coordinated invariants captured by a linear typestate token `DmaInFlight<Dir, CacheLineAligned<T>, Cap>`:

1. **Physical pinning**: Page frames must remain physically immobile (no swap/compaction/migration) throughout the transfer.
2. **Spatial/temporal bounds (`IOMMU` IOVA or `CHERI-DMA`)**: Hardware translation/capability enforcement must restrict peripheral access strictly to the granted buffer and direction.
3. **Exclusive linear ownership surrender**: Submitting a descriptor linearly revokes CPU reads/writes to the buffer *and its entire enclosing cache lines* until completion. Rust `Pin<&mut [u8]>` enforces none of physical frame pinning, cache-line exclusivity, or asynchronous hardware ownership handoff.
4. **Explicit cache maintenance & cache-line exclusivity**: Flush dirty CPU lines to PoC before `DMA_TO_DEVICE`; ensure clean/invalid lines before `DMA_FROM_DEVICE` and invalidate *after* completion—strictly on cache-line-aligned non-shared buffers.
5. **Completion barrier & revocation**: Observe hardware completion, execute `DSB SY` + post-DMA invalidation, and unmap/invalidate IOTLB entries before reclaiming memory.

#### 3.2 ARMv8 Cache Maintenance, False-Sharing Tearing Impossibility, and Speculative Prefetching

Basis: source + execution + derived

In `torvalds/linux@4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:
- `arch/arm64/mm/cache.S:135-168` (`__dcache_inval_poc_nosync`) computes line size from `CTR_EL0.DminLine`, executes **`dc civac`** (clean + invalidate) on unaligned start/end boundary lines (L141, L145), **`dc ivac`** (pure invalidate) on interior aligned lines (L147), and **`dsb sy`** (`__pi_dcache_inval_poc`, L165). `DMA_TO_DEVICE` runs **`dc cvac`** + **`dsb sy`** (`__pi_dcache_clean_poc`, L195–199).
- `Documentation/core-api/dma-api.rst:234-246` explicitly warns that memory coherency operates at cache-line width, mapped regions must begin and end on cache-line boundaries, and *the API does not enforce this requirement*.

**Derived Impossibility Result (exhaustively verified in `support/verify_mmio_dma_axi_and_dpr.py`, Part 1)**: When an unaligned `DMA_FROM_DEVICE` buffer `D` (initial `0x0`, device writes `0xAA`) shares a 64B cache line with an adjacent CPU field `C` (initial `1`, CPU writes `2`), **no** ARMv8 cache maintenance instruction (`DC CIVAC`, `DC IVAC`, or `DC CVAC`) preserves `(D == 0xAA, C == 2)` across all interleavings. Furthermore, even with `CacheLineAligned` linear ownership and pre-DMA `DC CIVAC`, omitting post-DMA `DC IVAC` fails due to hardware speculative prefetching:

| Litmus Scenario (`support/verify_mmio_dma_axi_and_dpr.py`) | States | Terminals | Violations | Minimal Counterexample Witness |
|---|---:|---:|---:|---|
| Shared-line `DMA_FROM_DEVICE` + `DC CIVAC` | 23 | 4 | **2** | `CPU_STORE_ADJ_C=2` $\to$ `DMA_WRITE_DRAM_D=0xAA` $\to$ `CPU_DC_CIVAC+DSB_SY` (dirty WB clobbers DRAM `D` to `0x0`) $\to$ `cpu_read=(0x0, 2)` |
| Shared-line `DMA_FROM_DEVICE` + `DC IVAC` | 27 | 6 | **4** | `DMA_WRITE_DRAM_D=0xAA` $\to$ `CPU_STORE_ADJ_C=2` $\to$ `CPU_DC_IVAC+DSB_SY` (discards dirty `C=2`) $\to$ `cpu_read=(0xaa, 1)` |
| Shared-line `DMA_FROM_DEVICE` + `DC CVAC` | 25 | 5 | **3** | `CPU_STORE_ADJ_C=2` $\to$ `DMA_WRITE_DRAM_D=0xAA` $\to$ `CPU_DC_CVAC+DSB_SY` (dirty WB clobbers `D`) $\to$ `cpu_read=(0x0, 2)` |
| `CacheLineAligned` `DMA_FROM_DEVICE` **missing post-`DC IVAC`** | 64 | 9 | **3** | `PRE_DMA_DC_CIVAC_L0+DSB_SY` $\to$ `HW_SPEC_PREFETCH_L0` (refills stale `0x55`) $\to$ `DMA_WRITE_DRAM_D=0xAA` $\to$ `SKIP_POST_DMA_IVAC` $\to$ `cpu_read=(0x55, 2)` |
| **`CacheLineAligned` linear `DMA_FROM_DEVICE` + pre-`CIVAC` + post-`IVAC`** | **56** | **6** | **0** | **Proven sound**: `L0` never dirties during DMA; post-`DC IVAC` purges any speculatively prefetched clean copy |
| `DMA_TO_DEVICE` without `DC CVAC` | 4 | 2 | **1** | `DMA_READ_DRAM` reads stale `0x0` while `0xbb` sits dirty in cache |
| **`DMA_TO_DEVICE` with `DC CVAC + DSB SY`** | **6** | **2** | **0** | **Proven sound**: dirty line flushed to PoC before DMA read |
| **`DMA_TO_DEVICE` with `CXL.cache` snoop** | **4** | **2** | **0** | **Proven sound**: hardware snoop observes dirty host line `0xbb` |

#### 3.3 `IOMMU` Vulnerabilities (`Thunderclap`), `CHERI-DMA`, and `CXL 2.0/3.0` Coherence

Basis: documentation + normative + derived

- **`Thunderclap` (NDSS 2019, DOI `10.14722/ndss.2019.23194`)**: Markettos et al. showed commodity 4 KiB page-granular IOMMUs allow untrusted peripherals to corrupt unrelated kernel/user data sharing the same 4 KiB page as a small DMA buffer, exploit deferred IOTLB invalidations, and abuse overly broad OS mappings.
- **`CHERI-DMA` (HASP 2020, `dblp:conf/micro/MarkettosBBNMW20`)**: Markettos, Baldwin, Bukin, Neumann, Moore, and Watson proposed capability-checked DMA requests (and bridges such as `CapChecker`) enforcing byte-exact bounds, directional permissions, and unforgeable provenance directly on peripheral memory transactions.
- **`CXL 2.0/3.0` (`CXL.io`, `CXL.cache`, `CXL.mem`)**: Over PCIe 5.0 (32 GT/s, CXL 2.0) and PCIe 6.0 PAM4 (64 GT/s, multi-level switches & multi-host memory sharing, CXL 3.0), `CXL.io` remains non-coherent PCIe-equivalent DMA, **`CXL.cache`** lets Type 1/2 accelerators coherently cache/snoop host memory (eliminating software `DC CVAC`/`DC IVAC`), and **`CXL.mem`** maps Host-managed Device Memory (`HDM`) into cacheable host space with CXL 3.0 Back-Invalidation (`BI`). Hardware coherence removes invariant 4 (cache maintenance) but **not** invariants 1, 2, 3, or 5—linear ownership remains mandatory against SW/HW data races.

#### 3.4 Preemptive IRQs, Baker's Stack Resource Policy (`SRP`), `RTIC`, and Lost-Wakeup Traces

Basis: normative + source + execution + derived

Hardware IRQs create asymmetric preemptive concurrency: ISRs preempt lower-priority code at arbitrary instructions and cannot block on sleeping locks.

1. **Baker's `SRP` (1991, DOI `10.1007/BF00365393`)**: Assign each resource $R$ static ceiling $\lceil R \rceil = \max\{\pi(J) \mid J \text{ accesses } R\}$, and maintain dynamic system ceiling $\Pi = \max\{\lceil R \rceil \mid R \text{ locked}\}$. Job $J$ preempts iff $\pi(J) > \pi(\text{current}) \land \pi(J) > \Pi$. Baker proved: (i) **zero deadlocks**, (ii) **single-blocking bound**, (iii) **single shared LIFO stack**, and (iv) **zero data races**.
2. **`RTIC` static implementation (`rtic-rs/rtic@fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`)**:
   - `rtic-macros/src/syntax/analyze.rs:67-133,205-240` validates equal-priority `lock_free` resources and computes `Ownership::Contended { ceiling: cmp::max(ceiling, priority) }`.
   - `rtic/src/export/cortex_basepri.rs:62-84` emits the hardware ceiling lock:
     ```rust
     let current = basepri::read();
     basepri_max::write(cortex_logical2hw(ceiling, nvic_prio_bits));
     cortex_m::asm::isb(); // serializes new BASEPRI mask before accessing *ptr
     let r = f(&mut *ptr);
     asm!("", options(nostack, preserves_flags)); // compiler barrier before restore
     basepri::write(current);
     ```
     Two barriers are mandatory: `isb` forces Cortex-M `BASEPRI` masking to take effect before resource access, and the empty `asm!` prevents LLVM from sinking accesses past `basepri::write(current)`. Maximum-priority ceilings fall back to `critical_section::with` (`PRIMASK`, L69–70); tasks already at priority $C$ incur zero masking overhead.
3. **Level- vs. edge-triggered IRQ failure traces**: Failing to clear (or flush posted writes to) a level-IRQ status register causes an infinite **interrupt storm**. For edge-triggered IRQs / MSI-X, polling empty and then issuing unmasked `WFI` permits an intervening edge pulse + ISR acknowledgement to be consumed before sleep, causing a permanent **lost-wakeup deadlock**. Masking IRQs *before* polling—exploiting architectural ARMv8/Cortex-M/RISC-V `WFI` wakeup on pending enabled interrupts while masked—closes the window.

**Probe verification (`support/verify_mmio_dma_axi_and_dpr.py`, Part 4)**:
- **SRP vs. unprotected preemption** (`T1(1)`, `T2(2)`, `T3(3)`, shared `R` with $\lceil R \rceil = 3$): unprotected yields `3` data races across `45` states (`PREEMPT_ENTER_T1 -> T1_LOCK_R -> PREEMPT_ENTER_T3 -> DATA_RACE`); Baker SRP with saved/restored `BASEPRI` proves **`0` data races, `0` deadlocks, `0` LIFO stack violations across `40` states**.
- **Edge-IRQ product automaton**: unmasked poll-then-`WFI` reaches `1` lost-wakeup deadlock across `16` states (`DRV_POLL_SAW_EMPTY -> DEV_DATA_READY_PULSE_EDGE_IRQ -> EDGE_IRQ_PREEMPTS_BEFORE_WFI_ACKED -> DRV_WFI_UNMASKED_SLEEP`); masked poll-then-`WFI` proves **`0` lost wakeups across `14` states**.

---

### 4. Cycle-Accurate RTL $\sqsubseteq$ TLM Stuttering Refinement and Typed FPGA Dynamic Partial Reconfiguration (DPR)

#### 4.1 Cycle-Accurate RTL $\sqsubseteq$ TLM Stuttering Refinement and Progress Measures

Basis: normative + documentation + source + derived

Pipelined RTL executes variable numbers of stall, bubble, and arbitration cycles per logical software transaction (`TLM`), requiring **stuttering refinement**:

1. **Safety vs. liveness (`Namjoshi 1997`, DOI `10.1007/BFb0058037`; `Manolios 2000`, DOI `10.1007/3-540-40922-X_11`)**: Each RTL step either matches an abstract TLM step with identical external observations or stutters silently ($\tau$). Prefix trace inclusion proves *safety* but admits infinite silent stalls; proving *liveness* (Well-Founded Equivalence Bisimulation, `WEB`) requires a well-founded ranking function $\rho : \text{State}_{\text{RTL}} \to (W, \prec)$ strictly decreasing on every silent step ($\rho(c') \prec \rho(c)$).
2. **Mechanized hardware refinement stacks**:
   - **`Kami` (`mit-plv/kami@9217329eb4e1...:Kami/Semantics.v:1047-1073`)**: Defines modular `traceRefines p m1 m2` (`ma <<== mb`) over hidden-internal `Behavior` label sequences (`equivalentLabelSeq`), supporting horizontal subsystem substitution.
   - **`Bedrock2` (`mit-plv/bedrock2@0005c47b5eaa...:processor/src/processor/KamiRiscv.v:162-167`)**: Directly proves the stuttering disjunction `kstep1_sound`:
     ```coq
     Theorem kstep1_sound: forall ks1 ks2 rs1 P,
       related ks1 rs1 -> kstep1 ks1 ks2 -> cstep1 rs1 P ->
       related ks2 rs1 \/ exists rs2, related ks2 rs2 /\ P rs2.
     ```
     mapping silent steps (`KamiSilent`) to `nt = []` in `KamiLabelSeqR` (L133–140, 183–188).
   - **`Kôika` (`mit-plv/koika@8921e30434d9...:coq/OneRuleAtATime.v:279-293`)**: Proves `Theorem OneRuleAtATime`:
     ```coq
     Theorem OneRuleAtATime: forall s log,
       interp_scheduler r sigma rules s = log ->
       exists rs,
         (forall rl, List.In rl rs -> List.In rl (scheduler_rules s)) /\
         List.fold_left interp_oraat rs r = commit_update r log.
     ```
     collapsing concurrent single-cycle EHR schedules into sequential rule application.
   - **`Filament` (`cucapra/filament@3c17db5ce85c...`, PLDI 2023, DOI `10.1145/3591234`)**: Encodes pipeline timing intervals (`@[G, G+k)`) directly in the type system, statically rejecting structural hazards and misaligned multi-cycle joins.

#### 4.2 Typed FPGA Dynamic Partial Reconfiguration (`DPR` / `DFX`)

Basis: documentation + source + execution + derived

**Dynamic Partial Reconfiguration (`DPR`)** / AMD Xilinx **Dynamic Function eXchange (`DFX`, `UG909`)** reloads SRAM configuration frames of a live **Reconfigurable Partition (`RP`)** via `ICAP`/`MCAP` while the **Static Shell** (PCIe, DDR, AXI fabric, host CPU) runs continuously. Three failure modes arise when DPR is untyped:

1. **Orphaned in-flight AXI bursts $\implies$ PCIe bus wedge**: Clamping boundary wires while any host `AR` or `AW`/`W` burst awaits `RLAST`/`BVALID` triggers a PCIe Root Complex **Completion Timeout** (AER Fatal Error), permanently wedging the host link.
2. **Floating wire glitches during ICAP write**: Unclamped RP outputs toggle randomly while LUT/routing frames rewrite, injecting spurious `VALID`/IRQ pulses into the static shell.
3. **Post-swap ABI drift**: Swapping `AcceleratorV1` for `AcceleratorV2` changes register/channel layouts; any surviving stale software handle silently corrupts the new hardware image.

**Examined hardware IP & kernel flow**:
- **`AMD PG374` (`DFX Controller`)** orchestrates shutdown requests (`rm_shutdown_req`) and partial bitstream DMA to `ICAP`.
- **`AMD PG375` (`DFX Decoupler`)** clamps boundary signals to static defaults during reconfiguration (insufficient alone on active AXI buses).
- **`AMD PG377` (`DFX AXI Shutdown Manager`)** achieves protocol-compliant AXI4-MM/AXI4-Lite quiescence prior to decoupling: new arrivals receive clean `SLVERR` (or configurable `DECERR`/`OKAY`/`BACKPRESSURE`) while in-flight read/write bursts drain to `0`, only then signaling quiescence for `PG375`.
- **Linux `fpga_region_program_fpga` (`torvalds/linux@4405c18c95d2...:drivers/fpga/fpga-region.c:97-159`)** sequences `region->mutex`, `fpga_mgr_lock`, `fpga_bridges_disable` (L127), `fpga_mgr_load` (L133), and `fpga_bridges_enable` (L139)—providing no static typestate proof that active AXI/DMA handles were drained or that stale `OldABI` driver handles were invalidated (relying on runtime discipline and optional `compat_id`).

**Linear Typestate DPR Protocol**:
```text
ReconfigPartition<OldABI>
  --[ request_shutdown(): linearly consumes OldABI handle ]-->
DrainingPartition (PG377 drains inflight rd/wr; rejects new arrivals with SLVERR)
  --[ await_quiescence() [rd == 0 /\ wr == 0] -> assert_decouple() (PG375) ]-->
QuiescedDecoupled (all RP wires clamped; zero in-flight bursts)
  --[ load_authenticated_bitstream<NewABI>(bitstream, proof_cert) ]-->
ResetAndRelease --[ release_decouple() ]--> ReconfigPartition<NewABI>
```

**Probe verification (`support/verify_mmio_dma_axi_and_dpr.py`, Part 3)** across concurrent host AXI reads/writes (`MAX_INFLIGHT = 2`), `SLVERR` rejections, floating ICAP glitches, and ABI swaps:

| DPR Protocol Variant | States | Bus Wedges | Glitch Leaks | ABI Mismatches | Minimal Counterexample / Outcome |
|---|---:|---:|---:|---:|---|
| `naive_decouple` (no AXI drain) | 21 | **8** | 0 | **1** | `HOST_ISSUE_AXI_READ -> NAIVE_DECOUPLE_ORPHANS_INFLIGHT(rd=1,wr=0)->PCIE_BUS_WEDGE` |
| `drain_without_decoupler` (omits `PG375`) | 20 | 0 | **1** | 0 | `SHUTDOWN_REQ_ENTER_DRAINING -> SKIP_DECOUPLE_START_ICAP_V2 -> FLOATING_RP_GLITCH_LEAKED_TO_STATIC_SHELL` |
| `drain_without_abi_witness` (stale `OldABI` handle) | 22 | 0 | 0 | **1** | `... -> HOST_ISSUE_RD_WITH_STALE_ABI_V1_VS_HW_ABI_V2` |
| **`linear_typestate_dpr` (`PG377`+`PG375`+ABI token)** | **37** | **0** | **0** | **0** | **Proven safe** across all reachable interleavings |

---

### 5. Cross-Cutting Synthesis: Composition Contract for Verified SW↔HW Toolchains

Basis: derived

| Boundary Seam | Physical Failure Mode | Minimal Type / Protocol Invariant | Mechanized / Formal Witness | Compiler + Hardware Co-Obligation |
|---|---|---|---|---|
| **MMIO Registers** | Tearing, `W1C`/FIFO corruption, speculation, offset drift | Disjoint MMIO domain; width-indexed `RO`/`WO`/`W1C`/FSM handles; `Device-nGnRnE` | `Bedrock2` `end2end_lightbulb` / `Pancake` `ShMemLoad`/`ShMemStore` | Exact single-beat width; no hoisting; unified SW+RTL register schema |
| **Interconnects (`AXI4`, `TL-C`, `ESI`)** | `VALID`/`READY` deadlock, 4 KiB crossing, MSHR deadlock | `VALID` independent of `READY`; 4 KiB splitting; $A \ll B \ll C \ll D \ll E$; single-consumer channels | Acyclicity + priority monotonicity; `TLMonitor` assertions | Never share FIFOs across TL-C priority levels; split DMA at 4 KiB |
| **Coprocessors (`RoCC`)** | Unseen L1/PTW aliasing, scratchpad mutation, missing fences | Effect signature `(MemSet, CoherenceDomain, HiddenState, Fence)` | Modular `Sail` ISA + `Kôika`/`Filament` coprocessor | Replace inline `asm` with typed effectful intrinsics |
| **DMA & IRQs** | Cache-line tearing, spec-prefetch stale read, sub-page IOMMU leak, ISR race, lost wakeup | 5-invariant linear DMA + `CacheLineAligned` (or `CXL.cache`) + `CHERI-DMA`; Baker SRP `BASEPRI`; masked-WFI | Exhaustive ARMv8 litmus + SRP + IRQ proofs (`verify_mmio_dma_axi_and_dpr.py`) | Enforce cache-line exclusivity statically; emit `isb` + compiler barriers around masks |
| **RTL $\sqsubseteq$ TLM & FPGA `DPR`** | Silent stall; PCIe bus wedge; floating ICAP glitch; ABI drift | Stuttering simulation + well-founded rank; `PG377` drain $\to$ `PG375` decouple $\to$ linear `NewABI` | `Kami` `traceRefines`, `Kôika` `OneRuleAtATime`, `Manolios` WEB, DPR BFS | Never decouple with `inflight > 0`; linearly consume `OldABI` before swap |

## Boundaries

- **not examined**:
  - **Multi-core real-time locking** (e.g., `MSRP` spin-ceilings across SMP cores) and virtualized interrupt routing (`ARM GICv3/v4` ITS/vLPI, `RISC-V AIA` IMSIC) beyond single-core NVIC/CLIC masking.
  - **Other coherent fabrics & PCIe wire ordering**: `ARM AMBA CHI` (`IHI 0050`), `Intel UPI`/`AMD Infinity Fabric`, and full PCIe TLP ordering (`Relaxed Ordering`, `ATS`/`PRI` fault recovery).
  - **Physical timing closure, analog electricals, and CDC metastability**: Stuttering refinement operates at synchronous RTL cycle granularity and does not replace `STA` or CDC sign-off.
  - **Bitstream cryptographic verification internals** (AES-GCM/RSA/ECDSA inside `ICAP`/`CSU`/`PMC`) beyond treating authentication as a precondition to minting `ReconfigPartition<NewABI>`.
- **unknown**:
  - **Vendor-specific microarchitectural prefetcher corner cases** across ARMv8/RISC-V cores (e.g., cross-page prefetching under vendor `CPUECTLR` settings); the probe conservatively allows unconstrained clean speculative prefetching of any cacheable line.
  - **Unified axiomatic CXL 3.0 weak-memory model**: No machine-checked axiomatic model composing `aarch64.cat`/`riscv.cat`/`x86tso.cat` with multi-host CXL 3.0 `BI` + `CXL.mem` + `CXL.cache` + `CXL.io` ordering was found in the examined sources.
- **known not to apply**:
  - **ARMv8 `DC CVAC`/`DC IVAC` maintenance is unnecessary on hardware-snooped I/O paths** (standard x86-64 snooped PCIe and `CXL.cache`), though pinning, IOMMU/capability bounds, linear ownership, and ordering fences still apply.
  - **Single-core SRP `lock_free` guarantees do not hold on SMP**: `RTIC`'s equal-priority `lock_free` optimization (`analyze.rs:67-109`) relies on single-core non-preemption.
  - **`Bedrock2` `end2end_lightbulb` does not establish liveness or timing bounds**: Prefix safety (`End2EndLightbulb.v:167-175`) is vacuously satisfied by silent non-progress without a Namjoshi/Manolios progress rank.
- **unsupported**:
  - **`CIRCT ESI` auto-generated software APIs (`docs/Dialects/ESI/software_api.md:5`)**: Explicitly marked `**unimplemented**` in the examined upstream specification doc.
  - **Compile-time cache-line alignment enforcement in Linux `dma-api`**: Explicitly unenforced per `Documentation/core-api/dma-api.rst:240-241`.
  - **Static drain and ABI-handle invalidation in Linux `fpga_region`**: `drivers/fpga/fpga-region.c:97-159` provides runtime mutex/bridge callbacks without static handle consumption or ABI typestate checks.

## Evidence

All primary evidence was retrieved and verified on `2026-11-19`.

### Directly Examined Git Sources (Pinned 40-Character Revisions)

1. **`mit-plv/bedrock2` @ `0005c47b5eaa720bdcb9b94aceaca9f42726b861`**: `end2end/src/end2end/End2EndLightbulb.v:49-57,136-175` (`spec`, `iohi_to_iolo`, `prefix_of`, `end2end_lightbulb`); `End2EndPipeline.v:274-301` (`end2end`); `Bedrock2SemanticsForKami.v:10-14` (`MMIOREAD`/`MMIOWRITE`); `PrintAdmits.v:1-8`; `compiler/src/compiler/MMIO.v:40-94` (`compile_interact`, `compile_interact_length`, `compile_interact_emits_valid`); `processor/src/processor/KamiRiscv.v:133-140,162-196,478-496,549-588` (`KamiLabelSeqR`, `kstep1_sound`, `riscv_init_memory_undef_on_MMIO`, `proc_correct`).
2. **`mit-plv/kami` @ `9217329eb4e1d751f28ab175ebab230b1e8fd4da`**: `Kami/Semantics.v:380-480,724-727,936-940,1018-1073` (`SemAction`, `Step`, `Multistep`, `Behavior`, `equivalentLabelSeq`, `traceRefines`, `<<==`).
3. **`mit-plv/koika` @ `8921e30434d9e351c49df84c9aa14e72b0456ad0`**: `coq/OneRuleAtATime.v:26-55,243-293` (`interp_scheduler'_trace`, `Theorem OneRuleAtATime`).
4. **`CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`**: `pancake/README.md:1-102`; `pancake/panLangScript.sml:67-69,91-96` (`opsize`, `ShMemLoad`, `ShMemStore`); `pancake/semantics/panSemScript.sml:55-61,511-555,605-614` (`memaddrs`, `sh_memaddrs`, `sh_mem_load_def`, `sh_mem_store_def`, `SharedMem MappedRead|MappedWrite`); `pancake/proofs/pan_to_targetProofScript.sml:1285-1328,2572` (`pan_to_target_compile_semantics`).
5. **`chipsalliance/rocket-chip` @ `ece7b9ad544b07df39cd13b6fd7236562a26355d`**: `src/main/scala/tile/LazyRoCC.scala:24-115` (`RoCCInstruction`, `RoCCCoreIO`, `RoCCIO`, `HasLazyRoCC`); `src/main/scala/rocket/IDecode.scala:526-552` (`RoCCDecode`); `src/main/scala/tilelink/Bundles.scala:35-129` (`TLMessages`, `TLPermissions`); `src/main/scala/tilelink/Monitor.scala:35-100` (`TLMonitor`, `legalizeFormatA`).
6. **`llvm/circt` @ `203f159ce10d78940df4264327d5f3fc8b902112`**: `include/circt/Dialect/ESI/ESIChannels.td:33-139` (`ChannelSignaling`, `ChannelTypeImpl`, `hasOneConsumer`, `SnoopValidReadyOp`); `ESITypes.td:19-37` (`ESIListType`); `ESIServices.td:23-130` (`CustomServiceDeclOp`, `ServiceInstanceOp`, `ServiceImplementReqOp`); `ESIStdServices.td:15-120`; `docs/Dialects/ESI/services.md:29-109`; `software_api.md:1-24`.
7. **`rtic-rs/rtic` @ `fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`**: `rtic-macros/src/syntax/analyze.rs:67-133,205-240` (`lock_free`, `Ownership::Contended`); `rtic/src/export/cortex_basepri.rs:61-84` (`lock`, `basepri_max::write`, `isb`, compiler barrier).
8. **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`**: `arch/arm64/mm/cache.S:114-117,135-168,195-199` (`__dcache_inval_poc_nosync`, `dcache_clean_poc`); `Documentation/core-api/dma-api.rst:234-247`; `drivers/fpga/fpga-region.c:97-159` (`fpga_region_program_fpga`).
9. **`cucapra/filament` @ `3c17db5ce85c354dd3da0af57f3adcb59bb295ac`**: `README.md` (timeline-typed pipelined HDL overview).

### Verified Publications and Normative Specifications

- Erbsen, Gruetter, Choi, Wood, Chlipala, *"Integration Verification Across Software and Hardware for a Simple Embedded System"*, PLDI 2021, DOI `10.1145/3453483.3454069`.
- Choi, Vijayaraghavan, Sherman, Chlipala, Arvind, *"Kami: A Platform for High-Level Parametric Hardware Specification and Its Modular Verification"*, ICFP 2017, DOI `10.1145/3110268`.
- Bourgeat, Pit-Claudel, Chlipala, Arvind, *"The Essence of Bluespec: A Core Language for Rule-Based Hardware Design"*, PLDI 2020, DOI `10.1145/3385412.3385965`.
- Nigam, Azevedo de Amorim, Sampson, *"Modular Hardware Design with Timeline Types"*, PLDI 2023, DOI `10.1145/3591234`.
- Åman Pohjola et al., *"Pancake: Verified Systems Programming Made Sweeter"*, PLOS '23, DOI `10.1145/3623759.3624544`; Zhao et al., *"Verifying Device Drivers with Pancake"*, `arXiv:2501.08249` (v2, May 2025), DOI `10.48550/arXiv.2501.08249`; Murphy et al., *"High-Fidelity Specification of Real-World Devices"*, PLOS '25, DOI `10.1145/3764860.3768335`.
- Arm Limited, *AMBA AXI and ACE Protocol Specification* (`ARM IHI 0022`, §A3.3.1, §A3.4.1, Chapter A5).
- SiFive / CHIPS Alliance, *TileLink Specification* (`v1.8.1` / `v1.9.3`).
- Compute Express Link Consortium, *CXL 2.0* and *CXL 3.0* Specifications (`CXL.io`, `CXL.cache`, `CXL.mem`).
- Markettos et al., *"Thunderclap: Exploring Vulnerabilities in Operating System IOMMU Protection via DMA from Untrustworthy Peripherals"*, NDSS 2019, DOI `10.14722/ndss.2019.23194`; Markettos, Baldwin, Bukin, Neumann, Moore, Watson, *"Position Paper: Defending Direct Memory Access with CHERI Capabilities"*, HASP '20, pp. 7:1–7:9, `dblp:conf/micro/MarkettosBBNMW20`.
- Baker, *"Stack-Based Scheduling of Realtime Processes"*, *Real-Time Systems* 3(1):67–99, 1991, DOI `10.1007/BF00365393`.
- Namjoshi, *"A Simple Characterization of Stuttering Bisimulation"*, FSTTCS 1997, DOI `10.1007/BFb0058037`; Manolios, *"Correctness of Pipelined Machines"*, FMCAD 2000, DOI `10.1007/3-540-40922-X_11`.
- AMD / Xilinx, `UG909` (*Dynamic Function eXchange*), `PG374` (*DFX Controller*), `PG375` (*DFX Decoupler*), `PG377` (*DFX AXI Shutdown Manager*).

### Preserved Standalone Verification Execution

Run on `2026-11-19` (Python 3.10+ stdlib only, exit code `0`):
```console
python3 -B reports/verified-software-hardware-ffi-mmio-dma-interconnects-and-reconfigurable-fabrics/support/verify_mmio_dma_axi_and_dpr.py
```

Observed output:
```text
[PASS] 1. Non-coherent ARMv8 Cache+DRAM+DMA Litmus Verifier:
       - Unaligned shared-line DMA_FROM_DEVICE (DC_CIVAC): states=23, corrupt_terminals=2/4
       - Unaligned shared-line DMA_FROM_DEVICE (DC_IVAC): states=27, corrupt_terminals=4/6
       - Unaligned shared-line DMA_FROM_DEVICE (DC_CVAC): states=25, corrupt_terminals=3/5
       - Aligned DMA_FROM_DEVICE missing post DC_IVAC (spec-prefetch hazard): states=64, violations=3/9
       - CacheLineAligned linear DMA_FROM_DEVICE + pre-CIVAC + post-IVAC: states=56, violations=0/6 (PROVEN SOUND)
       - DMA_TO_DEVICE: no_clean violations=1, dc_cvac violations=0, cxl_cache violations=0
[PASS] 2. AXI4 Causality & TileLink-C Priority Acyclicity Verifier:
       - AXI4 compliant cycle=None; AWVALID->AWREADY=['AWREADY', 'AWVALID', 'AWREADY']; WVALID->AWREADY=['AWREADY', 'WVALID', 'AWREADY']; BVALID->BREADY=['BREADY', 'BVALID', 'BREADY']
       - AXI4 4KiB burst rule: 0x10000f80+128B legal=True, 0x10000f80+136B legal=False
       - TileLink-C A<B<C<D<E acyclic=True, shared A/C cycle=['A', 'B', 'C', 'A'], shared A/E cycle=['A', 'B', 'C', 'D', 'E', 'A'], 2-client separate deadlocks=0, shared-A/C deadlocks=1
[PASS] 3. Linear Typestate FPGA DPR Decoupler Verifier:
       - Naive decouple: states=21, bus_wedges=8
       - Drain w/o decoupler: states=20, glitch_leaks=1
       - Drain w/o ABI witness: states=22, abi_mismatches=1
       - Linear typestate + AxiShutdownManager: states=37, wedges=0, glitch_leaks=0, abi_mismatches=0 (PROVEN SAFE)
[PASS] 4. Baker SRP Priority-Ceiling & Edge-IRQ Lost-Wakeup Verifier:
       - Unprotected preemption: states=45, races=3
       - Baker SRP (ceiling=3): states=40, races=0, deadlocks=0, lifo_violations=0
       - Edge IRQ unmasked-poll: states=16, lost_wakeups=1
       - Edge IRQ masked-WFI: states=14, lost_wakeups=0 (PROVEN LIVE)
```

## Revalidation

1. **Rerun the multi-protocol probe** (`< 1 s`, stdlib only):
   ```console
   python3 -B reports/verified-software-hardware-ffi-mmio-dma-interconnects-and-reconfigurable-fabrics/support/verify_mmio_dma_axi_and_dpr.py --json
   ```
   Encode any candidate DMA cache-maintenance sequence, bus dependency graph, DPR decoupler FSM, or IRQ wait protocol directly into the script and verify `0` reachable violations.
2. **Diff narrow upstream regions against `REPORT.json` revisions**:
   - `mit-plv/bedrock2`: `End2EndLightbulb.v`, `compiler/MMIO.v`, `KamiRiscv.v` (`kstep1_sound`) for liveness, DMA, or IRQ extensions.
   - `CakeML/cakeml`: `pancake/semantics/panSemScript.sml` (`sh_mem_load_def`/`sh_mem_store_def`) and `pan_to_targetProofScript.sml` (`pan_to_target_compile_semantics`).
   - `llvm/circt`: `include/circt/Dialect/ESI/{ESIChannels,ESIStdServices}.td` and `docs/Dialects/ESI/software_api.md` (check if software API generation leaves `unimplemented`).
   - `chipsalliance/rocket-chip`: `tile/LazyRoCC.scala` and `tilelink/Monitor.scala`.
   - `torvalds/linux`: `arch/arm64/mm/cache.S` (`__dcache_inval_poc_nosync`) and `drivers/fpga/fpga-region.c` (`fpga_region_program_fpga`).
   - `rtic-rs/rtic`: `rtic/src/export/cortex_basepri.rs` (`lock`) and `rtic-macros/src/syntax/analyze.rs`.
3. **Normative revision checks**: Re-verify `ARM IHI 0022` (or AXI5 extensions), CXL 3.1+ `BI` coherence rules, and newer AMD Versal/UltraScale+ `PG377` shutdown modes before extending these claims to unmodeled silicon features.
