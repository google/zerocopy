# Non-Von-Neumann CPU, Dataflow, Spatial CGRA, Tile-BSP, Deterministic Streaming, PIM, and Reversible Compiler Architectures

## Summary

Mainstream systems languages (`C`, `C++`, and LLVM-targeted backends) hardcode six 1970s Von Neumann machine assumptions: (1) a mutable spatial register file, (2) eager synchronous trapping with global sticky status flags, (3) a flat byte-addressed cache-coherent address space, (4) arbitrary fine-grained shared-memory thread interleaving, (5) unobservable wall-clock execution time, and (6) free destructive bit erasure. Compiling onto non-Von-Neumann silicon exposes these as **historical contingencies**, while surfacing irreducible **VLSI and thermodynamic realities** (bypass fan-in, wire delay, SRAM bank/port limits, coherence energy, pipeline depth, and Landauer's $k_B T \ln 2$ erasure bound) that clean-slate compiler IRs and type systems must reify directly.

Across nine examined architectural families—**Mill CPU**, **EDGE/TRIPS**, **Plasticine/Spatial/SambaNova RDU**, **Cerebras WSE-2/WSE-3 (`CSL`)**, **Graphcore IPU (`Poplar` BSP)**, **Tenstorrent Tensix (`TT-Metalium`)**, **Groq TSP/LPU**, **UPMEM DPU / Samsung HBM-PIM**, and **Janus / Pendulum (`PISA`)**—compilation friction and verification obligations collapse onto six orthogonal IR and type-system primitives:

1. **Bounded-window temporal / block-argument / region dataflow IRs** (de Bruijn temporal offsets for Mill belts; RVSDG single-entry/single-exit regions with explicit state edges for EDGE hyperblocks and Mill Extended Basic Blocks), eliminating mutable register allocation and Briggs/Sreedhar $\phi$-copy cycles.
2. **First-class speculative value and metadata lattices** (`None > NaR(fault_kind, origin_pc) > Value(payload, width, fp_flags)` on Mill vs. software-only LLVM `poison`/`undef`/`freeze`) paired with explicit lossy-projection codecs across untagged byte memory.
3. **Phased modulo-loop combinators and vector mask smears** (`RETIRE`, rotating scratchpads, `smear`/`smearx`), collapsing software-pipelined and irregular early-exit loops into one steady-state kernel without peel/prologue/epilogue duplication.
4. **Explicit memory-hierarchy, banking, and alignment-qualified regions** (private scratchpads, 16-bank PMUs, 48 KB PE SRAMs, bank-isolated 64 MB MRAM with 8-byte / $\le 2048$-byte DMA slices).
5. **Phase-effect, choreographic, and linear circular-buffer protocol types** (Graphcore `Compute -> Sync -> Exchange` phase isolation; Cerebras 24-color acyclic wavelet routing; Tenstorrent SPSC wrap-exact circular buffers and cumulative wait discipline verified against `tenstorrent/tt-metal` headers).
6. **Cycle-indexed timeline types and bijective uncomputation disciplines** (Groq zero-arbiter deterministic streaming with plesiochronous `Deskew`; Janus/PISA forward-and-backward deterministic updates with zero garbage tape).

A standalone Python verifier ([verify_belt_nar_and_bsp_semantics.py](support/verify_belt_nar_and_bsp_semantics.py)) executes and checks concrete operational models of the Mill belt + `None > NaR > Value` + `conform` + `RETIRE`/`smear` semantics, Graphcore BSP phase-effect determinism, Tenstorrent Tensix multi-core circular-buffer invariants (including exact wrap-contiguity, SPSC races, cumulative wait hazards, and 101-state BFS deadlock exploration), and Janus reversible bijections.

## Applicability

This report covers thirteen durable primary subjects pinned in `REPORT.json`, comparing how their hardware execution contracts shape compiler IR design and formal verification:

- **Mill CPU (`Mill Computing, Inc.`)**: Applies to fifteen granted U.S. patents (`US 9,513,904` through `US 11,226,821`) and Mill Computing's official compiler architecture documentation (`LLVM IR -> genAsm -> conAsm`). Family-invariant `genAsm` semantics are separated from member-specific `conAsm` scheduling (*Tin*, *Silver*, *Gold*, varying in belt length, slots, and latencies).
- **Block-atomic dataflow & CGRAs**: Applies to **EDGE/TRIPS** (Burger et al., *IEEE Computer* 2004; Smith et al., CGO 2006), **RVSDG** (Reissmann et al., *ACM TECS* 2020), **Plasticine** (Prabhakar et al., ISCA 2017), **Spatial** (Koeplinger et al., PLDI 2018), and **SambaNova SN40L RDU** (Prabhakar et al., MICRO 2024).
- **Tile, wafer-scale, BSP, and deterministic streaming engines**: Applies to **Cerebras WSE-2 / WSE-3** (`CSL`, Lie, *IEEE Micro* 2023), **Graphcore Colossus GC2 (MK1) / GC200 (MK2)** (`Poplar` BSP, Jia et al., `arXiv:1912.03413v1`), **Tenstorrent Tensix** (`Wormhole` and `Blackhole`, plus observed `ARCH_QUASAR` stubs) inspected directly in `tenstorrent/tt-metal` at commit `11551f901bb3e2ad451a0fe5036312c4687d40c3`, and **Groq TSP/LPU** (Abts et al., ISCA 2020 and ISCA 2022).
- **PIM & reversible computing**: Applies to **UPMEM DPU** (Gómez-Luna et al., *IEEE Access* 2022 / `arXiv:2105.03814`), **Samsung HBM-PIM** (Lee et al., ISCA 2021), and **Janus / Pendulum (`PISA`)** (Yokoyama & Glück, PEPM 2007; Yokoyama, Axelsen & Glück, CF 2008; Landauer 1961).
- **Adjacent corpus cross-references (non-duplicating scope)**:
  - Mechanized LLVM IR `poison`/`undef`/`freeze` semantics (Vellvm, Alive2, Crellvm, `lean-mlir`) and Rust Tree Borrows / machine-frame verification live in `mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames`; this report contrasts Mill's hardware metadata lattice against Lee et al. (PLDI 2017) without repeating those Rust/LLVM tables.
  - Mutable-register parallel-move cycle resolution and spill certificate checkers live in `verified-regalloc2-spill-and-parallel-move-certificate-checker`; this report contrasts Briggs/Sreedhar swap cycles against Mill's simultaneous-read `conform` drops.
  - High-level synchronous dataflow (SCADE/Lustre), aerospace time-triggered verification, EDA/RTL verification, and quantum unitary circuit surveys live in `anneal-cps-robotics-aerospace-eda-and-quantum-survey`; this report focuses on Groq's cycle-exact streaming IR and Janus/PISA classical bijectivity.

Version-specific hardware capacities (`WSE-2` vs. `WSE-3`, `GC2` vs. `GC200`, `Wormhole` vs. `Blackhole`) are distinguished explicitly throughout **Findings**.

## Findings

### 1. Historical Von Neumann Contingencies vs. Physical Hardware Realities

Basis: documentation + source + derived

Every examined architecture strips away dynamic runtime hardware illusions (register renaming, cache coherence directories, OoO schedulers, dynamic bus arbiters, or trace-logging history buffers) and transfers an explicit structural invariant to the compiler boundary. Mainstream C/LLVM IR fails precisely because it erases structural locality, phase boundaries, timing, and bijectivity early into flat CFGs and raw byte pointers.

| Architecture Family | Execution Model | Operand / Local Storage | Sync & Coherence | Core C / LLVM Friction | Required Clean-Slate IR / Types |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Mill CPU** | Wide static-scheduled belt (`genAsm -> conAsm`) | Fixed FIFO belt (`b0..b_{N-1}`) + private `Base`/`Fence` scratchpad | Per-byte valid caches, deferred-load snooping, HW Spiller | Mutable regalloc (`WAR`/`WAW`), $\phi$-cycles, `&local`, `setjmp`, `uintptr_t`, no HW `NaR`/`None` | Bounded de Bruijn SSA, block-arg `conform`, `None > NaR > Value` lattice, phased `RETIRE`/`smear` |
| **EDGE / TRIPS** | Block-atomic intra-block dataflow ($\le 128$ ops) | Direct target-instruction routing on 2D ALU grid | Block-boundary reg/mem commit; intra-block `LSID` tags in LSQ | Basic-block CFGs, linear regalloc, aliasing pointers serializing `LSID`s | Single-entry/single-exit RVSDG regions with state edges and whole-block proofs |
| **Plasticine / Spatial / SambaNova RDU** | Statically configured CGRA streaming dataflow | 16-lane SIMD PCUs + 256 KB banked PMUs (16x16 KB banks) | Word-level switch fabric + input FIFOs + counter-chain backpressure | Pointer-chasing loops hiding affine banking and FIFO bounds | Explicit SRAM/FIFO/pattern IR (`Map`/`Reduce`/`Fold`/`Foreach`), banking & deadlock-free FIFO types |
| **Cerebras WSE-2 / WSE-3 (`CSL`)** | 850k–900k PE wafer-scale wavelet dataflow | 48 KB single-cycle SRAM/PE (40–44 GB total); no shared DRAM | 32-bit wavelets over 24 static virtual channels (`colors`) | No global pointers or coherence; 48 KB limit; untyped colors deadlock | Choreographic / multiparty session types proving color acyclicity, linear wavelets, $\le 48$ KB bounds |
| **Graphcore IPU (`GC2`/`GC200`, `Poplar`)** | 1,216–1,472 MIMD tiles, strict HW BSP | 304–900 MB SRAM; 6 worker + 1 supervisor context/tile | HW global barrier: `Compute` (local) -> `Sync` -> `Exchange` | Arbitrary shared-memory interleavings and locks break static schedules | BSP phase-effect types (`ComputePhase` vs. `ExchangePhase`) reducing proofs to per-tile + permutation |
| **Tenstorrent Tensix (`Wormhole`/`Blackhole`)** | 5 bare-metal RV32IM cores/tile (`BRISC`, `NCRISC`, `TRISC0..2`) | 1,464–1,536 KiB L1 SRAM + 2–8 KiB per-core local SRAM | Dual 2D NoC (`0`/`1`) unicast/multicast DMA, semaphores, 32–64 SPSC CBs | 3–5 separate C++ files linked by untyped CB IDs, raw L1 offsets, manual barriers | Single-source 5-core choreographies, linear wrap-exact SPSC CB tokens, typed NoC rectangles |
| **Groq TSP / LPU** | 100% compiler-scheduled, zero-arbiter VLIW | 220 MB SRAM; 320-lane (20x16) streaming conveyor | Cycle-exact slices (`MEM`/`MXM`/`VXM`/`SXM`/`ICU`); C2C `Deskew` | Zero wall-clock time (`t : Nat`) in LLVM IR; no dynamic slice branching | Cycle-indexed timeline types verifying spatial arrival alignment and static WCET |
| **UPMEM DPU / HBM-PIM** | Bank-local 32-bit RISC DPUs (24 tasklets) / bank PCUs | UPMEM: 64 MB MRAM + 64 KB WRAM + 24 KB IRAM per DPU | No inter-DPU network (host shuffles); explicit MRAM<->WRAM DMA | Host/DPU pointer disjointness; faults on unaligned or $>2048$ B DMA | Bank-indexed `DistributedArray<BankId, T>`, `Aligned8` bounded DMA slices, host-shuffle effects |
| **Janus / Pendulum (`PISA`)** | Logically bijective forward & backward execution | Reversible state updated via `+=`, `-=`, `^=`, `<=>` | Paired branch/loop assertions (`if`/`fi`, `from`/`until`), `call`/`uncall` | Destructive `x = y`, unchecked joins, and DCE force history taping | Linear-bijective types with verified zero-garbage ancilla uncomputation |

---

### 2. The Mill CPU Architecture: Belt Temporal SSA, `None > NaR > Value`, Phased Loops, Hardware Frame/Cache Primitives, and `genAsm -> conAsm`

#### 2.1 Temporal Belt Addressing and De Bruijn SSA Isomorphism

Basis: normative (U.S. Patents `9,513,921`, `9,747,238`, `9,965,274`) + documentation (`millcomputing.com`) + execution (`support/verify_belt_nar_and_bsp_semantics.py`)

Under `US 9,513,921` (granted Dec 20, 2016), Mill replaces general-purpose registers with a fixed-length logical FIFO queue called the **Belt** (member-specific length $N$, typically 8–32 entries):

- **Temporal Transition Rule**: If cycle $t$ has belt state $B_t = (v_0, \dots, v_{N-1})$ and functional units drop an ordered tuple of $k$ results $(r_0, \dots, r_{k-1})$ determined statically by slot order and latency, the next state is $B_{t+1} = (r_0, \dots, r_{k-1}, v_0, \dots, v_{N-k-1})$, discarding $(v_{N-k}, \dots, v_{N-1})$. Instructions encode only **source** temporal offsets (`add(b3, b4)`), never destinations.
- **De Bruijn SSA Correspondence**: Each belt index $b_i$ is literally a **bounded de Bruijn index** counting drops since production. Because entries are immutable once dropped, `WAW` and `WAR` hazards cannot be encoded, abolishing physical rename files and free lists.
- **Mixed-Latency Crossbar & Tag Bypass (`US 9,747,238`, granted Aug 29, 2017; `US 9,965,274`)**: Note that `US 9,747,238` specifically defines the **split crossbar circuit and slot-based functional-unit organization** (distinct from `US 9,747,216`, which covers the scratchpad and spiller). Single-cycle results route over a lower crossbar; multi-cycle units (2–4 cycles) shift through daisy-chained latency-specific slot output registers (`lat-1`..`lat-4`) into an upper crossbar, while `US 9,965,274` routes operands via dynamically generated result tags and tag-match muxes.
- **LLVM Friction**: LLVM's `SelectionDAG`/`MachineIR` register allocator assumes mutable spatial register classes, inserts destructive two-address copies, solves NP-complete coloring, and leaves unconstrained live ranges that exceed member belt length $N$.

#### 2.2 Belt Conformation (`conform`/`rescue`), Zero-Cycle `pick`, and Private `Base`/`Fence` Scratchpads

Basis: normative (U.S. Patents `9,747,216`, `11,226,821`) + documentation + execution (`support/verify_belt_nar_and_bsp_semantics.py`) + derived

1. **Block-Argument `conform` vs. Briggs/Sreedhar $\phi$-Copy Cycles**: On mutable registers, lowering SSA $\phi$-nodes into parallel `COPY` operations encounters the Briggs (1998) / Sreedhar (1999) lost-copy and swap-cycle problem (`r1 <-> r2` needs a temporary register; see `verified-regalloc2-spill-and-parallel-move-certificate-checker`). On a belt, slot $k$ cannot be overwritten in place. An IR with **explicit block arguments** (MLIR / Cranelift) assigns each join block $J(p_0, \dots, p_{m-1})$ an exact entry belt prefix $(b_0 = p_0, \dots, b_{m-1} = p_{m-1})$. Each predecessor edge emits an atomic **belt conformation / `rescue` drop** reading all $m$ sources simultaneously from its belt or scratchpad (`FILL`) *before* dropping them onto the front. Consequently, arbitrary cyclic permutations—including 2-swaps `(x, y) <-> (y, x)` and 3-cycles `(a, b, c) -> (b, c, a)`—require **zero temporary registers**. Our probe (`compile_conform_edge`) verifies zero-instruction identity edges, 3-cycle permutation edges, and scratchpad-fill edges converging onto identical belt prefixes.
2. **Zero-Cycle `pick(cond, t, f)` (`US 11,226,821`)**: Evaluates conditional selection at cycle boundaries over scalar or vector operands without branching, discarding any `NaR` in the untaken arm.
3. **Private Byte-Addressable Scratchpad (`US 9,747,216`, granted Aug 29, 2017)**: Long-lived operands copy off the belt via `SPILL` and return via `FILL` against per-frame circular windows bounded by hardware `Base`/`Fence` registers (`SCRATCHF` allocates, `SCRATCHD` deallocates), isolated from address-taken virtual memory.

#### 2.3 Inline Speculative Metadata (`None > NaR(provenance) > Value`) vs. LLVM `poison`/`undef`/`freeze`

Basis: normative (U.S. Patent `11,226,821`, granted Jan 11, 2022; Lee et al. PLDI 2017) + execution (`support/verify_belt_nar_and_bsp_semantics.py`) + derived

Every Mill belt operand pairs its payload with processor-internal metadata: scalar/vector tag, element width (`1`/`2`/`4`/`8` bytes), per-operand IEEE-754 exception flags, **`NaR` (Not-a-Result)**, and **`None`**, obeying strict precedence **`None > NaR(fault_kind, origin_pc) > Value(bits, width, fp_flags)`**:

| Semantic Property | Mill Hardware Metadata (`US 11,226,821`) | LLVM `poison`/`undef`/`freeze` (Lee et al., PLDI 2017) | Compiler & Verification Consequence |
| :--- | :--- | :--- | :--- |
| **Carrier** | Hardware metadata bits in belt, bypass, and scratchpad | Software-only UB fiction; no hardware tag on x86/ARM/RV64 | Mill executes aggressive hoisting directly in silicon; LLVM must guard trapping ops |
| **Speculative Faults** | Faulting speculable op yields `NaR(kind, pc)` without trapping | Immediate `SIGSEGV`/`SIGFPE` or UB if executed | Hoisted loads/divides discard untaken `NaR` safely via `pick` |
| **Fault Provenance** | Embeds error kind + originating PC (`splitNAR`/`joinNAR`, debug mode) | Zero provenance; UB manifests non-locally | Non-speculable consumers (`store`/`branch`/`call`) trap with exact origin PC |
| **Masked Absence (`None`)** | Strictly beats `NaR` (`None ⊕ NaR = None`); non-speculable ops silently **no-op** | No counterpart (`undef` picks arbitrary bits; branching on `poison` is UB) | Powers prologue-free `RETIRE` loops and OOB-safe `smear` vectorization |
| **IEEE-754 Flags** | Per-operand flags OR'd along speculable chains; committed only at commit | Global sticky `FCSR`/`MXCSR` inhibits FP hoisting (`strictfp`) | Removes false `WAW` dependencies on global FP status registers |
| **Width Polymorphism** | Single opcode dispatches on width metadata; mismatch faults/`NaR` | Typed per-width opcodes (`add i8`/`i32`/`i64`) | Compact ISA; hardware enforces width compatibility |
| **Memory Boundary** | **Processor-internal**: `store` strips metadata; `load` reconstructs fresh tags | Byte-level `poison` memory in Vellvm/Alive2 (`mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames`) | Verification requires a **lossy-projection codec** at store/load seams (storing `NaR` traps; storing `None` no-ops; FP flags must commit explicitly) |

Concrete temporal trace of aggressive speculative hoisting verified in [verify_belt_nar_and_bsp_semantics.py](support/verify_belt_nar_and_bsp_semantics.py) (compiling `out = (idx < 3 && denom != 0) ? mem[idx] / denom : fallback`):

```text
Cycle 0: drop [idx, denom, fallback]          -> Belt: b0=idx, b1=denom, b2=fallback
Cycle 1: hoist load(mem[b0]) @pc10;           -> OOB idx=99 yields NaR(OOB_LOAD, pc=10)
         eval cond = (0 <= b0 < 3 && b1 != 0) -> cond = Val(0)
         drop [loaded, cond]                  -> Belt: b0=loaded, b1=cond, b2=idx, b3=denom, b4=fallback
Cycle 2: hoist div(b0, b3) @pc20              -> propagates NaR(OOB_LOAD, pc=10) [or NaR(DIV_ZERO, pc=20) if denom=0]
         drop [div_res]                       -> Belt: b0=div_res, b1=loaded, b2=cond, b3=idx, b4=denom, b5=fallback
Boundary: sel = pick(b2, b0, b5)              -> cond=0 selects b5=fallback, discarding NaR & untaken INEXACT flag
Commit:  store(&out, sel) @pc30               -> commits fallback (0 traps); buggy cond=1 raises MillTrap(origin_pc=10|20)
```

Exhaustive probe checks confirm `None` dominates `NaR` even across store operands (`store(None, NaR)` and `store(NaR, None)` both silently no-op), untaken `INEXACT` flags never leak, and unguarded `NaR` traps preserve exact origin PCs (`10` and `20`).

#### 2.4 Phased Software-Pipelined Loops (`RETIRE`, Rotating Scratchpad, and Vector `smear`/`smearx`)

Basis: normative (U.S. Patents `9,817,669`, granted Nov 14, 2017; `11,226,821`) + execution (`support/verify_belt_nar_and_bsp_semantics.py`) + derived

To abolish prologue/epilogue code bloat in modulo-scheduled loops, Mill combines four primitives:

- **`RETIRE(k)` & `RETIRE WITH WIDTH LIST`**: Placed at the loop head, `RETIRE(k)` declares $k$ retiring operands per cycle. During warmup iterations before earlier stages finish, hardware pads missing drops with **`None`** (faulting if $>k$ arrive; no-op in steady state). `None` propagates through speculable ALU stages and turns premature non-speculable stores into silent no-ops, letting execution enter the steady-state kernel directly on cycle 0.
- **`INNER`, `LEAVE`, and Rotating Scratchpads**: `INNER` creates a fresh nested loop belt without disturbing the caller frame; `LEAVE` discards in-flight speculative loop ops and restores the outer belt with exit values (zero epilogue). Loop-carried values live in scratchpad windows rotated per iteration via `SCRATCHF`/`SCRATCHD`/`ROTATE` so logical offsets remain static.
- **Vector `smear` (inclusive), `smearx` (exclusive), `Remaining`, and `Satisfied` (`US 11,226,821`)**: On irregular early-exit `while`-loops (`strlen`/`strcpy`), speculative vector loads reading past the null terminator and past valid page boundaries yield `NaR("OOB_LOAD")` in trailing lanes. Inclusive `smear` turns `[0, 1, 0, 1]` into `[0, 1, 1, 1]`; exclusive `smearx` produces `[0, 0, 1, 1]`. Applying `pick(smearx_mask, None, loaded)` overwrites trailing `NaR` lanes with `None` (`None > NaR`), so the full-width vector store writes only the valid prefix and silently suppresses trailing OOB lanes with zero scalar tail loops.

Our probe verifies a 3-stage prologue/epilogue-free `RETIRE` loop bit-for-bit against sequential reference outputs across $N \in \{0, 1, 2, 3, 7, 16\}$ and verifies an 8-lane OOB-spanning `strcpy("hello\0")` committing exactly 6 bytes with zero traps. Formally, phased modulo-loop combinators replace 3–4 duplicated peel/body/epilogue CFGs with one inductive invariant over `None`-padded pipeline stages.

#### 2.5 Hardware Spiller, Implicit Zero Map (`IZM`), Backless Cache Lines, and Per-Byte Valid Caches

Basis: normative (U.S. Patents `9,513,904`, `9,652,230`, `9,747,216`, `10,802,987`) + derived

1. **Asynchronous Spiller (`US 9,513,921`; `US 9,747,216`)**: Saves/restores caller belts and scratchpads to private spillets in the background across `CALL`/`RETURN` and interrupts, abolishing caller/callee-save register ABI conventions.
2. **Implicit Zero Map (`IZM`, `US 9,652,230`, granted May 16, 2017)**: Tracks 1 bit per cache line for the top stack frame (`SP` + frame-size registers):
   - *Entry*: Sets frame IZM bits to `implicit-zero` (excess lines explicitly zeroed once).
   - *Load*: Set IZM bit returns zeros immediately as a hit without touching caches or DRAM.
   - *Store*: Merges written bytes with zeros into cache and clears the IZM bit (zero RFO traffic).
   - *Exit*: Valid (cleared-bit) lines are invalidated **without write-back**; untouched (set-bit) lines reset their bit—eliminating `memset(0)` prologues and cross-frame stack leakage simultaneously.
3. **Backless Cache Lines (`US 10,802,987`)**: Virtual cache lines lacking physical PTEs (or physical entries marked `pending`) satisfy reads with zeros purely in cache and allocate backing DRAM only upon write-back eviction.
4. **Per-Byte Valid Caches (`US 9,513,904`)**: One valid bit per byte per cache line (e.g., 64 bits/line) plus fully associative victim buffers make partial stores always hit without read-before-write fills, while byte-masked invalidations allow multiple cores to modify disjoint bytes of the same cache line without false sharing.

#### 2.6 Split-Stream Wide Encoding, EBB Exit Prediction, Deferred Loads, Pointer Events, and `genAsm -> conAsm` Friction

Basis: normative (U.S. Patents `9,513,920`, `9,524,163`, `9,690,581`, `9,785,441`, `9,875,106`, `9,959,119`) + documentation (`millcomputing.com/docs/compiler/`) + derived

- **Split-Stream Double-Ended Decode & Elided NOPs (`US 9,513,920`, `9,785,441`, `9,959,119`)**: Extended Basic Blocks split into opposing forward (`flow`/memory) and reverse (`exu`/compute) half-streams diverging from one entry address, decoded simultaneously from head and tail (`Svelte`/`Skinny` formats) at 30+ ops/cycle; a 0–7 bit **alignment hole** (`US 9,785,441`) encodes implicit NOP stall counts to preserve timed synchronization with zero NOP code bloat.
- **EBB Exit Prediction (`US 9,875,106`)**: Chains Exit Table/Exit Cache entries capturing target address, cache-line count, instruction count, loop count, and alternate recovery key (supporting bulk-loaded cold-start predictors and ~5-cycle recovery without full flushes).
- **Deferred Loads (`US 9,690,581`)**: `DLOAD` decouples load issue from belt retirement via static latency countdowns or `pickup` handles managed by Retire Stations that buffer early hits, stall on late misses, and snoop intervening stores for collision reissue.
- **Hardware Pointer Events & Granularity Bounds (`US 9,524,163`)**: Embedded pointer event bits index Read/Write/Update Interest Mask Registers for zero-polling GC/security traps, while a 6-bit granularity field enforces aligned power-of-two chunk bounds in parallel inside the Address Derivation Unit (plus a valid bit for safe one-past-the-end pointers).
- **Four C-isms Fighting `LLVM IR -> genAsm -> conAsm` Specialization**: Software ships as architecture-neutral dataflow SSA (`genAsm`) specialized at install time into concrete member binaries (`conAsm`, `millcomputing.com/docs/compiler/`). Legacy C fights this model via: (1) **`&local`** forcing non-escaping values out of belt/scratchpad into main memory; (2) **`setjmp`/`longjmp`** violating structured frame nesting over asynchronous spillers, `INNER`/`LEAVE`, and Retire Stations; (3) **`uintptr_t` round-tripping** destroying pointer event bits and 6-bit granularity bounds; and (4) **untyped C varargs** breaking fixed belt-argument signatures. Strict-provenance languages with explicit escaping locals and structured effects lower cleanly to `genAsm`, enabling lightweight translation validation of install-time `genAsm -> conAsm` specialization.

---

### 3. EDGE Block-Atomic Dataflow (`TRIPS`) and Coarse-Grained Reconfigurable Arrays (`Plasticine`, `Spatial`, `SambaNova RDU`)

#### 3.1 EDGE / TRIPS Atomic Hyperblocks and Mapping from RVSDG

Basis: normative (Burger et al., *IEEE Computer* 2004; Smith et al., CGO 2006; Reissmann et al., *ACM TECS* 2020) + derived

**Explicit Data Graph Execution (EDGE)**, realized in UT Austin's **TRIPS** processor (Burger, Keckler, McKinley et al., *IEEE Computer* 37(7):44–55, July 2004, `DOI:10.1109/MC.2004.65`), replaces centralized register broadcasting with compiler-formed atomic hyperblocks executing via dynamic intra-block dataflow over a 2D ALU grid:

- **Direct Target Encoding & Hard Block Limits (Smith et al., CGO 2006)**: Instructions encode explicit consumer **target instruction IDs** rather than register names; values travel point-to-point between ALUs. Each atomic TRIPS block must satisfy four strict hardware bounds: (1) **$\le 128$ instructions**, (2) **$\le 32$ memory operations** tagged with explicit **Load-Store Identifiers (`LSID`s)** for Load-Store Queue (`LSQ`) ordering, (3) **$\le 32$ register-bank reads** at entry and **$\le 32$ register-bank writes** at exit, and (4) constant-output predicated paths so block commit/squash is atomic.
- **LLVM Friction & RVSDG Fit (Reissmann et al., *ACM TECS* 2020, `DOI:10.1145/3391902`)**: Standard basic-block CFGs starve 128-op grids (demanding heavy if-conversion and tail duplication), linear register allocators ignore 2D wire-hop placement, and C pointer aliasing forces conservative `LSID` serialization. By contrast, **RVSDG** organizes programs into hierarchical single-entry/single-exit demand-dependence regions (`γ`-conditionals, `θ`-loops) with explicit memory-state edges: intra-region value edges map directly onto TRIPS target-instruction routing without $\phi$-nodes, partitioned state edges tighten `LSID` ordering without fragile alias recovery, and refinement verification reduces cleanly to **whole-block atomic state transitions**.

#### 3.2 Coarse-Grained Reconfigurable Arrays: `Plasticine`, `Spatial`, and `SambaNova SN40L RDU`

Basis: documentation (Prabhakar et al., ISCA 2017; Koeplinger et al., PLDI 2018; Prabhakar et al., MICRO 2024) + derived

CGRAs statically configure a 2D word-level spatial fabric so nested parallel patterns execute as pipelined streaming dataflow graphs with near-zero instruction fetch:

- **Plasticine (Prabhakar et al., ISCA 2017, `DOI:10.1145/3079856.3080256`)**: Checkerboard of **Pattern Compute Units (PCUs)**—multi-stage **16-lane SIMD** datapaths with scalar/vector/control I/O, small **input FIFOs** decoupling producer/consumer latency mismatches, and reconfigurable counter chains + up-down control state machines—and **Pattern Memory Units (PMUs)**—**256 KB scratchpads organized as 16 configurable 16 KB banks** with programmable address generators supporting reconfigurable banking, double/$N$-buffering, and local FIFOs.
- **Spatial (Koeplinger et al., PLDI 2018, `DOI:10.1145/3192366.3192379`)**: Hardware-centric DSL exposing explicit `SRAM`, `FIFO`, `RegFile`, `LineBuffer`, and nested parallel patterns (`Foreach`, `Reduce`, `Fold`, `MemReduce`, `FSM`), automating tiling, banking, $N$-buffering, retiming, and ML-guided tuning onto Plasticine CGRAs and FPGAs.
- **SambaNova SN40L RDU (Prabhakar et al., MICRO 2024, `DOI:10.1109/MICRO61859.2024.00100`)**: Commercializes Plasticine's PCU/PMU checkerboard inside Reconfigurable Dataflow Units backed by a three-tier memory hierarchy (on-chip PMU SRAM + on-package HBM + off-package DDR) for trillion-parameter Composition of Experts workloads.
- **Static Verification Hazards**: Raw C pointer loops obscure affine access strides needed for bank allocation. Clean-slate CGRA IRs must check two physical constraints statically: (1) **PMU bank-conflict freedom** (injective mapping or replication of 16 concurrent PCU lanes across 16 PMU banks), and (2) **reconvergent FIFO deadlock freedom** (when one producer forks two uneven-latency paths reconverging at a downstream PCU with finite input FIFOs, under-sized short-path FIFOs backpressure-lock the producer unless capacities satisfy SDF balance and latency-skew bounds).

---

### 4. Explicit Non-Coherent Tile, Wafer-Scale, BSP, and Deterministic Streaming Engines

#### 4.1 Cerebras Wafer-Scale Engine (`WSE-2`/`WSE-3`) and `CSL` Wavelet Dataflow

Basis: documentation (Lie, *IEEE Micro* 2023, `DOI:10.1109/MM.2023.3256384`; Cerebras SDK/CSL docs) + derived

Across a monolithic 300 mm wafer, wire capacitance and speed-of-light latency forbid shared coherent DRAM. Cerebras therefore exposes a pure distributed-memory 2D mesh:

| Parameter | Cerebras WSE-2 (CS-2) | Cerebras WSE-3 (CS-3) | Compiler / Verification Implication |
| :--- | :--- | :--- | :--- |
| **Node / Transistors** | 7 nm / 2.6 trillion | 5 nm / 4 trillion | Monolithic wafer die; zero inter-chip reticle breaks |
| **Compute Cores (PEs)** | 850,000 | 900,000 | No global OS scheduler; pure spatial mapping |
| **Aggregate / Per-PE SRAM** | 40 GB (20 PB/s) / **48 KB/PE** | 44 GB (21 PB/s) / **48 KB/PE** | Zero shared DRAM or coherence; code+stack+tensors $\le 48$ KB |
| **Fabric Mesh** | 5-port router, **24 static colors**, 32-bit **wavelets** | 5-port router, **24 static colors**, 32-bit **wavelets** | Non-blocking virtual channels; static multicast/broadcast |

In Zig-derived **`CSL`**, compile-time routing tables bind each PE's 5-port router across **24 hardware colors** (dedicated buffered virtual channels). Single-cycle 32-bit **wavelets** arriving on a bound color automatically trigger **`data_task`** handlers, while **`fabin_dsd` / `fabout_dsd`** Data Structure Descriptors drive autonomous microthreads streaming between 48 KB SRAM and fabric links. Because C/MPI hides channel IDs inside opaque library calls, untyped color assignments invite routing dependency cycles (wafer deadlock), unmatched wavelet counts (hung `data_task`s), and 48 KB SRAM overflows. Clean-slate wafer-scale languages require **spatial multiparty session / choreographic types** statically verifying channel-dependency acyclicity across all 24 colors, linear wavelet conservation, and static $\le 48\text{ KiB}$ per-PE memory footprints.

#### 4.2 Graphcore `IPU` (`GC2`/`GC200`) and `Poplar` Hardware BSP

Basis: documentation (Jia et al., `arXiv:1912.03413v1`) + execution (`support/verify_belt_nar_and_bsp_semantics.py`) + derived

Graphcore's Colossus IPU embeds Valiant's Bulk Synchronous Parallel (BSP) model directly in silicon: **MK1 `GC2`** provides **1,216 tiles** and **304 MB** In-Processor SRAM (6 hardware worker threads + 1 supervisor context/tile, characterized in Jia et al. `arXiv:1912.03413v1`); **MK2 `GC200`** scales to **1,472 tiles** and **900 MB** SRAM. Every superstep strictly alternates: (1) **`Compute`** (strictly private local SRAM), (2) **Hardware Global `Sync`**, and (3) **`Compiled Exchange`** (Poplar-scheduled, contention-free all-to-all packet exchange).

Formalizing BSP via a **phase-effect type system** captures this contract cleanly:

```text
  Γ; Compute(t) ⊢ r : Ref<t, A>            (remote Ref<t', A> with t' ≠ t is ill-typed)
  ----------------------------------- [T-LocalMem]
  Γ; Compute(t) ⊢ load/store r : Eff<Compute(t)>

  ∀i. src_i : Ref<s_i, A_i>, dst_i : Ref<d_i, A_i>
  ∀i ≠ j. (d_i, addr(dst_i)) ≠ (d_j, addr(dst_j))   (static destination disjointness)
  ------------------------------------------------------------------------------------- [T-Exchange]
  Γ; Exchange ⊢ xfer_set{(src_i -> dst_i)} : Eff<Exchange>
```

Under `[T-LocalMem]` and `[T-Exchange]`, intra-phase tile execution order and exchange packet arrival order are unobservable: verifying a 1,472-tile parallel program reduces to **sequential per-tile functional proofs** plus a **pure data-permutation proof**—completely bypassing weak-memory axioms and lock invariants. Our probe verifies bit-for-bit identical SRAM across **25 randomized intra-phase schedules** on a 4-tile, 3-superstep ring stencil, while statically rejecting both an injected remote read in `ComputePhase` and a dual-sender write collision in `ExchangePhase`. On severely imbalanced sparse graphs where global barriers idle fast tiles, **nested/sub-group BSP** over disjoint tile subsets is needed to recover efficiency without sacrificing static verifiability.

#### 4.3 Tenstorrent `Tensix` (`Wormhole`/`Blackhole`) and `TT-Metalium` Explicit 5-Core NoC + CB Architecture

Basis: source (`tenstorrent/tt-metal@11551f901bb3e2ad451a0fe5036312c4687d40c3`) + execution (`support/verify_belt_nar_and_bsp_semantics.py`) + derived

Direct source inspection of `tenstorrent/tt-metal@11551f901bb3e2ad451a0fe5036312c4687d40c3` pins the exact per-tile memory geometry and synchronization contracts across generations:

| Resource | Wormhole | Blackhole | Pinned Source (`tenstorrent/tt-metal@11551f90...`) |
| :--- | :--- | :--- | :--- |
| **Tile L1 SRAM (`MEM_L1_SIZE`)** | `1464 * 1024` (1,464 KiB) | `1536 * 1024` (1,536 KiB / 1.5 MiB) | `wormhole/dev_mem_map.h:33`; `blackhole/dev_mem_map.h:33` |
| **Per-Core Local SRAM (`0xFFB00000`)** | `BRISC`/`NCRISC`: 4 KiB; `TRISC0..2`: 2 KiB | `BRISC`/`NCRISC`: 8 KiB; `TRISC0..2`: 4 KiB | `wormhole/dev_mem_map.h:41-44`; `blackhole/dev_mem_map.h:43-45` |
| **NCRISC IRAM Cap** | `NCRISC_HAS_IRAM 1`, 16 KiB at `0xFFC00000` | No 16 KiB IRAM cap | `wormhole/dev_mem_map.h:52-54,65-75` |
| **Circular Buffers (`NUM_CIRCULAR_BUFFERS`)** | **32** (`ARCH_WORMHOLE`, 2 KiB TRISC cap) | **64** (host header reserves max 64) | `hw/inc/api/circular_buffer_constants.h:22-27` |

- **5-Core Intra-Tile Choreography**: Each tile packs five RV32IM cores: `BRISC` and `NCRISC` drive dual 2D-mesh NoCs (`noc = 0 | 1`) via `dataflow_api.h`, while `TRISC0` (`UNPACK`), `TRISC1` (`MATH`), and `TRISC2` (`PACK`) execute three macro-specialized compilations of one compute C++ source (`cb_api.h`). `cb_wait_front`/`cb_pop_front` run exclusively on `UNPACK` (`cb_api.h:44,76`); `cb_reserve_back`/`cb_push_back` run exclusively on `PACK` (`cb_api.h:92-98,130-136`); cross-TRISC queries (`get_tile_address`, `cb_api.h:172-186`) explicitly synchronize via `mailbox_write`/`mailbox_read`. Next-gen `#ifdef ARCH_QUASAR` stubs (`cb_api.h:8-9,142-147`) transition toward Dataflow Buffers (`LocalDFBInterface`).
- **Source-Verified Wrap-Contiguity Implementation & Failure Postmortems** (`tt_metal/hw/inc/api/dataflow/dataflow_api.h:208-224`, verbatim structure):

```cpp
FORCE_INLINE void cb_push_back(const int32_t operand, const int32_t num_pages) {
    uint32_t num_words = num_pages * get_local_cb_interface(operand).fifo_page_size;
    volatile tt_reg_ptr uint32_t* pages_received_ptr = get_cb_tiles_received_ptr(operand);
    pages_received_ptr[0] += num_pages;
    get_local_cb_interface(operand).fifo_wr_ptr += num_words;
    // Producer always writes into contiguous memory; wrap is legal ONLY at exact fifo_limit:
    ASSERT(get_local_cb_interface(operand).fifo_wr_ptr <= get_local_cb_interface(operand).fifo_limit);
    if (get_local_cb_interface(operand).fifo_wr_ptr == get_local_cb_interface(operand).fifo_limit) {
        get_local_cb_interface(operand).fifo_wr_ptr -= get_local_cb_interface(operand).fifo_size;
    }
}
```

Four concrete failure classes follow directly from these headers (all modeled and caught by our BFS verifier in [verify_belt_nar_and_bsp_semantics.py](support/verify_belt_nar_and_bsp_semantics.py)):
1. **Wrap-Boundary Overrun (`dataflow_api.h:217-223, 269-275`; `cb_api.h:29-34`)**: `cb_push_back` and `cb_pop_front` wrap *only* on exact equality `ptr == fifo_limit`. On a 12-tile CB, pushing `5` then `7` (`= 12`) wraps cleanly, whereas pushing `7` then `7` (`= 14`) violates `ASSERT(ptr <= fifo_limit)`—or silently corrupts adjacent L1 SRAM when asserts are disabled.
2. **Non-Cumulative `cb_wait_front` Race (`dataflow_api.h:458-461, 479-493`; `cb_api.h:24-27`)**: `cb_wait_front(cbid, n)` polls `((uint16_t)reg_read(pages_received_ptr)) - pages_acked >= n` without advancing `pages_acked`. Calling `cb_wait_front(8)` four times before `cb_pop_front(32)` returns immediately on the first 8 tiles (racing on tiles 8..31); callers must pass cumulative totals `8, 16, 24, 32`.
3. **SPSC Pointer-Ownership Race (`cb_api.h:62-66, 116-120`)**: `fifo_wr_ptr`/`fifo_rd_ptr` update unsynchronized; two cores pushing or two cores popping the same `cb_id` (e.g., compute + writer) corrupt CB pointers nondeterministically.
4. **NoC Barriers, Cache Invalidation, and Multicast Self-Exclusion (`dataflow_api.h:420, 918-957, 1921-2125`)**: Spin-waits explicitly invoke `invalidate_l1_cache()` to observe incoherent NoC/core writes; `noc_async_write_multicast` targets a rectangular coordinate range `(x_start, y_start, x_end, y_end)` at uniform L1 offset, **never writes to self** even when self lies in the rectangle, and requires `num_dests` to exclude self (e.g., `63` for an 8x8 grid containing self, $\ge 1$; loopback requires `noc_async_write_multicast_loopback_src`).

Our BFS verifier exhaustively explores all **101 interleaved states** of a 3-core double-buffered pipeline (`NCRISC -> CB0 -> TRISC -> CB1 -> BRISC`, `cap=4`, `batch=2`) proving deadlock/violation freedom, confirms legal `5 + 7 = 12` wrap, and catches `7 + 7` `WrapBoundaryViolation`, cross-CB circular `DEADLOCK`, dual-consumer `SPSC consumer violation`, and premature return on non-cumulative `cb_wait_front(8)`. Compiling one **choreographic tile source** down to all 5 cores with linear wrap-exact SPSC ring-buffer tokens and typed NoC rectangles eliminates all four failure classes statically.

#### 4.4 Groq `TSP` / `LPU`: 100% Compiler-Scheduled Cycle-Deterministic VLIW Streaming

Basis: documentation (Abts et al., ISCA 2020 `DOI:10.1109/ISCA45697.2020.00023`; Abts et al., ISCA 2022 `DOI:10.1145/3470496.3527405`) + derived

Groq's **Tensor Streaming Processor (TSP / LPU)** strips out *every* source of microarchitectural nondeterminism: zero caches, zero branch predictors, zero OoO schedulers, and zero dynamic arbiters. Functional slices sit spatially along a 2D streaming superlane conveyor: **`MEM`** (**220 MB** distributed on-chip SRAM on ISCA 2020 TSP), **`MXM`** (matrix multiply), **`VXM`** (vector ALU/activations), **`SXM`** (switch/permute/transpose), and **`ICU`** (instruction control). Vectors span **320 lanes** (20 superlanes $\times$ 16 lanes; 320 bytes at 8-bit width), moving across slices on exact compiler-scheduled clock cycles. Multi-chip Dragonfly systems (ISCA 2022) connect over chip-to-chip (`C2C`) **plesiochronous links** aligned via explicit **`Deskew`** operations to maintain deterministic global timing across racks.

Because LLVM IR has zero notion of clock time `t : Nat` or spatial column arrival cycles, targeting deterministic streaming VLIW demands a **timed synchronous IR** (`Stream<T, col, [t_0, t_1)>`, connecting with synchronous clocks in `anneal-cps-robotics-aerospace-eda-and-quantum-survey`), turning stream-collision freedom, spatial operand arrival alignment, and exact WCET into typechecking theorems.

---

### 5. Processing-in-Memory (`UPMEM`, `HBM-PIM`) and Reversible Bijective Computing (`Janus`, `Pendulum`/`PISA`)

#### 5.1 Processing-in-Memory (`UPMEM` DPU and Samsung `HBM-PIM`)

Basis: documentation (Gómez-Luna et al., *IEEE Access* 2022 / `arXiv:2105.03814`; Lee et al., ISCA 2021 `DOI:10.1109/ISCA52012.2021.00013`) + derived

- **UPMEM DPU (`DOI:10.1109/ACCESS.2022.3174101`)**: Embeds 32-bit in-order RISC DPUs (14-stage pipeline, up to **24 hardware tasklets**) directly inside DRAM chips. Each DPU owns strictly private **64 MB MRAM**, **64 KB WRAM** scratchpad, and **24 KB IRAM**, with **no direct inter-DPU interconnect** (cross-bank shuffles route through the host CPU). Because ALU ops execute only on WRAM, kernels issue explicit `mram_read`/`mram_write` DMA calls constrained to **strict 8-byte address and length alignment** and a **2,048-byte maximum single transfer size**.
- **Samsung HBM-PIM (`DOI:10.1109/ISCA52012.2021.00013`)**: Places SIMD Programmable Computing Units (`PCUs`) inside commercial HBM2 banks executing bank-local MAC commands issued over the standard JEDEC memory interface.
- **Clean-Slate Type Requirements**: Disjoint host-C / DPU-C binaries with raw byte-offset DMA invite silent cross-bank pointer bugs and alignment faults. Clean-slate PIM IRs need **bank-partitioned array types** (`DistributedArray<BankId, T>`), **alignment- and bound-refined DMA slices** (`AlignedSlice<8, MaxLen=2048>`), and **explicit host-shuffle effect types**.

#### 5.2 Reversible Computing (`Janus` and `Pendulum`/`PISA`)

Basis: normative (Landauer 1961 `DOI:10.1147/rd.53.0183`; Yokoyama & Glück, PEPM 2007 `DOI:10.1145/1244381.1244404`; Yokoyama, Axelsen & Glück, CF 2008 `DOI:10.1145/1366230.1366239`) + execution (`support/verify_belt_nar_and_bsp_semantics.py`) + derived

By **Landauer's Principle** (1961), erasing 1 bit dissipates at least $k_B T \ln 2$ of heat. Adiabatic CMOS hardware such as MIT's **Pendulum** microprocessor (**PISA** reversible ISA; Vieri 1999; Frank 1999) recovers switching charge iff every transition is **logically bijective** (forward- and backward-deterministic). Mainstream C/LLVM constructs (`x = y`, unchecked CFG joins, DCE) erase history continuously, forcing space-exploding Bennett history-taping unless clean uncomputation is synthesized.

Note the primary-source split in the Janus literature: **PEPM 2007** (`10.1145/1244381.1244404`, *"A reversible programming language and its invertible self-interpreter"*) formalizes Janus's clean reversible semantics, local inverter, and garbage-free self-interpreter; **CF 2008** (`10.1145/1366230.1366239`, *"Principles of a Reversible Programming Language"*) codifies the design principles and reversible algorithms (e.g., reversible FFT). Janus enforces bijectivity via non-self-referential invertible updates (`x += e`, `x -= e`, `x ^= e`, `x <=> y`) and paired entry/exit assertions that invert purely syntactically:

```text
Forward Statement                           Local Syntactic Inverse (`uncall`)
-----------------------------------------   -----------------------------------------
x += e   (x not free in e)                  x -= e
x <=> y                                     x <=> y
if e1 then s1 else s2 fi e2                 if e2 then inv(s1) else inv(s2) fi e1
from e1 do s1 loop s2 until e2              from e2 do inv(s1) loop inv(s2) until e1
```

In [verify_belt_nar_and_bsp_semantics.py](support/verify_belt_nar_and_bsp_semantics.py), `janus_fib_forward` and its local syntactic inverse `janus_fib_inverse` verify `inv(fwd(n, 1, 1)) == (n, 1, 1)` for all $n \in [0, 15]$ with zero history tape. Because quantum unitary circuits ($U^\dagger U = I$, `anneal-cps-robotics-aerospace-eda-and-quantum-survey`) impose the exact same zero-garbage ancilla constraint, a **linear-bijective IR with verified ancilla-zeroing postconditions** unifies classical adiabatic/PISA compilation with quantum oracle uncomputation.

---

### 6. Clean-Slate Compiler IR & Verification Synthesis: Six Orthogonal Primitives

Basis: derived (from Sections 1–5 and verified probe executions)

A single clean-slate verified compiler IR targeting both conventional CPUs and all nine non-Von-Neumann families cleanly requires six composable primitives:

1. **Block-Argument / RVSDG Structured Regions + Bounded Temporal Lifetimes**: Eliminates $\phi$-copy cycles; lowers uniformly to Mill temporal belt `conform`, EDGE/TRIPS 128-op atomic hyperblocks (explicit state edges -> minimal `LSID`s), and standard register allocators.
2. **First-Class Partial/Speculative Value Lattice + Lossy Memory Codecs**: Elevates `None > NaR(provenance) > Value(width, fp_flags)` alongside LLVM `poison`/`freeze` (`mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames`) with explicit stripping contracts at untagged byte stores.
3. **Phased Modulo-Loop & Vector Mask Combinators**: Encodes `RETIRE` warmup/drain and `smear`/`smearx` masks inside one inductive steady-state loop invariant.
4. **Memory-Space, Banking, and Alignment-Qualified Region Pointers**: Qualifies pointers by storage tier (`Belt`/`Scratchpad`/`PMU`/`PE_SRAM`/`L1`/`MRAM`/`WRAM`), bank stride, and DMA alignment/size (`Aligned8`, $\le 2048$ B).
5. **Phase-Effect, Choreographic, and Linear Ring-Buffer Protocol Types**: Statically enforces Graphcore BSP phase isolation, Cerebras 24-color routing acyclicity, and Tenstorrent SPSC wrap-exact CB tokens across multi-core projections.
6. **Cycle-Indexed Timeline & Linear-Bijective Sub-Calculi**: Verifies Groq spatial-temporal arrival alignment/WCET and Janus/PISA/quantum zero-garbage uncomputation.

## Boundaries

- **not examined**:
  - Empirical silicon benchmarks or cycle-accurate RTL simulations of the Mill CPU (no commercial Mill silicon had shipped as of `2026-11-19`; findings derive from granted USPTO patents, Mill Computing documentation, and our executable model).
  - Full RTL/Verilog netlists of TRIPS, Plasticine, SambaNova SN40L, Cerebras WSE-2/WSE-3, Graphcore GC2/GC200, Groq TSP, or Tenstorrent Wormhole/Blackhole.
  - Hardware capability security models (CHERI/Morello/CHERIoT) and Mill SASOS `Turfs`/`Portals`/`PLBs`/`WKRs` (`US 9,747,218`; `US 10,678,700`), which belong to a dedicated hardware-security/compartmentalization scope.
  - GPU SIMT warp divergence, `TMA`, TPU systolic layout algebras, and physical adiabatic CMOS energy-recovery measurements.
- **unknown**:
  - Unpublished internal heuristics of Mill Computing's proprietary `genAsm -> conAsm` specializer (spill-cost heuristics and latency-scheduling tradeoffs across family members).
  - Completeness and deadlock-detection boundaries of Cerebras's closed-source `CSL` router/color allocator on arbitrary irregular topologies.
  - Optimality and scaling limits of Graphcore `Poplar`'s exchange-schedule solver on highly irregular dynamic sparse graphs.
  - Final hardware semantics of Tenstorrent `Quasar` Dataflow Buffers (`LocalDFBInterface`), visible only via `#ifdef ARCH_QUASAR` stubs in `cb_api.h` at commit `11551f901bb3e2ad451a0fe5036312c4687d40c3`.
- **known not to apply**:
  - Mill operand metadata (`None`, `NaR`, width, per-operand FP flags) does **not** persist across main memory stores (`US 11,226,821` strips metadata on store).
  - Unconstrained C `&local` aliasing, `uintptr_t` casts, global sticky `FCSR` flags, and shared-memory lock concurrency do **not** map soundly onto Mill belts/scratchpads/granularity bounds, Cerebras 48 KB PE meshes, Graphcore BSP `ComputePhase`, Groq zero-arbiter slices, UPMEM isolated banks, or Janus/PISA bijective states.
  - Passing [verify_belt_nar_and_bsp_semantics.py](support/verify_belt_nar_and_bsp_semantics.py) validates the modeled operational semantics only, not commercial silicon RTL.
- **unsupported**:
  - In `tenstorrent/tt-metal@11551f901bb3e2ad451a0fe5036312c4687d40c3`, `cb_push_back` and `cb_pop_front` do **not** support wrap-spanning page counts (`ptr + n > fifo_limit` fails `ASSERT`) or multi-thread concurrent push/pop on one CB ID (`dataflow_api.h:217-223, 269-275`; `cb_api.h:29-34, 62-66, 116-120`).
  - `noc_async_write_multicast` does **not** deliver to self (`num_dests` excludes self and must be $\ge 1$; loopback requires `noc_async_write_multicast_loopback_src`, `dataflow_api.h:918-930`).
  - UPMEM DPUs do **not** support direct DPU-to-DPU transfers or unaligned / $> 2048$-byte single MRAM DMA transactions.
  - Groq TSP streaming slices do **not** support hardware cache coherence, dynamic bus arbitration, or dynamic hardware branch prediction.

## Evidence

All primary sources were verified on `2026-11-19`:

1. **Mill Computing Granted U.S. Patents & Compiler Docs (`https://millcomputing.com/patents/`, `https://millcomputing.com/docs/compiler/`)**:
   - `US 9,513,904` (per-byte valid caches); `US 9,513,920` (split-stream encoding); `US 9,513,921` (Dec 20, 2016 — temporal Belt + Spiller); `US 9,524,163` (pointer event bits, Interest Mask Registers, 6-bit granularity bounds); `US 9,652,230` (May 16, 2017 — Implicit Zero Map `IZM`); `US 9,690,581` (deferred loads `DLOAD`, Retire Stations, `pickup`); `US 9,747,216` (Aug 29, 2017 — byte-addressable `Base`/`Fence` scratchpad + Spiller); `US 9,747,238` (Aug 29, 2017 — split crossbar + slot-based functional units); `US 9,785,441` (elided NOP alignment hole); `US 9,817,669` (Nov 14, 2017 — `RETIRE`, `INNER`/`LEAVE`, rotating scratchpad); `US 9,875,106` (EBB exit prediction); `US 9,959,119` (double-ended decoding); `US 9,965,274` (result-tag bypass); `US 10,802,987` (backless cache lines); `US 11,226,821` (Jan 11, 2022 — unitary metadata, `NaR`/`None`, `pick`, `smear`/`smearx`, `Remaining`, `Satisfied`).
   - I. Godard, *"The Compiler — LLVM meets the truly alien"* (June 10, 2015): `LLVM IR -> genAsm -> conAsm`.
2. **EDGE/TRIPS, RVSDG & CGRAs**:
   - D. Burger, S. W. Keckler, K. S. McKinley et al., *IEEE Computer* 37(7):44–55, July 2004, `DOI:10.1109/MC.2004.65`; A. Smith et al., CGO 2006 (128-op, 32-LSID, 32-reg TRIPS bounds).
   - N. Reissmann, J. C. Meyer, H. Bahmann, M. Själander, *ACM TECS* 19(6), 2020, `DOI:10.1145/3391902` (`arXiv:1912.05036`).
   - R. Prabhakar et al., *Plasticine*, ISCA 2017, `DOI:10.1145/3079856.3080256` (16-lane PCU, 256 KB / 16-bank PMU); D. Koeplinger et al., *Spatial*, PLDI 2018, `DOI:10.1145/3192366.3192379`; R. Prabhakar et al., *SambaNova SN40L*, MICRO 2024, `DOI:10.1109/MICRO61859.2024.00100`.
3. **Cerebras WSE, Graphcore IPU & Groq TSP**:
   - S. Lie, *IEEE Micro* 43(3):18–30, May–June 2023, `DOI:10.1109/MM.2023.3256384`.
   - Z. Jia, B. Tillman, M. Maggioni, D. P. Scarpazza, `arXiv:1912.03413v1`, `DOI:10.48550/arXiv.1912.03413`.
   - D. Abts et al., ISCA 2020, `DOI:10.1109/ISCA45697.2020.00023`; D. Abts et al., ISCA 2022, `DOI:10.1145/3470496.3527405`.
4. **Tenstorrent Tensix Source (`tenstorrent/tt-metal`, commit `11551f901bb3e2ad451a0fe5036312c4687d40c3`)**:
   - `tt_metal/hw/inc/api/compute/cb_api.h:21-186` (`cb_wait_front` cumulative & `5+7=12` vs `7+7=14` rules, SPSC rule, `UNPACK`/`PACK` dispatch, `ARCH_QUASAR` `LocalDFBInterface`, TRISC mailbox broadcast).
   - `tt_metal/hw/inc/api/dataflow/dataflow_api.h:208-224,260-276,377-493,876-957,1921-2150` (exact `fifo_wr_ptr == fifo_limit` wrap `ASSERT`, `uint16_t` modular occupancy, `invalidate_l1_cache()`, `noc_async_write_multicast` self-exclusion, barriers/semaphores).
   - `tt_metal/hw/inc/internal/tt-1xx/wormhole/dev_mem_map.h:33,41-44,52-54,193-197`; `tt_metal/hw/inc/internal/tt-1xx/blackhole/dev_mem_map.h:33,43-45`; `tt_metal/hw/inc/api/circular_buffer_constants.h:22-27`; `tt_metal/api/tt-metalium/circular_buffer_constants.h:1-35`.
5. **PIM, Reversible Computing & LLVM `poison`**:
   - J. Gómez-Luna et al., *IEEE Access* 10, 2022, `DOI:10.1109/ACCESS.2022.3174101` (`arXiv:2105.03814`); S. Lee et al., ISCA 2021, `DOI:10.1109/ISCA52012.2021.00013`.
   - R. Landauer, *IBM J. Res. Dev.* 5(3):183–191, 1961, `DOI:10.1147/rd.53.0183`; T. Yokoyama & R. Glück, PEPM 2007, `DOI:10.1145/1244381.1244404`; T. Yokoyama, H. B. Axelsen & R. Glück, CF 2008, `DOI:10.1145/1366230.1366239`.
   - J. Lee et al., *Taming Undefined Behavior in LLVM*, PLDI 2017, `DOI:10.1145/3062341.3062343`.
6. **Executable Probe Execution (`support/verify_belt_nar_and_bsp_semantics.py`)**:
   - Executed `2026-11-19` via `python3 -B reports/mill-edge-dataflow-and-tile-bsp-compiler-architectures/support/verify_belt_nar_and_bsp_semantics.py` (exit `0`): verified Mill lattice/hoisting/provenance/`conform`/`RETIRE` ($N \in \{0,1,2,3,7,16\}$)/`smearx`, Graphcore BSP determinism (25 randomized schedules + remote-compute and exchange-contention rejections), Tenstorrent Tensix CB protocol (101 BFS states, `5+7=12` pass, `7+7` wrap violation, circular deadlock, SPSC dual-pop, cumulative wait check), and Janus Fibonacci bijection ($n \in [0, 15]$).

## Revalidation

1. **Re-run the standalone semantic verifier** (Python 3.10+ stdlib only):
   ```console
   python3 -B reports/mill-edge-dataflow-and-tile-bsp-compiler-architectures/support/verify_belt_nar_and_bsp_semantics.py
   ```
2. **Diff `tenstorrent/tt-metal` headers against `11551f901bb3e2ad451a0fe5036312c4687d40c3`**:
   - Inspect `tt_metal/hw/inc/api/compute/cb_api.h`, `tt_metal/hw/inc/api/dataflow/dataflow_api.h`, `tt_metal/hw/inc/api/circular_buffer_constants.h`, and `tt_metal/hw/inc/internal/tt-1xx/{wormhole,blackhole}/dev_mem_map.h` (plus `tt-2xx/quasar/`) for changes to `fifo_wr_ptr == fifo_limit` wrap contiguity, cumulative `cb_wait_front` rules, `NUM_CIRCULAR_BUFFERS`, `MEM_L1_SIZE`, or `Quasar` `LocalDFBInterface` replacement of CBs.
3. **Check successor specifications**:
   - Monitor `https://millcomputing.com/patents/` for new grants or shipped silicon manuals, and check newer Cerebras WSE/CSL, SambaNova RDU, Groq LPU, and UPMEM SDK documentation (`mram_read`/`mram_write` alignment and transfer-size caps), adding successor generations as distinct subjects rather than overwriting pinned observations.
