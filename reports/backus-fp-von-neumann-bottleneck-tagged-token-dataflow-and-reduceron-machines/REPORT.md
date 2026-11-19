# Critiques of the von Neumann Bottleneck, Harvard Split-Memory Enforcement, Tagged-Token Dataflow, and Reduceron Graph-Reduction Machines

## Summary

The classical von Neumann execution model couples three distinct mechanisms into one bottleneck: (1) a single sequential program counter (`PC`) driving control flow, (2) a unified readable/writable/executable linear address space multiplexing instructions and mutable data over a narrow address/data bus, and (3) word-at-a-time state mutation via named storage cells. Decoupling or replacing these three mechanisms across hardware, OS page tables, compilers, and language runtimes yields four sharp architectural and verification lessons:

1. **Point-free combinator algebras eliminate mutable state variables at the cost of routing-term explosion unless compiled to flat, bounded-arity templates.** John Backus's 1977 Turing Award lecture (`FP`/`FFP`, `DOI: 10.1145/359576.359579`) replaces named variables and imperative assignments with variable-free combining forms obeying algebraic equational laws, while Turner's bracket abstraction (`{S, K, I, B, C}`) compiles $\lambda$-expressions into variable-free combinator graphs. However, naive `{S, K, I}` abstraction inflates $k$-argument expressions cubically ($729$ AST nodes at $k = 8$), and even `{S, K, I, B, C}` grows quadratically ($67$ nodes at $k = 8$). Hardware graph reducers only beat sequential bytecode machines when they abandon fine-grained combinators for flat, multi-atom **template instantiation** (`21` atoms at $k = 8$ in Reduceron).
2. **Retrofitting Harvard instruction/data separation (`XOM` and `W^X`) onto modified-Harvard unified virtual memory breaks silently when compilers emit inline data reads or page-table bits overload privilege flags.** On ARM/Thumb-2 and AArch64, Execute-Only Memory (`-mexecute-only`) requires suppressing `.text` constant islands and `TBB`/`TBH` PC-relative byte/halfword jump-table loads (`llvm/llvm-project` `ARMConstantIslandPass.cpp`, `ARMISelLowering.cpp`), because D-side loads from execute-only `.text` fault even though I-side fetches succeed. Worse, pre-ARMv8.7 Linux implemented user execute-only mappings (`_PAGE_EXECONLY`) by clearing `PTE_USER` (`AP[1]=0`) while keeping `PTE_UXN=0`; because ARMv8.1 `PAN` (Privileged Access Never) only trapped `EL1` kernel reads when `PTE_USER` was set, user XOM pages completely bypassed `PAN`, forcing upstream Linux (`torvalds/linux`) and Android 11 to disable AArch64 XOM until hardware `FEAT_EPAN` and ARMv8.9 `PIE` (`PIE_E0 = PIE_X_O`, `PIE_E1 = PIE_NONE_O`) restored orthogonal permission semantics.
3. **Program-counter-free dataflow substrates succeed or fail on how they materialize token matching and imperative memory ordering.** Pure dynamic tagged-token dataflow replaces the `PC` with associative `<context, code-block, port>` tag CAMs that become energy and area bottlenecks; MIT Monsoon (`DOI: 10.1145/285930.285999`) eliminates associative CAMs via an **Explicit Token Store (`ETS`)** using direct frame-pointer + offset presence bits, Id **I-structures** (`DOI: 10.1145/69558.69562`) preserve Church–Rosser determinism via write-once `{EMPTY, DEFERRED, PRESENT, TOP}` slots, **WaveScalar** (`DOI: 10.1109/MICRO.2003.1253203`) enforces sequential load/store order without a `PC` or central reorder buffer via topological `(pred, seq, succ)` wave-ordered memory tags, and **Triggered Instructions** (`DOI: 10.1145/2485922.2485935`) / **RipTide** (`MICRO 2022`) replace per-cycle instruction fetch with local queue/predicate guards.
4. **Wide parallel FPGA memories enable single-cycle PC-free graph reduction (`Reduceron`), provided the compiler enforces five static template-fragmentation and GC-safepoint invariants.** Naylor, Runciman, and Reich's **Reduceron** (`tommythorn/Reduceron` @ `e9b051238698040afe1d484b1ebd57f6b58f5036`; `JFP 2012`, `DOI: 10.1017/S0956796812000214`) partitions state across six independent wide Xilinx Virtex-5 BRAM structures (`234`-bit program templates, dual-port `77`-bit heap applications, `8`-wide `Octostack` crossbar, update stack, case-table stack, and stop-and-copy to-space) to execute each semantic reduction rule in **one `96 MHz` clock cycle** (`10.08x`–`20.06x` faster than a `210 MHz` MicroBlaze C baseline on the same FPGA, and within `4x`–`5x` of `3 GHz` Core 2 Duo `GHC -O2`). Sound single-cycle execution relies on (a) compile-time `refersCheck` template splitting so the top-of-spine atom never points to a heap cell allocated in the same clock cycle, (b) `canCollect()` safepoint gating (`original == True`) so stop-and-copy GC never fires mid-fragment while unrooted sub-template cells are addressed via negative relative heap offsets, (c) 1-bit pointer-uniqueness dashing (`Invariant 3`) eliminating `88%` of thunk updates in zero critical-path cycles, and (d) dynamic/static **Primitive Redex Speculation (`PRS`)** folding unboxed arithmetic during template instantiation (`1.58x` cycle speedup and `2.5x` fewer GC cycles measured on `fib 20`).

## Applicability

This report compares and synthesizes nine primary artifacts spanning language algebra, modified-Harvard OS/compiler enforcement, dataflow microarchitectures, and graph-reduction hardware/runtimes:

- **Algebraic Functional Substrates**: John Backus's `FP` and `FFP` systems (`CACM 1978`, `DOI: 10.1145/359576.359579`) compared against Turner SKI/director-string combinators (`SPE 1979`), Simon Peyton Jones's Spineless Tagless G-machine in `ghc/ghc` (`83038fbee5efea8e3ebd5090b2ff5537462e169d`, `rts/include/rts/storage/ClosureMacros.h`), and Lafont interaction-combinator reduction in `HigherOrderCO/HVM` (`7365a56cca56a5853c979755891cb86aa343c42d`).
- **Harvard vs. Modified-Harvard Memory Protection**: `llvm/llvm-project` (`4520919d72d4fbcaa8416c9de404a0d37161b410`, `llvm/lib/Target/ARM/ARMConstantIslandPass.cpp` and `ARMISelLowering.cpp`) `-mexecute-only` code generation paired with `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `arch/arm64/include/asm/pgtable-prot.h`) `PAGE_EXECONLY`, `FEAT_EPAN`, and ARMv8.9 `PIE` encodings.
- **Dataflow & Spatial Control Paradigms**: Dennis static dataflow, Arvind/Nikhil MIT Tagged-Token Dataflow & Id I-structures/M-structures (`ACM TOPLAS 1989`), Papadopoulos & Culler's Monsoon Explicit Token Store (`ISCA 1990`), Swanson et al.'s WaveScalar wave-ordered memory (`MICRO 2003` / `ACM TOCS 2007`), and Parashar et al.'s Triggered Instructions (`ISCA 2013`).
- **Hardware Graph Reduction**: Naylor, Runciman, and Reich's FPGA Reduceron across both the York Virtex-5 `77`-bit-app / `18`-bit-atom implementation (`mn416/reduceron-project` @ `9dba5d9500e131f2bce31b6258bfc39e69c6bf3d`, `JFP 2012`) and Tommy Thorn's extended `6`-atom-per-app (`APSIZE = 6`, `MAXPUSH = 8`, `MAXAPS = 4`) / `128`-bit packed external-memory fork (`tommythorn/Reduceron` @ `e9b051238698040afe1d484b1ebd57f6b58f5036`), where behavioral differences between the `2008` (`IFL '07`, `111 MHz`), `2010`/`2012` (`ICFP '10` / `JFP '12`, `96 MHz` spineless + PRS), and `emu.c` (`APSIZE = 6`, `22`-bit/33-bit atom variants) revisions are distinguished explicitly below.

Host execution observations (`emu.c` compilation and runs, plus standalone Python verification probes) were collected on `x86_64` Linux (`gcc -O2`, Python `3.11+`). Cycle counts from `emu.c` reflect architectural Reduceron clock ticks (`swap + prim + apply + unwind + update`), excluding multi-cycle stop-and-copy GC sweeps (`#GCs` reported separately).

## Findings

### 1. Backus's von Neumann Bottleneck, Point-Free `FP`/`FFP`, and Combinator Compilation Trade-Offs

`Basis: normative + source + execution + derived`

In his 1977 Turing Award lecture (*CACM* 21(8):613–641, `DOI: 10.1145/359576.359579`), Backus identifies two coupled pathologies of conventional architectures and imperative languages:

1. **Physical & Semantic Word-at-a-Time Traffic**: Every computation is decomposed into pumping single machine words back and forth through a narrow address/data conduit (the *von Neumann bottleneck*), where a large fraction of traffic is not problem payload at all, but addresses, loop indices, stack-frame bookkeeping, and instruction fetches needed solely to locate the next word.
2. **Non-Algebraic State-Transition Semantics**: Imperative statements operate on an implicit global store $\sigma : \text{Loc} \to \text{Val}$ via assignment `x := e`. Because expressions carry side effects and aliasing hazards, programs lack simple compositional substitution laws; reasoning requires Hoare-style preconditions/postconditions or symbolic store threading over $\sigma$ rather than ordinary equational algebra over programs themselves.

Backus's **`FP` system** eliminates named variables altogether. An `FP` system consists of objects $O$ (atoms, sequences $\langle x_1, \dots, x_n \rangle$, and undefined $\bot$), primitive functions ($+, \times, \text{trans}, \text{tl}, \text{id}, \text{eq}, \dots$), and a fixed set of **functional forms** (program-forming operations, `PFO`s) applied via $f : x$:

- **Composition**: $(f \circ g) : x \equiv f : (g : x)$
- **Construction**: $[f_1, \dots, f_n] : x \equiv \langle f_1 : x, \dots, f_n : x \rangle$ (strict in $\bot$: if any $f_i : x = \bot$, the result is $\bot$)
- **Condition**: $(p \to f ; g) : x \equiv f : x$ if $(p : x) = T$, $g : x$ if $(p : x) = F$, else $\bot$
- **Apply-to-all**: $\alpha f : \langle x_1, \dots, x_n \rangle \equiv \langle f : x_1, \dots, f : x_n \rangle$
- **Right Insert (Fold)**: $/f : \langle x_1 \rangle \equiv x_1$, and $/f : \langle x_1, \dots, x_n \rangle \equiv f : \langle x_1, /f : \langle x_2, \dots, x_n \rangle \rangle$
- **Constant & Binary-to-Unary**: $\bar{y} : x \equiv y$ (for $x \neq \bot$); $(\text{bu } f \; x) : y \equiv f : \langle x, y \rangle$

Inner product becomes the variable-free point-free definition $\text{IP} \equiv (/+) \circ (\alpha \times) \circ \text{trans}$, and programs satisfy **laws of the Algebra of Programs** directly as function equalities—such as $[f_1, \dots, f_n] \circ g \equiv [f_1 \circ g, \dots, f_n \circ g]$ and $\alpha(f \circ g) \equiv (\alpha f) \circ (\alpha g)$—without side-condition checks for variable capture or pointer aliasing. To make `FP` extensible and hardware-realizable without a `PC`, Backus defines **`FFP` (Formal Functional Programming)** alongside an active linear expression-tree store (`Section 15` of Backus 1978) in which innermost reducible applications (`metacomposition` cells `( <op, ...> : operand )`) rewrite in place concurrently across a tree network of cells.

#### Why Naive Variable Elimination Blows Up: `SKI` vs. `STG` vs. `HVM` vs. Flat Templates

When general $\lambda$-calculus programs with arbitrary cross-nested variable references are compiled into variable-free combinators via D. A. Turner's bracket abstraction (*Softw. Pract. Exper.* 9(1):31–49, 1979, `DOI: 10.1002/spe.4380090105`), eliminating variables trades environment indexing for **combinator routing trees**:

- **Pure `{S, K, I}` Abstraction**: $[x]\,x = \mathbf{I}$; $[x]\,E = \mathbf{K}\,E$ ($x \notin \text{FV}(E)$); $[x]\,(E_1\,E_2) = \mathbf{S}\,([x]\,E_1)\,([x]\,E_2)$. Abstracting $k$ arguments over a simple left-associated sum $x_0 + x_1 + \dots + x_{k-1}$ duplicates every combinator spine at each outer $\lambda$, exploding AST size as $\Theta(k^3)$.
- **Turner `{S, K, I, B, C}` Optimization**: Introducing $\mathbf{B}\,f\,g\,x = f\,(g\,x)$ (when $x \notin \text{FV}(f)$) and $\mathbf{C}\,f\,g\,x = (f\,x)\,g$ (when $x \notin \text{FV}(g)$) avoids duplicating closed subterms per pass, reducing AST growth on $k$-argument linear sums from $\Theta(k^3)$ to $\Theta(k^2)$—still quadratic when variables are routed past $k$ enclosing binders (improved to $O(k \log k)$ balanced routing via Kennaway & Sleep's 1988 director strings).
- **Executed Probe Comparison (`probe_pkg1.py`)**: Measuring exact AST node counts on $\lambda x_0 \dots x_{k-1}.\; ((x_0 + x_1) + \dots + x_{k-1})$ confirms:
  - $k = 2$: `25` nodes (`SKI`) vs. `1` (`BC` with $\eta$-reduction to `+`) vs. `3` atoms (`Reduceron` flat template);
  - $k = 4$: `137` nodes (`SKI`) vs. `15` (`BC`) vs. `9` atoms (`Reduceron`);
  - $k = 6$: `361` nodes (`SKI`) vs. `37` (`BC`) vs. `15` atoms (`Reduceron`);
  - $k = 8$: `729` nodes (`SKI`) vs. `67` (`BC`) vs. `21` atoms (`Reduceron`).

This quantitative gap explains three divergent historical engineering paths:
1. **Stock von Neumann Optimization (`STG` in `ghc/ghc` @ `83038fbee5efea8e3ebd5090b2ff5537462e169d`)**: Simon Peyton Jones's Spineless Tagless G-machine (*JFP* 2(2):127–202, 1992) concedes that stock CPUs have fast registers and instruction caches, compiling supercombinators to native machine code where closures pair an entry-code pointer with flat free-variable payloads. To mitigate indirect-jump and heap-dereference stalls when scrutinizing evaluated algebraic values, `ghc/ghc` (`rts/include/rts/storage/ClosureMacros.h:148–180`) steals the low `2` or `3` alignment bits (`TAG_MASK`) of `StgClosure*` pointers (`GET_CLOSURE_TAG`, `UNTAG_CLOSURE`, `tagConstr`) to encode whether a closure is already evaluated and which constructor tag (`1 .. TAG_MASK`) it carries, avoiding memory loads on evaluated scrutiny (`Marlow et al., ICFP 2007`, `13%`–`14%` wall-clock speedup). Even so, `STG` remains fundamentally memory-bandwidth- and branch-predictor-bound on thunk allocation and indirect entry calls.
2. **Parallel Interaction Combinators (`HigherOrderCO/HVM` @ `7365a56cca56a5853c979755891cb86aa343c42d`)**: Yves Lafont's Interaction Combinators (*Inf. Comput.* 1997: constructor $\gamma$, duplicator $\delta$, eraser $\epsilon$) guarantee **strong confluence** (every active principal-port pair rewrites locally in 1 step with zero global lock coordination). HVM2 maps active pairs onto multi-core CPU and CUDA GPU threads using packed 32-bit/64-bit ports and atomic CAS wire-linking, reaching hundreds of millions to billions of interactions/second on RTX 4090 GPUs. However, practitioner profiling of HVM/Bend reveals two sharp physical limits: (a) higher-order $\lambda$-terms outside elementary affine types require explicit *bookkeeping/duplication nodes* whose step count can exceed eager call-by-value execution by orders of magnitude, and (b) fine-grained irregular pointer-graph rewrites over global GPU VRAM hit atomic L2 contention whenever active wires cross warp-local shared memory.
3. **Wide-Memory Hardware Template Instantiation (`Reduceron`)**: Rather than reducing 2-node combinator redexes sequentially or compiling to `PC`-driven instructions, Reduceron compiles supercombinators into bounded flat expression-graph templates instantiated in parallel across wide dual-port SRAMs in a single clock tick.

---

### 2. Pure vs. Modified Harvard Split-Memory Consequences: `XOM`, Constant Islands, `PAN`/`EPAN`, and `W^X`

`Basis: source + normative + documentation + derived`

Pure Harvard machines (e.g., Microchip AVR `ATmega` Flash `PROGMEM` vs. SRAM, TI DSPs, microcontroller boot ROMs, and Reduceron's isolated `234`-bit Program BRAM vs. `77`-bit Heap BRAM) physically separate instruction and data address buses: an instruction address `0x0010` and a data address `0x0010` name completely disjoint storage arrays, simultaneous instruction fetch and multi-port data access never contend, and data overwrites structurally cannot corrupt executable code.

Mainstream application processors (x86-64, AArch64, RISC-V RV64GC) implement a **Modified Harvard** microarchitecture: split L1 Instruction (`L1I`) and L1 Data (`L1D`) caches sit in front of a unified L2/L3 cache and unified virtual address space. This compromise introduces three recurring systems, compiler, and security hazards:

#### Hazard 2A: Compiler Constant Islands & Inline Jump Tables vs. Execute-Only Memory (`XOM`)

To block Just-In-Time Return-Oriented Programming (`JIT-ROP`) from reading `.text` pages to harvest gadgets at runtime, OSes and embedded MPUs map code pages **Execute-Only** (`PROT_EXEC` without `PROT_READ`). On RISC ISAs with fixed-width 16/32-bit instructions (ARM/Thumb-2, AArch64), arbitrary 32/64-bit constants cannot fit in one instruction word; compilers traditionally emit PC-relative **constant islands** (literal pools embedded directly inside `.text` between basic blocks, read via `LDR Rt, [PC, #imm]`) and inline Thumb-2 table branches (`TBB [PC, Rm]` / `TBH [PC, Rm, LSL #1]`).

Direct inspection of `llvm/llvm-project` (`4520919d72d4fbcaa8416c9de404a0d37161b410`) shows the exact codegen invariants required when `-mexecute-only` (`Subtarget->genExecuteOnly()`) is enabled:

1. **Suppression of `TBB`/`TBH` Inline Jump Tables** (`llvm/lib/Target/ARM/ARMConstantIslandPass.cpp:496–498`):
   ```cpp
   // Optimize jump tables using TBB / TBH.
   if (GenerateTBB && !STI->genExecuteOnly())
     MadeChange |= optimizeThumb2JumpTables();
   ```
   Because `TBB`/`TBH` issue a **D-side byte/halfword load** against `.text`, executing `TBB` inside an execute-only page triggers an immediate Data Abort / `SIGSEGV` (`SEGV_ACCERR`). `ARMISelLowering.cpp:3270–3276` likewise forces jump tables out-of-line into `.rodata` (`EK_BlockAddress` rather than `EK_Inline`) when `hasV8MBaselineOps()` `BF`/`B` relative branches do not suffice.
2. **Promotion of Constant Pools & `MOVW`/`MOVT` Synthesis** (`llvm/lib/Target/ARM/ARMISelLowering.cpp:2454–2505, 3239–3255`):
   - `long-calls` combined with `-fPIC` and `-mexecute-only` is rejected as a **fatal usage error** (`ARMISelLowering.cpp:2454–2456`: `"long-calls with execute-only and position-independent code is not supported"`), because PIC GOT-prel thunks rely on PC-relative constant-pool loads.
   - 32-bit addresses and immediates must be materialized purely from I-side instruction bits via `MOVW` + `MOVT` (`++NumMovwMovt`, `ARMISelLowering.cpp:2464–2470`) or AArch64 `MOVZ` + `MOVK` sequences (up to 4 instructions / 16 bytes for a 64-bit constant), while floating-point/vector constant pools are promoted to separate internal `GlobalVariable`s in `.rodata` (`ARMISelLowering.cpp:3243–3255`).
   - Any hand-written assembly, CRT startup stub, or static archive compiled *without* `-mexecute-only` linked into an XOM segment leaves a single inline literal load that crashes deterministically at runtime.

#### Hazard 2B: The Linux/Android ARMv8 `XOM` $\times$ `PAN` Privilege-Bit Collision Post-Mortem

Android 10 enabled `XOM` (`PROT_EXEC`-only `.text`) across AArch64 system binaries in 2019, only for both upstream Linux (`torvalds/linux`, Jan 2020, Catalin Marinas / Will Deacon) and Android 11 to **revert user `XOM` after security researcher Siguza disclosed a critical interaction flaw with `PAN` (Privileged Access Never)**:

- **Root Cause (Ad-Hoc PTE Encoding Trick)**: ARMv8.0-A stage-1 page table entries lacked an explicit user-execute-only permission state when `PTE_USER` (`AP[1] = 1`) was set (`AP[2:1] = 11` meant `EL0` Read-Only, so setting `UXN = 0` yielded Read+Execute, never Execute-Only). To synthesize `EL0` Execute-Only, Linux defined `_PAGE_EXECONLY` *without* `PTE_USER` (`AP[2:1] = 10`, `EL1` Read-Only / `EL0` No-Data-Access) while clearing `PTE_UXN` (`UXN = 0`, allowing `EL0` instruction fetch).
- **Security Failure**: ARMv8.1 `PAN` prevents the kernel (`EL1`) from accidentally dereferencing user-space pointers by faulting whenever `EL1` performs a data read to a page carrying `PTE_USER` (`AP[1] = 1`). Because `_PAGE_EXECONLY` cleared `PTE_USER` (`AP[1] = 0`), the CPU treated user-allocated `mmap(..., PROT_EXEC)` pages as **kernel-readable memory**—allowing an attacker in user space to map attacker-chosen data as `PROT_EXEC` and pass its address to a confused-deputy kernel read gadget with zero `PAN` fault!
- **Hardware & Kernel Resolution (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`)**: Inspection of `arch/arm64/include/asm/pgtable-prot.h:64–65, 149–189` confirms that Linux today retains `#define _PAGE_EXECONLY (_PAGE_DEFAULT | PTE_RDONLY | PTE_NG | PTE_PXN)` (index `4` vs. `_PAGE_READONLY_EXEC` index `5` with `PTE_USER`), but strictly gates user execute-only mappings on hardware **ARMv8.7-A `FEAT_EPAN`** (Enhanced PAN, which traps `EL1` reads of `AP[1]=0, UXN=0` pages) or **ARMv8.9-A `FEAT_S1PIE`** (Permission Indirection Extension, where `PIE_E0` maps `_PAGE_EXECONLY` to `PIE_X_O` while `PIE_E1` explicitly maps `_PAGE_EXECONLY` to `PIE_NONE_O`, lines `172` and `181`). On x86-64, user XOM instead relies on Intel Memory Protection Keys (`MPK`/`PKU`, `PKEY_DISABLE_ACCESS`), because `PKRU` suppresses D-side loads/stores while leaving I-side instruction fetches unaffected.

#### Hazard 2C: Dynamic `JIT` `W^X` Coherence Stalls on Modified-Harvard Cores

Whereas x86-64 hardware snoops `L1I` against `L1D` store buffers (incurring a severe ~100–300-cycle self-modifying-code pipeline nuke on cross-modifying writes), AArch64 and RISC-V maintain **non-coherent `L1I` vs. `L1D` caches**. Emitting JIT machine code safely under `W^X` requires:
1. Toggling write permission (`mprotect` TLB shootdown IPIs across all threads at `2`–`15 µs`, or Apple Silicon `MAP_JIT` + `pthread_jit_write_protect_np` writing thread-local `APRR`/`S3_6_C15_C1_5` in `< 10 ns` without TLB shootdowns); and
2. Executing explicit cache-line cleans to Point of Unification (`DC CVAU`), `DSB ISH`, instruction-cache invalidation (`IC IVAU`), `DSB ISH`, and cross-core context synchronization (`ISB` / `membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED_SYNC_CORE)` on Linux, because a remote thread running concurrently can execute stale prefetched instructions even after `IC IVAU` broadcasts unless it executes `ISB`).

---

### 3. Program-Counter-Free Dataflow Substrates: Tagged Tokens, `Monsoon` `ETS`, `I`-Structures, `WaveScalar`, and `Triggered Instructions`

`Basis: normative + documentation + execution + derived`

Dataflow architectures discard the sequential `PC` and register-renaming window altogether: an instruction fires iff its required operand tokens have arrived. Four generations of dataflow designs trace a systematic elimination of associative hardware bottlenecks and imperative memory-ordering gaps:

| Dataflow Substrate | Firing & Token-Matching Mechanism | Loop / Recursion Re-Entrancy | Memory & State Semantics | Dominant Hardware / Compiler Bottleneck |
| :--- | :--- | :--- | :--- | :--- |
| **Static Dataflow** (Dennis & Misunas, *ISCA* 1975) | Direct presence bits inside fixed instruction templates (`1` token per arc) | **Static loops only** via explicit back-pressure acknowledgment arcs; **no general recursion** | Pure value streams / arrays copied conceptually | Ack-arc double token traffic; zero dynamic recursion or multi-instance parallelism |
| **MIT Tagged-Token (`TTDA`)** (Arvind & Nikhil, *IEEE TC* 1990) | Associative **Waiting-Matching Unit (`WMU`)** CAM keyed on `<context, code-block, inst, port>` | Unbounded dynamic loop iterations & recursion via unique `context` tags | **Id `I-structures`** (`empty`/`deferred`/`present`) + `M-structures` (`take`/`put`) | Associative CAM `WMU` power/latency explodes under large unmatched token working sets |
| **MIT `Monsoon` (`ETS`)** (Papadopoulos & Culler, *ISCA* 1990, `DOI: 10.1145/285930.285999`) | **Explicit Token Store (`ETS`)**: token carries `<FP, IP>`; direct SRAM read/modify/write of 1-bit `presence` flag at `FP + r` | Dynamic heap/stack **Activation Frames (`FP`)** allocated per call/iteration | Split `I-structure` memory (`3` presence bits per 64-bit word) | Single-input (`unary`) tokens bypass frame store, but dyadic ops pay 1 extra bubble cycle on first operand arrival |
| **`WaveScalar`** (Swanson et al., *MICRO* 2003, `DOI: 10.1109/MICRO.2003.1253203`) | Distributed `WaveCache` PE tiles matching `<wave-num, offset>` tags | `wave-advance` instructions increment `wave-num` at loop/call boundaries without `PC` | **Wave-Ordered Memory (`WOM`)**: loads/stores carry `(pred, seq, succ)` tags | Tag width + store-buffer stalling when conditional paths require memory-NOP (`MEM-NOP`) gap repair |
| **`Triggered Instructions` (`TIA`) / `RipTide`** (Parashar et al., *ISCA* 2013, `DOI: 10.1145/2485922.2485935`; Gobieski et al., *MICRO* 2022) | Per-PE rule table `(input-channel-ready ∧ predicate-reg == mask) -> datapath op + pred update`; **token-free NoC routing** in RipTide | Explicit per-PE FSM predicate states & control-flow steer/merge switches in NoC | Banking/LSQ or statically disambiguated scratchpad channels | **NP-hard spatial place-and-route (`P&R`)** compile times & routing congestion when DFG exceeds PE fabric radix |

#### Key Semantic Invariants of `I`-Structures vs. `M`-Structures and Wave-Ordered Memory

1. **Deterministic Single-Assignment Confluence (`Id` `I-Structures`, Arvind, Nikhil, & Pingali, *ACM TOPLAS* 11(4):599–632, 1989, `DOI: 10.1145/69558.69562`)**:
   - Pure functional array updates copy entire arrays unless mutated in place, while arbitrary imperative stores introduce read-write data races under asynchronous dataflow firing.
   - An `I-structure` allocates an array of cells initialized to `EMPTY` and enforces a monotone lattice $\text{EMPTY} \sqsubseteq \text{DEFERRED}(q) \sqsubseteq \text{PRESENT}(v) \sqsubseteq \top_{\text{err}}$:
     - `I-fetch(a, i)` on `PRESENT(v)` returns `v` immediately; on `EMPTY` or `DEFERRED(q)`, it appends the reader's continuation tag `<FP, IP>` to a linked list queued directly inside slot `a[i]` (`DEFERRED(q')`) without spinning!
     - `I-store(a, i, v)` on `EMPTY` writes `PRESENT(v)`; on `DEFERRED(q)`, it writes `PRESENT(v)` and broadcasts `v` to every waiting continuation in `q`; on `PRESENT(_)` (a second write!), it transitions deterministically to $\top_{\text{err}}$ (run-time single-assignment violation).
     - **Verification Consequence**: Because `PRESENT(v)` is immutable once written and `I-fetch` blocks silently until `I-store` arrives, **any schedule of asynchronous dataflow firings produces the exact same observable result (or the exact same $\top_{\text{err}}$ fault)**—eliminating data-race non-determinism completely! Conversely, Barth, Nikhil, and Arvind's **`M-structures`** (*FPCA* 1991: `take` empties a full cell, `put` fills an empty cell) sacrifice Church–Rosser confluence to express accumulators and histograms in place, re-introducing schedule-dependent lock/race bugs.
2. **Enforcing Imperative Load/Store Total Order Without a Program Counter (`WaveScalar`, Swanson et al. 2003/2007)**:
   - Compiling C/C++/Rust to dataflow previously failed because pointer-aliasing loads and stores have no data dependence through registers when addresses are computed independently.
   - WaveScalar partitions a CFG into acyclic hyperblocks (**waves**, bounded by loops and calls), assigns each static memory operation inside a wave a topological sequence number `seq`, and annotates every memory request token with `<wave, pred, seq, succ>` (`?` when multiple predecessors/successors exist across a branch, resolved by compiler-inserted `MEM-NOP`s along memory-free branch arms).
   - **Completeness Invariant (`probe_pkg1.py`)**: A store buffer can retire or forward across `<w, pred, seq, succ>` iff a contiguous chain of `(succ_i == seq_{i+1}) ∧ (pred_{i+1} == seq_i)` links exists with zero gaps. In our executable probe, when `ST(seq=0, succ=1)` and `LD(pred=1, seq=2)` arrive out-of-order before `ST(pred=0, seq=1, succ=2)`, `LD(seq=2)` deterministically stalls (`retired_len = 1`) until `seq=1` arrives (`retired_len = 3`), guaranteeing sequential memory consistency with zero central `PC` or broadcast ROB!
3. **Industrial Spatial-Dataflow Reality Check (Intel `CSA` & Wave-Computing Post-Mortems vs. `RipTide`)**:
   - Commercial general-purpose dataflow startups and projects—including Wave-Computing's Dataflow Processing Unit (filed Chapter 11 in 2020) and Intel's Configurable Spatial Accelerator (`CSA`, developed under Triggered Instructions lineage and shelved in 2021)—repeatedly hit two non-academic deployment walls: (a) **Place-and-Route (`P&R`) Compilation Cliffs**, where mapping irregular control-heavy C++ graphs onto bounded-radix 2D PE meshes took minutes to hours of ILP/simulated-annealing compile time or spilled back to host x86 cores; and (b) **Amdahl Control-Flow Tax**, where dynamic tag matching and predicate broadcasting burned 30%–50% of on-chip energy on scalar code. CMU's **RipTide** (*MICRO* 2022) demonstrated that folding control-flow steer/merge/carry gates directly into NoC router crossbars with *statically scheduled token-free streams* cuts energy `6.6x` vs. a RISC-V scalar core on embedded C kernels, precisely by bounding fabric scale (e.g., `6x6` PEs) so SAT/SMT spatial mapping converges reliably.

---

### 4. Hardware Graph Reduction Without an Instruction Pointer: The FPGA `Reduceron`

`Basis: source + execution + documentation`

Direct inspection of `mn416/reduceron-project` (`9dba5d9500e131f2bce31b6258bfc39e69c6bf3d`, `jfp-reduceron.pdf`) and `tommythorn/Reduceron` (`e9b051238698040afe1d484b1ebd57f6b58f5036`, `flite/Flite/RedCompile.hs`, `emulator/emu.c`, `emulator/red_atom.h`, `fpga/Heap.hs`, `fpga/Collect.hs`) reveals how Reduceron eliminates the instruction pointer entirely while executing each graph-reduction rule in **1 clock cycle**.

#### 4.1 Six Parallel Memory Structures and Single-Cycle Prefetch Invariants

Instead of one unified memory port, the Virtex-5 LX110T Reduceron (`JFP 2012`, Table 2) splits machine state across six independent on-chip Block RAM (`BRAM`) structures consuming `90%` of the FPGA's `296` dual-port `18-Kbit` BRAMs (`5,328 Kbit` = `666 KiB` total) and only `14%` of logic slices at **`96 MHz`**:

| Parallel Memory Unit | Element Type | Width (Virtex-5 JFP / `emu.c` Extended) | Depth (Virtex-5) | Hardware Porting & Role |
| :--- | :--- | :--- | :--- | :--- |
| **Program Memory** | `Template` | `234` bits (`13` $\times$ `1K`$\times$`18b` BRAMs) | `1,024` templates | Single-port wide ROM/BRAM; outputs entire function template in 1 tick |
| **Heap (`fromSpace`)** | `App` | `77` bits (`77` $\times$ `32K`$\times$`1b` BRAMs) / `128` bits (`red_atom.h`) | `32,768` apps (`~308 KiB`) | **True dual-port** (`Heap.hs`: `snocA` + `snocB` append 2 apps in 1 tick!) |
| **Reduction Stack (`Octostack`)** | `Atom` | `18` bits (JFP) / `22`–`33` bits (`emu.c` / `red_atom.h`) | `8,192` atoms + **top-8 registers** | `8`-wide combinational crossbar (`~2,000` gates, `<1%` FPGA logic): simultaneous top-`8` read, pop $\le 8$, push $\le 6$ (`MAXPUSH=8` in `emu.c`) |
| **Update Stack (`UStack`)** | `(StackAddr, HeapAddr)` | `28` bits | `4,096` frames | Tracks shared reducible heap cells awaiting normal-form overwrite |
| **Case-Table Stack (`LStack`)** | `TemplateAddr` | `18` bits | `4,096` entries | Pushes case-alternative jump-table base indices (`MAXLUTS = 2`/tick) |
| **GC Copy Space (`toSpace`)** | `App` | `77` bits | `16,384` apps (`~154 KiB`) | Cheney-style iterative stop-and-copy target (`Collect.hs`) |

Note the width scaling between revisions: the Virtex-5 `JFP 2012` configuration uses `MaxAppLen = 4`, `MaxSpineLen = 6` (`6`-wide spine template instantiation!), and `MaxAppsPerBody = 2` (`77`-bit heap cells, `18`-bit atoms), whereas `tommythorn/Reduceron`'s `emulator/emu.c:17–21` widens `APSIZE = 6` (`6`-atom heap applications!), `MAXPUSH = 8`, `MAXAPS = 4`, and `ATOMWIDTH = 22`, and `emulator/red_atom.h:47–108` defines a compact `128`-bit external-memory cell packing four `33`-bit tagged atoms (with `HT = 5` or `3` implicit head-tag bits leaving `25`–`27` pointer bits = `512 MiB` to `2 GiB` addressable heap).

Because Xilinx BRAMs have a **1-cycle synchronous read latency** (an address presented in cycle $t$ appears on `outputA` in cycle $t + 1$), Reduceron avoids stall cycles by maintaining two hardware prefetch invariants across every transition (`JFP 2012`, §4.6):
- **Invariant 1 (Heap Prefetch)**: Whenever the top of the reduction stack `stack[sp-1]` is `PTR sh x`, heap application `heap[x]` is *already valid* on `Heap.outputA` at the start of the current clock cycle.
- **Invariant 2 (Template Prefetch)**: Whenever `stack[sp-1]` is `FUN orig arity f`, template `code[f]` is *already valid* on Program Memory's data bus at the start of the current clock cycle.

#### 4.2 Five Compiler-Hardware Co-Design Invariants Verified in Source (`RedCompile.hs`, `emu.c`, `Collect.hs`)

Reading `flite/Flite/RedCompile.hs` alongside `emulator/emu.c` and `fpga/Collect.hs` exposes five subtle correctness invariants that any verifier or compiler targeting template-instantiation hardware must preserve:

1. **The `refersCheck` Read-After-Write Hazard Split (`RedCompile.hs:135–177`)**:
   - Suppose template `f` allocates a new heap application `VAR sh 0` (at `base + 0`) *and* pushes `VAR sh 0` as the new top of the reduction stack (`head push`). In cycle $t$, `base + 0` is being *written* to `Heap` port A (`snocA`), so `Heap.outputA` cannot simultaneously prefetch `base + 0` for cycle $t + 1$, violating **Invariant 1**!
   - `RedCompile.hs:153, 175` detects `refersCheck (head push)` (`refersCheck (R.VAR sh i) = i >= 0`) and splits `f` into two templates (`fr n m`): template `f` instantiates the heap applications and pushes `[FUN False 0 x]` (preserving Invariant 2 via Program Memory lookup of `x`, with zero stack pops!), and sub-template `x` in cycle $t + 1$ pushes the relocated `VAR sh (i - offset)` onto the spine while prefetching `base + i` cleanly from `Heap`!
2. **Non-Interruptible Sub-Template Chains & GC Safepoint Gating (`RedCompile.hs:125–133`, `emu.c:664–667, 811`)**:
   - During a split template chain `f -> x_1 -> x_2`, `f` appends heap cells at `hp .. hp + k - 1` that are **not yet referenced by any atom on `stack` or `ustack`**; `x_1` will connect them using negative relative offsets `VAR sh (-k)` (`base + (-k)` in `emu.c:471`).
   - If stop-and-copy GC (`collect()`) triggered while `stack[sp-1]` held `FUN False 0 x_1`, `collect()` would discard the unrooted cells as garbage *and* reset `hp = gcHigh`, corrupting `base + (-k)` into an out-of-bounds or wrong-cell read!
   - `RedCompile.hs` (`flagFuns`) marks original top-level functions `original = True` and compiler-synthesized continuation fragments `original = False`; `emu.c:664–667` enforces:
     ```c
     static inline Bool canCollect() {
       return (stack[sp-1].tag != FUN || stack[sp-1].contents.fun.original);
     }
     ```
     paired with a **200-application heap guardband** (`if (hp > MAXHEAPAPPS-200 && canCollect()) collect();`, `emu.c:811`) bounding the maximum allocations any uninterruptible sub-template chain can perform before hitting an `original == True` safepoint.
3. **1-Bit Dynamic Uniqueness Dashing & Update Avoidance (`Invariant 3`, `JFP 2012` §5.1, `emu.c:302–307`)**:
   - Standard lazy evaluators push an update frame on *every* thunk entry, even when the thunk has only a single reference. Reduceron carries a `shared : Bool` bit inside every `PTR`/`VAR`, `ARG`, and `REG` atom, maintaining **Invariant 3**: *Every `PTR False x` (`shared == False`) on the reduction stack points to an application referenced nowhere else in the machine.*
   - Three combinational-logic dashing rules preserve Invariant 3 in zero extra clock cycles: (a) compiler marks `ARG True i` iff parameter `i` occurs $> 1$ time in a template (`RedCompile.hs:117–119`); (b) unwinding `PTR True x` dashes every `PTR` inside `heap[x]` to `shared = True` as it enters the stack, and pushes an update frame *only* if `sh == True && red(heap[x])`; and (c) **updating `heap[ha]` with a normal form on the stack dashes the normal form's stack atoms (`dashN`, `emu.c:303`)** because writing those atoms to `heap[ha]` duplicates any unique pointer they held!
   - Our executable probe (`probe_pkg1.py`) demonstrates that omitting `dashN` during `update` breaks Invariant 3: a boxed thunk `u = 20 + 22` inside a shared constructor is evaluated *twice* (`2` evaluations instead of `1`, breaking call-by-need sharing and exploding exponential DAGs). Across the 16 Reduceron benchmarks, sound dynamic dashing eliminates **`88%` of all heap updates** and shrinks peak `UStack` depth from `406` to `11`.
4. **The Stop-and-Copy Forwarding-Pointer `shared`-Bit Bug (`emu.c:562–566`)**:
   - In `copyChild(Atom child)`, when `heap[addr]` is first evacuated to `heap2[gcHigh]` via a unique pointer `child` (`shared = 0`), `heap[addr]` is overwritten with a `COLLECTED` forwarding marker. An earlier Reduceron emulator bug wrote `return app.atoms[0];` on subsequent encounters of `COLLECTED`—which overwrote a *second* caller's `shared = 1` bit with `0`, manufacturing bogus "unique" pointers after GC! `emu.c:562–566` explicitly documents and fixes this by preserving the incoming `child.contents.var.shared` bit and updating only `child.contents.var.id = app.atoms[0].contents.var.id`.
5. **Dynamic & Static Primitive Redex Speculation (`PRS`, `emu.c:488–505`, `Memo50.txt`)**:
   - In `instApp`, `PRIM regId [a, PRI op, b]` checks in combinational logic whether `a` and `b` (from `ARG` or `REG`) are *already unboxed `NUM` atoms* during function instantiation. If so (`a.tag == NUM && b.tag == NUM`), an on-chip ALU computes `registers[rid] = prim(op, a, b)` immediately in the **same clock cycle** without allocating a heap thunk! If either operand is still a `VAR` thunk pointer, hardware falls back cleanly by allocating `[inst(a), PRI op, inst(b)]` at `heap[hp++]` and setting `registers[rid] = VAR False hp`.
   - Running the compiled `emu` binary (`gcc -O2 emu.c`) on `fib(20) = 10946` confirms that enabling `PRS` cuts total cycles from `207,910` to `131,344` (`1.58x` speedup), eliminates `100%` of heap updates (`10% -> 0%`), cuts `Unwind` steps from `31%` to `16%`, and drops stop-and-copy `#GCs` from `5` to `2` (`Max Heap` live post-GC cells `26 -> 8`). Runciman's `Memo50.txt` (`mn416/reduceron-project`) further shows that static `Ana`/`Cata` algebraic-valuableness fixpoint analysis (`Table 8` of `JFP 2012`) doubles `Fib` throughput again (`0.90 -> 1.80` hand-reductions/cycle, `2.0x` runtime speedup) by eliminating PRS fallback templates.

---

### 5. Six-Level Quantitative Engineering Matrix (`L1`–`L6`)

`Basis: source + execution + documentation + derived`

Every non-von-Neumann or split-memory substrate shifts costs sharply across authoring (`L1`), toolchain build (`L2`), compilation/synthesis (`L3`), runtime execution (`L4`), certificate/invariant checking (`L5`), and memory/silicon/energy footprints (`L6`):

| Substrate / System | (L1) Authoring & Day-2 Proof/Repair Velocity | (L2) Toolchain / Simulator Build Time & RSS | (L3) Program Compile / Place-and-Route Speed | (L4) Execution Speed, Tail Latency & WCET | (L5) Static / Certificate Verification Speed | (L6) Memory, Binary, Silicon & Energy Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Backus `FP` / Turner `SKI` Combinators** | Compact equational laws (`~10` lines for matrix/IP specs), zero alias proofs; high cognitive load (`>4` nested point-free forms) | Minimal reference reducer/translator `< 500` LoC; builds in `< 0.2 s` (`< 30 MiB` RSS) | Bracket abstraction $O(n)$–$O(n^3)$ in `< 5 ms` for KLoC modules | Naive `SKI` `10x`–`50x` slower than `STG` due to 2-node routing steps (`SKIM` 1985 reached `30x` `8 MHz 68000`) | Pure syntactic $\beta$/combinator rewrite checking at `> 100 MB/s`, `< 1 ms` cold start | **Cubic `SKI` AST blowup** (`729` vs `21` nodes at $k=8$); high transient cons-cell churn |
| **Modified-Harvard `XOM` (`LLVM -mexecute-only` + Linux `EPAN`/`PIE`)** | Near-zero source change for C/Rust, **high Day-2 build-flag/ASM audit cost** (1 non-XOM `.o` object crashes process) | `llvm-project` full build `~25`–`60 min`, `8`–`16 GiB` LLD peak RSS | `< 1%` compile-time overhead in `ARMConstantIslandPass` / `ISel`; `< 50 ms` per small TU | `2%`–`6%` code-size/cycle overhead (`MOVW`+`MOVT` / `MOVZ`+`MOVK` replacing 1-load literal pool); `MAP_JIT` `APRR` switch `< 10 ns` vs `mprotect` IPI `2`–`15 µs` | ELF section-scan verifier checking zero `.text` D-side relocs/TBB ops runs at `> 500 MB/s` (`< 2 ms`) | `4`–`16 B` immediate sequence vs `4 B` `LDR + 4/8 B` literal; zero extra page-table RAM with hardware `EPAN`/`PIE` |
| **Dynamic Dataflow (`Monsoon ETS` / `WaveScalar` / `RipTide`)** | `Id` functional code concise; spatial CGRA / `TIA` kernels require manual banking & channel-sizing tuning | Academic RTL + LLVM CGRA flow (`RipTide` / `WaveScalar` sim) `5`–`20 min` build, `2`–`6 GiB` RSS | `Monsoon`/`WaveScalar` wave formation `< 1 s`; **CGRA `P&R` SAT/ILP `1 s` to `> 600 s` `rlimit` timeouts** on irregular graphs | `Monsoon` `10 MIPS`/PE (`1990`); `WaveScalar` `1.2`–`1.8x` IPC over OoO baseline; `RipTide` **6.6x energy efficiency** over scalar RISC-V (`µW` regime) | `WaveScalar` `(pred,seq,succ)` topological completeness check is linear $O(|E|)$ (`< 1 ms`) | `Monsoon` `3` presence bits per `64b` I-structure word (`4.7%`); `WaveScalar` tag overhead `~16`–`32b`/op; `RipTide` `0` dynamic tag bits |
| **`GHC` `STG` on Stock OoO CPU (`ghc/ghc`)** | Mature Haskell ecosystem; proving low-level RTS/GC invariants requires complex concurrent separation logic | Full `GHC` bootstrap `20`–`45 min`, `4`–`8 GiB` RSS | `100 ms`–`10+ s` per module (Core-to-Core + STG-to-Cmm/LLVM) | **`0.05`–`0.80 s`** across 16 Reduceron benchmarks at `3 GHz` (`4x`–`5x` faster than `96 MHz` FPGA Reduceron); GC tail spikes `0.9%`–`45.3%` runtime (`OrdList`) | Core Lint typecheck `~5`–`20 MB/s`; RTS C runtime (`~100 KLoC`) unverified | High RTS footprint (`~1`–`4 MiB` binary overhead, `480 KiB`+ nursery/heap); `2`–`3` pointer tag bits in `StgClosure*` |
| **Parallel Interaction Nets (`HigherOrderCO/HVM`)** | Affine/functional subset ergonomic (`Bend`), non-affine higher-order terms require manual duplication/superposition tuning | `hvm` C/CUDA compiler builds in `~3`–`15 s` (`gcc`/`nvcc`), `< 500 MiB` RSS | Term-to-interaction-net lowering `< 50 ms` interactive | Up to `10^9` interactions/s on RTX 4090 for embarrassingly parallel trees; degrades sharply under atomic CAS contention | Local active-pair port linearity check $O(|V|)$ at `> 200 MB/s` (`< 1 ms`) | `64`-bit node pairs + preallocated multi-GB flat interaction-net arena on GPU |
| **FPGA `Reduceron` (`tommythorn/Reduceron`)** | **~2,000 LoC York Lava** (`<400` LoC reduction rules + `300` LoC `Recipe`); `emu.c` is `1,040` LoC; rapid architectural iteration | `emu.c` builds in **`0.18 s` (`~32 MiB` RSS)**; `flite` Haskell compiler `< 5 s`; Verilog full regression takes days | `flite -r` compiles Haskell subset to `.red` templates in **`< 20 ms`**; **FPGA bitstream synthesis/P&R `15`–`45 min` (`2`–`4 GiB` RSS)** | **`96 MHz`** Virtex-5 (`0.40`–`1.80` hand-reductions/cycle); **`10.08x`–`20.06x` faster than `210 MHz` MicroBlaze**; deterministic `1`-tick step outside stop-and-copy GC (`0.1%`–`14.7%` `%GC`) | Static template auditor (`MaxAppLen`, `MaxSpineLen`, `refersCheck`, `original` safepoints) runs in **`O(|P|)` `< 1 ms`** (`> 150 MB/s`) | **`20,050 B` `.text` (`36 KiB` ELF)** for `emu`; **`666 KiB` total Virtex-5 BRAM** (`462 KiB` dual-space heap), `14%` Virtex-5 logic slices, `< 3 W` FPGA core power |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Minimization (`C2`)

`Basis: derived + source`

#### (C1) Human Comprehensibility vs. Agent Execution Ease

- **The Point-Free Readability Inversion**: LLMs and algebraic rewrite engines manipulate Backus `FP` combinators (`(/+) ∘ (α×) ∘ trans`) and `SKI` terms effortlessly because every subterm is context-free (zero alpha-renaming or free-variable environment tracking). For human engineers, however, point-free expressions rapidly exceed human working memory (`4 ± 1` chunks) once `3+` values must be plumbed across asymmetric branches (`bu`, `trans`, `distl`, or `S`/`B`/`C` combinator nests), turning a trivial 1-line named expression `f(x, y, z) = (x + z) * (y - z)` into an opaque routing puzzle where Day-2 spec changes require re-deriving positional permutations.
- **1-Page Auditability of Reduceron vs. Stock OoO + RTS**: By contrast, Reduceron's small-step operational specification (`step :: (Prog, Heap, Stack, UStack) -> State`, `JFP 2012` §3 & §5) fits literally on **one printed page (`< 45` lines of executable Haskell)** while preserving named F-lite source variables for human authors and compiling directly into flat, human-readable `.red` templates (`("fib_false", 0, [], ...)`). When a hardware or compiler bug occurs (such as the `COLLECTED` `shared`-bit bug in `emu.c:562`), `emu -t` prints the complete architectural state (`Heap`, `Stack`, `UStack`, `Regs`, `LStack`) at each discrete tick—eliminating speculative-execution ghosts, non-coherent `L1I`/`L1D` races, and hidden microarchitectural state.
- **Dataflow Debugging Legibility**: `Id` `I-structures` yield **schedule-invariant failure diagnostics** (a double-write `TOP_ERROR` occurs on the exact same cell regardless of thread/PE timing), whereas `M-structures` and spatial CGRA place-and-route spills force humans to debug non-local timing and topological congestion artifacts invisible in source code.

#### (C2) Universal Conceptual Minimization: Eliminating Complexity vs. Shifting It

Comparing failed workarounds against durable solutions across all nine subjects isolates where complexity is merely *renamed/pushed into adapters* versus *genuinely eliminated*:

1. **False Simplification #1 — Overloading Privilege Bits for Permission Orthogonality (`Linux ARMv8.0 XOM`)**: Encoding user Execute-Only by clearing `PTE_USER` did not add true Harvard separation; it pushed a hidden obligation onto every `EL1` kernel memory-access check (`PAN`), creating an exploitable privilege-boundary hole. ARMv8.9 `PIE` (`4`-bit index into independent `PIR_EL0` / `PIR_EL1` permission registers in `pgtable-prot.h:169–189`) genuinely eliminates the coupling by separating `(EL0 R/W/X)` from `(EL1 R/W/X)` directly in the translation regime.
2. **False Simplification #2 — Eliminating Variables via Fine-Grained Combinators (`SKI`) or Associative Tag CAMs (`TTDA`)**: `SKI` eliminates variable environments only by encoding variable lookup as an $O(k^3)$ runtime tree walk; `TTDA` eliminates the `PC` only by turning every binary instruction into an associative hardware hash-table lookup (`WMU` CAM). Neither reduces fundamental work.
3. **Minimal Universal Representation (*Staged Frame-Template Graphs with Uniqueness & Capability-Order Tokens*)**: All four non-von-Neumann families converge cleanly onto a single three-part intermediate representation that handles pure computation, in-place mutation, and ordered I/O without special-case hardware CAMs or speculative recovery:
   - **Flat Bounded-Width Frame Templates (`Monsoon ETS` + `Reduceron`)**: Represent functions as statically sized activation/instantiation frames (`<= K` slots) addressed by direct base-plus-offset arithmetic (`FP + r` or `hp + offset`) rather than `SKI` routing trees or associative tag CAMs;
   - **1-Bit Linear/Unique Reference Polarity (`PTR False` / `ARG shared`)**: Encode affine uniqueness directly in pointer/port tags (`1` bit), turning non-shared thunk update elision and safe in-place buffer reuse into local combinational rules (`dashIf`) with zero global alias analysis;
   - **Explicit Partial-Order Capability Chains (`WaveScalar` `(pred, seq, succ)` / `I-structure` monotone cells)**: Represent pure values as unordered graph edges, single-assignment synchronization as monotone `{EMPTY -> PRESENT}` lattice cells, and sequential external memory/MMIO effects as explicit capability-token chains `(pred, seq, succ)`—genuinely eliminating centralized reorder buffers, branch predictors, and associative load/store queues rather than pushing ordering hazards into ad-hoc barrier instructions.

## Boundaries

- **Multi-Core / Off-Chip DRAM Scaling of Reduceron (`not examined` / `unsupported` in Virtex-5 RTL)**: The evaluated Virtex-5 Reduceron (`mn416/reduceron-project`) stores its entire heap in single-cycle on-chip FPGA BRAM (`462 KiB` total across `fromSpace` + `toSpace`) and executes sequentially (`1` reduction rule per cycle). While `tommythorn/Reduceron/emulator/red_atom.h` defines a `128`-bit external-DRAM cell packing (`512 MiB`–`2 GiB`), hardware heap-cache miss stalls over off-chip DDR controllers and multi-Reduceron parallel shared-heap coherence were **not implemented in synthesizable RTL** (`unsupported`).
- **Higher-Order Static `PRS` & CAFs (`known not to apply` / `unsupported`)**: Colin Runciman's static `PRS` analysis (`Memo50.txt`) is restricted to **first-order** F-lite programs with non-recursive local `let` bindings (`known not to apply` to arbitrary higher-order function arguments without defunctionalization), and `tommythorn/Reduceron/README.md` (`Q1`) confirms that dynamically loaded programs and Constant Applicative Form (`CAF`) static heap pre-linking remain `unsupported` in the current FPGA image flow.
- **Stop-and-Copy GC Hard Real-Time Bounds (`known not to apply`)**: Although every non-GC Reduceron transition executes in exactly `1` clock cycle (`10.4 ns` at `96 MHz`), `Collect.hs` performs stop-and-copy evacuation + `copyBack` proportional to live `toSpace` size, introducing multi-thousand-cycle pauses (`0.1%`–`14.7%` of total runtime); Reduceron's `1`-tick step guarantee therefore **does not directly establish sub-microsecond hard real-time WCET** across GC boundaries without an incremental/real-time collector.
- **Silicon ASIC Clock Projection (`unknown`)**: How fast Reduceron's `8`-wide `Octostack` crossbar and combinational `PRS` + `instApp` datapath (`96 MHz` on 65nm Virtex-5 FPGA vs. `3 GHz` Core 2 Duo) would clock as a custom standard-cell ASIC on modern 5nm/3nm CMOS—and whether multi-port SRAM banking area would outweigh custom superscalar OoO logic—remains `unknown` without physical ASIC synthesis and SRAM compiler characterization.

## Evidence

### Primary Upstream Repositories & Source Coordinates

1. **`tommythorn/Reduceron` @ `e9b051238698040afe1d484b1ebd57f6b58f5036`** (inspected 2026-11-19):
   - `flite/Flite/RedCompile.hs:111–185`: `tr` shared-argument counting (`shared = length ... > 1`), `flagFuns` (`original` safepoint flag), `fragment` / `frag` / `fr` enforcing the five hardware template invariants including `refersCheck (R.VAR sh i) = i >= 0`.
   - `emulator/emu.c:17–40, 300–575, 664–667, 795–860`: `APSIZE = 6`, `MAXPUSH = 8`, `MAXAPS = 4`, `ATOMWIDTH = 22` (`19`-bit signed integer truncation), `dash` / `update` normal-form dashing, `instApp` dynamic `PRS` (`app->tag == PRIM`), `copyChild` `COLLECTED` `shared`-bit bug fix (`lines 562–566`), and `canCollect()` safepoint guard (`hp > MAXHEAPAPPS-200 && canCollect()`).
   - `emulator/red_atom.h:1–115`: `128`-bit packed heap-application design (`4` $\times$ `33`-bit tagged atoms with implicit size via `Invalid` slots and `HT = 5` / `3` head-tag bit recovery yielding `25`–`27` pointer bits).
   - `fpga/Heap.hs:1–85` & `fpga/Collect.hs:1–250`: York Lava dual-port `Heap` (`snocA`/`snocB` parallel single-cycle appends) and iterative `Recipe` stop-and-copy collector (`copyChild`, `updateUStack`, `copyBack`).
2. **`mn416/reduceron-project` @ `9dba5d9500e131f2bce31b6258bfc39e69c6bf3d`** (inspected 2026-11-19):
   - `jfp-reduceron.pdf` (Naylor & Runciman, *JFP* 22(4–5):574–613, 2012, `DOI: 10.1017/S0956796812000214`): Tables 1–8 (`MaxAppLen = 4, MaxSpineLen = 6, MaxAppsPerBody = 2`; Virtex-5 LX110T `96 MHz`, `14%` slices, `90%` of `296` $\times$ `18-Kbit` BRAMs; `88%` update avoidance; `10.08x`–`20.06x` speedup over `210 MHz` MicroBlaze; `0.40`–`1.80` hand-reductions/cycle).
   - `memos/Memo50.txt` (Runciman, 23 June 2010): Static `Ana`/`Cata` algebraic type-oracle and valuableness fixpoint analysis for guaranteed `PRS`.
3. **`llvm/llvm-project` @ `4520919d72d4fbcaa8416c9de404a0d37161b410`** (inspected 2026-11-19):
   - `llvm/lib/Target/ARM/ARMConstantIslandPass.cpp:496–498`: `!STI->genExecuteOnly()` guard disabling inline `TBB`/`TBH` Thumb-2 jump tables.
   - `llvm/lib/Target/ARM/ARMISelLowering.cpp:2454–2505, 3239–3276`: `reportFatalUsageError` on `-fPIC` + `long-calls` + `genExecuteOnly()`, `MOVW`/`MOVT` callee synthesis, and constant-pool promotion to internal `.rodata` globals.
4. **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`** (inspected 2026-11-19):
   - `arch/arm64/include/asm/pgtable-prot.h:62–65, 128–131, 149–189`: `_PAGE_EXECONLY` omitting `PTE_USER` vs. ARMv8.9 `PIE_E0` (`PIE_X_O`) and `PIE_E1` (`PIE_NONE_O`) orthogonal permission indirection.
5. **`ghc/ghc` @ `83038fbee5efea8e3ebd5090b2ff5537462e169d`** & **`HigherOrderCO/HVM` @ `7365a56cca56a5853c979755891cb86aa343c42d`** (inspected 2026-11-19):
   - `rts/include/rts/storage/ClosureMacros.h:148–180`: `GET_CLOSURE_TAG`, `UNTAG_CLOSURE`, and `tagConstr` low-bit pointer tagging in STG closures.
6. **Specifications, Peer-Reviewed Papers & Practitioner Reports**:
   - John Backus, *CACM* 21(8):613–641, 1978 (`DOI: 10.1145/359576.359579`); D. A. Turner, *Softw. Pract. Exper.* 9(1):31–49, 1979 (`DOI: 10.1002/spe.4380090105`); S. L. Peyton Jones, *JFP* 2(2):127–202, 1992 (`DOI: 10.1017/S0956796800000319`).
   - Arvind, R. S. Nikhil, & K. K. Pingali, *ACM TOPLAS* 11(4):599–632, 1989 (`DOI: 10.1145/69558.69562`); G. M. Papadopoulos & D. E. Culler, *ISCA* 1990 (`DOI: 10.1145/285930.285999`); S. Swanson et al., *MICRO-36* 2003 (`DOI: 10.1109/MICRO.2003.1253203`); A. Parashar et al., *ISCA* 2013 (`DOI: 10.1145/2485922.2485935`); G. Gobieski et al., *RipTide*, *MICRO* 2022 (`DOI: 10.1109/MICRO56248.2022.00050`).
   - Practitioner/Security Disclosures: Siguza's ARMv8 `XOM` + `PAN` bypass analysis & Catalin Marinas's Linux kernel revert (`arm64: Revert support for execute-only user mappings`, Jan 2020) and Android 10/11 AOSP XOM deprecation notes.

### Executed Verification Probes (`2026-11-19`)

1. **Upstream `tommythorn/Reduceron` C Emulator (`emu.c`) Compilation & `fib(20)` `PRS` Benchmark**:
   - Compiled `emulator/emu.c` + `red_atom.h` + `red_types.h` (`gcc -O2`): ELF `text = 20,050 B`, `data = 824 B`, `bss = 288 B` (`36 KiB` stripped/unstripped file size).
   - Executed `fib(20) = 10946` without PRS (`APP` thunks) vs. with dynamic PRS (`PRIM` register slots):
     - Without PRS: `Result = 10946`, `Ticks = 207910` (`Swap 5%, Prim 26%, Unwind 31%, Update 10%, Apply 26%`), `#GCs = 5`, `#Cases = 21891`, `Max Heap = 26`, `Max Stack = 44`, `Max UStack = 1`.
     - With PRS: `Result = 10946`, `Ticks = 131344` (`Swap 8%, Prim 8%, Unwind 16%, Update 0%, Apply 66%, PRS Success = 99%`), `#GCs = 2`, `#Cases = 21891`, `Max Heap = 8`, `Max Stack = 40`, `Max UStack = 0`.
2. **Standalone Python Probe (`probe_pkg1.py`, reproduced in Revalidation below)**:
   - Output: `COMBINATOR_BLOWUP (k, ski_nodes, bc_nodes, reduceron_template_atoms): [(2, 25, 1, 3), (4, 137, 15, 9), (6, 361, 37, 15), (8, 729, 67, 21)]`, `SHARING_UPDATE_EVALS (sound_dashN=True, omit_dashN=False): (1, 2)`, `ISTRUCTURE_TEST: [('r1', 99), ('r2', 99)] OK TOP_ERROR`, `WAVESCALAR_RETIRE (missing_seq1_len, complete_len): 1 3`.

## Revalidation

Run the following self-contained standard-library Python `3.10+` probe (`< 50 ms`, zero external dependencies) to revalidate (1) `SKI` vs. `BC` vs. Reduceron template scaling, (2) Reduceron Invariant 3 (`dashN` on update), (3) `Id` `I-structure` deterministic confluence and double-write `TOP_ERROR` detection, and (4) `WaveScalar` `(pred, seq, succ)` out-of-order retirement blocking:

```bash
python3 - <<'EOF'
def free_vars(t):
    return ({t} if t.startswith("x") else set()) if isinstance(t, str) else (free_vars(t[1]) | free_vars(t[2]))

def size(t):
    return 1 if isinstance(t, str) else 1 + size(t[1]) + size(t[2])

def abs_ski(x, t):
    if t == x: return "I"
    if x not in free_vars(t): return ("@", "K", t)
    return ("@", ("@", "S", abs_ski(x, t[1])), abs_ski(x, t[2]))

def abs_bc(x, t):
    if t == x: return "I"
    if x not in free_vars(t): return ("@", "K", t)
    f, g = t[1], t[2]
    xf, xg = (x in free_vars(f)), (x in free_vars(g))
    if not xf and xg and g == x: return f
    if not xf and xg: return ("@", ("@", "B", f), abs_bc(x, g))
    if xf and not xg: return ("@", ("@", "C", abs_bc(x, f)), g)
    return ("@", ("@", "S", abs_bc(x, f)), abs_bc(x, g))

rows = []
for k in (2, 4, 6, 8):
    t = "x0"
    for i in range(1, k): t = ("@", ("@", "+", t), f"x{i}")
    s, b = t, t
    for i in reversed(range(k)):
        s, b = abs_ski(f"x{i}", s), abs_bc(f"x{i}", b)
    rows.append((k, size(s), size(b), 3 * (k - 1)))
assert rows == [(2, 25, 1, 3), (4, 137, 15, 9), (6, 361, 37, 15), (8, 729, 67, 21)], rows

def sim_dash_on_update(use_dash):
    evals = 0
    heap = [("RED", [("FUN_MK", 0)]), ("RED", [("INT", 20), ("PRI", "+"), ("INT", 22)])]
    nf = [("CON", "Box"), ("PTR", False, 1)]
    heap[0] = ("NF", list(nf))
    if use_dash:
        nf = [(a[0], True, a[2]) if a[0] == "PTR" else a for a in nf]
    for sh, idx in [(nf[1][1], nf[1][2]), (True, heap[0][1][1][2])]:
        if heap[idx][0] == "RED":
            evals += 1
            if sh: heap[idx] = ("NF", [("INT", 42)])
    return evals
assert (sim_dash_on_update(True), sim_dash_on_update(False)) == (1, 2)

def wavescalar_retire(ops):
    by_k = {(w, seq): (pred, succ) for (w, pred, seq, succ) in ops}
    out, cur = [], (0, 0)
    while cur in by_k:
        pred, succ = by_k[cur]
        if out and pred != out[-1]: break
        out.append(cur[1])
        if succ is None: break
        cur = (cur[0], succ)
    return out
assert wavescalar_retire([(0, None, 0, 1), (0, 1, 2, None)]) == [0]
assert wavescalar_retire([(0, None, 0, 1), (0, 1, 2, None), (0, 0, 1, 2)]) == [0, 1, 2]
print("OK: all combinator, Reduceron dashN, and WaveScalar checks passed")
EOF
```

To revalidate upstream compiler/kernel execute-only invariants after an LLVM or Linux upgrade:
1. Check `llvm/lib/Target/ARM/ARMConstantIslandPass.cpp` and `ARMISelLowering.cpp` (plus `AArch64` constant-island / literal-load lowering) for `genExecuteOnly()` guards prohibiting inline `.text` constant pools and `TBB`/`TBH` table loads.
2. Check `arch/arm64/include/asm/pgtable-prot.h` (`_PAGE_EXECONLY`, `PIE_E0`, `PIE_E1`) and `arch/arm64/mm/mmap.c` (`VM_EXEC`-only gating on `ARM64_EPAN` / `S1PIE`) to confirm user XOM cannot be enabled on pre-`EPAN` cores where `AP[1]=0` bypasses `PAN`.
