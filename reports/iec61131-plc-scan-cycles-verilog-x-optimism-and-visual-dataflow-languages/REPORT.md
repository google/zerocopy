# Cyclic Scan Semantics, 4-State RTL Event Scheduling, GPU SIMT Uniformity, and Spatial/Latent Visual Dataflow Languages

## Summary

Reactive hardware, cyber-physical control, SIMT graphics, and visual dataflow languages depart sharply from sequential imperative execution models by coupling computation to cyclic I/O latches, stratified zero-time delta-cycle queues, lockstep SIMD/SIMT reconvergence invariants, and geometric or chronological graph topology. Across four primary domains verified from standards, compiler implementations, and peer-reviewed formalizations:

1. **IEC 61131-3 Industrial PLCs (`MATIEC`, `OpenPLC_v3`, `PLCverif`, `K-ST`):** Industrial Programmable Logic Controllers execute an infinite, watchdog-bounded **Input-Latch (`%I`) $\to$ Logic-Scan (`%M`, `%Q`) $\to$ Output-Flush (`%Q`)** loop (`OpenPLC_v3` `main.cpp:160-237`), carrying persistent per-instance memory in stateful `FUNCTION_BLOCK` records (`R_TRIG`, `TON` in `MATIEC` `lib/edge_detection.txt` and `lib/timer.txt`). While this scan model makes single-task Structured Text (`ST`) deterministic per cycle, underspecified evaluation order in graphical Ladder Diagrams (`LD`), Sequential Function Charts (`SFC` simultaneous divergence/convergence in `MATIEC` `generate_c_sfc.cc:969-992`), and asynchronous I/O update tasks causes silent semantic divergence across CODESYS, Siemens STEP 7/TIA Portal, and Rockwell Logix runtimes—a gap formally audited by CERN's `PLCverif` and the K-framework `K-ST` semantics (which uncovered 5 compiler bugs and 9 functional defects in OpenPLC).
2. **Verilog / SystemVerilog RTL vs. Synthesis & FIRRTL/CIRCT (`IEEE Std 1800`, `Verilator`, `Yosys`, `FIRRTL`, `CIRCT`):** SystemVerilog's 4-state `{0, 1, X, Z}` logic exhibits **X-optimism**: `if (1'bX)` deterministically executes the `else` branch in simulation (masking uninitialized pre-reset registers), whereas gate synthesis (`Yosys` `opt_expr.cc:245-274, 607-623`) exploits `State::Sx` as don't-care optimization freedom (`x & a -> 0` or `a`, `x ^ a -> 0`) and 2-state simulators (`Verilator` `V3Unknown.cpp:347-405`) collapse `X` to `0`, `1`, or random values. Concurrently, IEEE 1800 Section 4.4's **17-region stratified event scheduler** resolves zero-time delta cycles across `Active -> Inactive (#0) -> NBA (<=) -> Observed -> Reactive -> Postponed`, causing nondeterministic blocking (`=`) races between parallel `always @(posedge clk)` blocks that disappear under non-blocking (`<=`) assignments. **FIRRTL / CIRCT** (`firrtl-spec` `spec.md:3990-3992`, `ExpandWhens.cpp`) eliminates X-optimism by defining RTL strictly over 2-state boolean logic with deterministic last-connect mux lowering and static rejection of combinational loops.
3. **GPU SIMT Control-Flow Uniformity (`W3C WGSL`, `Dawn/Tint`, `TinyWGSL`, `GraphicsFuzz`):** GPU shaders execute threads in lockstep warps/subgroups and $2\times 2$ pixel quads, where derivative operations (`dpdx`/`dpdy`/`textureSample`) and workgroup barriers (`workgroupBarrier()`) trigger undefined behavior or full-GPU hangs when reached in divergent control flow. Whereas GLSL/HLSL/SPIR-V leave barrier divergence as UB (exposing vendor miscompilations found by `GraphicsFuzz`, OOPSLA 2017), **WGSL** mandates a compile-time directed implication-graph **Uniformity Analysis** (`wgsl/index.bs:12585-12661`, implemented in Chromium `Tint` `uniformity.cc`), checking reachability from `RequiredToBeUniform` to `MayBeNonUniform`. Formalizing this analysis in **TinyWGSL** (Lee-Jones, Wickerson, & Donaldson, PLDI 2026 DOI `10.1145/3808331`) exposed a **soundness bug** (missing `CFend -> V` edge on `continuing { break if (e); }`, now fixed in `wgsl/index.bs:13250-13258`) and three precision bugs, plus Alloy-generated differential bugs in `Tint`.
4. **2D Spatial Patch-Cord & Latent-Pin Visual Languages (`Pure Data`, `Max/MSP`, `LabVIEW G`, `Unreal Blueprints`):** Visual graph languages hide non-obvious scheduling rules outside the rendered graph topology. **Pure Data** (`src/m_obj.c:575-702`, `src/x_arithmetic.c:47-72`) uses hot-left/cold-right inlets and dispatches single-outlet fan-out strictly in **invisible wire-creation order** (tail-appended linked list `o->o_connections`), whereas **Max/MSP** dispatches fan-out by **2D canvas pixel coordinates** (right-to-left X, bottom-to-top Y); inserting an explicit `trigger` (`t b f`, `src/x_connective.c:1084`) is required to make execution order invariant across edits and engines. **LabVIEW G** combines strict all-inputs-ready token firing with default **non-reentrant SubVI single-dataspace serialization** (implicit mutex + persistent shift-register state), while **Unreal Blueprints** combines imperative execution pins with multi-frame **Latent Nodes** (`FLatentActionManager`, where `Delay` silently drops re-entrant triggers while pending, `RetriggerableDelay` resets the timer, and concurrent execution paths share Blueprint instance state).

## Applicability

This report characterizes four reactive, hardware, parallel, and visual execution domains whose non-standard scheduling semantics create high-severity verification, portability, and synthesis-mismatch hazards:

| Domain | Primary Subjects Examined | Relationship Among Subjects | Scope of Claims |
| :--- | :--- | :--- | :--- |
| **Industrial PLC scan cycles** | IEC 61131-3 Ed. 3.0 (2013); `beremiz/matiec@c316fe57`; `thiagoralves/OpenPLC_v3@b5d41356`; `K-ST` (`10.1109/TSE.2023.3315292`, `runtimeverification/k@4a46d123`); CERN `PLCverif` (`10.18429/JACoW-ICALEPCS2021-MOPV042`) | Normative IEC 61131-3 model compared against open-source compiler/runtime (`MATIEC`/`OpenPLC_v3`) and formal verification semantics (`PLCverif`, `K-ST`), contrasted with commercial vendor documentation | Applies to single-task and multi-task cyclic PLC execution for ST, LD, and SFC; vendor comparisons (CODESYS, Siemens, Rockwell) derive from documented runtime architectures and `K-ST`/`PLCverif` literature rather than closed-source binary execution. |
| **RTL 4-state vs. 2-state scheduling** | IEEE Std 1800-2017 / 2023 (Sections 4.4, 12.4); `verilator/verilator@f84382c2`; `YosysHQ/yosys@e4a169b8`; `chipsalliance/firrtl-spec@0bbb9d4b`; `llvm/circt@203f159c` | Normative IEEE 1800 4-state stratified scheduler compared against 2-state simulation (`Verilator`), don't-care synthesis (`Yosys`), and 2-state deterministic IR (`FIRRTL`/`CIRCT`) | Applies to synthesizable SystemVerilog RTL, Verilator's `V3Sched`/`V3Unknown` passes, Yosys `opt_expr` (with default `!config.keepdc`), and FIRRTL v4.0.0 semantics. Analog AMS (`Verilog-AMS`) and full UVM testbench DPI interactions are out of scope. |
| **GPU SIMT uniformity** | `gpuweb/gpuweb@d178d914` (`wgsl/index.bs`); `google/dawn@0a5ab784` (`uniformity.cc`); `TinyWGSL` (PLDI 2026 `10.1145/3808331`); `google/graphicsfuzz@aa32d4cb` (OOPSLA 2017 `10.1145/3133917`) | Normative WGSL spec + Chromium Tint implementation analyzed through TinyWGSL's formal operational semantics and contrasted with UB-based GLSL/SPIR-V driver fuzzing (`GraphicsFuzz`) | Applies to WGSL compute and fragment shader uniformity analysis (including `subgroup_uniformity` extensions in `Tint` and `wgsl/index.bs`). Note that `gpuweb@d178d914` already incorporates the `break if` fix reported in `TinyWGSL` Section 5. |
| **Visual dataflow & latent graphs** | `pure-data/pure-data@5182c4f9` (`src/m_obj.c`, `src/x_arithmetic.c`, `src/x_connective.c`); Cycling '74 Max/MSP docs; NI LabVIEW G docs; Epic Unreal Engine Blueprints (`FLatentActionManager`) docs | Direct C-source verification of Pure Data's scheduler contrasted against documented semantics of Max/MSP, LabVIEW G, and Unreal Blueprints | Pure Data findings are backed by direct C source inspection and execution probes; Max/MSP, LabVIEW G, and Unreal Blueprint behaviors reflect official upstream documentation and established runtime semantics (proprietary C++ internals were not directly inspected). |

## Findings

### 1. IEC 61131-3 Industrial PLC Languages: Cyclic Determinism and Vendor Evaluation Races

#### 1.1 The Atomic Scan-Cycle Execution Model (`Input-Latch -> Logic-Scan -> Output-Flush`)

`Basis: normative + source + execution`

Unlike event-driven software or continuous physical circuits, an IEC 61131-3 PLC runs a periodic, watchdog-monitored discrete-time control loop. Direct inspection of the OpenPLC v3 runtime (`thiagoralves/OpenPLC_v3@b5d41356`, `webserver/core/main.cpp:160-237`) shows the exact runtime realization of the canonical 3-stage scan cycle:

1. **Atomic Input Latch (`%I`, `main.cpp:182-203`):** `updateBuffersIn()` and `updateBuffersIn_MB()` snapshot physical digital/analog hardware pins and Modbus/EtherCAT slave registers into an in-memory **process input image table** under `pthread_mutex_lock(&bufferLock)`. Throughout the subsequent logic scan, all reads of `%I` observe this frozen snapshot, preventing torn reads if a physical sensor toggles mid-scan.
2. **Deterministic Logic Scan (`%M`, `%Q`, `main.cpp:205`):** `config_run__(__tick++)` executes compiled Program Organization Units (`POU`s generated by `MATIEC` from `ST`, `LD`, `FBD`, `IL`, or `SFC`), mutating internal memory (`%M`), persistent `FUNCTION_BLOCK` instance structs, and the in-memory **process output image table** (`%Q`).
3. **Atomic Output Flush (`%Q`) and Cycle-Deadline Pacing (`main.cpp:206-223`):** `updateBuffersOut_MB()` and `updateBuffersOut()` commit the final output image atomically to actuators after releasing `bufferLock`, followed by `sleep_until(&timer_start, common_ticktime__)` to align with the fixed scan period $T_{\text{scan}}$. In safety-certified industrial PLCs, exceeding the hardware **watchdog timer** ($T_{\text{cycle}} > T_{\text{watchdog}}$) immediately faults the CPU and forces all physical outputs into a fail-safe de-energized state.

#### 1.2 Persistent `FUNCTION_BLOCK` State Across Scans (`R_TRIG`, `TON`)

`Basis: normative + source + execution`

IEC 61131-3 strictly distinguishes stateless `FUNCTION`s from stateful `FUNCTION_BLOCK` (`FB`) instances whose `VAR` fields persist across scan cycles. In `beremiz/matiec@c316fe57`, `lib/edge_detection.txt:20-34`:

```iecst
FUNCTION_BLOCK R_TRIG
  VAR_INPUT  CLK: BOOL; END_VAR
  VAR_OUTPUT Q: BOOL;   END_VAR
  VAR M: BOOL;          END_VAR
  Q := CLK AND NOT M;
  M := CLK;
END_FUNCTION_BLOCK
```

Similarly, `TON` (On-Delay Timer, `beremiz/matiec`, `lib/timer.txt`) tracks elapsed time `ET` against preset `PT` across scans using the latched scan timestamp (`__CURRENT_TIME`), setting `Q := TRUE` only when `IN` remains continuously high for at least `PT`. Two subtle semantic hazards emerge directly from scan-cycle discretization:

- **Nyquist / Pulse-Width Aliasing:** Any physical sensor pulse shorter than $T_{\text{scan}}$ (or transitioning high and low between two `updateBuffersIn()` snapshots) is completely invisible to `R_TRIG`.
- **Conditional-Call Stale Memory Bug:** If an `R_TRIG` or `TON` instance is invoked inside an `IF cond THEN fb(...); END_IF;` branch and `cond` turns `FALSE` while `CLK`/`IN` is `TRUE`, its internal state `M` or timer start timestamp **freezes** at the last executed scan rather than updating, causing a missed edge or premature timeout many cycles later when `cond` becomes `TRUE` again.

#### 1.3 Graphical Ladder Diagram (`LD`) & `SFC` Vendor Divergence

`Basis: normative + source + documentation + execution`

While IEC 61131-3 Edition 3.0 standardizes syntax and core semantics, it leaves critical execution-order details implementation-defined across graphical languages and multi-task runtimes:

1. **Ladder Diagram (`LD`) Rung/Coil Order & Cross-Rung Propagation (Probe 2A):**
   - In standard top-to-bottom, left-to-right scanning, if Rung 1 assigns internal coil `%M0.0 := %I0.0` and Rung 2 assigns `%Q0.0 := %M0.0`, a rising input on scan $k$ propagates to `%Q0.0` on the **same** scan $k$ (`[False, True, True, False]`). If an editor, optimizer, or graphical layout tool reorders Rung 2 before Rung 1 (e.g., column-major vs. row-major network flattening or feedback-wire topological sorting), `%Q0.0` observes the **previous scan's** `%M0.0`, introducing a silent 1-scan delay (`[False, False, True, True]`) that can violate interlock timing specs!
   - **Vendor Runtime Split:**
     - **CODESYS / TwinCAT:** Enforces left-to-right, top-to-bottom network evaluation per POU with synchronous task I/O snapshots, though configurable execution-order modes (explicit dataflow order vs. top-to-bottom visual order in CFC/FBD) alter evaluation order.
     - **Siemens STEP 7 / TIA Portal:** Uses synchronous Process Image Input/Output (`PII`/`PIQ`) for OB1 cyclic scans, but also permits direct peripheral I/O reads/writes (`%IW:P` / `PIW`), which bypass the scan latch mid-cycle and reintroduce torn-read hazards.
     - **Rockwell Studio 5000 / Logix5000:** Runs **asynchronous I/O tasks** concurrently with the continuous/periodic logic task by default; reading a raw hardware input tag twice in the same rung or across two rungs can yield **two different values within a single scan** unless the engineer explicitly buffers inputs into local tags at the start of the scan (a classic portability trap when migrating from Siemens/IEC-synchronous designs!).
2. **Sequential Function Chart (`SFC`) Step/Transition/Action Races (`beremiz/matiec@c316fe57`, `stage4/generate_c/generate_c_sfc.cc:969-992`):**
   - `MATIEC` lowers each SFC network into four strictly sequential C code phases per scan:
     1. `// Transitions fire test` (`transitiontest_sg`, line 970) — evaluates all transition guards against current active steps.
     2. `// Transitions set and reset steps` (`stepsetreset_sg`, line 975) — deactivates source steps and activates target steps.
     3. `// Steps association` (`actionassociation_sg`, line 982) — binds step action qualifiers (`N`, `S`, `R`, `P`, `L`, `D`).
     4. `// Actions state evaluation` (`actionstateeval_sg`, line 989) — executes active actions.
   - Across commercial vendors, **simultaneous divergence/convergence** (`AND` branches) and **unsafe/unreachable multi-token loops** diverge sharply on: (a) whether two consecutive transitions can fire in a single scan (zero-time chain propagation vs. one-step-per-scan evolution), (b) whether a `P` (pulse) action executes when a step is activated and deactivated in the same scan, and (c) priority tie-breaking when two diverging `OR` selection branches have simultaneously true guards (left-to-right visual order vs. explicit priority numbers vs. mutual-exclusion error).

#### 1.4 Formal Verification and Reference Semantics (`PLCverif` and `K-ST`)

`Basis: documentation + normative`

- **CERN `PLCverif`** (Darvas et al., ICALEPCS 2015 DOI `10.18429/JACoW-ICALEPCS2015-WEPGF092`; Lopez-Miguel, Tournier, & Fernández Adiego, ICALEPCS 2021 DOI `10.18429/JACoW-ICALEPCS2021-MOPV042` / `arXiv:2203.17253v1`): Translates Siemens SCL/STL and IEC 61131-3 ST programs into an intermediate Control-Flow Automaton (CFA) explicitly wrapped in a cyclic **EoC (End-of-Cycle)** / **BoC (Beginning-of-Cycle)** harness that nondeterministically assigns fresh input values `%I` at BoC and asserts safety temporal properties (`AG`/`EF` or assertion invariants) strictly at EoC, discharging proofs via NuXmv, Theta, or CBMC. This BoC/EoC abstraction faithfully filters out transient mid-scan intermediate coil states.
- **`K-ST`** (Wang, Wang, Poskitt, Chen, Sun, & Cheng, *IEEE TSE 2023*, DOI `10.1109/TSE.2023.3315292` / `arXiv:2202.04076v2`, built in the K framework `runtimeverification/k@4a46d123`): Defines an executable rewriting semantics for IEC 61131-3 ST and validates it differentially across **509 real-world ST programs** harvested from GitHub against CODESYS, Omron CX-Programmer, and Mitsubishi GX Works2—identifying cross-vendor semantic discrepancies (integer overflow, `FOR`-loop bound re-evaluation, array/string boundary handling) and uncovering **5 compiler bugs and 9 functional defects** in OpenPLC (`MATIEC`).

---

### 2. Verilog / SystemVerilog 4-State `X-Optimism`, 17-Region Event Queue, and FIRRTL/CIRCT

#### 2.1 Four-State `{0, 1, X, Z}` `X-Optimism` vs. Synthesis Don't-Care Freedom

`Basis: normative + source + execution`

IEEE Std 1800 (SystemVerilog) models digital wires and variables over a 4-valued logic domain $\{0, 1, \mathsf{X}, \mathsf{Z}\}$, where $\mathsf{X}$ ambiguously conflates *uninitialized storage*, *bus contention*, and *synthesis don't-care*. This conflation creates **X-optimism**—a systematic soundness gap between RTL simulation and synthesized silicon:

1. **Simulation `if (1'bX)` Takes `else` Deterministically (IEEE 1800 Section 12.4, Probe 2B):**
   In `if (cond) out = a; else out = b;`, IEEE 1800 defines `cond` as true **if and only if** `cond` evaluates to a known non-zero value. When `cond === 1'bX` (e.g., an unreset control register at power-up), `cond` is **not true**, so RTL simulation deterministically executes the `else` branch (`out = b`) and silently **destroys** the `X` taint! Even if `a` and `b` disagree (`1` vs `0`), the simulator reports a clean known `0` instead of propagating `X`, masking missing-reset bugs until silicon bring-up or gate-level simulation. (Similarly, `case (sel)` treats `X` as failing to match `0` or `1`, falling silently into `default:`.)
2. **Synthesis Exploits `X` as Don't-Care Minimization (`YosysHQ/yosys@e4a169b8`, `passes/opt/opt_expr.cc:245-274, 607-623`):**
   In Yosys's expression optimizer (`opt_expr.cc`), unless `-keepdc` (`config.keepdc`) is explicitly set, `State::Sx` and `State::Sz` bits are aggressively replaced with whichever constant minimizes gate area:
   - Lines `247-250`: For `$and`, `State::Sx` and `State::Sz` are replaced by `State::S0`; for `$or`, they are replaced by `State::S1`.
   - Lines `611-620`: For 1-bit `$xor` / `$_XOR_`, if either operand is `State::Sx` or `State::Sz`, `opt_expr` replaces the entire gate with constant `State::S0` (`const_xor`), and for `$xnor` with constant `State::S1` (`const_xnor`)!
   Consequently, synthesized netlists choose an **arbitrary** concrete boolean realization for any `X`-driven cone, which need not match the simulator's `else`-branch choice.
3. **2-State Cycle-Accurate Simulation (`verilator/verilator@f84382c2`, `src/V3Unknown.cpp:347-405`):**
   Because Verilator compiles SystemVerilog directly into fast 2-state C++ (`uint32_t`/`uint64_t` bitvectors without separate X-masks), `V3Unknown::visit(AstConst*)` (`lines 347-365`) replaces every literal `X`/`Z` bit at compile time according to `--x-assign`: `0` (optimistic zero), `1`, or `unique` (a pseudo-random runtime constant initialized via `--x-initial unique`). While `--x-initial unique` exposes some uninitialized-register bugs by randomizing startup values across runs, Verilator cannot faithfully simulate 4-state `X`-propagation semantics (such as `===` identity checks against `1'bx` or runtime tri-state `Z` contention).

#### 2.2 IEEE Std 1800 Section 4.4: The 17-Region Stratified Event Scheduler and `=` vs. `<=` Races

`Basis: normative + source + execution`

Within a **single simulation timestamp $t$**, IEEE Std 1800-2017 / 1800-2023 (Section 4.4) partitions zero-time event processing into **17 ordered regions** grouped around an **Active region set** (RTL design) and a **Reactive region set** (testbench `program` blocks), with backward delta-cycle feedback loops:

| # | Region Name | Region Group | Scheduled Events & Execution Rules |
| :---: | :--- | :--- | :--- |
| 1 | **Preponed** | Sampling | Read-only snapshot of variables for SVA concurrent assertions and clocking-block inputs before any delta updates at time $t$. |
| 2 | **Pre-Active** | PLI/VPI | Read-only PLI/VPI callback hook prior to Active execution. |
| 3 | **Active** | Active set | Arbitrary-order execution of RTL blocking assignments (`=`), continuous `assign` statements, `$display`, primitives, and **RHS evaluation** of non-blocking assignments (`<=`). |
| 4 | **Inactive** | Active set | Explicit `#0` zero-delay events scheduled from Active (re-loops to Active once drained). |
| 5 | **Pre-NBA** | Active set | PLI/VPI callback hook immediately before NBA commits. |
| 6 | **NBA** | Active set | **LHS commits** of all non-blocking assignments (`<=`) queued during Active; value changes trigger new Active-region sensitivity events (delta-cycle loop back to Region 3). |
| 7 | **Post-NBA** | Active set | PLI/VPI callback hook after NBA commits. |
| 8 | **Pre-Observed** | Assertion | PLI/VPI callback hook before assertion evaluation. |
| 9 | **Observed** | Assertion | Evaluation of SVA property/sequence expressions using Preponed sampled values; pass/fail action blocks schedule into Reactive. |
| 10 | **Post-Observed** | Assertion | PLI/VPI callback hook after Observed. |
| 11 | **Reactive** | Reactive set | Execution of verification `program` blocks, assertion action blocks, and clocking drives (mirror of Active). |
| 12 | **Re-Inactive** | Reactive set | `#0` events from Reactive (loops back to Reactive). |
| 13 | **Pre-Re-NBA** | Reactive set | PLI/VPI callback hook before Re-NBA. |
| 14 | **Re-NBA** | Reactive set | LHS commits of `<=` from Reactive (can trigger delta cycles back to Active or Reactive). |
| 15 | **Post-Re-NBA** | Reactive set | PLI/VPI callback hook after Re-NBA. |
| 16 | **Pre-Postponed** | Finalizing | PLI/VPI callback hook before read-only end-of-slot monitoring. |
| 17 | **Postponed** | Finalizing | Read-only `$strobe` / `$monitor` execution; mutating any net/variable or scheduling earlier-region events at time $t$ is strictly illegal. |

**Canonical Blocking (`=`) vs. Non-Blocking (`<=`) Shift-Register Race (Probe 2B):**
Consider two concurrent sequential processes triggered on the same `posedge clk`:
- Process `P1`: `always @(posedge clk) a = d;` (or `a <= d;`)
- Process `P2`: `always @(posedge clk) b = a;` (or `b <= a;`)
Starting from `(a=0, b=0, d=1)`:
- **With blocking `=`:** Both `P1` and `P2` run in the **Active** region in an **unspecified, simulator-chosen order**. If `P1` runs before `P2`, `a` mutates immediately to `1` and `P2` reads the new value, yielding `(a=1, b=1)` (collapsing a 2-stage shift register into a 1-stage wire!). If `P2` runs before `P1`, `P2` reads the old `0`, yielding `(a=1, b=0)`. Both outcomes are legal under IEEE 1800, creating simulator-dependent nondeterminism that diverges from physical flip-flop hardware.
- **With non-blocking `<=`:** Both `P1` and `P2` evaluate their RHS expressions (`d=1`, `a=0`) during the **Active** region and enqueue deferred writes into the **NBA** region (Region 6). Regardless of whether Active executes `P1 -> P2` or `P2 -> P1`, the NBA region commits `(a=1, b=0)` identically.

In compiled 2-state simulation, Verilator (`verilator/verilator@f84382c2`, `src/V3Sched.cpp:17-36, 745`) collapses the 17 IEEE regions into a statically-ordered multi-loop schedule (`settle` $\to$ `ico` input comb $\to$ `act` active/clock-gen loop $\to$ `nba` non-blocking update loop executed by `VerilatedEvalLoop`), explicitly documenting at `V3Sched.cpp:22-26` that combinational cycles must be broken via hybrid logic and blocking-assigned generated clocks must be isolated into `act`.

#### 2.3 Clean 2-State Alternative: FIRRTL and CIRCT

`Basis: normative + source`

The **FIRRTL** intermediate representation (`chipsalliance/firrtl-spec@0bbb9d4b`, `spec.md`, FIRRTL v4.0.0) and its MLIR/LLVM compiler **CIRCT** (`llvm/circt@203f159c`) redesign RTL semantics to eliminate both X-optimism and procedural delta-cycle races by construction:

1. **Strict 2-State Boolean Semantics (`spec.md:3990-3992`):** Normatively states: *"FIRRTL is defined for 2-state boolean logic. The behavior of a generated circuit in a language, such as Verilog or VHDL, which have multi-state logic, is undefined in the presence of values which are not 2-state. A FIRRTL compiler need only respect the 2-state behavior of a circuit."*
2. **Deterministic Last-Connect Mux Lowering (`spec.md:1631-1648, 2296-2313`; CIRCT `ExpandWhens.cpp:44-62`):** Procedural `when (c) : connect w, b` blocks are statically lowered into pure combinational multiplexers under **Last Connect Semantics** (eliminating `=` vs `<=` procedural ordering ambiguity), while uninitialized signals must be explicitly marked via `invalidate w` (`spec.md:1719-1783`, tracked via `isInvalidValue` in `ExpandWhens.cpp:45-54`).
3. **Static Rejection of Combinational Loops (`spec.md:1785-1792`):** FIRRTL statically forbids combinational loops even if runtime mux selects or last-connect overwrites would mask them—preventing zero-time delta-cycle livelock at compile time.

---

### 3. GPU Shader SIMT Uniformity: WGSL Static Analysis, `TinyWGSL`, and `GraphicsFuzz`

#### 3.1 SIMT Lockstep Hazards: Quad Derivatives and Barrier Divergence

`Basis: normative + documentation`

Modern GPU hardware executes shader invocations in lockstep SIMD/SIMT groups (32-lane NVIDIA warps, 32/64-lane AMD wavefronts, or $2\times 2$ fragment pixel quads) sharing a single instruction fetch/program counter with an active-lane execution mask. Two classes of GPU operations break naive single-thread semantics whenever control flow diverges across lanes:

- **Implicit Quad Derivatives (`dpdx`, `dpdy`, `fwidth`, `textureSample`):** Fragment hardware computes screen-space partial derivatives by subtracting register values of horizontally/vertically adjacent lanes in a $2\times 2$ pixel quad. If one pixel takes an `if` branch and its neighbor lane is masked off (inactive or took `else`), the derivative reads stale or garbage register contents from the inactive lane.
- **Workgroup & Subgroup Barriers (`workgroupBarrier()`, `storageBarrier()`):** Hardware barrier instructions stall arriving lanes until *all* invocations in the workgroup/subgroup reach the same dynamic barrier instance. If threads diverge (`if (local_invocation_id.x == 0) { workgroupBarrier(); }`), waiting threads block forever—causing **barrier divergence**, which on many GPUs wedges the command queue and triggers OS-level GPU timeout detection and recovery (TDR).

In legacy shading APIs (GLSL, HLSL, raw SPIR-V), barrier divergence and non-uniform derivatives are **undefined behavior** with no static check, and subtle control-flow reconvergence heuristics vary across GPU vendors. **GraphicsFuzz** (`google/graphicsfuzz@aa32d4cb`, Donaldson, Evrard, Lascu, & Thomson, *OOPSLA 2017*, DOI `10.1145/3133917`) demonstrated via metamorphic semantics-preserving shader transformations (injecting opaque dead branches, live-code wrapping, and loop mutations) that commercial GPU shader compilers frequently miscompile divergent control flow, producing wrong pixels, crashes, or hangs even on well-defined shaders.

#### 3.2 W3C WGSL Graph-Based Static Uniformity Analysis and Chromium `Tint`

`Basis: normative + source`

Because WebGPU runs untrusted web shaders on client GPUs, W3C **WGSL** (`gpuweb/gpuweb@d178d914`, `wgsl/index.bs:12585-12661`) elevates control-flow uniformity into a **mandatory static compile-time rejection pass**, implemented in Chromium's `Tint` compiler (`google/dawn@0a5ab784`, `src/tint/lang/wgsl/resolver/uniformity.cc:73-115, 498, 583`).

For each function and uniformity scope (`kWorkgroup`/`draw`, and optionally `kSubgroup` under the `subgroup_uniformity` extension, `uniformity.cc:73-77`), the analyzer builds a directed **uniformity implication graph** $G = (V, E)$:

- **Special Sentinel Nodes (`wgsl/index.bs:12641-12661`):**
  - Sources: `RequiredToBeUniform.error` (mandatory collective ops: `workgroupBarrier`, `storageBarrier`, `textureBarrier`, `dpdx`/`dpdy`/`fwidth`, `textureSample`), plus diagnostic-severity variants `.warning` and `.info`.
  - Sink: `MayBeNonUniform` (non-uniform inputs such as `@builtin(local_invocation_id)`, `@builtin(global_invocation_id)`, writable `storage` buffer loads, atomic operations, or fragment stage interpolated inputs).
- **Program Nodes & Implication Edges (`wgsl/index.bs:12645-12659`):** Every control-flow point (`CF_start`, `CF_after`, `CF_return`), expression value, and local variable version is a node; a directed edge $u \to v$ encodes logical implication *"if $u$ must be uniform, then $v$ must be uniform"* (so `RequiredToBeUniform.error -> call_site` asserts the call must be uniform, and `lid -> MayBeNonUniform` asserts `lid` cannot be assumed uniform).
- **Acceptance Criterion (`uniformity.cc:498`, `Traverse`):** A shader passes uniformity analysis **if and only if** there is **no directed path** in $G$ from `RequiredToBeUniform.error` to `MayBeNonUniform`. Interprocedural calls are analyzed bottom-up in call-graph order (WGSL forbids recursion), summarizing each callee via `CallSiteTag`, `FunctionTag`, and per-parameter `ParameterTag` summaries (`uniformity.cc:79-95`).

#### 3.3 Formal Soundness & Precision Flaws Exposed by `TinyWGSL` (PLDI 2026)

`Basis: normative + source + execution`

In *"Uniformity Analysis in the WebGPU Shading Language"* (*PACMPL* Vol. 10, PLDI 2026, Article 253, DOI `10.1145/3808331`), Lee-Jones, Wickerson, and Donaldson gave the first independent operational semantics of barrier divergence for a core calculus (**TinyWGSL**), proved a cleaned-up reformulation sound, and exposed **four major defects** in the prior WGSL specification (all four accepted by the W3C GPUWeb Working Group):

1. **Soundness Bug — Unsound Acceptance of Non-Uniform `break if` (Section 5, Fig. 10a; Probe 2C):**
   Consider:
   ```wgsl
   fn main(lid: u32) {
     loop {
       workgroupBarrier();
       continuing { break if (lid == 0); }
     }
     workgroupBarrier();
   }
   ```
   Thread `lid == 0` breaks out of the loop and stalls at the post-loop `workgroupBarrier()`, while threads `lid != 0` continue into the next loop iteration and stall at the in-loop `workgroupBarrier()`—an immediate barrier divergence deadlock! Yet the pre-fix WGSL uniformity rules omitted the implication edge from control-flow uniformity *after* `break if (e)` (`CFend`) to the condition expression `e` (`V`), allowing the shader to pass with zero path from `RequiredToBeUniform.error` to `MayBeNonUniform` (reproduced in Probe 2C). Direct inspection of our pinned upstream specification (`gpuweb/gpuweb@d178d914`, `wgsl/index.bs:13250-13258`) confirms the accepted fix is now present verbatim:
   ```text
   break if e;   |   CFend   |   (CF, e) => V   |   CFend   |   CFend -> V
   Note: The edge from CFend to V captures the fact that when the condition value
   is non-uniform, then control flow resulting from this `break if` statement is
   also non-uniform.
   ```
2. **Precision Bug 1 — Overly Conservative Loop Statement Behavior (Fig. 10b):** The spec always unioned a loop's body behavior with its `continuing` block's behavior; when the loop body ended in an unconditional `return;`, the unreachable `continuing { break if (...); }` made post-loop code appear reachable, falsely rejecting unreachable non-uniform barriers after the loop.
3. **Precision Bug 2 — Unconditional Loop Back-Edges (Fig. 10c):** The spec unconditionally linked loop-head uniformity to end-of-body uniformity even when the loop could never iterate (e.g., an inner loop whose only exit is a non-uniform `return;`), falsely rejecting a barrier executed once on entry to the outer loop.
4. **Precision Bug 3 — Connecting Unreachable `continuing` Blocks (Fig. 10d):** Analyzing and wiring an unreachable `continuing` block containing a non-uniform barrier into the uniformity graph triggered spurious compile errors.

Additionally, mechanizing the analysis in Alloy and differentially testing SAT-generated control-flow graphs against Chromium `Tint` uncovered specification-implementation discrepancies and a `Tint` front-end bug (PLDI 2026, Section 6).

---

### 4. 2D Spatial Patch-Cord and Latent-Pin Visual Dataflow Languages

#### 4.1 Pure Data vs. Max/MSP: Invisible Creation-Order vs. Pixel-Coordinate Fan-Out

`Basis: source + documentation + execution`

Patcher-based multimedia dataflow languages (**Pure Data / Pd** and **Cycling '74 Max/MSP**) share an almost identical visual surface syntax—boxes connected by patch cords—and the **Hot/Cold Inlet Discipline**, yet diverge critically on fan-out execution order:

1. **Hot Leftmost Inlet vs. Cold Right Inlets (`pure-data/pure-data@5182c4f9`, `src/x_arithmetic.c:47-72`):**
   In `binop1_new` (`lines 47-53`), arithmetic boxes like `+` and `-` register their right operand via `floatinlet_new(&x->x_obj, &x->x_f2)`, which **silently overwrites `x->x_f2` without emitting any output**. Only messages arriving at the leftmost ("hot") inlet invoke `binop1_plus_float` (`lines 69-72`):
   ```c
   static void binop1_plus_float(t_binop *x, t_float f) {
       outlet_float(x->x_obj.ob_outlet, (x->x_f1 = f) + x->x_f2);
   }
   ```
   Therefore, any patch wiring a single value to both inlets of a binary operator (e.g., computing `x - x` or `x * x`) **must** deliver the message to the cold right inlet *before* the hot left inlet.
2. **Pure Data's Invisible Wire-Creation-Order Dispatch (`src/m_obj.c:575-702`):**
   Direct inspection of `pure-data/pure-data@5182c4f9` proves that Pd's message scheduler is **depth-first, stack-bounded** (`stackcount_add()` / `outlet_stackerror()`, `m_obj.c:578-583`) and traverses `x->o_connections` in **linked-list order** (`m_obj.c:607-608`):
   ```c
   for (oc = x->o_connections; oc; oc = oc->oc_next)
       pd_float(oc->oc_to, f);
   ```
   When a user draws a patch cord in the editor, `obj_connect` (`m_obj.c:668-702`) **appends the new `t_outconnect` to the tail of `o->o_connections`**:
   ```c
   /* append it to the end of the list */
   if ((oc2 = *ochead)) {
       while (oc2->oc_next)
           oc2 = oc2->oc_next;
       oc2->oc_next = oc;
   }
   ```
   **Consequence:** Two Pure Data patches that are **pixel-for-pixel visually identical** on screen execute in opposite orders if their patch cords were drawn in different chronological orders! Deleting and redrawing a single wire silently reverses the runtime evaluation order (computing `x - prev_x` instead of `x - x = 0`, demonstrated in Probe 2D).
3. **Max/MSP's Spatial Pixel-Coordinate Ordering (Documentation Contrast):**
   By contrast, Max/MSP sorts fan-out deliveries from a single outlet strictly by **2D geometric canvas coordinates**: **right-to-left by destination X-coordinate**, breaking horizontal ties **bottom-to-top by destination Y-coordinate** (depth-first per branch). While this makes visual appearance reflect order, merely **dragging a box a few pixels horizontally** for visual neatness silently flips program execution order!
4. **Canonical Order-Independent Fix (`trigger` / `t`, `src/x_connective.c:1034-1103`):**
   In both Pd and Max, deterministic patches never fan out directly from one outlet to order-dependent targets; instead they interpose a `trigger` object (`t f f` or `t b f`), whose `trigger_list` implementation (`src/x_connective.c:1084`) explicitly iterates outlets strictly from right to left (`for (i = (int)x->x_n, u = x->x_vec + i; u--, i--;)`), guaranteeing right-outlet (cold inlet) delivery before left-outlet (hot inlet) delivery regardless of wire creation history or canvas coordinates (verified in Probe 2D).

#### 4.2 LabVIEW G: Strict Token Firing vs. Non-Reentrant SubVI Serialization

`Basis: documentation`

National Instruments **LabVIEW G** eliminates fan-out ordering races at the dataflow level because every node follows **strict dataflow firing** (a node executes if and only if *all* of its input terminals have received tokens, with no hot/cold inlet asymmetry, and pure parallel branches have no guaranteed order unless serialized explicitly via error-cluster wires). However, LabVIEW introduces a distinct concurrency and hidden-state hazard through **VI Reentrancy**:

- **Default Non-Reentrant Execution:** By default, every SubVI is **non-reentrant**, meaning all call sites across parallel `While` loops share a **single allocated data space** (front-panel controls, indicators, and shift registers) protected by an **implicit internal semaphore**. Calling a non-reentrant SubVI from two parallel loops silently serializes execution (introducing head-of-line blocking and priority inversion in real-time targets) and couples state across callers—a behavior intentionally exploited for **Functional Global Variables (FGVs)** via uninitialized shift registers, but hazardous when unintended.
- **Preallocated vs. Shared Clone Reentrancy:** Enabling *Preallocated clone reentrant execution* allocates one private dataspace per static call site (preserving per-call-site shift-register state without contention), whereas *Shared clone reentrant execution* draws clones dynamically from a pool (breaking stateful shift registers across invocations because consecutive calls at one site may bind different pooled clones!).

#### 4.3 Unreal Engine Blueprints: Imperative Exec Pins, Pull-Evaluated Pure Nodes, and Multi-Frame Latent Re-Entrancy

`Basis: documentation`

Unreal Engine's **Blueprints** (compiled to `Kismet` VM bytecode) is **not** a pure dataflow graph; it fuses an imperative control-flow graph (**white `Exec` pins**) with demand-driven data wires:

1. **Multi-Evaluation of Pure Data Nodes:** Pure (green) Blueprint nodes lack `Exec` pins and are **not memoized** across distinct impure `Exec` consumers: wiring a single `RandomFloat` or expensive `LineTrace` pure node into two sequential `Exec` nodes re-executes the pure node twice, yielding **two different random values** for a wire that visually appears to carry one value.
2. **Latent Nodes (`Delay`, `RetriggerableDelay`, `MoveComponentTo`) and `FLatentActionManager`:**
   Latent nodes suspend a Blueprint's execution wire across multiple game frames without blocking the main game thread, registering an `FPendingLatentAction` keyed by `(CallbackTarget, UUID)` inside `FLatentActionManager` (ticked each frame via `FLatentActionManager::ProcessLatentActions`):
   - **Standard `Delay` Silent Drop:** If an event fires a `Delay` node whose `(CallbackTarget, UUID)` already has a pending action in `FLatentActionManager`, the new trigger is **silently ignored/dropped** until the original countdown expires.
   - **`RetriggerableDelay` Timer Reset:** Looks up the active `FPendingLatentAction` for that node UUID and resets its remaining countdown to full duration rather than spawning a second concurrent continuation.
   - **Shared-Frame / Actor-State Re-Entrancy:** Because Blueprint event-graph local/member variables live on the single `UObject`/`AActor` instance (unlike per-invocation stack frames in async coroutines), when a second event or loop iteration mutates Blueprint variables while a latent action is suspended, the resumed latent continuation observes the **mutated post-interleaving state** rather than the values captured before `Delay`.

---

### 5. Cross-Domain Architectural Trade-Off Matrix

`Basis: derived`

| Language / Runtime | Primary Execution Mechanism | Hidden Ordering / Value Hazard | Failure Manifestation | Canonical Mitigation / Formal Architecture |
| :--- | :--- | :--- | :--- | :--- |
| **IEC 61131-3 (`MATIEC` / `OpenPLC` / Vendors)** | Atomic `Input-Latch -> Scan -> Output-Flush` loop | Cross-rung order, conditional `FB` freeze, async I/O (Rockwell), SFC simultaneous transitions | 1-scan interlock lag, missed short pulses, vendor migration regressions | Explicit BoC input buffering, unconditional `FB` calls, BoC/EoC CFA model checking (`PLCverif`), `K-ST` differential oracles |
| **SystemVerilog (`IEEE 1800`, `Yosys`, `Verilator`)** | 4-state `{0,1,X,Z}` + 17-region stratified delta queue | `if (1'bX)` takes `else` (X-optimism); Yosys `Sx` don't-care folding; Active-region blocking `=` race | RTL sim passes while synthesized silicon fails; simulator-dependent shift-register collapse | Strict `<=` for sequential `always_ff`, `unique case`/X-assertions, or 2-state deterministic IR (`FIRRTL`/`CIRCT`) |
| **GPU Shaders (`WGSL`, `Tint`, `SPIR-V`)** | Lockstep SIMT warps & $2\times 2$ quads | Non-uniform `workgroupBarrier()` / `dpdx` / `break if` divergence | Full GPU hang / OS TDR reset or silent vendor miscompilation (`GraphicsFuzz`) | Mandatory static implication-graph uniformity analysis (`wgsl/index.bs`, `Tint`), mechanized operational soundness (`TinyWGSL` + Alloy) |
| **Pure Data (`m_obj.c`)** | Depth-first stack-bounded message graph; hot/cold inlets | Invisible wire-creation order (`o->o_connections` tail-append) | Visually identical patches yield opposite results (`x - prev_x` vs `0`) | Explicit right-to-left `trigger` (`t b f`, `x_connective.c:1084`) on all multi-target fan-outs |
| **Max/MSP** | Depth-first message graph; hot/cold inlets | 2D canvas pixel coordinates (right-to-left X, bottom-to-top Y) | Moving a box horizontally silently reverses computation order | Explicit `trigger` (`t`) objects decoupling semantics from layout |
| **LabVIEW G** | Strict all-inputs-ready token dataflow | Default non-reentrant SubVI shared dataspace & implicit mutex | Parallel loop serialization deadlock / shared-clone shift-register corruption | Explicit preallocated-clone reentrancy for stateful parallel SubVIs; error-cluster sequencing |
| **Unreal Blueprints (`Kismet`)** | Imperative `Exec` pins + pull data + `FLatentActionManager` | Unmemoized pure nodes; `Delay` silent trigger drop; shared instance state across frames | Double-evaluated random values; dropped events; post-delay state corruption | Cache pure outputs into variables; isolate async workflows into dedicated tasks/C++ state machines |

## Boundaries

- **IEC 61131-3 Edition 4.0 (2025) and Closed-Source Commercial PLC Internals (`not examined`):** Direct source-level inspection covered `beremiz/matiec@c316fe57` (targeting IEC 61131-3 Ed. 2/3) and `thiagoralves/OpenPLC_v3@b5d41356`. Proprietary compilers/runtimes for CODESYS, Siemens TIA Portal, and Rockwell Studio 5000 were not directly decompiled or executed; vendor divergence findings rely on published manuals and the peer-reviewed `K-ST` / `PLCverif` validation studies.
- **VHDL Delta-Cycle Semantics & Commercial SystemVerilog 4-State Simulators (`not examined`):** VHDL's two-phase signal/variable delta-cycle scheduler (which avoids Verilog's Active-region `=` vs `<=` race on signals by separating `:=` variables from `<=` signals) and commercial simulators (VCS, Xcelium, Questa) with proprietary X-propagation modes (`xprop` `tmerge`/`xmerge`) were not directly executed here.
- **WGSL Dynamic Errors and `subgroup_uniformity` Edge Cases (`unknown` / `not examined`):** As noted explicitly in `gpuweb/gpuweb@d178d914` (`wgsl/index.bs:12602-12604`), WGSL uniformity analysis explicitly assumes **dynamic errors** (such as out-of-bounds buffer traps or infinite loops) do not occur. Furthermore, `TinyWGSL` (PLDI 2026) focuses on compute-shader workgroup uniformity; full formal mechanization of the newer `subgroup_uniformity` multi-scope extension (`uniformity.cc:73-77`) and fragment-shader helper-invocation derivative semantics was not examined in detail.
- **Verilator 4-State X-Propagation (`unsupported`):** `verilator/verilator@f84382c2` (`src/V3Unknown.cpp`) is architecturally a 2-state simulator; faithful runtime 4-state `X`/`Z` propagation and `===` identity matching against runtime `X` values are unsupported by design.
- **Max/MSP, LabVIEW G, and Unreal Engine C++ Source Internals (`not examined`):** Unlike Pure Data (`pure-data/pure-data@5182c4f9`, inspected directly in C source), Max/MSP, LabVIEW G, and Unreal Engine's `FLatentActionManager.cpp` are closed-source or gated behind EULA repositories and were analyzed solely from official technical documentation rather than pinned source commits.
- **Generalizing TinyWGSL's Pre-Fix `break if` Bug to Current Chromium `Tint` (`known not to apply` at pinned HEAD):** Direct inspection of `gpuweb/gpuweb@d178d914` (`wgsl/index.bs:13250-13258`) confirms that the accepted `CFend -> V` rule fix for `break if` is already incorporated in the pinned WGSL specification revision; the unsound acceptance applies only to pre-fix WGSL revisions and unpatched older compilers predating the 2025/2026 spec update.

## Evidence

### Primary Repositories, Standards, and Peer-Reviewed Papers Inspected (Observed 2026-11-19)

1. **IEC 61131-3, MATIEC, OpenPLC, PLCverif, and K-ST:**
   - `thiagoralves/OpenPLC_v3`, commit `b5d41356dab4aeadca0dd7ca64ba542f870b595d`: `webserver/core/main.cpp:160-237` (`while(run_openplc)` executing `glueVars`, `updateBuffersIn`, `pthread_mutex_lock(&bufferLock)`, `updateBuffersIn_MB`, `config_run__(__tick++)`, `updateBuffersOut_MB`, `pthread_mutex_unlock`, `updateBuffersOut`, `sleep_until(&timer_start, common_ticktime__)`).
   - `beremiz/matiec`, commit `c316fe57e335381cbe91f61c7366857198580ac7`:
     - `lib/edge_detection.txt:20-34` (`R_TRIG` and `F_TRIG` stateful `VAR M: BOOL` edge detectors).
     - `lib/timer.txt` and `lib/standard_FB.txt:33-43` (standard IEC 61131-3 function blocks).
     - `stage4/generate_c/generate_c_sfc.cc:969-992` (4-phase SFC lowering: `transitiontest_sg`, `stepsetreset_sg`, `actionassociation_sg`, `actionstateeval_sg`).
   - `K-ST` paper: Kun Wang, Jingyi Wang, Christopher M. Poskitt, Xiangxiang Chen, Jun Sun, and Peng Cheng, *K-ST: A Formal Executable Semantics of the Structured Text Language for PLCs*, IEEE Transactions on Software Engineering (2023), DOI `10.1109/TSE.2023.3315292`, `arXiv:2202.04076v2` (built on K framework `runtimeverification/k@4a46d1231473b599c699160132fd6e76a5c46406`).
   - `PLCverif` papers: Dániel Darvas et al., *PLCverif: A Tool to Verify PLC Programs Based on Model Checking Techniques*, ICALEPCS 2015, DOI `10.18429/JACoW-ICALEPCS2015-WEPGF092`; Ignacio D. Lopez-Miguel, Jean-Charles Tournier, and Borja Fernández Adiego, *PLCverif: Status of a Formal Verification Tool for Programmable Logic Controller*, ICALEPCS 2021, DOI `10.18429/JACoW-ICALEPCS2021-MOPV042`, `arXiv:2203.17253v1`.
2. **SystemVerilog, Verilator, Yosys, FIRRTL, and CIRCT:**
   - IEEE Std 1800-2017 / IEEE Std 1800-2023, Section 4.4 (17-region stratified event scheduler) and Section 12.4 (`if-else` 4-state condition evaluation).
   - `verilator/verilator`, commit `f84382c2b0b113d4cc3e4b6fb5f749c6491866ba`:
     - `src/V3Sched.cpp:17-36, 745`: static partitioning of clocked/combinational logic into `settle`/`act`/`nba` loops (`VerilatedEvalLoop`).
     - `src/V3Unknown.cpp:347-405`: `visit(AstConst*)` lowering literal `X`/`Z` constants per `v3Global.opt.xAssign()` (`0`, `1`, `unique`).
   - `YosysHQ/yosys`, commit `e4a169b8fea4c1e7121518937854672efa41c658`:
     - `passes/opt/opt_expr.cc:245-274, 607-623`: replacing `State::Sx` / `State::Sz` with `State::S0` (`$and`, `$xor`) or `State::S1` (`$or`, `$xnor`) whenever `!config.keepdc`.
   - `chipsalliance/firrtl-spec`, commit `0bbb9d4b83e1d9c4f5b52d7e5527574ee4b11390`:
     - `spec.md:1631-1648, 1719-1792, 2296-2313, 3990-3992`: Last Connect Semantics, `invalidate`, static prohibition of combinational loops, and normative 2-state boolean logic definition.
   - `llvm/circt`, commit `203f159ce10d78940df4264327d5f3fc8b902112`:
     - `lib/Dialect/FIRRTL/Transforms/ExpandWhens.cpp:44-62`: `isInvalidValue` and `when` last-connect mux expansion.
3. **WGSL, Tint, TinyWGSL, and GraphicsFuzz:**
   - `gpuweb/gpuweb`, commit `d178d9145ab1652ec933e71a8c30e8f6470f00a3`:
     - `wgsl/index.bs:12585-12661`: Uniformity Analysis overview, sentinel nodes (`RequiredToBeUniform.{error,warning,info}`, `MayBeNonUniform`), implication-graph semantics, dynamic-error caveat (`lines 12602-12604`).
     - `wgsl/index.bs:13250-13258`: Updated `break if e;` rule emitting `CFend -> V`.
   - `google/dawn`, commit `0a5ab78416b90f79e8a7a0cf976dd24ab78b7ae6`:
     - `src/tint/lang/wgsl/resolver/uniformity.cc:73-115, 498, 583`: `UniformityScope` (`kAll`, `kWorkgroup`, `kSubgroup`), `CallSiteTag`, `FunctionTag`, `ParameterTag`, `struct Node`, `Traverse`, and `ProcessStatement`.
   - `TinyWGSL` paper: James Lee-Jones, John Wickerson, and Alastair F. Donaldson, *Uniformity Analysis in the WebGPU Shading Language*, Proc. ACM Program. Lang. 10, PLDI, Article 253 (June 2026), 25 pages, DOI `10.1145/3808331` (Sections 5 & 6, Fig. 10a–d).
   - `GraphicsFuzz`: `google/graphicsfuzz`, commit `aa32d4cb556647ddaaf2048815bd6bca07d1bdab`; Alastair F. Donaldson, Hugues Evrard, Andrei Lascu, and Paul Thomson, *Automated Testing of Graphics Shader Compilers*, Proc. ACM Program. Lang. 1, OOPSLA (2017), DOI `10.1145/3133917`.
4. **Pure Data & Visual Dataflow Documentation:**
   - `pure-data/pure-data`, commit `5182c4f90c4d79fc78e2c58048fe78f155631167`:
     - `src/m_obj.c:575-632`: `outlet_bang`, `outlet_float`, etc. iterating `o->o_connections` with `stackcount_add()` overflow check.
     - `src/m_obj.c:668-702`: `obj_connect` tail-appending connections in chronological creation order.
     - `src/x_arithmetic.c:47-72`: `binop1_new` (`floatinlet_new` cold right inlet) and `binop1_plus_float` (hot left inlet).
     - `src/x_connective.c:1034-1103`: `trigger_new` and `trigger_list` iterating outlets right-to-left (`for (i = (int)x->x_n, u = x->x_vec + i; u--, i--;)`).
   - Official documentation consulted: Cycling '74 Max/MSP order-of-operations documentation (right-to-left, bottom-to-top pixel-coordinate fan-out), National Instruments LabVIEW VI Reentrancy documentation (non-reentrant vs. preallocated/shared clones), Epic Games Unreal Engine `FLatentActionManager` / Blueprint Latent Actions documentation.

### Execution Probes (Observed 2026-11-19, Python 3.13.15, Linux x86_64)

Running a standalone Python verification script modeling IEC 61131-3 scan/rung ordering and `R_TRIG`, IEEE 1800 `if (1'bX)` X-optimism and Active/NBA shift-register races, the WGSL uniformity graph on TinyWGSL Fig. 10a (pre-fix vs. post-fix `break if`), and Pure Data creation-order vs. Max/MSP spatial-X fan-out produced the following verbatim witness outputs:

```text
=== PROBE 2A: IEC 61131-3 Scan Cycle & Cross-Rung Order Divergence ===
Inputs %I0.0          : [False, True, True, False]
Top-down (R1->R2) %Q0 : [False, True, True, False]
Reordered (R2->R1) %Q0: [False, False, True, True]
R_TRIG Q trace        : [False, True, False, False, True]

=== PROBE 2B: Verilog 4-State X-Optimism & Stratified Blocking (=) vs Non-Blocking (<=) ===
SV sim if(1'bX) 1 else 0 -> 0 (deterministically takes else branch!)
2-state silicon realizations for sel in {0,1}: {'0': '0', '1': '1'}
Blocking (=)     P1->P2: (1, 1), P2->P1: (1, 0)  (RACE: True)
Non-blocking (<=) P1->P2: (1, 0), P2->P1: (1, 0)  (RACE: False)

=== PROBE 2C: WGSL Uniformity Graph (TinyWGSL PLDI 2026 Fig. 10a break-if bug vs fix) ===
Pre-fix WGSL rule  -> accepted: True witness: None
Post-fix WGSL rule -> accepted: False witness: RequiredToBeUniform -> barrier_after_loop -> CF_after_loop -> expr_break_if_cond -> var_lid -> MayBeNonUniform

=== PROBE 2D: Pure Data Creation-Order vs Max/MSP Canvas-X Fan-Out & trigger Fix ===
Pd (wired left-first)  output: [10, 15] (computes v - prev_v!)
Max/MSP (spatial RTL)  output: [0, 0] (computes v - v = 0)
Pd with [trigger f f]  output: [0, 0] (order-independent: 0)
```

## Revalidation

To verify these invariants cheaply against newer upstream releases or local toolchains without redoing full multi-system research:

1. **OpenPLC / MATIEC Scan & SFC Lowering Check:** Diff `thiagoralves/OpenPLC_v3` `webserver/core/main.cpp` around `while(run_openplc)` (confirming atomic `updateBuffersIn` / `config_run__` / `updateBuffersOut` framing) and `beremiz/matiec` `stage4/generate_c/generate_c_sfc.cc` (`transitiontest_sg` $\to$ `stepsetreset_sg` $\to$ `actionassociation_sg` $\to$ `actionstateeval_sg`).
2. **Yosys `Sx` Folding & Verilator 2-State Check:** Diff `YosysHQ/yosys` `passes/opt/opt_expr.cc` around `config.keepdc` and `State::Sx`, and `verilator/verilator` `src/V3Unknown.cpp` (`visit(AstConst*)`). If `yosys` and `iverilog` are installed locally, synthesize `module m(input a, output y); assign y = a ^ 1'bx; endmodule` with `yosys -p "read_verilog m.v; opt_expr; dump"` to confirm `$xor` with `1'bx` folds directly to `1'b0` under default `!keepdc`, contrasting with `1'bx` in 4-state simulation.
3. **WGSL Uniformity Regression Check:** Inspect `gpuweb/gpuweb` `wgsl/index.bs` around `break if *e*;` (confirming `CFend -> V` remains mandatory) and compile the TinyWGSL Fig. 10a shader (`loop { workgroupBarrier(); continuing { break if (lid == 0u); } } workgroupBarrier();`) with `tint` (or `naga`) to verify static rejection with a uniformity error.
4. **Pure Data Connection-Order Check:** Diff `pure-data/pure-data` `src/m_obj.c` (`obj_connect` tail-append onto `o->o_connections` and `outlet_float` traversal) and `src/x_connective.c` (`trigger_list` right-to-left loop) to confirm Pd has not changed fan-out dispatch semantics from wire-creation order.
