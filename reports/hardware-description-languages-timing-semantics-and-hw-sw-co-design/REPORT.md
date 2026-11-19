# Hardware Description Languages, Timing Semantics, and HW–SW Co-Design

## Summary

Mainstream HDLs (IEEE Std 1800-2023 SystemVerilog) and C/C++ High-Level Synthesis (HLS) inherit discrete-event simulation and sequential pointer-memory semantics incompatible with deterministic synthesis and formal verification:

1. **SystemVerilog specifies an imperative event simulator, not a synchronous state machine.** IEEE Std 1800-2023 Clause 4 leaves `Active`-region process order unspecified, creating legal blocking (`=`) sequential races (Cummings, SNUG 2000). Clause 12.4 evaluates `if (1'bx)` as false (`X`-optimism) while Clause 11.4.11 ternary (`?:`) merges bitwise and synthesis treats `X` as don't-care freedom (Turpin, SNUG 2003). `Verismith` (FPGA 2020) exposed 11 unique bugs across Yosys, Vivado, and Icarus Verilog (0 in Quartus Prime), and untyped clock/reset wires omit CDC, RDC, latch, and combinational-loop checks.
2. **C-based HLS suffers opaque `II` cliffs and `#pragma` hazards.** Unconstrained pointers and unchecked pragmas cause throughput cliffs and miscompilations (Herklotz et al., FCCM 2021). Coq-verified `VeriCert` (OOPSLA 2021; PLDI 2024 hyperblock scheduling) proves backward simulation (`transf_c_program_correct`) to a deterministic two-edge Coq `Verilog` model outside IEEE 1800 races/`X` and rejects multi-TU inputs.
3. **Modern typed, rule-based, timeline, functional, and multi-level hardware systems enforce invariants statically:** `Kami`/`Kôika` prove ORAAT serializability (`OneRuleAtATime`) and circuit compilation (`compiler_correct`) via explicit schedules and 2-port EHRs; `Filament` discharges Presburger `@[G, G+1]` intervals and `II` bounds via SMT; `Dahlia` enforces time-sensitive affine SRAM banking across `---` barriers; `Spade` combines ADTs, `pipeline(N)` stages, and linear `inv &T` backward wires; `Calyx` splits structural cells from dynamic/static control; `CIRCT` lowers typed MLIR dialects (`hw`/`comb`/`seq`/`handshake`/`esi`/`arc`/`verif`) to upstream MLIR `smt` and BTOR2; `Lakeroad` maps FPGA LUT/DSP primitives via Rosette/`bitwuzla` sketches; `Hardcaml` checks comb loops and runtime UID clock domains; `Clash` enforces phantom `DomainConfiguration` types and explicit synchronizers; and `Silver Oak`/`Cava` proves OpenTitan AES-256 equivalence axiom-free in Coq.
4. **Clockless QDI synthesis** (`CHP -> HSE -> PRS` via Martin synthesis and `ACT`) replaces global clocks with dual-rail handshakes and C-element completion detection (modulo local isochronic forks).
5. **Executable witnesses** in `support/verify_hdl_semantics_and_timelines.py` verify the IEEE 1800 blocking race and `X`-divergence, Filament interval/II/wrap-around checks, Kôika's 16-cell EHR matrix and 96-state ORAAT equivalence, and Dahlia's affine banking rules.

## Applicability

Applies to synchronous RTL, HLS, and clockless QDI hardware toolchains as observed on `2026-11-19` across the 16 subjects pinned in `REPORT.json` (40-char SHAs and DOIs in `REPORT.json` and `## Evidence`):

- **Baseline semantics & reliability**: `IEEE Std 1800-2023`, `Cummings (2000)`, `Turpin (2003)`, `Verismith` (`ymherklotz/verismith`), and `Herklotz et al. (FCCM 2021)`.
- **HLS & split-control IRs**: `VeriCert` (`ymherklotz/vericert`, incorporating PLDI 2024 `GiblePar`/`DHTL` beyond OOPSLA 2021 `HTL`), `Dahlia` (`cucapra/dahlia`), and `Calyx` (`cucapra/calyx`).
- **Typed, rule-based & embedded HDLs**: `Kami` (`mit-plv/kami`), `Kôika` (`mit-plv/koika`), `Filament` (`cucapra/filament`), `Spade` (`arXiv:2304.03079`, TRETS 2026), `Hardcaml` (`janestreet/hardcaml`, v0.18 preview `Clock_domain.Runtime`), `Clash` (`clash-lang/clash-compiler`), and `Silver Oak`/`Cava` (`project-oak/silveroak`).
- **Multi-level compilers, tech-mapping, QDI & HW–SW touchpoints**: `LLVM CIRCT` (`llvm/circt`, after `smt` upstreaming to core MLIR), `Lakeroad` (`gussmith23/lakeroad`), `Martin (1990)` / `ACT` (`asyncvlsi/act`), `Bedrock2+Kami` (PLDI 2021), `CakeML/Silver` (PLDI 2019), and `Lutsig` (FormaliSE 2019, CPP 2021).

### Cross-References to Adjacent Corpus Reports

Pair this report with two adjacent packages without duplicating their Rust-specific tables:

- `anneal-cps-robotics-aerospace-eda-and-quantum-survey`: broader EDA verification tools (Yosys, SymbiYosys, ABC) and cross-domain assurance layering.
- `anneal-concurrency-weak-memory-kernels-and-storage-survey`: host-side weak memory models (RC11, LKMM, AArch64, RVWMO), Rust atomics/volatiles, and driver-side MMIO/DMA concurrency.

Source-symbol and theorem claims apply strictly to the pinned revisions in `REPORT.json`; broader generalizations to closed-source EDA suites rest on normative specifications and published empirical literature marked in `Basis:` lines.

## Findings

### 1. Semantic Breakdown of IEEE 1800-2023 SystemVerilog for Verification and Synthesis

Basis: normative (`IEEE Std 1800-2023`, Clauses 4, 11.4.11, 12.4) + documentation (`Cummings SNUG 2000`, `Turpin SNUG 2003`, `Verismith FPGA 2020`) + source (`ymherklotz/verismith`) + execution (`support/verify_hdl_semantics_and_timelines.py`)

#### 1.1 Stratified Event-Queue Scheduling and Blocking (`=`) vs. Nonblocking (`<=`) Races

Synchronous digital RTL is mathematically a deterministic Mealy/Moore transition relation $(S \times I \to S \times O)$ updating state simultaneously on clock edges. IEEE Std 1800-2023 Clause 4 instead defines semantics via a stratified discrete-event simulator queue partitioning each simulation time slot into ordered regions:

```text
Preponed  (read-only sampling: concurrent assertions, clocking block inputs)
  -> [ Active (blocking '=', RHS of '<=', continuous assigns; arbitrary process order)
       -> Inactive (#0 zero-delay events after Active drains)
       -> NBA (LHS commits of '<='; triggered sensitivities loop back to Active) ]*
  -> Observed (evaluate triggered SVA concurrent assertions)
  -> [ Reactive (program blocks, clocking outputs, assertion action blocks)
       -> Re-Inactive -> Re-NBA ]* (may re-trigger Active)
  -> Postponed (read-only $strobe/$monitor; no mutations)
```

Because IEEE 1800-2023 leaves execution order among concurrent processes in `Active` unspecified, mixing blocking assignments (`=`) across sequential clock-edge blocks creates a legal simulator race (Cummings, SNUG 2000):

```systemverilog
// RACY: concurrent posedge blocks sharing q1 via blocking '='
always @(posedge clk) q1 = d;   // B1
always @(posedge clk) q2 = q1;  // B2
```

Executing `(B1, B2)` writes `q1 = d` before `B2` reads `q1`, collapsing two flip-flops into one (`q2' = d`), whereas `(B2, B1)` yields the 2-stage shift (`q2' = q1`) matching synthesized flip-flops. Nonblocking `<=` separates RHS evaluation (`Active`) from LHS commit (`NBA`), making both orderings confluent. `verify_systemverilog_anomalies()` in `support/verify_hdl_semantics_and_timelines.py` mechanically confirms `order(B1,B2)=(1, 1) != order(B2,B1)=(1, 0)` for `=` versus `order(B1,B2)=order(B2,B1)=(1, 0)` for `<=`.

| Construct / Interaction | IEEE 1800-2023 Region Semantics | Synthesized Hardware Interpretation | Failure / Divergence Mode |
| :--- | :--- | :--- | :--- |
| Sequential `always_ff` with `=` | Writes LHS immediately in `Active` | Edge-triggered flip-flop | Legal simulator race across concurrent blocks; collapsed shift stages |
| Sequential `always_ff` with `<=` | Evaluates RHS in `Active`; commits LHS in `NBA` | Edge-triggered flip-flop | Order-invariant across blocks (mixing `=` and `<=` on one target remains hazardous) |
| `#0` delay in combinational logic | Defers event to `Inactive` | Ignored or rejected by synthesis | Delta-cycle artifacts absent from physical gates |
| Incomplete `if`/`case` in combinational block | Retains previous value across activations | Infers level-sensitive transparent latch | Unintended state, glitch capture, STA failure |
| Omitted signal in `always @(...)` list | Simulator skips re-evaluation on missing input | Synthesis builds full combinational cone | Stale simulated output vs. live hardware (`always_comb` mitigates legacy lists) |

#### 1.2 Four-Valued Logic (`0`/`1`/`X`/`Z`), `X`-Optimism, and Synthesis Divergence

SystemVerilog's 4-state bit domain `{0, 1, x, z}` conflates three incompatible concepts into `X`: (1) physical uninitialized/metastable unknown (requiring Kleene-pessimistic propagation across `{0, 1}`), (2) synthesis don't-care optimization freedom, and (3) multi-driver contention.

IEEE Std 1800-2023 Clause 12.4 evaluates an `if` condition as true **iff it has a nonzero known value** (at least one `1` and no `x`/`z` bits); otherwise it takes `else`. By contrast, Clause 11.4.11 evaluates ternary `sel ? a : b` on `sel === 1'bx` by merging both branches bitwise (yielding `X` when `a != b`). As Turpin (SNUG 2003) showed, structurally identical multiplexers therefore diverge under `sel = 1'bx, a = 1'b1, b = 1'b0`:

```systemverilog
always_comb if (sel) y_if = a; else y_if = b;  // IEEE §12.4: sel=X -> y_if = b (0)
assign y_tern = sel ? a : b;                   // IEEE §11.4.11: sel=X -> y_tern = X
```

| Semantic Model | `sel=X, a=1, b=0` | `sel=X, a=1, b=1` | Verification Impact |
| :--- | :---: | :---: | :--- |
| IEEE 1800-2023 §12.4 `if (sel)` | `0` (`else`) | `1` | **`X`-optimistic**: silently hides uninitialized control signals in RTL simulation |
| IEEE 1800-2023 §11.4.11 `sel ? a : b` | `X` | `1` | Propagates `X` when branches differ; agrees on `1` when branches match |
| Kleene 3-valued / `Xprop` `tmerge` | `X` | `1` | Sound abstraction over concrete binary realizations `sel in {0, 1}` |
| Synthesized netlist / silicon (`sel=1`) | `1` | `1` | **Pre- vs. post-synthesis divergence (`sim=0 != silicon=1`)** |

`support/verify_hdl_semantics_and_timelines.py` confirms `if(X,1,0)=0 != synth(sel=1)=1` while `ternary(X,1,0)=X` and `kleene=X`. Formal equivalence checkers frequently compound this blind spot by treating RTL `X` as a don't-care matching either `0` or `1` in the netlist.

#### 1.3 Empirical Synthesis Unreliability (`Verismith`, FPGA 2020)

Because IEEE 1800 defines no formal synthesizable subset, synthesis frontends and optimizers silently miscompile valid RTL. `Verismith` (Herklotz & Wickerson, FPGA 2020) differentially fuzzed Vivado, Quartus Prime, Yosys, and XST using deterministic loop-free Verilog. Inspection of `ymherklotz/verismith` `src/Verismith/Generate.hs` (L142–207) and `Fuzz.hs` (L197–287, L503–559) confirms that `randomOrdAssigns` topologically orders continuous assignments to rule out combinational loops and excludes `BinDiv`/`BinMod`/`BinCEq` before invoking `synthesis` and formal `equivalence` checks. Across its published campaign, `Verismith` reported **11 unique bugs** (6 fixed before publication):

- **Yosys**: 4 mis-synthesis bugs (functionally wrong netlist) + 1 crash bug (development revision).
- **Vivado**: 3 mis-synthesis bugs + 2 crash bugs.
- **Icarus Verilog**: 1 simulator bug caught during differential checking.
- **Quartus Prime**: 0 mis-synthesis or crash bugs observed in that campaign.

#### 1.4 Untyped Clock/Reset Wires, CDC Metastability, and Combinational Loops

Representing clocks and resets as undifferentiated 1-bit `logic` wires leaves three physical hazards unchecked by the language:

1. **CDC Metastability and Multi-Bit Tearing**: Sampling across asynchronous clocks violates setup/hold windows, causing analog metastability whose resolution time is only probabilistically bounded ($MTBF \propto e^{t_{\text{res}}/\tau}$). Parallel 2-FF synchronizers still suffer **multi-bit tearing** across skewed bits (e.g., binary `0111 -> 1000` sampled as `0000`), requiring Gray-coded async FIFOs or handshakes for multi-bit words.
2. **Reset-Domain Crossings (RDC)**: Asynchronously asserting reset in one domain while a consumer domain remains active injects unsynchronized transitions identical to CDC faults.
3. **Cross-Module Combinational Loops**: Because Verilog module interfaces omit input-to-output combinational dependency summaries, composing acyclic ready/valid submodules can silently form zero-register feedback rings.

---

### 2. High-Level Synthesis Predictability Cliffs and Verified C-to-Verilog Compilation

Basis: documentation (`Herklotz et al. FCCM 2021`, `VeriCert OOPSLA 2021 & PLDI 2024`, `Dahlia PLDI 2020`) + source (`ymherklotz/vericert`, `cucapra/dahlia`) + execution (`support/verify_hdl_semantics_and_timelines.py`)

#### 2.1 Commercial C/C++ HLS Aliasing, `#pragma` Hazards, and `II` Cliffs

Commercial HLS tools (Vitis HLS, Catapult) synthesize pipelined datapaths from sequential C/C++. Achieving target initiation interval `II = 1` demands proving no loop-carried alias hazards and mapping parallel reads/writes onto disjoint SRAM ports (1R1W or 2RW/cycle). Unconstrained C pointers force brittle heuristics: small edits trigger sudden `II` cliffs (e.g., `II = 1` collapsing to `II > 10`), while unchecked override directives (`#pragma HLS dependence false`) silently generate hardware with data hazards. Empirical differential testing by Herklotz et al. (FCCM 2021) documented functional miscompilations in production HLS suites even without erroneous user pragmas.

#### 2.2 Coq-Verified C-to-Verilog HLS (`VeriCert`, OOPSLA 2021 & PLDI 2024)

`VeriCert` (Herklotz et al., OOPSLA 2021; extended with hyperblock scheduling by Herklotz & Wickerson, PLDI 2024) verifies C-to-Verilog compilation in Coq atop CompCert (`ymherklotz/vericert`). Direct inspection of `src/Compiler.v` (L484–586), `src/hls/GiblePar.v` (L38–76), `src/hls/DHTL.v` (L46–85), `src/hls/Verilog.v` (L208–675), and `src/hls/DVeriloggenproof.v` (L521–540) establishes:

1. **Verified Pass Pipeline (`src/Compiler.v:484–529`)**: After CompCert's verified C-to-RTL optimization chain (`Csyntax -> ... -> RTLgen -> Tailcall -> Inlining -> Renumber -> Constprop -> CSE -> Deadcode -> Unusedglob`), VeriCert composes `forward_simulation` proofs across `GibleSeqgen -> CondElim -> IfConversion (x3) -> DeadBlocks -> GiblePargen -> GibleSubPargen -> DHTLgen -> ClockMemory -> DMemorygen -> ClockRegisters -> DVeriloggen`.
2. **Translation-Validated Hyperblock Scheduling**: `GiblePar` (`ParBB.t := list (list (list instr))`, `GiblePar.v:40`) models predicated parallel instruction blocks produced by untrusted OCaml oracles (`Schedule.ml`, `IfConversionOracle.ml`) and checked by verified Coq validators; `DHTL` (`DHTL.v:49–85`) separates `mod_datapath`, `mod_controllogic`, and synchronous `ram` descriptors (`ram_en`, `ram_u_en`, `ram_addr`).
3. **End-to-End Theorem & Exact TCB Seam**: `Theorem transf_c_program_correct` (`src/Compiler.v:570–576`) proves `transf_hls p = OK tp -> backward_simulation (Csem.semantics p) (Verilog.semantics tp)`. However:
   - `Verilog.step` (`step_module`, `src/hls/Verilog.v:618–640`) defines one deterministic synchronous cycle (`mis_stepp` posedge + `merge_regs nasr1 basr1`, then `mis_stepp_negedge` negedge + merge), omitting IEEE 1800 Clause 4 `Active`-region nondeterminism and 4-state `X`/`Z` values.
   - `PrintVerilog.ml` text emission and downstream logic synthesis (Vivado/Yosys) sit outside Coq.
   - Separate compilation (`src/Compiler.v:579–582`) is vacuous because VeriCert rejects multi-translation-unit inputs.

#### 2.3 Time-Sensitive Affine SRAM Bank-Port Types (`Dahlia`, PLDI 2020)

`Dahlia` (Nigam et al., PLDI 2020; `cucapra/dahlia`) eliminates HLS `II` cliffs by treating physical SRAM bank ports as time-sensitive affine capabilities. Inspecting `src/main/scala/typechecker/AffineCheck.scala` (L75–230) and `CapabilityChecker.scala` (L48–69) confirms:

- **Per-Step Bank Consumption (`CPar`, L225–226; `checkLVal`, L177–196)**: Declaring a banked array `TArray` registers physical bank resources (`addPhysicalResource`, L200–202). Concurrent accesses consume bank capabilities via `env.consumeWithGadget` (L192); colliding on a bank in the same step fails typechecking, and `CapabilityChecker` (L55–63) rejects duplicate writes (`AlreadyWrite`).
- **Bank-Aligned Unrolling (`getConsumeList`, L130–156)**: Unrolled index `TIndex((s, e), _)` enforces `(e - s) % bank == 0` (`BankUnrollInvalid`, L137–138) and verifies total bank resources match the unroll factor (`InsufficientResourcesInUnrollContext`, L185–190); constant `TStaticInt(v)` consumes `v % bank` (L142–143); raw dynamic indices `TSizedInt` are rejected on banked dimensions (`dims(dim)._2 != 1` -> `InvalidDynamicIndex`, L145–148) unless mediated by views/gadgets, outlawing hidden arbiters.
- **Sequential Capability Refresh (`CSeq`, L203–224)**: Across a sequential barrier (`---`), `AffineCheck` restores bank capabilities via `resource.toFresh` (L219) for the next logical time step.

`verify_dahlia_affine_banks()` in `support/verify_hdl_semantics_and_timelines.py` mechanically checks conflict-free `unroll 4` on `bank 4`, bank 0/1 rejection on `bank 2`, and recovery across a sequential barrier.

---

### 3. Guarded Atomic Actions and One-Rule-at-a-Time (`ORAAT`) Hardware (`Bluespec`, `Kami`, `Kôika`)

Basis: documentation (`Kami ICFP 2017`, `Kôika PLDI 2020`) + source (`mit-plv/kami`, `mit-plv/koika`) + execution (`support/verify_hdl_semantics_and_timelines.py`)

#### 3.1 Modular Trace Refinement for Guarded Atomic Actions (`Kami`, ICFP 2017)

Guarded Atomic Actions (introduced by Bluespec `BSV`) describe concurrent hardware via isolated atomic rules that execute concurrently in silicon while preserving **One-Rule-at-a-Time (`ORAAT`)** sequential semantics for verification. `Kami` (Choi et al., ICFP 2017; `mit-plv/kami`) embeds Bluespec-style rules and methods in Coq. Inspection of `Kami/Semantics.v` (L345–365, L965–1015) and `Kami/RefinementFacts.v` (L428–635, L1337–1366) verifies that `traceRefines` (`<<==`) is a preorder (`traceRefines_refl`, `traceRefines_trans`), congruent under parallel module composition (`traceRefines_same_module_structure_modular_1/2`, `traceRefines_comm`, `traceRefines_assoc_1/2`), and invariant under flattening (`flatten_traceRefines` / `flatten_traceRefines_inv`). This modular refinement algebra supports hierarchical RISC-V and cache proofs, though Kami relied on an unverified translation to BSV and inherited BSV's opaque heuristic scheduler.

#### 3.2 Explicit Schedules, Ephemeral History Registers (`EHRs`), and Coq-Verified Compilation (`Kôika`, PLDI 2020)

`Kôika` (Bourgeat et al., PLDI 2020; `mit-plv/koika`) replaces BSV's heuristic scheduler with explicit user-defined schedules (`Cons`, `Try`, `Done`, `coq/OneRuleAtATime.v:248–260`), two-port Ephemeral History Registers (`P0`, `P1`), and a Coq-verified circuit compiler.

Inspecting `coq/Logs.v` (L70–116) and `coq/TypedSemantics.v` (L86–112) extracts the exact dynamic conflict predicates governing a later rule against earlier committed `sched_log` and rule-local `action_log` (`combined = log_app action_log sched_log`):

- `may_read sched_log P0 idx` := `¬exists(W0, sched_log) ∧ ¬exists(W1, sched_log)` (reads cycle-start `r0[idx]`).
- `may_read sched_log P1 idx` := `¬exists(W1, sched_log)` (reads `latest_write0(combined, idx)` if present, else `r0[idx]`, providing deterministic single-cycle forwarding).
- `may_write sched_log action_log P0 idx` := `¬exists(R1, combined) ∧ ¬exists(W0, combined) ∧ ¬exists(W1, combined)`.
- `may_write sched_log action_log P1 idx` := `¬exists(W1, combined)`.

This produces the exact 16-cell intra-cycle conflict matrix (row = earlier committed op in `sched_log`; column = later op; `ABORT` discards the later rule's `action_log`):

| Earlier Op \ Later Op | `R0` | `W0` | `R1` | `W1` | Rationale |
| :--- | :---: | :---: | :---: | :---: | :--- |
| **`R0`** | `OK` | `OK` | `OK` | `OK` | Reading initial state `r0` commutes before `W0`/`R1`/`W1` |
| **`W0`** | `ABORT` | `ABORT` | **`OK` (forwards `W0`)** | `OK` | `R1` observes `W0` in-cycle; `R0`/`W0` after `W0` violates ORAAT order |
| **`R1`** | `OK` | `ABORT` | `OK` | `OK` | `W0` after `R1` would invalidate the value `R1` already observed |
| **`W1`** | `ABORT` | `ABORT` | `ABORT` | `ABORT` | `W1` is terminal for the cycle; no later access is allowed |

Two flagship Coq theorems close the semantic gap down to optimized bit-level circuits:

- **`Theorem OneRuleAtATime` (`coq/OneRuleAtATime.v:279–293`)**: For every schedule `s` and cycle log `log = interp_scheduler r sigma rules s`, there exists a committed subsequence `rs` of `scheduler_rules s` such that `List.fold_left interp_oraat rs r = commit_update r log`.
- **`Theorem compiler_correct` (`coq/CompilerCorrectness/Correctness.v:36–48`)**: For every register `reg`, evaluating the compiled circuit `compile_scheduler lco rules external s` equals `bits_of_value` of `TypedSemantics.interp_cycle sigma rules s r`.

`verify_koika_ehr_oraat()` in `support/verify_hdl_semantics_and_timelines.py` transcribes `coq/Logs.v` and `coq/TypedSemantics.v` directly, confirms all 16 conflict-matrix cells, demonstrates `W0 -> R1` forwarding versus `R1 -> W0` conflict abort, and exhaustively verifies `OneRuleAtATime` across 96 `(state, schedule)` cases (`96/96 PASS`).

---

### 4. Timeline Interval Types, Expression-Based Pipelining, and Split-Control IRs (`Filament`, `Spade`, `Calyx`)

Basis: documentation (`Filament PLDI 2023`, `Spade OSDA 2023 & TRETS 2026`, `Calyx ASPLOS 2021`) + source (`cucapra/filament`, `cucapra/calyx`) + execution (`support/verify_hdl_semantics_and_timelines.py`)

#### 4.1 Presburger Timeline Interval Types (`Filament`, PLDI 2023)

Statically scheduled datapaths (FPUs, crypto pipelines, DSP filters) fail silently in Verilog/Chisel/Hardcaml when a submodule latency changes by 1 cycle or a shared functional unit is invoked faster than its initiation interval `II`. `Filament` (Nigam et al., PLDI 2023; `cucapra/filament`) attaches availability intervals `@[G, G+1]` and recurrence delays `G: L` to component signatures, verifies all Presburger arithmetic constraints via SMT, and erases types to zero-overhead Verilog.

Direct inspection of `crates/filament/src/ir_passes/{interval_check.rs, discharge.rs, assignment_check.rs, phantom_check.rs}` verifies the complete obligation set:

| Pass & Source Lines | Generated Proof Obligation | Hardware Hazard Eliminated |
| :--- | :--- | :--- |
| `IntervalCheck::delay_wf` (`interval_check.rs:43–62`) | $\text{delay}(G) > 0$ | Degenerate zero-cycle recurrence |
| `IntervalCheck::range_wf` (`interval_check.rs:25–40`) | $\text{end} > \text{start}$ | Inverted or empty validity windows |
| `IntervalCheck::start` (`interval_check.rs:158–195`) | $\text{delay}(G) \ge (\text{end} - \text{start})$ | Signal outliving recurrence period and overwriting next input wave |
| `IntervalCheck::event_binding` (`interval_check.rs:80–117`) | $\text{delay}_{\text{caller}} \ge \text{delay}_{\text{callee}}$ | Violating callee initiation interval $II$ |
| `IntervalCheck::instance` & `invoke` (`interval_check.rs:199–306`) | $\text{use\_start} \ge \text{start} \land \text{use\_start} + \text{delay} \le \text{end}$, $\text{delay}(G) \ge \text{end} - \text{start}$ | Structural double-booking and modular wrap-around clashes on shared units |
| `IntervalCheck::connect` (`interval_check.rs:308–360`) | $\text{src.start} \le \text{dst.start} \land \text{src.end} \ge \text{dst.end}$ | Pipeline wire skews (reading too early or too late) |
| `AssignCheck` (`assignment_check.rs:10–80`) | Each monomorphized port index written $\le 1$ time | Multi-driver wire contention |
| `PhantomCheck` (`phantom_check.rs:9–90`) | Phantom events cannot govern shared instances | Erasing timing events still needed to separate time-multiplexed uses |
| `Discharge::conf_solver` (`discharge.rs:104–122`) | Discharges obligations via `easy_smt` (`Z3`, `Boolector`, `CVC5`, `Bitwuzla`) | Automated parametric Presburger checking |

`verify_filament_timelines()` in `support/verify_hdl_semantics_and_timelines.py` validates an aligned 3-stage MAC while rejecting a 1-cycle wire skew (`@[G+2, G+3] -> @[G+3, G+4]`), a structural double-booking of a shared `II=2` multiplier (`G+0`, `G+1`), and a wrap-around clash (`G+0`, `G+2` under caller `II=3`, cyclic gap `1 < 2`).

#### 4.2 Expression-Oriented Pipelining, ADTs, and Linear Backward Wires (`Spade`, OSDA 2023 / TRETS 2026)

`Spade` (Skarman & Gustafsson, OSDA 2023 `arXiv:2304.03079`; Skarman, Sörnäs, & Gustafsson, ACM TRETS 2026 `10.1145/3793550`) eliminates major RTL failure classes without external SMT solvers via three Rust-inspired constructs:

- **Pure Expressions and Exhaustive ADTs**: Total expressions, tagged `enum`/`Option<T>` values, and exhaustive `match` make inferred latches unrepresentable and replace error-prone manual `valid`+payload wire pairs.
- **Explicit `pipeline(N)` Scoping**: Named pipeline stages (`reg;`) and statically checked stage offsets (`stage(+k)`/`stage(-k)`) reject cross-stage latency skew at compile time.
- **Linear Backward Wires (`inv &T`)**: Inverted ports (superseding earlier `&mut T`/`~T` syntax) allow consumer-to-producer backpressure (`ready`) inside composite port types while enforcing **linear single-driver checking**—statically rejecting both undriven floating backward wires and multi-driver short circuits.

#### 4.3 Split Structural-Datapath / Imperative-Control IR (`Calyx`, ASPLOS 2021)

`Calyx` (Nigam et al., ASPLOS 2021; `cucapra/calyx`) bridges software SSA (which erases wires, ports, and bitwidths) and flat RTL (which erases loop/control structure into opaque FSMs). Inspecting `calyx/ir/src/control.rs` (L10–340) and `calyx/opt/src/passes/` confirms:

- **Structural `cells` and guarded `wires` (`Group`, `StaticGroup`, `CombGroup`)** expose instantiated registers, ALUs, and memories directly to reusable structural passes (`cell_share.rs`, `wire_inliner.rs`, `dead_assignment_removal.rs`).
- **Dynamic vs. Static `Control` (`control.rs:12–338`)**: Dynamic `Seq`, `Par`, `If`, and `Invoke` synchronize via 1-bit `go`/`done` handshakes for variable-latency units, while `StaticSeq`, `StaticPar`, `StaticEnable`, and `StaticInvoke` carry explicit cycle counts (`StaticLatency`), enabling `static_promotion.rs`, `static_fsm_allocation.rs`, `schedule_compaction.rs`, and `compile_static.rs` to eliminate per-group handshake FSM overhead.

---

### 5. Multi-Level Hardware Compilers, Formal Technology Mapping, and Embedded HDLs

Basis: documentation (`Lakeroad ASPLOS 2024`, `CIRCT`, `Hardcaml`, `Clash`, `Silver Oak`) + source (`llvm/circt`, `gussmith23/lakeroad`, `janestreet/hardcaml`, `clash-lang/clash-compiler`, `project-oak/silveroak`)

#### 5.1 Progressive MLIR Hardware and Formal Dialects (`LLVM CIRCT`)

Inspection of `llvm/circt` (`include/circt/Dialect/` and `include/circt/Conversion/`) documents its stratified MLIR dialect spine:

| Tier | Verified Dialects (`include/circt/Dialect/`) | Verified Key Types / Ops | Architectural Role |
| :--- | :--- | :--- | :--- |
| **Elastic / Accelerator** | `Calyx`, `Handshake`, `DC`, `ESI`, `AXI4`, `Pipeline`, `LoopSchedule`, `Kanagawa` | `ESI`: `ChannelSignaling` (`ValidReady`, `FIFO`, `ValidOnly`), `esi.wrap.{vr,fifo,vo}`, `esi.snoop.{vr,xact}` (`ESIChannels.td:34–297`) | Latency-insensitive channel composition and host–accelerator services (`ESIServices.td`) |
| **Frontend Ingestion** | `FIRRTL`, `Moore`, `LLHD`, `FSM` | Chisel/FIRRTL, SystemVerilog (`Moore`), low-level simulation (`LLHD`) | Multi-language frontend lowering |
| **Core Structural RTL** | `HW`, `Comb`, `Seq`, `HWArith`, `Synth`, `Datapath` | `Seq`: `!seq.clock`, `!seq.hlmem`, `!seq.firmem`, `!seq.immutable` (`SeqTypes.td:21–115`) | Event-queue-free typed RTL spine (`!seq.clock` separates clocks from 1-bit data) |
| **Emission & Simulation** | `SV`, `Emit`, `Arc`, `Sim`, `SystemC` | `Arc`: `arc.define`, `arc.state`, `arc.memory`, `arc.storage.get`, `arc.root_input/output` (`ArcOps.td:31–526`) | Restricted SystemVerilog emission (`HWToSV.h`) or LLVM-compiled cycle simulation (`ArcToLLVM.h`) |
| **Formal Verification** | `Verif`, `LTL` (+ upstream core MLIR `smt`) | `Verif`: `verif.assert/assume/cover`, `clocked_assert`, `has_been_reset`, `verif.bmc`, `verif.lec`, `verif.refines` (`VerifOps.td:46–314`) | Lowered to upstream MLIR `smt` and BTOR2 via `Conversion/{VerifToSMT,HWToSMT,CombToSMT,DatapathToSMT,FSMToSMT,SMTToZ3LLVM,HWToBTOR2}.h` |

Notably, at the pinned commit `203f159c...`, `smt` no longer resides under `include/circt/Dialect/`—it was upstreamed to core MLIR (`mlir::smt`), with CIRCT retaining the hardware-to-SMT and Z3/LLVM lowering passes.

#### 5.2 SMT Sketch-Guided FPGA Technology Mapping (`Lakeroad`, ASPLOS 2024)

`Lakeroad` (Smith et al., ASPLOS 2024; `gussmith23/lakeroad`) replaces fragile structural pattern matchers for FPGA LUTs, carry chains, and DSP blocks (Xilinx UltraScale+, Lattice ECP5, Intel `altmult_accum`, SOFA) with Rosette/SMT synthesis. Inspecting `racket/synthesize.rkt` (L20, L30–100, L195, L872, L1184–1187) and `racket/btor.rkt` confirms that `Lakeroad` extracts formal bitvector models directly from vendor primitive Verilog simulation libraries via Yosys/BTOR, instantiates parameterized sketches (`synthesize-with-sketch`, `synthesize-lattice-ecp5-dsp`), and solves for a functionally equivalent mapping using `bitwuzla` (`(current-solver (bitwuzla))`, L1187)—eliminating heuristic DSP/LUT mis-synthesis bugs modulo vendor simulation-model accuracy.

#### 5.3 Functional and Proof-Assistant-Embedded HDLs (`Hardcaml`, `Clash`, `Silver Oak`/`Cava`)

1. **`Hardcaml` (`janestreet/hardcaml`, v0.18 preview)**: Embeds structural RTL in OCaml with deterministic Verilog/VHDL emission (`rtl_verilog_of_ast.ml`) and `Cyclesim` simulation. Direct inspection verifies elaboration-time combinational loop checking (`Signal_graph.detect_combinational_loops : t -> unit Or_error.t`, `src/signal_graph.mli:56–58`), clock-pin DRC (`src/design_rule_checks.ml:45–62`), runtime UID clock-domain tracking (`Clock_domain.Runtime.t = Constant | Unknown | Exact of Exact.t` and `construct_mapping_from_spec_to_exact` catching `Maps_to_unknown` / `Maps_to_multiple`, `kernel/clock_domain.mli:28–94`), and `Async_fifo` (`src/async_fifo.mli`). Widths and domains are validated at OCaml elaboration time rather than in the host static type system.
2. **`Clash` (`clash-lang/clash-compiler`)**: Compiles Haskell to Verilog/SystemVerilog/VHDL with GHC type-level natural bitwidths (`KnownNat`) and phantom clock/reset domains (`type Domain = Symbol`, `data Signal (dom :: Domain) a`, `Clock dom`, `Reset dom`, `Clash/Signal/Internal.hs:783–1258`). Each domain carries a compile-time `DomainConfiguration` (`Internal.hs:258–359`: `_period`, `_activeEdge` `Rising | Falling`, `_resetKind` `Asynchronous | Synchronous`, `_initBehavior` `Unknown | Defined`, `_resetPolarity` `ActiveHigh | ActiveLow`). Cross-domain signal mixing is a GHC compile-time error unless mediated through `Clash/Explicit/Synchronizer.hs` (L53–251), where `dualFlipFlopSynchronizer` (L75–96) explicitly warns it is safe **only for single-bit signals** (illustrating binary `0111 -> 1000` tearing to `0000`), while `asyncFIFOSynchronizer` (L100–251) synchronizes multi-bit words via `trueDualPortBlockRam` and Gray-coded pointers.
3. **`Silver Oak / Cava` (`project-oak/silveroak`)**: Embeds a Lava-style structural HDL in Coq for OpenTitan cryptographic silicon. `cava/Cava/Core/Circuit.v` (L31–65) defines `Inductive Circuit : Type -> Type -> Type := Comb | Compose | First | Second | LoopInitCE | DelayInitCE` with `circuit_state` and `reset_state`; restricting feedback to registered `LoopInitCE` makes combinational loops unrepresentable. `silveroak-opentitan/aes/Impl/AES256Equivalence.v` (L142–195) proves 14-round AES-256 functional equivalence (`full_cipher_equiv`) and round-trip invertibility (`full_cipher_inverse`) with zero axioms (`FullCipherEquiv_Assumptions.out`: `Closed under the global context`). Crucially, `README.md` (L32–37) states that Coq/Haskell SystemVerilog netlist extraction (`AESSV.hs`) remains unverified.

---

### 6. Clockless Quasi-Delay-Insensitive (`QDI`) Hardware (`CHP` / Martin Synthesis / `ACT`)

Basis: documentation (`Martin 1990`, `Ataei et al. IEEE Design & Test 2021`) + source (`asyncvlsi/act`) + derived (synchronous–asynchronous duality)

#### 6.1 Communicating Hardware Processes (`CHP -> HSE -> PRS`) and `ACT`

Alain J. Martin (1990) established algebraic compilation for **Quasi-Delay-Insensitive (`QDI`)** clockless circuits eliminating global clock distribution, PVT clock-tree margins, and CDC synchronizers:

1. **`CHP`**: CSP-style concurrent processes communicating over unbuffered channels (`X!e`, `Y?v`) with parallel (`,`), sequential (`;`), deterministic guarded selection, arbitrated nondeterministic selection, and loops.
2. **`HSE` (Handshake Expansion)**: Refines channel actions into 4-phase/2-phase request–acknowledge transitions over delay-insensitive data codes (e.g., dual-rail 1-of-2 `{d.0, d.1}`: neutral `00`, false `10`, true `01`, illegal `11`) with Muller C-element completion detection.
3. **`PRS` (Production Rule Set)**: Compiles HSE state graphs into CMOS pull-up (`g -> x+`) and pull-down (`h -> x-`) transistor guards preserving stability and non-interference.

Rajit Manohar's **`ACT`** toolkit (`asyncvlsi/act`; Ataei et al., *IEEE Design & Test* 2021) unifies all three tiers. Direct inspection of `act/lang.h` (L65–127, L223–285) and `act/prs.h` (L44–55) verifies `enum act_chp_lang_type` (`ACT_CHP_COMMA`, `SEMI`, `SELECT`, `SELECT_NONDET`, `LOOP`, `DOLOOP`, `SEND`, `RECV`, `ACT_HSE_FRAGMENTS`, guarded command `act_chp_gc`) alongside `enum act_prs_expr_type` (`AND`, `OR`, `VAR`, `NOT`, `ANDLOOP`, `ORLOOP`), transistor sizing (`act_size_spec_t`: `w`, `l`, `flavor`, `folds`), precharge annotations (`pchg`), and `ACT_PRS_RULE`.

#### 6.2 Isochronic Forks and Synchronous–Asynchronous Duality

Because purely delay-insensitive circuits with standard single-output gates are too restricted for general computation (Martin 1990), QDI adds the weakest sufficient physical timing assumption: the **isochronic fork** (skew between branches of a local wire fork is less than one gate delay, so acknowledging one branch guarantees arrival on the other). Comparing `Filament`/`Clash`/`CIRCT ESI` against `CHP`/`ACT` reveals an exact duality:

| Axis | Synchronous Typed HDLs (`Filament`, `Clash`, `Spade`) | Clockless QDI (`CHP`, Martin Synthesis, `ACT`) | Elastic Bridge (`CIRCT ESI`, `Handshake`, GALS) |
| :--- | :--- | :--- | :--- |
| **Time Model** | Global discrete ticks + Presburger intervals `@[G, G+1]` | Partial order of local causal events (no global clock) | Clocked islands linked by latency-insensitive `ValidReady`/`FIFO` channels |
| **Composition Contract** | Static latency $L$, `II`, matching phantom `Domain` | Dual-rail channel rendezvous + C-element completion | Backpressure-aware `valid`/`ready` handshake |
| **Timing Sign-Off** | Global worst-case Static Timing Analysis (STA) | Local isochronic-fork verification only; average-case speed | Per-island STA + verified CDC synchronizers / async FIFOs |
| **Primary Failure Class** | 1-cycle skew, setup/hold violation, CDC metastability | Isochronic-fork violation, orphaned transitions, deadlock | Combinational `ready`/`valid` loops, backpressure deadlock |

---

### 7. Comparative Architecture Matrix and HW–SW Co-Design Seam Implications

Basis: source (all 13 pinned repositories) + documentation (`Bedrock2+Kami PLDI 2021`, `CakeML/Silver PLDI 2019`, `Lutsig FormaliSE 2019 & CPP 2021`) + derived (cross-system taxonomy and co-design synthesis)

#### 7.1 Side-by-Side Architecture Comparison

| System | Core Semantic Model | Timing / Concurrency / Resource Guarantee | Primary Verification Anchor | Remaining External TCB |
| :--- | :--- | :--- | :--- | :--- |
| **SystemVerilog (`1800-2023`)** | Stratified event queue (§4) + `{0,1,x,z}` | None for CDC, `II`, skew, latches, or `=`/`<=` races | Linters, SVA, `Xprop`, commercial LEC | Entire synthesis, P&R, sim-vs-synth gap |
| **`Verismith`** | Acyclic deterministic Verilog fuzzer | Excludes comb loops & `BinDiv`/`BinMod`/`BinCEq` | Differential fuzzing (`Fuzz.hs`, 11 bugs) | Testing only; no soundness guarantee |
| **`VeriCert`** | CompCert `Csem` -> `GiblePar` -> `DHTL` -> Coq `Verilog` | Preserves C sequential semantics + hyperblock scheduling | Coq `transf_c_program_correct` (`Compiler.v:570`) | Deterministic 2-edge Coq `Verilog` (no `X`/races); `PrintVerilog.ml` + synth; 1 TU limit |
| **`Dahlia`** | Imperative HLS with affine bank types | Rejects SRAM bank conflicts (`AffineCheck.scala`) & double writes | Compile-time affine type soundness | Lowers to Calyx/C++; downstream synth unverified |
| **`Kami`** | Coq Bluespec rules & methods | Modular ORAAT trace refinement (`RefinementFacts.v`) | Coq modular proofs (RISC-V, `Bedrock2+Kami`) | BSV/Verilog backend & BSV heuristic scheduler |
| **`Kôika`** | Explicit schedules + 2-port EHRs (`P0`/`P1`) | Dynamic conflict resolution (`coq/Logs.v:70–101`) | Coq `OneRuleAtATime` + `compiler_correct` | Verilog pretty-printing & EDA synth/P&R |
| **`Filament`** | Structural RTL + Presburger `@[G, G+1]` types | Rejects 1-cycle skews, `II` & double-booking hazards | SMT (`Z3`/`Boolector`/`CVC5`/`Bitwuzla`) | No functional proof; Verilog emission & synth |
| **`Spade`** | Expression RTL + ADTs + `pipeline(N)` + `inv &T` | No latches, stage-checked pipelines, linear backward wires | Static Rust-hosted type/linearity checker | No mechanized compiler proof; SV synth |
| **`Calyx`** | Structural cells/wires + dynamic/static `Control` | Separates `go`/`done` handshakes from static FSMs (`control.rs`) | Well-formedness (`well_formed.rs`) + reusable passes | Compiler passes (`compile_static.rs`) unverified |
| **`LLVM CIRCT`** | Progressive MLIR dialects (`hw`/`seq`/`esi`/`arc`/`verif`) | `!seq.clock`, typed `ESI` channels, `verif.lec`/`bmc`/`refines` | Lowering to upstream MLIR `smt` & BTOR2 | C++ passes & SMT encoder unverified |
| **`Lakeroad`** | Rosette/SMT sketch-guided FPGA mapper | Bitvector equivalence to vendor LUT/DSP models | `bitwuzla` SMT verification (`synthesize.rkt:1187`) | Vendor sim models, Yosys glue, P&R |
| **`Hardcaml`** | OCaml structural RTL + `Always` DSL | Comb-loop check (`Signal_graph`) + UID `Clock_domain.Runtime` | `Cyclesim` tests, DRC (`design_rule_checks.ml`) | Elaboration-time checks only; Verilog/synth |
| **`Clash`** | Pure Haskell streams `Signal dom a` | Static GHC phantom domains (`DomainConfiguration`) & `KnownNat` | Type safety + `asyncFIFOSynchronizer` | `unsafeSynchronizer`, Clash-to-Verilog & synth |
| **`Silver Oak / Cava`** | Coq Lava `Inductive Circuit` (`LoopInitCE`) | Comb-loops unrepresentable; indexed bitwidths | Axiom-free OpenTitan AES-256 Coq proofs | Haskell SV netlist extraction (`AESSV.hs`) & synth |
| **`ACT` (QDI)** | Clockless `CHP -> HSE -> PRS` processes | Dual-rail DI handshakes + C-element completion (`act/lang.h`) | Martin algebraic refinements (modulo isochronic forks) | C++ synthesis passes, sizing, physical fork sign-off |

#### 7.2 Architectural Laws for Verified HW–SW Co-Design and the RTL FFI Seam

Synthesizing across all examined systems yields three durable laws for HW–SW co-verification (MMIO, DMA, interrupts, coprocessors):

1. **Formalize the HW–SW seam against a small deterministic RTL core, not full SystemVerilog.** Landmark end-to-end verified stacks avoid raw SystemVerilog as the callee model: **`Bedrock2` + `Kami`** (Erbsen et al., PLDI 2021) proved Coq refinement from an IoT app and MMIO driver through a verified compiler to a cycle-accurate Kami RISC-V core over a shared external-event trace; **`CakeML` on `Silver`** (Lööw et al., PLDI 2019) and **`Lutsig`** (Lööw & Myreen, FormaliSE 2019; Lööw, CPP 2021) proved compilation from HOL4 down to a deterministic Verilog subset and gate-level netlist.
2. **Factor accelerators into orthogonal typed planes.** Control arbitration and side-effecting MMIO registers (W1C, FIFO pop-on-read) align with **ORAAT / Guarded Atomic Actions** (`Kôika`/`Kami`, pairing with host volatile/atomic ordering in `anneal-concurrency-weak-memory-kernels-and-storage-survey`); fixed-latency datapaths and banked SRAMs align with **Timeline + Affine Bank + Linear Port Types** (`Filament` + `Dahlia` + `Spade` `inv &T`); cross-domain seams align with **Phantom Clock Domains** (`Clash`) and **Elastic / Asynchronous Channels** (`CIRCT ESI`, `ACT` QDI).
3. **Stratify post-RTL assurance explicitly.** Even Coq-verified RTL compilers (`Kôika`, `VeriCert`, `Silver Oak`) leave vendor synthesis, P&R, STA, and bitstream generation outside proof kernels (partially narrowed by `Lutsig` and `Lakeroad`). Co-verification claims must therefore separate kernel-checked proofs, translation-validated passes (`circt-lec`, `Lakeroad` SMT), and physical sign-off (STA, CDC/isochronic-fork checks), matching `anneal-cps-robotics-aerospace-eda-and-quantum-survey`.

## Boundaries

- **not examined**:
  - **Live GitLab source of `Spade` (`gitlab.com/spade-lang/spade`)**: Proxy restrictions on non-GitHub hosts prevented pinning a GitLab SHA; Spade claims rely on `arXiv:2304.03079`, ACM TRETS 2026, and documentation.
  - **Proprietary EDA internals (`Vivado`, `Quartus Prime`, `Design Compiler`, `Vitis HLS`, `Catapult`, `SpyGlass`)**: Closed-source binaries were not executed; findings rest on IEEE Std 1800-2023 and published empirical studies (`Verismith`, `Herklotz et al.` FCCM 2021).
  - **Standalone `Chisel`/`FIRRTL` Scala compilers, Bluespec `bsc`, SystemVerilog SVA (Clause 16), and analog/physical sign-off (SPICE, STA corner derating, bitstreams)**: Not audited line-by-line.
- **unknown**:
  - **Post-2020 synthesis bug rates in current Vivado/Quartus/Yosys releases**: `Verismith`'s 11-bug count reflects its FPGA 2020 snapshot and was not re-measured.
  - **Scaling of `Lakeroad` beyond fixed-width LUT/DSP arithmetic to BRAM/URAM inference, control FSMs, and large ASIC standard-cell libraries**: Not established at the inspected commit.
  - **Mechanized compiler soundness for `Filament` and `Dahlia`**: Neither repository ships a Coq/Lean soundness proof comparable to `Kôika`'s `Correctness.v`.
- **known not to apply**:
  - **`VeriCert`'s `transf_c_program_correct` does NOT cover IEEE 1800-2023 event races or 4-state `X`**: `src/hls/Verilog.v:618–640` targets a deterministic two-edge Coq `Verilog` model.
  - **`Clash`'s `dualFlipFlopSynchronizer` is NOT safe for multi-bit words**: `Clash/Explicit/Synchronizer.hs:57–74` documents multi-bit tearing and requires Gray-coded `asyncFIFOSynchronizer`.
  - **`Silver Oak / Cava`'s axiom-free proof does NOT verify SystemVerilog extraction**: `README.md:32–37` excludes Coq-to-SystemVerilog netlist generation (`AESSV.hs`).
  - **`support/verify_hdl_semantics_and_timelines.py` does NOT verify upstream compilers**: It checks faithful Python transcriptions of the core formal models only.
- **unsupported**:
  - **Multi-TU compilation in `VeriCert`**: `src/Compiler.v:579–582` fails if more than one C translation unit is supplied.
  - **Variable-latency elastic backpressure inside pure `Filament` timeline types**: `IntervalCheck` requires static Presburger intervals and delays.
  - **Zero-timing-assumption general-purpose QDI circuits in `ACT`**: QDI VLSI requires the local **isochronic fork** assumption (Martin 1990).

## Evidence

All primary evidence was acquired and verified on `2026-11-19`.

### 1. Pinned Upstream Git Repositories and Direct Source Coordinates

| Subject | Repository & Full 40-Char SHA | Inspected Paths, Symbols & Line Ranges |
| :--- | :--- | :--- |
| **Kôika** | `mit-plv/koika` @ `8921e30434d9e351c49df84c9aa14e72b0456ad0` | `coq/Logs.v:70–116` (`may_read`, `may_write`, `latest_write0`, `commit_update`); `coq/TypedSemantics.v:54–112` (`interp_action`); `coq/OneRuleAtATime.v:243–293` (`Theorem OneRuleAtATime`); `coq/CompilerCorrectness/Correctness.v:36–48` (`Theorem compiler_correct`) |
| **Kami** | `mit-plv/kami` @ `9217329eb4e1d751f28ab175ebab230b1e8fd4da` | `Kami/Semantics.v:345–365,965–1015`; `Kami/RefinementFacts.v:428–635,1337–1366` (`traceRefines_refl/trans`, `traceRefines_same_module_structure_modular_1/2`, `flatten_traceRefines`) |
| **VeriCert** | `ymherklotz/vericert` @ `8df09a182cc3ae3859d5bd6ab881b1066d38fabe` | `src/Compiler.v:484–586` (`transf_c_program_correct`, 1-TU restriction); `src/hls/GiblePar.v:38–76`; `src/hls/DHTL.v:46–85`; `src/hls/Verilog.v:208–299,618–675` (`step_module`); `src/hls/DVeriloggenproof.v:521–540` |
| **Verismith** | `ymherklotz/verismith` @ `dd54c5f2c1b1b00696576fb70002d18fcafdc1e2` | `src/Verismith/Generate.hs:142–207` (`randomOrdAssigns`, `genBitVec`); `src/Verismith/Fuzz.hs:197–287,503–559` (`synthesis`, `equivalence`, `fuzz`) |
| **Filament** | `cucapra/filament` @ `3c17db5ce85c354dd3da0af57f3adcb59bb295ac` | `crates/filament/src/ir_passes/interval_check.rs:25–360` (`range_wf`, `delay_wf`, `event_binding`, `start`, `invoke`, `instance`, `connect`); `discharge.rs:104–122` (`conf_solver`); `assignment_check.rs:10–80`; `phantom_check.rs:9–90` |
| **Dahlia** | `cucapra/dahlia` @ `bd68b131ee14f46dd9d2099f86ead01f7d756a71` | `src/main/scala/typechecker/AffineCheck.scala:75–230` (`getConsumeList`, `BankUnrollInvalid`, `InvalidDynamicIndex`, `CSeq` `toFresh`); `CapabilityChecker.scala:48–69` (`AlreadyWrite`) |
| **Calyx** | `cucapra/calyx` @ `e1bca4bf6779ccc98b5099f9a2284ca3b0bef637` | `calyx/ir/src/control.rs:10–340` (`Seq`, `StaticSeq`, `Par`, `StaticPar`, `If`, `StaticEnable`, `Invoke`, `StaticInvoke`); `calyx/opt/src/passes/` (`compile_static.rs`, `cell_share.rs`, `static_fsm_allocation.rs`, `static_promotion.rs`, `well_formed.rs`) |
| **LLVM CIRCT** | `llvm/circt` @ `203f159ce10d78940df4264327d5f3fc8b902112` | `include/circt/Dialect/` inventory; `Seq/SeqTypes.td:21–115`; `ESI/ESIChannels.td:34–297`; `Verif/VerifOps.td:46–314`; `Arc/ArcOps.td:31–526`; `include/circt/Conversion/{VerifToSMT,HWToSMT,CombToSMT,DatapathToSMT,FSMToSMT,SMTToZ3LLVM,HWToBTOR2,CalyxToHW,ArcToLLVM}.h` |
| **Lakeroad** | `gussmith23/lakeroad` @ `c5c5a9ac4efc250374df7f9a37d59087a6cc7ba1` | `racket/synthesize.rkt:20,30–100,195,872,1184–1187` (`bitwuzla`, `synthesize-with-sketch`, `rosette-synthesize`); `racket/{btor,sketches,architecture-description}.rkt` |
| **Hardcaml** | `janestreet/hardcaml` @ `d9da179ea12228a0e3f7c1358fedec2ab8971f73` | `src/signal_graph.mli:56–58,102–108` (`detect_combinational_loops`); `src/design_rule_checks.ml:45–62`; `kernel/clock_domain.mli:6–94` (`Exact`, `Runtime`, `construct_mapping_from_spec_to_exact`); `src/async_fifo.mli` |
| **Clash** | `clash-lang/clash-compiler` @ `920973dbb208b14f875eff730dbcf739fad22870` | `clash-prelude/src/Clash/Signal/Internal.hs:258–359,783–1258` (`DomainConfiguration`, `Signal`, `Clock`, `Reset`); `Clash/Explicit/Synchronizer.hs:53–251` (`dualFlipFlopSynchronizer`, `asyncFIFOSynchronizer`) |
| **Silver Oak** | `project-oak/silveroak` @ `cccfdb4e19c5906256d2ed4487bf1a0aa2fab99e` | `README.md:32–37`; `cava/Cava/Core/Circuit.v:31–65` (`Circuit`, `circuit_state`); `silveroak-opentitan/aes/Impl/AES256Equivalence.v:125–195` (`full_cipher_equiv`, `full_cipher_inverse`); `FullCipherEquiv_Assumptions.out` (`Closed under the global context`) |
| **ACT** | `asyncvlsi/act` @ `6071f559d2996923f067447804b2737551a54715` | `act/lang.h:65–127` (`act_prs_expr_type`, `act_size_spec_t`, `ACT_PRS_RULE`), `L223–285` (`act_chp_lang_type`, `ACT_HSE_FRAGMENTS`, `act_chp_gc`); `act/prs.h:44–55` |

### 2. Primary Specifications and Peer-Reviewed Literature

- **IEEE Std 1800-2023**: *IEEE Standard for SystemVerilog—Unified Hardware Design, Specification, and Verification Language*, 2024-02-28, DOI `10.1109/IEEESTD.2024.10458102`.
- **Cummings (2000)**: Clifford E. Cummings, *Nonblocking Assignments in Verilog Synthesis, Coding Styles That Kill!*, SNUG San Jose 2000.
- **Turpin (2003)**: Mike Turpin, *The Dangers of Living with an X (bugs hidden in your Verilog)*, SNUG Boston 2003.
- **Verismith (2020)**: Yann Herklotz & John Wickerson, *Finding and Understanding Bugs in FPGA Synthesis Tools*, FPGA 2020, DOI `10.1145/3373087.3375310`.
- **HLS Reliability (2021)**: Yann Herklotz, Zewei Du, Nadesh Ramanathan, & John Wickerson, *An Empirical Study of the Reliability of High-Level Synthesis Tools*, IEEE FCCM 2021, DOI `10.1109/FCCM51124.2021.00034`.
- **VeriCert (2021 & 2024)**: Yann Herklotz, James D. Pollard, Nadesh Ramanathan, & John Wickerson, *Formal Verification of High-Level Synthesis*, PACMPL 5(OOPSLA), 2021, DOI `10.1145/3485494`; Yann Herklotz & John Wickerson, *Hyperblock Scheduling for Verified High-Level Synthesis*, PACMPL 8(PLDI), 2024, DOI `10.1145/3656455`.
- **Kami (2017)**: Joonwon Choi, Muralidaran Vijayaraghavan, Benjamin Sherman, Adam Chlipala, & Arvind, *Kami: A Platform for High-Level Parametric Hardware Specification and Its Modular Verification*, PACMPL 1(ICFP), 2017, DOI `10.1145/3110268`.
- **Kôika (2020)**: Thomas Bourgeat, Clément Pit-Claudel, Adam Chlipala, & Arvind, *The Essence of Bluespec: A Core Language for Rule-Based Hardware Design*, PLDI 2020, DOI `10.1145/3385412.3385965`.
- **Dahlia (2020)**: Rachit Nigam, Sachille Atapattu, Samuel Thomas, Zhijing Li, Theodore Bauer, Yuwei Ye, Apurva Koti, Adrian Sampson, & Zhiru Zhang, *Predictable Accelerator Design with Time-Sensitive Affine Types*, PLDI 2020, DOI `10.1145/3385412.3385974`.
- **Calyx (2021)**: Rachit Nigam, Samuel Thomas, Zhijing Li, & Adrian Sampson, *A Compiler Infrastructure for Accelerator Generators*, ASPLOS 2021, DOI `10.1145/3445814.3446712`.
- **Filament (2023)**: Rachit Nigam, Pedro Henrique Azevedo de Amorim, & Adrian Sampson, *Modular Hardware Design with Timeline Types*, PACMPL 7(PLDI), 2023, DOI `10.1145/3591234`.
- **Spade (2023 & 2026)**: Frans Skarman & Oscar Gustafsson, *Spade: An Expression-Based HDL With Pipelines*, OSDA 2023, `arXiv:2304.03079`; Frans Skarman, Gustav Sörnäs, & Oscar Gustafsson, *Spade – A Modern Hardware Description Language*, ACM TRETS 2026, DOI `10.1145/3793550`.
- **Lakeroad (2024)**: Gus Henry Smith, Benjamin Kushigian, Vishal Canumalla, Andrew Cheung, Steven Lyubomirsky, Sorawee Porncharoenwase, René Just, Gilbert Louis Bernstein, & Zachary Tatlock, *FPGA Technology Mapping Using Sketch-Guided Program Synthesis*, ASPLOS 2024, DOI `10.1145/3620665.3640387`.
- **QDI / ACT (1990 & 2021)**: Alain J. Martin, *Programming in VLSI: From Communicating Processes to Delay-Insensitive Circuits*, Caltech CS-TR-89-1 / Addison-Wesley 1990, pp. 1–64; Samira Ataei, Wenmian Hua, Yihang Yang, Rajit Manohar, Yi-Shan Lu, Jiayuan He, Sepideh Maleki, & Keshav Pingali, *An Open-Source EDA Flow for Asynchronous Logic*, *IEEE Design & Test* 38(2), pp. 27–37, April 2021, DOI `10.1109/MDAT.2021.3051334`.
- **End-to-End HW–SW Verification**: Andres Erbsen, Samuel Gruetter, Joonwon Choi, Clark Wood, & Adam Chlipala, *Integration Verification across Software and Hardware for a Simple Embedded System*, PLDI 2021, DOI `10.1145/3453483.3454065`; Andreas Lööw, Ramana Kumar, Yong Kiam Tan, Magnus O. Myreen, Michael Norrish, Oskar Abrahamsson, & Anthony Fox, *Verified Compilation on a Verified Processor*, PLDI 2019, DOI `10.1145/3314221.3314622`; Andreas Lööw & Magnus O. Myreen, *A Proof-Producing Translator for Verilog Development in HOL*, FormaliSE 2019, DOI `10.1109/FormaliSE.2019.00020`; Andreas Lööw, *Lutsig: A Verified Verilog Compiler for Verified Circuit Development*, CPP 2021, DOI `10.1145/3437992.3439916`.

### 3. Preserved Executable Verification Probe

- **Script**: `support/verify_hdl_semantics_and_timelines.py` (Python 3.10+, stdlib only).
- **Observed Run (`2026-11-19`)**:
  ```console
  $ python3 -B reports/hardware-description-languages-timing-semantics-and-hw-sw-co-design/support/verify_hdl_semantics_and_timelines.py
  [PASS] 1. SystemVerilog IEEE 1800-2023 Event-Queue & X-Optimism Witnesses:
         blocking_race: order(B1,B2)=(1, 1) != order(B2,B1)=(1, 0)
         nba_confluent: order(B1,B2)=order(B2,B1)=(1, 0)
         x_divergence: if(X,1,0)=0 vs ternary(X,1,0)=X vs kleene=X vs synth(sel=1)=1
  [PASS] 2. Filament Presburger Timeline & II Typechecker:
         valid_mac: PASS
         skew_1cycle: ValidMAC: timeline skew on c_reg2 @[G+2, G+3] -> a0.y @[G+3, G+4] (source must contain destination interval)
         double_booked: DoubleBooked: structural double-booking on shared instance 'sm' (II=2) between u0@G and u1@G+1 under caller II=4 (cyclic gaps 1, 3 < 2)
         wrap_around_clash: WrapClash: structural double-booking on shared instance 'sm' (II=2) between u0@G and u1@G+2 under caller II=3 (cyclic gaps 2, 1 < 2)
  [PASS] 3. Koika EHR Conflict Matrix & ORAAT Serializability:
         ehr_matrix_16_cells: EXACT_MATCH(coq/Logs.v)
         forwarding_case: committed=['exec_stage', 'decode_stage'], next={'buf': 7, 'out': 2}
         conflict_abort_case: committed=['early_p1_reader'], next={'buf': 2, 'out': 0}
         oraat_exhaustive_states: 96/96 PASS
  [PASS] 4. Dahlia Time-Sensitive Affine Bank-Port Checker:
         unroll4_bank4: PASS
         unroll4_bank2_conflict: affine bank conflict on a[2]: bank 0 (mod 2) already consumed in current step
         seq_barrier_refresh: PASS
  ```

## Revalidation

Use narrow discriminating checks rather than repeating the full survey:

1. **Re-run the executable semantic/type-system probe** (<1s, stdlib only):
   ```console
   python3 -B reports/hardware-description-languages-timing-semantics-and-hw-sw-co-design/support/verify_hdl_semantics_and_timelines.py
   ```
   A passing run confirms consistency of the encoded models; it does not check upstream compiler drift.
2. **Diff narrow anchor files against pinned SHAs** when upgrading an upstream system: `mit-plv/koika` (`coq/Logs.v`, `coq/OneRuleAtATime.v`); `ymherklotz/vericert` (`src/Compiler.v`, `src/hls/Verilog.v`); `cucapra/filament` (`crates/filament/src/ir_passes/{interval_check.rs, discharge.rs}`); `llvm/circt` (`include/circt/{Dialect,Conversion}/`); `janestreet/hardcaml` (`kernel/clock_domain.mli`); `clash-lang/clash-compiler` (`Clash/Signal/Internal.hs`, `Clash/Explicit/Synchronizer.hs`); `project-oak/silveroak` (`FullCipherEquiv_Assumptions.out`, `README.md`). For `Spade`, pin a 40-char commit SHA from `https://gitlab.com/spade-lang/spade` once GitLab access is available and audit the `inv &T` linear checker and `pipeline(N)` passes directly.
3. **Re-run differential synthesis/HLS fuzzing** (`Verismith` against current Vivado/Quartus/Yosys) only when fresh quantitative mis-synthesis rates are required; no static check replaces live differential testing of closed-source EDA suites.
