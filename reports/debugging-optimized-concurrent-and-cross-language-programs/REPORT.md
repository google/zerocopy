# Debugging Optimized, Concurrent, and Cross-Language Programs

## Summary

Debugging breaks down across three orthogonal fault lines—aggressive optimization, concurrent/nondeterministic execution, and stackless or polyglot runtimes—because debuggers observe machine artifacts (`rsp`, physical registers, live memory, `.eh_frame`) that compilers, OS schedulers, coroutines, and language runtimes deliberately decouple from source causality:

1. **Optimization Currency & Soundness**: Code motion, DCE, SROA, register coalescing, and tail-call elimination violate *currency* (Hennessy, 1982; Adl-Tabatabai & Gross, 1993/1996), creating `noncurrent-stale` (roll-forward), `noncurrent-premature` (roll-back), `evicted` (nonresident), and path-dependent `suspect` variables. Silent wrong values are strictly worse than `<value optimized out>`: empirical testing campaigns exposed dozens of wrong-value and incompleteness bugs in production GCC, Clang/LLVM, `rustc`, GDB, and LLDB (Li et al., PLDI '20: 47 bugs; Di Luna et al., ASPLOS '21: 34 bugs; Assaiante et al., ASPLOS '23: 24 confirmed of 38 reported). Modern LLVM defends across four layers—non-instruction `#dbg_*` records (`RemoveDIs`), `Assignment Tracking` (`#dbg_assign` + `DIAssignID`), backend `Instruction Referencing` (`DBG_INSTR_REF` + `DBG_PHI` + two-function `LiveDebugValues`), and `Key Instructions` (`atomGroup`/`atomRank` driving DWARF `is_stmt`)—scored by `DExTer`.
2. **One State Relation**: Verified compiler simulation relations, JIT deoptimization maps (Graal `FrameState`/`VirtualObjectNode`, HotSpot `ScopeDesc`, V8 `TranslatedState`, formalized in `sourir` POPL '18 and `CoreJIT` POPL '21), GC stack maps, and sound DWARF v5 location lists (`DW_OP_stack_value`, `DW_OP_implicit_value`, `DW_OP_implicit_pointer`, `DW_OP_entry_value`, `DW_OP_piece`) are four projections of one machine-to-source state relation. JIT deopt guarantees safepoint completeness by blocking DCE of live interpreter state; AOT DWARF keeps zero runtime overhead by permitting partiality. Exporting a verified compiler's simulation witness bridges soundness without runtime cost.
3. **Deterministic Record-and-Replay & Time Travel**: Mozilla's `rr` (O'Callahan et al., USENIX ATC '17) achieves `1.49x`–`1.79x` record and `0.72x`–`1.56x` replay overhead on low-parallelism Linux workloads without kernel patches or binary instrumentation by single-core thread serialization, `seccomp-bpf` + `syscallbuf` + CoW cloning, and deterministic PMU branch counters paired with register/stack digests (`ProtoMark`). `ReplayTimeline` bounds live checkpoints to `O(log T)` via factor-2 exponential spacing; Pernosco indexes `rr` traces offline for `O(log W)` omniscient backward dataflow queries; Hermit (`Reverie` + `Detcore`) provides deterministic execution and `--chaos` schedule search. Hard `rr` walls include external `MAP_SHARED` writers, GPU/RDMA/`io_uring` async rings, broken/absent VM PMUs, AMD Zen `SpecLockMap`, Intel SMI drift, and ARM LL/SC speculative counters.
4. **Async Causality & Polyglot Stack Walking**: Stackless `async` coroutines erase OS `rsp` caller chains across `.await`, requiring event telemetry (`tokio-console`) or intrusive `Pin<&mut Frame>` future trees (`async-backtrace`). Across `Python`/`Rust`/`C++`/`JVM JIT` boundaries, standard `.eh_frame` unwinders fail at interpreter loops (`_PyEval_EvalFrameDefault`), dynamic code arenas, and kernel NMIs, driving frame pointers, Linux `ORC` / userspace `SFrame`, `perf` `jitdump` v2 + CPython per-code-object trampolines, and GDB's `__jit_debug_register_code` / Python `FrameFilter` + `Unwinder` hooks (`libpython.py`).
5. **Executable Probe**: `support/verify_debug_currency_and_replay.py` verifies Hennessy/Adl-Tabatabai-Gross CFG currency classification, `DW_OP_stack_value`/`DW_OP_entry_value` rescue, wrong-value detection, `O(log T)` checkpoint scaling (`7`/`9`/`11` for `1,491`/`5,991`/`23,991` steps), near-crash reverse-watchpoint recovery (`99` steps for distance `79`), omniscient root-cause chaining, and `MAP_SHARED`/DMA divergence detection.

## Applicability

This report synthesizes 15 durable primary subjects listed in `REPORT.json` across four coupled engineering seams:

- **Optimization & debuginfo semantics**: Hennessy (1982), DWARF Version 5 (2017-02-13), Di Luna et al. (ASPLOS '21), Assaiante et al. (ASPLOS '23), and `llvm/llvm-project` (`4f67d9e5e0ce3de41929bae220feb8858b0085b9`) trace the progression from formal currency definitions through empirical defect campaigns to modern LLVM IR/MIR defenses.
- **Unifying state relation**: `oracle/graal` (`c1b06aa797a4aef3ee170f82e508f674a3d2f2f3`), `openjdk/jdk` (`186489b55b5df61e270174a76104a2af27cc7197`), and `v8/v8` (`e88118f63dd96f24a9acb8bd0665e7880063f5c0`) are analyzed for their deoptimization frame-state structures alongside DWARF v5 and verified-compiler simulations.
- **Record-and-replay & deterministic execution**: O'Callahan et al. (USENIX ATC '17, `arXiv:1705.05937v1`) and current `rr-debugger/rr` (`608efe319bbbc4d0f5658d984e16be187801325d`) are compared longitudinally (documenting post-2017 evolution such as AArch64 LSE support and AMD Zen `SpecLockMap` probes) and contrasted with Pernosco and `facebookexperimental/hermit` (`f5430390f6235786bf10dafac78942500766d112`).
- **Async causality & polyglot unwinding**: `tokio-rs/console` (`b59758e5a6effe3a9df3ec84a2f28d319d178234`), `tokio-rs/async-backtrace` (`3dcc5ad3c0c3e2dce2fcf513dcec3ae5448597cb`), `python/cpython` (`441c010fef90ab2860ae8142cbfd1fd52f53ba75`), and `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) characterize Linux x86-64/AArch64 user-space and kernel seams.

**Cross-reference boundary with adjacent corpus packages**:
- Rust-specific DWARF v5 / CodeView binary encoding tables, `rustc` DIE schemas, and debugger pretty-printer contracts live in `rustc-dwarf-codeview-debuginfo-emission-and-debugger-contracts` and `direct-verified-dwarf-v5-and-codeview-debug-section-emitter` and are not duplicated here.
- Native ELF/Mach-O `.eh_frame` CFI and Windows SEH `.pdata`/`.xdata` mechanics live in `unwinding-on-elf-and-macho-targets` and `unwinding-on-windows-targets-and-32bit-seh`; this report covers cross-runtime unwinding seams above them.
- Rust MIR coroutine state-machine lowering (`StateTransform`, `Pin`, discriminants) lives in `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics`; this report covers runtime async causal tree reconstruction.

Concrete PMU hex codes, Linux syscall filters, LLVM flags, and CPython trampoline layouts apply strictly to the pinned revisions and Linux x86-64/AArch64 targets; architectural invariants generalize subject to **Boundaries**.

## Findings

### 1. The Currency Problem Under Optimization: Hennessy (1982) to Adl-Tabatabai & Gross

Basis: normative (DWARF Version 5) + documentation (Hennessy 1982; Adl-Tabatabai & Gross 1993, 1996) + derived + execution (`support/verify_debug_currency_and_replay.py`)

Unoptimized (`-O0`) compilation preserves a near-bijective mapping between source statements $s$ and machine PC ranges, keeping every variable $v$ in a dedicated stack slot updated in source order. Under `-O2`/`-O3`, optimizers preserve only observable I/O and return behavior, freely reordering, eliminating, splitting, or coalescing internal state.

Hennessy (1982, ACM TOPLAS 4(3), pp. 323–344) formalized this **data-value problem** by comparing $v$'s *expected value* (from sequential source execution up to breakpoint $s$) against its *actual value* in machine storage at target instruction $pc \leftrightarrow s$. Adl-Tabatabai & Gross (POPL '93, PLDI '93, PLDI '96) extended the model to global optimizations, global register allocation, and CFG joins. Let $\mathrm{ReachSrc}(s, v)$ be the source definitions of $v$ reaching $s$, $\mathrm{ExecTgt}(pc, v)$ the definitions whose target writes executed before $pc$, and $\mathrm{Owner}(pc, \mathrm{home}(v))$ the logical variable/temporary currently occupying $v$'s storage at $pc$:

| Classification | Formal Condition at $(pc \leftrightarrow s, v)$ | Triggering Optimizations | Debugger Recovery / Semantics |
| :--- | :--- | :--- | :--- |
| **`current`** | $\mathrm{ExecTgt}(pc, v) = \mathrm{ReachSrc}(s, v)$ and $\mathrm{Owner}(pc, \mathrm{home}(v)) = \{v\}$ (or sound DWARF synthesis) | None, or verified DWARF synthesis | Safe to report runtime value directly. |
| **`noncurrent-stale`** *(roll-forward)* | $\exists d \in \mathrm{ReachSrc}(s, v) \setminus \mathrm{ExecTgt}(pc, v)$ with $d \prec_{\text{src}} s$ | DCE, DSE, store sinking, delayed scheduling | Storage holds an older value; recoverable only if omitted RHS inputs remain live (`DW_OP_stack_value`). |
| **`noncurrent-premature`** *(roll-back)* | $\exists d' \in \mathrm{ExecTgt}(pc, v) \setminus \mathrm{ReachSrc}(s, v)$ with $s \preceq_{\text{src}} d'$ | Hoisting, speculative motion, LICM across $s$ | Storage was overwritten early; requires roll-back (impossible without prior backup/logging). |
| **`evicted`** *(nonresident)* | Definition executed on time, but $\mathrm{home}(v) = \bot$ or $\mathrm{Owner}(pc, \mathrm{home}(v)) \neq \{v\}$ | Register coalescing, live-range splitting, caller-saved clobber, tail-call elimination | Value vanished from storage unless rescued by `DW_OP_entry_value` or `DW_OP_stack_value`. |
| **`suspect`** *(path-dependent)* | At a CFG join, $v$ is `current` on one predecessor path and `noncurrent-*`/`evicted` on another | PRE, branch-asymmetric scheduling or coalescing | Static analysis cannot decide currency; truthful debuggers must warn or report `<optimized out>`. |

Two asymmetries govern DWARF v5 location descriptions (`DWARF Version 5`, 2017-02-13):

1. **Truthfulness over availability**: Failing to terminate an old location range after register coalescing, hoisting, or sinking causes the debugger to display a silent wrong value—strictly worse than `<value optimized out>`.
2. **DWARF v5 reconstruction primitives and hard ceiling**:
   - **Implicit locations (Section 2.6.1.1.3)**: `DW_OP_stack_value` treats the top of the DWARF expression stack as the *value* itself rather than an address, reconstructing pure derived variables (e.g., `y = x * 2 + 1` via `DW_OP_breg1 0, DW_OP_lit1, DW_OP_shl, DW_OP_plus_uconst 1, DW_OP_stack_value`). `DW_OP_implicit_value` embeds constant byte blocks; `DW_OP_implicit_pointer` models SROA-eliminated pointers by referencing the target DIE plus offset. All implicit locations are **read-only**.
   - **Entry-value recovery (Section 2.5.1.7)**: `DW_OP_entry_value` evaluates an expression using entry-time register/memory state, resolved via caller `DW_TAG_call_site_parameter` records (Section 3.3.2); indirect calls without call-site info or tail calls break recovery.
   - **Composite locations (Section 2.6.1.2)**: `DW_OP_piece` / `DW_OP_bit_piece` stitch SROA-split structs from register, memory, constant, and empty fragments (`DW_OP_LLVM_fragment(offset_bits, size_bits)` in `llvm/docs/SourceLevelDebugging.md` L144–L155).
   - **Ceiling**: DWARF evaluates only *current* machine state (plus caller call-site constants); it cannot invert lossy transforms (`x & 0`) or recover discarded overwritten values (`noncurrent-premature` without a surviving copy).

### 2. Empirical Debug-Info Failure Campaigns and Modern LLVM Mitigations

Basis: documentation (Li et al. PLDI '20; Di Luna et al. ASPLOS '21; Assaiante et al. ASPLOS '23) + source (`llvm/llvm-project@4f67d9e5e0ce3de41929bae220feb8858b0085b9`)

Because compilers rely on every optimization pass to hand-maintain debug metadata as an unchecked side channel, `-O2`/`-O3` binaries exhibit both **incorrectness** (wrong lines, frames, or values) and **avoidable incompleteness** (variables unnecessarily dropped to `<optimized out>` or absent from DIEs):

| Campaign | Venue & Methodology | Toolchains Tested | Quantitative Findings |
| :--- | :--- | :--- | :--- |
| **Li et al. (2020)** | PLDI '20; *actionable programs* $P_{\langle s, v \rangle}$ checking UB-free variable values at reachable breakpoints against `-O0` | GCC, LLVM/Clang, `rustc` | **47 confirmed bugs** in GCC and LLVM plus additional `rustc` bugs. |
| **Di Luna et al. (2021)** (`Debug^2`) | ASPLOS '21 (`arXiv:2011.13994v2`, DOI `10.1145/3445814.3446695`); differential `-O0` vs. optimized checking invariants over **source lines**, **stack frames**, and **arguments** | LLVM (`clang`/`lldb`), GNU (`gcc`/`gdb`), Rust (`rustc`/`lldb`) | **34 unknown bugs**: **23** LLVM (`clang`/`lldb`), **8** GNU (`gcc`/`gdb`), **3** Rust (`rustc`/`lldb`); **14 fixed** by publication. |
| **Assaiante et al. (2023)** | ASPLOS '23 (`arXiv:2211.09568v1`, DOI `10.48550/arXiv.2211.09568`); 5,000-program census + **3 empirical completeness conjectures** + pass bisection | GCC 4.8–10.3 + trunk (`500d3f0`) / GDB 11.2; Clang 5.0–11.1 + trunk (`c2c977c`) / LLDB 13.0 (x86-64) | **38 reported, 24 confirmed**: **11** `clang` (8 passes), **10** `gcc` (7 transforms), **1** `lldb`, **2** `gdb`; ~50% involved constant-valued variables. |

Assaiante et al.'s three conjectures (`arXiv:2211.09568v1` Section 3.2–3.4) separate avoidable compiler bugs from unavoidable optimization loss without requiring an `-O0` completeness oracle:
- **Conjecture 1 (Call Argument Visibility)**: A variable passed to an *opaque function* (cross-TU or indirect call) must be visible with its value on the call line (20 issues, 14 confirmed; 3.36x more unique violations in GCC than Clang).
- **Conjecture 2 (Constituent Availability)**: On a line assigning to global storage via a non-simplifiable expression, any constituent variable $x$ that is constant or unalterable-and-live-later must be visible (11 issues, 5 confirmed; 3.9x more unique violations in Clang than GCC, prominently `LoopStrengthReduce` salvaging).
- **Conjecture 3 (Decaying Visibility)**: After assignment to a local variable, availability along subsequent stepped lines may only stay constant or monotonically degrade absent reassignment—never `<optimized out>` early and visible later (7 issues, 5 confirmed, e.g., GCC `-Og` `-ftree-ccp` bug 104938 and LLVM SROA bug 54796).

Their 5,000-program census (Section 2, pp. 3–4) further established that variable availability must be multiplied by line-coverage ratio (since `-O2`/`-O3` delete lines where variables are lost), that Clang aliases `-Og` to `-O1` whereas GCC `-Og` retained substantially higher combined coverage, and that fixing one cross-cutting GCC bug closed half the availability gap between `-O1` and `-Og`.

#### Modern LLVM Four-Layer Defense (`llvm/llvm-project@4f67d9e5e0ce3de41929bae220feb8858b0085b9`)

1. **Non-Instruction Debug Records (`RemoveDIs`, `llvm/docs/RemoveDIsDebugInfo.md` L1–L60)**: Replaces `call void @llvm.dbg.*` pseudo-instructions with out-of-band `DbgRecord` objects (`#dbg_value`, `#dbg_declare`, `#dbg_assign`) so debug metadata disappears from basic-block instruction lists and cannot alter pass heuristics or `-g` codegen. `BasicBlock::iterator` carries a 1-bit debug flag (`begin`/`getFirstNonPHIIt`/`getFirstInsertionPt`), and manual instruction moves use `moveBeforePreserving`.
2. **Assignment Tracking (`llvm/docs/AssignmentTracking.md` L1–L233)**: Defers memory-vs-register selection until after middle-end passes by emitting `#dbg_assign(Value, ValueExpr, Variable, DIAssignID, Address, AddressExpr)` linked to stores/allocas via `distinct !DIAssignID()` attachments (Clang default via `-Xclang -fexperimental-assignment-tracking=enabled`, but disabled by default under LTO/ThinLTO and LLDB tuning, L230–L233). Moving or deleting a store requires **no pass changes**: an unlinked `DIAssignID` automatically marks the stack home stale, avoiding wrong values. Store merging calls `Instruction::mergeDIAssignID`; SROA/partial DSE splits `#dbg_assign` with `FragmentInfo` and `Undef` address for dead pieces; a fixed-point dataflow pass lowers surviving locations to MIR `DBG_INSTR_REF`.
3. **Instruction Referencing (`llvm/docs/InstrRefDebugInfo.md` L18–L193)**: Tags defining `MachineInstr`s with `debug-instr-number N` and references them via `DBG_INSTR_REF <instr_num>, <op_num>` (plus `DBG_PHI $reg, <num>` at block entries after `phi-node-elimination`), eliminating expensive `LiveDebugVariables` maintenance during regalloc. In-place mutations call `MachineInstr::dropDebugNumber()` (degrading safely to `<optimized out>`); replacements record `MachineFunction::substituteDebugValuesForInst`. `LiveDebugValues` solves two separate SSA dataflow systems—variables $\to$ values and values $\to$ machine locations via target hooks (`isCopyInstrImpl`, `isLoadFromStackSlotPostFE`, `isStoreToStackSlotPostFE`)—then joins them.
4. **Key Instructions (`llvm/docs/KeyInstructionsDebugInfo.md` L1–L160)**: Reduces stepping jumpiness under scheduling (following Tice & Graham, 2000; enabled via `-gkey-instructions`, DWARF-only, disabled at `-O0`, no CodeView or coroutine support yet per L7–L13). Adds 60-bit `atomGroup` and 3-bit `atomRank` to `DILocation` (sharing a 64-bit word with 1-bit `irlayers`, L48) plus `DISubprogram::keyInstructions`. Clang ranks finalizing atom instructions (stores, branches, EH; calls are always `is_stmt`) as rank 1 and backup RHS instructions at higher ranks; DWARF emission selects the last lowest-rank instruction per `(atomGroup, inlinedAt)` in each basic block and floats `is_stmt` to the top of contiguous same-line instructions. At the pinned revision, LLDB does not yet interpret `is_stmt` (L25).
5. **DExTer Scoring (`cross-project-tests/debuginfo-tests/dexter/dex/heuristic/Heuristic.py` L26–L106, L438–L460)**: Drives LLDB or Visual Studio DTE (GDB unsupported, `README.md` L9) and scores $\text{score} = 1.0 - \min(\sum \text{penalties}, \text{max\_penalty}) / \text{max\_penalty}$, encoding truth-over-availability weights: **incorrect value = `7`**, **missing value = `6`**, **not evaluatable = `5`**, **irretrievable / unreachable / missing step / incorrect state = `4`**, **variable optimized away = `3`**, **misordered values = `3`**, **misordered steps = `2`**.

### 3. The Unifying Structural Insight: One Machine-to-Source State Relation Across Four Subsystems

Basis: source (`oracle/graal@c1b06aa797a4aef3ee170f82e508f674a3d2f2f3`, `openjdk/jdk@186489b55b5df61e270174a76104a2af27cc7197`, `v8/v8@e88118f63dd96f24a9acb8bd0665e7880063f5c0`) + documentation (Hölzle, Chambers & Ungar PLDI '92; Flückiger et al. POPL '18; Barrière et al. POPL '21) + derived

**Verified compiler simulation relations, JIT deoptimization frame-state maps, GC stack maps, and sound DWARF location lists are four projections of one underlying mathematical object**: a partial relation $R_{pc} \subseteq \Sigma_{\text{machine}} \times \Sigma_{\text{source}}$ connecting physical machine state at $pc$ to source activation frames, locals, and virtualized objects.

| Subsystem | Examined Source Artifact | Program Points | Completeness | Optimizer Constraint | Current Soundness Basis |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **AOT Debug Info** | DWARF v5 `.debug_loclists` + `.debug_line` (`llvm/llvm-project`) | Every PC / `is_stmt` | **Partial** (`<optimized out>` allowed; read-only) | **Minimal**: must not inhibit DCE, SROA, or scheduling (`RemoveDIs`) | Unverified; hand-maintained per pass |
| **JIT Deopt Maps** | Graal `FrameState` + `VirtualObjectNode`; HotSpot `ScopeDesc`; V8 `TranslatedState` | Safepoints / speculative guards / call sites | **Total** for all interpreter locals, stack, monitors, and inlined frames | **Strong**: deopt points act as live uses of all interpreter state, blocking DCE and pinning effects | Runtime-critical (bugs cause CVEs); formalized in `sourir` (POPL '18) & Coq-verified in `CoreJIT` (POPL '21) |
| **GC Stack Maps** | HotSpot `OopMap` (`DebugInformationRecorder`), LLVM `gc.statepoint` | Allocation & safepoint calls | **Total** for live managed object pointers | **Moderate**: constrains derived pointers across safepoints | Runtime-critical (missing root causes UAF) |
| **Compiler Simulation** | CompCert `match_states` / translation-validation witnesses | Lock-step or stuttering simulation points | **Total** over proof-relevant state | **Pass-specific**: requires simulation proof or certified checker | Machine-checked in prover, but **discarded** before binary emission |

Production JIT deopt maps directly instantiate the executable version of this relation (originating in Hölzle, Chambers & Ungar, PLDI '92 for SELF, where breakpoints dynamically deoptimized active frames into interpreter activations):
- **Graal (`FrameState.java` L69–L130, `VirtualObjectNode.java`)**: Captures locals, operand stack (`StackState`: `BeforePop`, `AfterPop`, `Rethrow`), monitors, outer inlined `FrameState`s, and `VirtualObjectNode` / `EscapeObjectState` descriptors for scalar-replaced heap objects. Its Javadoc states directly (L73): *"This can be used as debug or deoptimization information."*
- **HotSpot (`scopeDesc.hpp` L38–L148, `debugInfoRec.hpp`)**: Maps `PcDesc` to linked `ScopeDesc` frames (`sender()` walks inlined callers), recording `Method*`, `bci`, `locals()`, `expressions()`, `monitors()`, `should_reexecute()`, `has_ea_local_in_scope()`, and `objects_to_rematerialize(frame&, RegisterMap&)` to materialize escape-analyzed allocations on exit.
- **V8 (`src/deoptimizer/translated-state.h` L45–L130)**: Combines `DeoptimizationFrameTranslation` opcodes with `RegisterValues` into `TranslatedState` $\to$ `TranslatedFrame` $\to$ `TranslatedValue` (`kTagged`, `kInt32`, `kDouble`, `kSimd128`, `kCapturedObject`, `kUniqueCapturedObject`, `kDuplicatedObject`, `kCapturedStringConcat`), exposing `IsMaterializableByDebugger()` (L75) so DevTools inspects scalar-replaced objects directly via deopt metadata.
- **Implication for verified AOT toolchains**: Formalizations (`sourir`, POPL '18; Coq-mechanized `CoreJIT`, POPL '21) prove soundness by elevating assumptions and frame-state maps to first-class IR objects. In AOT verified compilers, each pass's simulation proof (`match_states`) or translation-validation witness already encodes the exact computable map from surviving machine registers/slots/expressions to source variables; projecting that witness into `.debug_loclists` produces **sound-by-construction debuginfo** (eliminating silent wrong values) without sacrificing AOT optimization freedom.

### 4. Deterministic Record-and-Replay and Time-Travel Debugging (`rr`, `Pernosco`, `Hermit`)

Basis: documentation (O'Callahan et al. USENIX ATC '17, `arXiv:1705.05937v1`; Pernosco) + source (`rr-debugger/rr@608efe319bbbc4d0f5658d984e16be187801325d`, `facebookexperimental/hermit@f5430390f6235786bf10dafac78942500766d112`) + execution (`support/verify_debug_currency_and_replay.py`)

#### `rr` Architecture: User-Space Replay Without Kernel Patches or Binary Instrumentation

O'Callahan et al. (USENIX ATC '17, `arXiv:1705.05937v1`) and `rr-debugger/rr@608efe319bbbc4d0f5658d984e16be187801325d` draw the determinism boundary strictly at the Linux user/kernel ABI plus nondeterministic CPU instructions:

1. **Single-Core Serialization (`src/Scheduler.cc`, `src/Scheduler.h` L84)**: All tracee threads are pinned to one logical CPU via `sched_setaffinity` (also stabilizing `CPUID` core-ID queries) and scheduled one at a time for `DEFAULT_MAX_TICKS = 2_500_000` retired conditional branches (~50 ms). Eliminating parallel execution eliminates inter-thread data-race nondeterminism between context switches without memory instrumentation. Under `--chaos` (`src/Scheduler.cc` L38–L95), `rr` assigns low priority (`0.1` per thread, `0.3` main thread) and injects high-priority-only starvation windows across 12 power-of-2 durations (`1 ms`–`2 s`, capped at `20%` runtime) to surface schedule-sensitive bugs during recording.
2. **Syscall Recording, `seccomp-bpf`, and `syscallbuf` (`arXiv:1705.05937v1` Sections 2.3 & 3)**: Trapping every syscall via `ptrace` causes `24.53x` slowdown on `cp` and `4.66x` on `htmltest`. `rr` preloads `librrpreload` to patch syscall sites into a shared in-process `syscallbuf`, installs a `seccomp-bpf` filter allowing buffered syscalls without `ptrace` traps, detects blocking syscalls via `PERF_COUNT_SW_CONTEXT_SWITCHES`, and uses Btrfs/XFS copy-on-write cloning for large file reads/mmaps. Table 1–2 measurements (Skylake quad-core, Fedora 23, Btrfs SSD):

| Workload | Baseline | `rr` Record | `rr` Replay | Single-Core (`taskset`) | Record (no `syscallbuf`) | DynamoRIO-null (DBI floor) | Trace Rate (Compressed) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`cp`** | 1.04 s | **1.49x** | **0.72x** | 0.98x | 24.53x | 1.24x | 19.03 MB/s (+586.14 MB/s cloned) |
| **`octane`** | 32.73 s | **1.79x** | **1.56x** | 1.36x | 2.65x | *crash* | 0.08 MB/s |
| **`htmltest`** | 23.74 s | **1.49x** | **1.01x** | 1.07x | 4.66x | 14.03x | 0.79 MB/s |
| **`sambatest`** | 31.75 s | **1.57x** | **1.23x** | 0.95x | 2.23x | 1.43x | 6.85 MB/s |
| **`make -j8`** | 20.99 s | **7.85x** | **11.93x** | 3.36x | 11.32x | 10.97x | 15.82 MB/s (+5.50 MB/s cloned) |

`make -j8` spawns `2,430` short-lived processes (`>= 80` syscalls before `librrpreload` initializes) and forfeits 8-way parallelism (`3.36x` from `taskset` alone); `cp` replays faster than native (`0.72x`) because emulated syscalls avoid kernel I/O.

3. **Deterministic PMU Counters & `ProtoMark` State Identity (`src/PerfCounters.cc` L224–L310, `src/ReplayTimeline.h` L267–L323)**:
   Asynchronous signal and preemption delivery requires a strictly deterministic counter unaffected by page-fault restarts (which break x86 `instructions retired`) or hardware/SMM interrupt exits (which break total `branches retired`, `arXiv:1705.05937v1` Section 2.4.1–2.4.2). `rr` counts **retired conditional branches (`RCB`)** or taken branches and disambiguates execution points with `ProtoMark = (MarkKey(FrameTime, Ticks, ReplayStepKey), Registers, ReturnAddressList)` (sampling stack words to separate branchless repeated calls with identical GPRs). To absorb PMU interrupt **skid** (late firing by dozens to thousands of branches), replay programs the PMI `skid_size` ticks early, plants a breakpoint at target PC, and steps to the exact `ProtoMark` (Section 2.4.3).

| CPU Lineage (`src/PerfCounters.cc`) | PMU Event & Raw Hex | Semantics | `skid_size` | Critical Quirks (`PerfCounters_x86.h` / `_aarch64.h`) |
| :--- | :--- | :--- | :---: | :--- |
| **Intel Nehalem – Comet Lake** | `BR_INST_RETIRED.CONDITIONAL` (`0x5101c4`) | `PMU_TICKS_RCB` | `100` | Comet Lake+ requires `/sys/devices/cpu/freeze_on_smi = 1` (L476–L510). HLE requires dual counters (`IN_TXCP` to count, non-`IN_TXCP` for PMI) to avoid abort livelock (L551–L580). |
| **Intel Ice Lake – Panther Lake** | `0x5111c4` (Lunar/Arrow `0x100005111c4`; Panther/Darkmont `0x5107c4`) | `PMU_TICKS_RCB` | `100`–`125` | Hybrid P/E cores map per-CPU PMU groups (`core`/`atom`/`lowpower`, L227–L270). |
| **AMD Zen – Zen 5** (`0x17`/`0x19`/`0x1a`) | `EX_RET_COND` (`0x5100d1`) | `PMU_TICKS_RCB \| PMU_SKID_UNBOUNDED` | `10000` | Requires disabling hardware `SpecLockMap` MSR; probes `0x510825` (`SPECLOCKMAPCOMMIT`) with `lock addl` and aborts if nonzero (L442–L474). |
| **ARM Neoverse N1–V3, Cortex-A76/A78/X1/A720** | `BR_RETIRED` (`0x21`) | `PMU_TICKS_TAKEN_BRANCHES` | `1000`–`10000` | ARMv8.1 LSE binaries work, **but LL/SC (`LDXR`/`STXR`) is nondeterministic**; `STREX_SPEC` (`0x6F`) counts *speculative* executions, forcing `reset_arch_extras<ARM64Arch>` to disable it (`if (0)`, L415–L427) and risking silent corruption. Cortex-A55/A75/A520 & Neoverse-E1 count microarchitectural `ISB` as branches and are **unsupported** (L289–L309). |

4. **`O(log T)` Exponential Checkpoints (`src/ReplayTimeline.cc` L1554–L1662)**:
   `ReplayTimeline::discard_past_reverse_exec_checkpoints` maintains an exponential checkpoint ladder (`low_overhead_inter_checkpoint_interval = 500000` µs, `expecting_reverse_exec_inter_checkpoint_interval = 100000` µs, `checkpoint_interval_exponent = 2`): within $[now - \text{base} \cdot 2^k, now]$, at most $k$ checkpoints survive (`0` in the innermost interval before insertion). This bounds live forked checkpoints to $\lceil \log_2(T/\text{base}) \rceil + O(1)$ and keeps reverse jumps of distance $d$ within $O(d)$ forward replay work.

5. **Exact Hardware and OS Walls Where `rr` Breaks**:
   - **External `MAP_SHARED` writers**: Async writes by non-recorded peers or drivers cause replay divergence (`arXiv:1705.05937v1` Section 2.5); `rr` disables PulseAudio/X11 SHM and patches vDSO syscalls, but arbitrary shared-memory peers must be recorded inside the same tree.
   - **GPUs, RDMA, and async kernel rings (`io_uring`, AIO)**: Direct DMA and kernel ring writes bypass syscalls. `src/record_syscall.cc` explicitly rejects them: Nvidia (`0xc020462a`) and RDMA (`0xc0181b01`) ioctls return `-ENOTTY` (L1675–L1679); `io_uring_setup`, `io_setup`, `clone3`, and `close_range` return `-ENOSYS` (L4826–L4837).
   - **Cloud VMs & hypervisor PMUs**: Many VMs hide PMUs; `rr` checks for KVM's `IN_TXCP` re-enable bug (L276–L295), Xen's PMI overcount bug (L297–L440), and VMware's VM-exit clustering distortion (`arXiv:1705.05937v1` Section 5.1).
   - **Nondeterministic instructions**: `RDTSC` is trapped via `prctl(PR_SET_TSC)`; `CPUID` faulting (Linux 4.12+) masks `RDRAND`/`RTM` where supported, and `rr` patches `libstdc++`/`libpthread` sites (`arXiv:1705.05937v1` Section 2.6), but unmasked user `RDRAND`/`RDSEED` or ARM LL/SC still breaks determinism.
   - **Multicore weak-memory races**: Single-core serialization prevents observing hardware memory reorderings (x86-TSO store buffers, Armv8 relaxed atomics).

#### Pernosco (Omniscient Debugging Over `rr`) vs. Hermit (Deterministic Execution)

| Dimension | `rr` (`rr-debugger/rr`) | **Pernosco** (O'Callahan & Huey) | **Hermit** (`facebookexperimental/hermit`) |
| :--- | :--- | :--- | :--- |
| **Mechanism** | Boundary recording (`ptrace` + `seccomp-bpf` + `syscallbuf` + PMU `RCB`) & single-core replay | Offline parallel replay of `rr` trace across checkpoints, building an all-time indexed memory/register/CFG database | Deterministic *execution* container (`Reverie` `ptrace`/seccomp + `Detcore`) virtualizing time, RNG, scheduling, CPUID, namespaces, `/proc/*/mountinfo` |
| **Primary Workflow** | Interactive GDB/LLDB reverse stepping & watchpoints | Instantaneous query-driven backward dataflow ("who wrote this byte?") with zero live re-execution | Repeatable `hermit run`, seeded `--chaos --sched-seed=N` concurrency bug finding, `hermit analyze --search`, experimental `record`/`replay` + `hermit-dap` |
| **Overhead** | ~`1.5x`–`1.8x` record (low-parallelism); ~`0.7x`–`1.6x` replay | `rr` record + parallel offline indexing pass | ~`3x`–`6x` planning budget on default `ptrace` backend (`README.md` L376–L379); experimental `liteinst`/`in-guest-trap`/`kvm` backends |
| **PMU Dependence** | **Mandatory** | Inherited from `rr` | **Optional**: PMU preemption, or `--max-timeslice=disabled` for syscall/thread-point scheduling on PMU-less hosts (`README.md` L37–L38, L353–L355) |
| **Reverse Query Cost** | `O(d)` replay over `O(log T)` checkpoints | `O(log W)` indexed lookup over $W$ writes | Experimental `hermit-dap` `stepBack`/`reverseContinue`; primary strength is forward deterministic schedule exploration |

### 5. Async Task Graphs and Causal Stack Reconstruction

Basis: source (`tokio-rs/console@b59758e5a6effe3a9df3ec84a2f28d319d178234`, `tokio-rs/async-backtrace@3dcc5ad3c0c3e2dce2fcf513dcec3ae5448597cb`) + derived

In synchronous execution, active callers remain chained on the OS stack (`rsp`/`rbp`). Stackless `async` coroutines lower each `async fn` into an anonymous state machine enum (see `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics`): returning `Poll::Pending` pops the OS frame, and later resumption on an executor worker leaves only the executor's `poll()` loop on `rsp`—erasing both spawning parents and sibling futures inside `join!`/`select!`.

Two Tokio architectures recover this causal graph:

1. **Event-Sourced Span Telemetry (`tokio-rs/console`, `console-subscriber/src/lib.rs` L59–L120)**: `ConsoleLayer` intercepts runtime `tracing` spans/events for task spawns, `poll` enter/exit, resource locks/timers, and waker clones/wakes/drops over an `mpsc::Sender<Event>` to a gRPC `Server`. This diagnoses busy-poll stalls and lost-waker deadlocks fleet-wide without halting threads, but tracks only instrumented runtime spans.
2. **Intrusive Future-Tree Traversal (`tokio-rs/async-backtrace`, `backtrace/src/{lib.rs,framed.rs,frame.rs}`)**: `#[async_backtrace::framed]` wraps futures in `Framed<F>` (`framed.rs` L11–L50: `#[pin] future: F`, `#[pin] frame: Frame`, `_pinned: PhantomPinned`). Each `Framed::poll` runs `frame.in_scope(|| future.poll(cx))` using a thread-local `ACTIVE_FRAME: Cell<Option<NonNull<Frame>>>` (`frame.rs` L62–L156): on first poll (`Kind::Uninitialized`), `Frame` links itself as a child of `ACTIVE_FRAME` directly inside the pinned future's memory (zero per-poll heap allocation), or registers as `Kind::Root { mutex: Mutex<()> }` if top-level. `taskdump_tree(wait_for_running_tasks)` walks these intrusive child/sibling links to print the full concurrent **tree** of suspended and `POLLING` futures. Source-documented operational hazards: (a) `taskdump_tree(true)` acquires each root `Mutex<()>` and **can deadlock** if a running task holds a non-async lock also needed by the dumper (`lib.rs` L167–L170); (b) unframed spawned outer blocks force every inner `#[framed]` call onto the global root lock (`lib.rs` L58–L85); and (c) unannotated dependency futures leave gaps in the tree.

### 6. Polyglot Mixed-Runtime Stack Walking (`Python` $\leftrightarrow$ `Rust` $\leftrightarrow$ `C++` $\leftrightarrow$ `JVM JIT`)

Basis: source (`python/cpython@441c010fef90ab2860ae8142cbfd1fd52f53ba75`, `torvalds/linux@4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) + documentation (GDB JIT Interface & Python FrameFilter/Unwinder API; Bastian et al. OOPSLA '19; GNU SFrame) + derived

Mixed `Python -> PyO3/Rust -> C++ -> JNI/JVM JIT` stacks span four incompatible unwinding regimes: AOT native frames (`.eh_frame` or frame pointers), interpreter dispatch loops collapsing logical frames into repeated `_PyEval_EvalFrameDefault` C frames over `_PyInterpreterFrame` linked lists, JIT code regions lacking on-disk ELF unwind tables, and NMI/profiler contexts where DWARF CFI bytecode is too slow or unsafe.

#### Native Unwinding Trade-Offs

| Mechanism | State / Format | Runtime / Space Cost | Unwind Speed & Safety | Limitations |
| :--- | :--- | :--- | :--- | :--- |
| **Frame Pointers** (`-fno-omit-frame-pointer -mno-omit-leaf-frame-pointer`) | Linked `rbp`/`x29` chain | Linux kernel measured ~`3.2%` `.text` growth, `5%`–`10%` worst-case slowdown (`orc-unwinder.rst` L31–L34) | Fastest (`O(depth)`); NMI-safe | Misses interrupted leaf/prologue windows before FP save (L49–L53); sacrifices 1 GPR. |
| **DWARF `.eh_frame` CFI** | Bytecode state machine (`DW_CFA_*`) | Zero `.text` cost | Slow interpreter; unsafe in NMI without verifier. Native precompilation yields **11x–60x** speedup (Bastian et al., OOPSLA '19) | Compiler/asm `.cfi` bugs (Bastian et al.; `orc-unwinder.rst` L104–L110). |
| **Linux Kernel `ORC`** (`Documentation/arch/x86/orc-unwinder.rst`) | Sorted `.orc_unwind_ip` + `.orc_unwind` via `objtool` CFG analysis | Zero `.text` cost; `~2–4 MB` RAM (`~50%` / `+1.3 MB` over `.eh_frame`, L56, L77–L78) | **20x–40x faster** than DWARF unwinder (L71–L74); interrupt-safe | Kernel-only; depends on `objtool` decoding compiler CFG (L123–L128). |
| **Userspace `SFrame`** (`.sframe`, `gas --gsframe`) | Compact table tracking strictly `CFA`, `RA`, and `FP` | Zero `.text` cost; compact ELF section | Fast async/profiler unwinding without bytecode | Backtracing/profiling only—cannot replace `.eh_frame` for C++/Rust exception unwinding (no callee-saved register rules or LSDA). |

#### Bridging Interpreted and JIT Runtimes to `perf` and `GDB`

1. **Linux `perf` `jitdump` v2 (`tools/perf/Documentation/jitdump-specification.txt` L1–L170)**: Append-only binary log (`magic = 0x4A695444` `"JiTD"`, `version = 1`, `CLOCK_MONOTONIC`/TSC timestamps) consumed by `perf inject -j` to synthesize ELF DSOs. Five record IDs: `0: JIT_CODE_LOAD` (code bytes, address, `code_index`, symbol), `1: JIT_CODE_MOVE`, `2: JIT_CODE_DEBUG_INFO` (source lines—normatively required *before* its `JIT_CODE_LOAD`, L135–L136), `3: JIT_CODE_CLOSE`, and `4: JIT_CODE_UNWINDING_INFO` (`unwind_data_size`, `eh_frame_hdr_size`, `mapped_size`, LSB `.eh_frame_hdr` + `.eh_frame`, L149–L170).
2. **CPython Perf Trampolines (`Python/perf_trampoline.c` L1–L130, `Python/perf_jit_trampoline.c` L1–L112, L258–L287)**: Allocates mmap'd arenas of assembly stubs (`Objects/asm_trampoline.S`)—one unique code address per Python code object forwarding to `_PyEval_EvalFrameDefault`. Map mode writes `/tmp/perf-PID.map` and requires `-fno-omit-frame-pointer -mno-omit-leaf-frame-pointer` (L125–L129). `jitdump` mode pads synthetic DSO ranges (`0x50` typical, L43–L56) so `perf inject -j` DSOs never overlap and emits a 20-byte `EhFrameHeader` (`_Static_assert(sizeof(EhFrameHeader) == 20)`, L258–L267) + `JIT_CODE_UNWINDING_INFO` for seamless DWARF unwinding through mixed `Python <-> C/Rust` stacks.
3. **GDB JIT Interface & Python Frame Stitching (`Tools/gdb/libpython.py` L85–L90, L981–L1005, L1722–L1881)**: JITs (LLVM ORC/MCJIT, V8, Wasmtime) expose `__jit_debug_register_code` and linked descriptor `__jit_debug_descriptor` so GDB loads in-memory ELF debuginfo on an internal breakpoint. For interpreters, GDB `gdb.FrameFilter` decorates native frames while `gdb.unwinder.Unwinder` sniffers synthesize `gdb.UnwindInfo` from `gdb.PendingFrame`. CPython's `libpython.py` matches `gdb.NORMAL_FRAME` (rejecting `gdb.INLINE_FRAME`, L1783–L1797) activations of `_PyEval_EvalFrameDefault`, extracts `frame` / `cframe["current_frame"]` (`_PyInterpreterFrame`, `get_pyop` L1866–L1880), and renders `PyFrameObjectPtr` locals interleaved with native frames—unless `-O2`/`-O3` optimizes out `frame`/`cframe` (`is_optimized_out()`, L1870, L1876), silently degrading stitching back to raw C frames.

### 7. Executable Verification Probe Results (`support/verify_debug_currency_and_replay.py`)

Basis: execution (`python3 -B reports/debugging-optimized-concurrent-and-cross-language-programs/support/verify_debug_currency_and_replay.py`) + derived

The standalone Python 3.10+ probe (`0.50 s` on Linux x86-64, stdlib-only) verifies both engines:

**Part 1 — CFG Currency & Differential Wrong-Value Oracle** (4-block diamond `B0 -> {B1, B2} -> B3` with DCE on `b`, hoisting of `s5: d`, sinking of `s3: c` and `s6: m`, `r0` clobber on `x`, and `B2` register coalescing of `k` onto `a`'s `r1`):

| Breakpoint PC (Block) | Var | Raw Storage | Final Class | Path Sensitivity | Result (`x=7, cond=1`) |
| :--- | :---: | :--- | :--- | :--- | :--- |
| `0x104` (`B0`, `s4`) | `a` | `current` | `current` | `definite` | `DW_OP_reg1` (`exp=8, obs=8`) |
| `0x104` (`B0`, `s4`) | `b` | `noncurrent-stale` | **`current`** | `definite` | Rescued via `DW_OP_stack_value` (`r1 << 1`, `exp=16, obs=16`) |
| `0x104` (`B0`, `s4`) | `c` | `noncurrent-stale` | `noncurrent-stale` | `definite` | Soundly `<optimized out>` (`exp=17, obs=None`) |
| `0x104` (`B0`, `s4`) | `d` | `noncurrent-premature` | `noncurrent-premature` | `definite` | Soundly `<optimized out>` (`exp=0, obs=None`) |
| `0x104` (`B0`, `s4`) | `x` | `evicted` | **`current`** | `definite` | Rescued via `DW_OP_entry_value(DW_OP_reg0)` (`exp=7, obs=7`) |
| `0x112` (`B3`, `s8`) | `a` | `evicted` | `evicted` | **`suspect-join`** | Coalesced on `B2` (`exp=8, obs=None`) |
| `0x112` (`B3`, `s8`) | `m` | `noncurrent-stale` | `noncurrent-stale` | **`suspect-join`** | Sunk on `B1` (`exp=14, obs=None`) |

Injecting 3 simulated compiler debuginfo bugs (stale `DW_OP_reg0` for clobbered `x`, un-dropped `DW_OP_reg3` for hoisted `d`, coalesced `DW_OP_reg1` for `a` on `cond=0`) catches all 3 wrong values differentially: `(0x104, d: 0 vs 13)`, `(0x104, x: 7 vs 999)`, `(0x112, a: 8 vs 10)`.

**Part 2 — `rr` Replay, `O(log T)` Checkpoints, Omniscient Indexing, and External-Writer Wall**:

| Workload (`total_iters`) | Crash $T$ | Trace Events | Max Checkpoints | $\lceil \log_2(T/32) \rceil + 3$ | Intervals Scanned | Fault Origin `(step, tid, rcb)` | Reverse Steps | Omniscient Chain |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `500` (far fault) | `1,491` | `3` | **`7`** | `9` | `7` | `(500, tid=1, rcb=1)` | `1,491` | `2` (write $\leftarrow$ syscall) |
| `2,000` (far fault) | `5,991` | `3` | **`9`** | `11` | `9` | `(2000, tid=1, rcb=1)` | `5,991` | `2` (write $\leftarrow$ syscall) |
| `8,000` (far fault) | `23,991` | `3` | **`11`** | `13` | `10` | `(8000, tid=1, rcb=1)` | `23,991` | `2` (write $\leftarrow$ syscall) |
| `8,000` (near, dist `79`) | `23,991` | `3` | **`11`** | `13` | **`2`** | `(23912, tid=1, rcb=1)` | **`99`** (`242x` vs $T$) | `2` (write $\leftarrow$ syscall) |

Each $4\times$ trace growth adds exactly `+2` live checkpoints (`7 -> 9 -> 11`), confirming $\log_2(T)$ scaling; near-crash locality recovers the corrupting write in `99` steps across `2` intervals (`242x` faster than replaying from step `0`); and an unrecorded external `MAP_SHARED`/DMA write at step `120` triggers immediate replay divergence (`True`).

## Boundaries

- **not examined**: Closed-source WinDbg TTD and UndoDB/LiveRecorder internals; GraalVM Truffle AST instrumentation (`InstrumentableNode`/`TruffleInstrument`) and DAP wire schemas; GPU debuggers (`cuda-gdb`, `ROCgdb`) and RTL co-simulation replay; cross-language exception unwinding semantics (covered in `compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026`).
- **unknown**: Quantitative Csmith/SPEC variable-availability deltas for LLVM with both `Assignment Tracking` and `Key Instructions` enabled at `4f67d9e5e0ce3de41929bae220feb8858b0085b9` (Assaiante et al. measured pre-2023 releases); whether unfinished DWARF Version 6 location-on-stack proposals resolve all `Hollow DIE` patterns (e.g., GCC bug 105108).
- **known not to apply**: `rr` cannot expose true multicore weak-memory hardware reorderings (x86-TSO store buffers, Armv8 relaxed atomics) because it serializes threads onto one core; DWARF v5 `DW_OP_stack_value`/`DW_OP_implicit_value` cannot support interactive variable mutation; Linux `ORC` and userspace `SFrame` do not replace `.eh_frame` for C++/Rust exception unwinding.
- **unsupported**: In `rr-debugger/rr@608efe319bbbc4d0f5658d984e16be187801325d`, `io_uring_setup`, `io_setup`, `clone3`, `close_range` (`-ENOSYS`), Nvidia/RDMA ioctls (`-ENOTTY`), unrecorded external `MAP_SHARED` writers, ARM Cortex-A55/A75/A520 & Neoverse-E1 PMUs, and reliable PMU detection of ARM LL/SC; in `llvm/llvm-project@4f67d9e5e0ce3de41929bae220feb8858b0085b9`, Key Instructions for CodeView/coroutines, default Assignment Tracking under LTO/ThinLTO/LLDB tuning, and GDB in `DExTer`; in `facebookexperimental/hermit@f5430390f6235786bf10dafac78942500766d112`, preemption timers, threads, `exec`, static binaries, and `gdbserver` under `liteinst`/`in-guest-trap`.

## Evidence

| Source / Artifact | Immutable Coordinates | Verified Paths / Symbols / Sections |
| :--- | :--- | :--- |
| **Hennessy (1982)** | ACM TOPLAS 4(3), pp. 323–344, DOI `10.1145/357172.357173` | Currency (`current`/`noncurrent`/`endangered`), roll-forward vs. roll-back recovery. |
| **O'Callahan et al. (2017)** | USENIX ATC '17, `arXiv:1705.05937v1`, DOI `10.48550/arXiv.1705.05937` | Sections 2.4–2.6, Section 3 (`seccomp-bpf` + `syscallbuf`), Tables 1–3, Section 5 (HW/OS constraints, ARM LL/SC). |
| **Di Luna et al. (2021)** | ASPLOS '21, `arXiv:2011.13994v2`, DOI `10.1145/3445814.3446695` | `Debug^2` invariants (lines, frames, args); 34 bugs (23 LLVM, 8 GNU, 3 Rust; 14 fixed). |
| **Assaiante et al. (2023)** | ASPLOS '23, `arXiv:2211.09568v1`, DOI `10.48550/arXiv.2211.09568` | Section 2 (5,000-program census), Sections 3.2–3.4 (Conjectures 1–3), Section 5 & Tables 1/3 (38 reported, 24 confirmed). |
| **DWARF Version 5** | DWARF Committee, 2017-02-13 (`dwarfstd.org/doc/DWARF5.pdf`) | Sections 2.5.1.7 (`DW_OP_entry_value`), 2.6.1.1.3 (`DW_OP_stack_value`, `DW_OP_implicit_value`, `DW_OP_implicit_pointer`), 2.6.1.2 (`DW_OP_piece`, `DW_OP_bit_piece`). |
| **`llvm/llvm-project`** | `4f67d9e5e0ce3de41929bae220feb8858b0085b9` | `llvm/docs/{AssignmentTracking,InstrRefDebugInfo,KeyInstructionsDebugInfo,RemoveDIsDebugInfo,SourceLevelDebugging}.md`; `cross-project-tests/debuginfo-tests/dexter/{README.md,dex/heuristic/Heuristic.py}`. |
| **`rr-debugger/rr`** | `608efe319bbbc4d0f5658d984e16be187801325d` | `src/{PerfCounters.cc,PerfCounters_x86.h,PerfCounters_aarch64.h,Scheduler.h,Scheduler.cc,ReplayTimeline.h,ReplayTimeline.cc,record_syscall.cc}`. |
| **`facebookexperimental/hermit`** | `f5430390f6235786bf10dafac78942500766d112` | `README.md` (L1–L400: Reverie/Detcore, backends, `--chaos`, 3–6x budget, `hermit-dap`). |
| **`tokio-rs/console`** | `b59758e5a6effe3a9df3ec84a2f28d319d178234` | `console-subscriber/src/lib.rs` (L59–L120 `ConsoleLayer`). |
| **`tokio-rs/async-backtrace`** | `3dcc5ad3c0c3e2dce2fcf513dcec3ae5448597cb` | `backtrace/src/{lib.rs,framed.rs,frame.rs}` (`#[framed]`, `Framed<F>`, `ACTIVE_FRAME`, `Kind::Root`, `taskdump_tree`). |
| **`python/cpython`** | `441c010fef90ab2860ae8142cbfd1fd52f53ba75` | `Python/{perf_trampoline.c,perf_jit_trampoline.c}` (L1–L130, L258–L287); `Tools/gdb/libpython.py` (L85–L90, L981–L1005, L1722–L1881). |
| **`torvalds/linux`** | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `Documentation/arch/x86/orc-unwinder.rst` (L1–L182); `tools/perf/Documentation/jitdump-specification.txt` (L1–L170). |
| **`oracle/graal`** | `c1b06aa797a4aef3ee170f82e508f674a3d2f2f3` | `compiler/src/jdk.graal.compiler/src/jdk/graal/compiler/nodes/{FrameState.java,virtual/VirtualObjectNode.java}`. |
| **`openjdk/jdk`** | `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/code/{scopeDesc.hpp,debugInfoRec.hpp}`. |
| **`v8/v8`** | `e88118f63dd96f24a9acb8bd0665e7880063f5c0` | `src/deoptimizer/translated-state.h` (L45–L130). |
| **Executable Probe** | `support/verify_debug_currency_and_replay.py` | Executed `python3 -B .../verify_debug_currency_and_replay.py` on 2026-11-19 (Python 3.13, Linux x86-64, exit `0`, `0.50 s`). |

## Revalidation

1. **Re-run the preserved probe**:
   ```console
   python3 -B reports/debugging-optimized-concurrent-and-cross-language-programs/support/verify_debug_currency_and_replay.py --json
   ```
   Verifies currency classification, DWARF synthesis, `O(log T)` checkpoint scaling, near-crash reverse-watchpoint locality, omniscient chaining, and `MAP_SHARED`/DMA divergence in `<1 s`.
2. **Diff `rr` hardware & syscall walls**: Diff `src/{PerfCounters.cc,PerfCounters_x86.h,PerfCounters_aarch64.h,record_syscall.cc,ReplayTimeline.cc}` in `rr-debugger/rr` against `608efe319bbbc4d0f5658d984e16be187801325d` for Zen 6+, ARMv9 non-speculative LL/SC counters, or `io_uring` support.
3. **Diff LLVM debuginfo status**: Diff `llvm/docs/{AssignmentTracking,InstrRefDebugInfo,KeyInstructionsDebugInfo,RemoveDIsDebugInfo}.md` and `Heuristic.py` against `4f67d9e5e0ce3de41929bae220feb8858b0085b9` to check LTO/LLDB Assignment Tracking enablement, coroutine Key Instructions, LLDB `is_stmt` support, and DExTer weights.
4. **Check polyglot unwinding**: Diff `Python/perf_jit_trampoline.c` and `Tools/gdb/libpython.py` against `441c010fef90ab2860ae8142cbfd1fd52f53ba75`, and check kernel `.sframe` integration alongside `orc-unwinder.rst` and `jitdump-specification.txt`.
5. **Re-benchmark empirical availability**: Re-run a `Debug^2`/conjecture differential campaign on newer GCC/Clang/`rustc` builds with `-g -O2 -gkey-instructions`; the preserved probe validates the formal currency and replay models, not live compiler binaries.
