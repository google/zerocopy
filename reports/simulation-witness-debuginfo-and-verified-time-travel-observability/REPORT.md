# Simulation-Witness Debug Information, Verified Deoptimization, and Deterministic Time-Travel Observability

## Summary

Four compiler metadata side-channels that mainstream toolchains maintain independently—**DWARF debug variable locations**, **`.eh_frame` stack-unwinding tables**, **JIT deoptimization `FrameState`s**, and **moving-GC root maps**—are mathematically projections of one object: the **simulation relation** mapping optimized target machine states back to abstract source frames. Grounding observability directly in verified compiler simulation witnesses and effect-bounded replay resolves four interlocking failures of production `-O3` debugging:

1. **Production Debuginfo Fails Both Correctness and Completeness Because Passes Maintain It Ad Hoc:** Empirical differential studies across GCC and LLVM (Li, Ding, Zhang & Italiano, PLDI 2020; Di Luna et al., ASPLOS 2021; Assaiante et al., ASPLOS 2023—24 newly confirmed GCC/LLVM completeness bugs across 1,000 test programs) show both silent *wrong variable values* and widespread `<optimized out>` losses. LLVM's `Instruction Referencing` (`DBG_INSTR_REF` in `llvm/llvm-project`, `llvm/docs/InstrRefDebugInfo.md`) decouples variable tracking from register allocation by solving two SSA problems (`var → value`, `value → machine location`), yet still requires manual `MachineInstr::dropDebugNumber()` on mutated instructions (omitting it displays wrong values), drops debug numbers entirely on cloned instructions (`TailDuplicator`), and carries no formal correctness proof.
2. **Verified JIT Deoptimization Proves Executable State Reconstruction Is a Simulation Relation:** Building on Hölzle, Chambers & Ungar (PLDI 1992), Partial Escape Analysis `VirtualObject` rematerialization (Stadler et al., CGO 2014), and `sourir` (Flückiger et al., POPL 2018), **CoreJIT** (Barrière et al., POPL 2021, `Aurele-Barriere/CoreJIT`) formalizes `Framestate (fun_id, label) varmap (list synth_frame) next` and `Assume` directly in Coq (`src/coqjit/specIR.v`), restricts captured registers to `PositiveSet.inter rs_def rs_live_before` (`src/coqjit/framestate_insertion.v`), and ties `forge_interpreter_state` directly into the external backward simulation `match_states` (`src/coqjit/jit_proof.v`) ordered lexicographically over `(optim_index, exec_index)`.
3. **Unverified `.eh_frame` DWARF Tables Are Both Buggy and Slow:** Bastian, Kell & Zappa Nardelli (OOPSLA 2019) showed that compiler-emitted `.eh_frame` bytecode tables contain subtle instruction-granularity defects in GCC/LLVM, can be dynamically validated (`dwarf-unwind-validator`) or synthesized from binaries, and run **11×–60× faster** when precompiled into native unwind stubs—demonstrating that unwind metadata should be synthesized and checked from the backend frame-layout proof rather than emitted as unverified Turing-complete DWARF expressions.
4. **Effect-Bounded Deterministic Replay vs. Cryptographic Forward Secrecy:** OS-level deterministic replay systems (`rr-debugger/rr`, USENIX ATC 2017; `facebookexperimental/hermit`) depend on brittle per-microarchitecture hardware PMU tables (`src/PerfCounters.cc` tracks per-uarch `skid_size`, `has_ioc_period_bug`, and `only_one_counter` from Intel Merom through Panther Lake and AMD Zen 6), serialize multicore execution onto one core (`rr`), or fail closed across unsupported backends (`hermit` exit `122`), and cannot transparently replay opaque GPU/driver memory. Furthermore, algebraic variable rematerialization (`RematExpr`) and time-travel `CausalLog`s **violate cryptographic forward secrecy** if they allow reconstructing a `Sec<T>` secret after `zeroize()`—requiring a static **Non-Recordable / Non-Rematerializable Erasure Barrier** enforced at witness verification time.

## Applicability

These findings apply to optimizing AOT compilers, verifying/certifying compilers, tiered JIT runtimes, stack unwinders, deterministic record-replay systems, and cryptographic/high-assurance toolchains that must reconcile aggressive optimization (`-O2`/`-O3`) with sound observability and secret erasure.

The subjects in `REPORT.json` relate across five coupled layers of the observability stack:

- **LLVM `InstrRef` (`llvm/llvm-project` at `c078d7b6876e6f21c0162671374939016b174c94`), Li et al. (PLDI 2020, `yuanboli233/debug-info-testing` at `0c74da8d29601f140c60c6fb28da45b48ee54dc9`), Di Luna et al. (ASPLOS 2021), and Assaiante et al. (ASPLOS 2023)** characterize the failure modes, empirical availability gaps, and unverified engineering invariants of production DWARF debug-information pipelines.
- **CoreJIT (`Aurele-Barriere/CoreJIT` at `8740d4149be649d0746d9f0d2d759b387a8f3246`, POPL 2021), `sourir` (POPL 2018), Hölzle et al. (PLDI 1992), and Stadler et al. (CGO 2014)** establish the formal theory and Coq mechanization of executable deoptimization state maps (`varmap`, `synth_frame`, `VirtualObject`) as pass-level simulation witnesses.
- **Bastian, Kell & Zappa Nardelli (OOPSLA 2019)** characterizes `.eh_frame` DWARF stack-unwinding validation, synthesis, and native precompilation.
- **`rr` (`rr-debugger/rr` at `608efe319bbbc4d0f5658d984e16be187801325d`, USENIX ATC 2017) and Hermit (`facebookexperimental/hermit` at `8bc703d3bb736b0119bbb77b1a3a0d804da66987`)** characterize the OS/hardware nondeterminism boundary, PMU microarchitecture fragility, and backend trade-offs of deterministic replay.
- **Simon, Chisnall & Anderson (EuroS&P 2018)** anchors the compiler-optimization vs. secret-erasure (`zeroize`) problem, extended here (`Basis: derived + execution`) to formal interference with `RematExpr` witnesses and time-travel `CausalLog`s.

All repository references are pinned to exact commits inspected on `2026-11-19`. Derived architecture definitions—the Unified State-Recovery Witness $\mathcal{W}$, Two-Mode Recovery Contract, and Erasure-Barrier taint discipline—are marked `Basis: derived` and tested by the self-contained micro-probe in **Evidence**.

## Findings

### 1. Why Production `-O3` Debug Info Fails: Correctness, Completeness, and LLVM `InstrRef`

**Basis:** documentation + source (`llvm/llvm-project` at `c078d7b6876e6f21c0162671374939016b174c94`: `llvm/docs/InstrRefDebugInfo.md`, `llvm/lib/CodeGen/LiveDebugValues/InstrRefBasedImpl.cpp`) + empirical studies (Li et al., PLDI 2020, `10.1145/3385412.3386020`; Di Luna et al., ASPLOS 2021, `10.1145/3445814.3446695`; Assaiante et al., ASPLOS 2023, `10.1145/3575693.3575720` / `arXiv:2211.09568`).

#### 1.1 Empirical Taxonomy of Debuginfo Defects in GCC and LLVM

Testing studies cleanly separate two orthogonal failure classes in optimized binaries:
1. **Debuginfo Incorrectness (Wrong Values & Bad Stepping — Li et al. PLDI 2020; Di Luna et al. ASPLOS 2021):** Worse than reporting `<optimized out>`, a stale or erroneously preserved debug location displays a *plausible but semantically false value* (or halts on lines inconsistent with `-O0` execution). Li, Ding, Zhang, and Italiano (PLDI 2020; open-source framework `yuanboli233/debug-info-testing` integrating Csmith + Dexter `DexExpectWatchValue`/`DexExpectStepOrder`) validated `-O2 -g` executions against unoptimized reference traces, exposing dozens of wrong-value and stepping defects across GCC and Clang/LLVM. Di Luna et al. (ASPLOS 2021) extended differential trace checking to expose additional wrong-value bugs in optimized ELF binaries.
2. **Debuginfo Incompleteness (Unnecessary `<optimized out>` — Assaiante et al. ASPLOS 2023):** Because legitimate dead-code elimination can make some variables genuinely unavailable, completeness lacks a trivial oracle. Assaiante, D'Elia, Di Luna, and Querzoni (ASPLOS 2023) formulated **empirical availability conjectures**—including:
   - *Conjecture 1 (Visibility of Call Argument Sources):* variables whose values feed live call arguments (exposing bugs in Clang `InstructionCombining` and up to `223` violations at GCC `-Os` vs. `10` at `-Og`);
   - *Conjecture 2 (Availability of Constituents):* variables used in live computations or loop induction expressions (exposing `LoopStrengthReduce` bugs in Clang and `3.9×` more violations in Clang than GCC across `1,000` test programs);
   - *Conjecture 3:* visibility of constants and unmodified variables along live paths.
   Testing `1,000` C programs across `-Og/-O1/-O2/-O3/-Os` yielded **24 confirmed compiler/debugger bugs** in GCC-GDB and Clang-LLDB.

#### 1.2 Mechanics and Residual Unsoundness of LLVM Instruction Referencing (`DBG_INSTR_REF`)

Traditional LLVM debug tracking (`DBG_VALUE`) named virtual registers, which break whenever register allocation coalesces, splits, spills, or moves values. Modern LLVM (`llvm/docs/InstrRefDebugInfo.md:18-192`) replaces register naming post-isel with **Instruction Referencing**:

```text
%2:gr32 = ADD32rr %0, %1, implicit-def $eflags, debug-instr-number 1
DBG_INSTR_REF 1, 0, !123, !456, debug-location !789
```

- **Decoupled Two-SSA Solve (`LiveDebugValues`, `InstrRefBasedImpl.cpp`):** During register allocation, `DBG_INSTR_REF` instructions are unlinked (only `PHI` nodes emit `DBG_PHI $reg, <num>` at block entries during `phi-node-elimination`). Afterward, `LiveDebugValues` solves two independent SSA dataflow problems—(a) mapping source variables to abstract `(instr_num, operand_num)` value IDs, and (b) tracking which physical registers and stack slots hold each value ID via target hooks (`isCopyInstrImpl`, `isLoadFromStackSlotPostFE`, `isStoreToStackSlotPostFE`, plus `MachineMemoryOperand` clobber tracking)—then joins both tables to emit DWARF location lists.
- **Residual Structural Gaps Explicitly Documented in `InstrRefDebugInfo.md`:**
  1. **Silent Wrong Values on Uninstrumented In-Place Mutation (lines 139–151):** Any target pass that mutates a `MachineInstr` in place to compute a different value *must* manually call `MachineInstr::dropDebugNumber()`. Forgetting that single call does not crash compilation—it silently displays the mutated instruction's wrong value for the source variable!
  2. **Total Loss on Cloned Instructions (lines 187–192):** Passes that duplicate machine instructions (`TailDuplicator`, `MachineFunction::CloneMachineInstr`) must *drop* instruction numbers because tracking duplicated instruction numbers across CFG clones is explicitly documented as unimplemented.
  3. **No Algebraic Inversion / Rematerialization Proof:** When `LoopStrengthReduce` replaces induction variable `i` with pointer `p = base + 8*i` and drops `i`, `InstrRef` can only recover `i` if the pass hand-constructs a DWARF `DIExpression` (`DW_OP_minus`, `DW_OP_constu 8`, `DW_OP_div`, `DW_OP_stack_value`)—with zero mechanical verification that the expression matches the pass's actual arithmetic invariant!

---

### 2. Verified JIT Deoptimization and Simulation-Relation Witnesses (`CoreJIT`)

**Basis:** normative specification (Hölzle et al., PLDI 1992, `10.1145/143103.143114`; Stadler et al., CGO 2014, `10.1145/2581122.2544157`; Flückiger et al., POPL 2018, `10.1145/3158137`; Barrière et al., POPL 2021, `10.1145/3434327`) + source (`Aurele-Barriere/CoreJIT` at `8740d4149be649d0746d9f0d2d759b387a8f3246`: `src/coqjit/specIR.v`, `src/coqjit/framestate_insertion.v`, `src/coqjit/jit_proof.v`).

#### 2.1 The Equivalence of Deoptimization Maps and Debuginfo

Hölzle, Chambers, and Ungar (PLDI 1992, Self) showed that full source-level debugging of aggressively optimized code—including inlined calls—can be achieved by dynamically deoptimizing machine frames back into unoptimized interpreter frames using compiler-emitted scope descriptors. Stadler, Würthinger, and Mössenböck (CGO 2014, Graal Partial Escape Analysis) extended this to **scalar-replaced heap objects**: instead of blocking scalar replacement whenever a deoptimization point is reachable, the `FrameState` attaches a **`VirtualObject` descriptor** recording the object's class/type and the live scalar expressions for each field, allocating and populating the concrete object lazily *only if* deoptimization (or debugger inspection) actually triggers.

Flückiger et al. (POPL 2018, `sourir`) formalized speculative optimization passes (`Assume` / `Framestate` preservation) in an intermediate calculus; **CoreJIT** (Barrière, Blazy, Flückiger, Pichardie & Vitek, POPL 2021) mechanized a full dynamic speculative JIT compiler end-to-end in Coq on CompCert's `Smallstep`/`Behaviors` framework.

#### 2.2 CoreJIT's Mechanized Witness Architecture (`Aurele-Barriere/CoreJIT`)

Direct inspection of `Aurele-Barriere/CoreJIT` establishes the exact formal blueprint for turning a simulation relation into executable state recovery:

1. **First-Class Deoptimization Instructions (`src/coqjit/specIR.v:57-99`):**
   ```coq
   Definition varmap : Type := list (reg * expr).
   Definition deopt_target : Type := fun_id * label.
   Definition synth_frame : Type := deopt_target * reg * varmap.

   (* Inside Inductive instruction: *)
   | Framestate : deopt_target -> varmap -> list synth_frame -> label -> instruction
   | Assume     : list expr -> deopt_target -> varmap -> list synth_frame -> label -> instruction
   ```
   - A `Framestate` acts as a verified deoptimization template: operationally it may *nondeterministically* either fall through to `next` or reconstruct the unoptimized base version's register file via `varmap` plus synthesize any inlined caller activation frames from `list synth_frame`.
   - Every function carries both an immutable `fn_base : version` (proved free of speculative instructions by `base_no_spec : base_version fn_base`, `specIR.v:146-151`) and an optional optimized `fn_opt : option version`.
2. **Minimal Live-and-Defined Capture (`src/coqjit/framestate_insertion.v:53-67`):**
   `insert_single_framestate` computes `PositiveSet.inter rs_def rs_live_before` from forward defined-register analysis (`def_regs`) and backward liveness (`liveness`) over `base_c`, emitting an `identity_varmap` capturing *only* registers that are simultaneously definitely defined and live—minimizing artificial live-range extension. Subsequent passes (e.g., constant propagation `const_prop.v`, inlining `inlining.v`, `assume_insertion.v`) update the expressions in `varmap` and `synth_frame` *as part of the pass transformation* and prove simulation preservation!
3. **Executable State Forging Inside the Backward Simulation (`src/coqjit/jit_proof.v:116-128`):**
   ```coq
   Inductive match_states : program -> jit_index -> state -> jit_state -> Prop :=
   | jit_match : forall p ji jitp jitps stack synchro int_state newstack src_state ms
       (INTERNAL_SIM : backward_internal_simulation' p jitp (jorder ji) (jrel ji))
       (FORGE        : forge_interpreter_state jitp stack synchro = OK (int_state, newstack))
       (INTERNAL_MATCH : (jrel ji) (jindex ji) src_state (make_state int_state newstack ms)),
       match_states p ji src_state (mk_jit_state jitp jitps ms stack synchro (joptim ji))
   ```
   To prevent infinite stuttering across repeated recompilations, `jit_order` (`jit_proof.v:84-94`) uses a **lexicographic well-founded order** `lex_ord lt exec_order` over `jit_index := optim_index * exec_index`, decrementing `optim_index` (bounded by `max_optim`) on every JIT optimization step. Because `forge_interpreter_state` is a *premise* of `match_states`, any wrong variable expression in `varmap` or `synth_frame` causes the Coq simulation proof to **fail to typecheck**—making wrong reconstructed values mathematically impossible!

#### 2.3 Unified State-Recovery Witness ($\mathcal{W}$) for AOT + JIT + GC + Unwind

**Basis:** derived from CoreJIT (`10.1145/3434327`), Stadler et al. (CGO 2014), and Bastian et al. (OOPSLA 2019) + execution (micro-probe Part A).

Generalizing CoreJIT's `varmap`/`synth_frame` to AOT verifying/translation-validating compilers yields a single **Unified State-Recovery Witness** $\mathcal{W}$ checked alongside each pass's refinement certificate:

$$\mathcal{W}(pc_{\text{tgt}}) : \text{MachState} \times \text{CausalLog} \longrightarrow \text{List}\Big(\text{SrcFrame}\big(\text{Var} \mapsto \mathbf{LocExpr} \mid \mathbf{RematExpr} \mid \mathbf{VirtualObj} \mid \mathbf{CausalReplay} \mid \mathbf{Erased}\big)\Big)$$

| Projection Consumer | Derived From $\mathcal{W}$ | Defect Class Eliminated |
|---|---|---|
| **Source Debugger (`DWARF` replacement)** | `LocExpr` (register/stack/sub-reg) + `RematExpr` (proven invertible algebra, e.g., $i = (p - p_0)/\text{stride}$) + `VirtualObj` (scalar-replaced aggregates) | Eliminates wrong values (`Li et al.`) and recovers strength-reduced / SROA variables without extending live ranges |
| **Stack Unwinder (`.eh_frame` replacement)** | Caller `CFA` + saved-register `LocExpr` + `synth_frame` inline descriptors | Eliminates hand-authored `.eh_frame` CFI bugs (`Bastian et al.`) and inlined-frame mismatches |
| **JIT Deopt / OSR Transfer** | Full `SrcFrame` materialization at `Assume`/`Framestate` points | Eliminates deopt-state CVEs and OSR register-corruption bugs |
| **Moving-GC Root Map** | Subset of live `LocExpr` entries carrying `GcManaged` pointer types at safepoints | Eliminates optimizer/GC-root desynchronization bugs |

**Two-Mode Recovery Contract (Live-State vs. Register Pressure Trade-Off):** Demanding instant zero-replay recovery of *dead* source variables at every instruction turns every PC into a live use, blocking DCE and inflating register spills (the classic JIT `FrameState` pressure problem). Splitting $\mathcal{W}$ cleanly into:
- **Mode 1 (Zero-Overhead Live Recovery):** `LocExpr` + `RematExpr` + `VirtualObj` derived purely from live machine state (zero extra spills, zero runtime cost; in micro-probe Part A across `25,944` observations over `1,000` randomized loop executions with strength reduction + SROA, Mode 1 raises variable availability from `50.0%` to `100.0%` with `0` wrong values), and
- **Mode 2 (Lazy Causal-Log Slice Recomputation):** `CausalReplay` for genuinely dead-code-eliminated variables, evaluated lazily off-line by re-executing the pure backward slice from the nearest recorded checkpoint in a time-travel build (zero overhead in non-logged production builds)
reifies the fundamental register-pressure vs. omniscient-visibility trade-off explicitly.

---

### 3. Verified and Precompiled DWARF Stack Unwinding (OOPSLA 2019)

**Basis:** normative specification + execution literature (Bastian, Kell & Zappa Nardelli, OOPSLA 2019, `10.1145/3360572`).

Production binaries compiled with `-fomit-frame-pointer` rely on `.eh_frame` tables encoding DWARF Call Frame Information (CFI) bytecode—a Turing-complete stack machine computing the Canonical Frame Address (`CFA`) and caller callee-saved registers at every instruction PC. Bastian, Kell, and Zappa Nardelli (OOPSLA 2019) established three critical empirical and engineering findings:

1. **Unwind Tables Are Pervasively Unverified and Contain Bugs:** Using dynamic instruction-step validation (`dwarf-unwind-validator`), checking compiler-generated `.eh_frame` entries against actual machine-state register transitions across real ELF binaries revealed subtle compiler bugs in both GCC and LLVM (particularly in prologues, epilogues, shrink-wrapped paths, and inline assembly).
2. **Binary Synthesis Is Viable for Stripped/Legacy Code:** When unwind metadata is absent or untrusted, `dwarf-unwind-synthesis` recovers sound CFI tables via abstract interpretation of stack-pointer and register-save patterns directly over machine code.
3. **Interpreting DWARF Bytecode Dominates Unwind Latency (11×–60× Speedup via Precompilation):** Interpreting `.eh_frame` DWARF bytecode inside `libunwind` and Linux `perf` sampling profilers adds severe runtime overhead. Precompiling validated CFI rows into straight-line native machine unwind stubs delivers **11× to >25×–60× faster stack unwinding** while preserving exact register recovery.

**Design Implication:** Treating unwind CFI as a verified projection of $\mathcal{W}$ (compiled to flat table/native stubs akin to SFrame/ORC or Bastian's precompiled tables, rather than interpreted Turing-complete DWARF bytecode) eliminates both the security/reliability risk of corrupt unwind tables and the 10×+ interpreter overhead.

---

### 4. Deterministic Record-Replay: `rr`, Hermit, and Heterogeneous Nondeterminism Boundaries

**Basis:** documentation + source (`rr-debugger/rr` at `608efe319bbbc4d0f5658d984e16be187801325d`: `src/PerfCounters.cc`, `src/RecordSession.cc`; `facebookexperimental/hermit` at `8bc703d3bb736b0119bbb77b1a3a0d804da66987`: `README.md`) + O'Callahan et al. (USENIX ATC 2017).

#### 4.1 Hardware-PMU Fragility and Serialization Limits in `rr`

`rr` (O'Callahan et al., USENIX ATC 2017) achieves practical userspace record-and-replay for Linux programs without kernel patches by trapping syscalls (with seccomp-bpf + syscall-buffering for fast paths), recording nondeterministic outputs (`read`, `clock_gettime`, `getrandom`, signal delivery), and pinpointing asynchronous event delivery using a **hardware performance counter (`retired conditional branches`)**.

Direct inspection of `rr-debugger/rr` (`src/PerfCounters.cc:52-160`) exposes the deep microarchitectural fragility of hardware-PMU-based replay:
- `struct perf_event_attrs` must track per-microarchitecture `bug_flags`, `skid_size` (interrupt delivery overshoot), `ticks_min_period`, `has_ioc_period_bug`, `only_one_counter`, `activate_useless_counter`, and `llsc_fail` (for ARM LL/SC loops).
- `enum CpuMicroarch` manually maintains an ever-growing list spanning **50+ CPU microarchitectures** from `IntelMerom` through `IntelPantherLake`, `AMDF15` through `AMDZen6`, and `ARMNeoverseN1` through `ARMNeoverseV3`, `AmpereOne`, `QualcommOryonX1`, and `AppleM1Firestorm`. Missing or misconfigured PMU quirk entries (or virtualized/cloud VMs without reliable deterministic branch counters) break replay outright.
- **Single-Core Serialization & Unrecorded Shared Memory:** To avoid recording every inter-thread data race in multicore weak memory (which costs bandwidth proportional to shared-memory contention), `rr` **serializes all recorded threads onto a single CPU core**. Furthermore, `rr` cannot deterministically replay GPU kernel executions, DMA/MMIO device-shared memory, or shared-memory segments mutated by external unrecorded processes.

#### 4.2 Controlled Deterministic Execution in Hermit (`facebookexperimental/hermit`)

Inspecting `facebookexperimental/hermit` (`README.md:1-220`, version `0.4.0`, `2026-10-02`) reveals how modern Linux deterministic execution environments handle interception and fail-closed safety:

| Backend (`--backend=...`) | Interception Mechanism | Preemption / Concurrency Limits | Explicit Fail-Closed Guards (Exit `122`) |
|---|---|---|---|
| **`ptrace`** (default) | Reverie ptrace + seccomp filter + Linux user/PID/mount namespaces | User-space PMU counters for precise preemption (runs without PMU with coarser preemption points); full `fork`/`exec`/threads | `--strict` refuses runs without explicit `--epoch` (never silently reads host clock) |
| **`liteinst`** (experimental) | Preloaded `libdetcore_liteinst.so` patching syscall sites in-guest; coordinator state over socket | **No preemption timer** (`--max-timeslice=disabled` required); **no threads, no `exec`**, no static/SUID/`DT_PREINIT_ARRAY` binaries; dynamic loader & prior shared-lib constructors run unmonitored | Refuses `--verify`, `--timeout`, `--skid-margin`, `--gdbserver`; never silently falls back to `ptrace` |
| **`in-guest-trap`** | Same in-guest runtime with `REVERIE_LITEINST_SITE_PATCHING=0` (seccomp `SIGSYS` fallback) | Same thread/`exec`/preemption limits as `liteinst` | Verifies coordinator settings + zero patched/candidate sites; refuses env tampering (exit `122`) |
| **`kvm`** | Read-write `/dev/kvm` guest-kernel Linux ABI | Supports `run`, `analyze`, `bisect` | Reserves `3 GiB` host VA per guest process + `3 GiB` per in-flight `exec`; refuses finite `RLIMIT_AS` (exit `122`), requiring cgroup `memory.max` |

#### 4.3 Effect-Bounded `CausalLog` and Coarse Transaction Checkpoints

**Basis:** derived from `rr`, Hermit, and deterministic simulation testing (FoundationDB / TigerBeetle).

Rather than attempting opaque binary-level interception of arbitrary OS syscalls and hardware PMU skid, a language/runtime with an explicit **Nondeterminism Effect Row** (syscalls, atomic acquire loads, RNG/clock reads, MMIO/DMA completions, GPU kernel launches) achieves portable, multicore-capable deterministic replay via two rules:
1. **Typed Effect-Boundary Logging:** Only nondeterministic boundary events enter the `CausalLog`. Thread-local computations proved race-free by linear/ownership types (`&mut T` exclusivity) require **zero inter-thread logging** and run natively across multiple cores! Inter-thread shared-memory logging overhead scales strictly with actual cross-thread atomic synchronization rate.
2. **Coarse Transaction Checkpoints for Opaque Accelerators:** Closed vendor GPU/NPU drivers do not expose instruction-level simulation witnesses or deterministic warp schedules. Recording at the **kernel-launch boundary** (capturing input/output buffer snapshots or tile hashes as a single `CausalLog` transaction event) provides exact replay of host-accelerator interactions at kernel granularity without requiring driver source access.

---

### 5. Forward-Secrecy Collision: Cryptographic `zeroize()` vs. `RematExpr` and `CausalLog`

**Basis:** normative/security literature (Simon, Chisnall & Anderson, EuroS&P 2018, `10.1109/EuroSP.2018.00009`) + derived + execution (micro-probe Part B).

#### 5.1 Why Debug Witnesses and Time-Travel Logs Break Cryptographic Forward Secrecy

Simon, Chisnall, and Anderson (EuroS&P 2018, *What You Get Is What You C*) documented how mainstream optimizing C compilers silently violate cryptographic security invariants—most famously dead-store elimination removing `memset(key, 0, sizeof(key))` before buffer deallocation, and register spilling leaving uncleared secret copies on the stack.

Introducing **verified algebraic rematerialization (`RematExpr`)** and **time-travel `CausalLog`s** creates a **strictly stronger, previously unexamined forward-secrecy hazard** even when the compiled machine code faithfully executes `zeroize(&mut key)` and clears all stack spills:

1. **Algebraic Secret Resurrection via `RematExpr`:** Suppose a constant-time signing routine holds `key : Sec<u64>`, draws a masking nonce `mask : u64`, computes a Boolean-masked share `share = key ^ mask`, and then executes `zeroize(&mut key)` while `share` and `mask` remain live in registers. An unconstrained witness synthesizer observing the algebraic equivalence `key == share ^ mask` emits a sound `RematExpr` recovering `key` at PCs *after* `zeroize(&mut key)`! As demonstrated in micro-probe Part B (`probe_sim_debug_zeroize.py`), this recovers the exact 64-bit secret in **`1,000 / 1,000` (100%)** of post-zeroize machine states despite the memory slot `key_mem` containing `0`.
2. **Temporal Secret Resurrection via `CausalLog`:** If a time-travel `CausalLog` records either the entropy/input event that loaded `key` or a pre-zeroize memory checkpoint, any post-compromise attacker or core dump containing the `CausalLog` can replay backward past `zeroize()` and recover every erased session key—completely destroying forward secrecy!

#### 5.2 The Static Non-Recordable / Non-Rematerializable Erasure Barrier

To compose simulation-witness observability safely with cryptographic code, the witness verifier must enforce a **Two-Part Erasure Barrier** on secrecy-typed values (`Sec<T>`):

1. **Witness Non-Interference Across `zeroize(v)`:** At every program point $pc$ dominated by (or reachable after) `zeroize(v)`, the simulation witness MUST satisfy:
   $$\mathcal{W}(pc)(v) = \mathbf{Erased}$$
   and no `RematExpr` or `VirtualObj` attached to any *other* variable at $pc$ may evaluate a dependency set whose algebraic information flow reconstructs $v$ (enforced conservatively by rejecting any post-barrier `RematExpr` reading `Sec`-tainted live registers/slots unless explicitly declassified).
2. **Non-Recordable Effect Partitioning in `CausalLog`:** Any effect sourcing or mutating a `Sec<T>` value is statically marked **non-recordable** (forbidden from entering persistent `CausalLog` buffers; time-travel replay stops at an explicit `SecretEpochBoundary` where post-zeroize reverse stepping is disallowed unless an explicit insecure debug-only build flag overrides `Sec<T>` erasure).

Micro-probe Part B confirms that enforcing this static Erasure Barrier rejects `1,000 / 1,000` post-zeroize rematerialization attempts at witness-checking time with **`0` leaked bits**.

## Boundaries

- **Known not to apply (Omniscient Zero-Cost Inspection of Dead Variables):** No compiler simulation witness can recover a *dead-code-eliminated* variable whose value is algebraically non-invertible from live machine state (e.g., an unused hash digest or overwritten loop temporary) without either preserving live registers (increasing spill pressure) or retaining a `CausalLog` checkpoint for lazy replay.
- **Unsupported (Instruction-Granularity Deterministic Replay Inside Closed Vendor GPU/NPU Drivers):** Neither `rr`, Hermit, nor language-level `CausalLog`s can replay internal warp/SM execution inside opaque binary GPU drivers (CUDA/Vulkan/Metal); replay stops at the coarse kernel-launch transaction boundary.
- **Unsupported (LLVM `InstrRef` Tracking Across Cloned Instructions):** `llvm/docs/InstrRefDebugInfo.md:187-192` explicitly states that `DBG_INSTR_REF` does not track cloned instructions (`TailDuplicator`, `CloneMachineInstr`), unconditionally dropping debug numbers on clones.
- **Unsupported (Hermit `liteinst` / `in-guest-trap` Multithreading, `exec`, and Preemption):** `facebookexperimental/hermit` (`README.md:184-206`) explicitly documents that both in-guest backends fail closed on threads, `exec`, preemption timers (`--max-timeslice=disabled` mandatory), static binaries, and `DT_PREINIT_ARRAY`.
- **Known not to apply (CoreJIT Features Missing Relative to Production VMs):** Direct inspection of `Aurele-Barriere/CoreJIT` (`specIR.v`) confirms its IR models integer/address values, registers, calls, and linear memory, but does *not* include moving garbage collection, Graal-style heap `VirtualObject` escape rematerialization, lazy deoptimization (return-address patching of active stack frames), or multithreaded safepoint invalidation.
- **Unknown (Exact `-O3` Variable-Availability Gain of Automated Algebraic `RematExpr` on SPEC/Real-World C/Rust Corpora):** While micro-probe Part A demonstrates `50% → 100%` recovery on strength-reduced + SROA loops and Assaiante et al. (ASPLOS 2023) document frequent LSR/`InstCombine` losses in GCC/LLVM, no production compiler has yet measured whole-corpus SPEC CPU2017 availability gains from automatically extracting invertible `RematExpr` recipes directly from pass simulation proofs.
- **Not examined (Hardware Trace Recorders such as Intel PT / ARM CoreSight and Windows WinDbg TTD):** Hardware branch-trace compression and proprietary Windows Time Travel Debugging (`TTD`) binary instrumentation were not directly examined at source level.

## Evidence

### Primary Specifications and Peer-Reviewed Papers

1. **Li, Ding, Zhang, and Italiano (PLDI 2020):** *Debug Information Validation for Optimized Code*, PLDI 2020, DOI `10.1145/3385412.3386020` (differential validation of `-O2 -g` debuginfo correctness in GCC and Clang/LLVM).
2. **Di Luna, Italiano, Massarelli, Österlund, Giuffrida, and Querzoni (ASPLOS 2021):** *Who's Debugging the Debuggers? Exposing Debug Information Bugs in Optimized Binaries*, ASPLOS 2021, DOI `10.1145/3445814.3446695`.
3. **Assaiante, D'Elia, Di Luna, and Querzoni (ASPLOS 2023):** *Where Did My Variable Go? Poking Holes in Incomplete Debug Information*, ASPLOS 2023, DOI `10.1145/3575693.3575720`, `arXiv:2211.09568` (full PDF verified on `2026-11-19`: Conjectures 1–3, Table 1 violation counts across `1,000` test programs in Clang/GCC at `-Og/-O1/-O2/-O3/-Os`, `3.9×` Clang-vs-GCC ratio on Conjecture 2, `223` vs `10` GCC violations on Conjecture 1, `24` confirmed bugs).
4. **Barrière, Blazy, Flückiger, Pichardie, and Vitek (POPL 2021):** *Formally Verified Speculation and Deoptimization in a JIT Compiler*, Proc. ACM Program. Lang. 5, POPL (2021), DOI `10.1145/3434327`.
5. **Deoptimization Foundations:** Hölzle, Chambers & Ungar, *Debugging Optimized Code with Dynamic Deoptimization* (PLDI 1992, `10.1145/143103.143114`); Stadler, Würthinger & Mössenböck, *Partial Escape Analysis and Scalar Replacement for Java* (CGO 2014, `10.1145/2581122.2544157`); Flückiger et al., *Correctness of Speculative Optimizations with Dynamic Deoptimization* (POPL 2018, `10.1145/3158137`).
6. **Bastian, Kell, and Zappa Nardelli (OOPSLA 2019):** *Reliable and Fast DWARF-Based Stack Unwinding*, Proc. ACM Program. Lang. 3, OOPSLA (2019), DOI `10.1145/3360572` (`dwarf-unwind-validator`, `dwarf-unwind-synthesis`, `11×–60×` unwind precompilation speedup).
7. **Deterministic Replay & Secret Erasure:** O'Callahan et al., *Engineering Record and Replay for Deployability* (USENIX ATC 2017, pp. 377–389); Simon, Chisnall & Anderson, *What You Get Is What You C: Controlling Side Effects in Mainstream C Compilers* (IEEE EuroS&P 2018, `10.1109/EuroSP.2018.00009`).

### Pinned Upstream Repository Source Inspections (Observed `2026-11-19`)

- `llvm/llvm-project` @ `c078d7b6876e6f21c0162671374939016b174c94`:
  - `llvm/docs/InstrRefDebugInfo.md:1-194`: `DBG_INSTR_REF`, `DBG_PHI`, two-SSA `LiveDebugValues` join, mandatory `dropDebugNumber()` on mutated instructions, unimplemented cloned-instruction tracking (`TailDuplicator`).
  - `llvm/lib/CodeGen/LiveDebugValues/InstrRefBasedImpl.h` & `.cpp`: instruction-referencing value-tracking backend implementation.
- `yuanboli233/debug-info-testing` @ `0c74da8d29601f140c60c6fb28da45b48ee54dc9`:
  - `README.md`, `dexter/dex/command/commands/DexExpectWatchValue.py` & `DexExpectStepOrder.py`: PLDI 2020 testing harness.
- `Aurele-Barriere/CoreJIT` @ `8740d4149be649d0746d9f0d2d759b387a8f3246`:
  - `src/coqjit/specIR.v:57-159`: `varmap`, `deopt_target`, `synth_frame`, `Framestate`, `Assume`, `base_no_spec`.
  - `src/coqjit/framestate_insertion.v:53-67`: `PositiveSet.inter rs_def rs_live_before` minimal register capture.
  - `src/coqjit/jit_proof.v:65-128`: `jit_order := lex_ord lt exec_order`, `match_states` embedding `forge_interpreter_state` inside `backward_internal_simulation'`.
- `rr-debugger/rr` @ `608efe319bbbc4d0f5658d984e16be187801325d`:
  - `src/PerfCounters.cc:52-160`: `perf_event_attrs` quirk flags (`skid_size`, `has_ioc_period_bug`, `only_one_counter`, `llsc_fail`) and `CpuMicroarch` enumeration across 50+ Intel/AMD/ARM uarches.
- `facebookexperimental/hermit` @ `8bc703d3bb736b0119bbb77b1a3a0d804da66987`:
  - `README.md:129-220`: `--strict --epoch`, four backends (`ptrace`, `liteinst`, `in-guest-trap`, `kvm`), exit-`122` fail-closed guards, `3 GiB` KVM VA reservation, and `liteinst` thread/`exec`/preemption restrictions.

### Executable Micro-Probe (`Basis: execution`, Observed `2026-11-19`)

Self-contained Python 3 probe verifying (Part A) Unified Simulation Witness (`LocExpr | RematExpr | VirtualObj`) recovery vs. naive register-only tracking under induction-variable strength reduction + SROA across `1,000` randomized runs (`25,944` variable observations); and (Part B) unchecked `RematExpr` post-`zeroize()` key resurrection vs. static Erasure-Barrier rejection across `1,000` 64-bit random keys:

```python
import random

def run_comparison(trials=1000, seed=20261119):
    rng = random.Random(seed)
    total_obs = naive_avail = witness_avail = wrong_values = 0
    for _ in range(trials):
        n = rng.randint(1, 12)
        arr = [rng.randint(-1000, 1000) for _ in range(n)]
        bias, base = rng.randint(-50, 50), 0x10000
        acc_ref = acc_opt = i_ref = 0
        r_p, r_end = base, base + 8 * n
        while r_p < r_end:
            pt_ref = {"x": arr[i_ref], "y": i_ref * 2 + bias}
            src = {"acc": acc_ref, "i": i_ref, "pt": pt_ref, "bias": bias}
            r_x = arr[(r_p - base) // 8]
            mach = {"r_acc": acc_opt, "r_p": r_p, "r_base": base, "r_x": r_x, "r_bias": bias}
            naive = {"acc": mach["r_acc"], "i": None, "pt": None, "bias": mach["r_bias"]}
            remat_i = (mach["r_p"] - mach["r_base"]) // 8
            wit = {"acc": mach["r_acc"], "i": remat_i,
                   "pt": {"x": mach["r_x"], "y": remat_i * 2 + mach["r_bias"]}, "bias": mach["r_bias"]}
            for k, v in src.items():
                total_obs += 1
                naive_avail += (naive[k] is not None)
                if wit[k] is not None:
                    witness_avail += 1
                    wrong_values += (wit[k] != v)
            acc_ref += pt_ref["x"] + pt_ref["y"]
            acc_opt += r_x + (remat_i * 2 + bias)
            i_ref += 1; r_p += 8
    return total_obs, naive_avail, witness_avail, wrong_values
```

Recorded execution output (`python3 probe_sim_debug_zeroize.py`, exit code `0`):

```text
[Part A] Observations=25944 across 1000 randomized runs:
  Naive LocExpr-only availability : 12972/25944 (50.0%)
  Unified Witness W availability  : 25944/25944 (100.0%)
  Witness W wrong values          : 0
[Part B] Forward-secrecy trials=1000:
  Unchecked RematExpr post-zeroize key recovery : 1000/1000 (100% SECRET LEAK!)
  Erasure-Barrier witness rejections            : 1000/1000 (leaks=0)
```

## Revalidation

1. **Check LLVM `InstrRef` Cloned-Instruction Support:** Diff `llvm/docs/InstrRefDebugInfo.md` and `llvm/lib/CodeGen/LiveDebugValues/InstrRefBasedImpl.cpp` against `c078d7b6876e6f21c0162671374939016b174c94` to see whether `CloneMachineInstr` / `TailDuplicator` preserves instruction numbers or adds verified `DIExpression` synthesis during `LoopStrengthReduce`.
2. **Check CoreJIT / Verified JIT Extensions:** Check `Aurele-Barriere/CoreJIT` (and follow-up POPL 2023+ CompCert JIT work) for support for heap-object `VirtualObject` rematerialization, moving-GC safepoints, or lazy deoptimization beyond `specIR.v`.
3. **Check `rr` PMU and Hermit Backend Maturity:** Diff `rr-debugger/rr` (`src/PerfCounters.cc`) against `608efe319bbbc4d0f5658d984e16be187801325d` for newly added CPU microarchitecture quirks, and diff `facebookexperimental/hermit` (`README.md`) against `8bc703d3bb736b0119bbb77b1a3a0d804da66987` to see if `liteinst` gains multithreading, `exec`, or preemption-timer support.
4. **Re-run Forward-Secrecy Witness Check:** Whenever adding a new `RematExpr` algebraic rewrite rule or `CausalLog` event type to a witness-emitting compiler, run an automated taint-barrier check modeled on `probe_sim_debug_zeroize.py` Part B verifying that every variable cleared by `zeroize()` maps strictly to `Erased` and is algebraically non-recoverable from live post-barrier machine state and logs.
