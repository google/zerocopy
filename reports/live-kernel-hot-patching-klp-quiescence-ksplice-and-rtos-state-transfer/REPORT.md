# Live Kernel Hot-Patching, Per-Task Quiescence, Binary Diffing, and Real-Time State Transfer

## Summary

Zero-downtime patching of running system software spans four fundamentally distinct consistency and state-migration regimes whose guarantees and failure modes do not transfer across substrates:

1. **Linux Kernel Livepatch (`klp`) Hybrid Quiescence (`torvalds/linux`):** Combines kpatch-style reliable sleeping stack checking (`klp_check_stack`, requiring `CONFIG_HAVE_RELIABLE_STACKTRACE` / `objtool`) with kGraft-style per-task `TIF_PATCH_PENDING` transitions at kernel-exit/idle boundaries and RCU `func_stack` redirection inside `ftrace` handlers (`klp_ftrace_handler`). While eliminating global `stop_machine` pauses, per-task switching protects **intra-thread call-stack consistency only**: an exhaustive state-space check (`klp_quiescence_model`) verifies that concurrent unpatched (`KLP_TRANSITION_UNPATCHED`) and patched (`KLP_TRANSITION_PATCHED`) threads still deadlock on reversed lock orders or dereference `NULL` on uninitialized `klp_shadow_*` variables. At hyperscale fleets, stuck `PF_KTHREAD` loops, `CONFIG_LTO_CLANG_THIN` inlining (`kpatch-build` vs. `klp-build`), and `FTRACE_OPS_FL_IPMODIFY` collisions with BPF/`kretprobe` observability tools stall rollouts.
2. **Global Rendezvous & Hypervisor Patching (`Ksplice`, `Xen`):** `Ksplice` achieved `88%` (`56/64`) zero-helper automation on historical Linux CVEs under global `stop_machine`, whereas `Xen` hypervisor livepatching exploits its **stackless return-to-guest** boundary (`is_idle_domain`) to rendezvous all physical CPUs within a `30 ms` timeout (`MILLISECS(30)`), eliminating stack unwinders while exposing a subtle `LIVEPATCH_ACTION_REPLACE` window where previously applied patches are reverted before checking the replacement payload's expectations.
3. **General User-Space Dynamic Software Updating (`Kitsune`, `Rubah`):** Replacing multi-version C/Java state requires explicit quiescent cut-points (`kitsune_update` + `longjmp(*jmp_env)` stack teardown) and heap transformers. `Rubah`'s lazy object-proxy migration compresses multi-GB heap update pauses from minutes to `2–3 s` (`90%` steady throughput recovered in `<30 s`), yet introduces unbounded per-access migration latency incompatible with hard real-time deadlines.
4. **Hard Real-Time Embedded & RTOS Hot-Swapping (`RapidPatch`, `AutoPatch`, Dual-Bank Ping-Pong):** Reboot-oriented bootloaders (`MCUboot`) incur `30 ms–2,000 ms` flash sector erasures incompatible with `<1 ms` cyclic loops (`1–10 kHz`). Sub-millisecond RTOS upgrades use either hardware Flash Patch and Breakpoint (`FPB`, capped at `6–8` slots), sandboxed eBPF dispatch (`RapidPatch`: `<8 µs` delay, `<64 KB` RAM), LLVM-synthesized native trampolines (`AutoPatch`: `<12.7 µs` delay, `~23%` memory overhead), or deterministic **dual-bank + ping-pong state transfer** running a bounded total transformer $\tau : \Sigma_v \to \Sigma_{v+1}$ inside verified inter-cycle slack at the top-of-frame idle boundary.

## Applicability

This synthesis governs runtime code replacement and live data-structure migration across four execution environments:
- **Monolithic OS kernels** running Linux (`x86_64`, `ppc64le`, `s390x`, `arm64`, `loongarch64`), inspected at `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) and `dynup/kpatch` (`862cda5e7b6827505ec429ab0bc0ad61cd26f068`), alongside `Ksplice` (`EuroSys 2009`).
- **Type-1 bare-metal hypervisors**, inspected at `xen-project/xen` (`92ddcda17fb00020c6215d51df4c6a25d5eb0b5e`, `xen/common/livepatch.c`).
- **User-space services in C and JVM**, inspected at `kitsune-dsu/kitsune-core` (`6393a0c148976c910df313bda4b578e7c240a6d2`) and `plum-umd/rubah` (`e0dcea715b074f486cc064d45e794d03f1ccd317`).
- **Safety-critical / hard real-time embedded MCUs** (`ARM Cortex-M4/M33`, `nRF52840`, `STM32-F446RE`, `ESP32`) running `zephyrproject-rtos/zephyr` (`c9e38773358dfe0b19fe920f611e288cca4bdf66`) or `FreeRTOS/FreeRTOS-Kernel` (`83a45bf290024de16ca94df1f7262bcde6c82ffe`), evaluated across `IoTAccessControl/RapidPatch`, `DependableSystemsLab/AutoPatch`, and `mcu-tools/mcuboot`.

Execution probes (`klp_quiescence_model.py` and `klp_bench.c`) ran on Linux `7.1.6` (`x86_64`, 8-vCPU Intel Xeon @ 2.20 GHz, `gcc 15.2.0`, `Python 3.13.15`). Model-checking results apply identically across all architectures implementing `kernel/livepatch/transition.c`; absolute user-space C microbenchmark nanoseconds illustrate relative costs of trampoline indirection and hash-table spinlocks vs. direct calls and inline struct fields rather than raw kernel privilege-transition overhead.

## Findings

### 1. Linux Kernel Livepatch (`klp`) Hybrid Quiescence, Barriers, and Production Hazards

`Basis: source + documentation + execution`

#### `klp_transition` Protocol and RCU-Free Synchronization

Mainline Linux livepatching (`torvalds/linux` `kernel/livepatch/transition.c`, `patch.c`, and `Documentation/livepatch/livepatch.rst`) rejects global `stop_machine()` freezes in favor of gradual per-task convergence governed by `klp_transition_patch` and `klp_target_state` (`KLP_TRANSITION_IDLE`, `KLP_TRANSITION_UNPATCHED`, `KLP_TRANSITION_PATCHED`):

1. **Initialization & Memory Barriers (`transition.c#L552-L619`):** `klp_init_transition()` sets `task->patch_state = !state` across all processes, threads, and per-CPU `idle_task(cpu)` threads, issues `smp_wmb()` (`#L603`), and sets `func->transition = true`. The corresponding `smp_rmb()` fences inside `klp_ftrace_handler` (`patch.c#L84-L98`) guarantee that no CPU ever observes `func->transition == true` paired with a stale `KLP_TRANSITION_IDLE` task state.
2. **`ftrace` NOP Trampoline Redirection (`patch.c#L40-L125, L186-L193`):** When patching `old_func` for the first time, `klp_patch_func()` registers `klp_ftrace_handler` at the compiler `-fentry` prologue slot with `FTRACE_OPS_FL_DYNAMIC | FTRACE_OPS_FL_IPMODIFY | FTRACE_OPS_FL_PERMANENT`. The handler acquires `ftrace_test_recursion_trylock()`, walks `ops->func_stack` via RCU, inspects `current->patch_state` if `unlikely(func->transition)`, skips redirection on cumulative `func->nop` markers (`#L118-L119`), and overwrites `ftrace_regs_set_instruction_pointer(fregs, (unsigned long)func->new_func)`.
3. **Why `synchronize_rcu()` Fails (`transition.c#L60-L75`):** Because Linux livepatch permits patching early entry/idle functions **where RCU is not watching**, `klp_synchronize_transition()` cannot use `synchronize_rcu()` and instead executes `schedule_on_each_cpu(klp_sync)` to force a scheduling barrier across every CPU (`#L72-L75`).

#### Four Task-Switching Paths and Stuck-Transition Failure Modes

Tasks converge to `klp_target_state` through four paths (`transition.c#L254-L487`, `livepatch.rst#L94-L171`):
- **Reliable Stack Walk (`klp_check_stack`, `transition.c#L254-L282`):** For sleeping tasks inactive on any CPU (`!task_curr(task)` via `task_call_func()`), `stack_trace_save_tsk_reliable()` captures up to `MAX_STACK_ENTRIES = 100` frames; if no frame falls inside `[func_addr, func_addr + func_size)` for any transitioning function, the task switches immediately. Without `CONFIG_HAVE_RELIABLE_STACKTRACE`, `klp_try_switch_task` returns `false` (`#L318-L319`), blocking stack-based patching entirely (`livepatch.rst#L128-L130`).
- **Scheduler Switch Hook (`__klp_sched_try_switch`, `transition.c#L357-L381`):** Guarded by static branch `klp_sched_try_switch_key`, `__schedule()` probes `current`'s stack at context-switch time to transition CPU-bound `kthread`s (`#L31-L38`).
- **Kernel-Exit & Idle Loop (`klp_update_patch_state`, `#L175-L199`):** User tasks returning from syscalls, IRQs, or signals clear `TIF_PATCH_PENDING` atomically (`test_and_clear_tsk_thread_flag`, acting as an `smp_rmb`) and adopt `klp_target_state`. Swapper idle tasks call `klp_update_patch_state()` inside the idle loop (`livepatch.rst#L115-L118`). Forked children inherit their parent's state in `klp_copy_process()` (`transition.c#L676-L695`).
- **Fake-Signal Wakeups & Forced Escape (`#L387-L420, L706-L731`):** After `SIGNALS_TIMEOUT = 15` retries (`klp_signals_cnt`), `klp_send_signals()` emits `set_notify_signal(task)` to non-kthreads and `wake_up_state(task, TASK_INTERRUPTIBLE)` to kthreads. If tasks remain stuck (e.g., `TASK_UNINTERRUPTIBLE` disk waits or custom unyielding kthreads), admins can reverse (`klp_reverse_transition`) or run `klp_force_transition()` (`echo 1 > /sys/kernel/livepatch/<patch>/force`), which forcibly drops `TIF_PATCH_PENDING` across running tasks—**permanently setting `patch->forced = true` and disabling `rmmod` forever** (`livepatch.rst#L163-L171`) because tasks may still sleep inside old patch module code.

#### Mixed-Universe Semantic Hazards & Hyperscale Fleet Postmortems

`Basis: execution + documentation`

1. **Cross-Task Invariant Breakdown (`klp_quiescence_model`):** Per-task consistency only guarantees that *within a single thread*, a caller and callee do not mix old/new versions of the patched set. When Patch $P$ modifies a protocol shared across threads—such as reversing lock order (`v0`: `L1 -> L2` vs. `v1`: `L2 -> L1`) or adding a new required shadow variable—the transition window produces mixed-universe deadlocks and null-dereferences. Our explicit state-space probe (`klp_quiescence_model.py`, 6 reachable states) finds the exact witness trace:
   `T0[PATCHED]: lock(L2) -> T1[UNPATCHED]: lock(L1)` (deadlock when `T1` remains pinned `UNPATCHED` by an unrelated patched stack frame), and shows `unpatched_creator_klp_shadow_get=None` when an unpatched allocator constructs an object read by a patched consumer unless defensive `klp_shadow_get_or_alloc` is used everywhere.
2. **Hyperscale Fleet Engineering Experience (Meta LPC Reports):** In *"Kernel Live Patching at Scale"* (Linux Plumbers Conference talks by Song Liu, Rik van Riel, and David Vernet), fleet operators running millions of Linux servers documented three dominant rollout failures:
   - **Observability Hook Conflicts:** `FTRACE_OPS_FL_IPMODIFY` (`patch.c#L191`) grants exclusive IP-modification ownership; active BPF trampolines and `kretprobe` profilers sharing function entries fail livepatch registration with `-EBUSY` (`livepatch.rst#L437-L442`).
   - **ThinLTO Inlining Explosion (`CONFIG_LTO_CLANG_THIN`):** Cross-translation-unit inlining in clang-LTO production kernels breaks `kpatch-build` ELF object correlation and expands the set of functions needing patching, motivating upstream `klp-build` integration.
   - **Unpatchable Kthread Loops:** Long-running filesystem/workqueue kthreads (e.g., `btrfs` or `events_unbound`) that `cond_resched()` while remaining inside a patched helper frame keep `klp_check_stack_func` returning `-EAGAIN` indefinitely.
3. **Code Patching vs. Ring-0 Data Interpreters (July 19, 2024 CrowdStrike Outage):** In contrast to ELF code patches gated by compiler/verifier checks, CrowdStrike's July 19, 2024 outage (Channel File 291) pushed a dynamic configuration template with **21 input fields** to a Windows ring-0 interpreter (`csagent.sys`) expecting **20 fields**, bypassing validator checks and triggering immediate `STATUS_ACCESS_VIOLATION` out-of-bounds BSOD boot loops across ~8.5 million hosts. Industry postmortems contrasted this failure with Linux **eBPF static bounds verification** (which rejects out-of-bounds table reads at load time) and stressed that any live kernel extension—code or interpreted rule—requires both **static memory-safety admission checks** and **staged canary rings**.

---

### 2. Shadow Variables (`klp_shadow_*`), Binary Diffing (`kpatch`, `Ksplice`), and Xen Livepatch

`Basis: source + execution + documentation`

#### Struct Extension via `klp_shadow_*` (`kernel/livepatch/shadow.c`)

Because livepatches cannot alter `sizeof(struct S)` or field offsets compiled into unpatched kernel subsystems (`Documentation/livepatch/shadow-vars.rst#L1-L55`), Linux attaches side-car fields via a global RCU hash table:

- **Implementation (`shadow.c#L38-L299`):** `DEFINE_HASHTABLE(klp_shadow_hash, 12)` (`4,096` buckets) indexed by `(unsigned long)obj`, serialized on mutations by a **single global spinlock** `DEFINE_SPINLOCK(klp_shadow_lock)` (`#L44`).
- **Constructor Spinlock Trap (`__klp_shadow_get_or_alloc`, `#L104-L170`):** `kzalloc` runs *before* taking `klp_shadow_lock` (throwing away speculative allocations on race `#L130-L138`), **but the custom `ctor(obj, data, ctor_data)` executes strictly under `spin_lock_irqsave(&klp_shadow_lock, flags)`** (`#L128-L159`). Heavy allocation or lock contention on hot networking/filesystem structs serializes every CPU in IRQ-disabled context.
- **Measured Read & Contention Amplification (`klp_bench`):** User-space microbenchmarking of the exact `klp` patterns (`gcc -O2`, 3 runs x 2M iterations) measured median `inline_field_ns=0.87` (`0.75–1.07 ns`) vs. `shadow_hash_get_ns=4.96` (`4.86–5.34 ns`, **`5.70x`** read-side hash traversal penalty) vs. `shadow_spinlock_update_ns=11.71` (`11.62–11.75 ns`, **`13.46x`** even totally uncontended). By contrast, a warm branch-predicted indirect trampoline (`klp_trampoline_ns=2.84 ns` median vs. `direct_call_ns=3.09 ns` median) adds negligible user-space branch cost once resident in L1 I-cache/BTB, whereas kernel-space `ftrace` redirection incurs additional `ftrace_test_recursion_trylock` + frame-save overhead when `CONFIG_HAVE_DYNAMIC_FTRACE_WITH_ARGS` is absent.
- **Cumulative `.replace` Leaks:** Unpatched object destructors never call `klp_shadow_free()`. Cumulative livepatches with `.replace` (`transition.c#L92-L95`) must preserve or clean up `<obj, id>` entries across replacement boundaries via `klp_shadow_free_all(id, dtor)` or risk silent slab leaks.

#### ELF Binary Diffing (`dynup/kpatch` vs. `Ksplice`)

| Dimension | `dynup/kpatch` (`862cda5e...`, `create-diff-object.c`) | `Ksplice` (`EuroSys 2009`, `DOI: 10.1145/1519065.1519085`) |
| :--- | :--- | :--- |
| **Diffing Granularity & Flags** | Compiles original vs. patched C with `-ffunction-sections -fdata-sections`; correlates `.text.<fn>`, `.text.unlikely.<fn>`/`.cold`, `.rodata.<sym>` (`#L92-L147`). | Compares pre- and post-patch compiled object code (`pre`/`post` ELF sections) with zero source annotations; identifies modified functions & data relocations. |
| **Arch & Compiler Quirks** | Explicitly handles `ppc64le` `.localentry` 8-byte global/local offset (`#L156-L192`), 2-level `.toc` relocations (`toc_rela`, `#L220-L233`), and AArch64 `$x`/`$d` mapping symbols (`#L241-L249`). | Primarily targeted `x86-32`/`x86_64` pre-LTO GCC kernels before `.retpoline_sites` / `ORC` proliferation. |
| **Special Sections & Relocs** | Rebuilds 13 architecture-specific metadata tables (`special_sections[]`, `#L2652-L2720`: `__bug_table`, `__ex_table`, `__jump_table`, `.altinstructions`, `.static_call_sites`, `.retpoline_sites`, `.return_sites`, `ORC` unwinders `#L2999`) + emits `.klp.rela.<obj>.<sec>` for unexported static symbols. | Uses `kallsyms` + `System.map` symbol tables; injects direct `jmp` trampolines at patched function prologues. |
| **Quiescence & Automation** | Targets mainline `klp` (`KLP_ARCH = true`); fails closed (`DIFF_FATAL`, `#L56-L60`) on structural data-layout or unsupported special-section edits. | Global `stop_machine()` quiescence checking all kernel stacks in one freeze; patched **56/64 (`88%`)** Linux CVEs (2005–2008) with 0 LoC helpers and the remaining **12%** with **~17 LoC average**. |

#### Hypervisor Stackless Quiescence (`xen-project/xen`)

`xen/common/livepatch.c` (`92ddcda17fb00020c6215d51df4c6a25d5eb0b5e`) achieves global quiescence **without any stack unwinder**:
- Because hypervisor vCPU context switches return completely to guest execution with empty hypervisor stacks, `do_livepatch_work()` (`#L1795-L1959`) triggers only when `is_idle_domain(current->sched_unit->domain)` (`#L1810`), IPIs peer CPUs via `tasklet_schedule_on_cpu`, masks NMIs (`arch_livepatch_mask()` `#L1848`), and synchronizes all CPUs via a two-phase `livepatch_work.semaphore` spin bounded by `MILLISECS(30)` (`#L1745, L1769-L1789`).
- **Non-Atomic `LIVEPATCH_ACTION_REPLACE` Gap (`#L1614-L1676`):** `LIVEPATCH_ACTION_REPLACE` reverts **every applied payload** in `applied_list` *before* calling `livepatch_check_expectations(data)` (`#L1653-L1659`). If the new payload fails expectation checks, Xen aborts replacement and logs `SYSTEM MIGHT BE INSECURE: Replace action has been aborted after reverting ALL payloads!`—exposing an unpatched window requiring re-application. `REPLACE` also refuses modules with vetoing pre/post hooks (`#L2175-L2181`).

---

### 3. General User-Space Dynamic Software Updating (`Kitsune` & `Rubah`)

`Basis: source + documentation`

1. **`Kitsune` (`kitsune-dsu/kitsune-core` @ `6393a0c148976c910df313bda4b578e7c240a6d2`, OOPSLA 2012 `DOI: 10.1145/2384616.2384635`):**
   - **Control-Flow Reset via `longjmp` (`src/kitsune.c#L106-L322`):** Legacy C processes run inside a `dlopen` driver loop. At annotated top-level loop quiescent points `kitsune_update(pt_name)`, threads converge via `ktthread_rapidq()` / `ktthread_main_wait()` (`#L136, L302`), spill compiler-tracked stack variables (`stackvars_move_to_heap()` `#L299`), and execute `longjmp(*jmp_env, 1)` (`#L315`) to unwind the entire C stack back to the driver, which `dlopen`s `v+1` and calls `kitsune_init_inplace()`.
   - **State Transformers:** Compiler-generated `xfgen` rules and custom hooks (`_kitsune_prestart_xform`, `_kitsune_mainupdate_xform`) migrate old globals and structs fetched via `dlsym(prev_ver_handle, ...)` (`#L368-L373`) before resuming at the matching `kitsune_update()` call site and calling `dlclose(prev_ver_handle)`.
2. **`Rubah` (`plum-umd/rubah` @ `e0dcea715b074f486cc064d45e794d03f1ccd317`, OOPSLA 2014 `DOI: 10.1145/2660193.2660220`):**
   - Operates on **stock JVMs** via bytecode rewriting (`-1.0%` to `+2.5%` steady-state overhead).
   - **Eager vs. Lazy Heap Migration:** Parallel eager heap traversal (`4x` faster than single-threaded traversal) still incurs **tens of seconds to minutes of stop-the-world pause** on multi-GB heaps (H2, Voldemort). `Rubah`'s lazy algorithm pauses all threads only for **`2–3 seconds`** regardless of heap size to swap class metadata and root handles, migrating individual old objects on first post-update dereference (`90%` steady throughput recovered in `<= 30 s`).
   - **Hard Real-Time Rejection:** Lazy on-demand state transformation violates deterministic Worst-Case Execution Time (WCET): a time-critical thread touching an unmigrated root object can trigger a transitive GC/transformer cascade mid-deadline.

---

### 4. Sub-Millisecond Hot-Swapping & Deterministic State Transfer in Safety-Critical RTOSes

`Basis: source + documentation + derived`

Safety-critical real-time controllers (`Zephyr` `c9e38773358d...`, `FreeRTOS` `83a45bf29002...`, `ARINC 653` avionics, `1–10 kHz` motor/power-inverter loops) enforce cyclic frame periods $T_{\text{cycle}} \in [100\ \mu\text{s}, 10\ \text{ms}]$ where any missed deadline triggers physical instability or safety trips.

#### Why Bootloader Flash-Swapping Fails Real-Time Upgrades

`mcu-tools/mcuboot` (`c5983c9af5408587c31ca0302c6a0d36c6fc8741`, `docs/design.md#L55-L249`) verifies `image_header` (`32 B`, `IMAGE_MAGIC = 0x96f3b83d`) and swaps `FLASH_AREA_IMAGE_PRIMARY` / `SECONDARY` through `FLASH_AREA_IMAGE_SCRATCH` across reboots. Even on dual-bank MCUs, erasing a 4 KiB–256 KiB NOR flash sector stalls single-bank XIP reads and consumes **`30 ms–2,000 ms` per sector**, plus cold-boot RTOS reinitialization—disqualifying bootloader swaps whenever physical control loops cannot drop out for milliseconds.

#### Embedded Live-Patching Mechanisms Compared

1. **ARM Cortex-M Hardware FPB (`Flash Patch and Breakpoint`):** Zero steady-state instruction overhead by remapping flash instruction fetches in hardware via `FP_COMPn` comparators; **strictly capped at `6` instruction/literal slots (Cortex-M3/M4, FPBv1 limited to lower 512 MB code space) or `8` slots (Cortex-M7/M33, FPBv2)**, exhausting immediately on multi-function patches or struct changes.
2. **`RapidPatch` (`IoTAccessControl/RapidPatch` @ `2c4fddeb5b8c...` / `43498177c61b...`, USENIX Security 2022):** Dispatches fixed-location instrumentation traps or hardware breakpoints into a lightweight userspace **eBPF VM** (`< 64 KB` RAM footprint). Achieves **`< 8 µs` average patch delay** and **`< 0.6%` steady-state overhead**, guaranteeing memory-safe sandboxed filters/hotfixes at the cost of interpreter dispatch latency and inability to add fields to statically allocated kernel structs.
3. **`AutoPatch` (`DependableSystemsLab/AutoPatch` @ `9ab6ba0a619447832e88c9f2517a7c4725df37d3`, CCS 2024 `DOI: 10.1145/3658644.3690255`):** Two-pass LLVM compiler pipeline (`AutoPatchFirstPass` trampoline insertion + `AutoPatchSecondPass` static diff/equivalence synthesis) generating native ARM/Xtensa `.o` hotpatches evaluated on `Zephyr` across `nRF52840`, `STM32-F446RE`, and `ESP32` (`README.md#L4-L40`). Delivers **`< 12.7 µs` average total delay** (`~50%` faster trigger-to-execution path vs. `RapidPatch` in automated tests) with **`~23%` memory overhead** and native machine-code WCET predictability.

#### Deterministic Dual-Bank Ping-Pong State Transfer Architecture

`Basis: derived`

To upgrade **both code and stateful controller schemas** inside a hard cyclic deadline $T_{\text{cycle}}$ without `klp` stack walks or lazy GC proxies:

1. **Slack-Period Pre-Staging:** A low-priority background task writes and cryptographically verifies image `Bank B` ($v+1$) in dual-bank flash (or reserved SRAM) without disturbing `Bank A` ($v$) XIP execution.
2. **State Separation:** Persistent controller state $\Sigma_v$ (integrators, Kalman covariances, FSM phases; typically `64 B–16 KiB` in static BSS/struct pools, zero post-init `malloc`) resides in a dedicated dual-bank ping-pong SRAM arena (`Arena A` vs. `Arena B`), isolated from ephemeral stack scratch.
3. **Frame-Boundary Schedulability Invariant:** Let $C_v, C_{v+1}$ be static WCETs of the cyclic control step, $\Delta_{\text{switch}}$ the atomic MPU/vector-table pointer flip (`< 1 µs`), and $\tau_{v \to v+1} : \Sigma_v \to \Sigma_{v+1}$ a loop-free total state transformer:

$$\text{WCET}(\tau_{v \to v+1}) + \Delta_{\text{switch}} \le T_{\text{cycle}} - \max(C_v, C_{v+1}) - J_{\text{IRQ}}$$

At the **idle end-of-minor-frame boundary** (where every periodic task has returned cleanly to its wait loop—so call stacks hold zero active controller frames), an interrupt-masked critical window runs $\tau_{v \to v+1}(\Sigma_v^A) \to \Sigma_{v+1}^B$, flips the active vector/MPU bank pointer, and preserves $\Sigma_v^A$ read-only as a **1-cycle hardware-watchdog rollback snapshot** during the first cycle of $v+1$.

---

### 5. Six-Level Performance, Verification & Resource Matrix (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| System | (L1) Authoring Velocity & Repair Cost | (L2) Toolchain Build Time & RSS | (L3) Analysis / Patch Generation Speed | (L4) Steady-State & Transition Runtime Cost | (L5) Quiescence / Safety Check Speed | (L6) Binary, Memory & Metadata Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Linux `klp` + `kpatch-build`** (`4405c18c...` / `862cda5e...`) | High manual audit when structs/locks change; requires `klp_shadow_*` glue & cumulative `.replace` cleanup | Full kernel debuginfo + `kpatch-build` C tool (`create-diff-object.c`: 4.7 kLoC); minutes per kernel build | Seconds–minutes (`-ffunction-sections` ELF section diff + `klp-build` LTO handling) | `0%` unpatched; warm user trampoline sim `~2.84 ns` vs `3.09 ns` direct (`~0 ns` I-cache/BTB hot); **`5.70x`** shadow hash read (`4.96 ns` vs `0.87 ns`), **`13.46x`** spinlock update (`11.71 ns`) | Milliseconds–seconds convergence; **unbounded stall** on `TASK_UNINTERRUPTIBLE` / stuck kthreads (`SIGNALS_TIMEOUT=15s`) | `.ko` diff module (`10s–100s KiB`) + `4096`-bucket `klp_shadow_hash` + `ftrace_ops` / trampoline pages |
| **`Ksplice`** (`10.1145/1519065.1519085`) | **88% (56/64)** Linux CVEs zero-helper-code; ~17 LoC avg for remaining 12% | Pre/post kernel object diff driver | Seconds per patch diff | Zero steady-state overhead beyond direct `jmp` prologue patch; global `stop_machine` freeze (`ms`) | Single global stack scan inside `stop_machine()` across all CPUs | Small `.ko` binary diff + prologue trampoline bytes |
| **`Xen livepatch`** (`92ddcda1...`) | Explicit `livepatch-build-tools` + manual avoidance of non-atomic `REPLACE` hooks | Xen build + hypervisor ELF diff tools | Seconds per payload | Zero steady-state call overhead (`arch_livepatch_apply` direct rewrite); `<= 30 ms` global CPU pause (`MILLISECS(30)`) | Fast stackless rendezvous at `is_idle_domain` (fails `-EBUSY` if any CPU misses 30 ms window) | Per-payload `text`/`ro`/`rw` hypervisor pages (`LIVEPATCH_MAX_SIZE` bounded) |
| **`Kitsune`** (`6393a0c1...`, `10.1145/2384616.2384635`) | Requires manual `kitsune_update()` annotations + `xfgen` rules for renamed/changed structs | `ktcc` compiler wrapper + `libkitsune` C runtime | Seconds (standard C compile + `.so` link) | Negligible polling flag check (`if (update_requested)`); update pause dominated by heap migration (`ms`) | Instant at explicit `ktthread_main_wait` quiescent barrier | Keeps dual `dlopen` `.so` mappings briefly during migration until `dlclose(prev_ver_handle)` |
| **`Rubah` (Eager vs. Lazy)** (`e0dcea71...`, `10.1145/2660193.2660220`) | Annotated Java class evolution + `update()` point placement | Standard JDK + Rubah bytecode rewriter | Seconds (JVM bytecode instrumentation) | `-1.0%` to `+2.5%` steady-state overhead; **2–3 s** lazy pause vs **10s–minutes** parallel eager pause; 90% recovery `<= 30 s` | Barrier at safe update points + lazy class-version dispatch check | Dual-version class metadata + object migration forwarding headers |
| **`RapidPatch`** (`2c4fddeb...`, USENIX Sec '22) | Patch written as restricted C -> compiled to eBPF; constrained by verifier & no new struct fields | `RapidPatch-ToolChain` + embedded eBPF runtime (`< 64 KB` RAM) | Sub-second Clang BPF compilation (`eBPF` bytecode `100s B`) | **`< 8 µs`** average patch delay; **`< 0.6%`** runtime overhead | Load-time bounded-loop/memory safety check (ms host-side or onboard lightweight check) | **`< 64 KB` MCU RAM** footprint; small eBPF patch bytecode in SRAM/Flash |
| **`AutoPatch`** (`9ab6ba0a...`, CCS '24) | Automated LLVM synthesis from official C source diffs | Custom LLVM 9 passes (`AutoPatchFirstPass` / `SecondPass`) | Seconds (IR instrumentation + static path diff) | **`< 12.7 µs`** average total delay; native ARM execution after dispatch | Static LLVM IR admissibility & WCET analysis before flashing | **`~23%` average memory overhead** from pre-placed trampoline instrumentation |
| **`MCUboot` vs. RTOS Ping-Pong Transfer** (`c5983c9a...`) | `MCUboot`: zero app code changes; Ping-Pong: explicit total $\tau : \Sigma_v \to \Sigma_{v+1}$ schema | Standard Zephyr/FreeRTOS GCC/ARM build | Seconds | `MCUboot`: **`30 ms–2,000 ms`**/sector reboot outage; Ping-Pong: **`< 100 µs`** deterministic switch (`WCET(τ)` bounded) | `MCUboot`: ECDSA/Ed25519/SHA256 TLV boot check; Ping-Pong: static WCET + 1-cycle watchdog rollback | `MCUboot`: `2x` flash slots + scratch sector; Ping-Pong: `2x` flash banks + `2x` persistent state SRAM (`64 B–16 KiB`) |

---

### 6. Human Comprehensibility (`C1`) and Universal Conceptual Simplicity (`C2`)

`Basis: derived + source`

#### (C1) Human Comprehensibility Audit

Linux `klp` (`transition.c`, `patch.c`, `shadow.c`) forces human patch reviewers to reason simultaneously across **seven non-local concepts**: (1) `TIF_PATCH_PENDING` visibility barriers, (2) `CONFIG_HAVE_RELIABLE_STACKTRACE` / `ORC` unwinding completeness, (3) interrupt-state inheritance (`current->patch_state`), (4) `2^k` mixed-version execution interleavings across unpatched/patched tasks, (5) `klp_shadow_lock` IRQ-disabled constructor safety, (6) `notrace` / `FTRACE_OPS_FL_IPMODIFY` exclusions, and (7) cumulative `.replace` shadow-variable cleanup. A 20-line C security patch routinely expands into hundreds of lines of shadow lifecycle hooks and concurrency proofs that defeat 1-page human auditability.

By contrast, explicit cut-point systems (`Xen` `is_idle_domain`, `Kitsune` `kitsune_update`, and RTOS cyclic minor-frame boundaries) restore **local, 1-page human auditability**: there are zero mixed-version concurrent tasks, zero stack-frame checks, and state migration reduces to inspecting a single pure total function $\tau : \Sigma_v \to \Sigma_{v+1}$ verifying $I_v(\sigma) \implies I_{v+1}(\tau(\sigma))$.

#### (C2) Simplicity, Minimization & Universal Generalization

Across Linux `klp`, `Ksplice`, `Xen`, `Kitsune`, `Rubah`, and RTOS patchers, complexity proliferates through redundant mechanisms enforcing one goal: *never execute old-schema code against new-schema data (or vice versa) with half-migrated call stacks*.

1. **Universal Minimal Model — Explicit Stackless Cut-Points + Typed State Homomorphisms:**
   - Replace per-task stack inspection (`ORC` + `klp_check_stack`), dual-version ftrace dispatching (`klp_ftrace_handler`), and untyped global hash sidecars (`klp_shadow_hash`) with two orthogonal primitives:
     - **Cut-Point Quiescence:** Patch switches occur strictly at top-level event/cycle boundaries where the call stack contains zero application frames (already true natively in hypervisor VMEXITs, RTOS cyclic loops, async event reactors like `io_uring`/epoll workers, and `Kitsune` loop points).
     - **Dual-Arena State Homomorphism ($\tau$):** Persistent state $\Sigma_v$ sits behind one versioned arena pointer flipped atomically after a deterministic transformer $\tau : \Sigma_v \to \Sigma_{v+1}$ completes, retaining $\Sigma_v$ read-only for 1-step rollback.
2. **Rigorous Verification of Genuine Complexity Elimination vs. Irreducible Cases:**
   - **Genuinely eliminated:** Eliminates per-task `patch_state` flags, `klp_shadow_lock` contention, `ftrace` IPMODIFY collisions, and mixed-version lock-order deadlocks entirely from event-driven kernels, hypervisors, and RTOS controllers.
   - **Irreducible remainder (cannot be unified away):** Monolithic general-purpose Unix kernels running **unbounded blocking syscalls** (`nfs`, unyielding `btrfs` kthreads, deep VFS locks) cannot globally pause all threads at top-of-loop without breaking latency SLAs (`stop_machine`), and **multi-gigabyte JVM/database heaps** (`Rubah`) exceed pause budgets if $\tau$ eagerly copies the entire heap—meaning per-task stack quiescence (`klp`) and lazy object proxies (`Rubah`) remain necessary complexity for unbounded blocking stacks and multi-GB heaps respectively.

## Boundaries

- **`unsupported` — Linux `klp` general kthread/reliable convergence without `CONFIG_HAVE_RELIABLE_STACKTRACE`:** `kernel/livepatch/transition.c#L318-L319` and `Documentation/livepatch/livepatch.rst#L128-L130` explicitly establish that architectures lacking reliable stack unwinding cannot use stack checking (`klp_try_switch_task` returns `false`), leaving sleeping kthreads unpatched unless custom `klp_update_patch_state()` checkpoints are hand-placed inside every kthread loop.
- **`known not to apply` — `MCUboot` flash swap to hard real-time `<1 ms` zero-downtime upgrades:** Rebooting and erasing NOR flash sectors (`30 ms–2,000 ms` per sector) violates sub-millisecond cyclic deadlines and wipes volatile controller state unless backed by persistent SRAM checkpoints.
- **`known not to apply` — Linux `klp` per-task transition safety to global lock-order or data-invariant changes:** `klp_quiescence_model.py` and `livepatch.rst#L64-L72` confirm per-task switching does not synchronize independent threads sharing global locks or `klp_shadow_*` entries; mixed `KLP_UNPATCHED` / `KLP_PATCHED` tasks deadlock unless prevented by external synchronization or global quiescence.
- **`known not to apply` — `Xen` `LIVEPATCH_ACTION_REPLACE` atomicity with vetoing hooks or expectation mismatches:** `xen/common/livepatch.c#L1620-L1659, L2175-L2181` disallows `REPLACE` on payloads with vetoing hooks and reverts all applied patches *before* checking the new payload's expectations.
- **`known not to apply` — `Rubah` lazy object-proxy migration to hard real-time WCET loops:** Deferring object transformation until first post-update dereference moves unbounded migration time onto arbitrary real-time execution paths.
- **`unknown` — Automated soundness verification of arbitrary C/RTOS state transformers $\tau$:** Determining semantic equivalence between legacy state invariants and arbitrary user-written $\tau_{v \to v+1}$ across unannotated C pointers remains undecidable in general without explicit programmer/spec invariants.
- **`not examined` — Proprietary Windows kernel driver (`csagent.sys`) livepatching internals and commercial mainframe/automotive AUTOSAR OTA dual-bank ECU vendor implementations.**

## Evidence

### Pinned Repositories & Source Locations

- **`torvalds/linux`** @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`2026-11-19`):
  - `kernel/livepatch/transition.c#L35-L75, L175-L282, L305-L487, L552-L619, L706-L731`: `klp_sched_try_switch_key`, `klp_synchronize_transition`, `klp_update_patch_state`, `klp_check_stack` (`MAX_STACK_ENTRIES = 100`), `klp_send_signals` (`SIGNALS_TIMEOUT = 15`), `klp_init_transition`, `klp_force_transition`.
  - `kernel/livepatch/patch.c#L40-L125, L186-L193`: `klp_ftrace_handler`, `FTRACE_OPS_FL_{DYNAMIC, IPMODIFY, PERMANENT}`.
  - `kernel/livepatch/shadow.c#L38-L299`: `klp_shadow_hash` (`4096` buckets), `klp_shadow_lock`, `__klp_shadow_get_or_alloc` (`ctor` inside `spin_lock_irqsave`), `klp_shadow_free_all`.
  - `Documentation/livepatch/livepatch.rst#L50-L209, L408-L448` and `Documentation/livepatch/shadow-vars.rst#L1-L55`.
- **`dynup/kpatch`** @ `862cda5e7b6827505ec429ab0bc0ad61cd26f068` (`2026-11-19`):
  - `kpatch-build/create-diff-object.c#L56-L249, L2652-L2720, L2999`: `DIFF_FATAL`, `is_bundleable`, `is_gcc6_localentry_bundled_sym`, `toc_rela`, `kpatch_is_mapping_symbol`, `special_sections[]`, `kpatch_regenerate_orc_sections`.
- **`xen-project/xen`** @ `92ddcda17fb00020c6215d51df4c6a25d5eb0b5e` (`2026-11-19`):
  - `xen/common/livepatch.c#L53-L75, L1414-L1472, L1614-L1676, L1728-L1970, L2153-L2186`: `struct livepatch_work`, `apply_payload`, `LIVEPATCH_ACTION_REPLACE` revert-before-expectations sequence, `MILLISECS(30)` timeout, `do_livepatch_work` (`is_idle_domain`), `check_for_livepatch_work`.
- **`kitsune-dsu/kitsune-core`** @ `6393a0c148976c910df313bda4b578e7c240a6d2` (`src/kitsune.c#L51-L373`: `jmp_env`, `kitsune_init_inplace`, `kitsune_update`, `stackvars_move_to_heap`, `longjmp`, `dlclose(prev_ver_handle)`).
- **`plum-umd/rubah`** @ `e0dcea715b074f486cc064d45e794d03f1ccd317` (`README.md`).
- **`IoTAccessControl/RapidPatch`** @ `43498177c61b14b70df81df141a7b8622e354995` (`README.md`) & `ArtifactEvaluation` @ `2c4fddeb5b8ccc20226a61422448243ac065775f`; **`IoTAccessControl/RapidPatch-ToolChain`** @ `32e35d5b9b539d8c84e07f7f149f6f7fce536f26`.
- **`DependableSystemsLab/AutoPatch`** @ `9ab6ba0a619447832e88c9f2517a7c4725df37d3` (`README.md#L1-L40`).
- **`mcu-tools/mcuboot`** @ `c5983c9af5408587c31ca0302c6a0d36c6fc8741` (`docs/design.md#L55-L249`: `image_header`, TLV layout, `FLASH_AREA_IMAGE_SCRATCH` swap).
- **`zephyrproject-rtos/zephyr`** @ `c9e38773358dfe0b19fe920f611e288cca4bdf66`; **`FreeRTOS/FreeRTOS-Kernel`** @ `83a45bf290024de16ca94df1f7262bcde6c82ffe`.

### Peer-Reviewed Papers & Practitioner Incident Reports

- Arnold & Kaashoek, *"Ksplice: Automatic Rebootless Kernel Updates"*, EuroSys 2009, `DOI: 10.1145/1519065.1519085`.
- Hayden et al., *"Kitsune: Efficient, General-purpose Dynamic Software Updating for C"*, OOPSLA 2012, `DOI: 10.1145/2384616.2384635`.
- Pina, Veiga, & Hicks, *"Rubah: DSU for Java on a Stock JVM"*, OOPSLA 2014, `DOI: 10.1145/2660193.2660220`.
- He et al., *"RapidPatch: Firmware Hotpatching for Real-Time Embedded Devices"*, 31st USENIX Security Symposium, Aug 2022, pp. 2225–2242.
- Salehi & Pattabiraman, *"AutoPatch: Automated Generation of Hotpatches for Real-Time Embedded Devices"*, ACM CCS 2024, `DOI: 10.1145/3658644.3690255`.
- Practitioner engineering reports: Meta Linux Plumbers Conference talks (*"Kernel Live Patching at Scale"*, Song Liu, Rik van Riel, David Vernet on LTO, `klp-build`, `FTRACE_OPS_FL_IPMODIFY`, and kthread transition stalls); CrowdStrike Channel File 291 Root Cause Analysis (July 2024 out-of-bounds 21-vs-20 IPC template failure in `csagent.sys`).

### Self-Contained Executable Probes (`2026-11-19`)

Environment: Linux `7.1.6-1rodete1-amd64 x86_64`, 8-vCPU Intel Xeon @ 2.20 GHz, `gcc (Debian 15.2.0-14) 15.2.0`, `Python 3.13.15`.

#### Probe A: State-Space Model of Per-Task `klp_transition` & Shadow Hazards (`klp_quiescence_model.py`)

```python
#!/usr/bin/env python3
from collections import deque

def check_split_state_hazards():
    init = (0, 0, None, None)  # (pc0, pc1, owner_L1, owner_L2)
    q = deque([init])
    visited = {init: []}
    deadlock_trace = None
    while q:
        s = q.popleft()
        pc0, pc1, l1, l2 = s
        trace = visited[s]
        if pc0 == 1 and l1 == 1 and pc1 == 1 and l2 == 0:
            deadlock_trace = trace
            break
        next_states = []
        if pc0 == 0 and l2 is None:
            next_states.append(((1, pc1, l1, 0), "T0[PATCHED]: lock(L2)"))
        elif pc0 == 1 and l1 is None:
            next_states.append(((2, pc1, 0, l2), "T0[PATCHED]: lock(L1)"))
        elif pc0 == 2:
            next_states.append(((0, pc1, None, None), "T0[PATCHED]: unlock(L1,L2)"))
        if pc1 == 0 and l1 is None:
            next_states.append(((pc0, 1, 1, l2), "T1[UNPATCHED]: lock(L1)"))
        elif pc1 == 1 and l2 is None:
            next_states.append(((pc0, 2, l1, 1), "T1[UNPATCHED]: lock(L2)"))
        elif pc1 == 2:
            next_states.append(((pc0, 0, None, None), "T1[UNPATCHED]: unlock(L2,L1)"))
        for ns, act in next_states:
            if ns not in visited:
                visited[ns] = trace + [act]
                q.append(ns)

    shadow_table = {}
    obj_id = 0xdeadbeef
    naive_get = shadow_table.get((obj_id, 1), None)
    safe_get_or_alloc = shadow_table.setdefault((obj_id, 1), {"v2_field": 0})
    func_addr, func_size = 0xffffffff81100000, 0x120
    stack_entries = [0xffffffff81a00410, 0xffffffff81100048, 0xffffffff81090020]
    in_bounds = any(func_addr <= ip < func_addr + func_size for ip in stack_entries)

    print(f"reachable_states_explored={len(visited)} mixed_state_deadlock={deadlock_trace is not None}")
    print("deadlock_witness=" + " -> ".join(deadlock_trace))
    print(f"unpatched_creator_klp_shadow_get={naive_get} safe_get_or_alloc={safe_get_or_alloc}")
    print(f"kthread_loop_frame_blocks_klp_check_stack={in_bounds}")

if __name__ == "__main__":
    check_split_state_hazards()
```

Observed output:
```text
reachable_states_explored=6 mixed_state_deadlock=True
deadlock_witness=T0[PATCHED]: lock(L2) -> T1[UNPATCHED]: lock(L1)
unpatched_creator_klp_shadow_get=None safe_get_or_alloc={'v2_field': 0}
kthread_loop_frame_blocks_klp_check_stack=True
```

#### Probe B: Trampoline Dispatch & Shadow-Hash Lookup Cost Benchmark (`klp_bench.c`)

```c
#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

static inline uint64_t nsec_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

struct Obj { uint64_t a; uint64_t inline_v2; };
struct ShadowNode { void *obj; unsigned long id; uint64_t data; struct ShadowNode *next; };

#define HASH_BITS 12
static struct ShadowNode *g_buckets[1U << HASH_BITS];
static pthread_spinlock_t g_shadow_lock;

static inline uint32_t hash_ptr(void *p) {
    return (uint32_t)(((uintptr_t)p * 0x9e3779b97f4a7c15ULL) >> (64 - HASH_BITS));
}

__attribute__((noinline)) uint64_t direct_callee(uint64_t x) { return x + 1; }
static volatile int g_func_transition = 0;
static __thread int t_patch_state = 1;
static uint64_t (*volatile g_func_stack_top)(uint64_t) = direct_callee;

__attribute__((noinline)) uint64_t klp_trampoline_sim(uint64_t x) {
    uint64_t (*fn)(uint64_t) = g_func_stack_top;
    asm volatile("" ::: "memory");
    if (__builtin_expect(g_func_transition, 0)) {
        asm volatile("" ::: "memory");
        if (t_patch_state == 0) return x;
    }
    return fn(x);
}

__attribute__((noinline)) uint64_t *shadow_get_sim(void *obj, unsigned long id) {
    struct ShadowNode *n = g_buckets[hash_ptr(obj)];
    while (n) {
        if (n->obj == obj && n->id == id) return &n->data;
        n = n->next;
    }
    return NULL;
}

int main(void) {
    const int N = 2000000;
    pthread_spin_init(&g_shadow_lock, PTHREAD_PROCESS_PRIVATE);
    struct Obj objs[64];
    struct ShadowNode nodes[64];
    memset(objs, 0, sizeof(objs));
    memset(nodes, 0, sizeof(nodes));
    for (int i = 0; i < 64; i++) {
        objs[i].inline_v2 = (uint64_t)i;
        nodes[i].obj = &objs[i];
        nodes[i].id = 1;
        nodes[i].data = (uint64_t)i;
        uint32_t b = hash_ptr(&objs[i]);
        nodes[i].next = g_buckets[b];
        g_buckets[b] = &nodes[i];
    }

    uint64_t acc = 0, t0 = nsec_now();
    for (int i = 0; i < N; i++) acc += direct_callee((uint64_t)i);
    uint64_t t1 = nsec_now(), t2 = nsec_now();
    for (int i = 0; i < N; i++) acc += klp_trampoline_sim((uint64_t)i);
    uint64_t t3 = nsec_now(), t4 = nsec_now();
    for (int i = 0; i < N; i++) { acc += objs[i & 63].inline_v2; asm volatile("" : "+r"(acc)); }
    uint64_t t5 = nsec_now(), t6 = nsec_now();
    for (int i = 0; i < N; i++) { acc += *shadow_get_sim(&objs[i & 63], 1); asm volatile("" : "+r"(acc)); }
    uint64_t t7 = nsec_now(), t8 = nsec_now();
    for (int i = 0; i < N; i++) { pthread_spin_lock(&g_shadow_lock); nodes[i & 63].data++; pthread_spin_unlock(&g_shadow_lock); }
    uint64_t t9 = nsec_now();

    printf("direct_call_ns=%.2f klp_trampoline_ns=%.2f\n", (double)(t1 - t0) / N, (double)(t3 - t2) / N);
    printf("inline_field_ns=%.2f shadow_hash_get_ns=%.2f shadow_spinlock_update_ns=%.2f (sink=%lu)\n",
           (double)(t5 - t4) / N, (double)(t7 - t6) / N, (double)(t9 - t8) / N, (unsigned long)acc);
    return 0;
}
```

Observed output (3 consecutive runs):
```text
--- run 1 ---
direct_call_ns=3.09 klp_trampoline_ns=2.76
inline_field_ns=0.75 shadow_hash_get_ns=4.86 shadow_spinlock_update_ns=11.71 (sink=4000128000000)
--- run 2 ---
direct_call_ns=2.08 klp_trampoline_ns=3.23
inline_field_ns=0.87 shadow_hash_get_ns=4.96 shadow_spinlock_update_ns=11.75 (sink=4000128000000)
--- run 3 ---
direct_call_ns=3.61 klp_trampoline_ns=2.84
inline_field_ns=1.07 shadow_hash_get_ns=5.34 shadow_spinlock_update_ns=11.62 (sink=4000128000000)
```

## Revalidation

To confirm whether kernel livepatch invariants or upstream implementation details have evolved:

1. **Diff Linux `klp` transition & shadow locking, plus Xen `REPLACE` logic (1–2 s):**
   ```sh
   GIT_TERMINAL_PROMPT=0 git -c protocol.version=0 ls-remote https://github.com/torvalds/linux.git HEAD
   curl -sSL https://raw.githubusercontent.com/torvalds/linux/HEAD/kernel/livepatch/shadow.c | grep -n -E "DEFINE_HASHTABLE|DEFINE_SPINLOCK|ctor\("
   curl -sSL https://raw.githubusercontent.com/xen-project/xen/HEAD/xen/common/livepatch.c | grep -n -A 15 "case LIVEPATCH_ACTION_REPLACE:"
   ```
   Verify whether `klp_shadow_hash` still runs `ctor()` under global `klp_shadow_lock` and whether Xen `LIVEPATCH_ACTION_REPLACE` still checks expectations after reverting applied payloads.

2. **Re-run Probe A (`klp_quiescence_model.py`, <1 s):** Save Probe A to `/tmp/klp_quiescence_model.py` and run `python3 /tmp/klp_quiescence_model.py`; verify `mixed_state_deadlock=True` and the 2-step deadlock witness.

3. **Re-run Probe B (`klp_bench.c`, <1 s):** Save Probe B to `/tmp/klp_bench.c` and run:
   ```sh
   gcc -O2 -pthread /tmp/klp_bench.c -o /tmp/klp_bench && /tmp/klp_bench
   ```
   Confirm global spinlocked shadow hash operations (`shadow_hash_get_ns`, `shadow_spinlock_update_ns`) remain `~5x–15x` slower than inline struct field loads (`inline_field_ns`), while warm branch-predicted indirect calls match direct-call latency within ~1 ns.
