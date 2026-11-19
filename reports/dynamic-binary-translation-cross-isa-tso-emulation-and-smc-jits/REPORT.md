# Dynamic Binary Translation: Cross-ISA x86-TSO Emulation, Self-Modifying JITs, x87/Flag Laziness, and Precise Guest Signals

## Summary

Emulating `x86-64` on weakly ordered `ARMv8`/`AArch64` and `RISC-V` (`RVWMO`) hosts requires closing four orthogonal semantic gaps that dominate both soundness and performance in production Dynamic Binary Translators (DBTs):

1. **Cross-ISA memory consistency (`x86-TSO` $\to$ `ARMv8-MCA`/`RVWMO`)**: `x86-TSO` preserves `Load->Load`, `Load->Store`, and `Store->Store` order while permitting only `Store->Load` reordering through per-core FIFO store buffers (and enforces multi-copy atomicity). Naive barrier insertion (`DMB ISH` / `LDAR`+`STLR`) over-constrains `Store->Load` or incurs severe pipeline stalls. Production systems span four concrete points on the hardware/software frontier:
   - **Hardware TSO mode** (`Apple Silicon` `ACTLR_EL1_EnTSO = 1ULL << 1` in XNU / Rosetta 2 and Linux `prctl(PR_SET_MEM_MODEL, PR_SET_MEM_MODEL_TSO)` on Apple silicon; `RISC-V Ztso` extension): zero software barriers on normal guest loads/stores.
   - **ARMv8.3/8.4 Release-Consistent Processor-Consistent (`FEAT_LRCPC`/`FEAT_LRCPC2`) + `SIGBUS` half-barrier backpatching** (`FEX-Emu`): emits `LDAPR`/`LDAPUR` (plus a trailing `NOP` slot) for loads and `NOP` + `STLR`/`STLUR` for stores so `STLR -> LDAPR` is *not* serialized; however, ARM Cortex Erratum `3877900` forces FEX to disable `LDAPUR` (`FEAT_LRCPC2`) on Neoverse V2/V3/V3AE and Cortex-X3/X4/X925/C1 cores because `LDAPUR` executes with full `LDAR` ordering. When an unaligned access traps (`SIGBUS`), FEX concurrently patches the barrier slot *first* and the memory op *second* with `std::memory_order_release` + `__builtin___clear_cache` to prevent an unbarriered execution window on concurrent threads.
   - **Unconditional barrier-based TSO** (`QEMU TCG` with `guest_default_memory_order = TCG_MO_ALL & ~TCG_MO_ST_LD` emitting `DMB ISHLD` before loads and `DMB ISH` before stores on AArch64, and `FENCE` on RV64; `Box64` `STRONGMEM=4` emitting `DMB_ISHLD` before loads and `DMB_TSO` after stores). Notably, `Box64` `STRONGMEM=4` on ARM64 places `DMB ISH` *after* stores and therefore over-constrains `SB`, whereas QEMU places `DMB ISH` *before* stores and preserves `SB`.
   - **Heuristic write-sequence barriers** (`Box64` `STRONGMEM=1..3`): deliberately omit reader-side barriers (`SMREAD()` is a no-op below level `4`), which leaves `MP`, `WRC`, and `IRIW` observable and unsound on weak `ARMv8`/`RVWMO` cores unless hardware `LRCPC+LRCPC2+LSE2` (`use_lrcpc`) or PE `VolatileMetadata` overrides individual sites.
2. **Self-modifying code (SMC) and cross-thread instruction-cache coherence**: Guest JITs (`V8`, `JVM`, `.NET`) write machine code through `RW` mappings (often dual-mapped `RW`+`RX` aliases via `memfd`) and execute it on sibling threads. Sound emulation requires page-write protection (`mprotect(PROT_READ)` in QEMU `page_protect` / FEX `CONFIG_SMC_MTRACK`, or Box64 `protectDB` + `X31_hash_code` validation), walking mirrored VMAs backed by the same underlying resource (`VMA->ResourceNextVMA` in FEX), unlinking chained translation blocks atomically, and respecting ARMv8's relaxed instruction-fetch semantics (`DC CVAU; DSB ISH; IC IVAU; DSB ISH; ISB` on the writer plus `ISB` or context-synchronizing event on the reader).
3. **Lazy condition codes (`EFLAGS`) and 80-bit `x87` floating point**: Materializing `CF/PF/AF/ZF/SF/OF` on every x86 arithmetic op is prohibitive. QEMU encodes deferred flag recipes (`CC_OP_*`) inside `tcg_gen_insn_start` metadata; FEX uses `RedundantFlagCalculationElimination` plus ARMv8.4/8.5 `FEAT_FLAGM`/`FEAT_FLAGM2` (`CFINV`, `RMIF`, `SETF8/16`, `AXFLAG`/`XAFLAG`) and Apple Silicon exposes `ACTLR_EL1_EnAPFLG`/`EnAFP`; Box64 uses pass-based flag liveness (`BOX64_DYNAREC_SAFEFLAGS=0..2`). For legacy `x87`, exact 80-bit extended precision requires software emulation (QEMU `floatx80` SoftFloat; FEX default `X87.cpp` + `x87StackOptimizationPass`), whereas optional 64-bit `double` lowering (FEX `X87ReducedPrecision`, Box64 `BOX64_DYNAREC_X87DOUBLE`) trades 11 bits of significand precision and exponent range for native FP throughput.
4. **Precise guest `ucontext_t` signal frames and native library thunking**: Any superblock optimization that reorders potentially faulting memory operations or eliminates dead register/flag writes across a faulting instruction corrupts the architectural `ucontext_t` (`RIP`, `RSP`, `EFLAGS`, GPRs, `xstate`) inspected by guest `SIGSEGV`/`SIGBUS` handlers (e.g., managed runtimes, `Wine` SEH, anti-cheat). DBTs maintain precision either via hardware shadow-register commit/rollback (`Transmeta CMS`), compressed host-PC-to-guest-PC unwind tables (`QEMU` `x86_restore_state_to_opc`, `Box64` `instsize` tables, `FEX` `SignalDelegator` + `RestoreFrame_x64`), and redirect modified guest `RIP` back through the JIT dispatcher loop. Hybrid native-library thunking (`Box64` `AddBridge`/`AddAutomaticBridge` and `FEX` `HostToGuestTrampolineTemplate`) eliminates DBT overhead across heavy host `.so` boundaries while marshaling ABI layouts and host-to-guest function-pointer callbacks.

## Applicability

This report synthesizes primary-source code inspection, architectural specifications, peer-reviewed literature, and an executable axiomatic verification probe across four directly examined DBT/kernel codebases and five foundational specifications/papers:

- **Direct source-level scope (pinned immutable revisions)**:
  - **QEMU TCG** (`qemu/qemu` @ `08c9bbb825148dec9669f5184ecf18823bb6d631`): `target/i386` guest frontend (`x86_tcg_ops`, `CCOp`, `floatx80`), `tcg/tcg-op-ldst.c` memory-ordering barrier emission, `tcg/aarch64` and `tcg/riscv64` barrier lowering, `accel/tcg/{tb-maint.c,user-exec.c}`, and `docs/devel/multi-thread-tcg.rst`. Applies to both user-mode (`linux-user`) and multi-threaded system-mode (`MTTCG`) emulation where `CF_PARALLEL` is set.
  - **FEX-Emu** (`FEX-Emu/FEX` @ `be66e03d65217f53a7a2e5af46473cc9a79ce3f8`): `AArch64` host user-mode Linux (and Wine/PE volatile metadata) `x86`/`x86-64` DBT (`FEXCore` JIT `MemoryOps.cpp`, `Arm64.cpp` unaligned `SIGBUS` handler, `HostFeatures.cpp`, `OpcodeDispatcher/{Flags,X87,X87F64}.cpp`, `x87StackOptimizationPass.cpp`, `SyscallsSMCTracking.cpp`, `SignalDelegator/{SignalDelegator,GuestFramesManagement}.cpp`, `Thunks.cpp`).
  - **Box64** (`ptitSeb/box64` @ `6f0df3efe29aedae73e516277ce9cb2378779960`): user-mode `x86-64` Linux (and WowBox64) DynaRec targeting `ARM64` and `RV64` (`src/dynarec/dynarec_helper.h`, `arm64/` and `rv64/` emitters/passes, `dynablock.c`, `src/libtools/signals.c`, `src/tools/bridge.c`, `docs/USAGE.md`).
  - **Apple XNU** (`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`): `osfmk/arm64/proc_reg.h` definitions for Apple Silicon `ACTLR_EL1` bits (`EnTSO`, `EnAPFLG`, `EnAFP`, `EnPRSV`). Rosetta 2's proprietary translator binary itself is closed-source and not directly inspected; claims about Rosetta 2 are explicitly separated from XNU kernel register definitions (see **Boundaries**).
- **Normative and formal scope**:
  - `x86-TSO` (Sewell et al., CACM 2010), `ARMv8` Multicopy-Atomic (MCA) concurrency (Pulte et al., POPL 2018), `ARMv8-A` relaxed instruction-fetch semantics (Simner et al., ESOP 2020), `ArMOR` translation tables (Lustig et al., ISCA 2015), and `Transmeta Code Morphing Software` speculative commit/rollback (Dehnert et al., CGO 2003).
- **Host/target constraints**: Memory-model proofs assume a **multicopy-atomic (MCA)** host (`ARMv8.0+` under the revised MCA specification, `RISC-V RVWMO`, or `RISC-V Ztso`). Legacy non-MCA hosts (`ARMv7`, `POWER`) require stronger cumulative barriers (`DMB`/sync on readers) even where `IRIW` is concerned and are explicitly excluded unless noted.

## Findings

### 1. Cross-ISA Memory Consistency: Bridging `x86-TSO` to `ARMv8-MCA` and `RVWMO`

`Basis: normative + source + execution`

#### 1.1 The Architectural Ordering Gap (`ArMOR` & `x86-TSO` vs. `ARMv8`/`RVWMO`)

Under `x86-TSO` (Sewell et al., CACM 2010), every logical core drains writes through a local FIFO store buffer into a single coherent memory; stores become globally visible to all other cores simultaneously (multicopy atomicity). Consequently, `x86-TSO` preserves three of the four cross-address same-thread orderings:

| Ordering pair | `x86-TSO` | `ARMv8-MCA` (plain `LDR`/`STR`) | `RISC-V RVWMO` (plain `LD`/`SD`) | `RISC-V Ztso` / Apple `EnTSO` | Distinguishing Litmus Test |
| :--- | :---: | :---: | :---: | :---: | :--- |
| `Load -> Load` (`R->R`) | **Preserved** | Relaxed | Relaxed | **Preserved** | `MP`, `WRC`, `IRIW` |
| `Load -> Store` (`R->W`) | **Preserved** | Relaxed | Relaxed | **Preserved** | `LB` |
| `Store -> Store` (`W->W`) | **Preserved** | Relaxed | Relaxed | **Preserved** | `MP`, `2+2W` |
| `Store -> Load` (`W->R`) | Relaxed (unless `MFENCE`/`LOCK`) | Relaxed | Relaxed | Relaxed | `SB` (allowed), `SB+MFENCE` (forbidden) |
| Multicopy Atomicity (MCA) | **Yes** | **Yes** (ARMv8 revised) | **Yes** | **Yes** | `IRIW` (with `R->R` order) |

In the `ArMOR` framework (Lustig et al., ISCA 2015), a Dynamic Binary Translator acts as a **memory consistency model (MCM) shim** translating guest memory events into host memory events plus barriers/annotations so that every host-admissible execution projects to a guest-admissible `x86-TSO` execution (refinement soundness: $\mathcal{E}_{\text{host}}(\llbracket P \rrbracket) \subseteq \mathcal{E}_{\text{x86-TSO}}(P)$). The difficulty is asymmetric: enforcing `W->R` unnecessarily (e.g., via `STLR -> LDAR`) is *sound* (strictly stronger than TSO) but destroys store-buffer latency hiding, whereas dropping `R->R` or `W->W` is *unsound* and breaks lock-free algorithms (`MP`, `WRC`, `2+2W`, `LB`).

#### 1.2 Hardware TSO Mode: Apple Silicon `ACTLR_EL1` and RISC-V `Ztso`

`Basis: source + documentation`

Rather than injecting per-access barriers into translated ARM64 code, Apple Silicon implements dedicated microarchitectural compatibility modes configured via privileged `ACTLR_EL1` control bits, defined in `apple-oss-distributions/xnu` (`osfmk/arm64/proc_reg.h:3227-3236`):

```c
#define APSTATE_G_SHIFT   (0)
#define APSTATE_P_SHIFT   (1)
#define APSTATE_A_SHIFT   (2)
#define APSTATE_AP_MASK   ((1ULL << APSTATE_A_SHIFT) | (1ULL << APSTATE_P_SHIFT))

#define ACTLR_EL1_EnTSO   (1ULL << 1)
#define ACTLR_EL1_EnAPFLG (1ULL << 4)
#define ACTLR_EL1_EnAFP   (1ULL << 5)
#define ACTLR_EL1_EnPRSV  (1ULL << 6)
```

- **`ACTLR_EL1_EnTSO` (bit 1)**: Switches the core into hardware Total Store Ordering for the active thread (context-switched per thread by XNU for Rosetta 2 processes, and exposed to Linux user space on Apple Silicon via Asahi Linux's `prctl(PR_SET_MEM_MODEL, PR_SET_MEM_MODEL_TSO)`). Plain `LDR`/`STR` and NEON/SIMD accesses execute with `x86-TSO` ordering natively in hardware without software fences or `SIGBUS` alignment traps.
- **`ACTLR_EL1_EnAPFLG` (bit 4)** and **`APSTATE_{G,P,A}`**: Hardware support for alternative flag semantics (including x86 Parity `PF` and Adjust `AF` computation).
- **`ACTLR_EL1_EnAFP` (bit 5)**: Enables `FEAT_AFP` (Alternate Floating-Point behavior), matching x86 IEEE-754 NaN payload propagation and flush-to-zero semantics on ARM64 FP/SIMD units.
- On RISC-V, the ratified **`Ztso`** extension strengthens plain `LD`/`SD` to TSO ordering natively, while non-`Ztso` `RVWMO` cores offer **`fence.tso`** (`0x8330000f`, encoding `fm=0b1000, pred=rw, succ=rw`), which enforces `R->R`, `R->W`, and `W->W` without serializing `W->R`.

#### 1.3 Software & Hybrid TSO Lowerings Across QEMU TCG, FEX-Emu, and Box64

`Basis: source + derived`

Direct inspection of all three open-source DBT codebases reveals four sharply distinct lowering architectures:

1. **QEMU TCG (`qemu/qemu` @ `08c9bbb825148dec9669f5184ecf18823bb6d631`)**:
   - Guest default ordering is declared in `target/i386/tcg/tcg-cpu.c:162-168`:
     ```c
     const TCGCPUOps x86_tcg_ops = {
         .mttcg_supported = true,
         .precise_smc = true,
         .guest_default_memory_order = TCG_MO_ALL & ~TCG_MO_ST_LD,
     ```
   - Host default ordering is `TCG_TARGET_DEFAULT_MO = 0` on both `aarch64` (`tcg/aarch64/tcg-target-mo.h:10`) and `riscv64` (`tcg/riscv64/tcg-target-mo.h:10`), versus `TCG_MO_ALL & ~TCG_MO_ST_LD` on `x86_64` (`tcg/x86_64/tcg-target-mo.h:17`).
   - On every guest load (`tcg/tcg-op-ldst.c:258`), `tcg_gen_qemu_ld_int` calls `tcg_gen_req_mo(TCG_MO_LD_LD | TCG_MO_ST_LD)`. Masking with `guest_mo` (`~TCG_MO_ST_LD`) yields `TCG_MO_LD_LD`. On AArch64 (`tcg/aarch64/tcg-target.c.inc:1611-1621`), `tcg_out_mb` emits **`DMB ISHLD`** (`DMB_ISH | DMB_LD`). On RV64 (`tcg/riscv64/tcg-target.c.inc:1670-1686`), `tcg_out_mb` emits **`fence r, r`** (`0x0220000f`).
   - On every guest store (`tcg/tcg-op-ldst.c:302`), `tcg_gen_qemu_st_int` calls `tcg_gen_req_mo(TCG_MO_LD_ST | TCG_MO_ST_ST)`. Because AArch64 lacks a combined load-store + store-store barrier weaker than full `DMB ISH`, `sync[TCG_MO_LD_ST | TCG_MO_ST_ST]` falls into the default table entry `[0 ... TCG_MO_ALL] = DMB_ISH | DMB_LD | DMB_ST` (**full `DMB ISH` before every store!**). On RV64, `tcg_out_mb` ORs `0x02100000 | 0x01100000 = 0x03100000` (`fence rw, w`).
   - **Key subtlety (Derived)**: Because QEMU emits `DMB ISH` *before* every store and `DMB ISHLD` *before* every load, a `Store` followed by a `Load` executes `DMB ISH; STR; DMB ISHLD; LDR`. Since `DMB ISHLD` only orders prior *loads*, `Store -> Load` (`SB`) is **not** serialized—preserving exact `x86-TSO` semantics without over-constraining `SB`, while `tcg_optimize()` merges adjacent barriers when no memory op intervenes (`docs/devel/multi-thread-tcg.rst:300-303`). Furthermore, `tcg_gen_mb` emits nothing in non-`CF_PARALLEL` (single-vCPU) mode.

2. **FEX-Emu (`FEX-Emu/FEX` @ `be66e03d65217f53a7a2e5af46473cc9a79ce3f8`)**:
   - **Tiered GPR TSO emission** (`FEXCore/Source/Interface/Core/JIT/MemoryOps.cpp:767-853` for `LoadMemTSO`; `1791-1861` for `StoreMemTSO`):
     - *Tier 1 (`SupportsTSOImm9`, `FEAT_LRCPC2`)*: Emits `LDAPUR{B,H,W,X}` (with 9-bit signed offset) + `NOP` (for >8-bit loads), and `NOP` + `STLUR{B,H,W,X}` for stores.
     - *Tier 2 (`SupportsRCPC`, `FEAT_LRCPC`)*: Emits `LDAPR{B,H,W,X}` + `NOP` for loads, and `NOP` + `STLR{B,H,W,X}` for stores. Crucially, under ARMv8.3-RCPC, `STLR -> LDAPR` is **not** ordered, matching `x86-TSO` (`SB` allowed) while blocking `MP`, `LB`, `2+2W`, `WRC`, and `IRIW`.
     - *Tier 3 (baseline `ARMv8.0`)*: Emits `LDAR{B,H,W,X}` + `NOP` for loads and `NOP` + `STLR{B,H,W,X}` for stores. This is sound but **over-constrains `SB`** because ARMv8 orders `STLR -> LDAR`.
     - *Vector/SIMD ops*: Emits plain `LDR`/`STR` (`S`/`D`/`Q`/`SVE ld1b/st1b`), adding `DMB ISHLD` after vector loads (`MemoryOps.cpp:848-851`) and `DMB ISH` before vector stores (`MemoryOps.cpp:1841-1844`) **only** when `VectorTSOEnabled` is true (default `false` in `Config.json.in:614-620`, trading strict vector TSO for throughput; similarly `MemcpySetTSOEnabled` defaults to `false` for `REP MOVS`/`REP STOS`, `Config.json.in:622-629`).
     - *PE Volatile Metadata*: `Config.json.in:660-665` and `SyscallsSMCTracking.cpp:342-345` ingest Windows PE volatile-metadata tables (`CTX->AddForceTSOInformation(...)`) to restrict TSO barriers selectively to instructions not proven thread-local/non-volatile by MSVC/Clang!
   - **Silicon Erratum 3877900 Workaround (`Source/Common/HostFeatures.cpp:448-475`)**: On ARM `Neoverse V2`, `V3`, `V3AE`, `Cortex-X3`, `X4`, `X925`, `C1-Ultra`, and `C1-Premium`, `LDAPUR`/`LDAPURB`/`LDAPURH` execute with full **`LDAR` Load-Acquire ordering** instead of weaker `LDAPR` ordering (silently serializing `STLR -> LDAPUR`). FEX parses `MIDR_EL1` across all host CPUs and forces `HostFeatures->SupportsTSOImm9 = false` on affected cores (matching LLVM PR #124274), falling back to `LDAPR` (`FEAT_LRCPC`).
   - **Concurrent `SIGBUS` Unaligned Half-Barrier Backpatching (`FEXCore/Source/Utils/ArchHelpers/Arm64.cpp:2103-2185`)**: On ARM64 without `FEAT_LSE2` (or on accesses crossing a 16-byte / cache-line boundary), `LDAR`/`LDAPR`/`LDAPUR`/`STLR`/`STLUR` fault with `SIGBUS` on unaligned addresses. FEX's `HandleUnalignedAccess` acquires a per-block spinlock (`InlineTail->SpinLockFutex`) and **mutates the JIT code buffer in-place in strict reverse/barrier-first release order**:
     - *Load (`[0] ldapur/ldapr/ldar ; [1] nop`)*:
       1. `std::atomic_ref<uint32_t>(PC[1]).store(DMB_LD, std::memory_order_release)` (`DMB ISHLD`, `0xD5033DBF`).
       2. `std::atomic_ref<uint32_t>(PC[0]).store(LDR/LDUR, std::memory_order_release)`.
       3. `ClearICache(&PC[0], 8)` (`__builtin___clear_cache`), return PC adjustment `0` to re-execute `PC[0]`.
     - *Store (`[-1] nop ; [0] stlur/stlr`)*:
       1. `std::atomic_ref<uint32_t>(PC[-1]).store(DMB, std::memory_order_release)` (`DMB ISH`, `0xD5033BBF`).
       2. `std::atomic_ref<uint32_t>(PC[0]).store(STR/STUR, std::memory_order_release)`.
       3. `ClearICache(&PC[-1], 8)`, return PC adjustment `-4` to back up and execute the newly inserted `DMB ISH` before the store.
     - **Why ordering is load-bearing**: Patching `PC[0]` to plain `LDR` *before* writing `DMB_LD` to `PC[1]` would expose a concurrent thread to `LDR; NOP`, breaking `MP`, `WRC`, and `IRIW`. Writing `DMB_LD` first ensures a racing thread executes either `LDAPR; DMB ISHLD` (over-barriered, sound) or `LDR; DMB ISHLD` (sound). Conversely, `Config.json.in:636-637` warns that once a site is backpatched, subsequent *aligned* accesses through that site also execute `LDR+DMB_LD`/`DMB+STR` rather than atomic acquire/release instructions (losing sub-word/cross-line atomicity on non-`LSE2` cores).

3. **Box64 (`ptitSeb/box64` @ `6f0df3efe29aedae73e516277ce9cb2378779960`)**:
   - **Heuristic Write-Sequence (`SEQ`) StrongMem Levels (`src/dynarec/dynarec_helper.h:9-211`)**: Box64 defines a `SEQ` as a control-flow-bounded run of instructions containing at least one guest store.
     - `STRONGMEM=0` (default): No barriers on normal loads/stores.
     - `STRONGMEM=1` (`STRONGMEM_LAST_WRITE`): Emits `DMB_TSO()` before the first scalar store (`WILLWRITE`), before the last scalar store (`WILLWRITE`), and at the end of the `SEQ` (`SMEND`). Under `BOX64_DYNAREC_WEAKBARRIER=1`, these weaken to `DMB_ISHLD` (start) and `DMB_ISHST` (last write / end); under `WEAKBARRIER=2`, the pre-last-write barrier is omitted.
     - `STRONGMEM=2` (`STRONGMEM_SIMD_WRITE`): Extends level 1 to SIMD stores (`SMWRITE2()`).
     - `STRONGMEM=3` (`STRONGMEM_SEQ_WRITE`): Additionally emits `DMB_TSO()` after every 3rd store inside a `SEQ` (`if (++dyn->smwrite >= 3)`).
     - `STRONGMEM=4` (`STRONGMEM_QEMU`): Activates `SMREAD()` (`DMB_ISHLD()` before every guest load, `dynarec_helper.h:141-146`) and emits `DMB_TSO()` after every guest store (`dynarec_helper.h:112-113`). Notably, Box64's auto-detection (`docs/USAGE.md:313,327,377,503`) automatically forces `STRONGMEM=1` for `MonoBleedingEdge`, `libjvm`, and Unity, and **`STRONGMEM=4` specifically for Intel `oneTBB`'s lock-free scheduler**.
   - **Hardware LRCPC fast path (`src/dynarec/arm64/dynarec_arm64_pass0.h:43-56`)**: When `strongmem > 0` and the host advertises `cpuext.lrcpc && cpuext.lrcpc2 && cpuext.uscat` (`FEAT_LRCPC + FEAT_LRCPC2 + FEAT_LSE2`), Box64 sets `use_lrcpc = 1` and clears `x64.strongmem = 0` on instructions lowered via `LDAPUR`/`STLUR` (respecting `VolatileFenceGetLevel(ip, ...)` for Windows PE volatile metadata).
   - **RISC-V `fence.tso` hardware quirk (`src/dynarec/rv64/rv64_emitter.h:602-617`)**: Box64 maps `DMB_ISH() -> fence rw,rw`, `DMB_ISHLD() -> fence r,rw`, `DMB_ISHST() -> fence w,w`, and emits `FENCE_TSO()` (`0x8330000f`) inside `DMB_TSO()` **only** when `cpuext.vector && !cpuext.xtheadvector` (avoiding illegal-instruction traps on pre-RVA22 T-Head C906/C910 cores), otherwise falling back to `fence rw,rw`.
   - **Critical architectural asymmetry (Derived + Execution)**: Because `DMB_TSO()` defaults to `DMB_ISH()` on ARM64 (`dynarec_helper.h:240`) and `SMWRITE()` is emitted *after* the store instruction, `Box64 STRONGMEM=4` on ARM64 executes `STR; DMB ISH; DMB ISHLD; LDR` and **over-constrains `SB`**, whereas `Box64 STRONGMEM=4` on RV64 (with `FENCE_TSO()`) and `QEMU TCG` preserve `SB`. More critically, `Box64 STRONGMEM=1..3` emit **zero barriers on read-only sequences** (`SMREAD()` is empty), leaving `MP`, `WRC`, and `IRIW` **unsound** on weak ARMv8/RV64 hosts!

#### 1.4 Axiomatic Litmus Verification Matrix

`Basis: execution` (reproducible Python axiomatic checker in **Evidence**; multicopy-atomic host):

| Translation Scheme | `SB (0,0)` (TSO: Allow) | `SB+MFENCE` (TSO: Forbid) | `MP (1,0)` (TSO: Forbid) | `LB (1,1)` (TSO: Forbid) | `2+2W` (TSO: Forbid) | `WRC` (TSO: Forbid) | `IRIW` (TSO: Forbid) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`x86-TSO` (normative)** | `ALLOW` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` |
| **Apple `ACTLR_EL1.EnTSO` / RV `Ztso`** | `ALLOW` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` |
| **FEX `FEAT_LRCPC` (`LDAPR`+`STLR`)** | `ALLOW` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` |
| **FEX `ARMv8.0` / Erratum `3877900` (`LDAR`/`LDAPUR`+`STLR`)** | **`OVER-STR`** | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` |
| **QEMU TCG (`DMB ISH`+`STR`, `DMB ISHLD`+`LDR`) / Box64 `SM=4` RV64** | `ALLOW` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` |
| **Box64 `STRONGMEM=4` ARM64 (`STR`+`DMB ISH`, `DMB ISHLD`+`LDR`)** | **`OVER-STR`** | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` |
| **FEX Half-Barrier Backpatch (`LDR; DMB_LD` / `DMB; STR`)** | `ALLOW` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` | `FORBID` |
| **Box64 `STRONGMEM=1..3` (write-SEQ only, `SMREAD=nop`)** | `ALLOW` | `FORBID` | **`UNSOUND!`** | `FORBID` | `FORBID` | **`UNSOUND!`** | **`UNSOUND!`** |
| **Broken FEX patch order (`PC[0]=LDR` before `PC[1]=DMB_LD`)** | `ALLOW` | `FORBID` | **`UNSOUND!`** | `FORBID` | `FORBID` | **`UNSOUND!`** | **`UNSOUND!`** |
| **Bare `ARMv8`/`RVWMO` (`Box64 STRONGMEM=0`)** | `ALLOW` | `FORBID` | **`UNSOUND!`** | **`UNSOUND!`** | **`UNSOUND!`** | **`UNSOUND!`** | **`UNSOUND!`** |

---

### 2. Self-Modifying Code (SMC), Dual-Mapped Guest JITs, and Relaxed Instruction Fetch

`Basis: normative + source`

#### 2.1 The Guest-to-Host Cache Coherence Gap

On `x86-64`, instruction caches are hardware-coherent with data stores (requiring only a branch or serializing instruction for cross-modifying code). On `ARMv8-A` (Simner et al., ESOP 2020) and `RISC-V`, data caches (`D-cache`) and instruction caches (`I-cache`) are **not coherent**: a store to a translated JIT code buffer or patched jump target is **not** guaranteed to be observed by instruction fetches on the same or sibling cores until the architectural maintenance sequence executes:

- **ARMv8-A writer + reader sequence** (Simner et al., ESOP 2020):
  1. Writer core: `STR` (write new host instruction word, 32-bit aligned) $\to$ `DC CVAU` (clean D-cache line to Point of Unification, unless `CTR_EL0.IDC = 1`) $\to$ `DSB ISH` $\to$ `IC IVAU` (invalidate I-cache line across Inner Shareable domain, unless `CTR_EL0.DIC = 1`) $\to$ `DSB ISH`.
  2. Executing/reader core: **`ISB`** (or exception entry/return) to flush the fetch/decode pipeline.
  3. **Concurrent Modification Restriction (ARM ARM CMODX)**: On ARMv8-A, concurrently executing an instruction word while another core overwrites it is architecturally `CONSTRAINED UNPREDICTABLE` *unless* both old and new instructions belong to the small concurrent-modification-safe set (`B`, `BL`, `BRK`, `HVC`, `ISB`, `NOP`, `SMC`, `SVC`, `UDF`, `BKPT`). Notice that FEX's `SIGBUS` backpatching (`Arm64.cpp:2108-2163`) overwrites `LDAPR`/`STLR` with `LDR`/`STR` and `NOP` with `DMB`—outside the strict ARMv8 CMODX set! FEX relies on `SpinLockFutex` + strict `PC[1]`-then-`PC[0]` release stores + `__builtin___clear_cache`, which works on existing ARM64 microarchitectures with single-copy-atomic 32-bit instruction fetch but remains an architectural boundary (see **Boundaries**).
- **RISC-V**: Uses `FENCE.I` (`0x0000100f`, Box64 `rv64_emitter.h:619-620`) for local thread I-cache sync; cross-hart I-cache invalidation requires the Linux `riscv_flush_icache` syscall (triggering cross-hart IPIs executing `fence.i`).

#### 2.2 Detecting Guest SMC Across QEMU, FEX-Emu, and Box64

Guest programs—and especially guest JITs (`V8`, `SpiderMonkey`, `HotSpot`, `.NET CoreCLR`)—modify x86 code pages via ordinary stores, `mprotect(RW -> RX)`, or **dual-mapped (`RW` + `RX`) shared memory aliases** (`memfd_create` / `shm_open` mapped twice at distinct virtual addresses):

| Mechanism | QEMU TCG (`accel/tcg/`) | FEX-Emu (`SyscallsSMCTracking.cpp`) | Box64 (`src/dynarec/dynablock.c`) |
| :--- | :--- | :--- | :--- |
| **Default SMC detection** | Page write-protection (`page_protect` clears host `PROT_WRITE`, remembers `PAGE_WRITE_ORG`); `SIGSEGV` invokes `page_unprotect()` (`user-exec.c:125-128`) and invalidates TBs on that page. | `CONFIG_SMC_MTRACK` (`Config.json.in:594`): write-protects translated guest code pages (`PROT_READ`); write `SIGSEGV` triggers `InvalidateGuestCodeRange` + `mprotect(PROT_READ \| PROT_WRITE)` (`SyscallsSMCTracking.cpp:88-115`). | Page write-protection (`protectDB`) + fast code checksum (`X31_hash_code` / `ARCH_CRC`, `dynablock.c:89-96`) verified on entry to unprotected (`dirty`) blocks (`BOX64_DYNAREC_DIRTY`). |
| **Dual-mapped `RW`+`RX` JIT aliases** | SoftMMU tracks by *guest physical address* (`tb_invalidate_phys_range`), catching aliases automatically; `linux-user` tracks virtual pages and requires explicit `mprotect`/`mmap` interception. | Tracks `VMATracking::MappedResource` linked lists; on a write fault, walks `VMA->ResourceNextVMA` and computes `FaultBaseMirrored = Offset - VMA->Offset + VMA->Base`, invalidating **every** virtual alias of the backing inode (`SyscallsSMCTracking.cpp:104-112`)! | Tracks `prot` bitmaps per VA page; `unprotectDB` / `hotpage` heuristics fall back to checksummed dirty blocks when pages flip rapidly between write and execute. |
| **Cross-thread TB unlinking** | `tb_set_jmp_target()` patches direct jumps atomically under `tb->jmp_lock`; full code-cache flushes use `async_safe_run_on_cpu()` (`tb-maint.c:771-809`) to quiesce all vCPUs. | Acquires signal-deferred `CodeInvalidationMutex` (`GuardSignalDeferringSectionWithFallback`, `SyscallsSMCTracking.cpp:343,386`); invalidates per-thread/shared lookup caches before unprotecting guest memory. | `InvalidDynablock()` (`dynablock.c:98-118`) removes jumptable entries immediately, patches `callrets` with `ARCH_UDF`, calls `ClearCache(db->block, db->size)`, and defers freeing until safe (`FreeInvalidDynablock`). |
| **Precise self-modifying current instruction** | `.precise_smc = true` (`tcg-cpu.c:164`): detects write to currently executing TB, re-translates remaining instructions after the modifying store. | `CONFIG_SMC_FULL` mode checks guest code bytes before every block execution (slowest, guarantees exact SMC even across unintercepted shared memory). | `is_addr_autosmc(addr)` (`dynarec_helper.h:225`) triggers per-instruction/single-step re-verification on hot self-modifying sites. |

---

### 3. Lazy Condition Codes (`EFLAGS`) and 80-Bit `x87` Emulation

`Basis: source + documentation`

#### 3.1 Lazy `EFLAGS` Materialization and ARMv8 Flag Extensions

Every x86 integer ALU instruction updates up to six arithmetic status flags (`CF`, `PF`, `AF`, `ZF`, `SF`, `OF`), whereas ARM64 `NZCV` lacks `PF` (low-byte parity) and `AF` (half-carry bit 4), and RISC-V has no condition-code register at all.

- **QEMU TCG (`target/i386/cpu.h:1543-1640`, `target/i386/tcg/translate.c:301-315`)**: Defers flag evaluation by storing raw operands `(CC_DST, CC_SRC, CC_SRC2)` and an enum tag `CCOp` (`CC_OP_ADDB..Q`, `CC_OP_SUBB..Q`, `CC_OP_LOGICB..Q`, `CC_OP_EFLAGS`, `CC_OP_DYNAMIC`, etc.). Live operand tracking (`cc_op_live_[]`) eliminates dead `CC_SRC`/`CC_SRC2` stores, and `tcg_gen_insn_start(pc_arg, dc->cc_op, 0)` (`translate.c:3603`) embeds the compile-time `cc_op` into the unwind table so faults reconstruct `env->cc_op` lazily without emitting per-instruction stores to `CPUX86State`.
- **FEX-Emu (`OpcodeDispatcher/Flags.cpp`, `IR/Passes/RedundantFlagCalculationElimination.cpp`, `HostFeatures.cpp:370-371,507-508`)**:
  - Uses SSA-level dead-flag elimination (`RedundantFlagCalculationElimination`) across basic blocks/superblocks plus deferred `NZCV` caching (`CalculateDeferredFlags`, `Flags.cpp:254-267`) and explicit `InvalidatePF_AF()` on operations like `MUL`/`UMUL`/`Logical` (`Flags.cpp:397-432`).
  - Exploits **`FEAT_FLAGM`** (`CFINV`, `RMIF`, `SETF8`, `SETF16`) to invert carry for `SUB`/`CMP` (`x86` borrow vs. `ARM64` inverted carry) and set `NZ` directly from 8/16-bit values, plus **`FEAT_FLAGM2`** (`AXFLAG`/`XAFLAG`) for x86-compatible `FCOMI`/`COMISS` unordered NaN flag layouts (`ZF=1, PF=1, CF=1`).
- **Box64 (`docs/USAGE.md:89-91,148-155`, `arm64_emitter.h:2281`, `dynarec_arm64_helper.h`)**:
  - Performs backward liveness analysis across a dynablock (`x64.need_before`, `x64.gen_flags`), using native ARM64 flags (`IFNATIVE(NF_SF|NF_VF)`, `SETF8`/`SETF16` when `cpuext.flagm`, `CFINV`) whenever a flag producer feeds a branch directly.
  - Exposes **`BOX64_DYNAREC_SAFEFLAGS`** (`0`: assume `CALL`/`RET` never consume flags; `1` [default]: most `RET`s preserve flags, most `CALL`s do not; `2`: preserve flags across all `CALL`/`RET` and edge cases). Setting `SAFEFLAGS=0` breaks non-ABI hand-written assembly (e.g., routines returning carry flags in `CF`), illustrating the classic DBT soundness-vs-speed trade-off at call boundaries.

#### 3.2 `x87` 80-Bit Extended Precision and Stack Register Allocation

Legacy x86 floating-point code operates on an 8-deep circular register stack (`ST(0)..ST(7)`) with an 80-bit format (1 sign bit, 15-bit biased exponent, **explicit integer bit**, 63-bit fraction; 64-bit significand), 3-bit `TOP` pointer, 16-bit `FCW` (precision/rounding control), 16-bit `FSW`, and 16-bit `FTW` tag word. Neither `ARM64` nor `RV64` implements 80-bit binary floating point in hardware.

| Engine | Default Precision Mode | Fast Reduced-Precision Option | Stack Virtualization Strategy |
| :--- | :--- | :--- | :--- |
| **QEMU TCG** (`target/i386/tcg/fpu_helper.c`) | Full 80-bit software `floatx80` (`SoftFloat`) respecting `FCW` precision control (`set_floatx80_rounding_precision`). | None (always exact `floatx80`). | Architectural `env->fpregs[8]` indexed via `(env->fpstt + i) & 7`. |
| **FEX-Emu** (`X87.cpp`, `X87F64.cpp`, `x87StackOptimizationPass.cpp`) | Full 80-bit `F80` (`_F80CVTTo`, `cephes_128bit` / softfloat helpers, `X87.cpp:61-71`). | `X87ReducedPrecision=true` (`Config.json.in:666-668`, `X87F64.cpp:26-62`): lowers `x87` directly to hardware ARM64 IEEE-754 `binary64` (`F64`), explicitly ignoring `FCW` rounding-precision bits (`X87F64.cpp:33,52`). | `x87StackOptimizationPass` models a virtual `FixedSizeStack` with `StackSlot::{UNUSED, INVALID, VALID}` and tracks compile-time `TopOffset` (`x87StackOptimizationPass.cpp:48-77`), eliding dynamic `TOP` rotations inside a block and falling back to `_StackForceSlow()` on `FLDCW`/`FLDENV`/`SetX87FTW`. |
| **Box64** (`docs/USAGE.md:329-331`, `dynarec_arm64_d8.c`) | Host `double` (`binary64`) inside DynaRec (`EXT_CACHE_ST_D` / `EXT_CACHE_ST_F` / `EXT_CACHE_ST_I64`, `dynarec_rv64_private.h:15-18`) with optional `long double` / soft-80-bit in interpreter paths. | `BOX64_DYNAREC_X87DOUBLE=1` forces 64-bit double emulation uniformly (avoids 80-bit conversion overhead; breaks numerical code relying on 64-bit significand or 15-bit exponent $> 10^{308}$). | Per-block static x87 stack cache mapped to host FP/vector registers, flushed to `x64emu_t` on block exit and signal boundaries. |

---

### 4. Precise Guest Signal Frames (`ucontext_t`) Under Superblock Optimization

`Basis: source + execution + documentation`

#### 4.1 The Superblock Reordering vs. Signal-Precision Paradox

Real x86-64 workloads rely on **precise synchronous signals**: JVM/V8 null-check elimination catches `SIGSEGV`, inspects `ucontext->uc_mcontext.gregs[REG_RIP]`, and rewrites `RIP` to a deoptimization stub; Wine/Proton translates `SIGSEGV`/`SIGILL`/`SIGFPE` into Windows Structured Exception Handling (SEH); guard-page stack growth and anti-cheat self-checks inspect exact `RAX..R15`, `RSP`, `RIP`, `EFLAGS`, and `xstate` (`fpstate`/`ymmh`).

Consider the 4-instruction x86 basic block verified in our executable probe (**Evidence**):
```asm
0x401000: add rax, 1       ; RAX: 10 -> 11, ZF = 0
0x401004: mov rbx, [rsi]   ; valid load -> 0xCAFE
0x401007: mov rcx, [rdi]   ; FAULTS with SIGSEGV when rdi == 0
0x40100a: add rax, 2       ; coalesced / dead-flag target
```
If a DBT aggressively coalesces `add rax, 1` + `add rax, 2` into `add rax, 3`, hoists `[rdi]` above `[rsi]`, and eliminates the intermediate `ZF` write before `0x40100a`, then upon `SIGSEGV` at `0x401007` the guest signal handler observes:
- **`RAX = 13`** instead of `11`,
- **`RBX = 0`** instead of `0xCAFE`,
- **`ZF = 1`** instead of `0`.

Every production DBT resolves this tension via one of two mechanisms:

1. **Hardware Speculative Commit/Rollback (`Transmeta Code Morphing Software`, Dehnert et al., CGO 2003)**:
   - The Transmeta Crusoe/Efficeon VLIW hardware provided **shadow architectural registers** and a **gated store buffer**. Translated superblocks freely reordered loads, hoisted arithmetic, and eliminated intermediate flag writes across faulting boundaries. At commit points, a hardware `commit` instruction atomically copied working registers to shadow registers and released buffered stores. On any synchronous trap (`SIGSEGV`/page fault), a hardware `rollback` discarded working registers and buffered stores and fell back to the exact **in-order interpreter** from the last committed guest `EIP`, guaranteeing 100% precise x86 exceptions *without* inhibiting superblock scheduling!
2. **Software Unwind Tables & Restricted Reordering (QEMU, FEX-Emu, Box64)**:
   - Without hardware shadow registers, software DBTs **forbid reordering trapping memory ops across each other or clobbering architectural state needed before a faulting instruction**, and reconstruct lazy metadata (`RIP`, `EFLAGS`, cached registers) from compact host-PC unwind tables:
     - **QEMU TCG** (`accel/tcg/user-exec.c:65-96`, `target/i386/tcg/tcg-cpu.c:87-117`): `adjust_signal_pc` adjusts the faulting host PC by `+GETPC_ADJ` so `cpu_restore_state_from_tb` searches the compressed `tcg_gen_insn_start` metadata table and invokes `x86_restore_state_to_opc`, restoring exact `env->eip` (handling `CF_PCREL` page offsets) and `env->cc_op`.
     - **FEX-Emu** (`SignalDelegator.cpp:140-159`, `GuestFramesManagement.cpp:41-206`): On any host signal, FEX backs up the host `ucontext_t` onto a 16-byte-aligned stack frame (`ArchHelpers::Context::BackupContext`), maps host fault info to x86 `si_code`/`err_code` (`X86_PF_INSTR`), materializes compacted `EFLAGS`, `gregs`, `mxcsr`, `FCW`/`FSW`/`AbridgedFTW`, and rotated `x87` registers `mm[(i + TOP) % 8]` into a synthetic `FEXCore::x86_64::ucontext_t`, and delivers it to the guest handler. Upon `rt_sigreturn`, `RestoreFrame_x64` (`GuestFramesManagement.cpp:131-143`) checks whether the guest handler **modified `RIP`** (`Context->OriginalRIP != guest_uctx->uc_mcontext.gregs[FEX_REG_RIP]`); if so, it **cannot** resume at the original host JIT PC—it copies all guest GPRs/flags/xstate back into `Frame->State` and hijacks the host `ucontext` PC to `Config.AbsoluteLoopTopAddressFillSRA` (re-entering the top of the JIT dispatcher and reloading Static Register Allocation)!
     - **Box64** (`src/libtools/signals.c:386-495`, `dynarec_arm64_pass3.h:22-27`): Pass 3 records a compact `instsize` table mapping every translated x86 instruction byte-length to its emitted native 4-byte instruction count (`addInst(dyn->instsize, ..., x64.size, size/4)`). On `SIGSEGV`/`SIGBUS`, Box64 walks `instsize` to recover exact `x64pc` and `x64emu_t`, synthesizes `x64_ucontext_t` + `xstate` (setting magic `0x46505853` and resetting FPU/XMM/MXCSR to `0x1f80` before entering the guest handler, matching Linux `fpu__clear_user_states`), and translates `X64_TRAPNO` (`14` page fault, `13` GPF, `17` alignment check).

---

### 5. Native Library Thunking and Bidirectional Host/Guest Callbacks

`Basis: source`

Translating massive C/C++ graphics, audio, and libc libraries (`libGL`, `libvulkan`, `libX11`, `libasound`, `libc`) instruction-by-instruction wastes both JIT compile time and execution bandwidth. Both Box64 and FEX-Emu implement **mixed-mode native library thunking**, which introduces a sharp FFI/ABI soundness boundary whenever host libraries invoke **guest function pointers** (callbacks such as `qsort` comparators, `VkAllocationCallbacks`, X11 error handlers, or `pthread_create` entry points):

- **Box64 Bridges (`src/tools/bridge.c:110-208`)**:
  - Guest-to-host calls resolve symbol imports to synthetic x86 **bridge stubs** allocated via `AddBridge` / `AddAutomaticBridge` (a compact `0xCC` / `INT3` or custom trap opcode + pointer to a C `wrapper_t` and target host `fnc`, deduplicated via `kh_get(bridgemap, ...)`). When the dynarec encounters a bridge address, it exits directly to the native wrapper `w(emu, fnc)` which marshals SysV x86-64 ABI arguments (`RDI, RSI, RDX, RCX, R8, R9, XMM0..7`) to native ARM64/RV64 registers.
  - Host-to-guest callbacks are wrapped by generating native C callback trampolines (using `addAlternate` / `RunFunctionFmt`) that capture the guest x86 function pointer, enter `x64emu_t` emulation on the current thread, and marshal the return value back to the native host library.
- **FEX-Emu Host-to-Guest Trampolines (`Source/Tools/LinuxEmulation/Thunks.cpp:43-88`)**:
  - Uses explicit guest-side + host-side thunk `.so` pairs (`libGL-guest.so` / `libGL-host.so`) that pack arguments into a uniform struct (`HostPacker` / `GuestUnpacker`).
  - For callbacks passed from guest code into a host library, FEX clones a machine-code template section (`HostToGuestTrampolineTemplate`, `Thunks.cpp:43-66`) paired with an adjacent `TrampolineInstanceInfo { void* HostPacker; uintptr_t CallCallback; uintptr_t GuestUnpacker; uintptr_t GuestTarget; }` (`Thunks.cpp:75-80`). When the host library invokes the native function pointer, the trampoline passes the instance info into `HostPacker`, invokes `CallCallback` to re-enter FEX's x86 JIT at `GuestUnpacker` $\to$ `GuestTarget`, and unpacks the result back across the host ABI.
- **Struct-Layout Verification Invariant (`Source/Tools/LinuxEmulation/CMakeLists.txt:93-161`)**: Because 32-bit x86 (`i386` 4-byte `uint64_t` alignment inside structs) and 64-bit `aarch64`/`x86-64` disagree on struct padding (notably `ioctl`, `stat`, `siginfo_t`, `ucontext_t`), FEX runs an automated build-time Clang AST verifier (`Scripts/StructPackVerifier.py`) asserting byte-for-byte field-offset equality across `x86_32`, `x86_64`, and `aarch64` headers.

## Boundaries

- **Apple Rosetta 2 internals — `unknown` / `not examined` (closed source)**: While `ACTLR_EL1_EnTSO`, `ACTLR_EL1_EnAPFLG`, `ACTLR_EL1_EnAFP`, and `ACTLR_EL1_EnPRSV` are directly verified in open-source `apple-oss-distributions/xnu` (`osfmk/arm64/proc_reg.h:3233-3236`), the closed-source Rosetta 2 AOT/JIT translator binary (`oahd` / `runtime`) was not reverse-engineered or executed in this study. Specifically, Rosetta 2's internal AOT caching format, exact `x87` software implementation, and macOS Mach exception/signal translation internals are `not examined`.
- **FEX `SIGBUS` in-place backpatching under strict ARMv8 CMODX — `unknown` (architectural vs. empirical gap)**: FEX's `HandleUnalignedAccess` (`Arm64.cpp:2108-2163`) concurrently overwrites `LDAPR`/`STLR` with `LDR`/`STR` and `NOP` with `DMB` using release-ordered 32-bit atomic stores and `__builtin___clear_cache`. Because `LDAPR`/`LDR`/`STLR`/`STR`/`DMB` are outside the ARMv8-A Concurrent Modification and Execution (CMODX) allowlist (Simner et al., ESOP 2020), architectural conformance on *arbitrary* future ARMv8 implementations is `unknown` (not formally guaranteed by the ARM ARM, even though it functions on current silicon where 32-bit instruction fetches are single-copy atomic and `DMB` precedes `LDR`/`STR` release).
- **Non-multicopy-atomic hosts (`ARMv7`, `POWER`) — `known not to apply`**: The axiomatic probe in **Evidence** assumes a multicopy-atomic (MCA) host (`ARMv8.0+` revised MCA or `RISC-V RVWMO`). On non-MCA hosts, `FEX FEAT_LRCPC` does not exist and half-barrier mappings without cumulative reader barriers (`DMB SY`/`hwsync`) fail `IRIW` and `WRC`.
- **Quantitative wall-clock microbenchmarks on physical ARM64/RV64 silicon — `not examined`**: This report establishes structural, source-level, and axiomatic soundness distinctions; empirical SPEC/game slowdown ratios across hardware SKUs (e.g., Apple M-series vs. Neoverse V2 vs. Oryon vs. RISC-V SpacemiT) were not measured on physical target hardware here.
- **Unaligned atomic RMW (`LOCK CMPXCHG` / `LOCK XADD` crossing cache lines) — `not examined` in full**: While FEX's `Arm64.cpp` contains split-lock / `CASPAL` `SIGBUS` handling (`Arm64.cpp:2098`) and Box64 provides `BOX64_DYNAREC_ALIGNED_ATOMICS` (`USAGE.md:64-65`), cross-cache-line `LOCK` split-atomicity emulation (requiring global stop-the-world locks or mutex-hashed address tables across processes) was not exhaustively audited across all three engines.
- **Over-strong claims rejected**: Having `FEAT_LRCPC2` (`LDAPUR`/`STLUR`) in `ID_AA64ISAR1_EL1` does **not** guarantee fast TSO emulation on ARMv8.4+ cores—ARM Erratum `3877900` silently degrades `LDAPUR` to full `LDAR` ordering on Neoverse V2/V3 and Cortex-X3/X4/X925/C1 cores. Likewise, `Box64` `STRONGMEM=1..3` does **not** soundly emulate `x86-TSO` for arbitrary lock-free C++11/Rust programs; only `STRONGMEM=4` (or hardware TSO / `use_lrcpc` on `LRCPC+LRCPC2+LSE2`) enforces reader-side `R->R` ordering.

## Evidence

### Primary Git Repository Sources (Observed `2026-11-19`)

1. **`qemu/qemu` @ `08c9bbb825148dec9669f5184ecf18823bb6d631`**:
   - `include/tcg/tcg-mo.h:28-46` — `TCGBar` (`TCG_MO_LD_LD`, `TCG_MO_ST_LD`, `TCG_MO_LD_ST`, `TCG_MO_ST_ST`, `TCG_MO_ALL`, `TCG_BAR_LDAQ`, `TCG_BAR_STRL`, `TCG_BAR_SC`).
   - `tcg/aarch64/tcg-target-mo.h:10` & `tcg/riscv64/tcg-target-mo.h:10` — `TCG_TARGET_DEFAULT_MO = 0`; `tcg/x86_64/tcg-target-mo.h:17` — `TCG_TARGET_DEFAULT_MO = (TCG_MO_ALL & ~TCG_MO_ST_LD)`.
   - `target/i386/tcg/tcg-cpu.c:87-117, 162-176` — `x86_tcg_ops` (`.mttcg_supported = true`, `.precise_smc = true`, `.guest_default_memory_order = TCG_MO_ALL & ~TCG_MO_ST_LD`, `x86_restore_state_to_opc`).
   - `tcg/tcg-op-ldst.c:117-124, 258, 302` — `tcg_gen_req_mo` barrier insertion before guest loads (`TCG_MO_LD_LD | TCG_MO_ST_LD`) and stores (`TCG_MO_LD_ST | TCG_MO_ST_ST`).
   - `tcg/aarch64/tcg-target.c.inc:1611-1621` & `tcg/riscv64/tcg-target.c.inc:1670-1686` — `tcg_out_mb` lowering to `DMB_ISH | DMB_LD/ST` and RISC-V `OPC_FENCE`.
   - `target/i386/cpu.h:1543-1643`, `target/i386/tcg/translate.c:301-315, 3590-3604` — `CCOp`, `cc_op_live_[]`, `tcg_gen_insn_start(pc_arg, dc->cc_op, 0)`.
   - `target/i386/tcg/fpu_helper.c:70-76` — `floatx80` software 80-bit constants/helpers.
   - `accel/tcg/tb-maint.c:771-809`, `accel/tcg/user-exec.c:65-128`, `docs/devel/multi-thread-tcg.rst:28-33, 154-170, 298-306`.
2. **`FEX-Emu/FEX` @ `be66e03d65217f53a7a2e5af46473cc9a79ce3f8`**:
   - `FEXCore/Source/Interface/Config/Config.json.in:592-668` — `SMCChecks` (`CONFIG_SMC_MTRACK`), `TSOEnabled`, `VectorTSOEnabled` (`false`), `MemcpySetTSOEnabled` (`false`), `HalfBarrierTSOEnabled` (`true`), `KernelUnalignedAtomicBackpatching`, PE volatile metadata, `X87ReducedPrecision` (`false`).
   - `Source/Common/HostFeatures.cpp:240-242, 299-302, 448-475, 497-516` — `FEAT_LRCPC`/`LRCPC2`/`LRCPC3`/`LSE2`/`AFP`/`FlagM`/`FlagM2` probing and ARM Cortex Erratum `3877900` MIDR blocklist disabling `SupportsTSOImm9`.
   - `FEXCore/Source/Interface/Core/JIT/MemoryOps.cpp:767-853, 1791-1861` — `LoadMemTSO` and `StoreMemTSO` 3-tier GPR lowering (`LDAPUR`/`LDAPR`/`LDAR` + `NOP`; `NOP` + `STLUR`/`STLR`) and optional vector `DMB ISHLD`/`DMB ISH`.
   - `FEXCore/Source/Utils/ArchHelpers/Arm64.cpp:106-124, 1932-1934, 2103-2185` — `HandleUnalignedAccess` lock-protected barrier-first atomic in-place backpatching and `ClearICache`.
   - `Source/Tools/LinuxEmulation/LinuxSyscalls/SyscallsSMCTracking.cpp:86-117, 139-145, 340-386` — `PROT_READ` write-fault handler walking `VMA->ResourceNextVMA` to invalidate mirrored `RW`/`RX` aliases, plus `AddForceTSOInformation`.
   - `FEXCore/Source/Interface/Core/OpcodeDispatcher/{Flags.cpp:38-75,254-432, X87.cpp:27-71, X87F64.cpp:26-62}` and `FEXCore/Source/Interface/IR/Passes/x87StackOptimizationPass.cpp:20-77`.
   - `Source/Tools/LinuxEmulation/LinuxSyscalls/SignalDelegator.cpp:140-159`, `SignalDelegator/GuestFramesManagement.cpp:29-230`, `Thunks.cpp:43-88`, `Source/Tools/LinuxEmulation/CMakeLists.txt:93-161`.
3. **`ptitSeb/box64` @ `6f0df3efe29aedae73e516277ce9cb2378779960`**:
   - `docs/USAGE.md:64-65, 89-95, 148-172, 308-332, 374-378, 500-504` — `STRONGMEM=0..4`, `SAFEFLAGS=0..2`, `X87DOUBLE`, `VOLATILE_METADATA`, `DIRTY`, oneTBB/Mono/libjvm auto-profiles.
   - `src/dynarec/dynarec_helper.h:9-241` — `SEQ` barrier definitions (`SMREAD`, `SMWRITE`, `SMWRITE2`, `WILLWRITE`, `SMSTART`, `SMEND`, `STRONGMEM_QEMU=4`, `DMB_TSO`).
   - `src/dynarec/arm64/dynarec_arm64_pass0.h:43-56`, `src/dynarec/arm64/dynarec_arm64_pass3.h:22-27`, `src/dynarec/arm64/arm64_emitter.h:396-411, 2281`.
   - `src/dynarec/rv64/rv64_emitter.h:602-625` — RV64 `FENCE_R_RW`, `FENCE_W_W`, `FENCE_RW_RW`, `FENCE_TSO` (`0x8330000f`), `DMB_TSO` `xtheadvector` guard, `FENCE_I`.
   - `src/dynarec/dynablock.c:49-122`, `src/libtools/signals.c:380-495`, `src/tools/bridge.c:110-208`.
4. **`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`**:
   - `osfmk/arm64/proc_reg.h:3227-3236` — `APSTATE_{G,P,A}`, `ACTLR_EL1_EnTSO`, `ACTLR_EL1_EnAPFLG`, `ACTLR_EL1_EnAFP`, `ACTLR_EL1_EnPRSV`.

### Peer-Reviewed Specifications & Literature

- J. C. Dehnert et al., *"The Transmeta Code Morphing Software: Using Speculation, Recovery, and Adaptive Retranslation to Address Real-Life Challenges"*, **CGO 2003**, DOI `10.1109/CGO.2003.1191529`.
- D. Lustig, C. Trippel, M. Pellauer, M. Martonosi, *"ArMOR: Defending Against Memory Consistency Model Mismatches in Heterogeneous Architectures"*, **ISCA 2015**, DOI `10.1145/2749469.2750378`.
- P. Sewell et al., *"x86-TSO: A Rigorous and Usable Programmer's Model for x86 Multiprocessors"*, **CACM** 53(7), 2010, DOI `10.1145/1785414.1785443`.
- C. Pulte et al., *"Simplifying ARM Concurrency: Multicopy-Atomic Axiomatic and Operational Models for ARMv8"*, **POPL 2018**, DOI `10.1145/3158107`.
- B. Simner et al., *"ARMv8-A System Semantics: Instruction Fetch in Relaxed Architectures"*, **ESOP 2020**, DOI `10.1007/978-3-030-44914-8_23`.

### Executable Verification Probe (Observed `2026-11-19`, Python 3.13, Stdlib Only)

Running the self-contained script below reproduces the exact 10-scheme $\times$ 7-litmus axiomatic soundness table (Section 1.4) and the superblock `ucontext_t` corruption counterexample (Section 4.1):

```python
#!/usr/bin/env python3
from dataclasses import dataclass
from typing import Dict, List, Set, Tuple

def has_cycle(nodes: Set[str], edges: Set[Tuple[str, str]]) -> bool:
    adj: Dict[str, List[str]] = {n: [] for n in nodes}
    for u, v in edges:
        adj.setdefault(u, []).append(v)
    state: Dict[str, int] = {}
    def dfs(u: str) -> bool:
        state[u] = 1
        for v in adj.get(u, []):
            st = state.get(v, 0)
            if st == 1 or (st == 0 and dfs(v)):
                return True
        state[u] = 2
        return False
    return any(state.get(n, 0) == 0 and dfs(n) for n in nodes)

@dataclass(frozen=True)
class Ev:
    id: str; tid: int; idx: int; kind: str; addr: str

TESTS = {
    "SB": ([Ev("W0x",0,0,"W","x"), Ev("R0y",0,1,"R","y"), Ev("W1y",1,0,"W","y"), Ev("R1x",1,1,"R","x")],
           {("R0y","W1y"), ("R1x","W0x")}, True),
    "SB+MFENCE": ([Ev("W0x",0,0,"W","x"), Ev("F0",0,1,"MFENCE",""), Ev("R0y",0,2,"R","y"),
                   Ev("W1y",1,0,"W","y"), Ev("F1",1,1,"MFENCE",""), Ev("R1x",1,2,"R","x")],
                  {("R0y","W1y"), ("R1x","W0x")}, False),
    "MP": ([Ev("W0x",0,0,"W","x"), Ev("W0y",0,1,"W","y"), Ev("R1y",1,0,"R","y"), Ev("R1x",1,1,"R","x")],
           {("W0y","R1y"), ("R1x","W0x")}, False),
    "LB": ([Ev("R0x",0,0,"R","x"), Ev("W0y",0,1,"W","y"), Ev("R1y",1,0,"R","y"), Ev("W1x",1,1,"W","x")],
           {("W1x","R0x"), ("W0y","R1y")}, False),
    "2+2W": ([Ev("W0x",0,0,"W","x"), Ev("W0y",0,1,"W","y"), Ev("W1y",1,0,"W","y"), Ev("W1x",1,1,"W","x")],
             {("W1x","W0x"), ("W0y","W1y")}, False),
    "WRC": ([Ev("W0x",0,0,"W","x"), Ev("R1x",1,0,"R","x"), Ev("W1y",1,1,"W","y"),
             Ev("R2y",2,0,"R","y"), Ev("R2x",2,1,"R","x")],
            {("W0x","R1x"), ("W1y","R2y"), ("R2x","W0x")}, False),
    "IRIW": ([Ev("W0x",0,0,"W","x"), Ev("W1y",1,0,"W","y"), Ev("R2x",2,0,"R","x"), Ev("R2y",2,1,"R","y"),
              Ev("R3y",3,0,"R","y"), Ev("R3x",3,1,"R","x")],
             {("W0x","R2x"), ("R2y","W1y"), ("W1y","R3y"), ("R3x","W0x")}, False),
}

def ppo(evs: List[Ev], mode: str) -> Set[Tuple[str, str]]:
    edges: Set[Tuple[str, str]] = set()
    by_t: Dict[int, List[Ev]] = {}
    for e in evs: by_t.setdefault(e.tid, []).append(e)
    for seq in by_t.values():
        seq.sort(key=lambda e: e.idx)
        has_w = any(e.kind == "W" for e in seq)
        for i in range(len(seq)):
            for j in range(i + 1, len(seq)):
                a, b = seq[i], seq[j]
                if "MFENCE" in (a.kind, b.kind): continue
                if any(seq[k].kind == "MFENCE" for k in range(i + 1, j)):
                    edges.add((a.id, b.id)); continue
                if mode == "exact_tso":
                    if not (a.kind == "W" and b.kind == "R"): edges.add((a.id, b.id))
                elif mode == "over_strong":
                    edges.add((a.id, b.id))
                elif mode == "write_seq_only":
                    if has_w and b.kind == "W": edges.add((a.id, b.id))
    return edges

for mode in ("exact_tso", "over_strong", "write_seq_only", "bare_weak"):
    res = {k: ("ALLOW" if not has_cycle({e.id for e in evs if e.kind != "MFENCE"}, ppo(evs, mode) | ext) else "FORBID")
           for k, (evs, ext, _) in TESTS.items()}
    print(f"{mode:16s}: {res}")

# Precise guest ucontext_t counterexample on faulting superblock
def run_guest_exact(rax0, rsi_mem, rdi_addr):
    rax, rbx, rcx, zf = rax0, 0, 0, 1
    rax += 1; zf = int(rax == 0); rbx = rsi_mem
    if rdi_addr == 0:
        return {"fault_rip": "0x401007", "RAX": rax, "RBX": rbx, "RCX": rcx, "ZF": zf}
    return {"fault_rip": None, "RAX": rax + 2, "RBX": rbx, "RCX": 0xBEEF, "ZF": int(rax + 2 == 0)}

def run_naive_reordered(rax0, rsi_mem, rdi_addr):
    rax, rbx, rcx, zf = rax0 + 3, 0, 0, 1
    if rdi_addr == 0:
        return {"fault_rip": "0x401007", "RAX": rax, "RBX": rbx, "RCX": rcx, "ZF": zf}
    return {"fault_rip": None, "RAX": rax, "RBX": rsi_mem, "RCX": 0xBEEF, "ZF": int(rax == 0)}

print("exact_ucontext  :", run_guest_exact(10, 0xCAFE, 0))
print("naive_ucontext  :", run_naive_reordered(10, 0xCAFE, 0))
```

Observed output:
- `exact_tso` (`EnTSO`/`Ztso`/`FEX LDAPR+STLR`/`QEMU TCG`/`Box64 SM=4 RV64`/`FEX Half-Barrier`): `SB=ALLOW`, all other 6 tests `FORBID`.
- `over_strong` (`FEX ARMv8.0 LDAR+STLR`/`Erratum 3877900`/`Box64 SM=4 ARM64`): all 7 tests `FORBID` (`SB` over-constrained).
- `write_seq_only` (`Box64 SM=1..3`/broken FEX backpatch order): `MP=ALLOW`, `WRC=ALLOW`, `IRIW=ALLOW` (3 unsound outcomes).
- `bare_weak` (`Box64 SM=0`): `MP`, `LB`, `2+2W`, `WRC`, `IRIW` all `ALLOW` (5 unsound outcomes).
- Precise `ucontext_t` counterexample: expected `{'fault_rip': '0x401007', 'RAX': 11, 'RBX': 51966, 'RCX': 0, 'ZF': 0}` vs. naive reordered JIT `{'fault_rip': '0x401007', 'RAX': 13, 'RBX': 0, 'RCX': 0, 'ZF': 1}` (corrupts `RAX`, `RBX`, and `ZF`).

## Revalidation

To verify whether these findings still hold on newer upstream revisions or new host silicon:

1. **Memory-ordering lowering diff check** (cheapest, `< 30 s`):
   - **QEMU**: Inspect `target/i386/tcg/tcg-cpu.c` (`guest_default_memory_order`), `tcg/tcg-op-ldst.c` (`tcg_gen_req_mo` call sites), and `tcg/{aarch64,riscv64}/tcg-target.c.inc` (`tcg_out_mb` — check whether AArch64 begins emitting `LDAPR`/`STLR` or `FEAT_LRCPC3` `LDIAPP`/`STILP` directly instead of `DMB`).
   - **FEX-Emu**: Diff `Source/Common/HostFeatures.cpp` (check the `IgnoreLRCPC2` Erratum `3877900` MIDR list and `PR_SET_MEM_MODEL_TSO` hardware-TSO probing), `JIT/MemoryOps.cpp` (`LoadMemTSO`/`StoreMemTSO`), and `Utils/ArchHelpers/Arm64.cpp` (`HandleUnalignedAccess` patch ordering).
   - **Box64**: Diff `src/dynarec/dynarec_helper.h` (`SMREAD`/`SMWRITE`/`WILLWRITE` definitions — check whether `STRONGMEM=1..3` gains reader-side barriers or whether `DMB_TSO()` on ARM64 switches to `LDAPUR`/`STLUR` by default) and `src/dynarec/rv64/rv64_emitter.h` (`DMB_TSO` `Ztso`/`fence.tso` gating).
   - **Apple XNU**: Diff `osfmk/arm64/proc_reg.h` around `ACTLR_EL1_EnTSO`.
2. **Axiomatic regression check**: Save the embedded Python 3 litmus checker from **Evidence** to `/tmp/dbt_tso_check.py`, update `ppo()` to reflect any newly added DBT barrier placement, and run `python3 /tmp/dbt_tso_check.py`; verify that no TSO-forbidden litmus test (`SB+MFENCE`, `MP`, `LB`, `2+2W`, `WRC`, `IRIW`) becomes `ALLOW`.
3. **Hardware silicon erratum check**: On any new ARMv8.4+/v9 host core, run a 2-thread `SB` hardware litmus test (e.g., `litmus7` / `herdtools7`) comparing `STLR; LDAPR` vs. `STLR; LDAPUR`; if `STLR; LDAPUR` exhibits zero `SB (0,0)` outcomes across $10^7$ iterations while `STLR; LDAPR` observes `SB (0,0)`, the core exhibits Erratum `3877900`-class over-serialization and should disable `LDAPUR`.
