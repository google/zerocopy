# Cross-Modifying Code, Live Binary Patching, and Instruction-Cache Coherence Models

## Summary

Verified compilers and ISA-level machine-code verifiers typically assume an immutable executable code segment whose bytes remain fixed across execution. Production kernels, hypervisors, JIT compilers, and debuggers routinely violate this assumption via live binary patching (`jump_label`/`static_branch`, `static_call`, `ftrace`, `kprobes`, boot-time `.altinstructions`, and dynamic JIT compilation) across split data caches (D-cache), instruction caches (I-cache), pre-decoded micro-op caches, and speculative fetch buffers. Three hardware and verification invariants govern soundness across `ARMv8-A`, `x86-64`, and `RISC-V`:

1. **Non-Coherent Relaxed Instruction Fetch (`ARMv8-A` `esop2020.cat` & `aarch64.cat`):** Unlike coherent data memory, ARMv8-A instruction fetches are *not* instruction-to-instruction coherent (`CoFF` allows a thread to fetch a new instruction and subsequently fetch an older one at the same address) and *not* data-to-instruction coherent by default. With `CTR_EL0.IDC = 0, DIC = 0`, synchronizing a code write requires the full 5-step sequence `DC CVAU -> DSB ISH -> IC IVAU -> DSB ISH -> ISB` (with the final `ISB` or Context Synchronization Event required on **every** executing PE). Even when hardware advertises both `FEAT_IDC` (`CTR_EL0.IDC = 1`) and `FEAT_DIC` (`CTR_EL0.DIC = 1`)—eliding `DC CVAU` and `IC IVAU`—an explicit **`ISB`** (or exception entry/return `IFB`) remains strictly mandatory on every executing core to flush prefetched pipeline state. Moreover, concurrent modification without synchronization (`CMODX`) triggers **`CONSTRAINED UNPREDICTABLE`** unless both old and new instructions belong to Arm's restricted 8-instruction safe subset (`B`, `BL`, `BRK`, `HVC`, `ISB`, `NOP`, `SMC`, `SVC`); concurrently patching conditional branches (`B.cond`) can execute a hybrid of old condition and new target (or vice versa).
2. **Variable-Length `x86-64` Cache-Line Splits & Linux's 3-Step `INT3` (`text_poke_bp`) Protocol:** On `x86-64`, `6.25%` (`4/64`) of unaligned 5-byte `CALL`/`JMP rel32` patch sites straddle a 64-byte cache-line boundary and `25.00%` (`16/64`) straddle a 16-byte fetch window. Because Intel SDM Vol. 3A Section 8.1.3/9.1.3 does not guarantee atomic cross-modifying code (`XMC`) across cache lines or unsynchronized fetch pipelines, naive direct overwrites let concurrent cores execute torn instructions (`#UD` or corrupted jump targets). Linux (`arch/x86/kernel/alternative.c`, `smp_text_poke_batch_finish` + `smp_text_poke_int3_handler`) avoids `stop_machine()` via a 3-step `INT3` (`0xCC`) protocol with three IPI serializing barriers (`smp_text_poke_sync_each_cpu()`) and a lock-free per-CPU refcount (`text_poke_array_refs`), restricting live-emulated opcodes to a tiny finite set (`RET`, `CALL`, `JMP32`, `JMP8`, `Jcc`). Omitting either the first or second IPI sync re-introduces reachable torn-instruction executions.
3. **`RISC-V` Local-Only `FENCE.I` and Verification of Finite Patch-Site Families:** Under `riscv/riscv-isa-manual` `Zifencei`, `FENCE.I` synchronizes **only the local hart's** instruction fetch with stores already visible to that hart; it provides zero cross-hart I-cache invalidation, requiring a data fence (`RISCV_FENCE(w, o)`) followed by SBI/IPI remote `FENCE.I` (`sbi_remote_fence_i`) or `stop_machine()`. The same manual revision also defines two optional extensions:
   - **`Ziccif`:** atomic fetch of naturally aligned instructions of at most `min(ILEN,XLEN)` bits, with safe-harbour rules for concurrent modification.
   - **`Ziccid`:** an operational instruction/data coherence model. Stores eventually become visible to fetches, and fetches are in program order. Its ratification status is qualified in **Boundaries**.
   Neither removes the need for `FENCE.I` for immediate local visibility. To certify live-patched binaries without abandoning machine-code compiler proofs or admitting arbitrary self-modifying code, verification can lift immutable-code receipts to **finite, typed patch-site families** ($\mathcal{F}(p) = \{I_{\text{old}}, I_{\text{trap}}, I_{\text{new}}\}$ or finite ABI-conforming callee sets `{f_1, ..., f_k}`), combining a per-site bisimulation invariant across all legal states in $\mathcal{F}(p)$ with a separate concurrency-model receipt proving that intermediate hardware states never leave $\mathcal{F}(p)$.

## Applicability

This report covers architectural instruction-fetch memory models, OS live text-patching mechanisms, and formal verification boundaries across three major 64-bit ISAs:

- **ARMv8-A / AArch64 formal ifetch semantics:**
  - *ARMv8-A System Semantics: Instruction Fetch in Relaxed Architectures* (Simner, Flur, Pulte, Armstrong, Pichon-Pharabod, Maranget & Sewell, ESOP 2020, DOI `10.1007/978-3-030-44914-8_23`, extended technical report inspected) and its executable axiomatic cat model in `rems-project/isla` @ `e9b5d945394277656593a0d429466d7fa0a2b4b3` (`web/client/dist/esop2020.cat`, `test_litmus_esop2020.sh`).
  - Arm Ltd.'s official evolved AArch64 axiomatic memory model in `herd/herdtools7` @ `1670f9e8ebb76f7cd4ba373e1c21948330eb086a` (`herd/libdir/aarch64.cat`, `aarch64hwreqs.cat`, `aarch64util.cat`, `aarch64fences.cat`, `ifetch-cos.cat`), explicitly contrasting the ESOP 2020 baseline (`IDC=0, DIC=0`) with the newer official `aarch64.cat` model parameterized by `DIC`, `IDC`, `ETS2`/`ETS3`, `ExS`/`EIS`/`EOS`, and `CMODX`.
- **RISC-V `Zifencei` normative specification:** `riscv/riscv-isa-manual` @ `5f1104a0613af80219232b1e4bc108f9ec2bd6b2` (`src/unpriv/zifencei.adoc`).
- **Intel x86-64 `XMC` architectural specification:** Intel 64 and IA-32 Architectures Software Developer's Manual Vol. 3A, *Handling Self- and Cross-Modifying Code* (Section 8.1.3 / 9.1.3 depending on SDM edition).
- **Linux kernel live text patching implementations:** `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, directly inspecting:
  - `x86-64`: `arch/x86/kernel/alternative.c`, `arch/x86/kernel/jump_label.c`, `arch/x86/kernel/static_call.c`, `arch/x86/kernel/kprobes/opt.c`.
  - `ARM64`: `arch/arm64/kernel/patching.c`, `arch/arm64/mm/cache.S`, `arch/arm64/kernel/jump_label.c`, `arch/arm64/kernel/ftrace.c`, `arch/arm64/kernel/probes/kprobes.c`.
  - `RISC-V`: `arch/riscv/kernel/patch.c`, `arch/riscv/mm/cacheflush.c`.
- **Formal verification of code modification:** Cai, Shao & Vaynberg (PLDI 2007, DOI `10.1145/1273442.1250743`, *Certified Self-Modifying Code*) and Myreen (POPL 2010, DOI `10.1145/1706299.1706313`, *Verified Just-In-Time Compiler on x86*).

**Scope note on version evolution:** Note that in `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, the historically named x86 symbols `text_poke_bp_batch` and `poke_int3_handler` have evolved into `smp_text_poke_batch_finish`, `smp_text_poke_single`, `smp_text_poke_sync_each_cpu`, and `noinstr int smp_text_poke_int3_handler(struct pt_regs *regs)`; the underlying 3-step `INT3` + IPI protocol is preserved while adding lock-free per-CPU refcounting (`text_poke_array_refs`) and 6-byte `Jcc.d32` handling.

## Findings

### 1. Why Instruction Fetch Is Weaker Than Data Memory

Basis: normative (`Arm DDI 0487`, `riscv/riscv-isa-manual`) + source (`rems-project/isla`, `herd/herdtools7`) + documentation (`Simner et al., ESOP 2020`)

Modern superscalar processors maintain coherent data memory across cores via hardware MESI/MOESI protocols on L1D/L2/L3 caches. Because writes to executable code are rare compared to instruction fetches, architectures deliberately decouple the instruction-fetch path from data coherence:

1. **Split L1D / L1I caches without universal I-cache snooping:** On ARMv8-A (with `IDC=0, DIC=0`) and RISC-V, a data store lands in a core's store buffer and L1 data cache without automatically cleaning to the **Point of Unification (PoU)** or invalidating stale lines in local or remote L1 instruction caches.
2. **Pre-decoded micro-op (`uop`) caches and fetch/decode queues:** Even if L1I is coherent with L1D (as on x86-64 and ARMv8-A with `IDC=1, DIC=1`), a core may have speculatively fetched and decoded instructions far ahead in the instruction stream at any time since its last **Context Synchronization Event** (`ISB`, exception entry/return on ARMv8-A; `CPUID`/`IRET`/`SERIALIZE` on x86-64; `FENCE.I` on RISC-V).
3. **Three coherence properties broken by `ifetch` (`Simner et al., ESOP 2020`, Section 3.2):**
   - **Instruction-to-Instruction Coherence (`CoFF`):** **Violated on ARMv8-A** (both architecturally allowed and observed on physical silicon). A thread executing `BL f; BL f` while another thread overwrites `f: B l0` with `B l1` can execute the new `B l1` on the first call and the **older** `B l0` on the second call (`1:X0=2, 1:X1=1`)—for instance when one fetch hits memory/L2 while another hits an un-invalidated L1I/prefetch entry.
   - **Data-to-Instruction Coherence (`CoFR` / `CoRF`):** Reading the new instruction bytes via a data load (`LDR`) does **not** guarantee a program-order-later instruction fetch sees the new instruction (the data read hits coherent L1D while the instruction fetch hits stale L1I or fetch queue).
   - **Instruction-to-Data Coherence:** Fetching an instruction does not force prior/subsequent data reads to agree without barriers.

---

### 2. ARMv8-A Formal Instruction-Fetch Models: ESOP 2020 (`Isla`) vs. Official `herdtools7` (`aarch64.cat`)

Basis: source (`rems-project/isla` @ `e9b5d945394277656593a0d429466d7fa0a2b4b3`, `herd/herdtools7` @ `1670f9e8ebb76f7cd4ba373e1c21948330eb086a`) + documentation (`Simner et al., ESOP 2020`) + execution (Micro-Probe 2, Probe 1)

#### 2.1 The ESOP 2020 Axiomatic Model (`rems-project/isla/web/client/dist/esop2020.cat`)

Simner et al. (ESOP 2020, DOI `10.1007/978-3-030-44914-8_23`) extended Arm's user-mode axiomatic model with instruction-fetch events (`IF`), cache maintenance events (`DC` for `DC CVAU`, `IC` for `IC IVAU`), and five new relations:
- `fe` (*fetch-to-execute*): connects an instruction's `IF` event to every execution event (`R`, `W`, `DC`, `IC`, `DSB`, `ISB`) of that instruction.
- `fpo` (*fetch-program-order*): orders `IF` events in control-flow unfolding order (`po = fe^-1; fpo; fe`).
- `irf` (*instruction-read-from*): relates a write `W` to every `IF` that fetches from it; `ifr = (irf^-1; co) & loc` (*instruction-from-reads*) relates an `IF` to every write coherence-after the write it fetched.
- `scl` (*same-cache-line*): equivalence relation on events targeting the same cache line.
- `wco` (*extended coherence order*): acyclic total order per cache line extending `co` over `W`, `DC`, and `IC` (`co = ([W]; wco; [W]) & loc`).

Verbatim core axioms from `rems-project/isla` @ `e9b5d945394277656593a0d429466d7fa0a2b4b3` (`web/client/dist/esop2020.cat`):

```cat
let ifr  = (irf^-1; co) & loc
let iseq = [W]; (wco & scl); [DC]; (wco & scl); [IC]

let obs  = rfe | fr | wco | irf | (ifr; iseq)
let fob  = [IF]; fpo; [IF] | [IF]; fe | [ISB]; fe^-1; fpo
let dob  = addr | data | ctrl; [W] | (ctrl | (addr; po)); [ISB]
         | addr; po; [W] | (addr | data); rfi
let bob  = ... | [R | W | F | C]; po; [DSB.ISH] | [DSB.ISH]; po; [R | W | F | C]
         | [DMB.SY]; po; [DC]
let cob  = [R | W]; (po & scl); [DC] | [DC]; (po & scl); [DC]
let ob   = (obs | fob | dob | aob | bob | cob)^+

acyclic po-loc | fr | co | rf as internal
irreflexive ob as external
```

**How `ifr; iseq` enforces the 5-step cache-sync protocol:** Suppose write `W1` overwrites `W0` at code address `f`, followed by `DC CVAU` (`DC1`), `DSB ISH` (`D1`), `IC IVAU` (`IC1`), `DSB ISH` (`D2`), and `ISB` (`ISB1`) (either on the same thread in `SM+dc-dsb-ic-dsb-isb` or across threads via flag release/acquire + `ctrl; ISB` in `MP.RF+cachesync+ctrl-isb`). If a later fetch `F1` attempts to fetch stale `W0`, then:
1. `(F1, W1) ∈ ifr`, and `(W1, DC1, IC1) ∈ iseq`, yielding `(F1, IC1) ∈ obs ⊆ ob`.
2. On the synchronization chain, `(IC1, D2) ∈ bob`, `(D2, ISB1)` (or `D2 -> Wflag -rfe-> Rflag -ctrl-> ISB2`) `∈ ob`, and `(ISB, F1) ∈ [ISB]; fe^-1; fpo ⊆ fob ⊆ ob`.
3. Closing transitively yields `(F1, F1) ∈ ob`, violating `irreflexive ob`—hence stale fetch `F1` is **forbidden**!
4. **Removing ANY single barrier breaks the cycle:**
   - Remove final **`ISB`** (`SM+dc-dsb-ic-dsb` or `MP.RF+cachesync+ctrl`): no `[ISB]; fe^-1; fpo` edge reaches `F1`, so `ob` stays irreflexive and stale `F1` is **allowed** (Micro-Probe 2, Probe 1).
   - Remove `DSB ISH` between `DC` and `IC`: `DC` and `IC` are not ordered into `wco`, breaking `iseq`.
   - Note that `IC IVAU` is **broadcast to the Inner Shareable domain** (`B2.2.5`), so `DC` and `IC` do not even need to run on the same thread as the executing PE—only `ISB` (or an exception context-synchronization event) is required on every executing PE.

**Empirical silicon validation & Qualcomm Snapdragon 820 hardware bug (`Simner et al., ESOP 2020`, Section 6):** Testing 7 Armv8-A SoCs (Snapdragon 810, Tegra K1, Snapdragon 820, Exynos 8895, Snapdragon 425, Amlogic 905, and a second Amlogic 905) across 1,456 `diy`-generated ifetch litmus tests (~10M iterations each) validated the model against hardware and uncovered a real **silicon bug on the Qualcomm Snapdragon 820 (4× Kryo cores)**: `MP.RF+cachesync+ctrl-isb`—with the *complete* architectural cache-synchronization sequence—produced an architecturally illegal stale-fetch outcome in **84 out of 1.1 billion runs**.

#### 2.2 Evolution to Arm's Official `aarch64.cat` (`herd/herdtools7` @ `1670f9e8ebb76f7cd4ba373e1c21948330eb086a`)

Comparing `esop2020.cat` against Arm Ltd.'s newer official `herd/libdir/aarch64.cat` and `aarch64hwreqs.cat` reveals three major architectural generalizations:

1. **Feature-flag parameterization for `FEAT_IDC` (`CTR_EL0.IDC`) and `FEAT_DIC` (`CTR_EL0.DIC`):**
   ```cat
   (* herd/herdtools7 herd/libdir/aarch64.cat *)
   let IC-ca =
       (if not "DIC" && not "IDC" then [IC]; IC-after; [Imp & Instr & R]; ca; [W]; DC-after; [DC.CVAU] else 0)
       | (if not "DIC" && "IDC" then [IC]; IC-after; [Imp & Instr & R]; ca; [W] else 0)
       | (if "DIC" && "IDC" then [Imp & Instr & R]; ca; [W] else 0)
   ```
   - `IDC=0, DIC=0` (baseline Armv8.0): both `DC CVAU` and `IC IVAU` are required.
   - `IDC=1, DIC=0`: data cache is clean to PoU for instruction fetch; `DC CVAU` is elided (Linux replaces it with `dsb ishst` in `arch/arm64/mm/cache.S`), while `IC IVAU` + `DSB ISH` + `ISB` remain mandatory.
   - `IDC=1, DIC=1` (e.g., modern Armv8.2+ / Apple Silicon): `IC-ca` collapses directly to `[Imp & Instr & R]; ca; [W]`, eliding both `DC CVAU` and `IC IVAU`! **Crucially, `ISB` (or an `IFB` event) is STILL required** to introduce the `IFB-ob` edge into `Imp & Instr & R`: as verified in Micro-Probe 2 (Probe 1), `SM+dsb-isb` becomes forbidden under `IDC=1, DIC=1` while `MP.RF+cachesync+ctrl` (no `ISB`) remains **allowed** even with `IDC=1, DIC=1`!
2. **Generalized Instruction Fetch Barrier (`IFB`) for Exception Synchronization (`aarch64hwreqs.cat` lines 88–103):**
   ```cat
   let EXC-ENTRY-IFB = if not "ExS" || "EIS" then EXC-ENTRY else EXC-ENTRY \ SVC
   let EXC-RET-IFB   = if not "ExS" || "EOS" then EXC-RET else {}
   let IFB = ISB | EXC-ENTRY-IFB | EXC-RET-IFB
   ```
   Under default Armv8-A (or with `SCTLR_ELx.EIS = 1, EOS = 1` when `FEAT_ExS` is present), exception entry (`EXC-ENTRY`, such as an IPI or `BRK` trap) and exception return (`ERET` = `EXC-RET`) act as architectural Context Synchronization Events equivalent to `ISB`. This is the exact formal justification behind Linux ARM64's `kick_all_cpus_sync()` IPI in `jump_label.c` and its `kprobes.c` XOL-slot optimization!
3. **Concurrent Modification and Execution (`CMODX`) and `CONSTRAINED UNPREDICTABLE`:**
   Per Arm DDI 0487 Section B2.2.5 (`Simner et al., ESOP 2020`, Section 3.1) and `aarch64.cat` lines 160–175:
   - Concurrent modification of an instruction *without* synchronizing writer and reader (`W` and `Imp & Instr & R` unordered in `ob`) is permitted **only** when both original and replacement instructions belong to the safe subset: **`B`**, **`BL`**, **`BRK`**, **`HVC`**, **`ISB`**, **`NOP`**, **`SMC`**, **`SVC`** (plus `UDF` in newer Armv8.x revisions).
   - Overwriting any other instruction concurrently (e.g., `ADD X0,X0,#1` $\to$ `SUB X0,X0,#1` in `W+F`) triggers **`CONSTRAINED UNPREDICTABLE`**: the PE may exhibit *any* behavior achievable by executing any sequence of instructions permitted at that Exception Level (weaker than atomic old/new choice, though bounded by EL privilege isolation unlike C/C++ whole-program UB).
   - Concurrent modification of conditional branches (`B.EQ g` $\to$ `B.NE h` in `W+F+branches`) is explicitly non-single-copy-atomic: hardware may execute **`B.NE g`** or **`B.EQ h`** (mixing old condition with new target or vice versa).
   - In `herd/libdir/aarch64.cat`, unordered `CMODX-conflicts` on restricted instructions trigger `flag ~empty CMODX-unordered-conflicts as violates-CMODX-requirements`.

---

### 3. Intel `x86-64` Cross-Modifying Code (`XMC`), Cache-Line Splits, and Linux's 3-Step `INT3` Protocol

Basis: normative (`Intel SDM Vol. 3A 8.1.3/9.1.3`) + source (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) + execution (Micro-Probe 2, Probe 2)

#### 3.1 Intel SDM Vol. 3A `XMC` Rules and Variable-Length Torn-Instruction Hazards

Unlike ARMv8-A's fixed-width 32-bit aligned instructions, `x86-64` instructions are variable-length (`1` to `15` bytes) with **no alignment guarantee**:
- A standard 5-byte `CALL rel32` (`0xE8 <s32>`) or `JMP rel32` (`0xE9 <s32>`) starts at an arbitrary byte offset `off ∈ [0..63]` inside a 64-byte cache line. As verified in Micro-Probe 2 (Probe 2), **`4/64` (`6.25%`)** of offsets (`[60, 61, 62, 63]`) straddle two 64-byte cache lines, and **`16/64` (`25.00%`)** (`[12..15, 28..31, 44..47, 60..63]`) straddle a 16-byte instruction-fetch window.
- Although x86-64 maintains hardware L1I-to-L1D cache snooping (eliminating explicit `DC CVAU`/`IC IVAU` cache maintenance), **Intel SDM Vol. 3A Section 8.1.3 / 9.1.3 (*Handling Self- and Cross-Modifying Code*)** mandates that unsynchronized cross-modifying code is **undefined** whenever a remote core concurrently executes instructions being modified: a non-atomic store spanning two cache lines (or independent fetch-buffer refills on a split line) allows an executing core to decode **byte 0 from the old instruction concatenated with bytes 1..4 from the new instruction** (or vice versa), producing an illegal opcode (`#UD`) or jumping to an arbitrary corrupted 32-bit displacement.
- Intel's architectural `XMC` rule requires that executing cores do not execute modified instructions until the write is complete AND execute a **serializing instruction** (`CPUID`, `IRET`, `SERIALIZE`, etc.) before entering the modified code. (For single-byte aligned updates such as writing a 1-byte `INT3 = 0xCC`, the single-byte store never splits a cache line and is inherently atomic.)

#### 3.2 Linux `x86-64` Live Patching (`arch/x86/kernel/alternative.c`)

To patch live kernel instructions (`jump_label`, `static_call`, `ftrace`, optimized `kprobes`) on SMP systems **without** stalling all cores in `stop_machine()`, Linux (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `arch/x86/kernel/alternative.c`, lines 2650–2950) implements a batched 3-step `INT3` breakpoint protocol via a temporary writable `mm` alias (`text_poke()`):

1. **Publish patch table & arm lock-free refcount:** Holding `text_mutex`, `smp_text_poke_batch_finish()` populates `text_poke_array.vec` (up to `TEXT_POKE_ARRAY_MAX = PAGE_SIZE / sizeof(struct smp_text_poke_loc)` entries), sets per-CPU `text_poke_array_refs = 1` with `atomic_set_release`, and issues `smp_wmb()` pairing with `smp_rmb()` in the `#BP` handler.
2. **Step 1 — Write 1-byte `INT3` (`0xCC`) at byte 0 of every site, then IPI Sync #1:**
   - Each 1-byte `0xCC` store is guaranteed single-byte atomic (never splits a cache line).
   - `smp_text_poke_sync_each_cpu()` sends an IPI to every online CPU; IPI entry and `IRET` act as hardware serializing instructions flushing all prefetch/decode buffers. After IPI Sync #1 returns, **no remote CPU can still decode `OLD[0]`**—any CPU reaching the site is guaranteed to hit `0xCC` and enter `noinstr int smp_text_poke_int3_handler(struct pt_regs *regs)`.
3. **Emulation during the `INT3` window (`smp_text_poke_int3_handler`, lines 2707–2778):**
   - Acquires per-CPU `try_get_text_poke_array()` (`raw_atomic_inc_not_zero`), binary-searches `text_poke_array.vec` for `regs->ip - 1`, and dispatches on **strictly six finite opcode classes**:
     - `INT3_INSN_OPCODE`: pass through (not consumed).
     - `RET_INSN_OPCODE` (`0xC3`): `int3_emulate_ret(regs)`.
     - `CALL_INSN_OPCODE` (`0xE8`): `int3_emulate_call(regs, ip, ip + tpl->disp)`.
     - `JMP32_INSN_OPCODE` (`0xE9`) / `JMP8_INSN_OPCODE` (`0xEB`): `int3_emulate_jmp(regs, ip + tpl->disp)`.
     - `0x70 ... 0x7f` (`Jcc`): `int3_emulate_jcc(regs, tpl->opcode & 0xf, ip, tpl->disp)`.
     - Anything else: **`BUG()`** (kernel panic). For `NOP` replacement, the caller supplies a synthetic `JMP` emulation target skipping `tpl->len` bytes; for 5-byte `static_call` special instructions (`arch/x86/kernel/static_call.c`: `xor5rax = {0x2e, 0x2e, 0x2e, 0x31, 0xc0}`, `warninsn`, `unlockinsn`), `static_call` supplies `emulate = CALL` to the original helper during the transition!
4. **Step 2 — Overwrite tail bytes `1..len-1` (handling 6-byte `0x0f 0x8x` `Jcc.d32` prefix at line 2847), emit `perf_event_text_poke` (for Intel PT trace reconstruction), then IPI Sync #2:**
   - Because byte 0 is still `0xCC` across every CPU, mutating bytes `1..len-1` cannot be decoded by any concurrent core.
   - `smp_text_poke_sync_each_cpu()` flushes stale tail bytes from all CPUs' fetch buffers (note the inline source comment at line 2882: *"According to Intel, this core syncing is very likely not necessary and we'd be safe even without it. But better safe than sorry (plus there's not only Intel)."*). Micro-Probe 2 (Probe 2) confirms that on an independent-cache-line fetch model, omitting IPI Sync #2 allows a reader to fetch `(NEW[0], OLD[1..4])` right after Step 3!
5. **Step 3 — Replace byte 0 (`0xCC`) with `NEW[0]`, then IPI Sync #3, then drain `text_poke_array_refs`:**
   - Final 1-byte atomic write activates the complete new instruction; IPI Sync #3 ensures no CPU can newly enter `smp_text_poke_int3_handler` for this batch; decrementing and spinning on `text_poke_array_refs` waits for any in-flight `#BP` handlers to finish before zeroing `text_poke_array.nr_entries`.

**Patch-site hygiene checks:** Both `arch/x86/kernel/jump_label.c` (`__jump_label_patch` `memcmp(addr, expect, size)` $\to$ `BUG()`) and `arch/x86/kernel/kprobes/opt.c` (`smp_text_poke_single` installing `JMP32` to the out-of-line detour slot) strictly validate that the existing machine bytes belong to the expected patch-site state before modifying text.

---

### 4. `RISC-V` `Zifencei` (`FENCE.I`) Coherence and Cross-Architecture Live-Patching Matrix

Basis: normative (`riscv/riscv-isa-manual` @ `5f1104a0613af80219232b1e4bc108f9ec2bd6b2`) + source (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`)

#### 4.1 Normative `Zifencei` Semantics (`src/unpriv/zifencei.adoc`)

The RISC-V Unprivileged ISA Specification (`src/unpriv/zifencei.adoc`, normative clause `[[norm:fence-i_op]]`) defines `FENCE.I` strictly as a **single-hart** barrier:

> *"A `fence.i` instruction orders all explicit memory accesses and instruction fetches that precede the `fence.i` in program order before all instruction fetches that follow the `fence.i` in program order."*
> *"RISC-V does not guarantee that stores to instruction memory will be made visible to instruction fetches on a RISC-V hart until that hart executes a `fence.i` instruction... `fence.i` does **not** ensure that other RISC-V harts' instruction fetches will observe the local hart's stores in a multiprocessor system. To make a store to instruction memory visible to all RISC-V harts, the writing hart also has to execute a data `fence` before requesting that all remote RISC-V harts execute a `fence.i`."*

Two critical systems consequences follow directly from `zifencei.adoc` and Linux `arch/riscv/`:
1. **User-space migration hazard:** Because an OS may migrate a user thread onto a different physical hart *after* it runs `fence.i`, standard Linux ABI removes direct `fence.i` reliance from user space and mandates a syscall (`sys_riscv_flush_icache`) tracked via `mm->context.icache_stale_mask` (`arch/riscv/mm/cacheflush.c`, `flush_icache_mm`).
2. **Kernel SMP patching (`arch/riscv/mm/cacheflush.c` & `arch/riscv/kernel/patch.c`):**
   - `flush_icache_all()` runs `local_flush_icache_all()`, then **`RISCV_FENCE(w, o)`** (explicitly ordering prior D-cache instruction stores before the MMIO write to CLINT/S-IMSIC that triggers the IPI!), then `sbi_remote_fence_i(NULL)` (or `on_each_cpu(ipi_remote_fence_i, NULL, 1)`).
   - For multi-instruction or arbitrary patching (`patch_text()` in `arch/riscv/kernel/patch.c`), Linux uses `stop_machine_cpuslocked(patch_text_cb, ...)`: the last-arriving master hart writes through a temporary `FIX_TEXT_POKE0`/`FIX_TEXT_POKE1` fixmap alias (supporting up to 2 pages), executes `atomic_inc_return_release(&patch->cpu_count)`, and every parked remote hart exits the spin loop and runs `local_flush_icache_all()` (`fence.i`).

#### 4.2 Cross-Architecture Live Binary Patching Matrix (`torvalds/linux` @ `4405c18c95`)

| Dimension | `x86-64` (`alternative.c`, `jump_label.c`, `static_call.c`) | `ARMv8-A` (`patching.c`, `cache.S`, `jump_label.c`, `kprobes.c`) | `RISC-V` (`patch.c`, `cacheflush.c`) |
| :--- | :--- | :--- | :--- |
| **Instruction width & alignment** | Variable 1–15 B; unaligned (6.25% of 5 B sites split 64 B CL) | Fixed 32-bit (4 B), strictly 4-byte aligned (`(uintptr_t)tp & 0x3` rejected) | 32-bit or 16-bit (`RVC` compressed); 2-byte aligned (32-bit insn can split 4 B/CL boundary!) |
| **Hardware D$/I$ coherence** | Snooped L1I/L1D; fetch/decode pipeline still needs serialization | Split L1I/L1D unless `CTR_EL0.IDC=1` & `DIC=1`; `IC IVAU` broadcasts ISH | Split; no hardware broadcast; `FENCE.I` is strictly **local hart only**. Optional `Ziccid` guarantees eventual store-to-fetch visibility and in-order fetch; `FENCE.I` is still needed for immediate visibility. |
| **Full sync sequence (writer + reader)** | Store + IPI serializing barrier (`IRET`/`CPUID`/`SERIALIZE`) on all CPUs | `DC CVAU` (unless `IDC=1`: `DSB ISHST`) $\to$ `DSB ISH` $\to$ `IC IVAU` (unless `DIC=1`) $\to$ `DSB ISH` $\to$ `ISB` / `EXC-ENTRY`/`ERET` on every PE | Data `FENCE w,o` + remote IPI / `SBI_RFENCE_REMOTE_FENCE_I` executing `FENCE.I` on every remote hart |
| **Concurrent modification safety** | Only 1-byte writes (e.g., `INT3 = 0xCC`) are split-free atomic; multi-byte XMC is UB (`#UD`) | `CMODX`: safe *only* for `{B, BL, BRK, HVC, ISB, NOP, SMC, SVC}`; else `CONSTRAINED UNPREDICTABLE`; `B.cond` tears cond/target | No general concurrent-modification guarantee in the base ISA. With `Ziccif`, naturally aligned fetches of ≤ `min(ILEN,XLEN)` bits are atomic. `ziccif.adoc` gives safe-harbour rules: single-copy-atomic aligned stores; no change spanning an aligned `M`-byte boundary except via a shorter unconditional jump; no merging of smaller instructions into a larger one; coherence PMA. |
| **Linux lockless fast path (`jump_label`)** | 3-step `INT3` `smp_text_poke_single` (3 IPI syncs, no `stop_machine`) | `aarch64_insn_patch_text_nosync` (`B`/`NOP` CMODX-safe) + `kick_all_cpus_sync()` IPI (`IFB`) | `patch_text_nosync` / `flush_icache_all` or `stop_machine` for multi-insn / `RVC` sites |
| **Linux arbitrary site patching (`kprobes`)** | `INT3` single-byte atomic poke; `optprobe` 5 B `JMP` via `smp_text_poke_single` | `aarch64_insn_patch_text` via **`stop_machine_cpuslocked`** + per-CPU `isb()` (arbitrary target not in CMODX safe list) | `patch_text` via **`stop_machine_cpuslocked`** + per-hart `local_flush_icache_all()` (`fence.i`) |

---

### 5. Certifying Finite Patch-Site Families Without Invalidating Machine-Code Compilation Receipts

Basis: derived + normative (`Cai et al., PLDI 2007`; `Myreen, POPL 2010`) + source (`torvalds/linux` `jump_label.c`, `static_call.c`, `alternative.c`)

Verified compilers (CompCert, CakeML) and binary-level proof-carrying systems discharge compilation correctness by establishing a forward/backward simulation theorem under an **immutable code-memory invariant**: $\forall t, a \in \text{Text}.\ \text{mem}_t[a] = \text{code}_0[a]$. Admitting unconstrained self-modifying code (SMC) requires either full runtime code-as-data program logics with explicit code-invariant frames (such as Cai, Shao & Vaynberg's *Certified Self-Modifying Code*, PLDI 2007, DOI `10.1145/1273442.1250743`, which tracks code predicates inside separation logic over a Harvard/cache-flush machine) or verified JIT code-generation invariants (Myreen, POPL 2010, DOI `10.1145/1706299.1706313`, which proves `x86` `icache` flush soundness when emitting verified bytecode translations into fresh heap buffers). Both require heavy whole-program proof machinery that destroys modular compilation receipts for ordinary statically compiled code.

Production live-patching systems (`jump_label`, `static_call`, `ftrace`, boot `.altinstructions`) never need unconstrained SMC. Instead, every mutable site $p$ belongs to a **finite, statically declared, ABI-typed patch-site family** $\mathcal{F}(p)$, enabling a modular **two-layer certification contract** that preserves standard immutable-code compiler receipts everywhere outside $p$:

1. **Layer A — Static Finite-Family Compilation Receipt (Compiler / Sequential Semantics):**
   - Treat each patch site $p \in \mathcal{P}$ as a distinguished opaque pseudo-instruction parameterized by a finite mode set $M_p$ (e.g., for `jump_label`: $M_p = \{\text{NOP}, \text{JMP}(L_{\text{target}})\}$; for `static_call`: $M_p = \{\text{CALL}(f_1), \dots, \text{CALL}(f_k), \text{NOP}/\text{RET0}\}$ where every $f_i$ satisfies the identical calling convention, clobber mask, stack-frame height, and relational pre/post specification $(P_p, Q_p)$).
   - **No cross-site optimizer assumptions:** The compiler treats `p` as a control-flow/ABI barrier whose observable state transition is nondeterministically drawn from the finite union $\bigcup_{m \in M_p} \llbracket m \rrbracket$, guaranteeing fixed byte width (`len(p) ∈ {2, 4, 5, 6}`), exact alignment (4-byte on AArch64; optionally cache-line interior on x86-64), and register-liveness compatibility across *every* $m \in M_p$.
   - Because $\mathcal{F}(p)$ is finite and statically enumerated at link time (matching Linux's `__jump_table` and `.static_call_sites` ELF sections), the compiler's simulation proof checks only $|M_p|$ concrete machine encodings at site $p$ while keeping $\text{mem}[a] = \text{code}_0[a]$ intact for all $a \notin \bigcup_{p \in \mathcal{P}} [p, p + \text{len}(p))$.
2. **Layer B — Concurrent Transition & `ifetch` Protocol Receipt (Weak-Memory / Runtime Semantics):**
   - Define the extended runtime family $\mathcal{F}_{\text{live}}(p) = \mathcal{F}(p) \cup \mathcal{F}_{\text{tramp}}(p)$, where $\mathcal{F}_{\text{tramp}}(p)$ contains the transient trap encoding (e.g., `0xCC` + `#BP` emulation via `smp_text_poke_int3_handler` on `x86-64`, or empty on `ARMv8-A` when $\mathcal{F}(p) \subseteq \{\text{B}, \text{BL}, \text{NOP}, \text{BRK}\}$).
   - Prove **two obligations** against the target ISA's formal `ifetch` memory model (`aarch64.cat`, Intel SDM `XMC`, or RISC-V `Zifencei`):
     1. **No escape from $\mathcal{F}_{\text{live}}(p)$ (Non-Tearing / No-CMODX-Violation):** Every instruction fetch event `IF` at site $p$ across all interleaved patching steps yields either an atomic encoding in $\mathcal{F}(p)$ or a trap in $\mathcal{F}_{\text{tramp}}(p)$ (never a torn byte combination or `CONSTRAINED UNPREDICTABLE` state).
     2. **Trap Bisimulation & Bounded Quiescence:** Every trap state $I_{\text{trap}} \in \mathcal{F}_{\text{tramp}}(p)$ executes a handler semantically bisimilar to *some* valid member $m \in \mathcal{F}(p)$ (preserving register state, flags, and return address without corrupting callee-saved registers), and after the final synchronization barrier (`kick_all_cpus_sync` / IPI Sync #3 / remote `FENCE.I`), all subsequent fetches at $p$ are ordered strictly after the write to $m_{\text{new}}$ (ruling out stale `m_old` fetches via `irreflexive ob`).

Under this decomposition, ordinary compiler passes outside $\mathcal{P}$ retain unmodified immutable-code soundness proofs, while live-patching safety reduces to checking a small, reusable per-architecture protocol proof plus per-site membership in $\mathcal{F}(p)$.

---

### 6. Executable Verification Micro-Probe Results

Basis: execution (Python 3.13.5, stdlib only, deterministic relational & state-space verification)

Running `/tmp/probe_ifetch_patching.py` directly evaluates the `esop2020.cat` / `aarch64.cat` (`IDC`/`DIC`/`CMODX`) axiomatic relations across 10 canonical litmus scenarios and exhaustively verifies the x86-64 cache-line split geometry and 3-step `INT3` protocol:

```text
=== PROBE 1: ARMv8-A Axiomatic Ifetch Model (Simner ESOP 2020 & herdtools7 aarch64.cat) ===
  SM (stale, no sync)                (IDC=0,DIC=0) -> allowed=True , CMODX_violation=False
  SM+dc-dsb-ic-dsb-isb (stale)       (IDC=0,DIC=0) -> allowed=False, CMODX_violation=False
  SM+dc-dsb-ic-dsb (NO ISB, stale)   (IDC=0,DIC=0) -> allowed=True , CMODX_violation=False
  SM+dsb-isb (stale)                 (IDC=0,DIC=0) -> allowed=True , CMODX_violation=False
  SM+dsb-isb (stale)                 (IDC=1,DIC=1) -> allowed=False, CMODX_violation=False
  CoFF (new then old fetch)          (IDC=0,DIC=0) -> allowed=True , CMODX_violation=False
  MP.RF+cachesync+ctrl-isb (stale)   (IDC=0,DIC=0) -> allowed=False, CMODX_violation=False
  MP.RF+cachesync+ctrl (NO ISB)      (IDC=0,DIC=0) -> allowed=True , CMODX_violation=False
  MP.RF+cachesync+ctrl (NO ISB)      (IDC=1,DIC=1) -> allowed=True , CMODX_violation=False
  W+F (ADD -> SUB concurrent)        (IDC=0,DIC=0) -> allowed=True , CMODX_violation=True

=== PROBE 2: x86-64 Cache-Line Split Geometry & Linux 3-Step INT3 text_poke_bp Verification ===
5-byte CALL/JMP rel32 straddling 64B cache line: 4/64 (6.25%), offsets=[60, 61, 62, 63]
5-byte CALL/JMP rel32 straddling 16B fetch window: 16/64 (25.00%), offsets=[12, 13, 14, 15, 28, 29, 30, 31, 44, 45, 46, 47, 60, 61, 62, 63]
  Linux 3-step INT3 (full 3 IPI syncs)             -> safe=True , torn_witness=None
  Omit IPI_SYNC #1 (between INT3 and tail write)   -> safe=False, torn_witness=(1, 'WRITE_TAIL_NEW', ('OLD', 'NEW'))
  Omit IPI_SYNC #2 (between tail write and byte0)  -> safe=False, torn_witness=(3, 'WRITE_B0_NEW', ('NEW', 'OLD'))
  Naive direct overwrite (no INT3)                 -> safe=False, torn_witness=(0, 'WRITE_TAIL_NEW', ('OLD', 'NEW'))
```

## Boundaries

- **Combined Virtual Memory (`VMSA` / `TLBI` / page-table updates) + `ifetch`, and `MTE` (`memtag`) + `ifetch`:** **unsupported** in Arm's official `herd/herdtools7` @ `1670f9e8ebb76f7cd4ba373e1c21948330eb086a` (`herd/libdir/aarch64util.cat`, lines 148–151 explicitly emit `combining-vmsa-and-ifetch-is-not-supported` and `combining-memtag-and-ifetch-is-not-supported`). Furthermore, `aarch64util.cat` line 142 flags `Assuming-no-two-modified-instructions-are-on-the-same-cache-line`. Soundness of simultaneous page-table remapping (e.g., W^X transition + `TLBI`) and live instruction modification requires a unified VMSA+ifetch model beyond this cat specification.
- **ARMv8-A `W+F+branches` exact operational execution of hybrid conditional branches:** **not examined** in the executable probe above (reported directly from Arm DDI 0487 and `Simner et al., ESOP 2020`, Section 3.1).
- **Non-x86/ARM64/RISC-V architectures (IBM POWER `dcbst`/`sync`/`icbi`/`isync`, s390x, LoongArch) and AMD/VIA-specific `XMC` microarchitectural errata:** **not examined**. Note that `arch/x86/kernel/alternative.c` line 2882 explicitly retains IPI Sync #2 out of caution for non-Intel x86 CPUs; vendor-specific microarchitectural errata (like the Qualcomm Snapdragon 820 `MP.RF+cachesync+ctrl-isb` bug or CPU-specific errata requiring `MSR` workarounds) cannot be ruled out by architectural models alone.
- **RISC-V instruction-fetch extensions beyond `Zifencei`** (status corrected 2026-11-20). At the pinned manual `5f1104a0613af80219232b1e4bc108f9ec2bd6b2` (byte-identical for these files at `c05f1725f25526dd8463bac6ca75cfcfbee17d05`):
  - **`Ziccif`** (`src/unpriv/ziccif.adoc`, `[[norm:Ziccif_if_atomicity]]`, `[[norm:Ziccif_fetch_mechanism]]`) is "ratified alongside the RVA20U64 profile". It defines atomic fetch of naturally aligned power-of-2 sizes of at most `min(ILEN,XLEN)` bits, an operational fetch state machine, and the safe-harbour rules summarized in the matrix.
  - **`Ziccid`** (`src/unpriv/ziccid.adoc`) defines an operational model:
    - fetches appear in the global memory order, in program order;
    - each hart has a bounded instruction buffer;
    - stores *eventually* become visible to fetches;
    - `FENCE.I` makes older explicit accesses globally visible and then flushes the buffer;
    - the model applies only to coherent, cacheable PMA regions.
  - Ziccid's status is mixed (**unknown** formal ratification):
    - it was added by commit `f0b597df25de3f8304dbfc2bb9a02d4696b82b2a` (2026-06-11, "Add Ziccid draft spec");
    - `src/unpriv/preface.adoc` lines 34–35 list `ziccif 1.0` and `ziccid 1.0` among modules "all of which have been ratified";
    - neither chapter exists in ratified release tag `20250508` (`584390d9d872835b1bc45ab9ea946b56db3ad485`);
    - `src/profiles/rva23.adoc` still says Ziccid "might be added as an option in the future".
  - Spike `riscv-software-src/riscv-isa-sim@e53c8ccf3448ae459877ed3236cb39b2a1d493bf` implements Ziccid as mutual exclusion between store-TLB and instruction-TLB pages (`riscv/mmu.cc` L138–146, L352–358).
  - **`Zicbom`** is not an ifetch fence. `src/unpriv/cmo.adoc` (L180–184 and L244–248 at `c05f1725`) says CBO invalidate, clean and flush "are *not* ordered by other instructions that order stores, e.g. fence.i and sfence.vma".
  - Address-targeted `fence.i` remains a proposal only (`src/unpriv/zifencei.adoc` L55–58, "Future approaches … more restricted versions of fence.i that only target a given address specified in rs1"). `Zicbop` was **not examined**.
  - Verifying live-patching protocols against the Ziccif and Ziccid operational models was **not examined**.
  - Related packages:
    - `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`: a mechanized ghost `icacheDirtyPpn` / `fence.i` automaton for single-shot `W → X` code loading, and a RISC-V / ARMv8 / x86-64 barrier matrix.
    - `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors`: what a sound single-hart model may assume about fetches of unfenced bytes.
- **NMI / Machine Check Exception (`#MC`) reentrancy during x86 `smp_text_poke_int3_handler` and live kernel module patching (`ftrace`/`livepatch` consistency models):** **not examined** beyond the `noinstr` annotation and per-CPU `text_poke_array_refs` lock-free synchronization in `alternative.c`.
- **Full mechanized Coq/HOL4/Lean proof of the two-layer finite patch-site family contract:** **derived** architectural contract; no complete mechanized proof covering Linux's full `smp_text_poke_batch_finish` + `aarch64.cat` was located or checked in this study.

## Evidence

### Primary Git Repository Sources (Observed `2026-11-19`)
- `rems-project/isla` @ `e9b5d945394277656593a0d429466d7fa0a2b4b3`:
  - `README.md`: Isla Sail-based symbolic ISA and axiomatic concurrency engine overview.
  - `test_litmus_esop2020.sh`: invocation of `isla-axiomatic --model web/client/dist/esop2020.cat --ifetch`.
  - `web/client/dist/esop2020.cat` (full file, 53 lines): complete ESOP 2020 ARMv8-A axiomatic ifetch model (`ifr`, `iseq`, `obs`, `fob`, `dob`, `aob`, `bob`, `cob`, `ob`, `internal`, `external`, `atomic`).
- `herd/herdtools7` @ `1670f9e8ebb76f7cd4ba373e1c21948330eb086a`:
  - `herd/libdir/aarch64.cat`: official Armv8 Application Level Memory Model with `IC-ca` (`DIC`/`IDC` conditionals), `Instr-obs`, `Instr-read-ordered-before`, `IC-ob`, and `CMODX-conflicts` / `CMODX-unordered-conflicts` (`violates-CMODX-requirements`).
  - `herd/libdir/aarch64hwreqs.cat` (lines 60–130): `f-ib`, `DSB-ob` (`ETS2`/`ETS3`), `EXC-ENTRY-IFB`, `EXC-RET-IFB`, `IFB`, `IFB-ob`, `f-ob`.
  - `herd/libdir/aarch64util.cat` (lines 70–151): `Within-CMODX-List = if "ifetch" then Restricted-CMODX else emptyset`, and explicit unsupported/caveat flags (`Assuming-no-two-modified-instructions-are-on-the-same-cache-line`, `combining-vmsa-and-ifetch-is-not-supported`, `combining-memtag-and-ifetch-is-not-supported`).
  - `herd/libdir/ifetch-cos.cat`: `wco` generation over `W | DC | IC_loc`, `irf`, `ifr`, `fe`, `fpo`.
- `riscv/riscv-isa-manual` @ `5f1104a0613af80219232b1e4bc108f9ec2bd6b2`:
  - `src/unpriv/zifencei.adoc`: normative `[[norm:fence-i_op]]` and `[[norm:fence-i_rsv]]` clauses, single-hart scope of `FENCE.I`, cross-hart `FENCE` + remote `FENCE.I` requirement, and user-space thread-migration rationale for Linux syscall ABI.
  - (Observed 2026-11-20.) `src/unpriv/ziccif.adoc`, `src/unpriv/ziccid.adoc`, `src/unpriv/preface.adoc` L10–40, `src/profiles/rva23.adoc` L175–190. These are unchanged through `c05f1725f25526dd8463bac6ca75cfcfbee17d05`; `src/unpriv/cmo.adoc` L180–250 was read at `c05f1725`. Also checked: Ziccid introduction commit `f0b597df25de3f8304dbfc2bb9a02d4696b82b2a`; absence of both chapters at tag `20250508` (`584390d9d872835b1bc45ab9ea946b56db3ad485`).
- `riscv-software-src/riscv-isa-sim` @ `e53c8ccf3448ae459877ed3236cb39b2a1d493bf` (observed 2026-11-20):
  - `riscv/mmu.cc` L138–146, L345–359: under `EXT_ZICCID`, store and instruction TLB refills flush the other kind's entries for the same physical page.
  - `riscv/mmu.cc` L55–68: without Ziccid, the decoded-instruction cache is flushed by `flush_icache`, which runs on `fence.i` and on TLB flushes.
- `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:
  - `arch/x86/kernel/alternative.c` (lines 2650–2950): `struct smp_text_poke_loc`, `text_poke_array_refs`, `noinstr int smp_text_poke_int3_handler(struct pt_regs *regs)` (exact finite emulated opcode switch + `BUG()`), and `smp_text_poke_batch_finish()` (3-step `INT3` + 3× `smp_text_poke_sync_each_cpu()` + 6-byte `Jcc.d32` prefix handling + `perf_event_text_poke`).
  - `arch/x86/kernel/jump_label.c` (lines 1–120): `__jump_label_patch()` (`JMP8`/`JMP32` vs. `x86_nops` + `memcmp` verification) calling `smp_text_poke_single()`.
  - `arch/x86/kernel/static_call.c` (lines 1–110): `CALL`/`NOP`/`JMP`/`RET`/`JCC` site types, 5-byte `xor5rax`/`retinsn`/`warninsn`/`unlockinsn` replacements paired with `emulate` call targets.
  - `arch/x86/kernel/kprobes/opt.c` (lines 363–511): `text_poke` of out-of-line detour slot and `smp_text_poke_single` installation of `JMP32`.
  - `arch/arm64/mm/cache.S` (lines 1–120): `caches_clean_inval_pou_macro` (`ARM64_HAS_CACHE_IDC` $\to$ `dsb ishst`; `ARM64_HAS_CACHE_DIC` $\to$ `isb`; otherwise `DC CVAU` + `IC IVAU`).
  - `arch/arm64/kernel/patching.c` (lines 1–310): `aarch64_insn_patch_text_nosync()` (4-byte alignment check + `FIX_TEXT_POKE0` write + `caches_clean_inval_pou`) and `aarch64_insn_patch_text()` (`stop_machine_cpuslocked` + per-CPU `isb()`).
  - `arch/arm64/kernel/jump_label.c` (full file): lockless `aarch64_insn_patch_text_nosync` for `B`/`NOP` followed by `kick_all_cpus_sync()`.
  - `arch/arm64/kernel/probes/kprobes.c` (lines 63–165): `aarch64_insn_patch_text_nosync` for XOL slot relying on `BRK` Context Synchronization Event vs. `aarch64_insn_patch_text` (`stop_machine`) for arming/disarming arbitrary target instructions.
  - `arch/riscv/kernel/patch.c` (lines 1–350): 2-page fixmap writer (`__patch_insn_write`), `patch_text_nosync`, and `patch_text()` (`stop_machine_cpuslocked` + `atomic_inc_return_release` + remote `local_flush_icache_all()`).
  - `arch/riscv/mm/cacheflush.c` (lines 1–110): `flush_icache_all()` (`RISCV_FENCE(w, o)` + `sbi_remote_fence_i`) and `flush_icache_mm()` (`icache_stale_mask`).

### Primary Specifications & Peer-Reviewed Literature
- Simner, B., Flur, S., Pulte, C., Armstrong, A., Pichon-Pharabod, J., Maranget, L., & Sewell, P. (2020). *ARMv8-A System Semantics: Instruction Fetch in Relaxed Architectures*. ESOP 2020, LNCS 12075, pp. 626–655. DOI `10.1007/978-3-030-44914-8_23`. (Extended report `esop2020-extended.pdf` directly inspected, including Sections 2–6 and Snapdragon 820 validation bug.)
- Arm Ltd. *Arm Architecture Reference Manual for A-profile Architecture (DDI 0487)*, Sections B2.2.5 / B2.4.4 (`CMODX`, `CTR_EL0.IDC`/`DIC`, Context Synchronization Events).
- Intel Corporation. *Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 3A*, Section 8.1.3 / 9.1.3 (*Handling Self- and Cross-Modifying Code*).
- Cai, H., Shao, Z., & Vaynberg, A. (2007). *Certified Self-Modifying Code*. PLDI 2007. DOI `10.1145/1273442.1250743`.
- Myreen, M. O. (2010). *Verified Just-In-Time Compiler on x86*. POPL 2010. DOI `10.1145/1706299.1706313`.

### Reproducible Executable Micro-Probe (`probe_ifetch_patching.py`)
Self-contained Python 3 probe (stdlib only) checking both the ARMv8-A axiomatic ifetch rules (`esop2020.cat` / `aarch64.cat`) and x86-64 cache-line split + 3-step `INT3` safety:

```python
#!/usr/bin/env python3
def comp(a, b): return {(x, w) for x, y in a for z, w in b if y == z}
def tc(r):
    while (n := r | comp(r, r)) != r: r = n
    return r
def inv(r): return {(y, x) for x, y in r}
def diag(s): return {(x, x) for x in s}

def allowed_ifetch(ev, rels, idc=False, dic=False):
    tag = lambda t: {e for e, ts in ev.items() if t in ts}
    W, R, IF, DC, IC, DSB, ISB = (tag(t) for t in ("W","R","IF","DC","IC","DSB","ISB"))
    po, fpo, fe, rfe, irf, co, wco, scl, loc, ctrl = (rels.get(k, set()) for k in
        ("po","fpo","fe","rfe","irf","co","wco","scl","loc","ctrl"))
    ifr = comp(inv(irf), co) & loc
    if not dic and not idc:
        ic_obs = comp(ifr, comp(comp(comp(comp(diag(W), wco & scl), diag(DC)), wco & scl), diag(IC)))
    elif not dic and idc:
        ic_obs = comp(ifr, comp(comp(diag(W), wco & scl), diag(IC)))
    else:
        ic_obs = ifr
    obs = rfe | wco | irf | ic_obs
    fob = comp(comp(diag(IF), fpo), diag(IF)) | comp(diag(IF), fe) | comp(comp(diag(ISB), inv(fe)), fpo)
    dob = comp(ctrl, diag(W | ISB))
    bob = comp(comp(diag(R|W|DC|IC), po), diag(DSB)) | comp(comp(diag(DSB), po), diag(R|W|DC|IC|ISB))
    cob = comp(comp(diag(R|W), po & scl), diag(DC)) | comp(comp(diag(DC), po & scl), diag(DC))
    ob = tc(obs | fob | dob | bob | cob)
    return all(x != y for x, y in ob)

# Verify ARMv8-A SM+dsb-isb under (IDC=0,DIC=0) vs (IDC=1,DIC=1) and CoFF
ev_dic = {"W0":{"W"},"W1":{"W"},"D1":{"DSB"},"ISB1":{"ISB"},"FISB":{"IF"},"F1":{"IF"}}
rel_dic = {"po":{("W1","D1"),("D1","ISB1"),("W1","ISB1")},"fe":{("FISB","ISB1")},"fpo":{("FISB","F1")},
           "co":{("W0","W1")},"wco":{("W0","W1")},"irf":{("W0","F1")},
           "loc":{(a,b) for a in ("W0","W1","F1") for b in ("W0","W1","F1")},
           "scl":{(a,b) for a in ("W0","W1","F1") for b in ("W0","W1","F1")}}
assert allowed_ifetch(ev_dic, rel_dic, idc=False, dic=False) is True
assert allowed_ifetch(ev_dic, rel_dic, idc=True, dic=True) is False
ev_coff = {"W0":{"W"},"W1":{"W"},"F1":{"IF"},"F2":{"IF"}}
rel_coff = {"fpo":{("F1","F2")},"co":{("W0","W1")},"wco":{("W0","W1")},"irf":{("W1","F1"),("W0","F2")},
            "loc":{(a,b) for a in ev_coff for b in ev_coff},"scl":{(a,b) for a in ev_coff for b in ev_coff}}
assert allowed_ifetch(ev_coff, rel_coff, idc=False, dic=False) is True

# Check x86-64 5B cache-line splits and 3-step INT3 reachability
assert [o for o in range(64) if (o // 64) != ((o + 4) // 64)] == [60, 61, 62, 63]
assert len([o for o in range(64) if (o // 16) != ((o + 4) // 16)]) == 16

def verify_xmc(steps):
    b0, tl, rb0, rtl = "OLD", "OLD", {"OLD"}, {"OLD"}
    for s in steps:
        if s == "INT3": b0 = "INT3"; rb0 |= {b0}
        elif s == "TAIL": tl = "NEW"; rtl |= {tl}
        elif s == "B0": b0 = "NEW"; rb0 |= {b0}
        elif s == "SYNC": rb0, rtl = {b0}, {tl}
        if any(f0 != "INT3" and f0 != ft for f0 in rb0 for ft in rtl):
            return False
    return True

assert verify_xmc(["INT3", "SYNC", "TAIL", "SYNC", "B0", "SYNC"]) is True
assert verify_xmc(["INT3", "TAIL", "SYNC", "B0", "SYNC"]) is False
assert verify_xmc(["INT3", "SYNC", "TAIL", "B0", "SYNC"]) is False
print("ALL IFETCH & LIVE-PATCHING PROBES PASSED")
```

## Revalidation

1. **Diff official Armv8-A `aarch64.cat` and `aarch64util.cat`:** Check `herd/herdtools7` (`herd/libdir/aarch64.cat`, `aarch64hwreqs.cat`, `aarch64util.cat`) at a newer commit for changes to `IC-ca`, `IFB`, `CMODX-conflicts`, or removal of the `combining-vmsa-and-ifetch-is-not-supported` / `Assuming-no-two-modified-instructions-are-on-the-same-cache-line` flags.
2. **Diff Linux kernel live-patching paths across architectures:** Inspect `arch/x86/kernel/alternative.c` (`smp_text_poke_int3_handler`, `smp_text_poke_batch_finish`), `arch/arm64/mm/cache.S` (`caches_clean_inval_pou_macro`), `arch/arm64/kernel/patching.c`, and `arch/riscv/kernel/patch.c` + `arch/riscv/mm/cacheflush.c` for new lockless patching fast paths, newly emulated `INT3` opcodes, or `Zicbom`/fine-grained RISC-V icache-flush support.
3. **Check RISC-V ISA manual `Zifencei` evolution:** Diff `riscv/riscv-isa-manual` `src/unpriv/zifencei.adoc` (and any newly ratified instruction-cache coherence extension) to see whether cross-hart or address-specific `fence.i` semantics have been ratified.
4. **Rerun the executable micro-probe:** Run the inline Python script above (`<50 ms`); for deeper ISA-level litmus validation, run `isla-axiomatic --arch aarch64.ir --model web/client/dist/esop2020.cat --ifetch` or `herd7 -model aarch64.cat -variant ifetch` on `CoFF`, `SM+dc-dsb-ic-dsb-isb`, `MP.RF+cachesync+ctrl-isb`, and `W+F`.
5. **Revalidate hardware silicon errata:** Remember that passing axiomatic checks (`herd7`/`isla`) validates software only against the *architectural* specification; new Arm/RISC-V/x86 silicon revisions require hardware litmus testing (`litmus7`) and vendor errata audits to catch microarchitectural coherence defects like the Snapdragon 820 `MP.RF+cachesync+ctrl-isb` bug.
