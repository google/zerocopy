# Foundational Software Fault Isolation and Extensible Kernel Architectures (1993–2011)

## Summary

Between 1993 and 2011, systems that hosted untrusted extensions inside a shared address space or kernel discovered a strict **four-layer hierarchy of isolation invariants**, where each generation's mechanism leaves an explicit residual failure mode that motivated the next layer:

1. **Layer 1 — Contiguous Address Masking, Bundle Alignment, and Dedicated-Register Interrupt Atomicity (Wahbe et al. SOSP 1993; PittSFIeld USENIX Security 2006):**
   Bitwise address sandboxing (`sandboxAddr base mask addr = (addr &&& mask) ||| base`) confines loads, stores, and indirect jumps to a power-of-two segment `[base, base + 2^k)` when `(base &&& mask) = 0` and `mask = 2^k - 1`. On variable-length CISC architectures (x86), range confinement alone fails because jumping into the middle of a multi-byte instruction decodes an unintended opcode stream; PittSFIeld closes this by clearing low alignment bits (`0x10fffff0`) so every indirect control transfer lands on a 16-byte chunk boundary. Even with alignment, two atomicity hazards remain: (a) if an interrupt or context switch occurs between masking a target address into a non-dedicated scratch register and using it, a signal handler or resumption path can clobber the register unless the sandboxed address is held in a **dedicated register** whose segment invariant is preserved or re-established across interrupts (Wahbe's 5-register MIPS/Alpha discipline vs. PittSFIeld's 1-register `%ebx` reservation); and (b) PittSFIeld's default return sequence (`andl $0x10fffff0, (%esp); ret`), chosen to preserve hardware Return Stack Buffer (RSB) prediction, masks the return address **in place on the shared stack**, opening a 1-instruction multi-threaded TOCTOU race unless popped into a register first (`--pop-ret`).
2. **Layer 2 — Bounded Execution Fuel and Differential Determinism for In-Kernel Downloaded Code (Exokernel / Aegis SOSP 1995; ASH & DPF SIGCOMM 1996; XOK / `XN` SOSP 1997):**
   Exokernel separates **bind-time policy authorization** from **$O(1)$ use-time capability checking** and downloads untrusted handlers into the kernel: Application-Specific Handlers (ASHs, confined via SFI + bounded backward-branch loop counters), Dynamic Packet Filters (DPF, compiled from amerged filter trie with structural shift-offset bounds hoisting), and `XN` User-Defined Functions (`owns-udf_T`, executed by a deterministic 37-opcode pseudo-RISC interpreter in `sys/ubb/interp.c`). Rather than verifying that an untrusted LibOS's `owns-udf_T` bytecode semantically matches its user-space filesystem layout, `XN` enforces a **Differential Determinism Pattern**: `udf_check` (`sys/ubb/check.c:106–185`) verifies that the UDF is pure, deterministic, and bounded (`INST_BUDGET = 100`), and `udf_alloc`/`udf_write`/`udf_dealloc` (`sys/ubb/udf.c:204–309`) re-evaluate `old_set = udf_run(meta)` and `new_set = udf_run(meta')` around every metadata mutation. For *any* pure function `f : MetadataBlock → List PhysBlock` (even a buggy or adversarial one), initializing every metadata slot `mInit` with `f mInit = []` and checking that added blocks `f(m') \ f(m)` are globally free (`db_isfree`) while freeing removed blocks `f(m) \ f(m')` guarantees that the kernel's global free map and all metadata slots' owned block sets remain **strictly pairwise disjoint** at all reachable states. Differential determinism protects **inter-LibOS physical block isolation** and catches silent block drops during `udf_write` (`set_eq(old_set, new_set)`), but does **not** prevent **intra-LibOS self-corruption** if `f(m)` disagrees with the LibOS's own user-space read path.
3. **Layer 3 — Split Scoped/Allocation Stacks, Byte-Granular Typestate Rights, and Capability-Mediated API Integrity (MiSFIT 1997; Nooks SOSP 2003; XFI OSDI 2006; BGI SOSP 2009; LXFI SOSP 2011):**
   Layer-1 SFI places the execution stack inside the writable data segment, allowing a linear heap/array overflow inside the sandbox to overwrite saved return addresses on the stack without violating segment bounds. **XFI** splits the stack into a pointer-free `ScopedStack` (holding return addresses, spilled registers, and control state, accessible only via static constant offsets from `SSP`) and an `AllocationStack` (for address-taken locals and arrays) alongside inline Control-Flow Integrity (CFI). However, in monolithic kernels (Windows, Linux), drivers allocate kernel objects (`KEVENT`, `KDPC`, `KTIMER`, `spinlock_t`) directly inside their own writable stack/heap and pass raw pointers to core kernel routines (`spin_lock_init(ptr)`), creating **in-sandbox kernel object corruption** and **confused-deputy API attacks**. **BGI** closes the in-sandbox object gap with a 1-byte-per-8-byte-slot `<domain, right>` table (`12.5%` space overhead) whose `SetType(p, size, type)` transition revokes the driver's direct byte-write permission (`<d, write> → <d, event>`) on the driver's own memory while the kernel object is active. **LXFI** adds multi-principal data-structure instances (`principal(sk)`, `principal(dev)`), generated capability proxies (`WRITE`, `REF`, `CALL`), and **writer-set tracking** on module-writable callback tables (`lxfi_check_indcall`) to defeat confused-deputy helpers and callback-table overwrites (such as CVE-2010-3904 in Linux `RDS`).
4. **Layer 4 — Kernel Extension Abort, Timeout, and Cancellation Recovery (VINO OSDI 1996 vs. Exception-Table Landing Pads + RAII `Drop` vs. Static Exceptionless Admission):**
   Even when an extension satisfies Layer 1 (memory confinement), Layer 2 (bounded fuel), and Layer 3 (CFI + capability-checked API calls), a synchronous fault (`#PF` on a guard page) or asynchronous watchdog timeout *after* the extension has acquired a kernel lock and mutated step 1 of a multi-part kernel state invariant leaves the kernel deadlocked or corrupted unless paired with a recovery mechanism. Comparing the four recovery architectures shows:
   - **Mode A (Non-unwinding trap kill):** Terminating the faulting thread inside the trap handler leaks held spinlocks and leaves half-mutated shared state.
   - **Mode B (Exception-table landing pad `__ex_table` + stack RAII `Drop` / C cleanup `goto`):** Redirecting the trapping instruction pointer to a local landing pad returning `Err(EFAULT)` allows stack-frame RAII `Drop` guards to release held spinlocks cleanly **if and only if** all fallible accesses precede shared-state mutation (*check-before-mutate*). If a fault occurs after a partial shared-state mutation, RAII `Drop` releases the lock (`lockHeld = false`) while exposing corrupted shared state (`primaryTable ≠ shadowAccounting`).
   - **Mode C (VINO dynamic LIFO compensating `undoStack` + two-phase locking):** Recording inverse mutators on a per-graft undo stack and holding locks until transaction commit or abort restores arbitrary multi-step shared-state mutations and releases locks across both synchronous faults and asynchronous watchdog timeouts, at the cost of per-mutation logging overhead.
   - **Mode D (Static exceptionless + bounded-resource admission, e.g., Anneal `SafeProgram.terminates` + `Refines`):** Proving at admission time that all memory accesses are in bounds (`Exceptionless`) and execution fuel is sufficient (`ResourceBounded`) eliminates runtime trap/timeout aborts (`aborted = false`) and preserves kernel quiescent invariants without runtime undo logs.

All four layers, their separating counterexamples, the universal $N$-slot differential determinism characterization, and the four-mode recovery comparison are mechanized in Lean 4 (`v4.34.1`) in [`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) (2,246 lines, zero warnings, `0 sorryAx`, `0 Classical.choice`, `0 Lean.ofReduceBool`).

---

## Applicability

This report examines the foundational software fault isolation (SFI) and extensible operating system architectures published between 1993 and 2011 identified in `REPORT.json`, together with their preserved source implementations (`pittsfield-0.7.tar.gz`, `pittsfield-proof-2009-10-30.tar.gz`, `pdos/xok@490cd2496ebbd2b4032c191a036c5711d118e3b9`, `dpf.tar.gz`) and their structural correspondence to the Anneal Rust-to-Lean-4 verification toolchain (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`).

The subjects relate as a **capability-and-invariant progression across shared-address-space extension substrates**:
- **Instruction-level SFI substrates** (Wahbe et al. 1993 on MIPS R3000 and DEC Alpha; PittSFIeld 2006 on IA-32 x86) define the bit-masking, alignment, and register-reservation rules for confining untrusted machine code within a contiguous virtual memory region.
- **Exokernel downloaded-code subsystems** (Aegis 1995, ASH 1996, DPF 1996, XOK/`XN` 1997) apply instruction-level sandboxing, bounded loop counters, dynamic code generation, and deterministic bytecode interpretation (`sys/ubb/interp.c`) to untrusted handlers and filesystem metadata functions inside an extensible kernel.
- **Commodity kernel extension isolation systems** (VINO 1996, MiSFIT 1997, Nooks 2003, XFI 2006, BGI 2009, LXFI 2011) address the gap between raw memory-range sandboxing and monolithic kernel invariants (return-address integrity, in-place kernel synchronization objects, confused-deputy helpers, multi-principal driver instances, and mid-operation extension aborts).
- **Anneal (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`)** serves as the static compile-time reference point against which runtime SFI guards, dynamic typestate tables, differential determinism, and compensating undo logs are compared.

Observations from primary papers (`documentation`) and historical source trees (`source`) apply directly to the cited architectures and revisions. The mechanized theorems in [`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) (`execution` + `derived`) apply to the formal state-transition models defined in that file and verified under Lean `v4.34.1` on `x86_64-unknown-linux-gnu`.

---

## Findings

### 1. Layer 1 — Contiguous Segment Masking, CISC Bundle Alignment, and Interrupt/Return Atomicity (Wahbe SOSP 1993 & PittSFIeld USENIX Security 2006)

**Basis:** `documentation` (Wahbe et al. SOSP 1993 §§2–4; McCamant & Morrisett USENIX Security 2006 §§3–4; MIT-CSAIL-TR-2005-067; MIT-CSAIL-TR-2006-035) + `source` (`pittsfield-0.7/sfi.pl`, `verify.pl`, `loader.c`; `pittsfield-proof-2009-10-30/sfi.lisp`) + `execution` + `derived` ([`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) `Layer1_WahbePittSFIeld`).

#### 1.1 Segment Matching vs. Address Sandboxing
Wahbe et al. define a fault domain as two contiguous power-of-two virtual memory segments—a code segment and a data segment—each identified by a common upper-bit prefix (**segment ID**). Given segment base $B$, power-of-two size $S = 2^k$, and bitmask $M = 2^k - 1$ where $B \mathbin{\&} M = 0$:

- **Segment Matching (4 instructions, exact fault address diagnostics, trap-on-violation):**
  ```assembly
  srl  dedicated_reg, unsafe_reg, shift_amt   # extract upper segment ID bits
  bne  dedicated_reg, seg_id_reg,8f           # trap if target segment != seg_id
  nop                                         # MIPS branch delay slot
  sw   val, 0(unsafe_reg)                     # safe access
  ```
- **Address Sandboxing (2 instructions, no branch, overwrites in-sandbox offset on error):**
  ```assembly
  and  tmp_reg, unsafe_reg, mask_reg          # clear upper bits (offset in [0, 2^k - 1])
  or   dedicated_reg, tmp_reg, seg_reg        # set upper segment ID bits
  sw   val, 0(dedicated_reg)                  # access via dedicated_reg
  ```
  In [`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean), `sandboxAddr_bounds` and `sandboxAddr_satisfies_segmentMatch` constructively prove (via a custom `onesMask` induction `and_two_pow_sub_one_eq_mod` avoiding `Classical.choice`) that for any arbitrary `addr : Nat`, `base ≤ sandboxAddr base (2^k - 1) addr < base + 2^k` and `(sandboxAddr base (2^k - 1) addr) / 2^k = base / 2^k`.

- **Guard Zones for Reg+Offset Addressing (`wahbe_guard_zone_offset_confinement`):**
  RISC load/store instructions support immediate displacements `offset(dedicated_reg)` ($-2^{15} \le \text{offset} < 2^{15}$ on MIPS). By placing unmapped guard zones of size $G$ immediately below $B$ and above $B + 2^k$, `dedicated_reg + offset` can never step across the guard zone into an adjacent segment without faulting (`base ≤ sandboxAddr base (2^k - 1) addr + offset < base + 2^k + G`), avoiding an extra `add` instruction before sandboxing.

#### 1.2 Dedicated Register Discipline vs. PittSFIeld Single-Register `0x0f`-Aligned Bundles
| Property | Wahbe et al. (SOSP 1993, MIPS / Alpha) | PittSFIeld (USENIX Security 2006, IA-32 x86) |
| :--- | :--- | :--- |
| **Dedicated Registers** | **5 dedicated registers** (or 4 when shift replaces code mask): `dedicated-code`, `dedicated-data`, `data-segment-id`, `code-segment-id`, `sandbox-mask` | **1 dedicated register (`%ebx`)** holding sandboxed effective address (`%ebp` optionally reserved under `--reserve-ebp` to save 1 byte on stack-frame accesses) |
| **Mask Constants** | Held in dedicated registers (`mask_reg`, `seg_reg`) because RISC lacks full 32-bit immediates in ALU instructions | Encoded as **32-bit immediates** directly inside x86 `andl`/`orl` instructions (`verify.pl:71`, `sfi.pl:91`), requiring zero registers for masks/tags |
| **Zero-Page Trick (`Single-AND` Optimization)** | Requires both `AND` and `OR` | Maps page `0` (`0x00000000..0x0000ffff`) unmapped (`PROT_NONE`) and chooses segment tags with a single set bit (`data_tag = 0x20000000`, `code_tag = 0x10000000`). A single `andl $0x20ffffff, %ebx` forces `addr` into either `[0, 2^k)` (if bit 29 was 0, guaranteed to hardware-fault in the unmapped zero region) or `[0x20000000, 0x20ffffff]` (if bit 29 was 1), eliminating the `orl` instruction (`pittsfieldSingleAnd_dichotomy`) |
| **Instruction / Target Alignment** | Fixed 4-byte RISC instructions | **16-byte chunks** (`chunk_size = 16`, mask clears low 4 bits `0x0f` via `0x10fffff0`). No instruction or basic-block header may cross a 16-byte boundary; multi-instruction `sandbox + jump` sequences must reside within the **same 16-byte chunk** (`verify.pl:185–240`, `sfi.lisp:186–295`) |

#### 1.3 Delay Slots, Mid-Instruction CISC Jumps, Interrupt Atomicity, and the Shared-Stack Return TOCTOU Race
1. **MIPS Delay Slots & CISC Mid-Instruction Jumps (`cisc_unaligned_jump_counterexample`):**
   On MIPS, a branch delay slot executes even if the branch is taken; placing `or dedicated_reg, tmp_reg, seg_reg` in the delay slot of an untrusted branch allows a fall-through path to skip the `or`. On CISC x86, jumping into byte offset `+1` of `andl $0x20ffffff, %ebx` (`81 e3 ff ff ff 20`) decodes the immediate operand bytes as an unguarded instruction stream (`sandboxCodeAligned_confinement_and_alignment` vs. `cisc_unaligned_jump_counterexample`).
2. **Interrupt / Context-Switch Atomicity (`non_dedicated_scratch_mid_sequence_escape` vs. `wahbe_dedicated_reg_mid_sequence_safe`):**
   Why must `dedicated_reg` *always* hold a valid sandboxed address (or why must PittSFIeld's verifier reset register safety at every 16-byte chunk boundary)?
   - If a compiler uses a general-purpose scratch register `r_scratch` (`r_scratch := (target & mask) | seg_id; store [r_scratch], val`) and an asynchronous timer interrupt or Unix signal fires **between** the mask instruction and the `store`, a signal handler or context-switch path that clobbers or fails to re-validate `r_scratch` causes the resumed `store [r_scratch], val` to write to an arbitrary kernel/host address (`non_dedicated_scratch_mid_sequence_escape`).
   - Under Wahbe's dedicated-register discipline, `dedicated_reg` is initialized inside the sandbox before domain entry, updated *only* via `(r & mask) | seg_id` (or by moving `(r & mask)` into `dedicated_reg` and immediately `OR`ing `seg_id`, where an interrupted intermediate value `(r & mask) < 2^k` lands in unmapped low memory `[0, 2^k)` and traps safely if dereferenced), and the OS trap/context-switch handler refuses orrolls back any context resuming at an unmasked indirect jump (`wahbe_dedicated_reg_mid_sequence_safe`).
3. **Cross-Fault-Domain LRPC Trampoline Invariants (Wahbe et al. §3.2):**
   Cross-domain calls cannot jump directly between fault domains because the caller's code mask prevents jumping outside the caller's code segment. Wahbe's stub generator emits a **per-export-entry call/return stub pair sitting outside both domains**: a single `jalr` leaves the caller's sandbox via a hardwired target table at the bottom of the code segment, the trusted stub saves/restores callee-saved registers, copies arguments directly between domains, switches the 5 dedicated segment/mask registers, and adjusts the hardware timer quantum if interrupted mid-stub.
4. **PittSFIeld's In-Place Stack Return Sequence TOCTOU Race (`pittsfield_inplace_ret_toctou_race`):**
   In `pittsfield-0.7/sfi.pl:234–245`, PittSFIeld's default return sequence is:
   ```assembly
   andl $0x10fffff0, (%esp)
   orl  $0x10000000, (%esp)
   ret
   ```
   PittSFIeld masks `(%esp)` *in place* in memory rather than popping into `%ebx` and executing `jmp *%ebx` so that the CPU's hardware **Return Stack Buffer (RSB)** continues to pair `call` and `ret` instructions (avoiding a 23% slowdown on `gcc`). However, as noted in McCamant & Morrisett §4 (`sfi.pl` `--pop-ret` flag) and mechanized in `pittsfield_inplace_ret_toctou_race`, because `(%esp)` resides in shared writable data memory (`0x20xxxxxx`), a concurrent thread in a multi-threaded sandbox can overwrite `(%esp)` *between* the `orl` and `ret` instructions, hijacking `EIP` to an arbitrary address `0xdeadbeef`! Safe multi-threaded SFI therefore requires either popping into a register (`popl %ebx; andl ...; jmp *%ebx`) or placing return addresses on a thread-private / write-protected shadow stack (`ScopedStack` in XFI).

---

### 2. Layer 2 — Exokernel Secure Bindings, Bounded Fuel (`ASH` / `DPF`), and Differential Determinism (`XN` `owns-udf_T`)

**Basis:** `documentation` (Engler et al. SOSP 1995 §3; Wallach et al. SIGCOMM 1996 §§2–3; Engler & Kaashoek SIGCOMM 1996 §§2–4; Kaashoek et al. SOSP 1997 §3) + `source` (`pdos/xok@490cd2496ebbd2b4032c191a036c5711d118e3b9` `src/exopc/sys/kern/scode.c`, `src/exopc/sys/ubb/{udf.c,interp.c,check.c,xn.c,ubs.h}`, `dpf.tar.gz` `src/dpf/{gen.c,optimize.c,tree.c}`) + `execution` + `derived` ([`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) `Layer2_ExokernelAshDpfxn`).

#### 2.1 Secure Bindings: Bind-Time Authorization vs. $O(1)$ Use-Time Checking
Exokernel decouples **authorization** (performed once at resource bind time, e.g., when a LibOS binds a virtual page into its software TLB or installs a packet filter) from **use-time access checking** (performed on every hardware TLB reload or packet arrival by checking a capability tag or self-authenticating capability). Theorem `exokernel_secure_binding_equivalence` in [`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) proves that whenever the kernel binding table only admits entries satisfying `bindTimePolicy owner cap res`, the $O(1)$ use-time tag check `checkUseTimeBinding table idx callerCap` is logically equivalent to full policy re-evaluation.

#### 2.2 ASH Bounded Backward-Branch Loop Counters (`scode.c`) and DPF Trie-Compiled Filters (`dpf2.0`)
- **ASHs (SIGCOMM 1996 & `src/exopc/sys/kern/scode.c`):**
  ASHs execute at interrupt time inside the kernel to perform integrated layer processing (checksumming, dynamic scatter-gather DMA initiation via `ae_eth_poll`, and immediate reply generation). In `src/exopc/sys/kern/scode.c:1–295`, XOK enforces two invariants on downloaded handlers:
  1. **Memory sandboxing (`scode_CheckProg`):** Rewrites/verifies memory loads and stores to mask addresses into the env's `s_region` or `ASH_REGION` (`(addr & s_mask) | s_base`).
  2. **Bounded backward-branch loop counters (`scode_instrument_branches` & `ash_backward_branch_exhausts_fuel`):** Forward jumps advance monotonically through the handler; every **backward branch** is instrumented to decrement a dedicated dynamic loop-trip counter register (initialized to a small constant budget before ASH entry) and jump to `scode_abort` if the counter reaches 0. Theorem `ash_backward_branch_exhausts_fuel` proves that even an infinite backward loop (`pc → pc`) terminates in at most `fuel + 1` steps.
- **DPF (SIGCOMM 1996 & `dpf.tar.gz`):**
  Instead of interpreting linear filter programs sequentially (as in CMU/Stanford Packet Filter or classic BPF), DPF merges all installed filters into a **prefix trie of atoms** (`src/dpf/tree.c`). Consecutive fixed-offset equality comparisons are coalesced into word-sized mask-and-compare atoms (`coalesce_atoms`), common prefixes are shared across all filters, hash tables handle sparse disjunctions, and `src/dpf/gen.c` dynamically emits native machine code (`ir_emit`) with **bounds-check hoisting** (computing the maximum packet offset required along a straight-line atom block and emitting a single length check at block entry, plus `check_shifts` verifying shift amounts $< \text{message length}$).

#### 2.3 XOK's `XN` Deterministic Bytecode (`sys/ubb/interp.c`) and the Differential Determinism Pattern (`sys/ubb/{check.c,udf.c}`)
How can an exokernel allow untrusted LibOSes (`ExOS` C-FFS, etc.) to define arbitrary on-disk metadata layouts (inodes, indirect blocks, B-trees) without either fixing a single kernel inode format or trusting the LibOS not to point its metadata at another LibOS's physical disk blocks?

Direct inspection of `pdos/xok@490cd2496ebbd2b4032c191a036c5711d118e3b9` (`src/exopc/sys/ubb/{ubs.h,check.c,interp.c,udf.c,xn.c}`) reveals the exact mechanism:

1. **The `XN` Pseudo-RISC Virtual Machine (`ubs.h` & `interp.c:1–215`):**
   Each LibOS metadata type $T$ registers a User-Defined Function **`owns-udf_T`** written in a 37-opcode register-transfer bytecode (`UBI_ADD`, `UBI_SUB`, `UBI_AND`, `UBI_OR`, `UBI_LOAD`, `UBI_BLEQ`, **`UBI_ADD_CEXT`** to emit an owned `[base_block, extent_len]` pair into the output set `u_s`, etc.) operating on `XN_NREGS = 16` registers and having **read-only access strictly to the single metadata block `meta` being inspected** (`check_addr` bounds every `UBI_LOAD` to `[0, m_nbytes)`).
2. **Static Verification of Pure Determinism and Termination (`udf_check` in `check.c:106–185`):**
   When a type is imported (`udf_check`), the kernel verifies that:
   - Every instruction opcode, register index (`< 16`), and immediate mode is legal (`check_inst`);
   - There are no instructions that read external mutable state, time, or other disk blocks; and
   - At runtime (`udf_interp` in `interp.c:56–198`), a strict instruction counter `inst_count` aborts the UDF if it exceeds **`INST_BUDGET = 100`** instructions (`ubs.h:42`), guaranteeing total, deterministic, pure termination.
3. **Differential Set Evaluation Across Metadata Mutations (`udf.c:204–309`):**
   Crucially, **`XN` never proves that `owns-udf_T(meta)` is semantically correct!** Instead, on every metadata modification (`sys_xn_alloc`, `sys_xn_write`, `sys_xn_dealloc`), `udf.c` runs the **exact same deterministic `owns-udf_T`** on both the pre-mutation metadata block (`old_set = udf_run(t, meta)`) and the proposed post-mutation metadata block (`new_set = udf_run(t, meta')`):
   - **`udf_alloc(t, meta, meta', alloc_set)` (`udf.c:204–253`):**
     Applies the mutation (`mv_write`), computes `new_set = udf_run(t, meta')`, and checks:
     ```c
     res_s = set_Sub(new_set, old_set);
     if (!set_eq(res_s, alloc_set)) { udf_rollback(meta, mv); return XN_BOGUS_OP; }
     ```
     and verifies in `xn.c` (`db_alloc`) that every block in `alloc_set` is currently free in the global kernel free map (`db_isfree`).
   - **`udf_write(t, meta, mv)` (`udf.c:267–290`):**
     For in-place metadata updates that neither allocate nor free blocks, checks **`set_eq(old_set, new_set)`** (`udf.c:280`); if the owned block set changed at all, rolls back `meta`!
   - **`udf_dealloc(t, meta, meta', free_set)` (`udf.c:292–335`):**
     Checks **`set_Sub(old_set, new_set) == free_set`** (`udf.c:315`), proving that every block being returned to the kernel global free list was genuinely claimed by `owns-udf_T(meta)` before the mutation!

#### 2.4 Necessary and Sufficient Conditions for Differential Determinism & Its Exact Semantic Boundary
In [`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) (`Layer2_ExokernelAshDpfxn`, Section 2.4), we formalize an $N$-slot `XN` disk state `XnGeneralDisk` (`metaStore : MetaSlot → MetadataBlock`, `isFree : PhysBlock → Bool`) and establish the exact mathematical characterization of Differential Determinism:

- **Universal Inter-LibOS Physical Block Disjointness (`xnInitGeneralDisk_satisfies_inv`, `xnGeneralStep_preserves_disjoint_inv`, `xnGeneralTrace_preserves_disjoint_inv`):**
  For **any** deterministic pure function `f : MetadataBlock → List PhysBlock` (even an arbitrary, buggy, or adversarial function), if:
  1. Every metadata slot `slot` is initialized to `mInit` where `f mInit = []` (`xnInitGeneralDisk`); and
  2. Every state transition `xnGeneralStep f disk slot m'` computes `added = diffBlocks (f m') (f (disk.metaStore slot))` and `removed = diffBlocks (f (disk.metaStore slot)) (f m')`, checks `noDupBlocks added && allFree disk.isFree added == true`, updates `metaStore slot := m'`, marks `added` allocated (`isFree b = false`), and marks `removed` free (`isFree b = true`);
  then across all reachable states in any finite trace `xnGeneralTrace`, `XnGeneralDisjointInv f` holds:
  $$\forall \text{slot}, b,\; \text{isFree}(b) = \text{true} \implies b \notin f(\text{metaStore}(\text{slot}))$$
  $$\forall s_1 \ne s_2, b,\; b \in f(\text{metaStore}(s_1)) \implies b \notin f(\text{metaStore}(s_2))$$
  - *Why Purity/Determinism Is Necessary (`xn_nondeterministic_udf_breaks_disjointness`):* If `f` is stateful or nondeterministic (`evilStatefulUdf epoch m`), it can report `f_0([10]) = [10]` during `udf_alloc` (passing `db_isfree(10)`) and later report `f_1([10]) = [20]` during `udf_dealloc`, freeing or corrupting a block `20` owned by another LibOS (`metaB`).
- **Exact Boundary of What Differential Determinism Does and Does NOT Guarantee:**
  1. *Silent block drop during `udf_write` is caught (`xn_udf_write_catches_silent_block_drop`):* If a buggy UDF `f` drops an owned block `b ∈ f(m)` (`b ∉ f(m')`) during a non-deallocating metadata write, `setEqBlocks (f m') (f m)` evaluates to `false`, rolling back the write (`xnStrictUdfWrite f disk slot m' = disk`).
  2. *Disagreement between `f(m)` and the LibOS's user-space read path causes intra-LibOS self-corruption without violating global inter-LibOS isolation (`xn_differential_determinism_intra_libos_boundary`):* Differential determinism binds the kernel's free map to `f(m)`, not to the LibOS's user-space file reader `libosUserRead(m)`. As proved in `xn_differential_determinism_intra_libos_boundary` (`buggyDropOddUdf` vs. `libosUserRead`), if Slot 0's UDF ignores odd block numbers while Slot 0's user-space code writes `[10, 11]`, `XnGeneralDisjointInv buggyDropOddUdf` remains 100% preserved across all slots, yet block `11` stays globally unallocated (`isFree 11 = true`)—exposing Slot 0's LibOS to intra-LibOS data loss without ever allowing it to steal an allocated block from Slot 1.

---

### 3. Layer 3 — Split Scoped/Allocation Stacks, Byte-Granular Typestate Rights, and API Integrity (`MiSFIT`, `Nooks`, `XFI`, `BGI`, `LXFI`)

**Basis:** `documentation` (Small & Seltzer USENIX COOTS 1997; Swift et al. SOSP 2003; Erlingsson et al. OSDI 2006 §§2–3; Castro et al. SOSP 2009 §§2–3; Mao et al. SOSP 2011 §§2–4) + `execution` + `derived` ([`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) `Layer3_XfiBgiLxfi`).

#### 3.1 Why Layer-1 SFI Fails on Intra-Sandbox Stack Return Addresses (`layer1_sfi_intra_sandbox_ret_overwrite`)
In Wahbe SFI, MiSFIT, and PittSFIeld, the execution stack resides inside the sandbox's writable data segment `[base, base + 2^k)`. Consequently, a linear buffer or array overflow inside the sandbox (`sfiStackStore s (arrBase + idx) attackerTarget`) satisfies the segment bounds check `(addr & mask) | base` and overwrites the saved return address on the stack (`retSlot`). When the function executes `ret`, even if the target is masked to an aligned 16-byte chunk inside the code segment, the attacker hijacks control flow to any chunk-aligned gadget or unintended function entry inside the module (`layer1_sfi_intra_sandbox_ret_overwrite`).

#### 3.2 XFI (OSDI 2006): Two-Region Memory Guards, Split `ScopedStack` / `AllocationStack`, and Inline CFI
Erlingsson et al. (*XFI: Software Guards for System Address Spaces*, OSDI 2006) close the intra-sandbox stack and control-flow vulnerabilities via three mechanisms:
1. **Two-Region Memory Protection (`mrguard(R, L, H)`):**
   - **Fastpath Contiguous Region `[A, B)`:** Checked inline by verifying `A + L ≤ R ≤ B - H` (computing `R - (A + L) ≤ (B - H) - (A + L)` via a single unsigned comparison + conditional trap `jc`). A static basic-block Hoare-logic verifier (`{P} i {Q}`) hoists checks across loops and constant-offset field accesses.
   - **Slowpath Fine-Grained Permission Table:** If the unsigned bounds check fails (`jc`), execution branches to a slowpath stub that consults a byte-granular permission table for non-contiguous host/kernel buffers granted to the module.
2. **Split `ScopedStack` vs. `AllocationStack` (`xfi_scoped_stack_immune_to_alloc_writes` & `xfi_call_write_ret_exact`):**
   - **`ScopedStack` (pointer `SSP`):** Holds return addresses, saved frame pointers, spilled registers, and non-address-taken locals. `SSP` may only be accessed via constant static offsets verified by the static verifier and is **never** passed as a computed pointer or reachable via `AllocationStack` stores.
   - **`AllocationStack` (pointer `ASP`):** Holds address-taken local variables and arrays whose pointers may be passed to subroutines.
   - Theorems `xfi_scoped_stack_immune_to_alloc_writes` and `xfi_call_write_ret_exact` prove that arbitrary computed-pointer writes to `AllocationStack` leave every `ScopedStackFrame` (and its `retAddr`) bit-for-bit identical.
3. **Inline Control-Flow Integrity (CFI):**
   Every computed branch or indirect call checks a 32-bit embedded equivalence-class ID (`prefetchnta <ID>`) placed immediately before the target instruction stream, while function returns pop their target directly from the uncorruptible `ScopedStack`.

#### 3.3 Nooks (SOSP 2003), BGI (SOSP 2009), and LXFI (SOSP 2011): Closing the In-Sandbox Kernel Object & Confused-Deputy API Gaps
Even with XFI's `ScopedStack` and CFI, isolating extensions inside a commodity monolithic kernel (Windows, Linux) encounters two structural obstacles proved in `xfi_confused_deputy_and_in_sandbox_object_corruption`:
- **Obstacle 1 — In-Sandbox Kernel Synchronization/Queue Objects (BGI §2 & §3.3):**
  In Windows and Linux, device drivers allocate kernel objects (`KEVENT`, `KDPC`, `KTIMER`, `spinlock_t`) **directly inside their own writable stack (`AllocationStack`) or module heap**. Once `KeInitializeEvent(&ev)` links `ev` into the kernel's global wait queue, `ev` still sits inside the driver's writable memory! A buggy driver can directly overwrite `ev`'s internal kernel list pointers (`flink`/`blink`) via an ordinary in-sandbox store, pass an uninitialized pointer as a `KEVENT*`, or free the stack frame / heap block while the kernel still holds active pointers to `ev`.
- **Obstacle 2 — Confused-Deputy Kernel Support Routines & Writable Callback Tables (LXFI §2):**
  Drivers invoke hundreds of kernel helpers (`spin_lock_init(ptr)`). Under XFI, if a module passes a pointer to a sensitive kernel field (`&current->cred->uid`) to `spin_lock_init(ptr)`, the trusted kernel zeroes `uid` on the module's behalf. Likewise, in CVE-2010-3904 (`RDS`), an unchecked write corrupted `rds_proto_ops.ioctl` inside the module's own writable data segment, hijacking subsequent core-kernel indirect calls through `ops->ioctl`.

How Nooks, BGI, and LXFI resolve these obstacles:
1. **Nooks (SOSP 2003 — Hardware Page Tables + XPC Object Tracker + Recovery Manager):**
   Nooks runs each Linux kernel extension in a lightweight **Extension Protection Domain (XPD)** using hardware page tables (kernel memory mapped read-only, extension memory read-write) switched via `CR3` on **Extension Procedure Calls (XPCs)**. An **Object Tracker** maintains a shadow hash table of kernel structures (`net_device`, `timer_list`, `page`) copied across the XPC boundary, and a **Recovery Manager** walks the Object Tracker on fault or timeout to release locks, untimer pending callbacks, free heap allocations, and reload the driver. Because every XPC crosses hardware page tables (`CR3` flush) and copies tracked objects, high-frequency drivers incur up to 54–62% CPU overhead.
2. **BGI (SOSP 2009 — 8-Byte Slot Table + Dynamic Typestate `SetType`/`CheckType` Revocation):**
   BGI replaces hardware page-table switches with a direct-mapped shadow table (1 byte of `<domain, right>` per 8-byte virtual memory slot, `12.5%` overhead, indexed via branchless bit rotation `sar eax, 3; btc eax, 0x1c`):
   - When a driver calls `KeInitializeEvent(p, ...)`, the BGI wrapper verifies that the driver has `<d, write>` on all slots of `*p` and executes **`SetType(p, sizeof(KEVENT), event)`**, changing the `dright` of the first slot of `*p` from `<d, write>` to **`<d, event>`** (and remaining slots to `<d, read>`).
   - Because `<d, event> ≠ <d, write>`, **the driver immediately loses direct byte-write permission to `*p` even though `*p` resides on the driver's own stack or heap** (`bgiDirectDriverStore_preserves_integrity`)!
   - Subsequent kernel calls (`KeSetEvent(p, ...)`) execute an inline `CheckType(p, event)` (`cmp byte ptr [table + (p >> 3)], <d, event>`), and stack/heap deallocation (`_BGI_slowRevokeAccess`, `ExFreePool`) traps if any slot still holds an active kernel object tag (`<d, dpc>`, `<d, timer>`) that was not properly destroyed via its kernel destructor.
3. **LXFI (SOSP 2011 — Multi-Principal Data-Structure Instances, Capability Proxies, and Writer-Set Tracking):**
   - **Data-Structure Principals (§2.3, §3.1):** Fine-grained runtime principals identified by kernel pointers (`principal(sk)` for `struct sock *sk`, `principal(dev)` for `struct net_device *dev`), tracked on a per-thread shadow stack with CFI-enforced direct-call declassifiers.
   - **Declarative API Capability Proxies (`WRITE`, `REF`, `CALL`, §2.2, §3.2):** Clang/LLVM generates API proxies that check `pre` capabilities in the active principal's table before invoking kernel routines (defeating `spin_lock_init(&current->cred->uid)`, proved in `bgiLxfiSpinLockInit_preserves_integrity`) and transfer transitive capabilities via capability iterators (`skb_caps(skb)`).
   - **Writer-Set Tracking for Core-Kernel Indirect Calls (§3.3):** When a module writes to a memory region `M` (such as `rds_proto_ops`), LXFI records the active principal in `M`'s **writer set**. Before the core kernel executes an indirect call through `*fp` in `M`, `lxfi_check_indcall` verifies that every principal in `M`'s writer set holds `CALL(*fp)`—defeating CVE-2010-3904 even though `rds_proto_ops` sits in the module's own writable data segment.

---

### 4. Layer 4 — Kernel Extension Abort, Timeout, and Cancellation Recovery (Four-Way Architectural Comparison)

**Basis:** `documentation` (Seltzer et al. OSDI 1996 §3; Swift et al. SOSP 2003 §3.4) + `source` (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` `trusted/lean/Trusted/Refinement.lean`) + `execution` + `derived` ([`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) `Layer4_VinoTransactionalGrafts`).

#### 4.1 Why Layers 1–3 Fail Under Mid-Operation Extension Abort (`sfi_cfi_api_abort_without_undo_deadlocks_and_corrupts`)
Suppose a kernel extension (a VINO "graft" or driver callback) satisfies Layer 1 (memory confinement), Layer 2 (bounded instruction fuel), and Layer 3 (CFI + capability-checked kernel helper calls). During execution, the extension legitimately calls a kernel helper to acquire a shared kernel lock (`AcquireLock 1`) and updates the first half of a paired kernel invariant (`AddPrimary 50`, leaving `primaryTable = 150 ≠ shadowAccounting = 100`), and then aborts—either because a subsequent memory access faults on an unmapped guard page (`#PF`) or because its instruction/time budget expires (`fuel = 0`).

As proved in `sfi_cfi_api_abort_without_undo_deadlocks_and_corrupts`, if the kernel simply terminates the extension without rolling back its legitimate kernel mutations, the kernel is left with **leaked locks (`lockHeld 1 = true`, permanently deadlocking the subsystem)** and **corrupted shared state (`primaryTable ≠ shadowAccounting`)**.

#### 4.2 Four-Way Comparison of Kernel Extension Abort / Timeout Recovery Modes
In [`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) (`Layer4_VinoTransactionalGrafts`, Section 4.2), we formalize and prove the exact post-fault / post-timeout behavior of the four architectural recovery modes (`four_mode_extension_recovery_comparison`):

| Recovery Mode | Representative Systems | Fault / Timeout Mechanism | Post-Abort Lock State (`lockHeld l`) | Post-Abort Shared State (`primaryTable = shadowAccounting`) | Mechanized Theorem in [`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Mode A:** Non-unwinding trap kill | Nebulet (`pfex_acquire` $\to$ `#PF` $\to$ `Thread::exit()`), raw SFI/MiSFIT without undo | Trap handler terminates faulting thread directly without unwinding stack frames or running undo log | **Leaked (`true`)** — permanent kernel deadlock | **Corrupted (`primaryTable ≠ shadowAccounting`)** | `modeA_trap_kill_leaks_lock` |
| **Mode B1:** Exception-table landing pad + RAII `Drop` (*check-before-mutate*) | Linux `__ex_table` (`copy_from_user`) + Rust `Guard` `Drop` / C cleanup `goto` | Trap handler redirects `RIP` to landing pad returning `Err(EFAULT)` *before* shared state mutation; RAII `Drop` releases lock `l` | **Released (`false`)** | **Consistent (`Quiescent`)** | `modeB_check_before_mutate_always_quiescent` |
| **Mode B2:** Exception-table landing pad + RAII `Drop` (*mutate-before-fault*) | Multi-step kernel mutation where fault occurs after Step 1 (`primaryTable += delta`) | Landing pad + RAII `Drop` releases lock `l`, but local stack `Drop` has no record of heap/global mutations already committed | **Released (`false`)** | **Corrupted (`primaryTable ≠ shadowAccounting`)** | `modeB_mutate_before_fault_releases_lock_but_corrupts_state` |
| **Mode C:** Dynamic LIFO compensating `undoStack` + 2PL | VINO (`OSDI 1996`, Seltzer et al. §3.2) | Every mutator pushes an inverse action (`SubPrimary`, `ReleaseLock`) onto `undoStack`; any `#PF` or asynchronous watchdog timeout (`fuel = 0`) executes `vinoRollback` in LIFO order | **Released (`false`)** | **Restored (`Quiescent`)** across both `#PF` and watchdog timeout | `modeC_vino_always_quiescent`, `vino_transaction_abort_restores_quiescent_invariant` |
| **Mode D:** Static exceptionless + bounded-resource admission | `Typechain` (`PLAS 2020`), Anneal (`SafeProgram.terminates` + `Refines`), verified eBPF | Compile-time `StaticAdmissionCert` proves `addr < memBound` (`Exceptionless`) and `0 < fuel` (`ResourceBounded`), eliminating runtime traps and timeouts altogether (`aborted = false`) | **Released (`false`)** | **Consistent (`Quiescent`)** with zero runtime undo-log overhead | `modeD_static_admission_never_aborts_and_quiescent` |

- **Why VINO Uses Compensating Functions Rather Than Raw Page Undo (Seltzer et al. §3.2):**
  Because kernel resources (locks, buffer-cache slots, allocated memory, network packets) are shared across concurrent kernel threads, rolling back raw physical memory bytes would clobber concurrent allocations made by other threads unless the extension locked entire allocator arenas. Instead, VINO wraps every kernel mutator $m$ callable by a graft with an inverse compensating function $m^{-1}$ pushed onto a LIFO undo stack (`applyUndo_applyMutator_cancel`, `vinoRollback_execTrace_exact`), holds acquired locks until transaction termination (strict two-phase locking so no other thread observes uncommitted graft state), and preempts grafts that hoard locks beyond a resource time-out quantum.

---

### 5. Structural Correspondence to Anneal (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`)

**Basis:** `source` (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` `README.md`, `PRINCIPLES.md`, `trusted/audit/src/lib.rs`, `trusted/lean/Trusted/Attributes.lean`, `trusted/lean/Trusted/Refinement.lean`) + `derived`.

Inspecting Anneal's source tree reveals a direct mapping between the 1993–2011 runtime SFI/kernel-extension hierarchy and Anneal's compile-time verification architecture:

| Runtime SFI / Kernel Mechanism (1993–2011) | Failure Mode Addressed | Anneal Compile-Time Equivalent (`joshlf/anneal@e6a0b2da5ec3`) |
| :--- | :--- | :--- |
| **Layer 1: Wahbe SFI / PittSFIeld / XFI `mrguard` & `ScopedStack`** | Out-of-bounds memory reads/writes, stack-frame return-address corruption, unaligned mid-instruction jumps | **Safe Rust + `#[anneal::trusted]` Audit (`trusted/audit/src/lib.rs`):** Safe Rust's affine borrow checker and bounds checking statically eliminate arbitrary pointer arithmetic, buffer overflows, and stack frame corruption; `cargo anneal audit` flags every `unsafe` block and `#[anneal::trusted]` item as an explicit verification obligation. |
| **Layer 2: Exokernel ASH Loop Counters & XN `INST_BUDGET` + Deterministic UDFs** | Non-termination in kernel handlers; nondeterministic/stateful metadata ownership spoofing | **Pure Functional LLBC Translation + `SafeProgram.terminates` (`trusted/lean/Trusted/Refinement.lean:45`):** Aeneas compiles Rust functions into pure, deterministic mathematical functions in Lean 4; `SafeProgram.terminates : ∀ s, ∃ s', step s = some s'` statically proves total termination without runtime fuel counters. |
| **Layer 3: BGI `SetType`/`CheckType` & LXFI `WRITE`/`REF`/`CALL` Capabilities** | In-sandbox kernel object corruption, typestate violations, confused-deputy kernel API calls | **Rust Affine Type Ownership + Anneal `isValid` & `precondition`/`postcondition` (`trusted/lean/Trusted/Attributes.lean`):** Rust's type system encapsulates private kernel fields and linear/affine typestates at zero runtime cost (vs. BGI's 12.5% shadow table), while Anneal's `isValid` type invariants and `requires`/`ensures` clauses verify semantic API contracts statically. |
| **Layer 4: VINO Compensating Undo-Log Transactions (Mode C)** | Partial state mutation or leaked locks when an extension faults/aborts mid-operation | **Mode D Static Admission (`SafeProgram.terminates` + `Refines` in `trusted/lean/Trusted/Refinement.lean:51–56`):** Because Anneal proves `SafeProgram.terminates` (implying `Result.ok` totality / no mid-execution panics or aborts) and proves `Refines` (`∀ s, R s a → ∃ a', AbsStep a a' ∧ R (cStep s) a'`), verified transitions cannot abort mid-mutation and therefore require no runtime undo log. |

---

## Boundaries

1. **Hardware MMU / MPK / Virtualization Isolation (`not examined`):**
   This report focuses on software-enforced fault isolation, capability-mediated API proxies, and software transactional recovery (plus Nooks's hybrid `CR3` XPD model as the historical baseline for XFI/BGI/LXFI). Hardware virtualization (`VT-x`, `SVM`), Extended Page Tables (`EPT`), ARM Pointer Authentication (`PAC`), and Intel Memory Protection Keys (`MPK`/`PKRU`) were **not examined** here.
2. **Original VINO, MiSFIT, XFI, BGI, and LXFI Source Trees (`unknown` / `not examined`):**
   While we directly inspected the primary source trees for PittSFIeld (`pittsfield-0.7.tar.gz`, `pittsfield-proof-2009-10-30.tar.gz`), Exokernel/XOK (`pdos/xok@490cd2496ebbd2b4032c191a036c5711d118e3b9`), DPF (`dpf.tar.gz`), and Anneal (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`), the proprietary Microsoft Research implementations of XFI and BGI (built on the Phoenix compiler and Windows kernel) and the Harvard VINO/MiSFIT and MIT LXFI source trees were **not examined** directly; findings for those systems are grounded in their published SOSP/OSDI/USENIX papers (`documentation`) and our mechanized Lean 4 models (`execution` + `derived`).
3. **Differential Determinism Does Not Verify Intra-LibOS Semantic Correctness (`known not to apply`):**
   As proved in `xn_differential_determinism_intra_libos_boundary` in [`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean), XOK's `XN` differential determinism check (`udf_alloc`/`udf_write`/`udf_dealloc` around a pure `owns-udf_T`) is **known not to apply** to intra-LibOS semantic correctness: if a LibOS supplies a buggy `owns-udf_T` whose computed block set disagrees with the LibOS's own user-space file reader, the LibOS can corrupt or lose its own blocks without violating global inter-LibOS block disjointness.
4. **Exception-Table Landing Pads + Stack RAII `Drop` Do Not Roll Back Committed Shared-State Mutations (`known not to apply`):**
   As proved in `modeB_mutate_before_fault_releases_lock_but_corrupts_state`, redirecting a kernel page fault via `__ex_table` to a stack-unwinding landing pad (`Err(EFAULT)`) with RAII `Drop` lock guards is **known not to apply** when shared kernel state has already been mutated prior to the faulting access (`mutate-before-fault`) or when an extension is preempted asynchronously mid-mutation without an undo log (Mode C) or static exceptionless admission certificate (Mode D).
5. **Speculative Execution Side Channels (`unsupported`):**
   The 1993–2011 SFI architectures examined here model architectural instruction execution only; protection against transient speculative execution attacks (Spectre/Meltdown bypassing bitwise masks or branch conditions in the speculative window) is **unsupported** by these classical SFI designs without additional speculative fence or index-masking transformations.

---

## Evidence

### 1. Primary Publications (`documentation`)
- **Wahbe et al. (SOSP 1993):** Robert Wahbe, Steven Lucco, Thomas E. Anderson, and Susan L. Graham, *"Efficient Software-Based Fault Isolation,"* SOSP 1993, pp. 203–216, DOI `10.1145/168619.168635` (PDF SHA-256 `0a90c74469b5f9d91df78c526be289979caafe94be3f8594e54980a340cb367b`).
- **McCamant & Morrisett (USENIX Security 2006 / PittSFIeld):** Stephen McCamant and Greg Morrisett, *"Evaluating SFI for a CISC Architecture,"* 15th USENIX Security Symposium, 2006 (PDF SHA-256 `a315f62e6911a3a8203ee03964e9717905ab6b8793ac8d0f81e187d1f2cfd770`); extended technical report MIT-CSAIL-TR-2005-067 (SHA-256 `f84a2fa4067fe22acfccff50c22b68cbb486c7332cdac382fdc13d52add2d16a`) and ACL2 proof report MIT-CSAIL-TR-2006-035 (SHA-256 `36541cf6f37db9cf8ad99e0da27832159ffd4705c56d97c40f3996a5fcb1f1dc`).
- **Engler, Kaashoek & O'Toole (SOSP 1995 / Exokernel):** Dawson R. Engler, M. Frans Kaashoek, and James O'Toole Jr., *"Exokernel: An Operating System Architecture for Application-Level Resource Management,"* SOSP 1995, pp. 251–266, DOI `10.1145/224056.224076` (PDF SHA-256 `1f7d1ab466e0c7041b25083628637b61a65400a1b9834c82ab38d28ccbc8a0e9`).
- **Wallach, Engler & Kaashoek (SIGCOMM 1996 / ASH):** Deborah A. Wallach, Dawson R. Engler, and M. Frans Kaashoek, *"ASHs: Application-Specific Handlers for High-Performance Messaging,"* SIGCOMM 1996, pp. 40–52, DOI `10.1145/248156.248161` (PDF SHA-256 `00d1904f69f53e4101ffab91a15f4679edc37c3a9142df98c0c3c70b64fb39fe`).
- **Engler & Kaashoek (SIGCOMM 1996 / DPF):** Dawson R. Engler and M. Frans Kaashoek, *"DPF: Fast, Flexible Message Demultiplexing using Dynamic Code Generation,"* SIGCOMM 1996, pp. 53–59, DOI `10.1145/248156.248162` (PDF SHA-256 `85277b0223647be89d8823d2ad0fca58b4966f4bad5ad1f69fc72b1f378b7f47`).
- **Kaashoek et al. (SOSP 1997 / XOK & XN):** M. Frans Kaashoek, Dawson R. Engler, Gregory R. Ganger, Héctor M. Briceño, Russell Hunt, David Mazières, Thomas Pinckney, Robert Grimm, John Jannotti, and Kenneth Mackenzie, *"Application Performance and Flexibility on Exokernel Systems,"* SOSP 1997, pp. 52–65, DOI `10.1145/268998.266644` (PDF SHA-256 `e9b7b77188f333da5725151db7900bddc9cab5fa3489b0b238726bfb329ea98e`).
- **Seltzer et al. (OSDI 1996 / VINO):** Margo I. Seltzer, Yasuhiro Endo, Christopher Small, and Keith A. Smith, *"Dealing With Disaster: Surviving Misbehaving Kernel Extensions,"* OSDI 1996, pp. 213–227, DOI `10.1145/238721.238779` (PDF SHA-256 `71ce26d61d7513fcad22278c6824c12971014864c3574d310f966123ca16b27c`).
- **Small & Seltzer (USENIX COOTS 1997 / MiSFIT):** Christopher Small, *"MiSFIT: A Tool for Constructing Safe Extensible C++ Systems,"* USENIX COOTS 1997 (PDF SHA-256 `a73d7a340b49f7d0bb4e2b710433ef8d93e59028aa1047cbef039f2d884bb126`).
- **Swift, Bershad & Levy (SOSP 2003 / Nooks):** Michael M. Swift, Brian N. Bershad, and Henry M. Levy, *"Improving the Reliability of Commodity Operating Systems,"* SOSP 2003, pp. 207–222, DOI `10.1145/945445.945466` (PDF SHA-256 `2e3bb82bba1668e6668d3f1f654d7663e03d70ff2a28c4ce941d7be996ff5efb`).
- **Erlingsson et al. (OSDI 2006 / XFI):** Úlfar Erlingsson, Martín Abadi, Michael Vrable, Mihai Budiu, and George C. Necula, *"XFI: Software Guards for System Address Spaces,"* OSDI 2006, pp. 75–88 (PDF SHA-256 `3bf476041fd12b3bd00f17d88caa06ecaf7ff41498761f5b1e39f555f094b981`).
- **Castro et al. (SOSP 2009 / BGI):** Miguel Castro, Manuel Costa, Jean-Philippe Martin, Marcus Peinado, Periklis Akritidis, Austin Donnelly, Paul Barham, and Richard Black, *"Fast Byte-Granularity Software Fault Isolation,"* SOSP 2009, pp. 45–58, DOI `10.1145/1629575.1629581` (PDF SHA-256 `e52566208e8ea7bb8074f5fea67b5480ec381d1cf19c8ada55e111b75e3a16ad`).
- **Mao et al. (SOSP 2011 / LXFI):** Yandong Mao, Haogang Chen, Dong Zhou, Xi Wang, Nickolai Zeldovich, and M. Frans Kaashoek, *"Software Fault Isolation with API Integrity and Multi-Principal Modules,"* SOSP 2011, pp. 115–128, DOI `10.1145/2043556.2043568` (PDF SHA-256 `2a5e520a4d77fd03f85732deed039ead2a6b25980d38583400e270361ed332d4`).

### 2. Primary Source Repositories and Historical Archives (`source` / `normative`)
- **PittSFIeld 0.7 & ACL2 Proof (`pittsfield-0.7.tar.gz`, SHA-256 `4f127e246c6f8539854c4a40230e535897848b8295d72aa93db0064a09619dea`; `pittsfield-proof-2009-10-30.tar.gz`, SHA-256 `6dac51fc4605d29f7143b41fd6a7af91d17b6e7dcb07a76f01894cccd1aa6ca1`):**
  - `sfi.pl:91–260` (rewriter emitting 16-byte chunk padding, `%ebx` sandboxing, and `--pop-ret` vs. in-place `(%esp)` return masking);
  - `verify.pl:71–245` (standalone static verifier enforcing `chunk_size = 16` alignment and `%ebx` state transitions);
  - `sfi.lisp:186–295` (ACL2 formalization of `verify-insn-list` and main safety theorem `run-safe-from-verify`).
- **MIT PDOS XOK / Exokernel (`pdos/xok@490cd2496ebbd2b4032c191a036c5711d118e3b9` & `exopc-06-22-2000.tar.gz`, SHA-256 `18a9bdfb7283424c303af4c3cb5aacc8dc17fb0a2f6fa9e19ecfb90a428228a4`):**
  - `src/exopc/sys/ubb/ubs.h:1–160` (`INST_BUDGET = 100`, `XN_NREGS = 16`, 37 pseudo-RISC opcodes `UBI_*`);
  - `src/exopc/sys/ubb/check.c:106–185` (`udf_check`, `check_inst`, `check_op`);
  - `src/exopc/sys/ubb/interp.c:56–215` (`udf_interp`, `check_addr`, `UBI_ADD_CEXT`);
  - `src/exopc/sys/ubb/udf.c:204–335` (`udf_alloc`, `udf_write`, `udf_dealloc`, `udf_run`, `udf_rollback`);
  - `src/exopc/sys/kern/scode.c:1–295` (`scode_CheckProg`, `scode_instrument_branches`).
- **MIT PDOS Dynamic Packet Filter (`dpf.tar.gz`, SHA-256 `862c2a870249e230d68c131d5237ee74c3f70248cd6c9d2a5ff12168d614364b`):**
  - `src/dpf/{tree.c,optimize.c,gen.c,ir.c}` (`coalesce_atoms`, `or_insert`, `check_shifts`).
- **Anneal (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`):**
  - `trusted/audit/src/lib.rs` (static scanner rejecting unapproved `unsafe` and auditing `#[anneal::trusted]`);
  - `trusted/lean/Trusted/Attributes.lean` (`isValid`, `precondition`, `postcondition`, `spec`);
  - `trusted/lean/Trusted/Refinement.lean:44–56` (`SafeProgram.terminates`, `Refines`).

### 3. Preserved Lean 4.34.1 Mechanization (`execution` + `derived`)
- **[`support/FoundationalSfiKernels.lean`](support/FoundationalSfiKernels.lean)** (2,246 lines, SHA-256 `7e9e20a3e18ef9a7c11cecadc7db1f8e33d39dff55a0bb0c43d7b3d1582f1c18`):
  Verified with Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) on `2026-11-02`. Every theorem prints its axiom footprint via `#print axioms` at the bottom of the file, confirming dependence exclusively on `[propext, Quot.sound]` (or `[]` — zero axioms), with `0 sorryAx`, `0 Classical.choice`, and `0 Lean.ofReduceBool`.

---

## Revalidation

1. **Re-verify the Preserved Lean 4.34.1 Mechanization (`support/FoundationalSfiKernels.lean`):**
   Run the Lean `v4.34.1` compiler directly on the preserved support file:
   ```bash
   lean reports/sfi-foundational-extensible-kernels-1993-2011/support/FoundationalSfiKernels.lean
   ```
   Confirm that the command exits with status `0`, emits zero warnings, and that the `#print axioms` output for all 40 theorems lists only `[propext, Quot.sound]` or `does not depend on any axioms` (never `sorryAx`, `Classical.choice`, or `Lean.ofReduceBool`).
2. **Re-check XOK `XN` Differential Determinism and ASH Sandboxing in `pdos/xok`:**
   If comparing against another revision of `pdos/xok`, diff `src/exopc/sys/ubb/{ubs.h,check.c,interp.c,udf.c}` and `src/exopc/sys/kern/scode.c` against commit `490cd2496ebbd2b4032c191a036c5711d118e3b9`. Check whether `INST_BUDGET`, `udf_check`'s opcode whitelist, `check_addr`'s metadata-block confinement, or the `set_Sub`/`set_eq` checks in `udf_alloc`/`udf_write`/`udf_dealloc` have changed.
3. **Re-check Anneal's Static Admission Obligations (`joshlf/anneal`):**
   If Anneal's `trusted/lean/Trusted/Refinement.lean` or `trusted/audit/src/lib.rs` changes from commit `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`, inspect whether `SafeProgram.terminates` still requires total transition steps (`∀ s, ∃ s', step s = some s'`) and whether `Refines` still enforces lock-step abstract state simulation without partial-mutation abort paths.
