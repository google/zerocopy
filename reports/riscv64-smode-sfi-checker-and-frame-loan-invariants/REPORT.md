# RISC-V S-Mode Single-Pass `RV64IM` SFI Checker, Hook Noninterference, and Zero-Copy Frame-Loan Invariants

## Summary

1. **A native S-mode `RV64IM` kernel extension can be admitted by a stateless, certificate-free, single-pass checker with a kernel-checked soundness proof.** [`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean) (`safe_and_terminates`, `never_traps`, `words_safe_and_terminate`) proves that an admitted instruction stream entered under a nine-clause kernel trampoline contract returns to the caller's `ra` within at most `N` instructions (`N` = module length), raises no synchronous exception, preserves every register outside eleven temporaries and two dedicated scratch-addressing registers, and leaves every byte outside two sandbox regions unchanged. No per-instruction certificate, dominance tree, or dataflow analysis is required: termination follows from strictly forward branches, and memory safety follows from two dedicated registers (`x6`/`x7`) whose invariants hold at every instruction boundary.
2. **Six SFI side conditions are individually necessary, each backed by a mechanized separating witness in [`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean):** non-negative raw load/store immediate (`neg_imm_reads_below_region`: `ld t0, -8(a0)` is naturally aligned, raises no trap, and reads a secret byte planted below the context region), natural alignment (`misaligned_load_traps`), region upper bound (`overrun_rejected`), non-negative 8-aligned `andi` mask (`neg_mask_does_not_bound`: a negative immediate sign-extends and aligns without bounding, so one `andi` can bound an index to at most `2047`), `jalr` restricted to `ret` (`computed_jalr_escapes`), and strictly forward branches (`self_branch_never_returns`).
3. **Unaligned `ld`/`sd` in S-mode does *not* raise an S-mode address-misaligned exception on QEMU TCG or OpenSBI firmware.** The RISC-V Unprivileged ISA makes misaligned access behavior EEI-dependent; QEMU `v10.0.0` TCG emits plain loads and stores without `MO_ALIGN` (requesting alignment only for `LR`/`SC`/`AMO`); OpenSBI omits `CAUSE_MISALIGNED_LOAD`, `CAUSE_MISALIGNED_STORE`, and `CAUSE_ILLEGAL_INSTRUCTION` from `medeleg` and emulates misaligned accesses in M-mode. A misaligned extension access is therefore silent under `qemu-system-riscv64 -M virt` and incurs unbounded-latency M-mode emulation on trapping silicon. Static natural alignment enforcement is mandatory, and **QEMU execution tests cannot detect missing alignment checks**.
4. **`RV64M` division and remainder never trap, and Lean 4 core's `BitVec.sdiv`/`BitVec.smtSDiv` disagree with `RV64M` `div` on negative dividends divided by zero.** All eight `RV64M` divide/remainder instructions (`div`, `divu`, `rem`, `remu`, `divw`, `divuw`, `remw`, `remuw`) are total with fixed by-zero and signed-overflow results, so an SFI checker needs no operand guard for trap freedom (`demoProg_safe`). However, in Lean `v4.34.1`, `BitVec.smtSDiv (-1#64) 0#64 = 1#64` and `BitVec.sdiv (-1#64) 0#64 = 0#64`, whereas `RV64M` `div` returns all ones (`0xffff_ffff_ffff_ffff`) for every dividend (`lean_sdiv_differs_from_rv64m_div`). Conversely, lowering source languages whose division traps on zero or signed overflow must preserve explicit guards because hardware will not trap.
5. **An admitted module is a function of its temporaries and sandbox bytes only (`sandbox_noninterference`), and hook activation preserves two-domain noninterference for every module iff the hook fires in its owning domain's context ([`support/HookNoninterference.lean`](support/HookNoninterference.lean)).** Confidentiality requires barring reserved registers (`ra`, `sp`, `gp`, `tp`, `s0`–`s11`, `a0`, `a1`, `t2`) as *data operands* (not only as destinations) and scrubbing all eleven temporaries on trampoline entry (`unscrubbed_temp_leaks`). Cross-domain hook activation leaks in both directions—through the verdict (`cross_domain_verdict_leaks`), execution time (`cross_domain_time_leaks`), and persistent scratch (`cross_domain_scratch_absorbs`). Moreover, seL4's information-flow proof (`seL4/l4v`, `domain_sep_inv`) assumes no `IRQHandlerCap` exists at all when non-timer IRQs are disabled, placing interrupt-attached hooks outside that proof's standing envelope.
6. **Zero-copy `LoanFrame` semantics is safe under seven independent kernel decisions and unsafe if any single one is omitted ([`support/LoanRingPin.lean`](support/LoanRingPin.lean), Part A, exhaustively kernel-checked over all 11,664 abstract states × 18 events).** Storing loan state out of line per frame with a loan token linked from the `Reply` object makes reply, `Reply` destruction, and frame revocation constant-size updates. Two easily missed requirements are a constant-time uniqueness witness at loan start (`need_uniqueCheck`) and refusing new mappings while a loan is active (`need_mapGuard`).
7. **Reading a user-shared ring entry twice is unsound under concurrent modification; copying once into kernel-private storage is sound ([`support/LoanRingPin.lean`](support/LoanRingPin.lean), Part B: `doubleFetch_out_of_bounds`, `copyOnce_in_bounds`, `batch_bounded`).** Proving TOCTOU freedom requires a verification semantics in which each read from user-writable memory is an independent nondeterministic event; any deterministic memory model equates repeated fetches by construction and cannot even state the bug.
8. **Loans, asynchronous I/O rings, and loaded kernel-module code/scratch frames can share a single per-frame pin (`pin : Option Holder`) with mandatory revocation notification ([`support/LoanRingPin.lean`](support/LoanRingPin.lean), Part C: `pin_safe`, `need_revoke_notification`).**

## Applicability

This report characterizes the interaction of six durable upstream subjects observed on `2026-11-19`:

- **RISC-V ISA Manual** (`riscv/riscv-isa-manual@5f1104a0613af80219232b1e4bc108f9ec2bd6b2`) — normative rules for `RV64IM` unprivileged instructions (`IALIGN = 32`, no `C` compressed extension, no FPU), `M`-extension division/remainder, `Zifencei` (`fence.i`), and supervisor-mode `sfence.vma` / address-translation caching.
- **QEMU** (`qemu/qemu@7c949c53e936aa3a658d84ab53bae5cadaa5d59c`, `v10.0.0`) — RISC-V TCG translation front end for load/store alignment flags and unaligned-access exception generation.
- **OpenSBI** (`riscv-software-src/opensbi@ed70256dd22c09962d146e433834239825ef0616`) — M-mode `medeleg` trap delegation and software emulation of misaligned loads and stores.
- **seL4 Microkernel** (`seL4/seL4@08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`) — RISC-V 64-bit `unmapPage` target-checking pattern, `sfence.vma` helpers, and per-capability frame mapping representation.
- **seL4 Verification (`l4v`)** (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`) — Isabelle/HOL `domain_sep_inv` standing assumption used in the kernel noninterference proof.
- **Lean 4** (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, `x86_64-unknown-linux-gnu`) — kernel proof checker for the three standalone support models and the exact `BitVec.sdiv` / `BitVec.smtSDiv` edge-case behavior.

**Target execution regime.** Findings apply to single-hart `RV64IM_Zicsr_Zifencei` S-mode kernels without compressed instructions (`IALIGN = 32`), without hardware FPU use in extensions, and without a microarchitectural cache-timing model. This complements prior corpus studies of x86-64 and AArch64 SFI/LFI verifiers (which left RISC-V SFI unexamined) by providing a self-contained, kernel-checked `RV64IM` S-mode SFI model and companion kernel-resource invariants.

**Scope of mechanized support files.** The three files under [`support/`](support/) use Lean 4 core only (no Mathlib, no `sorry`, no custom `axiom`, no `native_decide`, no `bv_decide`). They model: (1) a 19-operation `RV64IM` fragment over flat byte memory without address translation ([`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean)); (2) a two-domain abstract kernel with hook activations ([`support/HookNoninterference.lean`](support/HookNoninterference.lean)); and (3) a nine-field finite state machine for a loaned frame, a nondeterministic user-shared submission queue, and a four-holder per-frame pin ([`support/LoanRingPin.lean`](support/LoanRingPin.lean)). Transfer from these abstract models to a concrete kernel implementation depends on the refinement obligations documented in **Boundaries**.

## Findings

### 1. Stateless Single-Pass `RV64IM` S-Mode SFI Checker

#### 1.1 Machine Model, Register Discipline, and Admission Predicate

`Basis: execution (Lean kernel) + derived`

In [`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean) (namespace `SmodeSfiChecker`), machine state `St` is `(pc : Nat, regs : Nat → Nat, mem : Nat → Nat)` where `pc` is a byte offset from the module's load address (64-bit modular arithmetic is translation-invariant, so relative and absolute program counters step identically). The hardware model provides no confinement around S-mode execution: every address in `mem` is readable and writable, fetching outside `[0, 4 * prog.length)` yields `Trap.pcOutside`, `SYSTEM`-opcode instructions yield `Trap.privileged`, unmodeled encodings yield `Trap.illegal`, and `jalr` exits the module to an arbitrary target via `Out.ret target s`. Immediates are stored as raw encoded bit fields (`imm12 < 4096`, `off13 < 8192`, `off21 < 2^21`) and sign-extended by `sext12`, `sextB`, and `sextJ` during execution, matching hardware.

The checker partitions the 32 integer registers into fixed roles enforced statically at every instruction:

| Register(s) | Role | Permitted writers | Readable as data operand (`CanRead`) |
| --- | --- | --- | --- |
| `x0` | hardwired zero | ignored (`wrReg_zero`) | yes |
| `x1` (`ra`) | caller return address | never | no (permitted only as base of `jalr x0, 0(x1)`) |
| `x10` (`a0`) | context region base | never | no (permitted only as load/store base) |
| `x11` (`a1`) | scratch region base | never | no (permitted only as `rs1` in `add x7, x11, x6`) |
| `x6` (`t1`) | bounded, 8-aligned scratch index | only `andi x6, rs1, imm` (`imm < 2048 ∧ imm ≤ idxMask ∧ imm % 8 = 0`) | yes |
| `x7` (`t2`) | confined scratch address | only `add x7, x11, x6` | no (permitted only as load/store base) |
| `x5`, `x12`–`x17`, `x28`–`x31` | 11 temporaries (`IsTemp`) | any admitted ALU, `lui`, or load | yes |
| `x2`–`x4`, `x8`, `x9`, `x18`–`x27` | `sp`, `gp`, `tp`, `s0`–`s11` | never | no |

The per-instruction predicate `OkInstr cfg n i ins` inspects one decoded instruction at word index `i` of a module of length `n`, parameterized only by policy `cfg = { ctxBytes, scrBytes, idxMask }` (`SmodeSfiChecker.lean:243-290`):

```text
aluI   f rd rs1 imm    : i + 1 < n ∧ CanRead rs1 ∧
                         (IsTemp rd ∨ (rd = 6 ∧ f = .and ∧ imm < 2048 ∧ imm ≤ idxMask ∧ imm % 8 = 0))
alu3   f rd rs1 rs2    : i + 1 < n ∧
                         ((IsTemp rd ∧ CanRead rs1 ∧ CanRead rs2) ∨ (f = .add ∧ rd = 7 ∧ rs1 = 11 ∧ rs2 = 6))
lui    rd _            : i + 1 < n ∧ IsTemp rd
load   w _ rd rs1 imm  : i + 1 < n ∧ IsTemp rd   ∧ AddrOk cfg w rs1 imm
store  w rs2 rs1 imm   : i + 1 < n ∧ CanRead rs2 ∧ AddrOk cfg w rs1 imm
branch _ rs1 rs2 off   : i + 1 < n ∧ CanRead rs1 ∧ CanRead rs2 ∧
                         0 < off ∧ off < 4096 ∧ off % 4 = 0 ∧ i + off / 4 < n
jal    rd off          : rd = 0 ∧ 0 < off ∧ off < 2^20 ∧ off % 4 = 0 ∧ i + off / 4 < n
jalr   rd rs1 imm      : rd = 0 ∧ rs1 = 1 ∧ imm = 0
system _ | other _     : False

AddrOk cfg w rs1 imm :=
  w ∈ {1, 2, 4, 8} ∧ imm < 2048 ∧ imm % w = 0 ∧
  ((rs1 = 10 ∧ imm + w ≤ cfg.ctxBytes) ∨ (rs1 = 7 ∧ cfg.idxMask + imm + w ≤ cfg.scrBytes))
```

`check cfg prog` additionally enforces `0 < prog.length ≤ 2^20` and `cfg.idxMask + 8 ≤ cfg.scrBytes` (`SmodeSfiChecker.lean:302-304`), and `checkWords cfg ws := check cfg (ws.map decode)` composes the allow-list 32-bit word decoder (`SmodeSfiChecker.lean:1032-1093`) with `check`. The checker keeps no inter-instruction state and consumes no certificate.

#### 1.2 Kernel Entry Contract and Main Soundness Theorems

`Basis: execution (Lean kernel) + derived`

The kernel trampoline must establish `Entry cfg s0` (`SmodeSfiChecker.lean:335-344`), a nine-clause entry contract:

1. `s0.pc = 0` (start at instruction 0);
2. `s0.regs 10 % 8 = 0` and `s0.regs 10 + cfg.ctxBytes ≤ 2^64` (8-aligned non-wrapping context region);
3. `s0.regs 11 % 8 = 0` and `s0.regs 11 + cfg.scrBytes ≤ 2^64` (8-aligned non-wrapping scratch region);
4. `s0.regs 6 ≤ cfg.idxMask ∧ s0.regs 6 % 8 = 0` (trampoline initializes `x6 := 0`);
5. `∃ k, k ≤ cfg.idxMask ∧ k % 8 = 0 ∧ s0.regs 7 = s0.regs 11 + k` (trampoline initializes `x7 := x11`);
6. `s0.regs 1 % 4 = 0` and `s0.regs 1 < 2^64` (4-byte-aligned return address in `ra`).

Under `Entry cfg s0`, the six-field inductive invariant `Inv cfg n s0 s` (`SmodeSfiChecker.lean:352-358`: 4-aligned in-range `pc`, all registers outside `IsTemp ∪ {6, 7}` equal to `s0`, `x6` bounded and 8-aligned, `x7 = s0.regs 11 + k` for an admissible `k`, and every byte outside `InSandbox cfg s0` unchanged) is preserved by `exec_ok` (`:461-555`) with strictly increasing `pc` on every non-returning step, yielding:

```text
safe_and_terminates :
  check cfg prog = true → Entry cfg s0 →
  ∃ k s', k ≤ prog.length ∧ run prog k s0 = .ret (s0.regs 1) s' ∧ Returned cfg s0 s'
  -- Returned: (∀ r, ¬IsTemp r → r ≠ 6 → r ≠ 7 → s'.regs r = s0.regs r) ∧
  --           (∀ a, ¬InSandbox cfg s0 a → s'.mem a = s0.mem a)

never_traps :
  check cfg prog = true → Entry cfg s0 → Inv cfg prog.length s0 s → ∀ k t, run prog k s ≠ .trap t

words_safe_and_terminate :
  checkWords cfg ws = true → Entry cfg s0 →
  ∃ k s', k ≤ ws.length ∧ run (ws.map decode) k s0 = .ret (s0.regs 1) s' ∧ Returned cfg s0 s'
```

**Why dedicated registers eliminate dominance and dataflow analysis.** Because `x6` is writable only by an admissible `andi` and `x7` only by `add x7, x11, x6`, the invariants `x6 ≤ idxMask ∧ x6 % 8 = 0` and `x7 = scratchBase + k` hold at **every** instruction boundary. Consequently, any `load`/`store` through `x7` is safe wherever it appears, and branching into the middle of an `andi; add; ld` idiom cannot forge an out-of-bounds pointer. A sequence-based rule that verified `andi; add; ld` as a multi-instruction unit would have to forbid branches targeting interior instructions or propagate per-program-point facts—requiring CFG and dataflow bookkeeping in the kernel checker. This is the Wahbe dedicated-register SFI discipline instantiated with a mechanized `RV64` soundness proof.

#### 1.3 Six Individually Necessary Side Conditions and Separating Witnesses

`Basis: execution (Lean kernel) + normative + source + derived`

Each side condition of `OkInstr` and `AddrOk` is individually necessary. [`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean) (`cfgDemo = { ctxBytes := 64, scrBytes := 4096, idxMask := 2040 }`, `sDemo` with context at `0x10000`, scratch at `0x20000`, `ra = 0x80001000`, and secret byte `0xAA` planted at `0xfff8`) proves a concrete separating witness for each:

| # | Side condition | Failing instruction & concrete behavior | Mechanized witness (`SmodeSfiChecker.lean`) |
| --- | --- | --- | --- |
| 1 | Non-negative raw load/store immediate (`imm < 2048`) | `ld t0, -8(a0)` (raw `imm12 = 0xff8 = 4088`, word `0xff853283`): effective address `0xfff8` is 8-aligned, executes without any trap, and loads `0xAA` from below the context region. A checker bounding only the signed value from above (`signed_imm + w ≤ ctxBytes`) would admit it. | `neg_imm_reads_below_region` (`:910-917`) |
| 2 | Natural alignment (`imm % w = 0`, 8-aligned base/index) | `ld t0, 4(a0)`: starts inside the 64-byte context, triggers `Trap.loadMisaligned` under the conservative trapping model, and at `base + size - 4` an 8-byte access would also cross the upper region boundary (`imm % w = 0 ∧ imm + w ≤ size` closes both). | `misaligned_load_traps` (`:922-928`) |
| 3 | Region upper bound (`imm + w ≤ ctxBytes` / `idxMask + imm + w ≤ scrBytes`) | `ld t0, 64(a0)`: non-negative and 8-aligned, but bytes `[0x10040, 0x10048)` lie past the 64-byte context. | `overrun_rejected` (`:932-937`) |
| 4 | Non-negative, 8-aligned `andi` mask (`imm < 2048 ∧ imm ≤ idxMask ∧ imm % 8 = 0`) | `andi t1, t0, -8` (raw `0xff8`): sign-extends to `0xffff_ffff_ffff_fff8`, aligning without bounding; on `t0 = 2^40`, the result remains `2^40`. | `neg_mask_does_not_bound` (`:942-944`) |
| 5 | Restricted `jalr` (`rd = 0 ∧ rs1 = 1 ∧ imm = 0`) | `jalr x0, 0(t0)`: exits the module to `t0` (`0`) rather than caller `ra` (`0x80001000`). | `computed_jalr_escapes` (`:948-950`) |
| 6 | Strictly forward branches/jumps (`0 < off`, `off % 4 = 0`, `i + off/4 < n`, `jal` with `rd = 0`) | `beq x0, x0, 0`: remains at `pc = 0` after every step `k` and never returns. | `self_branch_never_returns` (`:955-977`) |

Additional mechanized boundary witnesses in the same section:

- **`SYSTEM` opcode rejection (`system_rejected`, `:991-994`):** Every `0x73` encoding (`ecall`, `ebreak`, `sret`, `mret`, `wfi`, `sfence.vma`, `csrrw`, `rdcycle`, etc.) traps in the model (`Trap.privileged`) and is rejected (`decode_rejected`, `:1108-1120`, also verifies rejection of `auipc`, `fence.i`, `lr.d`, and compressed 16-bit parcels such as `0x00000001`).
- **Scratch-mask reachability (`and_mask_bound`, `:374-379`):** Because `andi` sign-extends its 12-bit immediate, a single `andi` can either *bound* (`0 ≤ M ≤ 2047`) or *align* (negative `M`), never bound above `2047`. Requiring `M < 2048 ∧ M % 8 = 0` bounds and 8-aligns simultaneously (`a &&& m ≤ m ∧ (a &&& m) % 8 = 0`). With `idxMask = 0x7f8` (`2040`) and static load/store displacement up to `0x7f8`, `imm(x7)` reaches offsets `0 … 0xff7` of a 4 KiB scratch page. Larger scratch regions require either a kernel-loaded reserved mask register (`and x6, rs, xMASK`, covered by the same `and_mask_bound` lemma) or an `slli`/`srli` pair (not mechanized).
- **Forward-only layout vs. ranking certificates and bounded loops (`counter_wraps`, `:984-986`):**
  - *Derived comparison:* A certificate assigning a strictly decreasing numeric rank per program counter forces the control-flow graph to be acyclic; every finite DAG admits a topological layout in which every edge is strictly forward. Thus a per-PC rank certificate accepts no program that forward-only layout cannot already express, while adding a certificate table and table-verification logic to the kernel.
  - Admitting loops requires a rank over both `pc` and register state—for example, a dedicated loop-counter register written only by an initializer and a decrement and tested by a signed `0 < c` check. `counter_wraps` proves why testing `c ≠ 0` is unsound: `aluEval .add 0 (sext12 4095) = 2^64 - 1`, so `addi c, c, -1; bne c, x0, loop` entered with `c = 0` wraps and iterates `2^64 - 1` additional times. A bounded-loop checker would also need per-back-edge region checks ensuring no control path bypasses counter initialization and the loop body does not overwrite the counter (not mechanized).
- **Misaligned control transfers (normative):** `riscv/riscv-isa-manual@5f1104a0613af80219232b1e4bc108f9ec2bd6b2`, `src/unpriv/rv32.adoc:106-108, 475-478` specifies that with `IALIGN = 32` (no `C` extension), any taken branch or unconditional jump (`jal`/`jalr`) whose target address is not 4-byte aligned raises an instruction-address-misaligned exception. `OkInstr` prevents this via `off % 4 = 0` on all branches/jumps and `Entry.raAl` (`ra % 4 = 0`) on `ret`.

#### 1.4 Platform Behavior of Misaligned `ld`/`sd`: ISA vs. QEMU vs. OpenSBI

`Basis: normative + source + derived`

Assuming that an unaligned S-mode `ld`/`sd` raises a synchronous S-mode misaligned exception is **false** on standard RISC-V virtual and firmware platforms:

1. **Normative ISA (`riscv/riscv-isa-manual@5f1104a0613af80219232b1e4bc108f9ec2bd6b2`, `src/unpriv/rv32.adoc:692-719`):** Naturally aligned loads and stores shall not raise an address-misaligned exception. Misaligned loads and stores have *EEI-dependent* behavior: an EEI may support them in hardware or via an invisible trap into the execution environment; otherwise they may either complete or raise either an address-misaligned or an access-fault exception.
2. **QEMU `v10.0.0` TCG (`qemu/qemu@7c949c53e936aa3a658d84ab53bae5cadaa5d59c`):**
   - `target/riscv/insn_trans/trans_rvi.c.inc:363-370, 401-420, 471-516`: `gen_load_tl` and `gen_store_tl` pass the instruction's `MemOp` straight to `tcg_gen_qemu_ld_tl`/`tcg_gen_qemu_st_tl` without `MO_ALIGN`.
   - `MO_ALIGN` is requested only for atomics (`target/riscv/translate.c:1129-1141`, `target/riscv/insn_trans/trans_rva.c.inc:102-176`).
   - `riscv_cpu_do_unaligned_access` (`target/riscv/cpu_helper.c:1799-1824`), the sole producer of `RISCV_EXCP_LOAD_ADDR_MIS`, is invoked only when `MO_ALIGN` was set (via `tcg-cpu.c:148`).
   - *Derived:* Under QEMU `v10.0.0` TCG, a misaligned S-mode `ld`/`sd` completes silently with no exception.
3. **OpenSBI (`riscv-software-src/opensbi@ed70256dd22c09962d146e433834239825ef0616`):**
   - `lib/sbi/sbi_trap.c:424-463` (`delegate_traps`): sets `medeleg` to delegate `CAUSE_MISALIGNED_FETCH`, `CAUSE_BREAKPOINT`, `CAUSE_USER_ECALL`, and page faults; `CAUSE_MISALIGNED_LOAD`, `CAUSE_MISALIGNED_STORE`, and `CAUSE_ILLEGAL_INSTRUCTION` are **not** delegated to S-mode.
   - `lib/sbi/sbi_trap.c:328-342` routes misaligned load/store traps to `sbi_misaligned_load_handler` and `sbi_misaligned_store_handler` (`lib/sbi/sbi_trap_ldst.c:467-529`), which emulate the access in M-mode.

*Derived engineering consequence:* On `RV64IM` platforms running OpenSBI or QEMU, an unchecked misaligned access is either (a) completely silent on QEMU (so emulator-based fuzzing or negative tests cannot catch missing alignment checks), or (b) trapped to M-mode and emulated in firmware on hardware that traps, injecting unbounded firmware latency into S-mode kernel execution. Static natural alignment (`imm % w = 0`, 8-aligned base and masked index) is therefore required both for architectural trap-freedom/WCET and to prevent multi-byte accesses starting at `base + size - 4` from crossing the region boundary.

---

### 2. `RV64M` Division Semantics and the Lean 4 Core `BitVec` Discrepancy

`Basis: normative + execution (Lean kernel) + derived`

In `riscv/riscv-isa-manual@5f1104a0613af80219232b1e4bc108f9ec2bd6b2`, `src/unpriv/m-st-ext.adoc:90-128` (ratified 20191213 §7.2), integer division and remainder **never trap** (explicitly noted as avoiding introducing the sole arithmetic trap in the standard ISA). For width `L ∈ {32, 64}`:

| Condition | `divu` / `divuw` | `remu` / `remuw` | `div` / `divw` | `rem` / `remw` |
| --- | --- | --- | --- | --- |
| Divisor `b = 0` | `2^L - 1` (all ones, sign-extended to 64b for `*w`) | `x` (low 32b sign-extended for `remuw`) | `-1` (`2^64 - 1` for **every** dividend) | `x` (low 32b sign-extended for `remw`) |
| Signed overflow (`-2^(L-1) / -1`) | cannot occur | cannot occur | `-2^(L-1)` (sign-extended for `divw`) | `0` |

[`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean) (`aluEval`, `:111-135`, theorems `:845-878`) mechanizes all eight operations and proves every table entry (`divu_by_zero`, `remu_by_zero`, `div_by_zero`, `rem_by_zero`, `div_overflow`, `rem_overflow`, `divw_by_zero`, `divuw_by_zero`, `remw_by_zero`, `remuw_by_zero`, `divw_overflow`, `remw_overflow`, `div_trunc`):

- Because none of the eight instructions traps, `OkInstr` admits all of them with **no** operand precondition, and `demoProg_safe` (`:1023-1025`) proves an admitted 8-instruction module (`demoProg` / `demoWords_checked`) that divides by an attacker-controlled context word returns safely to `ra` within 8 steps. (For WCET budgeting, division instructions dominate per-instruction latency even though they never trap.)
- **Lean 4 core `BitVec` modeling trap (`lean_sdiv_differs_from_rv64m_div`, `:885-887`):** On `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), Lean's built-in signed bitvector division operators **disagree** with `RV64M` `div` when the dividend is negative and the divisor is zero:
  ```lean
  theorem lean_sdiv_differs_from_rv64m_div :
      BitVec.smtSDiv (-1#64) 0#64 = 1#64 ∧
      BitVec.sdiv    (-1#64) 0#64 = 0#64 ∧
      aluEval .div 18446744073709551615 0 = 18446744073709551615 := by decide
  ```
  - `BitVec.smtSDiv` follows the SMT-LIB `bvsdiv` convention (`+1` when dividend `< 0` and divisor `= 0`, `-1` when dividend `≥ 0` and divisor `= 0`).
  - `BitVec.sdiv` follows Lean core's total-division convention (`0` on division by zero).
  - `RV64M` `div` returns `-1` (`0xffff_ffff_ffff_ffff`) for **all** dividends when divisor is `0`.
  - Any Lean ISA semantics or translation validator that maps `RV64M` `div` directly to `BitVec.sdiv` or `BitVec.smtSDiv` is unsound on negative dividends divided by zero. (`BitVec.smtUDiv` does match `RV64M` `divu` by zero, returning all ones.)
- **Compiler lowering consequence (*derived*):** When compiling a source language in which integer division/remainder by zero or signed `MIN / -1` overflow are runtime panics or undefined behavior (such as Rust MIR), lowering to `RV64M` `div`/`rem` must preserve explicit software guards: the target instruction silently produces a defined bit pattern where the source language requires a trap.

---

### 3. Sandbox Confidentiality and Hook-Activation Noninterference

#### 3.1 Module-Level Confidentiality (`sandbox_noninterference`)

`Basis: execution (Lean kernel) + derived`

[`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean) (`:628-841`) defines `Vis r := IsTemp r ∨ r = 6 ∨ r = 7 ∨ r = 10 ∨ r = 11` and `LowEq cfg s0 s t` (agreement on `pc`, all `Vis` registers, and all bytes inside `InSandbox cfg s0`). It proves:

```text
sandbox_noninterference :
  check cfg prog = true → Entry cfg s0 → Entry cfg t0 → LowEq cfg s0 s0 t0 →
  ∀ k, OutLowEq cfg s0 (run prog k s0) (run prog k t0)
```

Two entry states may differ arbitrarily in all memory outside the two sandbox regions and in `ra`, `sp`, `gp`, `tp`, and `s0`–`s11`; after any step count `k`, both executions remain in the same control outcome (both running with `LowEq`, or both returned with `LowEq`, or the same trap), proving that step count, final temporaries, and final sandbox contents are independent of non-sandbox kernel state.

This proof exposes four structural obligations, three of which lie on the kernel trampoline/loader rather than the per-instruction check:

1. **Ban reserved registers as *data operands*, not merely as destinations.** In `OkInstr`, `CanRead` admits only `x0`, `IsTemp`, and `x6`. Allowing reserved registers as read operands (e.g., `sd sp, 0(a0)` or `add t0, s1, x0`) would preserve every callee-saved register while leaking kernel pointers or secrets directly into the sandbox.
2. **Initialize (scrub) all 11 temporaries on trampoline entry (`unscrubbed_temp_leaks`, `:1000-1003`).** `sd t0, 0(a0)` is admitted by `OkInstr` (`OkInstr cfgDemo 2 0 (.store 8 5 10 0)`), and copies whatever value the kernel left in `t0` into the context region (`writeBytes` produces `0` vs. `170` at `0x10000` depending on `t0`). `LowEq` assumes entry temporaries agree; the trampoline must explicitly define all 11 temporaries (11 register writes) unless the checker performs per-program-point definite-assignment analysis.
3. **Forbid PC-relative address materialization and hardware counters.** `auipc` is excluded (`decode_rejected`, `:1117`), `jal` requires `rd = x0` (`OkInstr`, `:286`), and `rdcycle`/`rdtime`/`rdinstret` fall under `SYSTEM` (`decode_rejected`, `:1116`), preventing the module from reading its kernel load address or wall/cycle counters.
4. **Loader and platform obligations outside `OkInstr` (`Basis: normative + derived`, not mechanized):**
   - *Copy-before-verify:* Copy untrusted code bytes into kernel-owned memory, verify that kernel-private copy, and only then mark the slot executable (never verify bytes still writable by user space—the code analogue of §5).
   - *Instruction-cache synchronization:* Execute `fence.i` after writing the module into the executable slot (`riscv/riscv-isa-manual@5f1104a0613af80219232b1e4bc108f9ec2bd6b2`, `src/unpriv/zifencei.adoc:77-80`: "`fence.i` orders all explicit memory accesses and instruction fetches that precede the `fence.i` in program order before all instruction fetches that follow"). Single-hart `fence.i` is sufficient on a single hart; SMP requires cross-hart I-cache shootdown.
   - *Strict allow-list decoding:* Because OpenSBI does not delegate `CAUSE_ILLEGAL_INSTRUCTION` (`lib/sbi/sbi_trap.c:424-463`), any undefined/reserved encoding admitted by a permissive decoder traps into M-mode first.
   - *S-mode interrupt latency and backing-frame lifetime:* Running a module with S-mode interrupts masked adds its worst-case path to kernel interrupt latency; backing code/scratch/context frames must remain pinned for the module's lifetime (§6).

#### 3.2 Hook Attachment Noninterference and the seL4 `domain_sep_inv` Envelope

`Basis: execution (Lean kernel) + source + derived`

[`support/HookNoninterference.lean`](support/HookNoninterference.lean) (namespace `HookNoninterference`) takes §3.1 as the abstract interface of any admitted module: an arbitrary deterministic function `Module := Nat → Nat → Nat × Nat × Nat` mapping `(ctx, scratch)` to `(scratch', verdict, cost)`. Kernel state `KState` tracks `owner : Dom` (the domain owning the module, its persistent scratch region, and the hook object), `scratch : Nat`, `obs : Dom → Nat` (per-domain observable IPC/context state), and `clock : Dom → Nat` (per-domain consumed time). One hook activation `fire m trig s` (`:48-52`) reads `s.obs trig` and `s.scratch`, updates `scratch`, writes `verdict` to `obs trig`, and adds `cost` to `clock trig`. Domain `d` observes `owner`, `obs d`, `clock d`, and (when `owner = d`) `scratch` (`ObsEq`, `:56-58`).

- **Sufficiency of same-domain activation (for *every* module `m`):**
  - `same_domain_step_consistent` (`:63-91`): `ObsEq d s t → ObsEq d (fire m s.owner s) (fire m t.owner t)`.
  - `same_domain_locally_respects` (`:95-103`): `s.owner ≠ d → ObsEq d (fire m s.owner s) s`.
- **Necessity — three bidirectional cross-domain leak witnesses (`owner = .hi`, `trig = .lo`):**
  - `cross_domain_verdict_leaks` (`:113-121`): module `fun _ sc => (sc, sc, 0)` leaks `hi`'s scratch to `lo`'s observable verdict (`hi → lo`).
  - `cross_domain_time_leaks` (`:126-134`): module `fun _ sc => (sc, 0, sc)` returns constant verdict `0` but leaks `hi`'s scratch through `clock .lo` (`hi → lo`).
  - `cross_domain_scratch_absorbs` (`:144-152`): module `fun ctx _ => (ctx, 0, 0)` copies `lo`'s context into `hi`-readable persistent scratch (`lo → hi`), creating an unauthorized information flow from attachment alone regardless of capability policy.

**Required domain-ownership invariant (*derived*):** For every attachment of module `M` to hook `H`, `label(M.code) = label(M.scratch) = label(H) = d`, **and every activation of `H` must execute in domain `d`**.

- *Endpoint / notification hooks:* For a cross-domain IPC object (sender in `S`, receiver in `R`), an `R`-owned module must **not** execute on `S`'s send path (its verdict and running time flow `R → S`, and `S`'s message flows into `R`'s scratch outside policy). Running the module on the **receive** side, in `R`'s scheduling slice and charged to `R`, satisfies the invariant. Intra-domain objects satisfy it trivially.
- *Interrupt hooks vs. seL4's noninterference premise:* An interrupt fires in whichever domain happens to be executing when the interrupt is taken; satisfying same-domain activation requires a total per-IRQ ownership map `irqOwner` and rewriting the interrupt controller's enable mask on every domain switch. However, inspection of `seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`, `proof/access-control/DomainSepInv.thy:16-34` shows that seL4's information-flow noninterference theorem (`proof/infoflow/Noninterference.thy:379`) takes `domain_sep_inv irqs st'` as a standing premise:
  ```isabelle
  definition domain_sep_inv where
    "domain_sep_inv irqs st s ≡
      (∀slot. ¬ cte_wp_at ((=) DomainCap) slot s) ∧
      (irqs ∨ (∀irq slot. ¬ cte_wp_at ((=) IRQControlCap) slot s
                        ∧ ¬ cte_wp_at ((=) (IRQHandlerCap irq)) slot s
                        ∧ interrupt_states s irq ≠ IRQSignal
                        ∧ interrupt_states s irq ≠ IRQReserved
                        ∧ (irq ∈ non_kernel_IRQs ⟶ interrupt_states s irq = IRQInactive)
                        ∧ interrupt_states s = interrupt_states st))"
  ```
  As `DomainSepInv.thy:16-25` notes, *"When `irqs` is `False` we require that non-timer IRQs are off permanently."* *Derived:* in any configuration covered by seL4's existing noninterference theorem (`irqs = False`), no `IRQHandlerCap` capability exists to attach a module to. Supporting interrupt hooks under noninterference therefore requires a new per-domain interrupt-partitioning proof (or confining interrupt hooks to integrity-only configurations).

---

### 4. Zero-Copy `LoanFrame` Lifecycle: Seven Necessary Kernel Invariants

#### 4.1 Exhaustive Finite-State Model and Safety Theorem

`Basis: execution (Lean kernel, exhaustive) + normative + source + derived`

[`support/LoanRingPin.lean`](support/LoanRingPin.lean) (namespace `LoanRingPin`, Part A, `:26-364`) models a client address space `A` lending a physical frame to a server address space `B` for the duration of a `Call` bound to a `Reply` object, in the presence of a third-party capability `C` to the same frame and hardware TLB caching in both `A` and `B`.

- **State (`LState`, `:43-53`):** 9 fields — `frameLive : Bool`, `replyLive : Bool`, `loan : Option Perm` (the loan token, `Perm = ro | rw`), `savedA : Option Perm` (client's pre-loan permission saved in the token), `pteA : Option Perm`, `tlbA : Option Perm`, `slot : Slot` (`empty | own | loaned p`), `tlbB : Option Perm`, `pteC : Option Perm`. Total abstract state space: `2 × 2 × 3 × 3 × 3 × 3 × 4 × 3 × 3 = 11,664` states.
- **TLB semantics:** Cached translations (`tlbA`, `tlbB`) are consulted alongside page-table entries (`canA`, `canB`, `:162-163`), modeling the RISC-V Supervisor ISA rule (`riscv/riscv-isa-manual@5f1104a0613af80219232b1e4bc108f9ec2bd6b2`, `src/priv/supervisor.adoc:1300-1304`) that hardware may use any translation valid at any time since the most recent subsuming `sfence.vma`.
- **Events (`Ev`, `:55-69`):** 13 constructors / 18 concrete transitions — `loan (ro|rw)`, `reply`, `revokeFrame`, `deleteReply`, `accessA (false|true)`, `accessB (false|true)`, `bUnmapPT`, `bMapOwn`, `bUnmapOwn`, `aUnmap`, `aMap (ro|rw)`, `cMap (ro|rw)`, `cUnmap`.
- **Safety predicate (`safe`, `:176-181`):**
  1. Nobody (`A`, `B`, or `C`) reaches a deleted frame (`!frameLive`).
  2. Server `B` reaches the frame only under a live loan and writes only under a `rw` loan.
  3. While any loan is live, neither `A` nor `C` has any writable translation (no concurrent modification / TOCTOU against the server).
  4. While an exclusive (`rw`) loan is live, neither `A` nor `C` has *any* translation to the frame.
  5. A live loan always has both a live `Reply` object and a live frame.

With all seven boolean fields of `Design` (`:72-81`) enabled (`good`), `inv_step_fields` (`:269-274`) and `inv_safe_fields` (`:281-286`) are discharged by `decide +kernel` over all `11,664 × 18` state-event pairs, establishing:

- `good_design_safe` (`:299-300`): `∀ tr : List Ev, safe (run good init tr) = true`.
- `no_collateral_unmap` (`:304-309`): `reply`, `revokeFrame`, and `deleteReply` never clear a server-owned page (`.own`) installed at the loan-slot address.
- `reply_restores_owner` (`:312-316`): after `[.loan p, .accessB false, .reply]`, `pteA = some .rw`, `loan = none`, and `slot = .empty`.

#### 4.2 Seven Individually Necessary Kernel Decisions

`Basis: execution (Lean kernel)`

Disabling any single field of `Design` while keeping the other six enabled yields an immediate violating trace (`LoanRingPin.lean:322-363`):

| # | `Design` decision | Minimal violating trace when disabled | Failure mode | Theorem |
| --- | --- | --- | --- | --- |
| 1 | `flushOnLoan`: `sfence.vma va, client_asid` at loan start | `[.accessA true, .loan .rw]` | Client's cached `rw` TLB entry survives PTE downgrade; client can still write during an exclusive loan. | `need_flushOnLoan` (`:322`) |
| 2 | `flushOnEnd`: `sfence.vma slot_va, server_asid` at loan end | `[.loan .rw, .accessB true, .reply]` | Server retains a cached translation to the frame after replying. | `need_flushOnEnd` (`:328`) |
| 3 | `endOnRevoke`: frame deletion ends loan via token | `[.loan .rw, .revokeFrame]` | Server keeps mapping physical memory about to be retyped. | `need_endOnRevoke` (`:335`) |
| 4 | `endOnReplyDel`: `Reply` destruction ends loan via token | `[.loan .rw, .deleteReply]` | Loan outlives the only object capable of ending it. | `need_endOnReplyDel` (`:341`) |
| 5 | `ppnCheck`: teardown clears loan slot only if PTE still maps the loaned frame | `[.loan .rw, .bUnmapPT, .bMapOwn, .reply]` | Kernel unmaps an unrelated page the server mapped itself after discarding the loan page table. | `need_ppnCheck` (`:347`) |
| 6 | `uniqueCheck`: start loan only if no second mapping exists | `[.cMap .rw, .loan .rw]` | Pre-existing alias through a second capability permits concurrent writes during the loan. | `need_uniqueCheck` (`:355`) |
| 7 | `mapGuard`: refuse new mappings of the frame while loaned | `[.loan .rw, .cMap .rw]` | Second capability creates a fresh writable mapping mid-loan. | `need_mapGuard` (`:361`) |

#### 4.3 Lifecycle Corner Cases, `sfence.vma` Rules, and seL4 Representation Constraints

`Basis: execution + normative + source + derived`

| Lifecycle corner case | Model events | Behavior under `good` |
| --- | --- | --- |
| Client's `Untyped`/`Frame` revoked before reply | `revokeFrame` | Loan ends immediately via the token (slot cleared and fenced, token cleared, frame dead). Revocation never blocks on an uncooperative server; the server must treat a fault on its loan slot as client withdrawal. |
| Server faults (while `Reply` persists) | none | Loan persists and client remains blocked, matching standard un-replied `Call` semantics. |
| Server TCB deleted or `Reply` capability dropped | `deleteReply` | Loan ends through the token; client's original mapping is restored. |
| Server tries to map over active slot, or unmaps its page table and maps its own page | `bMapOwn` (refused while occupied), or `bUnmapPT; bMapOwn` | Server can only discard its own access; subsequent loan teardown checks the target PPN and leaves the server's own page intact (`no_collateral_unmap`). |
| Server replies to a different client | none on this `Reply` | Unaffected; the loan is bound to the specific `Reply` object created by the lending `Call`. |
| Client TLB caches pre-loan `rw` entry on a single hart | `accessA true; loan p` | Still reachable on a single hart whenever another thread shares the client's address space and runs if the server is preempted; eliminated by `flushOnLoan`. |

- **Normative RISC-V `sfence.vma` semantics (`riscv/riscv-isa-manual@5f1104a0613af80219232b1e4bc108f9ec2bd6b2`, `src/priv/supervisor.adoc:1252-1259, 1338-1341, 1384-1389`):**
  - `sfence.vma rs1, rs2` with `rs1 ≠ x0` and `rs2 ≠ x0` invalidates leaf-PTE translation cache entries for virtual address `rs1` in address space `rs2`. Because the ASID is a register operand, the kernel can flush the client's entry without switching `satp`.
  - For permission *upgrades* (installing the server's loan mapping or restoring the client's mapping), `supervisor.adoc:1384-1389` permits deferring `sfence.vma` lazily (hardware uses either old or new permissions, possibly raising a page fault), and `:1338-1341` explicitly allows caching invalid (`V = 0`) PTEs. Therefore a kernel must either fence eagerly on upgrade or recognize and retry spurious faults on freshly installed mappings.
- **seL4 RISC-V source comparison (`seL4/seL4@08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`):**
  - *Target-PPN check (`ppnCheck`):* `src/arch/riscv/kernel/vspace.c:555-576` (`unmapPage`) returns without modifying the page table if the ASID no longer resolves, the walk ends at the wrong level, the PTE is invalid or non-leaf, or its PPN differs from the target frame—only then clearing the PTE and fencing. This implements `ppnCheck` and also defends against ASID reuse (where the recorded ASID now names a different address space with an unrelated page at the same VA).
  - *Fence granularity:* `seL4`'s `unmapPage` issues unqualified `sfence.vma` (`include/arch/riscv/arch/machine.h:139-142`), flushing every address space; the only narrower helper is `hwASIDFlush` (`sfence.vma x0, asid`, `:144-147`). Narrowing to `sfence.vma va, asid` for latency requires passing the *recorded* ASID from the token rather than the currently active ASID.
  - *State placement and constant-size teardown:* In seL4, mapping coordinates live on each *capability* (`include/arch/riscv/arch/64/mode/object/structures.bf:23-34`: `capFMappedASID`, `capFMappedAddress`; `src/arch/riscv/object/objecttype.c:76-84`), and physical frame pages have no in-band header (all bytes are user data). A kernel-created loan mapping has no capability in the server's CSpace, so an explicit token recording `(server ASID, slot VA, client ASID, client VA, saved perm)` linked from the `Reply` object and an out-of-line per-frame side table indexed by frame number is mandatory to make `reply`, `deleteReply`, and `revokeFrame` constant-size updates (`endLoan`, `:105-114`, touches only fields reachable from the token with no page-table walk).
  - *Uniqueness is the hidden linear-time step (derived):* Checking `uniqueCheck` under a per-capability mapping scheme would otherwise require scanning every capability derived from the frame. Constant-time loan admission therefore requires either maintaining a per-frame mapping count in the out-of-line frame side table or restricting loans to frames with a single capability verified in `O(1)`.

---

### 5. Single-Fetch Shared-Ring TOCTOU Prevention

`Basis: execution (Lean kernel) + derived`

[`support/LoanRingPin.lean`](support/LoanRingPin.lean) (Part B, `:365-424`) models user-shared submission-queue memory as an arbitrary stream of observations `Shared := Nat → SqEntry`, where the `i`-th kernel fetch of the same shared address returns `sh i` with no constraint relating `sh 0` and `sh 1`:

- **Double-fetch vulnerability (`doubleFetch_out_of_bounds`, `:405-408`):** `consumeDoubleFetch` checks `entryValid regionLen (sh 0)` and then acts on `((sh 1).off, (sh 1).len)`. The witness `fun i => if i = 0 then ⟨0, 0, 16⟩ else ⟨0, 0, 1048576⟩` passes validation against `regionLen = 4096` on fetch 0 and produces an out-of-bounds range `0 + 1048576 > 4096` on fetch 1.
- **Single-fetch soundness (`copyOnce_in_bounds`, `:391-401`):** `consumeCopyOnce` binds `let e := sh 0` once into a kernel-private value, validates `entryValid regionLen e`, and returns `(e.off, e.len)`. For every `regionLen` and every adversarial `sh : Shared`, `consumeCopyOnce regionLen sh = some (off, len) → off + len ≤ regionLen`.
- **Bounded ring-index discipline (`batch_bounded`, `:413-423`):** Reading the user-written 32-bit `tail` **once** per batch, maintaining `headPriv` exclusively in kernel-private storage (never reading the kernel's own head back from shared memory), computing `batchLen size headPriv tail := min ((tail % 2^32 + 2^32 - headPriv % 2^32) % 2^32) size`, and addressing slots via `slotIdx size headPriv i := (headPriv + i) % size` guarantees `batchLen ≤ size` and `∀ i, slotIdx < size` for every `size > 0` and every adversarial `tail`.

**Verification-semantics requirement (*derived*):** Any operational semantics that models memory deterministically (where two reads of the same location without an intervening kernel write return identical values by construction) renders double-fetch TOCTOU bugs unexpressible—`consumeDoubleFetch` would spuriously verify as safe. Mechanized proofs of TOCTOU freedom for shared-ring consumers must therefore model every read from user-writable memory as a distinct nondeterministic observation (matching `Shared := Nat → SqEntry`).

---

### 6. Unified Per-Frame Pin Across Loans, Rings, and Kernel Modules

`Basis: execution (Lean kernel) + derived`

[`support/LoanRingPin.lean`](support/LoanRingPin.lean) (Part C, `:425-550`) models every long-lived kernel subsystem retaining a physical frame across system calls with `Holder = loan | ring | modCode | modScratch` and a single authoritative per-frame field `pin : Option Holder` alongside per-holder back-references (`PState`, `2 × 5 × 16 = 160` abstract states; `PEv = pin h | release h | revoke`, `9` concrete events):

- **Safety predicate (`psafe`, `:488-493`):** Every holder whose back-reference is set must be the unique `pin` holder of a live frame (`frameLive = true`), and a deleted frame (`frameLive = false`) must have `pin = none`. Thus the kernel never dereferences retyped memory (e.g., writing ring completions or fetching/executing module code/scratch from a revoked frame) and no two subsystems share a pinned frame simultaneously.
- **Exhaustive soundness (`psafe_step_fields`, `pin_safe`, `:524-543`):** Checked exhaustively via `decide +kernel` over all `160 × 9` transitions when frame revocation notifies the pinned holder (`notify = true`: detach the holder recorded in `pin`, clear `pin`, and mark `frameLive := false`) and holder release clears `pin`.
- **Necessity of revocation notification (`need_revoke_notification`, `:547-550`):** When revocation ignores the pin (`notify = false`), both `[.pin .ring, .revoke]` and `[.pin .modCode, .revoke]` immediately violate `psafe`, leaving the ring or loaded module holding a dangling reference into deleted memory.

*Derived architectural unification:* One out-of-line per-frame `pin : Option Holder` field (co-located in the same frame-number side table needed for `LoanFrame` uniqueness) suffices to govern frame lifetime for zero-copy loans, asynchronous I/O rings, and S-mode module code/scratch frames simultaneously. Subsystem-specific teardown metadata (saved client permissions and VAs for loans, ring descriptors, or module slots) remains in the holder object, while the pin provides the single constant-time reverse pointer needed on frame revocation—discharging both the ring-backing-frame hazard and the S-mode module `Entry` frame-lifetime obligation (§3.1).

## Boundaries

- **Abstract models, not a concrete kernel implementation:** Every theorem in [`support/`](support/) holds for the Lean definitions in those files. Transfer to a concrete kernel requires establishing that the production checker refines `check`, the production decoder agrees with `decode`, the trampoline establishes `Entry` (including scrubbing all 11 temporaries), and the kernel's page-table/pin/ring implementations refine `step`, `consumeCopyOnce`, and `pstep`. None of those implementation-refinement steps is examined here.
- **Decoder faithfulness against the full ISA — unknown:** `decode` in [`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean) (`:1032-1090`) is checked on the 20 concrete 32-bit words in `decode_admitted` and `decode_rejected` (`:1096-1120`) and the 8 words of `demoWords_checked` (`:1131-1134`), not differentially verified against an authoritative ISA model (e.g., Sail).
- **Unmodeled `RV64IM` ISA features — not examined:** `SmodeSfiChecker.lean` omits virtual memory translation, page/access faults (whose absence in a kernel relies on the frame-pinning invariant of §6), interrupts, CSRs, `mulh`/`mulhsu`/`mulhu`, non-division `W` (`OP-32`) instructions (`addw`, `subw`, `sllw`, `srlw`, `sraw`, `mulw`), `auipc`, compressed (`C`) instructions, atomics (`A`), and floating-point (`F`/`D`). Adding `mulh*` or `OP-32` arithmetic requires only `aluEval`/`decode` cases.
- **QEMU misaligned-access behavior — source-only, single version:** The QEMU TCG finding is established by source inspection of `qemu/qemu@7c949c53e936aa3a658d84ab53bae5cadaa5d59c` (`v10.0.0`); no QEMU binary was executed in this investigation. Other QEMU versions, hardware virtualization (`KVM`), and physical RISC-V cores are **not examined**.
- **Bounded loops and kernel helper calls in S-mode modules — not examined:** Loops are analyzed only via `counter_wraps` and the derived counter-register discipline in §1.3; kernel helper calls from inside a module (which would alter the register-preservation and noninterference discipline) are **not examined**.
- **Microarchitectural and speculative side channels — not examined:** `HookNoninterference.lean` charges an abstract `cost : Nat` to the triggering domain's `clock`; cache timing, branch-predictor state, and speculative execution (Spectre) are **not examined**.
- **`LoanFrame` model scope — not examined:** `LoanRingPin.lean` Part A models one frame, one client mapping, one third-party capability, one server loan slot, one `Reply` object, and one hart. Multi-hart TLB shootdowns, nested loans, multiple simultaneous loans to one server, superpage mappings, and negative (invalid-PTE `V = 0`) TLB caching are **not examined** (negative PTE caching is noted from the ISA specification only).
- **Constant-size teardown — structural reading only:** §4.3's constant-size teardown observation is a structural reading of `endLoan` and seL4's data structures, not a benchmarked or formally mechanized complexity proof.
- **Shared-ring scope — not examined:** `LoanRingPin.lean` Part B covers single-entry double fetch and batch index clamping; completion-queue overflow, wake-up notification races, and registered-buffer lifetimes beyond the backing frame pin are **not examined**.
- **Attractive stronger conclusions not established:**
  - *Not established* that `OkInstr` is complete for any particular class of real-world hooks, or that forward-only control flow is expressive enough for all desired kernel extensions.
  - *Not established* that same-domain activation is *necessary* for every individual module (it is sufficient for all modules and necessary to exclude leaks across the three exhibited adversarial modules in `HookNoninterference.lean`).

## Evidence

### 1. Mechanized Support Material Preserved in This Package (`support/`)

All three files are standalone Lean 4 (`v4.34.1`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`) modules using the core library only (zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`), observed `2026-11-19`:

| File | Lines | Namespace | Key definitions & theorems |
| --- | ---: | --- | --- |
| [`support/SmodeSfiChecker.lean`](support/SmodeSfiChecker.lean) | 1,136 | `SmodeSfiChecker` | `St`/`Instr`/`exec`/`step`/`run` (`:37-237`); `OkInstr`/`AddrOk`/`check` (`:243-330`); `Entry`/`Inv` (`:335-358`); `and_mask_bound` (`:374`); `exec_ok`/`safe_and_terminates`/`never_traps` (`:461-623`); `sandbox_noninterference` (`:628-841`); `RV64M` division table & `lean_sdiv_differs_from_rv64m_div` (`:845-887`); separating witnesses `neg_imm_reads_below_region`, `misaligned_load_traps`, `overrun_rejected`, `neg_mask_does_not_bound`, `computed_jalr_escapes`, `self_branch_never_returns`, `counter_wraps`, `system_rejected`, `unscrubbed_temp_leaks` (`:892-1003`); `demoProg_safe` (`:1023`); allow-list `decode`, `decode_admitted`, `decode_rejected`, `words_safe_and_terminate`, `demoWords_checked` (`:1032-1134`). |
| [`support/HookNoninterference.lean`](support/HookNoninterference.lean) | 154 | `HookNoninterference` | `Dom`/`Module`/`KState`/`fire`/`ObsEq` (`:29-58`); `same_domain_step_consistent` (`:63-91`); `same_domain_locally_respects` (`:95-103`); `cross_domain_verdict_leaks` (`:113-121`); `cross_domain_time_leaks` (`:126-134`); `cross_domain_scratch_absorbs` (`:144-152`). |
| [`support/LoanRingPin.lean`](support/LoanRingPin.lean) | 552 | `LoanRingPin` | Part A (`:26-364`): `LState`/`Ev`/`Design`/`step`/`safe`/`inv`, exhaustive `decide +kernel` `inv_step_fields` (`:269`) & `inv_safe_fields` (`:281`), `good_design_safe` (`:299`), `no_collateral_unmap` (`:304`), `reply_restores_owner` (`:312`), seven necessity theorems `need_flushOnLoan`..`need_mapGuard` (`:322-363`). Part B (`:365-424`): `Shared`/`consumeCopyOnce`/`consumeDoubleFetch`, `copyOnce_in_bounds` (`:391`), `doubleFetch_out_of_bounds` (`:405`), `batch_bounded` (`:421`). Part C (`:425-550`): `Holder`/`PState`/`PEv`/`pstep`/`psafe`, exhaustive `psafe_step_fields` (`:524`), `pin_safe` (`:537`), `need_revoke_notification` (`:547`). |

### 2. Primary Upstream Sources (Observed `2026-11-19`)

| Subject | Immutable revision | Exact paths and line ranges | Evidence role |
| --- | --- | --- | --- |
| RISC-V ISA Manual | `riscv/riscv-isa-manual@5f1104a0613af80219232b1e4bc108f9ec2bd6b2` | `src/unpriv/rv32.adoc:106-118, 475-486, 692-719`; `src/unpriv/m-st-ext.adoc:90-128`; `src/unpriv/zifencei.adoc:77-80`; `src/priv/supervisor.adoc:1185-1199, 1252-1259, 1285-1310, 1332-1343, 1360-1389, 1593-1594` | normative |
| QEMU (`v10.0.0`) | `qemu/qemu@7c949c53e936aa3a658d84ab53bae5cadaa5d59c` | `target/riscv/insn_trans/trans_rvi.c.inc:363-420, 471-516`; `target/riscv/translate.c:1129-1141`; `target/riscv/insn_trans/trans_rva.c.inc:102-176`; `target/riscv/cpu_helper.c:1799-1824`; `target/riscv/tcg/tcg-cpu.c:148` | source |
| OpenSBI | `riscv-software-src/opensbi@ed70256dd22c09962d146e433834239825ef0616` | `lib/sbi/sbi_trap.c:328-342, 424-463`; `lib/sbi/sbi_trap_ldst.c:467-529` | source |
| seL4 Microkernel | `seL4/seL4@08c7e5fddb3111ff377745c8eefb07feb5c4cfb7` | `src/arch/riscv/kernel/vspace.c:555-576`; `include/arch/riscv/arch/machine.h:139-147`; `src/arch/riscv/object/objecttype.c:34-38, 76-84`; `include/arch/riscv/arch/64/mode/object/structures.bf:23-34` | source |
| seL4 Verification (`l4v`) | `seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e` | `proof/access-control/DomainSepInv.thy:16-34`; `proof/infoflow/Noninterference.thy:379`; `proof/infoflow/README.md` | source / documentation |
| Lean 4 (`v4.34.1`) | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` | Core `BitVec.sdiv` / `BitVec.smtSDiv` evaluated via `lean_sdiv_differs_from_rv64m_div` in `support/SmodeSfiChecker.lean:885-887` | execution |

## Revalidation

1. **Re-check the three standalone Lean 4 proofs (exit code `0`, zero warnings, zero `sorry`):**
   ```bash
   lean support/SmodeSfiChecker.lean
   lean support/HookNoninterference.lean
   lean support/LoanRingPin.lean
   ```
   `SmodeSfiChecker.lean` and `HookNoninterference.lean` check in seconds; `LoanRingPin.lean` performs exhaustive kernel evaluation (`decide +kernel` over 11,664 states × 18 events) and takes roughly one minute. To audit axioms without modifying the package files, run a one-line stdin check (confirming no `sorryAx` and no `Lean.ofReduceBool`):
   ```bash
   { cat support/SmodeSfiChecker.lean; printf '\n#print axioms SmodeSfiChecker.safe_and_terminates\n#print axioms SmodeSfiChecker.sandbox_noninterference\n#print axioms SmodeSfiChecker.words_safe_and_terminate\n#print axioms SmodeSfiChecker.lean_sdiv_differs_from_rv64m_div\n'; } | lean --stdin
   { cat support/HookNoninterference.lean; printf '\n#print axioms HookNoninterference.same_domain_step_consistent\n#print axioms HookNoninterference.same_domain_locally_respects\n'; } | lean --stdin
   { cat support/LoanRingPin.lean; printf '\n#print axioms LoanRingPin.good_design_safe\n#print axioms LoanRingPin.copyOnce_in_bounds\n#print axioms LoanRingPin.pin_safe\n'; } | lean --stdin
   ```
2. **Revalidate the misaligned-access platform findings on a newer QEMU or OpenSBI revision:**
   - In QEMU, inspect `gen_load_tl` and `gen_store_tl` in `target/riscv/insn_trans/trans_rvi.c.inc` to check whether `MO_ALIGN` has been added for regular integer loads/stores.
   - In OpenSBI, inspect `delegate_traps` in `lib/sbi/sbi_trap.c` to check whether `CAUSE_MISALIGNED_LOAD`, `CAUSE_MISALIGNED_STORE`, or `CAUSE_ILLEGAL_INSTRUCTION` has been added to `medeleg`.
   - For a direct execution probe on `qemu-system-riscv64 -M virt`, run a minimal S-mode payload executing `ld t0, 1(sp)`: completing without entering the S-mode trap vector confirms silent misaligned execution under TCG.
3. **Revalidate the seL4 `domain_sep_inv` and `unmapPage` premises:**
   - In `seL4/l4v`, inspect `domain_sep_inv` in `proof/access-control/DomainSepInv.thy`; the interrupt-hook envelope boundary holds as long as the `irqs = False` branch excludes `IRQHandlerCap`.
   - In `seL4/seL4`, inspect `unmapPage` in `src/arch/riscv/kernel/vspace.c` and `sfence_local` / `hwASIDFlush` in `include/arch/riscv/arch/machine.h` to check whether target-PPN verification or `sfence.vma` operand granularity has changed.
4. **Revalidate the `RV64M` division vs. Lean `BitVec` discrepancy:**
   - Compare `SmodeSfiChecker.aluEval` against the division-by-zero / overflow table (`[[divby0]]`) in `riscv/riscv-isa-manual` `src/unpriv/m-st-ext.adoc`, and re-run `lean_sdiv_differs_from_rv64m_div` on any newer Lean 4 release to verify whether `BitVec.sdiv` or `BitVec.smtSDiv` changed its zero-divisor semantics.
