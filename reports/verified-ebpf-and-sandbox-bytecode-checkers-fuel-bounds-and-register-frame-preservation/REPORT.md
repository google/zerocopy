# Verified eBPF and Machine-Code Sandbox Checkers: Arena Confinement, Callee-Saved Frame Preservation, Fuel Bounds, and Virtual-Memory ISA Composition

## Summary

Executing untrusted extension bytecode or compiled native code inside an OS kernel without a hardware privilege boundary requires discharging four coupled soundness obligations: **(1) memory-arena confinement** across disjoint `context`, `scratch`, and `payload` regions (with no pointer forgery or kernel-frame overlap), **(2) synchronous trap/fault absence** across division, shifts, alignment, and privileged instructions, **(3) host ABI preservation** of kernel callee-saved registers and stack pointers, and **(4) fuel-bounded or DAG-bounded termination**. Comparative source and proof inspection across **Jitterbug** (`uw-unsat/jitterbug@78d1e75a`), **PREVAIL** (`vbpf/ebpf-verifier@169eb5d6`), **CertrBPF / CertFC** (`future-proof-iot/CertFC@75690097`), **RockSalt** (`gangtan/CPUmodels@a6decc30`), **VeriWasm** (`PLSysSec/veriwasm@60a64d27`), **LFI** (`lfi-project/lfi-verifier@8c3c4798`), and **Sail RISC-V** (`riscv/sail-riscv@76f1ce3c`) establishes four core architectural results:

1. **No single existing system discharges the full binary-to-MMU chain:** PREVAIL checks relational region bounds and WTO loop counters in unverified C++; Jitterbug verifies JIT lowering down to RV64/x86-64/Arm64 *conditional* on `verifier-preconditions` assuming `heap-addr?`, alignment, and jump bounds; CertrBPF proves a runtime SFI table (`check_mem_aux2`) and fuel-monadic interpreter (`bpf_interpreter_aux`) in Rocq/CompCert `Clight` while axiomatizing helper calls (`call_inv_0..2`); RockSalt leaves six DFA lemmas `Admitted` and omits termination; and user-space SFI checkers (VeriWasm, LFI) depend on `PROT_NONE` guard pages that *fault* on OOB accesses.
2. **Source inspection uncovers concrete seams in cited verifiers:** In Jitterbug (`racket/arm64/spec.rkt`), `arm64-arch-safety` omits callee-saved `x24` and `arm64-simulate-call` retains `; FIXME: havoc caller-saved registers`. In VeriWasm (`src/checkers/`), `Stmt::Call` drops its `HeapBase` check (`heap_checker.rs:L76-L93`), online mode trusts arbitrary `.rodata`/`.data` offsets (`L156-L185`), stack reads test `< 8096` rather than `8192` (`stack_checker.rs:L127-L151`), and `JG`/`JLE` checks `Sf` twice while omitting `Zf` (`locals_checker.rs:L142-L146`). In `lfi-verifier`, Arm64 permits `MRS`/`MSR` on `FPCR`/`FPSR` (`src/arm64/verify.c:L80-L81, L163-L166`), and `lfiv_verify_riscv64` (`src/riscv64/verify.c:L3-L6`) returns `true` unconditionally.
3. **Host ABI preservation splits into three distinct patterns:** syntactic write-set exclusion (`ReadOnlyFixed` registers, as in LFI `x27`/`x25`), carved-frame prologue/epilogue invariants (Jitterbug RV64 `rv64-arch-invariants` over `[stackbase - 64, stackbase)`), and symbolic provenance tagging (`UninitCalleeReg(r)` in VeriWasm `LocalsChecker`).
4. **Virtual-memory composition requires a 6-clause MMU adequacy invariant ($\mathcal{I}_{\text{MMU}}$):** Inspecting every `PTW_Error` branch in `riscv/sail-riscv` (`vmem_ptw.sail`, `vmem.sail`) shows that flat-virtual SFI proofs lift soundly to S-mode Sv39/Sv48 execution only when code/arena/frame VAs are canonical, mapped by valid non-misaligned leaf PTEs with **`U = 0`** (S-mode fetch from `U = 1` always faults regardless of `sstatus.SUM`), **pre-set `A = 1` and writable `D = 1`** under `Svade`, PMP/PMA-accessible physical addresses, and physical disjointness between writable arenas and page-table/code/kernel frames across `satp`/`SFENCE.VMA`-free execution.

## Applicability

This report compares static bytecode analyzers, JIT refinement frameworks, and machine-code SFI checkers across the ten pinned subjects in `REPORT.json`:
- **Mechanized proof artifacts:** `uw-unsat/jitterbug@78d1e75a` (built on `uw-unsat/serval@72adc495`), `future-proof-iot/CertFC@75690097` (built on `AbsInt/CompCert@2685140b`), `gangtan/CPUmodels@a6decc30` (RockSalt), and `seL4/l4v@b0fe7693`.
- **Unmechanized C++/Rust/C static checkers:** `vbpf/ebpf-verifier@169eb5d6` (PREVAIL), `PLSysSec/veriwasm@60a64d27` (VeriWasm), and `lfi-project/lfi-verifier@8c3c4798` (LFI).
- **Authoritative ISA semantics:** `riscv/sail-riscv@76f1ce3c`.

Results govern sequential in-kernel bytecode VMs and bounded RISC-V / Arm64 / x86-64 sandboxes. General assembly framing (`asm!`, `Islaris`, `Kraken`, `s2n-bignum`, `Jasmin`, `Vale`) appears in `machine-code-verification-frameworks-and-assembly-contracts`.

## Findings

### 1. Comparative Architecture Matrix Across Verified Bytecode and Native SFI Checkers

Basis: source + documentation + derived

Table 1 contrasts how seven verification systems partition static checks, runtime guards, mechanized proofs, and trusted assumptions.

| System & Pin | Proof Substrate & TCB | Arena Confinement | Trap / Fault Absence | Host Register & Stack Frame | Termination / Fuel | Open Seam / Gap |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Jitterbug** (`uw-unsat/jitterbug@78d1e75a`, OSDI 2020) | Rosette / SMT over `Serval` (`rv64`, `rv32`, `arm64`, `arm32`, `x86_64`, `x86_32`) | `hybrid-memmgr` splits `stack-addr?` (host spills) from `heap-addr?` (external + carved BPF stack); assumes `heap-addr?` on `BPF_MEM` | Assumes upstream verifier guarantees non-zero `div`, bounded shifts, in-bounds jumps, and alignment (`#f` unaligned on RV64) | `rv64-arch-invariants` & `riscv-arch-safety` enforce `sp` and `ra,gp,tp,fp,s1..s11` equality on return | Does **not** verify guest loop termination; bounds tail calls at `MAX_TAIL_CALL_CNT` (`32`) | Trusts Linux BPF verifier for `verifier-preconditions`; Arm64 `arm64-arch-safety` omits `x24` (`L126-L133`) & caller havoc (`L170`) |
| **PREVAIL** (`vbpf/ebpf-verifier@169eb5d6`, PLDI 2019) | Unverified C++20 abstract interpreter (`SplitDBM` Zone + `TypeDomain` + `ArrayDomain`) | Relational `ValidAccess` over `T_STACK`, `T_CTX`, `T_PACKET`, `T_SHARED`, `T_SOCKET`, `T_ALLOC_MEM` + `ValidStore` | Static `ValidDivisor` (signed+unsigned 32-bit projections), `NonNull`, `TypeConstraint`, `ZeroCtxOffset` | Abstract eBPF registers `r0..r10` only; native prologue/epilogue delegated to unverified JIT | Bourdoncle WTO + `IncrementLoopCounter` + `BoundedLoopCount` (`counter <= limit`) | Unverified C++ transfer functions; no native target codegen |
| **Agni / Linux `tnum`** (CAV 2023, CGO 2022) | SMT (Z3 / Boolector) soundness proofs of kernel C operators | Verifies bitwise `tnum` `(value, mask)` and 32/64-bit min/max range transfer functions | Blocks range-pruning soundness bugs in pointer bounds checks | Out of scope | Out of scope (Linux caps explored states at `1M`) | Verifies isolated C operators, not whole-CFG fixpoints or JITs |
| **CertrBPF / CertFC** (`future-proof-iot/CertFC@75690097`, CAV 2022/2024) | Coq/Rocq spec -> synthesis -> CompCert `Clight` | **Runtime** SFI table `check_mem_aux2` translates integer addr to `Vptr b lo_ofs` or `Vnullptr` (`BPF_ILLEGAL_MEM`) | Runtime div-zero (`BPF_ILLEGAL_DIV`), shift (`BPF_ILLEGAL_SHIFT`), alignment, and `decode` checks + `bpf_verifier` | CompCert `Clight` ABI and CAV 2024 Thumb-2 JIT prologue/epilogue proofs | Structural `bpf_interpreter_aux (fuel: nat)` sets `BPF_ILLEGAL_LEN` (`val64_zero`) at `0` | Helper calls axiomatized via `call_inv_0..2` (`Isolation1.v:L28-L42`); CAV 2022 models interpreter (`CertFC`), CAV 2024 JIT targets Thumb-2 |
| **RockSalt** (`gangtan/CPUmodels@a6decc30`, PLDI 2012) | Coq/Rocq x86-32 RTL (`X86Semantics`) + NaCl DFA (`FastVerifier`) | Segment limits (`DS`/`SS`) + 32-byte chunk alignment (`NACLjmp` `and`-masking before indirect jumps) | `safeState_no_fail` proves every reachable step inside code bounds produces `Okay_ans` | `Same_Mach_State_Rel` preserves segment bases and non-sandbox code | **None** (`safeState_no_fail` is partial-correctness safety over `s ==>* s'`) | 6 DFA lemmas `Admitted` in `VerifierCorrectness.v:L79-L144`; relies on x86-32 segmentation |
| **VeriWasm** (`PLSysSec/veriwasm@60a64d27`, NDSS 2021) | Unverified Rust ELF binary dataflow checker (`yaxpeax_x86`) | `HeapBase + Bounded4GB + Bounded4GB` ($\le 8\text{ GiB}$), **relying on `PROT_NONE` guard pages to trap**; `probestack`/`stackgrowth` | Intentionally relies on `SIGSEGV` guard-page traps for OOB Wasm heap offsets | `LocalsChecker` tracks `UninitCalleeReg(r)` for `Rbx, R12..R15`; `StackChecker` requires `stackgrowth == 0` at `Stmt::Ret` | **None** (arbitrary loops allowed) | `Stmt::Call` `HeapBase` check commented out (`heap_checker.rs:L76-L93`); `8096` typo; `JG`/`JLE` flag bug; unsafe in kernel |
| **LFI** (`lfi-project/lfi-verifier@8c3c4798`, ASPLOS 2024) | Unverified C linear-scan decoder (`disarm64` / `fadec`) | Pins `x27` (`REG_BASE`) and enforces `[x27, wN, uxtw]` / `x28 = x27 + uxtw(wN)` + `4 GiB` guard pages | Rejects privileged ops, unguarded jumps, `RETAA`/`RETAB`, and unpredictable writeback | `fixedreg` forbids modifying `x27` (`REG_BASE`) and `x25` (`REG_CTX`); host runtime swaps context | **None** (native C/C++ control flow) | Uses faulting guard pages; permits `MRS`/`MSR` to `FPCR`/`FPSR`; `lfiv_verify_riscv64` returns `true` (`verify.c:L3-L6`) |

---

### 2. Memory-Arena Confinement: Static Relational Zones vs. Dynamic Capability Translation vs. Guard Pages

Basis: source + derived

Kernel sandboxes must confine all loads/stores to authorized `context`, `scratch` (stack), and `payload` (packet/map) arenas without relying on hardware page faults.

#### 2.1 PREVAIL's Typed Relational Zone Domain (`vbpf/ebpf-verifier@169eb5d6`)

`EbpfDomain` (`src/crab/ebpf_domain.hpp:L49-L160`) pairs `TypeToNumDomain state` (a register/cell `TypeDomain` bitset coupled with difference-bound constraints $x - y \le c$ in `SplitDBM`/`ZoneDomain`) with `std::optional<ArrayDomain> stack` maintaining `state.is_bottom() <=> !stack.has_value()` (`L154`). Every memory access checks `ValidAccess` in `EbpfChecker::operator()(const ValidAccess&)` (`src/crab/ebpf_checker.cpp:L505-L676`) across all enabled types in `dom.state.enumerate_types(s.reg)`:
- **`T_STACK` (`L513-L532`):** Requires `lb >= r10.stack_offset - subprogram_stack_size` and `ub <= total_stack_size`. Stack reads additionally check `dom.stack->all_num_lb_ub(...)` (or `w <= reg.stack_numeric_size - s.offset`) to block uninitialized stack/pointer disclosure. `ValidStore` (`L264-L268`) rejects storing non-`TS_NUM` values to any potentially non-`T_STACK` region, preventing kernel pointer leaks into `context`/`packet`/`shared`.
- **`T_CTX` (`L533-L577`):** Bounds `[lb, ub)` to `[0, ctx_size)`, requires `reg.ctx_offset == 0` when `context_access_requires_zero_offset` is active (`L535-L540`), rejects writes if `ctx_read_only` holds (`L572-L574`), and checks `write_may_touch_readonly_field` (`L71-L85, L543-L565`) so `data`, `end`, and `meta` pointer fields remain immutable.
- **`T_PACKET` (`L578-L595`):** Dereferences require `lb >= meta_offset` and `ub <= packet_size` (with `ptr_max` at `ebpf_domain.hpp:L28-L30` capping arithmetic below `int32_t::max() - max_packet_size` to avoid signed 64-bit wraparound), whereas pointer comparisons (`width == 0`) check `ub <= max_packet_size` (`L581-L590`).
- **`T_SHARED`, `T_ALLOC_MEM`, `T_SOCKET` (`L596-L645`):** `T_SHARED`/`T_ALLOC_MEM` check `[0, region_size)` and `uvalue > 0` (`require_non_null_or_zero_width`, `L154-L162`), while `T_SOCKET` restricts to read-only, constant-width, singleton-offset fields (`L57-L69, L616-L633`). `T_MAP`, `T_BTF_ID`, and `T_FUNC` fail closed on non-zero widths (`L656-L674`).

#### 2.2 Jitterbug's `hybrid-memmgr` & Assumed-Verifier Trust Seam (`uw-unsat/jitterbug@78d1e75a`)

Jitterbug (`racket/lib/hybrid-memory.rkt:L50-L77, L112-L184`) partitions target memory around `stackbase` and `stacksize`:
- **`stack-addr?` (`L54-L62`):** Addresses inside `[stackbase - stacksize, stackbase)` *minus* the guest `bpf-stack-range`. On RV64 (`racket/riscv/rv64/spec.rkt:L75-L86, L108-L114`), `stacksize = round_up(bpf_stack_depth, 16) + 64`, `bpf-stack-range = [-64 - round_up(bpf_stack_depth, 16), -64)`, and `[stackbase - 64, stackbase)` holds saved kernel `ra, fp, s1..s6`.
- **`heap-addr?` (`L68-L77`):** External memory union `bpf-stack-range`, emitting `load-event`/`store-event` trace entries (`L135-L180`); straddling accesses raise `core:bug` (`L137, L183`).

Crucially, `verifier-preconditions` (`racket/lib/spec/bpf.rkt:L208-L218`) **assumes** that every BPF memory access satisfies `(bvugt (bvadd addr size) addr)`, target alignment (`#f` unaligned on RV64 at `rv64/spec.rkt:L145`), and **`(heap-addr? mm addr size)`**. Thus Jitterbug proves kernel frame integrity *only* modulo soundness of the upstream static verifier; any range/tnum unsoundness (the defect class verified by Agni, `10.1007/978-3-031-37709-9_12`) invalidates `heap-addr?` and exposes saved `ra`/`fp` slots.

#### 2.3 CertrBPF's Dynamic Capability-Translating SFI Table (`future-proof-iot/CertFC@75690097`)

Without MMU hardware, CertrBPF enforces arena confinement dynamically in `check_mem_aux2` (`model/Semantics.v:L231-L261`) and proves CompCert safety in `isolation/CheckMem.v:L69-L166` and `isolation/IsolationLemma.v:L270-L483`. Scanning `bpf_mrs` (`memory_region` entries with `start_addr`, `block_size`, `block_perm`, `block_ptr = Vptr b 0`), `check_mem_aux2` computes `lo_ofs = addr -u start_addr` and checks: (1) `lo_ofs +u chunk <u block_size`, (2) `lo_ofs <=u max_unsigned - chunk`, (3) `lo_ofs %u chunk == 0`, and (4) `perm_ge mr_perm perm`. Valid checks mint a CompCert pointer capability `Vptr b lo_ofs` (`Semantics.v:L244`) satisfying `Mem.valid_access` (`CheckMem.v:L98-L166`, `check_mem_load`/`check_mem_store`); invalid ones return `Vnullptr` -> `BPF_ILLEGAL_MEM` (`Semantics.v:L285, L303`) with zero hardware page-fault risk.

#### 2.4 Guard-Page User-Space SFI (`VeriWasm` and `LFI`) vs. In-Kernel Requirements

User-space native SFI checkers convert out-of-bounds memory indexing into synchronous `SIGSEGV` faults via `PROT_NONE` guard pages, making them non-viable in trap-free kernel paths, and code inspection reveals concrete implementation bugs:
- **VeriWasm (`PLSysSec/veriwasm@60a64d27`):** `HeapChecker::check_heap_access` (`src/checkers/heap_checker.rs:L188-L248`) permits `[HeapBase + Bounded4GB + 0xffffffff]` (`L222-L242`) and `-0x1000` offsets (`L210, L215`), relying on `4 GiB` guard pages. Moreover: (1) the `Stmt::Call` check requiring `rdi == HeapBase` is commented out (`L76-L93`); (2) `check_ripconst_access` (`L156-L185`) trusts arbitrary computed offsets from `.rodata`/`.data` bases (`RIPConst`) in online single-function checks; and (3) `StackChecker::check_stack_read` / `check_bp_read` (`src/checkers/stack_checker.rs:L127, L133, L146, L151`) checks `< 8096` instead of `8192` ($8\text{ KiB}$).
- **LFI (`lfi-project/lfi-verifier@8c3c4798`):** On Arm64 (`src/arm64/verify.c:L71-L76, L377-L413, L485-L494`), loads/stores allow `[sp]`, `[x28]`, `[x27, wN, uxtw]`, or exact context offsets `[x25, #CTXREG_TP_OFFSET]` (`L389-L393`), with `x28` writable only via `add x28, x27, wN, uxtw` (`L486-L491`) over `4 GiB` guard pages, while `src/riscv64/verify.c:L3-L6` (`lfiv_verify_riscv64`) is an unimplemented `return true;` stub.

---

### 3. Trap and Synchronous-Fault Absence Across Bytecode and Bounded RISC-V / Arm64 Subsets

Basis: normative + source + derived

Non-trapping kernel execution requires proving every reachable instruction avoids synchronous exceptions:
1. **Division and Overflow:** x86-64 `div`/`idiv` raises `#DE` on zero divisor or `INT64_MIN / -1`, forcing runtime branches in JITs (`CertFC` `Semantics.v:L97-L142`) or static rejection in PREVAIL (`ValidDivisor`, `ebpf_checker.cpp:L233-L262`, where `may_be_zero_at_32_bits` checks *both* signed and unsigned 32-bit projections so `0x1_0000_0000` is rejected for `alu32` division). Conversely, **RISC-V M-extension** (`DIV`/`DIVU`/`REM`/`REMU`) and **Arm64** (`SDIV`/`UDIV`) never trap on division by zero or `INT_MIN / -1` (returning `-1`/dividend on RISC-V, `0`/`INT_MIN` on Arm64), removing architectural trap risk on those ISAs.
2. **Shift Ranges and `UNPREDICTABLE` Encodings:** eBPF forbids `shift >= 32/64` (`bpf.rkt:L174-L177`; `Semantics.v:L106-L113 -> BPF_ILLEGAL_SHIFT`), whereas RISC-V/Arm64 hardware masks shift amounts mod `XLEN`/`32`/`64`. Native Arm64 checkers must still reject `UNPREDICTABLE` register overlap: `lfi-verifier` (`src/arm64/verify.c:L577-L580`) explicitly rejects dual-output instructions (`mask == 0b11`) when `dinst.ops[0].reg == dinst.ops[1].reg`.
3. **Privileged, FP, and PAC Traps:** Bounded RISC-V subsets whitelist safe `RV64I/M/B/C` opcodes and exclude `SYSTEM` (`0x73`: `ECALL`, `EBREAK`, `SRET`, `MRET`, `WFI`, `CSR*`), `FENCE.I`, `AMO`, and FP/vector ops unless `mstatus.FS != 0b00` (`sail-riscv` `fdext_control.sail:L18-L20`). On Arm64, `lfi-verifier` (`src/arm64/verify.c:L163-L172, L260-L264, L281-L306`) rejects `RETAA`/`RETAB` (PAC fails on masked `x30`) and `SYS` (except `DC ZVA` on `x28`), but allows `MRS`/`MSR` on `FPCR`/`FPSR`—which traps in EL1 unless `CPACR_EL1.FPEN == 0b11`.
4. **Alignment Faults:** Targets with `#:have-efficient-unaligned-access #f` (`Jitterbug` `rv64/spec.rkt:L145`) or strict alignment (`CertrBPF` `Semantics.v:L242`) require static offset alignment proofs or byte-split load/store lowering.

---

### 4. Callee-Saved Kernel Register and Host-Stack Frame Preservation

Basis: source + derived

Kernel callers require invariant preservation of ABI callee-saved state (`{sp, gp, tp, fp/s0, s1..s11, ra}` on RV64; `{sp, x19..x30}` on AArch64; `{rsp, rbx, rbp, r12..r15, DF}` on x86-64) across all guest return paths:

1. **Syntactic Write-Set Exclusion (Zero-Spill Subsets & LFI):** Partition registers into `ReadOnlyFixed` (kernel ABI registers, arena base/limit registers, and `r_fuel`) and caller-saved scratch (`t0..t6, a0..a7` on RV64). Scanning decoded `rd` fields (`fixedreg` in `lfi-verifier` `src/arm64/verify.c:L137-L143, L448-L449` for `x27`/`x25`) establishes preservation with zero memory reasoning.
2. **Carved-Frame Prologue/Epilogue Simulation (Jitterbug `uw-unsat/jitterbug@78d1e75a`):** When guest programs use callee-saved registers (`s1..s4`), Jitterbug verifies `prologue-correctness` (`prologue.rkt:L87-L92`), per-instruction preservation of `rv64-arch-invariants` (`rv64/spec.rkt:L57-L94`: `ra, fp, s1..s6` backed in `[stackbase - 64, stackbase)`, `gp, tp, s7..s11` untouched, `sp = stackbase - stack_size`), and `epilogue-correctness` + `riscv-arch-safety` (`spec-common.rkt:L25-L38`: `sp == stackbase`, `pc == ra & ~1`, and equality of all 15 registers `(ra gp tp fp s1..s11)`).
   - **Arm64 Specification Gap (`racket/arm64/spec.rkt`):** `arm64-arch-safety` (`L126-L133`) checks `'(18 19 20 21 22 23 25 26 27 28 29 30)`—**omitting callee-saved `x24`** (also absent from `arm64-arch-invariants` `L94-L123`)—and `arm64-simulate-call` (`L170`) leaves `; FIXME: havoc caller-saved registers` unimplemented, unlike RV64's `(riscv:havoc-caller-saved! cpu)` (`rv64/spec.rkt:L48`).
3. **Symbolic Provenance Tracking Over Stack Spills (VeriWasm `PLSysSec/veriwasm@60a64d27`):** `LocalsChecker::regs_not_restored` (`src/checkers/locals_checker.rs:L78-L88, L152`) seeds `{Rbx, R12..R15}` with symbolic tag `UninitCalleeReg(r)`, propagates spills through stack slots, and enforces `regs[r] == UninitCalleeReg(r)` alongside `StackChecker`'s `stackgrowth == 0` at `Stmt::Ret` (`stack_checker.rs:L108-L115`). Note `locals_checker.rs:L142-L146` also contains a flag bug checking `Sf` twice while omitting `Zf` on `Opcode::JG | Opcode::JLE`.

---

### 5. Fuel-Bounded Termination: Acyclic PC Orderings, WTO Loop Counters, and Runtime Fuel Monads

Basis: source + derived

| Mechanism | Representative System | Runtime Cost | Expressiveness & Step Bound | Proof Obligations |
| :--- | :--- | :--- | :--- | :--- |
| **Forward Branch DAG** | Classic eBPF / Bounded RV64 subsets | `0` insns | $\le N_{\text{insns}}$ steps (`target_pc > pc`, no non-`ret` `JALR`) | Lexical decrease of `(code_end - pc)` |
| **WTO Relational Counters** | PREVAIL (`vbpf/ebpf-verifier@169eb5d6`) | `0` insns | Bounded loops (`counter <= BoundedLoopCount::limit`, `ebpf_checker.cpp:L276-L282`) | Soundness of Bourdoncle `_wto` + `IncrementLoopCounter` (`fwd_analyzer.cpp:L94-L145`) |
| **Fuel Monad (`fuel: nat`)** | CertrBPF (`future-proof-iot/CertFC@75690097`) | Per-insn decrement | Exact `fuel` steps (`BPF_ILLEGAL_LEN` -> `val64_zero`, `Semantics.v:L372-L403`) | Structural induction on `fuel` (`bpf_interpreter_preserving_inv`, `Isolation1.v:L204-L225`) |
| **Basic-Block Gas Metering** | Native RISC-V/Arm64 SFI with loops | `addi r_fuel, r_fuel, -k; bltz r_fuel, abort` at loop heads | $\le \text{fuel}_0 + \max_b |b|$ retired instructions | `r_fuel ∈ ReadOnlyFixed` for guest insns; positive block weight $k \ge 1$ per loop cycle |

Unlike Linux's exponential path-splitting instruction limit (`1M` explored states), PREVAIL's `_wto` relational counters (`fwd_analyzer.cpp:L94-L145`, `ebpf_domain.hpp:L84-L89`) bound loops in polynomial time. Conversely, RockSalt (`VerifierCorrectness.v:L3380-L3397`) proves only partial-correctness safety (`safeState_no_fail` over `s ==>* s'`) without termination, and Jitterbug bounds `BPF_TAIL_CALL` depth (`MAX_TAIL_CALL_CNT` in `bpf.rkt:L265, L282`) while trusting the verifier for intra-program loops.

---

### 6. Composing Flat-Virtual Sandbox Proofs Down to Operational Virtual-Memory ISA Semantics

Basis: normative + source + derived

Every checker in Table 1 verifies execution against a flat virtual memory $\text{Mem}_{\text{virt}} : \text{VAddr} \rightharpoonup \text{Byte}$. On an S-mode RISC-V (Sv39/Sv48) or EL1 AArch64 kernel CPU, every fetch, load, and store executes hardware page-table walks (`pt_walk` in `riscv/sail-riscv@76f1ce3c`, `model/sys/vmem.sail:L137-L260`) whose failures map to `PTW_Error` (`model/sys/vmem_ptw.sail:L16-L25, L70-L142`). Enumerating every `Err(...)` return in `vmem.sail` and `vmem_ptw.sail` (consistent with seL4 VSpace proofs in `seL4/l4v@b0fe7693`, `10.1007/978-3-642-03359-9_20`, `10.1007/s10817-019-09539-7`) yields the **exact 6-clause Kernel Virtual-Memory Adequacy Invariant ($\mathcal{I}_{\text{MMU}}$)** over the sandbox virtual footprint $\mathcal{V} = \mathcal{V}_{\text{code}} \cup \mathcal{V}_{\text{ctx}} \cup \mathcal{V}_{\text{scratch}} \cup \mathcal{V}_{\text{payload}} \cup \mathcal{V}_{\text{host}}$:

1. **Canonical Virtual Addresses (`¬PTW_Invalid_Addr`):** Every $va \in \mathcal{V}$ satisfies architectural sign-extension (`va[63..39] == sext(va[38])` in Sv39; `va[63..48] == sext(va[47])` in Sv48).
2. **Valid, Aligned Leaf PTEs (`¬PTW_Invalid_PTE ∧ ¬PTW_Misaligned`):** Under `satp`, `pt_walk` resolves every page covering $\mathcal{V}$ to a leaf PTE with `V = 1`, `¬(R = 0 ∧ W = 1)`, valid reserved/NAPOT bits, and superpage alignment `ppn[low_bits - 1 .. 0] == 0` (`vmem.sail:L222-L229`).
3. **Supervisor Privilege & `U = 0` Adequacy (`¬PTW_No_Permission`):** $\mathcal{V}_{\text{code}}$ has `X = 1`; readable arenas have `R = 1`; writable arenas ($\mathcal{V}_{\text{scratch}}$, writable $\mathcal{V}_{\text{payload}}$, $\mathcal{V}_{\text{host}}$) have `R = 1 ∧ W = 1`; and **every leaf PTE in $\mathcal{V}$ MUST have `U = 0`**, because in RISC-V S-mode, instruction fetch from a `U = 1` page unconditionally raises `E_Fetch_Page_Fault` even if `sstatus.SUM = 1`, and data access on `U = 1` pages faults whenever `sstatus.SUM = 0`.
4. **Pre-Set `A = 1` and Writable `D = 1` Under Software A/D (`Svade`, `¬PTW_PTE_Needs_Update`):** In `update_and_write_pte` (`vmem.sail:L95-L119`), whenever hardware A/D updates are disabled (`hw_updates_pte == false`), touching a leaf PTE with `A = 0` or writing one with `D = 0` returns `Err(PTW_PTE_Needs_Update())`, raising `E_Load_Page_Fault`/`E_SAMO_Page_Fault`/`E_Fetch_Page_Fault`. Hence $\mathcal{I}_{\text{MMU}}$ requires **`pte.A = 1` on all pages in $\mathcal{V}$ and `pte.D = 1` on all writable pages in $\mathcal{V}$** at sandbox entry (also eliminating implicit `Store(PageTableEntry)` side effects even under `Svadu`).
5. **Physical Memory & PMP Accessibility (`¬PTW_No_Access`):** All `read_pte` physical addresses (`vmem.sail:L67-L71`) and translated physical target addresses satisfy PMA and PMP permissions (`E_Load_Access_Fault`/`E_SAMO_Access_Fault`/`E_Fetch_Access_Fault` absent).
6. **Physical Disjointness & Translation Invariance ($\tau_{\text{MMU}}(\sigma') = \tau_{\text{MMU}}(\sigma)$):** The physical frames backing active page-table trees (`PTFrames(satp)`), `Code`, `Context`, and `HostSavedFrame` must be **disjoint** from the physical image $\tau(\mathcal{V}_{\text{scratch}} \cup \mathcal{V}_{\text{payload}}^{\text{rw}})$ of writable guest arenas (ruling out both page-table self-modification and cross-arena virtual aliasing). Since the bounded checker also forbids `satp`/`sstatus`/`menvcfg` CSR writes and `SFENCE.VMA`/`SINVAL.VMA`, $\tau_{\text{MMU}}$ is strictly invariant at every step, reducing Sv39/Sv48 operational refinement to flat-virtual safety.

## Boundaries

- **Speculative / transient execution (`known not to apply`):** None of the sequential bytecode/SFI models above or $\mathcal{I}_{\text{MMU}}$ establish Spectre-v1/v2 transient isolation on speculative CPUs; defending against speculative bounds bypass requires microarchitectural barriers (`lfence`, index masking, or pointer masking).
- **Concurrent multi-core shared-arena mutations (`unsupported` / `unknown`):** CertrBPF (`CertFC`) and Jitterbug (`hybrid-memmgr`) model sequential memory without concurrent shared writes (`unsupported`). Whether PREVAIL's sequential `T_SHARED` non-null invariants remain sound when concurrent kernel/user threads resize map backing buffers or race on non-atomic accesses is `unknown` from the single-thread abstract domain.
- **Mechanized TCB holes (`unsupported`):** RockSalt leaves six DFA lemmas `Admitted` (`VerifierCorrectness.v:L79-L144`), and CertrBPF axiomatizes external calls via `call_inv_0..2` (`Isolation1.v:L28-L42`); these remain unproved assumptions unless discharged.
- **Two-level hypervisor translation, IOMMU, and Arm64 MTE (`not examined`):** Guest/host two-level PTWs (`vmem.sail:L74-L88`), peripheral DMA IOMMU isolation, and Arm64 MTE tag checks were `not examined`.

## Evidence

### Primary Upstream Sources

1. **Jitterbug & Serval (`uw-unsat/jitterbug@78d1e75ad506498b585fbac66985ff9d9d05952d`, `uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`):**
   `racket/lib/hybrid-memory.rkt:L50-L77, L112-L184`; `racket/lib/spec/bpf.rkt:L147-L219, L251-L284`; `racket/lib/spec/prologue.rkt:L18-L94`; `racket/lib/spec/epilogue.rkt:L18-L74`; `racket/riscv/spec-common.rkt:L25-L39`; `racket/riscv/rv64/spec.rkt:L25-L162`; `racket/arm64/spec.rkt:L73-L173`.
2. **PREVAIL (`vbpf/ebpf-verifier@169eb5d6f48a59ffe4e902e977ae4e387f2b4e49`):**
   `src/crab/ebpf_domain.hpp:L28-L30, L49-L160`; `src/crab/ebpf_checker.cpp:L37-L85, L154-L162, L233-L282, L505-L697`; `src/fwd_analyzer.cpp:L94-L145, L190-L244`.
3. **CertrBPF / CertFC & CompCert (`future-proof-iot/CertFC@75690097c946c555cc4ce1e69d13ef86dc738180`, `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`):**
   `model/Semantics.v:L88-L182, L231-L314, L372-L403`; `isolation/CheckMem.v:L69-L166`; `isolation/IsolationLemma.v:L270-L483`; `isolation/Isolation1.v:L28-L42, L204-L225`; `isolation/VerifierInv.v:L52-L150`.
4. **RockSalt (`gangtan/CPUmodels@a6decc3085e1f8d8d4875e67f9ad9c7663910f8a`):**
   `x86model/RockSalt/VerifierCorrectness.v:L79-L144, L3344-L3398`.
5. **VeriWasm (`PLSysSec/veriwasm@60a64d279ecb676549aab51838d52b41ec6d1360`):**
   `src/checkers/heap_checker.rs:L75-L94, L156-L248`; `src/checkers/stack_checker.rs:L107-L194`; `src/checkers/locals_checker.rs:L78-L88, L130-L152`.
6. **LFI (`lfi-project/lfi-verifier@8c3c47983572039b138f8fa15c12231f2655bbef`):**
   `src/arm64/verify.c:L71-L90, L137-L172, L260-L306, L377-L413, L485-L494, L577-L610`; `src/riscv64/verify.c:L1-L6`.
7. **Sail RISC-V & seL4 (`riscv/sail-riscv@76f1ce3c184797178864b9869963e8b44465889e`, `seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`):**
   `model/sys/vmem_ptw.sail:L16-L25, L70-L142`; `model/sys/vmem.sail:L67-L260`; `model/extensions/FD/fdext_control.sail:L18-L20`.

### Peer-Reviewed Literature (DOIs)

- Luke Nelson et al., *Specification and verification in the field: Applying formal methods to BPF just-in-time compilers in the Linux kernel* (Jitterbug), OSDI 2020.
- Elazar Gershuni et al., *Simple and precise static analysis of untrusted Linux kernel extensions* (PREVAIL), PLDI 2019, DOI: `10.1145/3314221.3314590`.
- Harishankar Vishwanathan et al., *Verifying the Verifier: eBPF Range Analysis Verification* (Agni), CAV 2023, DOI: `10.1007/978-3-031-37709-9_12` (`tnum`, CGO 2022, DOI: `10.1109/CGO53902.2022.9741267`).
- Shenghao Yuan et al., *End-to-End Mechanized Proof of an eBPF Virtual Machine for Micro-controllers* (CertrBPF), CAV 2022, DOI: `10.1007/978-3-031-13188-2_15`; *End-to-End Mechanized Proof of a JIT-Accelerated eBPF Virtual Machine for IoT*, CAV 2024, DOI: `10.1007/978-3-031-65627-9_16`.
- Greg Morrisett et al., *RockSalt: Better, Faster, Stronger SFI for the x86*, PLDI 2012, DOI: `10.1145/2254064.2254111`.
- Evan Johnson et al., *Доверяй, но проверяй: SFI safety for native-compiled Wasm* (VeriWasm), NDSS 2021, DOI: `10.14722/ndss.2021.24078`.
- Zachary Yedidia, *Lightweight Fault Isolation*, ASPLOS 2024, DOI: `10.1145/3620665.3640408`.
- Rafal Kolanski, Gerwin Klein, *Types, Maps and Separation Logic*, TPHOLs 2009, DOI: `10.1007/978-3-642-03359-9_20`; Hira Taqdees Syeda, Gerwin Klein, *Formal Reasoning Under Cached Address Translation*, JAR 2020, DOI: `10.1007/s10817-019-09539-7`.
- Michael Sammler et al., *Islaris: Verification of Machine Code Against Authoritative ISA Semantics*, PLDI 2022, DOI: `10.1145/3519939.3523434`.

## Revalidation

Run the following read-only verification script against the pinned upstream revisions (or update revisions to `HEAD` to check whether `lfiv_verify_riscv64` and `arm64-arch-safety` have been completed):

```bash
python3 - <<'PY'
import subprocess

checks = [
    ("uw-unsat/jitterbug", "78d1e75ad506498b585fbac66985ff9d9d05952d",
     "racket/arm64/spec.rkt", ["'(18 19 20 21 22 23 25 26 27 28 29 30)", "FIXME: havoc caller-saved"]),
    ("uw-unsat/jitterbug", "78d1e75ad506498b585fbac66985ff9d9d05952d",
     "racket/lib/spec/bpf.rkt", ["(heap-addr? mm addr size)", "MAX_TAIL_CALL_CNT"]),
    ("vbpf/ebpf-verifier", "169eb5d6f48a59ffe4e902e977ae4e387f2b4e49",
     "src/crab/ebpf_checker.cpp", ["may_be_zero_at_32_bits", "BoundedLoopCount::limit"]),
    ("future-proof-iot/CertFC", "75690097c946c555cc4ce1e69d13ef86dc738180",
     "model/Semantics.v", ["Definition check_mem_aux2", "Fixpoint bpf_interpreter_aux"]),
    ("PLSysSec/veriwasm", "60a64d279ecb676549aab51838d52b41ec6d1360",
     "src/checkers/stack_checker.rs", ["< 8096"]),
    ("PLSysSec/veriwasm", "60a64d279ecb676549aab51838d52b41ec6d1360",
     "src/checkers/locals_checker.rs", ["UninitCalleeReg"]),
    ("lfi-project/lfi-verifier", "8c3c47983572039b138f8fa15c12231f2655bbef",
     "src/riscv64/verify.c", ["TODO: riscv verifier", "return true;"]),
    ("riscv/sail-riscv", "76f1ce3c184797178864b9869963e8b44465889e",
     "model/sys/vmem_ptw.sail", ["PTW_PTE_Needs_Update", "PTW_No_Permission"]),
]

for repo, sha, path, needles in checks:
    url = f"https://raw.githubusercontent.com/{repo}/{sha}/{path}"
    text = subprocess.check_output(["curl", "--http1.1", "-fsSL", url], text=True)
    for n in needles:
        assert n in text, f"Missing {n!r} in {repo}@{sha}:{path}"
    print(f"OK: {repo}@{sha[:8]}:{path}")
PY
```
