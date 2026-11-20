# Cryptographic Secret Erasure Across the MIR-to-Machine-ABI Seam: Callee-Saved Register Spills, Stack High-Water Scrubbing, and Interrupt-Masked Sandboxes

## Summary

Source-level and MIR-level memory zeroization primitives (`core::ptr::write_volatile`, `zeroize::Zeroize`, C23 `memset_explicit`) guarantee only that the final store to one named memory allocation survives dead-store elimination (DSE). They do **not** erase secret copies created by SSA register promotion, MIR by-value moves, LLVM `StackColoring` slot coalescing, ABI callee-saved register spills across downstream calls, or asynchronous interrupt trap-frame saves:

1. **Volatile Place Zeroization Misses Promoted Registers and Callee Spill Frames:** When a Rust function holds a secret scalar across an ordinary, non-cryptographic helper call and then zeroes the local via `write_volatile(&mut key, 0)`, LLVM promotes `key` into an ABI callee-saved register (`s0` on RV64, `x19` on AArch64, `%rbx` on x86-64) for its active live range and allocates a separate stack slot solely for the dead zero store (`sd zero, 8(sp)` / `str xzr, [sp, #8]` / `movq $0, 8(%rsp)`). If the helper needs that callee-saved register, its prologue spills the caller's secret onto the helper's stack frame (`sd s0, 16(sp)`) and its epilogue restores the register without scrubbing the save slot, stranding plaintext key material below `sp`.
2. **`-fzero-call-used-regs` Excludes Callee-Saved Registers and Stack Slots:** LLVM's `PEI::insertZeroCallUsedRegs` (`PrologEpilogInserter.cpp:1196-1335`) explicitly clears every register in `TRI.getCalleeSavedRegs(&MF)` from `RegsToZero` to preserve ABI calling conventions and never touches `MachineFrameInfo` stack objects. Even `-fzero-call-used-regs=all` on both caller and callee leaves callee-saved spill slots intact in the callee's dead frame.
3. **Epilogue Scrubbing Must Precede `sp` Deallocation After Callee-Saved Restoration:** Stack high-water-mark scrubbing (`GCC 14.2.0` `-fstrub` watermarks or machine-epilogue frame zeroing) requires a strict four-step partial order: (i) restore callee-saved registers (`ld s0..s11`), (ii) zeroize all dirty frame and save slots `[sp_min, sp_entry)` while `sp <= sp_min`, (iii) increment `sp := sp_entry`, and (iv) clear caller-saved scratch registers before `ret`. Zeroing save slots before restoring callee-saved registers corrupts caller state; incrementing `sp` before zeroing `[sp_min, sp_entry)` writes below `sp` on 0-byte-red-zone ABIs (`riscv64`, AAPCS64 `aarch64`), exposing secrets or corrupting asynchronous trap frames.
4. **Unmasked Interrupts (`sstatus.SIE = 1`) Exfiltrate Architectural Registers into Trap Stacks:** On RISC-V Supervisor systems (`entry.S:130-160`) and bare-metal `CSR_Interrupt` ISRs (`RISCVCallingConv.td:47-55`), any interrupt taken while secrets reside in `x1`–`x31`, `f0`–`f31`, or `v0`–`v31` copies the live register file into `pt_regs` on the kernel or interrupt stack before invoking nested C/Rust handlers. Complete architectural secret containment requires an interrupt-masked (`sstatus.SIE = 0`), bounded-WCET, call-spill-free sandbox that scrubs `[sp_min, sp_entry)` and all non-return registers *before* re-enabling `sstatus.SIE` (with `sstatus.FS = Off`, `sstatus.VS = Off` or explicit FP/vector scrubbing).

## Applicability

These findings govern the joint interaction of Rust MIR-to-LLVM lowering (`rust-lang/rust` `1.98.0-nightly` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `1.99.1` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`), LLVM backend prologue/epilogue and stack-coloring passes (`llvm/llvm-project` `19.1.0` @ `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4`), library zeroization (`RustCrypto/utils` `zeroize` @ `0feca06cf87e61567033a333feb79ecf3c427fea`), interprocedural compiler stack scrubbing (`gcc-mirror/gcc` `14.2.0` @ `04696df09633baf97cdbbdd6e9929b9d472161d3`), and target ABI / privilege specifications across:

- **RISC-V (`riscv64gc-unknown-none-elf`, `riscv64gc-unknown-linux-gnu`):** `lp64`/`lp64d` ABIs (`riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae`), RISC-V Supervisor privilege specification (`riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05`), and Linux `v6.12` trap entry (`torvalds/linux` @ `adc218676eef25575469234709c2d87185ca223a`).
- **AArch64 (`aarch64-unknown-none`, `aarch64-unknown-linux-gnu`):** Arm `AAPCS64` (`ARM-software/abi-aa` @ `ec3e2fb69065768aa1caf298813a7808b50bc264`).
- **x86-64 (`x86_64-unknown-linux-gnu`, `x86_64-pc-windows-msvc`):** System V AMD64 and Win64 register-preservation rules (`X86CallingConv.td`).
- **Formal Assembly & Mechanized Verification:** `jasmin-lang/jasmin` (`34f15840f10625bbc2cbf59b3d877e94c75bfbd9`) and `leanprover/lean4` (`v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`).

This package complements `compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences` (general DSE/CT preservation and Spectre fences) and `rust-stack-discipline-probes-red-zones-and-overflow` (prologue stack probing and red zones) by analyzing cross-call callee-saved spill propagation, epilogue `sp`-vs-scrub ordering, stack watermark scrubbers, and `sstatus.SIE = 0` containment. For multi-hart RISC-V PLIC interrupt ordering and MSRP ceilings around masked sandboxes, see `riscv-plic-priority-threshold-ordering-nested-sie-and-msrp-cross-hart-locking`.

## Findings

### 1. The MIR-to-ABI Erasure Gap: SSA Promotion, Stack Coloring, and Volatile Place Stores

Basis: normative + source + execution

In Rust (`compiler/rustc_codegen_ssa/src/mir/statement.rs:1-124`) and C, source-level zeroization libraries (`zeroize/src/lib.rs:278-285, 393-406` and `zeroize/src/barrier.rs:52-89`) prevent DSE on `&mut self` via `core::ptr::write_volatile` or bulk writes followed by an inline-assembly read barrier (`asm!("# {}", in(reg) ptr, options(readonly, preserves_flags, nostack))`). At the MIR-to-LLVM seam, this covers **only** the `alloca` backing `self` when `zeroize()` executes. Four compiler mechanisms replicate secrets outside that `alloca`:

1. **Address-Taken Split Between SSA Live Range and Dead Volatile Slot:** When `let mut local_key: u64 = *key_ptr;` has its address taken only at a trailing `write_volatile(&mut local_key, 0)`, SROA/`Mem2Reg` and register allocation keep `local_key` in a physical register across arithmetic and calls, materializing an 8-byte stack slot *exclusively* to receive the dead zero store. Compiling `crypto_caller_live_secret` (**Evidence §3**) with `rustc 1.98.0-nightly -C opt-level=2` emits:
   - **RV64 (`riscv64gc-unknown-none-elf`):** `ld s0, 0(a0)` loads the secret into `s0`; after `call innocent_helper` and `sub a0, a0, s0`, `volatile_store` emits `sd zero, 8(sp)`—zeroing an untouched stack slot while `s0` carried the secret across the call.
   - **AArch64 (`aarch64-unknown-none`):** `ldr x19, [x0]` loads the secret into `x19`; `volatile_store` emits `str xzr, [sp, #8]`, zeroing an untouched slot while `x19` holds the secret.
   - **x86-64 (`x86_64-unknown-linux-gnu`):** `movq (%rdi), %rbx` loads the secret into `%rbx`; `volatile_store` emits `movq $0, 8(%rsp)` while `%rbx` holds the secret.
2. **Rust By-Value Moves (`Operand::Move`) and Reallocation:** Moving a non-`Pin` secret value (`let s2 = s1;`, returning `Result<SecretKey, Err>`, or reallocating `Vec`) copies bytes from MIR place `_1` to `_2` before `StorageDead(_1)`. `ZeroizeOnDrop` zeroes `_2` while `_1`'s stack bytes remain unzeroed (`zeroize/src/lib.rs:167-180`; Simon, Chisnall & Anderson, EuroS&P 2018, DOI `10.1109/EuroSP.2018.00009`).
3. **Disjoint-Lifetime Slot Merging (`StackColoring.cpp`):** `StorageLive`/`StorageDead` lower to `llvm.lifetime.start.p0`/`llvm.lifetime.end.p0` (`statement.rs:78-96`). `llvm/lib/CodeGen/StackColoring.cpp` coalesces non-overlapping `FrameIndex` intervals onto shared stack offsets; an unzeroed secret temporary either persists in an unmerged slot or partially aliases a smaller subsequent public buffer.
4. **Anonymous Register-Allocator Spills (`RegAllocGreedy`):** When live values exceed physical registers, LLVM spills virtual registers via `MFI.CreateSpillStackObject` to anonymous `FrameIndex` slots unreachable from source pointers (`Vu et al., CC 2020`, DOI `10.1145/3377555.3377897`; `Vu et al., OOPSLA 2021`, DOI `10.1145/3485519`).

### 2. Cross-Architecture Callee-Saved Spill Leakage Across Innocent Helper Calls

Basis: normative + source + execution

Standard C and Rust ABIs split registers into caller-saved and callee-saved sets. Any secret live across a call to an ordinary helper (logging, formatting, slice/allocator checks, HAL reads) is preferentially assigned to a callee-saved register:

| Architecture / ABI | Normative & LLVM Source | Callee-Saved Integer GPRs | Callee-Saved FP / Vector Registers | ABI Red Zone | `SP` Align |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **RISC-V `lp64` / `lp64d`** | `riscv-cc.adoc:11-26, 79-94`; `RISCVCallingConv.td:16-28` | `s0`–`s1` (`x8`–`x9`), `s2`–`s11` (`x18`–`x27`) [12] | `lp64`: none; `lp64d`: `fs0`–`fs1` (`f8`–`f9`), `fs2`–`fs11` (`f18`–`f27`) [12] | `0 B` | `16 B` |
| **RISC-V `riscv_vector_cc`** | `riscv-cc.adoc:139-152`; `RISCVCallingConv.td:29-40` | `s0`–`s11` [12] | Same FPRs + `v1`–`v7`, `v24`–`v31` (base CC preserves `0` `v` regs) | `0 B` | `16 B` |
| **AArch64 `AAPCS64`** | `aapcs64.rst:838-899` | `x19`–`x28` + `x29` (`FP`) [11] (`x18` platform) | Low 64 bits (`d8`–`d15`) of `v8`–`v15`; bits `[127:64]` caller-saved | `0 B` (`128 B` Darwin, `16 B` Win64) | `16 B` |
| **x86-64 System V** | `X86CallingConv.td:1142` (`CSR_64`) | `rbx`, `rbp`, `r12`–`r15` [6] | None (`xmm`/`ymm`/`zmm` all caller-saved) | `128 B` (`[rsp-128, rsp)`) | `16 B` |
| **x86-64 `Win64`** | `X86CallingConv.td:1150-1155` | `rbx`, `rbp`, `rdi`, `rsi`, `r12`–`r15` [8] | `xmm6`–`xmm15` low 128 bits (`ymm`/`zmm` upper caller-saved) | `0 B` (`32 B` shadow above `ret`) | `16 B` |

**The Innocent-Callee Spill Witness:**
When `crypto_caller_live_secret` holds a secret in `s0` (RV64), `x19` (AArch64), or `%rbx` (x86-64) and calls `innocent_callee`—an unannotated public function making two indirect calls—`innocent_callee` (`rustc 1.98.0-nightly -C opt-level=2`) spills the caller's callee-saved register into its own stack frame, uses the register for public data, and restores the secret on exit:

```asm
# RISC-V RV64GC                         # AArch64 AAPCS64                       # x86-64 SysV
innocent_callee:                        innocent_callee:                        innocent_callee:
  addi  sp, sp, -32                       stp x30, x21, [sp, #-32]!               pushq %r15
  sd    ra, 24(sp)                        stp x20, x19, [sp, #16]  # SPILL!       pushq %r14
  sd    s0, 16(sp)   # SPILL!             mov x19, x2                             pushq %rbx        # SPILL!
  sd    s1, 8(sp)                         mov x20, x0                             movq  %rdx, %rbx
  sd    s2, 0(sp)                         blr x1                                  movq  %rdi, %r14
  ...                                     ...                                     ...
  ld    ra, 24(sp)                        ldp x20, x19, [sp, #16]  # RESTORE      popq  %rbx        # RESTORE
  ld    s0, 16(sp)   # RESTORE            sub x0, x8, x0                          popq  %r14
  ld    s1, 8(sp)                         ldp x30, x21, [sp], #32                 popq  %r15
  ld    s2, 0(sp)                         ret                                     retq
  addi  sp, sp, 32
  ret
```

Upon `ret`, even if `crypto_caller_live_secret` zeroes `s0`/`x19`/`%rbx` and scrubs its own frame `[sp_caller, sp_caller + 32)`, **an unzeroed 64-bit secret copy persists at `sp_caller - 16` (RV64), `sp_caller - 8` (AArch64), or `sp_caller - 32` (x86-64)** inside `innocent_callee`'s dead frame. Deeper calls propagate unused `s_k` secrets arbitrarily far down the stack. Consequently, unless the entire transitive call graph shares a verified stack-watermark scrubber (Finding 4), a MIR-to-ABI secret-erasure verifier must reject any call site `c` inside a secret sandbox with (1) `liveSecretScalars(c) != ∅` or (2) by-value secret arguments/returns in ABI registers (`Almeida et al., Jasmin, CCS 2017`, DOI `10.1145/3133956.3134078`; `Barthe, Grégoire & Laporte, CSF 2018`, DOI `10.1109/CSF.2018.00031`).

### 3. Why `-fzero-call-used-regs` Misses Callee-Saved Spills and Stack Frames

Basis: source + derived

Clang and GCC support `-fzero-call-used-regs=<kind>` (`skip`, `used-gpr-arg`, `used-gpr`, `used-arg`, `used`, `all-gpr-arg`, `all-gpr`, `all-arg`, `all`) to wipe call-clobbered registers before `ret`. Inspection of LLVM `19.1.0` `llvm/lib/CodeGen/PrologEpilogInserter.cpp:1159-1335` establishes four hard limits:

1. **Placement (`lines 1166-1172`):** `PEI::insertPrologEpilogCode` runs `TFI.emitEpilogue(MF, *RestoreBlock)` and then `insertZeroCallUsedRegs(MF)`.
2. **Return-Register Exclusion (`lines 1279-1323`):** Clears return operands (`a0`/`a1`, `x0`/`x1`, `rax`/`rdx`) and return-terminator uses (`ra`/`LR`) from `RegsToZero`.
3. **Unconditional Callee-Saved Exclusion (`lines 1325-1330`):**
   ```cpp
   // Don't clear registers that must be preserved.
   for (const MCPhysReg *CSRegs = TRI.getCalleeSavedRegs(&MF);
        MCPhysReg CSReg = *CSRegs; ++CSRegs)
     for (MCRegister Reg : TRI.sub_and_superregs_inclusive(CSReg))
       RegsToZero.reset(Reg);
   ```
4. **Zero Stack Coverage:** `TFI.emitZeroCallUsedRegs(RegsToZero, MBB)` emits only register-zeroing instructions; `MachineFrameInfo` objects (`CSI` save slots, spills, `alloca`s) are untouched.

Enabling `-fzero-call-used-regs=all` on *both* `crypto_caller_live_secret` and `innocent_callee` therefore still leaks `local_key`: `innocent_callee` excludes `s0`/`x19`/`%rbx` via `TRI.getCalleeSavedRegs` and leaves `16(sp)` unzeroed in its frame. Moreover, neither `rustc 1.98.0-nightly` nor `rustc 1.99.1` exposes `-fzero-call-used-regs` via CLI flags or attributes (`zeroize/src/lib.rs:192-195`).

### 4. Stack High-Water-Mark Scrubbing vs. Epilogue `SP`-Deallocation Ordering

Basis: source + derived

Erasing compiler spills and callee sub-frames requires scrubbing contiguous stack memory down to the minimum stack pointer (`sp_min`) reached during secret computation:

#### 4.1 Post-Call Sibling Allocation (`zeroize::zeroize_stack::<N>()`)
`RustCrypto/utils` (`zeroize/src/stack.rs:48-52`) defines `#[inline(never)] pub fn zeroize_stack<const N: usize>() { let buf = [0u8; N]; crate::optimization_barrier(&buf); }`. As `stack.rs:9-47` partially notes, this approach suffers four hazards: (1) LTO/CGU inlining of the inner sensitive function places `buf` below or disjoint from the secret frame; (2) static `N` either under-estimates spill depth or triggers `4 KiB` stack-probe loops (`rust-stack-discipline-probes-red-zones-and-overflow`); (3) an asynchronous preemption window exists between the inner `ret` (`addi sp, sp, +F`) and `zeroize_stack`'s prologue; and (4) caller-saved registers remain unscrubbed.

#### 4.2 Compiler Interprocedural Watermark Scrubbing (`GCC 14.2.0` `-fstrub`)
GCC `14.2.0` (`gcc/ipa-strub.cc`, `libgcc/strub.c:46-153`) threads `void **watermark` across strubbed call graphs: `__strub_enter` sets `*watermark = __builtin_frame_address(0)`, `__strub_update` sets `if (sp < *watermark) *watermark = sp`, and `__strub_leave` scrubs `[base, sp)` via `do *--end = 0; while (base < end); asm ("" : : "m" (base[0]));`. Two implementation guards in `libgcc/strub.c` are essential for any stack scrubber:
1. **Preventing Loop-to-`memset` Self-Clobber (`strub.c:88-90, 136-139`):** `__strub_leave` applies `-fno-tree-loop-distribute-patterns` when not allocating a dynamic VLA, because lowering the loop to `memset(base, 0, sp - base)` pushes `memset`'s own stack frame into `[base, sp)` and overwrites its own return address mid-scrub.
2. **Red-Zone Suppression vs. Below-`SP` Interrupt Hazard (`strub.c:69-83, 103-105, 123-134`):** An unreachable `asm goto` to `__strub_dummy_force_no_leaf()` prevents leaf red-zone locals on x86-64. However, without `TARGET_STRUB_USE_DYNAMIC_ARRAY`, `*--end = 0` writes *below* current `sp`; on RISC-V or AAPCS64 with unmasked interrupts, a trap arriving mid-loop pushes its `TrapFrame` below `sp` directly onto `[base, sp)`.

#### 4.3 Mandatory In-Epilogue Instruction Partial Order
In `RISCVFrameLowering.cpp:758-903`, `emitEpilogue` restores `CSI` registers from positive `sp` offsets before `addi sp, sp, StackSize` (`lines 851-855`). Verified epilogue erasure requires executing all four steps under masked interrupts in strict order:

$$\text{restoreCalleeReg}(r_i, s_i) \;\prec\; \text{zeroStackSlot}(s_i) \;\prec\; \text{popFrameSp} \;\prec\; \text{retInsn}$$

with $\text{zeroScratchReg}(r_j) \prec \text{retInsn}$ for all caller-saved $r_j \notin \{\text{publicRet}\}$:
- **`zeroStackSlot` before `restoreCalleeReg`:** Clobbers the caller's saved `s0`–`s11`/`ra` with `0` before `ld`, violating ABI preservation (`riscv-cc.adoc:166-168`).
- **`popFrameSp` before `zeroStackSlot`:** Leaves `[sp_old, sp_new)` unzeroed below `sp` on 0-byte-red-zone RV64/AAPCS64, exposing secrets or corrupting asynchronous trap frames.
- **`retInsn` before `zeroScratchReg`:** Leaks secret temporaries in `t0`–`t6` or unused `a1`–`a7`.

### 5. Interrupt-Masked (`sstatus.SIE = 0`) Secret-Erasure Sandboxes and Trap-Frame Containment

Basis: normative + source + derived

Even a call-free, spill-free cryptographic leaf function with a verified scrubbing epilogue **leaks secrets into RAM if preempted by an interrupt while secrets occupy architectural registers**:

1. **Trap-Frame Register Dump (`supervisor.adoc:51-125`, `entry.S:130-188`, `RISCVCallingConv.td:45-55`):**
   - When `sstatus.SIE == 1` (`supervisor.adoc:113-124`), any S-mode external or timer interrupt jumps to `stvec`. Linux `v6.12` (`.Lsave_context` in `arch/riscv/kernel/entry.S:130-160`) allocates `PT_SIZE_ON_STACK` (`288 B`) on the kernel stack and executes `REG_S x1`, `REG_S x3`, `REG_S x5`, and `save_from_x6_to_x31`, copying **all 31 GPRs** into `struct pt_regs` before `call do_irq` (`line 186`), where C handlers spill registers deeper into the IRQ stack without scrubbing on `sret`. Likewise, bare-metal `"riscv-interrupt"` ISRs (`CSR_Interrupt`, `RISCVCallingConv.td:47-55`) spill every used register across `X1, X5..X31` (and `F0..F31`) onto the ISR stack (see also Ge et al., EuroSys 2019, DOI `10.1145/3302424.3303976`; Van Bulck et al., CCS 2018, DOI `10.1145/3243734.3243822`).
2. **Six-Point Supervisor Secret-Erasure Sandbox Contract:**
   - **S1 (Mask `SIE` & Bound WCET):** Clear `sstatus.SIE` on entry (`csrrc s_saved, sstatus, 0x2`) and bound total cycles $C_{\text{sandbox}} \le \Delta_{\text{irq\_max}}$.
   - **S2 (FP / Vector Gate):** Require `sstatus.FS == 0b00` (`Off`) and `sstatus.VS == 0b00` (`Off`) (`supervisor.adoc:59-62`, trapping accidental FP/RVV instructions), or zero all touched `f0`–`f31`, `fcsr`, `v0`–`v31`, `vl`, `vtype`, and `vcsr` (`riscv-cc.adoc:108-127`).
   - **S3 (Closed Watermark Call Graph):** Either inline all helpers (`mirSandboxNoSpillCalls`: zero calls with live secrets or by-value secret ABI args/returns) or bound the closed static call tree's stack depth by $W$ bytes (`-Z emit-stack-sizes`).
   - **S4 (Pre-Pop Volatile Stack Scrub):** While `sstatus.SIE == 0` and `sp == sp_entry - W` (held allocated by an outer assembly trampoline if wrapping an inner core), restore `s0`–`s11`/`ra` first, then overwrite `[sp_entry - W, sp_entry)` with volatile `sd zero` stores *before* `addi sp, sp, +W`.
   - **S5 (Caller-Saved Wipe):** Zero `t0`–`t6`, `a1`–`a7` (and `a0` if unit return) after the last memory store.
   - **S6 (Restore `SIE`):** Restore `sstatus.SIE` from `s_saved & 0x2` (`andi t0, s_saved, 0x2; csrs sstatus, t0; mv t0, zero`) immediately before `ret`.

```text
  sp_entry  +-------------------------------+  <-- 16B-aligned entry SP
            | Trampoline saved ra / s0..s11 |  (restored BEFORE slot zeroing)
            +-------------------------------+
            | Inner locals + regalloc spills|  \  High-water region W bytes:
            | Closed-tree helper save slots |  /  zeroed WHILE sp == sp_floor & SIE == 0
  sp_floor  +-------------------------------+     strictly BEFORE sp += W
```

### 6. Mechanized Verification Model and Binary-Doubling Watermark Scaling

Basis: execution + derived

In Lean 4 (`v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`), mechanizing epilogue ordering and `4 KiB` (`512` 8-byte RV64 slots) watermark scrubbing via kernel reduction (`rfl`) hinges on two constructions:

1. **Decidable Epilogue Automaton (`stepIsaEpilogue`):** Partitioning RV64 registers into `fixedSystem = {0, 3, 4}`, `linkRa = {1}`, `stackSp = {2}`, `publicRetA0 = {10}`, `calleeSaved = {8, 9, 18..27}`, and `callerScratch = {5..7, 11..17, 28..31}` over state `(irqsMasked, spPopped : Bool)` and `(restoredRegs, dirtySlots, dirtyScratchReg : List Nat)` rejects all four ordering bugs by `rfl`: `popFrameSp` requires `irqsMasked && dirtySlots.isEmpty`; `restoreCalleeReg rId sId` requires `!spPopped`, `calleeSaved`, and `sId ∈ dirtySlots` (unclobbered prior to restore); `zeroStackSlot` requires `irqsMasked && !spPopped`; and `retInsn` requires `irqsMasked && spPopped && dirtySlots.isEmpty && dirtyScratchReg.isEmpty`.
2. **Strict-Pair Binary Doubling (`pow2`) vs. Call-by-Name `maxRecDepth`:** Certifying a `512`-slot (`4 KiB`) Patricia-tree (`PTree`) frame scrub via naive linear `@Nat.rec` fails Lean's `maxRecDepth = 512` at `256` slots (`2 KiB`). A naive binary-doubling step `fun _ ih st => let mid := ih st; ih (mid.1, mid.2)` *also* fails `maxRecDepth` at $d = 6$ (`64` slots), because call-by-name WHNF duplicates `ih st` across `.1`/`.2` and defers reduction to $2^d$ nested leaf frames. Eagerly matching the first half before invoking the second:
   ```lean
   def scrubRangePow2 (treeFuel d : Nat) (tr0 : PTree SlotResidue) (baseIdx : Nat) :
       (Nat × PTree SlotResidue) :=
     @Nat.rec (fun _ => (Nat × PTree SlotResidue) → (Nat × PTree SlotResidue))
       (fun st => match st with
         | (idx, tr) =>
           let r' := scrubSlot (PTree.getAt treeFuel tr idx)
           match idx + 1, PTree.setAt treeFuel tr idx r' with
           | idx', tr' => (idx', tr'))
       (fun _ ih st => match ih st with | (idx1, tr1) => ih (idx1, tr1))
       d (baseIdx, tr0)
   ```
   forces `(idx1, tr1)` to WHNF at each depth $k \in [0..d)$, bounding kernel WHNF stack depth to $O(d + \text{treeFuel}) \le 20$ frames and certifying a `512`-slot (`4 KiB`) RV64 page scrub via `rfl` in `~7.5 s` marginal kernel time (`~608 MiB` RSS).

## Boundaries

- **`known not to apply` — Source/MIR `write_volatile` and `-fzero-call-used-regs` for Full Erasure:** `core::ptr::write_volatile` (`zeroize::Zeroize`) is **known not to apply** to SSA-promoted registers, MIR move sources, `StackColoring`-merged slots prior to `zeroize()`, or callee-saved spills in downstream callees. `-fzero-call-used-regs=all` (`PrologEpilogInserter.cpp:1325-1330`) is **known not to apply** to `TRI.getCalleeSavedRegs(&MF)` or `MachineFrameInfo` stack slots.
- **`known not to apply` — `sstatus.SIE = 0` Against M-Mode Traps, NMIs, Page Faults, and Debug Halts:** Clearing `sstatus.SIE = 0` is **known not to apply** to non-delegated Machine-mode interrupts (`mstatus.MIE` / `mideleg = 0`, e.g., OpenSBI timer/IPI firmware traps), resumable NMIs (`Smrnmi`), synchronous page faults inside the sandbox (sandbox code and stack pages must be pre-faulted/pinned), or JTAG debug halts. M-mode firmware must scrub its own trap scratch frame if M-mode interrupts can preempt S-mode sandboxes.
- **`unsupported` — Compiler-Integrated Zeroization Attributes in `rustc` and Misaligned `-fstrub` Tails:** In `rustc 1.98.0-nightly` and `1.99.1`, `-fzero-call-used-regs`, `-fstrub`, and `[[clang::zeroize_on_return]]` are **unsupported** as `rustc` flags or attributes (`zeroize/src/lib.rs:192-195`). In GCC's `libgcc/strub.c:115-117`, scrubbing trailing sub-word bytes when `watermark` or `sp` is misaligned is **unsupported**.
- **`not examined` — Microarchitectural State and CHERI Capabilities:** Physical register file (PRF) rename remnants after hardware zero-idiom move elimination (`mv rd, zero` / `xor %eax, %eax`), L1D cache lines, store buffers, speculative execution windows (`compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences`), and CHERI capability registers (`c0`–`c31`) were **not examined**.
- **`unknown` — Cross-TU Callee-Spill Policy of Proposed LLVM `zeroize-stack`:** Because LLVM's `[[clang::zeroize_on_return]]` / `zeroize-stack` proposal is not merged in `llvmorg-19.1.0`, it remains **unknown** whether upstream LLVM will reject or watermark-wrap external non-LTO calls to prevent the innocent-callee `s0`/`x19`/`%rbx` spill leak in Finding 2.

## Evidence

### 1. Primary Upstream Source Code (Immutable 40-Char Revisions)
- **`llvm/llvm-project` @ `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4` (`llvmorg-19.1.0`):**
  - `llvm/lib/CodeGen/PrologEpilogInserter.cpp:1159-1335` (`PEI::insertPrologEpilogCode` and `PEI::insertZeroCallUsedRegs`, return-operand reset at `1280-1300`, `TRI.getCalleeSavedRegs` exclusion at `1325-1330`).
  - `llvm/lib/CodeGen/StackColoring.cpp:1-1352` (`LIFETIME_START`/`LIFETIME_END` slot coalescing).
  - `llvm/lib/Target/RISCV/RISCVCallingConv.td:16-67` (`CSR_ILP32_LP64`, `CSR_ILP32D_LP64D`, `CSR_V`, `CSR_Interrupt`).
  - `llvm/lib/Target/RISCV/RISCVFrameLowering.cpp:758-904` (`emitEpilogue` restore-before-`SPReg`-adjust order).
  - `llvm/lib/Target/X86/X86CallingConv.td:1141-1155` (`CSR_64`, `CSR_Win64`).
- **`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`) & `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`):** `compiler/rustc_codegen_ssa/src/mir/statement.rs:78-96` (`StorageLive`/`StorageDead` lowering).
- **`RustCrypto/utils` @ `0feca06cf87e61567033a333feb79ecf3c427fea`:** `zeroize/src/lib.rs:165-207, 278-285`, `zeroize/src/stack.rs:1-52`, `zeroize/src/barrier.rs:52-89`.
- **`gcc-mirror/gcc` @ `04696df09633baf97cdbbdd6e9929b9d472161d3` (`releases/gcc-14.2.0`):** `libgcc/strub.c:48-153` and `gcc/ipa-strub.cc:1-3629`.
- **`torvalds/linux` @ `adc218676eef25575469234709c2d87185ca223a` (`v6.12`):** `arch/riscv/kernel/entry.S:130-188` (`.Lsave_context` `save_from_x6_to_x31`) and `arch/riscv/include/asm/ptrace.h:1-185`.
- **`jasmin-lang/jasmin` @ `34f15840f10625bbc2cbf59b3d877e94c75bfbd9`:** Explicit `reg` vs `stack` storage classes in Jasmin.

### 2. Normative Specifications and Peer-Reviewed Literature
- **RISC-V ELF psABI (`riscv-non-isa/riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae`):** `riscv-cc.adoc:7-180`.
- **Arm AAPCS64 (`ARM-software/abi-aa` @ `ec3e2fb69065768aa1caf298813a7808b50bc264`):** `aapcs64/aapcs64.rst:819-908`.
- **RISC-V Privileged ISA (`riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05`):** `src/priv/supervisor.adoc:41-125`.
- L. Simon, D. Chisnall, R. Anderson, *"What You Get is What You C: Controlling Side Effects in Mainstream C Compilers"*, IEEE EuroS&P 2018, DOI: `10.1109/EuroSP.2018.00009`.
- G. Barthe, B. Grégoire, V. Laporte, *"Secure Compilation of Side-Channel Countermeasures: The Case of Cryptographic 'Constant-Time'"*, IEEE CSF 2018, DOI: `10.1109/CSF.2018.00031`.
- J. B. Almeida et al., *"Jasmin: High-Assurance and High-Speed Cryptography"*, ACM CCS 2017, DOI: `10.1145/3133956.3134078`.
- S. T. Vu, K. Heydemann, A. de Grandmaison, A. Cohen, *"Secure Delivery of Program Properties through Optimizing Compilation"*, ACM CC 2020, DOI: `10.1145/3377555.3377897`; and *"Reconciling Optimization with Secure Compilation"*, PACMPL (OOPSLA) 2021, DOI: `10.1145/3485519`.
- Q. Ge, Y. Yarom, T. Chothia, G. Heiser, *"Time Protection: The Missing OS Abstraction"*, ACM EuroSys 2019, DOI: `10.1145/3302424.3303976`.
- J. Van Bulck, F. Piessens, R. Strackx, *"Nemesis: Studying Microarchitectural Timing Leaks in Rudimentary CPU Interrupt Logic"*, ACM CCS 2018, DOI: `10.1145/3243734.3243822`.

### 3. Self-Contained Multi-Target Reproduction (`2026-11-20`)
Save to `/tmp/probe_repro.rs` and run with `rustc 1.98.0-nightly (14210df0e 2026-05-31)`:
```rust
#![feature(no_core, lang_items, rustc_attrs, intrinsics, auto_traits)]
#![no_core]

#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] unsafe auto trait Freeze {}
impl Copy for u64 {}
impl<T: PointeeSized> Copy for *mut T {}

#[rustc_intrinsic] pub unsafe fn volatile_store<T>(dst: *mut T, val: T);
#[rustc_intrinsic] pub unsafe fn unchecked_sub<T: Copy>(x: T, y: T) -> T;
extern "C" { fn innocent_helper(tag: u64) -> u64; }

#[no_mangle]
pub unsafe extern "C" fn crypto_caller_live_secret(key_ptr: *mut u64) -> u64 {
    let mut local_key: u64 = *key_ptr;
    let tag = innocent_helper(1);
    let mac = unchecked_sub(tag, local_key);
    volatile_store(&mut local_key as *mut u64, 0);
    mac
}

#[no_mangle]
pub unsafe extern "C" fn innocent_callee(
    pub_arg: u64, f1: extern "C" fn(u64) -> u64, f2: extern "C" fn(u64) -> u64
) -> u64 {
    let a = f1(pub_arg);
    let b = f2(a);
    unchecked_sub(unchecked_sub(a, b), pub_arg)
}
```
```bash
rustc --edition=2021 -C opt-level=2 -C panic=abort --crate-type=lib --target=riscv64gc-unknown-none-elf --emit=asm /tmp/probe_repro.rs -o /tmp/rv64.s
rustc --edition=2021 -C opt-level=2 -C panic=abort --crate-type=lib --target=aarch64-unknown-none --emit=asm /tmp/probe_repro.rs -o /tmp/aa64.s
rustc --edition=2021 -C opt-level=2 -C panic=abort -C llvm-args=--x86-asm-syntax=att --crate-type=lib --target=x86_64-unknown-linux-gnu --emit=asm /tmp/probe_repro.rs -o /tmp/x86.s
```

## Revalidation

1. **Re-run the 3-Target `#![no_core]` Spill Probe (`< 2 s`):** Run the three `rustc --emit=asm` commands above to verify whether `local_key` still promotes into `s0` / `x19` / `%rbx` across `innocent_helper` with a disconnected dead store (`sd zero, 8(sp)` / `str xzr, [sp, #8]` / `movq $0, 8(%rsp)`), and check `rustc -Z help | grep -iE 'zero|strub|scrub'` for newly added `rustc` flags.
2. **Diff `PrologEpilogInserter.cpp` and `RISCVFrameLowering.cpp`:** Check `PEI::insertZeroCallUsedRegs` and `emitEpilogue` for any `zeroize-stack` support, verifying whether `TRI.getCalleeSavedRegs(&MF)` remains excluded, whether slot zeroing sits strictly between `CSI` restoration and `SPReg` deallocation, and how external calls are gated.
3. **Disassembly Audit for `sstatus.SIE = 0` Sandboxes:** Verify via `llvm-objdump -d` that between `csrrc ..., sstatus, 2` and `csrs sstatus, ...`: `FS`/`VS` are off or scrubbed, zero external `call`/`jalr` instructions escape the static watermark, all `sd zero, k(sp)` stores satisfy `k >= 0` and precede `addi sp, sp, +W`, and all caller-saved scratch GPRs are cleared prior to `csrs sstatus` and `ret`.
