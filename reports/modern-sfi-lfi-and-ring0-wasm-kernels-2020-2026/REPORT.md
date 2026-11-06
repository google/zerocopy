# Modern Compiler/Binary-Verified SFI Kernels, Ring-0 WebAssembly Kernels, and Hardware-Assisted In-Kernel Sandboxes (2020–2026)

## Summary

Modern 64-bit Software Fault Isolation (SFI) and in-kernel WebAssembly sandboxes replace branch-based bounds checks and classic 32-byte instruction-bundle padding with hardware 32-bit zero-extension addressing (`[xBase, wIdx, uxtw]` on AArch64; `movl` + `(%r14, %rax)` or `%gs:(%eax)` `Segue` on x86-64) backed by unmapped virtual guard regions:

1. **Bundle-Free AArch64 Binary Verification (`lfi-project/lfi-verifier`, `lfi-project/lfi-runtime`, FMCAD 2025 `arXiv:2508.15898`)**:
   - Because AArch64 instructions are fixed 4-byte words that cannot decode at unaligned interior offsets, Lightweight Fault Isolation (LFI) eliminates instruction bundles and NOP padding on AArch64 (`0%` instruction-count and byte-size overhead on register-offset loads `ldr x0, [x27, w1, uxtw]`).
   - The production AArch64 ABI (`lfi-verifier` at `ecb5ff31b2deb83052a8f3dbad58bc6c595632f4`) migrated from the ASPLOS 2024 register set (`x21` base, `x18` address, `x22` scratch) to `x27` (`REG_BASE`), `x28` (`REG_ADDR`), `x26` (`REG_TEMP`), and `x25` (`REG_CTX`) to avoid colliding with the OS/kernel platform and `CONFIG_SHADOW_CALL_STACK` register `x18`.
   - `lfi-verifier` enforces a stateful link-register automaton (`v->x30_guarded`) that allows `x30` to hold unmasked values inside basic blocks (`ModifyX30Unchecked`) while requiring `add x30, x27, w30, uxtw` (`GuardX30Uxtw`) before any branch or return and at block exit. This register-masked return sequence (`ldr x30, [sp], #16; add x30, x27, w30, uxtw; ret`) is simultaneously immune to concurrent shared-memory stack TOCTOU races and preserves 100% hardware Return Stack Buffer (RSB) prediction accuracy (`register_masked_return_immune_to_stack_toctou` in [`support/ModernSfiAndWasmKernels.lean`](support/ModernSfiAndWasmKernels.lean)).
   - Soundness on AArch64 requires explicitly rejecting `CONSTRAINED UNPREDICTABLE` register overlaps on load-pair (`rt1 == rt2` in `ldp`) and pre/post-index writebacks (`rt == rn` in `[rn, #imm]!` / `[rn], #imm`), as implemented in `lfi-verifier/src/arm64/verify.c:494-524,573-577` and mechanized in `aarch64_ldp_overlapping_reg_unpredictable_hazard`.

2. **Negative-Offset Runtime Trampoline Placement (`[sandboxBase - 32, sandboxBase)`) vs. Page-0 KASLR Leaks (`lfi-runtime/core/box.c:94-123` vs. `lfi-research` and `jnwatson/kage`)**:
   - Placing the read-only host trampoline/metadata table at Page 0 (`[sandboxBase + 0]`, as in 2024 `lfi-research/liblfi/pal/ctx.c:36-65`) or in positive-offset read-only guest pages (`g2h_tramp_data` and `PROC_DATA` in `jnwatson/kage/security/kage/kage_main.c:221-255,1175-1224`) allows a verified unsigned load `ldr x0, [xBase, wIdx, uxtw]` to read raw 64-bit host runtime/kernel pointers into general-purpose registers, defeating ASLR/KASLR (`page0_trampoline_leaks_kaslr`).
   - Moving `struct Sys` to negative offsets `[sandboxBase - 32, sandboxBase)` (`lfi-runtime/core/box.c:94-123`) makes the trampoline table unreachable by any unsigned `[xBase, wIdx, uxtw]` load both architecturally and speculatively (`negative_offset_unreachable_by_uxtw`). However, source inspection of `lfi-verifier/src/arm64/verify.c:383-384,429-435` reveals an implementation asymmetry: `chkmemops` enforces destination register `x30` (`REG_RET`) for negative-offset loads through `x25` (`is_ctxreg_rtcall_load`) but omits the `ops[0].reg == REG_RET` check for `x27` (`rtsysreg`) when `--no-base-rtcalls` is not set. Full KASLR confidentiality requires both restricting the destination to `x30` and either pairing `ldur x30, [xBase, #-imm]` with an immediately adjacent `blr x30` lookahead or enforcing Position-Oblivious Code (`--poc`, `poc.c:43-44`) to forbid 64-bit reads of `x30` (`ldur_x30_with_mandatory_blr_prevents_gpr_leak_vs_unpaired_leak`).

3. **LFI x86-64 Dual-Bitmap Verification, `%gs` `Segue`, and Post-Link Prefix Padding (`lfi-verifier/src/x64/verify.c`, `lfi-rewriter/lfi-postlink/amd64.c`)**:
   - On x86-64, combining the `%gs` segment prefix (`0x65`) with the 32-bit address-size override prefix (`0x67`, `addr32`) confines `movq %gs:16(%eax), %rcx` (`65 67 48 8b 48 10`) to `[%gs_base, %gs_base + 2^32)` in a single instruction without zero-extension helper instructions.
   - `lfi-verifier/src/x64/verify.c:26-30,290-365,421-424` tracks two bitmaps (`bounds` for macroinstruction starts and `targets` for direct jump targets), allowing direct relative jumps to target any unaligned macroinstruction boundary (`(targets[w] & ~bounds[w]) == 0`) while restricting indirect jumps to 32-byte bundle boundaries (`lfi_x64_direct_and_indirect_branch_integrity`). Trailing bundle NOPs are eliminated before execution by `lfi-postlink/amd64.c:231-335`, which absorbs NOP byte counts as redundant `0x2e`/`0x65` segment prefixes on preceding instructions (`lfi_postlink_prefix_padding_preserves_32b_bundle`).

4. **Ring-0 WebAssembly Microkernels (`nebulet/nebulet`) vs. Verified Sandboxing Runtimes (`WaVe`, `Wasmachine`, `KSplit`, `Kage`)**:
   - Inspecting `nebulet/nebulet` (`a22b0198247ea0045b0f87aa31f849f8ffe15f66`) identifies four architectural soundness blockers in executing Cranelift-JITted WebAssembly directly in Ring 0 (`CPL = 0`) without hardware privilege rings or binary verification:
     1. **Unconfigured Interrupt Stack Table (`src/arch/x64/idt.rs:48-52`)**: Because Ring-0 interrupts (`CPL 0 -> CPL 0`) do not switch stacks unless an IST entry is set in the TSS/IDT, asynchronous interrupts push a 40-byte `ExceptionStackFrame` directly onto the Wasm thread's `RSP`, clobbering the 128-byte System V red zone (`ring0_interrupt_clobbers_redzone_without_ist`), double/triple-faulting when `RSP` is near the single 4 KiB stack guard page (`ring0_interrupt_boundary_double_fault_and_corruption`), or corrupting adjacent SIP memory. Configuring a dedicated IST stack restores isolation (`ring0_ist_restores_stack_isolation`).
     2. **Non-Unwinding Ring-0 Trap Exit Deadlocks Kernel Spinlocks (`src/abi/pfex.rs:8-37`, `src/object/thread.rs:138-152`)**: `pfex_acquire` locks `user_data.process.pfex_map().lock()` before dereferencing `vmctx.fastpath_offset_ptr(lock_offset)`. When `lock_offset` falls in the unmapped Wasm guard region, `#PF` invokes `Thread::exit()` without unwinding the Rust stack frame, permanently deadlocking `pfex_map` (`nebulet_pfex_trap_leaks_spinlock`). Replacing `#PF -> Thread::exit()` with a Linux-style `__ex_table` fault landing pad converts the guard-page `#PF` into an `Err(Error::FAULT)` return so RAII `Drop` releases `pfex_map.lock()` (`ring0_extable_landing_pad_preserves_pfex_lock_freedom`).
     3. **Shared Linear-Memory Bytecode TOCTOU (`src/abi/process.rs:66-76`)**: `wasm_compile` comments out `wasm_bytecode.to_vec()`, validating and compiling a live `&[u8]` slice aliasing mutable Wasm linear memory.
     4. **6 GiB vs. 8 GiB Guard Size Discrepancy (`src/memory/sip.rs:57,133`)**: `DEFAULT_GUARD_SIZE` is `2 GiB` (`1 << 31`) rather than 4 GiB; if 32-bit static offsets $K \ge 2^{31}$ elide software bounds checks, $\mathtt{base} + (2^{32}-1) + (2^{31}+1)$ escapes the 6 GiB SIP slot (`nebulet_2gib_guard_escape_if_offset_unbounded`).

5. **Speculative Execution Confinement (`uxtw` / `movl` / `addr32` vs. Branch-Checked Bounds Guards)**:
   - Branch-checked bounds guards (`if idx < 2^32`) are control dependencies that fail under Spectre v1 (PHT) misprediction unless paired with pipeline-serializing barriers (`lfence` / `csdb`, `branchChecked_spectre_v1_leaks_host_secret` and `branchCheckedWithFence_speculatively_confined`).
   - Hardware 32-bit zero-extension (`uxtw`, `movl`, `addr32`) enforces a data-path bit truncation in the ALU/AGU with no conditional branch, confining both architectural and transient memory accesses to $[\mathtt{sandboxBase}, \mathtt{sandboxBase} + 2^{32})$ under all branch-predictor oracles (`uxtw_speculatively_confined_for_all_oracles` and `uxtw_never_reads_outside_sandbox`).

---

## Applicability

- **Subjects and Relationship**:
  - This report compares and synthesizes static machine-code SFI verifiers and runtimes (**LFI** across `lfi-project/lfi-verifier@ecb5ff31b2deb83052a8f3dbad58bc6c595632f4`, `lfi-project/lfi-runtime@3b78c956368eb78d5d2241cec5d650e13f57f5cb`, `lfi-project/lfi-rewriter@1389430d371cf614e1d3ff8f7487d54d560692d9`, `lfi-project/lfi@749401bc68463ffaee2349ae9e37731ece8eda5d`, `lfi-project/lfi-specification@1a44e55c839f79df2e207639a9f0272038302b3f`, and `zyedidia/lfi@70f7c9e1ea905eb79f3e440506d7a8286ad7ec53`), in-kernel Linux driver sandboxes (**Kage** `jnwatson/kage@5583be54dfa35b74a3860a43fc89cb034a2184bc` and **KSplit** OSDI 2022), and Ring-0 / verified WebAssembly runtimes (**Nebulet** `nebulet/nebulet@a22b0198247ea0045b0f87aa31f849f8ffe15f66`, **Wasmachine** `arXiv:2011.09265v1`, and **WaVe** IEEE S&P 2023) to inform machine-code SFI certificate kernel design for **Anneal** (`joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`).
  - All formal theorems in [`support/ModernSfiAndWasmKernels.lean`](support/ModernSfiAndWasmKernels.lean) are checked with **Lean 4** (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, version `v4.34.1`) with zero warnings and zero non-standard axioms (`0 sorryAx`, `0 Classical.choice`, `0 Lean.ofReduceBool`).
- **Target Architectures and Operating Modes**:
  - **AArch64 (ARMv8-A / ARMv8.5-A)**: Applies to fixed-width 32-bit little-endian AArch64 instruction streams verified by `lfiv_verify_arm64` in full sandboxing mode (`LFI_BOX_FULL`), stores-only mode (`LFI_BOX_STORES`), jumps-only mode (`LFI_BOX_JUMPS`), position-oblivious code mode (`--poc`), and Linux 6.6 kernel module sandboxing (`CONFIG_SECURITY_KAGE`, `CONFIG_SHADOW_CALL_STACK`).
  - **x86-64 (AMD64 / Intel 64)**: Applies to 32-byte bundle-aligned x86-64 code streams verified by `lfiv_verify_x64` (`%r14` base register and/or `%gs` + `addr32` `Segue` mode) and Ring-0 (`CPL = 0`) 64-bit kernel execution in `nebulet`.

---

## Findings

### 1. Lightweight Fault Isolation (LFI) on AArch64 and x86-64

`Basis: normative specification + source + execution + derived`

#### 1.1 AArch64 Register ABI Evolution (`2024 lfi-research` vs. `2025–2026 lfi-verifier` & `Kage`)

Direct comparison of `lfi-project/lfi@749401bc68463ffaee2349ae9e37731ece8eda5d` (`lfi-verify/arm64/verify.c:57-64`, `lfi-leg/arm64/addr.leg`) against `lfi-project/lfi-verifier@ecb5ff31b2deb83052a8f3dbad58bc6c595632f4` (`src/arm64/verify.c:69-74`) and `jnwatson/kage@5583be54dfa35b74a3860a43fc89cb034a2184bc` (`security/kage/runtime.S:27-32,108-113`) shows a deliberate ABI migration:

| Register Role | `lfi-research` (2024) | `lfi-verifier` & `Kage` (2025–2026) | Verifier & Runtime Invariant |
| :--- | :--- | :--- | :--- |
| **Sandbox Base (`REG_BASE`)** | `x21` (`21`) | `x27` (`27`) | Immutable 4 GiB-aligned base pointer ($\mathtt{sandboxBase} = b \cdot 2^{32},\; b \ge 1$); rejected as a modified operand (`fixedreg(v, reg) == true`, `src/arm64/verify.c:135-141`). |
| **Sandboxed Address (`REG_ADDR`)** | `x18` (`18`) | `x28` (`28`) | Modified only via `add x28, x27, wN, uxtw` (`src/arm64/verify.c:483-489`). Always holds an address in $[\mathtt{x27}, \mathtt{x27} + 2^{32})$ (or within the unmapped guard zone upon writeback fault). |
| **Compiler Scratch (`REG_TEMP`)** | `x22` (`22`) | `x26` (`26`) | Holds intermediate 32-bit address calculations and preserves `w30` across runtime trampoline calls (`lfi-leg/arm64/syscall.leg:9-13`). |
| **Context Pointer (`REG_CTX`)** | `x25` (`25`) | `x25` (`25`) | Fixed register (`fixedreg`); permits only 64-bit `ldr/str xN, [x25, #16]` (`CTXREG_TP_OFFSET`) and runtime call loads `ldur x30, [x25, #-imm]` (`imm ∈ {8, 16, 24, 32}`, `src/arm64/verify.c:324-344,387-391,429-435`). |
| **Stack Pointer (`sp`)** | `sp` (`31`) | `sp` (`31`) | Modified only via `add sp, x27, wN, uxtw` (`src/arm64/verify.c:483-489`) or bounded pre/post-index writeback on a memory access. |
| **Link Register (`REG_RET`)** | `x30` (`30`) | `x30` (`30`) | Tracked by the stateful `v->x30_guarded` boolean across basic blocks (`src/arm64/verify.c:21,111-133,234-277,451-481,600-603`). |
| **OS Platform / Shadow Call Stack (`x18`)** | Used as `REG_ADDR` | Reserved (`x18` untouched by guest) | Moving `REG_ADDR` from `x18` to `x28` frees `x18` for Android, macOS, and the Linux kernel's `CONFIG_SHADOW_CALL_STACK` (`kage/security/kage/runtime.S:28,108-113`). |

#### 1.2 Bundle-Free AArch64 Verification Rules and Stateful `x30_guarded` Tracking

In `lfi-verifier/src/arm64/verify.c:526-606` (`vchk` and `lfiv_verify_arm64`), verification proceeds in a single $O(N)$ linear pass over 4-byte instructions without instruction bundles:

1. **Two-Tier Memory Confinement (`okmemop`, `verify.c:375-411`)**:
   - **Single-instruction `uxtw` register offset (`DA_OP_MEMREG`, `verify.c:398-402`)**: Accepts `[xBase, wN, uxtw #0]` (`basereg(op->reg) && op->memreg.ext == DA_EXT_UXTW && op->memreg.sc == 0`). Requiring `sc == 0` blocks scaled offsets (`uxtw #1..#4`) that would multiply the 32-bit index by $2, 4, 8,$ or $16$ and escape the 4 GiB arena.
   - **Displacement and writeback addressing via `x28` or `sp` (`DA_OP_MEMUOFF`, `DA_OP_MEMSOFF`, `DA_OP_MEMSOFFPRE`, `DA_OP_MEMSOFFPOST`, `verify.c:378-397`)**: Immediate offsets (`ldr x0, [x28, #imm]`, `ldp x0, x1, [sp, #16]!`) are permitted only on `x28` (`REG_ADDR`) or `sp` (`31`), while register post-index (`DA_OP_MEMREGPOST`, e.g., `ldr x0, [x28], x1`) is unconditionally rejected (`verify.c:402-403`).
   - **Why Pre/Post-Index Writeback Without Re-Masking Is Sound (`preIndex_writeback_confined_or_traps_in_guard` in [`support/ModernSfiAndWasmKernels.lean`](support/ModernSfiAndWasmKernels.lean), lines 495–512)**: Because AArch64 pre/post-indexed instructions (`ldr dst, [x28, #imm]!`, `|imm| <= 256`) perform a memory access simultaneously with updating `x28`, and `[sandboxBase - guardSize, sandboxBase)` / `[sandboxBase + 2^32, sandboxBase + 2^32 + guardSize)` (`guardSize >= 80 KiB`) are unmapped (`PROT_NONE`), the first writeback that pushes `x28` or `sp` outside `[sandboxBase, sandboxBase + 2^32)` faults inside the unmapped guard zone before any subsequent instruction can accumulate a second displacement.
2. **Stateful `x30_guarded` Automaton (`verify.c:234-277,451-481,600-603`)**:
   - The verifier initializes `v.x30_guarded = true` (`verify.c:589`).
   - Any modification to `x30` other than `add x30, x27, wN, uxtw` (`is_x30_guard`, `verify.c:112-122`), `ldr/ldur x30, [x27, #imm]` (`verify.c:458-470`), or `ldur x30, [x25, #-imm]` (`is_ctxreg_rtcall_load`, `verify.c:474-477`) sets `v->x30_guarded = false` (`verify.c:479`). Furthermore, in `--sandbox=stores` or `--sandbox=jumps` mode, any pre/post-index writeback using `x30` as the base register sets `v->x30_guarded = false` (`verify.c:507-511`, tested by `test/arm64/fail.s:204-229`).
   - Every direct or indirect branch (`DA64G_BRANCH`, `DA64G_BCOND`, `DA64G_BRANCHREG`, `DA64G_CBZ`, `DA64G_TBZ`, `DA64I_BR`, `DA64I_BLR`, `DA64I_RET` in `chkbranch`, `verify.c:234-277`) and end-of-buffer check (`verify.c:601-603`) requires `v->x30_guarded == true`.
   - Pointer-authenticated returns (`retaa`, `retab`, `verify.c:258-262`) are explicitly disallowed because `add x30, x27, w30, uxtw` strips upper PAC signature bits; instead, `autiasp` must precede `add x30, x27, w30, uxtw; ret` (`test/arm64/pass.s:125-130`).
   - We mechanized this stateful verifier and proved single-step and full-block soundness in `lfiVerifyStepStateful_sound` (lines 313–424) and `lfiVerifyBlock_sound` (lines 449–461) of [`support/ModernSfiAndWasmKernels.lean`](support/ModernSfiAndWasmKernels.lean).

#### 1.3 Rejection of AArch64 `CONSTRAINED UNPREDICTABLE` Overlapping-Register Encodings

`Basis: normative specification + source + execution`

In the ARMv8-A Architecture Reference Manual (Section K1.2.5), instruction encodings that modify the same register twice (`ldp Xt1, Xt2, [Xn]` with `t1 == t2`, or `cas`/`casp` pair overlaps) or that use a loaded/stored register as the writeback base register (`ldr Xt, [Xn, #imm]!` or `stp Wt1, Wt2, [Xn], #imm` with `t == n` and `n != 31`) have `CONSTRAINED UNPREDICTABLE` semantics: hardware may write `UNKNOWN` 64-bit values to the overlapping registers or perform unspecified writebacks.

- In `lfi-verifier/src/arm64/verify.c:573-577`, `vchk` rejects simultaneous register modification whenever `nmod(&dinst) == 0b11`:
  ```c
  if (mask == 0b11 && dinst.ops[0].reg == dinst.ops[1].reg)
      verr(v, &dinst, "simultaneous modification of the same register is unpredictable");
  ```
- In `lfi-verifier/src/arm64/verify.c:494-524`, `chkwriteback` rejects any pre/post-indexed instruction where a general-purpose operand `op->reg` matches the writeback base register `memreg` (`op->reg == memreg && op->reg != 31`, tested in `test/arm64/fail.s:29-30,71-82`).
- Theorem `aarch64_ldp_overlapping_reg_unpredictable_hazard` ([`support/ModernSfiAndWasmKernels.lean`](support/ModernSfiAndWasmKernels.lean), lines 1192–1237) proves that without this check, `ldp x0, x0, [x28]` (`fail.s:71-72`) enters `isArm64ConstrainedUnpredictable = true` and can corrupt `x21Base`, whereas `lfiVerifyLdpWb` guarantees `isArm64ConstrainedUnpredictable = false` and preserves `x21Base = sandboxBase`.

#### 1.4 Negative-Offset (`[sandboxBase - 32, sandboxBase)`) vs. Page-0 Trampoline Placement & Verifier Asymmetry

`Basis: source + execution + derived`

Across the three examined LFI implementations, host runtime trampoline pointers (`struct Sys` / `g2h_tramp_data`) are placed in three distinct virtual memory layouts with sharply different KASLR confidentiality properties:

1. **Page-0 Placement (`lfi-project/lfi@749401bc68463ffaee2349ae9e37731ece8eda5d`, `liblfi/pal/ctx.c:28-66`)**:
   - `sysalloc` maps `struct Sys` at `[base, base + pagesize)` (`PROT_READ`), storing `&lfi_syscall_entry`, `&lfi_get_tp`, `&lfi_set_tp`, `&lfi_ret`, and `base` at `[base + 0 .. base + 32]`.
   - Theorem `page0_trampoline_leaks_kaslr` ([`support/ModernSfiAndWasmKernels.lean`](support/ModernSfiAndWasmKernels.lean), lines 1057–1067) proves that `LoadUxtw .r0 idxReg` (`ldr x0, [x21, wIdx, uxtw]`) with `st.gpr idxReg = 0` passes verification and copies `st.mem sandboxBase = hostRuntimePtr` into `Gpr.r0`, leaking host runtime pointers.
2. **In-Sandbox Read-Only Literal Pool & `PROC_DATA` Placement (`jnwatson/kage@5583be54dfa35b74a3860a43fc89cb034a2184bc`, `security/kage/kage_main.c:221-255,1046,1175-1224`)**:
   - Kage allocates `kage->g2h_tramp_data` (containing raw host kernel pointers `const struct kage_g2h_call *call` and `unsigned long stub`) and per-invocation `PROC_DATA` (`guest_stack_end`, containing `struct kage_proc *lfiproc` at `[guest_stack_end + 0]`, `security/kage/runtime.S:6-18`) inside `[kage->base + 84 KiB, kage->base + 4 GiB)` with read-only page permissions (`set_memory_ro`). Any sandboxed `ldr x0, [x27, wIdx, uxtw]` addressing those offsets reads raw host kernel text and `kzalloc` pointers into `x0`.
3. **Negative-Offset `sys_page` Placement (`lfi-project/lfi-runtime@3b78c956368eb78d5d2241cec5d650e13f57f5cb`, `core/box.c:58-123,190-198`)**:
   - `syssetup` (`core/box.c:94-123`) maps `box->sys_page` at `box->base - pagesize` (`PROT_READ`) and places `struct Sys` (`32` bytes) at the end of that page: `(char *) box->sys_page + pagesize - sizeof(struct Sys) = [box->base - 32, box->base)` (or `[ctxreg - 32, ctxreg)` when `ctxreg` is enabled, `box.c:71-90`). Meanwhile, `[box->base, box->base + min_off)` (`min_off = max(BOX_INTERNAL_GUARD, pagesize)`, `box.c:190-198`) is unmapped (`PROT_NONE`).
   - Theorem `negative_offset_unreachable_by_uxtw` (lines 1076–1084) proves that for all `negImm > 0` with `negImm ≤ sandboxBase` and all `idxVal`, $\mathtt{sandboxBase} - \mathtt{negImm} < \mathtt{sandboxBase} + \mathrm{zext32}(\mathtt{idxVal})$, so no unsigned `uxtw` data load can address `[sandboxBase - 32, sandboxBase)` architecturally or speculatively.
   - **Verifier Asymmetry in `lfi-verifier/src/arm64/verify.c:383-384,429-435`**:
     - For `x25` (`REG_CTX`), `chkmemops` (`verify.c:429-435`) calls `is_ctxreg_rtcall_load` (`verify.c:337-344`), enforcing `dinst->mnem == DA64I_LDURX && dinst->ops[0].reg == REG_RET` (`x30`) and rejecting `ldur x0, [x25, #-8]` (`test/arm64/fail.s:191-192`).
     - For `x27` (`REG_BASE`, when `--no-base-rtcalls` is not set), `okmemop` (`verify.c:383-384`) allows `[x27, #-imm]` (`imm ∈ {-8, -16, -24, -32, 0, 8, 16, 24}`), and `chkmemops` omits the `dinst->ops[0].reg == REG_RET` check for `x27`, allowing `ldur x0, [x27, #-8]`.
     - Furthermore, as proven in `ldur_x30_with_mandatory_blr_prevents_gpr_leak_vs_unpaired_leak` (lines 1116–1131), preventing a sandboxed module from copying the loaded host entrypoint out of `x30` (`ldur x30, [x25, #-8]; mov x0, x30`) requires either a two-instruction lookahead (`ldur x30, [xBase/xCtx, #-imm]` immediately followed by `blr x30`, which overwrites `x30 := pc + 4`) or LFI's `--poc` mode (`lfi-verify/arm64/poc.c:43-44`), which forbids reading 64-bit values (`sf == 1`) from reserved/address registers (`x21`/`x27`, `x25`, `x18`/`x28`, `x30`, `sp`).

#### 1.5 Asynchronous Signal Sanitization & RSB-Preserving Return Sequences

`Basis: source + execution + derived`

1. **Host Signal Stack Isolation (`lfi-runtime/core/core.c:152-186`)**:
   - `lfi_init_sigaltstack` allocates a host stack via `malloc(SIGSTKSZ)` and registers it with `sigaltstack` before `lfi_ctx_run` (`core/ctx.c:70`), ensuring POSIX signal frames are never pushed onto the sandbox's `sp`.
2. **Context Restoration When `x30_guarded == false` (`async_signal_restore_requires_x30_remask`, lines 1348–1357)**:
   - Because `lfi-verifier` allows `x30` to be unmasked between `ldr x30, [sp], #16` and `add x30, x27, w30, uxtw`, an interrupt or guest-to-host call saving `x30` during that window records an unmasked `x30`. In `jnwatson/kage/security/kage/runtime.S:36-51`, `lfi_restore_partial_regs` explicitly executes `add x30, x27, w30, uxtw; ret` before returning to the guest, confining the resumed `PC` to `[sandboxBase, sandboxBase + 2^32)`.
3. **Return Sequence Comparison (`register_masked_return_immune_to_stack_toctou`, lines 1300–1328)**:
   - **In-place stack masking (`stackInPlaceMaskedReturn`, `andl $0xffffffe0, (%rsp); addl %r14d, 4(%rsp); ret`)**: Vulnerable to a concurrent thread overwriting `(%rsp)` in shared memory between the mask store and the `ret` load, escaping to `concurrentAttackerWrite >= sandboxBase + 2^32`.
   - **Register-popped indirect jump (`naclPopAndJmpReturn`, `pop %rcx; andl $0xffffffe0, %ecx; addq %r14, %rcx; jmpq *%rcx`)**: Immune to shared-memory stack TOCTOU (`inSandbox`), but replaces `ret` with `jmpq *%rcx`, desynchronizing the hardware Return Stack Buffer (`rsbHit = false`).
   - **LFI AArch64 register-masked return (`lfiRegisterMaskedReturn`, `ldr x30, [sp], #16; add x30, x27, w30, uxtw; ret`)**: Loads `[sp]` once into private register `x30`, masks/rebases `x30` in-register (`inSandbox`), and executes hardware `ret x30`. Whenever `sandboxBase` is 4 GiB-aligned and the saved return address `rsbTop = sandboxBase + retOffset` (`retOffset < 2^32`) is uncorrupted, `sandboxBase + zext32(rsbTop) = rsbTop`, achieving an exact RSB prediction hit (`rsbHit = true`) while remaining unconditionally confined under concurrent stack mutation.

#### 1.6 LFI x86-64 Dual-Bitmap Verification, `%gs` `Segue`, and Post-Link Prefix Padding

`Basis: source + execution + derived`

- **Dual-Bitmap Direct vs. Indirect Branch Verification (`lfi-verifier/src/x64/verify.c:26-30,290-365,421-424`)**:
  - Pass 1 decodes macroinstructions (`src/x64/macroinst.c:69-88`), sets `bounds[offset] = 1` at each macroinstruction boundary, verifies that no macroinstruction spans a 32-byte bundle boundary (`(addr / 32) != ((addr + count - 1) / 32)`), and sets `targets[target_offset] = 1` for every direct relative branch (`JMP`, `Jcc`, `CALL`).
  - Pass 2 verifies `(v.targets[w] & ~v.bounds[w]) == 0` (`verify.c:421-424`) and cross-checks total instruction count against the synthesized BDD decoder (`lfi_x86_bdd`, `verify.c:383-400,425-429`). Direct branches can therefore target unaligned macroinstruction boundaries without 32-byte NOP padding, while indirect branches mask their target with `0xffffffe0` (`lfi_x64_direct_and_indirect_branch_integrity`, lines 1004–1021).
- **Post-Link Segment Prefix Padding (`lfi-rewriter/lfi-postlink/amd64.c:231-335`)**:
  - `padrewrite` removes trailing bundle-alignment NOPs by prepending up to 4 redundant `0x2e` (`CS`) or `0x65`/`0x64` (`GS`/`FS`) segment prefixes to preceding non-branch, non-LEA instructions (keeping total instruction length $\le 15$ bytes), preserving 32-byte bundle alignment while reducing executed instruction count (`lfi_postlink_prefix_padding_preserves_32b_bundle`, lines 969–978).

---

### 2. Ring-0 WebAssembly Kernels and Intra-Kernel Driver Sandboxes

`Basis: documentation + source + execution + derived`

#### 2.1 Nebulet (`nebulet/nebulet@a22b0198247ea0045b0f87aa31f849f8ffe15f66`)

1. **Virtual Memory Layout and Guard-Page Bounds-Check Elision (`src/memory/mod.rs:28-46`, `src/memory/sip.rs:124-156`, `src/wasm/mod.rs:368-375`)**:
   - Nebulet allocates each Wasm instance's linear memory in `SIP_MEM_ALLOCATOR` (`0x0000_0081_0000_0000 .. +8 TiB`) with `DEFAULT_HEAP_SIZE = 1 << 32` (`4 GiB`) and `DEFAULT_GUARD_SIZE = 1 << 31` (`2 GiB`), configuring Cranelift with `MemoryStyle::Static { bound: 65536 }` and `offset_guard_size: 2 GiB`.
   - Pages are mapped on demand in Ring 0 (`PageTableFlags::PRESENT | WRITABLE | GLOBAL`, without `USER_ACCESSIBLE`). A 32-bit Wasm access `base + zext32(idx) + staticOffset` with `staticOffset < guardSize` is confined to mapped memory `[base, base + memSize)` or traps in the unmapped guard region `[base + memSize, base + 2^32 + guardSize)` (`wasm_guard_page_confinement`, lines 561–579).
   - **The 2 GiB Guard Seam (`nebulet_2gib_guard_escape_if_offset_unbounded`, lines 591–610)**: Although `src/memory/sip.rs:57` comments `// 8GiB`, line 133 sets `DEFAULT_GUARD_SIZE = 1 << 31` (`2 GiB`, total slot `6 GiB`). For a 32-bit Wasm `memarg.offset` $K = 2^{31} + 1 < 2^{32}$ and dynamic index $\mathtt{idx} = 2^{32} - 1$, $\mathtt{base} + \mathrm{zext32}(\mathtt{idx}) + K = \mathtt{base} + 2^{32} + 2^{31}$ jumps completely past the 2 GiB guard region into the adjacent SIP's virtual memory unless software bounds checks are emitted for all $K \ge 2^{31}$.
2. **Ring-0 Interrupt Red-Zone Clobbering and Stack-Guard Triple Faults (`src/arch/x64/idt.rs:48-52`, `src/memory/sip.rs:34-43`)**:
   - Because Nebulet runs Wasm threads at `CPL = 0` and leaves `tss.interrupt.stack_table[DOUBLE_FAULT_IST_INDEX]` commented out (`src/arch/x64/idt.rs:50`), hardware interrupts (`CPL 0 -> CPL 0`) push the 40-byte `ExceptionStackFrame` directly onto the Wasm thread's `RSP`.
   - Theorem `ring0_interrupt_clobbers_redzone_without_ist` (lines 665–681) proves that any Ring-0 interrupt clobbers `[rsp - 40, rsp)` inside the 128-byte System V red zone. Theorem `ring0_interrupt_boundary_double_fault_and_corruption` (lines 691–706) proves that an interrupt arriving at `rsp = stackBottom` faults inside the 4 KiB unmapped stack guard page (`DoubleFaultInGuardPage`, escalating to a triple fault without IST), while an unprobed frame offset at `rsp = lowerMappedTop + 16` silently corrupts adjacent lower mapped memory (`SilentCorruptionOfLowerMappedMemory`). Theorem `ring0_ist_restores_stack_isolation` (lines 713–722) proves that configuring a disjoint IST stack eliminates all three hazards.
3. **Ring-0 Trap-in-ABI Spinlock Deadlock and `__ex_table` Landing Pad Repair (`src/abi/pfex.rs:8-37`, `src/object/thread.rs:138-152`)**:
   - In `pfex_acquire` (`src/abi/pfex.rs:14-15`), the kernel locks `user_data.process.pfex_map().lock()` before dereferencing `lock.load(Ordering::Relaxed)` at `vmctx.fastpath_offset_ptr(lock_offset)`. When `zext32(lock_offset) >= memSize`, `#PF` invokes `page_fault_handler` (`src/arch/common/exception.rs:29`) -> `Process::handle_trap` -> `Thread::exit()`, which context-switches away without unwinding the Rust stack frame, permanently leaking `pfex_map.lock()` (`nebulet_pfex_trap_leaks_spinlock`, lines 760–768).
   - Theorem `ring0_extable_landing_pad_preserves_pfex_lock_freedom` (lines 1389–1416) proves that registering the `fastpath_offset_ptr` load in a Linux-style `__ex_table` fault landing pad that redirects `#PF` to a local `Err(Error::FAULT)` return allows the Rust lexical scope's RAII `Drop` guard to release `pfex_map.lock()` while keeping the thread alive across all in-bounds and out-of-bounds offsets.

#### 2.2 Comparison of Ring-0 / Verified Wasm Runtimes and Intra-Kernel Driver Sandboxes

| System | Execution Ring & Isolation Primitive | TCB & Verification Architecture | Cross-Boundary Memory & Object Discipline |
| :--- | :--- | :--- | :--- |
| **Nebulet** (`nebulet/nebulet@a22b0198...`) | Ring 0 (`CPL 0`), 4 GiB + 2 GiB MMU guard pages | Unverified Cranelift JIT in Ring 0; no binary verifier; no IST configured; non-unwinding `#PF` trap exit. | Direct Ring-0 Rust ABI helpers (`#[nebulet_abi]`) dereferencing `fastpath_offset_ptr` and uncopied `&[u8]` slices (`src/abi/process.rs:70`). |
| **Wasmachine** (`arXiv:2011.09265v1`, 2020) | Ring 0 kernel-mode execution of AOT-compiled Wasm in a Rust OS | Moves Wasm compilation ahead-of-time (AOT) out of the kernel; relies on Rust kernel safety + Wasm bounds/MMU isolation to avoid Ring-3/Ring-0 syscall mode switches. | Zero-copy kernel service invocations validating 32-bit linear-memory offsets at the syscall boundary. |
| **WaVe** (IEEE S&P 2023, `10.1109/SP46215.2023.10179396`) | Userspace 4 GiB SFI linear memory + mechanically verified WASI runtime | Pairs **VeriWasm** (static binary SFI verifier on compiled Wasm ELF) with a mechanically verified Rust/Veir WASI hostcall layer, removing the compiler and runtime from the unverified TCB. | Hostcalls accept `(offset: u32, len: u32)` into `[base, base + 4 GiB)`; mechanically proves memory safety, capability confinement, and absence of host pointer leaks into linear memory. |
| **KSplit** (OSDI 2022) & **LVDs** (OSDI 2020) | Ring 0 isolated driver domains via Intel EPT + `VMFUNC` (or x86 MPK/PKU) | Static Program Dependence Graph (PDG) analysis over kernel + driver C source infers shared struct fields and synchronization points, generating **KSplit IDL** marshaling code. | Deep-copies minimal active projections of shared kernel structs at RPC/lock boundaries; maps high-throughput DMA/packet rings (`skb`) into shared memory windows. |
| **Kage** (`jnwatson/kage@5583be54...`, Linux 6.6) | Ring 0 (`EL1`) AArch64 LFI (`[x27, wN, uxtw]`) + `x18` Shadow Call Stack swap | In-kernel `lfi-verifier` (`security/kage/verify.c`) verifies driver `.ko` machine code on load; BTF metadata generates guarded wrappers (`security/kage/guards.c`). | Replaces kernel object pointers (`struct device *`) with 64-bit non-canonical opaque descriptors (`0xfffffe00... | 1`), checked for sandbox ownership, BTF type ID, and RCU/refcount liveness in `kage_objtable_retrieve` (`kageRetrieveObj_sound`, lines 933–962). |

---

### 3. Speculative Execution Confinement (`uxtw` / `movl` / `addr32` vs. Branch-Checked Guards)

`Basis: normative specification + source + execution + derived`

In Section 3 of [`support/ModernSfiAndWasmKernels.lean`](support/ModernSfiAndWasmKernels.lean) (lines 777–885), we formalize a speculative execution machine (`SpecMachineState`) with an adversarial Pattern History Table (PHT) branch-prediction oracle (`phtPredictsInBounds : Bool`) and a microarchitectural cache-line read trace (`specReadLog : List Nat`):

1. **Branch-Checked Bounds Guards Leak Host Secrets Under Spectre v1 (`branchChecked_spectre_v1_leaks_host_secret`, lines 833–847)**:
   - While `execBranchCheckedGadget` is architecturally confined when `phtPredictsInBounds = false` (`branchChecked_architecturally_confined`, lines 818–830), whenever `idx >= 2^32` and `phtPredictsInBounds = true`, the transient execution path evaluates `addr1 = sandboxBase + idx >= sandboxBase + 2^32` before branch resolution, reading `mem[sandboxBase + idx]` outside the sandbox and recording `sandboxBase + zext32(secret * 4096)` in `specReadLog` even though `archResult` is rolled back to `0`.
2. ** Speculation Barriers Restore Confinement at High Pipeline Cost (`branchCheckedWithFence_speculatively_confined`, lines 873–885)**:
   - Inserting `lfence` (x86-64) or `csdb` (AArch64) after the conditional branch blocks transient loads along mispredicted paths (`16 bytes, 6 instructions` in [`support/sfi_encoding_probe_results.json`](support/sfi_encoding_probe_results.json)), but serializes out-of-order execution on every memory access.
3. **32-Bit Zero-Extension (`uxtw` / `movl` / `addr32`) Provides Unconditional Architectural and Speculative Confinement (`uxtw_speculatively_confined_for_all_oracles` & `uxtw_never_reads_outside_sandbox`, lines 850–870)**:
   - Because `ldr x0, [x27, w1, uxtw]`, `movl %eax, %eax; movq (%r14, %rax), %rcx`, and `movq %gs:(%eax), %rcx` zero-extend the 32-bit index inside the ALU/AGU data path without any conditional branch, every architectural and transient memory read in `specReadLog` satisfies `inSandbox sandboxBase a` under **all** branch-predictor oracles, and no address `secretAddr ∉ [sandboxBase, sandboxBase + 2^32)` is ever transiently read.

---

### 4. Empirical Instruction-Encoding and Code-Density Comparison (`llvm-mc`)

`Basis: execution`

Executing [`support/sfi_encoding_probe.py`](support/sfi_encoding_probe.py) with `/usr/bin/llvm-mc` across `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` produces the exact byte-level encodings preserved in [`support/sfi_encoding_probe_results.json`](support/sfi_encoding_probe_results.json):

| Operation Class | SFI / Wasm Scheme & Target | Assembly Sequence | Insts | Bytes | Exact Hex Bytes (`llvm-mc`) | Overhead vs. Unsandboxed |
| :--- | :--- | :--- | :---: | :---: | :--- | :--- |
| **Memory Load (`[reg]`)** | Unsandboxed Baseline (`x86-64`) | `movq (%rax), %rcx` | 1 | 3 B | `48 8b 08` | — |
| | NaCl / LFI Base-Reg (`x86-64`) | `movl %eax, %eax ; movq (%r14, %rax), %rcx` | 2 | 6 B | `89 c0 ; 49 8b 0c 06` | +1 inst, +3 B (+100%) |
| | **LFI `Segue` `%gs` + `addr32` (`x86-64`)** | `movq %gs:(%eax), %rcx` | **1** | **5 B** | `65 67 48 8b 08` | **+0 insts**, +2 B prefixes |
| | Unsandboxed Baseline (`aarch64`) | `ldr x0, [x1]` | 1 | 4 B | `20 00 40 f9` | — |
| | **LFI `uxtw` Single-Inst (`aarch64`, `x21`)** | `ldr x0, [x21, w1, uxtw]` | **1** | **4 B** | `a0 4a 61 f8` | **+0 insts, +0 B (0%)** |
| | **LFI `uxtw` Single-Inst (`aarch64`, `x27`)** | `ldr x0, [x27, w1, uxtw]` | **1** | **4 B** | `60 4b 61 f8` | **+0 insts, +0 B (0%)** |
| **Memory Load (`[reg + 16]`)** | **LFI `Segue` `%gs` + `addr32` (`x86-64`)** | `movq %gs:16(%eax), %rcx` | **1** | **6 B** | `65 67 48 8b 48 10` | **+0 insts**, +2 B prefixes |
| | LFI `x28` Addr-Reg (`aarch64`, `x27`/`x28`) | `add x28, x27, w1, uxtw ; ldr x0, [x28, #16]` | 2 | 8 B | `7c 43 21 8b ; 80 0b 40 f9` | +1 inst, +4 B |
| | Nebulet Ring-0 Wasm Guard-Page (`x86-64`) | `movl %eax, %eax ; movq 16(%rdi, %rax), %rcx` | 2 | 7 B | `89 c0 ; 48 8b 4c 07 10` | +1 inst, +3 B |
| | Branch-Checked + `lfence` (`x86-64`) | `movl %eax, %eax ; cmpq %rsi, %rax ; jae 1f ; lfence ; movq (%rdi, %rax), %rcx ; 1: ud2` | 6 | 16 B | `89 c0 ; 48 39 f0 ; 73 0a ; 0f ae e8 ; 48 8b 0c 07 ; 0f 0b` | +5 insts, +13 B + pipeline stall |
| **Indirect Jump / Return** | NaCl 32B Bundle Jump (`x86-64`) | `andl $0xffffffe0, %eax ; addq %r15, %rax ; jmpq *%rax` | 3 | 8 B | `83 e0 e0 ; 4c 01 f8 ; ff e0` | +2 insts + bundle NOP pad |
| | LFI Macroinst Jump (`x86-64`) | `andl $0xffffffe0, %eax ; leaq (%r14, %rax), %r11 ; jmpq *%r11` | 3 | 10 B | `83 e0 e0 ; 4d 8d 1c 06 ; 41 ff e3` | Preserves `%rax` via `%r11` |
| | **LFI Bundle-Free Jump (`aarch64`)** | `add x18, x21, w1, uxtw ; br x18` | **2** | **8 B** | `b2 42 21 8b ; 40 02 1f d6` | **+1 inst, 0 bundle padding** |
| | **LFI Bundle-Free Return (`aarch64`, `x27`)** | `add x30, x27, w30, uxtw ; ret` | **2** | **8 B** | `7e 43 3e 8b ; c0 03 5f d6` | **+1 inst, 0 bundle padding, RSB hit** |
| **Runtime Call Trampoline** | **LFI Bundle-Free Trampoline (`aarch64`, `x27`)** | `mov w26, w30 ; ldr x30, [x27] ; blr x30 ; add x30, x27, w26, uxtw` | **4** | **16 B** | `fa 03 1e 2a ; 7e 03 40 f9 ; c0 03 3f d6 ; 7e 43 3a 8b` | **16 B total (no 32B bundle pad)** |

---

## Boundaries

- **RISC-V (`rv64`) LFI Verifier (`lfi-verifier/src/riscv64/`)**: **not examined**. While `lfi-verifier` and `lfi-runtime` include a `riscv64` directory, our source inspection, encoding probes, and Lean 4.34.1 mechanization covered only AArch64 and x86-64.
- **ARMv8.5-A Memory Tagging Extension (MTE) and x86-64 Protection Keys for Userspace/Supervisor (PKU/PKS) Hardware Execution**: **not examined** via live hardware execution. In-kernel MPK/EPT trade-offs (LVDs/KSplit, ColorGuard) and AArch64 PAC/BTI verifier rules (`autiasp`, `paciasp`, `bti`, `retaa`/`retab` rejection in `lfi-verifier/src/arm64/verify.c:55-66,258-262`) were analyzed from source and specification rather than benchmarked on MTE/PKU silicon.
- **Cross-Process Spectre v2 (BTB) / BHI Hardware Flush Overhead**: **known not to apply** to intra-sandbox `uxtw` data loads (which cannot address outside `[sandboxBase, sandboxBase + 2^32)` even under BTB poisoning as long as `x27` holds `sandboxBase`), but **unknown** for the exact cycle cost of IBPB/BTB flushing when switching `x27` back to host kernel code that uses `x27` as an unmasked pointer.
- **Dynamic Code Modification / Self-Modifying JIT Inside LFI Sandboxes (`W^X`)**: **unsupported** without runtime verifier mediation. Both `lfi-runtime/core/box.c` and `lfi-research/liblfi/pal/vm.c:72-88` (`protectverify`) reject `PROT_WRITE | PROT_EXEC` mappings (`WX` memory) and require every executable mapping (`LFI_PROT_EXEC`) to pass `lfiv_verify` before `mprotect` enables execution.

---

## Evidence

### 1. Primary Source Repositories and Exact File/Line Coordinates

1. **`lfi-project/lfi-verifier` (`ecb5ff31b2deb83052a8f3dbad58bc6c595632f4`, observed 2026-11-02)**:
   - `src/arm64/verify.c:69-74`: AArch64 reserved register definitions (`REG_ADDR = 28`, `REG_BASE = 27`, `REG_RET = 30`, `REG_CTX = 25`).
   - `src/arm64/verify.c:111-133,234-277,451-481,600-603`: Stateful `v->x30_guarded` link-register tracking (`is_x30_guard`, `is_x30_ldr_guard`, `chkbranch`, `okmod`, and end-of-code check).
   - `src/arm64/verify.c:324-391,424-437`: Negative-offset runtime call immediates (`okctxrtcallimm`, `okrtcallimm`, `is_ctxreg_rtcall_load`) and the `chkmemops` check enforcing `REG_RET` on `x25` (`ctxreg`) while omitting it on `x27` (`rtsysreg`).
   - `src/arm64/verify.c:494-524,573-577`: Rejection of `CONSTRAINED UNPREDICTABLE` simultaneous register modifications (`mask == 0b11 && dinst.ops[0].reg == dinst.ops[1].reg`) and writeback register overlaps (`chkwriteback`).
   - `test/arm64/fail.s:29-30,71-82,121-160,183-229` and `test/arm64/pass.s:91-185`: Negative and positive regression test cases for `ldp` overlap, `x30_guarded`, `retaa`/`retab`, `x25` runtime calls, and writeback unguarding.
   - `src/x64/verify.c:26-30,124-184,290-365,383-429` and `src/x64/macroinst.c:69-88`: x86-64 `%r14` and `%gs` `addr32` (`Segue`) operand verification, `bounds`/`targets` dual-bitmap direct jump verification, and `lfi_x86_bdd` cross-check.
2. **`lfi-project/lfi-runtime` (`3b78c956368eb78d5d2241cec5d650e13f57f5cb`, observed 2026-11-02)**:
   - `core/box.c:58-123,190-198`: Negative-offset `sys_page` allocation (`box->sys_page = box->base - pagesize`, `struct Sys` placed at `[box->base - 32, box->base)` and `[ctxreg - 32, ctxreg)`) and internal guard regions.
   - `core/core.c:152-186`: Host `sigaltstack` setup (`lfi_init_sigaltstack`) isolating host signal frames from sandbox `sp`.
   - `core/arch/arm64/runtime.S:1-130` and `core/arch/x64/runtime.S:1-140`: World-switch context entry/exit assembly and runtime call trampolines.
3. **`lfi-project/lfi-rewriter` (`1389430d371cf614e1d3ff8f7487d54d560692d9`, observed 2026-11-02)**:
   - `lfi-postlink/amd64.c:231-335` (`padrewrite`): Post-link absorption of trailing 32-byte bundle NOPs into `0x2e`/`0x65`/`0x64` segment override prefixes.
4. **`lfi-project/lfi` (`lfi-research` branch at `749401bc68463ffaee2349ae9e37731ece8eda5d`, observed 2026-11-02)**:
   - `lfi-verify/arm64/verify.c:57-64` and `lfi-verify/arm64/poc.c:1-57`: ASPLOS 2024 `x21`/`x18`/`x22` register conventions and Position-Oblivious Code (`--poc`, `okreadpoc`) forbidding 64-bit reads of reserved/address registers.
   - `liblfi/pal/ctx.c:28-66` and `liblfi/pal/vm.c:30-37`: Page-0 (`[base + 0]`) `struct Sys` placement in the 2024 runtime.
5. **`jnwatson/kage` (`kage01` branch at `5583be54dfa35b74a3860a43fc89cb034a2184bc`, observed 2026-11-02)**:
   - `security/kage/kage_main.c:65-97,218-255,744-883,915-925,1046,1175-1234`: 64 GiB kernel `vmalloc` sandbox arena, in-guest `g2h_tramp_data` and `PROC_DATA` allocations, and RCU/refcounted opaque object table (`kage_objtable_retrieve`).
   - `include/linux/kage_objdescriptor.h:23-62`: Non-canonical 64-bit object descriptor encoding (`0xfffffe0000000000 | (owner << 32) | (type << 17) | (index << 1) | 1`).
   - `security/kage/runtime.S:6-18,36-51,91-154`: `GET_PROC`, `lfi_restore_partial_regs` (`add x30, x27, w30, uxtw; ret`), and `CONFIG_SHADOW_CALL_STACK` (`x18`) world-switching.
6. **`nebulet/nebulet` (`a22b0198247ea0045b0f87aa31f849f8ffe15f66`, observed 2026-11-02)**:
   - `src/memory/mod.rs:28-46,106-125` and `src/memory/sip.rs:34-43,57,124-156`: SIP virtual memory allocators, 4 KiB stack guard allocation, and `DEFAULT_HEAP_SIZE = 4 GiB` + `DEFAULT_GUARD_SIZE = 2 GiB`.
   - `src/wasm/mod.rs:285-296,368-375`: Cranelift `MemoryStyle::Static` configuration and 64-bit linear memory base emission.
   - `src/arch/x64/idt.rs:48-52` and `src/arch/common/exception.rs:8-35`: Unconfigured `TSS.interrupt.stack_table` (`DOUBLE_FAULT_IST_INDEX` commented out) and Ring-0 `#PF` demand paging / trap dispatch.
   - `src/object/process.rs:146-153`, `src/object/thread.rs:138-152`, `src/abi/pfex.rs:8-37`, and `src/abi/process.rs:66-76`: Non-unwinding `Thread::exit()` on `#PF` causing `pfex_map.lock()` spinlock deadlock in `pfex_acquire`, and uncopied `wasm_bytecode` slice TOCTOU in `wasm_compile`.
7. **Primary Literature**:
   - Zachary Yedidia, *Lightweight Fault Isolation: Practical, Efficient, and Secure Software Sandboxing*, ASPLOS 2024 (`doi:10.1145/3620666.3651336`, `arXiv:2402.15636v1`).
   - Matthew Sotoudeh and Zachary Yedidia, *Automated Formal Verification of a Software Fault Isolation System*, FMCAD 2025 (`arXiv:2508.15898v1`, `verification.tex:38-81`).
   - Elliott Wen and Gerald Weber, *Wasmachine: Bring the Edge up to Speed with a WebAssembly OS*, 2020 (`arXiv:2011.09265v1`).
   - Evan Johnson et al., *WaVe: A Verifiably Secure WebAssembly Sandboxing Runtime*, IEEE S&P 2023 (`doi:10.1109/SP46215.2023.10179396`).
   - Yongzhe Huang et al., *KSplit: Automating Device Driver Isolation*, USENIX OSDI 2022.

### 2. Preserved Support Material in This Package

1. **[`support/ModernSfiAndWasmKernels.lean`](support/ModernSfiAndWasmKernels.lean)** (`1,422 lines`, verified with Lean `v4.34.1`):
   - **Section 1 (Lines 16–515)**: AArch64 LFI machine model, stateless and stateful (`x30_guarded`) verifiers, single-step soundness (`lfiVerifyStepStateful_sound`), multi-step induction (`lfiVerifyProgStatefulAux_sound`), block soundness (`lfiVerifyBlock_sound`), and guard-zone pre-index writeback confinement (`preIndex_writeback_confined_or_traps_in_guard`).
   - **Section 2 (Lines 517–770)**: Ring-0 WebAssembly guard-page confinement (`wasm_guard_page_confinement`), the Nebulet 2 GiB guard seam counterexample (`nebulet_2gib_guard_escape_if_offset_unbounded`), Ring-0 interrupt red-zone clobbering (`ring0_interrupt_clobbers_redzone_without_ist`), stack-boundary double fault and lower-memory corruption (`ring0_interrupt_boundary_double_fault_and_corruption`), IST stack isolation (`ring0_ist_restores_stack_isolation`), and `pfex_acquire` trap spinlock leak (`nebulet_pfex_trap_leaks_spinlock`).
   - **Section 3 (Lines 772–885)**: Speculative execution model proving Spectre v1 leakage under branch-checked guards (`branchChecked_spectre_v1_leaks_host_secret`), confinement with `lfence`/`csdb` (`branchCheckedWithFence_speculatively_confined`), and unconditional speculative confinement under `uxtw` 32-bit zero-extension (`uxtw_speculatively_confined_for_all_oracles`, `uxtw_never_reads_outside_sandbox`).
   - **Section 4 (Lines 887–1022)**: Kage BTF opaque object descriptor soundness (`kageRetrieveObj_sound`), x86-64 `lfi-postlink` segment-prefix padding invariant (`lfi_postlink_prefix_padding_preserves_32b_bundle`), and x86-64 dual-bitmap direct/indirect jump target integrity (`lfi_x64_direct_and_indirect_branch_integrity`).
   - **Section 5 (Lines 1024–1422)**: Page-0 trampoline KASLR leak (`page0_trampoline_leaks_kaslr`), negative-offset trampoline unreachability by `uxtw` (`negative_offset_unreachable_by_uxtw`), paired `ldur x30; blr x30` confidentiality vs. unpaired `ldur x0, [x27, #-imm]` leakage (`ldur_x30_with_mandatory_blr_prevents_gpr_leak_vs_unpaired_leak`), AArch64 `ldp`/writeback `CONSTRAINED UNPREDICTABLE` overlap rejection (`aarch64_ldp_overlapping_reg_unpredictable_hazard`), LFI register-masked return TOCTOU immunity and RSB hit preservation (`register_masked_return_immune_to_stack_toctou`), asynchronous signal `x30` re-masking (`async_signal_restore_requires_x30_remask`), and Ring-0 `__ex_table` landing pad repair for `pfex_acquire` (`ring0_extable_landing_pad_preserves_pfex_lock_freedom`).
2. **[`support/sfi_encoding_probe.py`](support/sfi_encoding_probe.py)** and **[`support/sfi_encoding_probe_results.json`](support/sfi_encoding_probe_results.json)**:
   - Reproducible `/usr/bin/llvm-mc` probe and JSON output for 20 x86-64 and AArch64 SFI / Ring-0 Wasm instruction sequences.

---

## Revalidation

To revalidate the mechanized proofs and empirical instruction-encoding measurements in this package:

1. **Re-verify the Lean 4.34.1 mechanization (confirming exit code `0`, zero warnings, and zero non-standard axioms)**:
   ```bash
   lean support/ModernSfiAndWasmKernels.lean
   ```
   Every `#print axioms` line at the end of `support/ModernSfiAndWasmKernels.lean` must report only `[propext, Quot.sound]`, `[propext]`, or `does not depend on any axioms` (with `0 sorryAx`, `0 Classical.choice`, and `0 Lean.ofReduceBool`).
2. **Re-run the `llvm-mc` instruction-encoding probe**:
   ```bash
   python3 support/sfi_encoding_probe.py
   ```
   This regenerates `support/sfi_encoding_probe_results.json` and prints the 20-sequence comparison table.
3. **Check whether upstream `lfi-verifier` has patched the `x27` (`rtsysreg`) vs. `x25` (`ctxreg`) runtime-call destination asymmetry**:
   - Inspect `src/arm64/verify.c` in `lfi-project/lfi-verifier` around `okmemop` (`lines 375–392`) and `chkmemops` (`lines 424–437`) to see whether `rtsysreg(v, op->reg)` now enforces `dinst->mnem == DA64I_LDURX && dinst->ops[0].reg == REG_RET` (matching `is_ctxreg_rtcall_load`) and whether a two-instruction lookahead (`blr x30`) or `--poc` read check is enforced on runtime call loads.
