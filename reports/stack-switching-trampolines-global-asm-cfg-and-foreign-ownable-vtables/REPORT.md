# Stack-Switching Trampolines, Section-Wide `global_asm!` Cutpoint Graphs, and COFE-Free `ForeignOwnable` Vtables

## Summary

Verifying mixed Rust MIR, out-of-line assembly (`global_asm!` and external `.S`
objects), and C subsystem callbacks across production systems code—specifically
Fuchsia/Zircon/Starnix and Rust-for-Linux—exposes three structural boundaries
where single-stack LIFO call chains (`List LinkFrame`), per-symbol
`[st_value, st_value + st_size)` binary lifters, and stack-nested callback
borrow lifetimes fail:

1. **Two-entry stack-switching trampolines violate single-stack LIFO separation,
   retain dormant-stack Tree Borrows `StrongProtector`s, and require gated
   stack-root `DW_CFA_undefined` (`0x07`):**
   - Production restricted-mode and fiber trampolines—such as Fuchsia Starnix
     `restricted_enter_loop` + `restricted_return_loop`
     (`trampoline_x64.S:20-173`, `trampoline_arm64.S:19-201`), Zircon
     `x86_64_context_switch` / `arm64_context_switch`, and `corosensei`
     `stack_init_trampoline` + `stack_init_trampoline_return`—enter at one
     global symbol, pivot `rsp`/`sp` across disjoint stack allocations
     (violating single-stack `sp ∈ [sp_entry - F, sp_entry)`), and resume or
     exit through a second global symbol via cross-symbol branches.
   - Unlike stackless Rust `#[coroutine]` state machines—whose `resume` call
     returns `CoroutineState::Yielded` and retires its `FnEntry` protector
     before outer code runs—suspending a stackful Rust frame on Stack A leaves
     its `FnEntry` `StrongProtector`s active in `protected_tags` throughout
     Stack B's execution. Live Miri execution (`-Zmiri-tree-borrows`) proves
     that while Stack A is dormant, a foreign/sibling write **or even a
     sibling read** on an activated `&mut T` (`Unique`) triggers **immediate
     Undefined Behavior** even if Stack A never touches that reference again
     upon resumption, whereas a sibling read on an unactivated `&mut T`
     (`ReservedFrz false -> ReservedFrz true`) triggers deferred UB if and only
     if resumed Stack A subsequently writes.
   - At stack roots bordering unmapped `PROT_NONE` guard pages, omitting
     `.cfi_undefined rip` (`0x07, 0x10`) on x86-64 causes `_Unwind_Backtrace`
     and Phase-1 unwinding to `SIGSEGV` (`rc = -11`) dereferencing `[stack_top]`.
     On AArch64, LLVM's CIE emits `DW_CFA_def_cfa: WSP +0` with **no initial
     rule for `W30` (`LR`)**: under AAPCS64 DWARF §4.1 `SameValue` semantics
     (`libgcc_s` / `llvm-libunwind`), omitting `.cfi_undefined x30` (`0x07, 0x1e`)
     traps `_Unwind_Backtrace` (`22` identical-PC repeats in 25 steps) and hangs
     Phase-1 unwinding in an infinite fixed-point loop, whereas `unwinding 0.2.10`
     (`src/unwinder/frame.rs:146`: `new_ctx[Arch::RA] = 0`) initializes
     unmentioned `RA` to `0` (`Undefined`), silently masking missing
     `.cfi_undefined x30` in bare-metal tests. Admitting `DW_CFA_undefined` as a
     13th CFI opcode strictly on designated stack-root FDEs (while continuing to
     reject it inside interior function/inline-`asm!` FDEs) resolves both ISAs
     portably.
2. **`global_asm!` and Perlasm `.S` bypass MIR and per-symbol ELF boundaries,
   requiring a Section-Wide Entry-Cutpoint Graph (`SWECG`):**
   - Whereas `#[unsafe(naked)]` (`codegen_naked_asm`) wraps a single function in
     `.pushsection .text.<name>` and `.size <name>, . - <name>`, `global_asm!`
     (`codegen_global_asm` -> `llvm::append_module_inline_asm`) and Perlasm `.S`
     files (`aws-lc` `aesni-xts-avx512.S`, `trampoline-x86_64.S`, `aesni-x86_64.S`)
     bypass MIR completely, frequently omit `.size` (`st_size == 0`), fall
     through across global labels, share `.L` local tail helpers, jump backward
     across global symbols, and embed `.quad`/`.byte` lookup constants directly
     in `.text`.
   - Both naive ELF lifters fail: `[st_value, st_value + st_size)` vacuously
     accepts 0-byte `st_size == 0` functions and faults on jumps to shared
     `.Lshared_tail` helpers outside `.size`, while `[st_value, next_sym)`
     truncates symbol-to-symbol fallthroughs, rejects negative-offset
     cross-symbol branches (`pc = -4`), and misdecodes inline `.text` constant
     pools if swept linearly. Lifting each executable section (`SHF_ALLOC |
     SHF_EXECINSTR`) + `SHT_RELA` table as a whole via `SWECG` from exported/relocated
     entry offsets $E$, enforcing $V_{\text{exec}} \cap D_{\text{rodata}} = \emptyset$,
     and placing cutpoints at $E \cup \{\text{multi-predecessor joins / back-edges}\}$
     verifies all multi-entry clusters without duplication or vacuity.
3. **Temporally disjoint C ops-table vtables (`file_operations`, `fdf_sys`) are
   soundly verified by a COFE-free first-order linear `ForeignHandlePool`:**
   - In Linux `struct file_operations` (`open` -> `unlocked_ioctl`/`read_iter` ->
     `release`) and Fuchsia `fdf_sys` driver hooks, `open` converts a Rust
     allocation via `ForeignOwnable::into_foreign` into `void *private_data` and
     returns `0` to C, popping its stack frame before any callback runs.
   - Live `gcc 15.2.0` + Rust + Miri (`-Zmiri-tree-borrows`) experiments
     reproduce three real lifecycle hazards: (a) returning non-zero `-EINVAL`
     from `open` after storing `into_foreign` leaves `FMODE_OPENED` unset in
     `do_dentry_open` (`fs/open.c:1000-1004`), causing `__fput`
     (`fs/file_table.c:493`) to skip `release` and leak the handle; (b)
     reentrant `ioctl -> C -> ioctl` using `<Box<T, A> as ForeignOwnable>::borrow_mut`
     (`rust/kernel/alloc/kbox.rs:543-548`) fabricates aliasing `&mut T`
     references without dynamic tracking, causing immediate Tree Borrows
     protector UB; and (c) double `from_foreign` in `release` causes dangling-`Box`
     use-after-free UB.
   - Because C stores opaque first-order `void *` handles rather than
     self-referential higher-order closures in mutable shared heap, a COFE-free
     first-order linear `ForeignHandlePool` (`Unallocated | Owned | Shared(n) |
     MutLoaned | Freed`) proves arbitrary-length VFS event traces and
     arbitrary-depth reentrant `Shared(n)` callbacks sound by structural
     induction in pure Lean `v4.34.1` (`Init.*`-only, zero `sorry`, standard
     axioms `{propext, Classical.choice, Quot.sound}`).

---

## Applicability

This report governs binary/assembly lifting, stack/unwind modeling, and FFI
ownership contracts across the subjects recorded in `REPORT.json`:

- **Relationship to neighboring corpus reports:**
  - Extends single-stack heterogeneous `List LinkFrame` and reentrant `MIR <-> ISA`
    Tree Borrows protector rules onto **multi-stack pools (`StackPool`)** and
    **temporally disjoint heap-backed C vtable lifecycles (`ForeignHandlePool`)**.
  - Extends the 12-opcode (+2 DRAP expression) `.eh_frame` `Trusted.DwarfCfi`
    subset—which rejects `DW_CFA_undefined` (`0x07`) inside function-scoped
    inline `asm!` blocks—to a **13-opcode** model that admits `DW_CFA_undefined`
    exclusively on designated stack-root FDEs while preserving interior rejection.
  - Extends single-symbol `naked_asm!` / inline-`asm!` lifting to module-scope
    `global_asm!` and external Perlasm `.S` ELF relocatable objects.
- **Examined upstream systems and revisions:**
  - **Fuchsia OS (`4799c98e7566bf11f1bb3f07dfea86173f00e336`)**: Starnix
    restricted-mode syscall loops (`src/starnix/kernel/syscall_loop/src/trampoline_x64.S`
    and `trampoline_arm64.S`, `src/starnix/lib/asm_utils/include/starnix_asm_utils/asm.h`),
    Zircon thread context switches (`zircon/kernel/arch/x86/asm.S`,
    `zircon/kernel/arch/arm64/asm.S`), libc/Zircon thread roots
    (`sdk/lib/c/threads/thread-start.cc`, `zircon/kernel/arch/riscv64/mp.cc`),
    and driver runtime C ops bindings (`sdk/lib/driver/runtime/rust/fdf_sys/src/bindings.rs`).
    (Note: in older Fuchsia trees such as `fd31be1516bd2906c5b46be6c3ca3aa1adb162c0`,
    the Starnix trampolines resided under `src/starnix/kernel/execution/`; at
    `4799c98e7566` they reside under `src/starnix/kernel/syscall_loop/src/`.)
  - **Linux kernel (`torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2`)**:
    `ForeignOwnable` (`rust/kernel/types.rs`), `Box<T, A>` (`rust/kernel/alloc/kbox.rs`),
    `Arc<T>` (`rust/kernel/sync/arc.rs`), `MiscDeviceRegistration`
    (`rust/kernel/miscdevice.rs`), and C VFS lifecycle (`fs/open.c`, `fs/file_table.c`).
  - **User-space coroutine/fiber and crypto assembly crates**:
    `Amanieu/corosensei@4b5db4845204a4b2663d3f7f75866be4cc3c680d`,
    `bytecodealliance/wasmtime@40e0d780e4bfa34325d342db5bcf492bea227e07`,
    `nbdd0121/unwinding` `0.2.10` + `gimli` `0.34.0`,
    `aws/aws-lc@cd481c207e38f06aeb5766f4a1cdfce10a4c0af8` (`aws-lc-sys 0.47.0`),
    and `briansmith/ring@0b237cbbb4364529818608839faec2d2f9e12664` (`ring 0.17.14`).
- **Executed compiler, emulator, and prover environments (`x86_64-unknown-linux-gnu` host):**
  - `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`)
    and `miri 0.1.0` (`3ef0c22cdb`, `MIRIFLAGS="-Zmiri-tree-borrows"`) for Miri
    Tree Borrows suites, native x86-64 `global_asm!` unwind probes (`libgcc_s`),
    ELF64 `.o` symbol/CFG probes, and C+Rust VFS harnesses.
  - `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1`,
    target `aarch64-unknown-linux-gnu` linked statically via bundled `rust-lld`)
    executed under `qemu-aarch64 11.1.2` with `unwinding 0.2.10` (`fde-static`).
  - `gcc (Debian 15.2.0-14) 15.2.0`, `GNU Binutils 2.47`, and `llvm-dwarfdump 21.1.8`.
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
    with `-DElab.async=false -Ddebug.skipKernelTC=false` and fresh-kernel private
    replay (`trustLevel := 0`, `loadExts := false`).

---

## Findings

### 1. Stack-Switching Trampolines, Dormant-Stack Tree Borrows Protectors, and `DW_CFA_undefined`

#### 1.1 Two-Entry Cross-Symbol Control Flow and Failure of Single-Stack `PrivateStackSep`

Basis: `source` + `derived`

Single-stack FFI models represent call history as a single LIFO `List LinkFrame`
inside one contiguous stack region `[STACK_BASE, STACK_TOP)` where each callee's
stack pointer remains bounded within `[sp_entry - F, sp_entry)`. Production
context-switching and restricted-mode assembly breaks three assumptions of that
model simultaneously:

1. **Asymmetric two-symbol entry/exit and cross-symbol jumps:** In Fuchsia
   Starnix `src/starnix/kernel/syscall_loop/src/trampoline_x64.S:20-173` (and
   AArch64 `trampoline_arm64.S:19-201`), Rust calls `restricted_enter_loop`,
   which pushes callee-saved registers (`%rbx`, `%rbp`, `%r12`–`%r15`, `%rsp`),
   passes `leaq restricted_return_loop(%rip), %rsi` and `mov %rsp, %rdx` to
   `zx_restricted_enter` (`L62-68`), and switches into restricted Linux user
   mode on a disjoint user stack. When restricted mode traps or exits back to
   Zircon, the kernel jumps **directly to the second global symbol**
   `restricted_return_loop` (`L95`), which pivots `%rsp` back via `mov %rdi, %rsp`
   (`L97`), invokes `restricted_exit_callback_c` (`callq *%rcx`, `L157`), and
   then executes **cross-symbol branches** directly into interior local labels of
   `restricted_enter_loop`:
   ```gas
   // src/starnix/kernel/syscall_loop/src/trampoline_x64.S:163-173
     test %eax, %eax
     je .restricted_enter_loop_ret
     mov 0(%rsp), %rdi
     call restore_extended_pstate
     jmp .restricted_enter_loop_top
   END_FUNCTION(restricted_return_loop)
   ```
   Identical cross-symbol edges appear in `trampoline_arm64.S:192-199`
   (`cbz x0, .restricted_enter_loop_ret` and `b .restricted_enter_loop_top`).
2. **Disjoint stack-pointer pivots (`sp ∉ [sp_entry - F, sp_entry)`):**
   Zircon's `x86_64_context_switch` (`zircon/kernel/arch/x86/asm.S:20-49`),
   `arm64_context_switch` (`zircon/kernel/arch/arm64/asm.S:22-70`), Wasmtime's
   `wasmtime_fiber_switch` (`crates/fiber/src/stackswitch/x86_64.rs` and
   `aarch64.rs`), and `corosensei`'s `stack_init_trampoline` /
   `stack_call_trampoline` (`src/arch/x86_64.rs:175-357`) store the current
   stack pointer into a context record (`mov [rdi + OFF_RSP], rsp`), load `rsp`
   from an arbitrarily located heap/mmap stack allocation (`mov rsp, [rsi + OFF_RSP]`),
   and execute `ret` into a suspended frame on the target stack.
3. **Non-LIFO interleaving of active vs. dormant Rust frame chains:** Replacing
   a single `List LinkFrame` with a first-order linear `StackPool`
   (`List StackSlot`, where each slot owns `[base, top)` and transitions
   `Active(curSp, frames) <-> Dormant(savedSp, resumeSym, savedCsr, frames)`)
   preserves pairwise interval disjointness across arbitrary two-entry switches
   without step-indexed circularity (`StackPoolAndCfi.two_entry_switch_preserves_protectors_and_disjointness`
   in `support/StackSwitchGlobalAsmAndForeignVtable.lean`).

#### 1.2 Dormant-Stack Tree Borrows `StrongProtector` Persistence vs. Stackless `#[coroutine]`

Basis: `source` + `execution` (`support/reproduce_all_probes.py`, `support/empirical_receipts.json`) + `derived`

Under Tree Borrows (`rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`
and `vendor/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), every Rust
function call allocates a `FnEntry` `StrongProtector` in `global.protected_tags`
for reference arguments (`&T`, `&mut T`) that persists until that MIR stack
frame **returns or unwinds**.

Miri rejects raw inline assembly (`m1`: `unsupported operation: inline assembly
is not supported`), so Wasmtime itself models stackful fiber switching under
Miri by parking suspended fiber stacks on a `Mutex` + `Condvar` gate
(`wasmtime@40e0d780e4bf`, `crates/fiber/src/miri.rs:1-261`). Executing the
complete 8-case dormant-stack Tree Borrows matrix under `cargo +nightly miri test`
(`rustc 1.102.0-nightly`, `MIRIFLAGS="-Zmiri-tree-borrows"`) establishes a sharp
semantic boundary between **stackful fiber suspension** and **stackless Rust
`#[coroutine]` yields**:

| Probe ID | Dormant Stack A State Across Switch to Stack B | Stack B Operation While Stack A Is Dormant | Stack A Action After Resume | Miri `-Zmiri-tree-borrows` Outcome (`empirical_receipts.json`) | Tree Borrows State Mechanism |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `m1` | Inline `asm!("mov {}, rsp", ...)` | — | — | **Unsupported (`rc = 1`)**: `inline assembly is not supported` | Miri has no ISA stack-pivot executor |
| `m2a` | `x: &mut u64` activated (`*x = 11`, `Unique`, protected) | Writes disjoint `slot_b` | `*x + 1` | **Pass (`rc = 0`)** | Disjoint `AllocId`; Stack A protector undisturbed |
| `m2b` | `x: &mut u64` (`ReservedFrz false`, protected), passes child `*mut u64` `&raw mut *x` to Stack B | Writes `*child = 77` | Reads `*x` (`77`) | **Pass (`rc = 0`)** | Child write is a `LocalAccess` relative to `x`'s tag (`ReservedFrz false -> Unique`) |
| `m2c` | `x: &mut u64` activated (`*x = 11`, `Unique`, protected) | Sibling write `*root_sibling = 99` | Reads `*x` | **Immediate UB on Stack B (`rc = 1`)**: `write access through <...> (root of the allocation) ... is forbidden` | `ForeignAccess` write on protected accessed `Unique` (`tbStep .write .foreign .unique true true = none`) |
| `m2d` | `x: &mut u64` activated (`*x = 11`, `Unique`, protected) | **Sibling read `_ = *root_sibling`** | **Returns `0` without ever reading or writing `x` again!** | **Immediate UB on Stack B (`rc = 1`)**: `read access through <...> (root of the allocation) ... is forbidden` | `ForeignAccess` read on protected accessed `Unique` tries `Unique -> Frozen`, which `StrongProtector` forbids immediately |
| `m2e` | `x: &mut u64` **unactivated** (`ReservedFrz false`, protected) | Sibling read `_ = *root_sibling` (`10`) | **Writes `*x = 42`** | **Deferred UB on Stack A resume (`rc = 1`)**: `write access through <...> is forbidden` | Stack B read sets `conflicted := true` (`ReservedFrz true`); still-active protector forbids `ReservedFrz true -> Unique` |
| `m2f` | `x: &mut u64` **unactivated** (`ReservedFrz false`, protected) | Sibling read `_ = *root_sibling` (`10`) | **Reads `*x` (`10`) only** | **Pass (`rc = 0`)** | `LocalAccess` read on `ReservedFrz true` remains `ReservedFrz true` |
| `m2g` | **Stackless `#[coroutine]`** holding `rmut: &mut u64`, writes `*rmut = 11`, executes `yield;` | Caller reads `*raw` (`11`) while coroutine is `Yielded` | Resumes and reads `*rmut` (`11`) | **Pass (`rc = 0`)** | `Coroutine::resume(Pin<&mut Self>, ())` **returns**, retiring its `FnEntry` protector at `yield`; `Unique -> Frozen` succeeds! |

**Critical soundness consequence (`StackPoolAndCfi.two_entry_switch_preserves_protectors_and_disjointness`
and `dormant_stack_tree_borrows_complete_matrix`):** A stack-switching trampoline
verifier **must not** model `fiber_yield` / `context_switch` as retiring or
suspending the outgoing stack's `protected_tags`. Because `stack_a_frame` has not
returned at the MIR level, LLVM's `noalias` attributes on `x: &mut u64` span the
entire activation of `stack_a_frame` across the assembly call, so `poolActiveProtectors`
must remain the union of protectors across **both** the `Active` stack and all
`Dormant` stacks in `StackPool`.

#### 1.3 Cross-ISA Stack-Root `DW_CFA_undefined` (`0x07`) Asymmetry and `unwinding 0.2.10` Divergence

Basis: `normative` (DWARF v4/v5 §6.4, SysV AMD64 psABI, Arm AAPCS64 DWARF §4.1) + `source` + `execution`

Every newly spawned thread, kernel bootstrap stack, or symmetric fiber stack
requires a **root FDE** telling DWARF `.eh_frame` unwinders (`_Unwind_Backtrace`,
`_Unwind_RaiseException`) that no caller frame exists above `stack_top`. Production
Fuchsia/Zircon code uses `.cfi_undefined` on the return-address column across all
three supported architectures—e.g., `sdk/lib/c/threads/thread-start.cc:240`
(`.cfi_undefined %%rip` in `ThreadStart::AsmTrampoline`) and
`zircon/kernel/arch/riscv64/mp.cc:131` (`.cfi_undefined ra`).

However, omitting `.cfi_undefined` produces **completely different failure modes**
on x86-64 vs. AArch64—and exposes an implementation divergence between
`libgcc_s`/`llvm-libunwind` and Rust's `no_std` `unwinding 0.2.10` crate:

1. **x86-64 (`rustc 1.102.0-nightly` + `libgcc_s`, Suite 1B):**
   LLVM's x86-64 CIE initializes `CFA = RSP + 8` and `RIP = [CFA - 8]`. When a
   root trampoline enters with `RSP == stack_top` directly below an unmapped
   `PROT_NONE` upper guard page:
   - **With `.cfi_def_cfa rsp, 0; .cfi_undefined rip; .cfi_undefined rbp`**
     (`fiber_root_good_x64`, `DW_CFA_undefined: RIP` verified via
     `llvm-dwarfdump --eh-frame`): `_Unwind_Backtrace` halts cleanly with
     `_URC_END_OF_STACK` (`5`) after `3` frames (`good_bt`: `rc = 0`);
     `catch_unwind` inside Stack B runs `Drop` (`drops = 1`) and yields cleanly
     back to Stack A (`good_catch`: `rc = 0`); and an uncaught panic at Stack B's
     root cleanly detects `_URC_END_OF_STACK` and aborts via `SIGABRT`
     (`good_uncaught`: `rc = -6`).
   - **Without `.cfi_undefined rip`** (`fiber_root_bad_x64`): the unwinder
     evaluates `RIP = [RSP + 8 - 8] = [stack_top]` inside the `PROT_NONE` guard
     page, crashing both `_Unwind_Backtrace` (`bad_bt`) and uncaught Phase-1
     unwinding (`bad_uncaught`) with **`SIGSEGV` (`rc = -11`)**.
2. **AArch64 (`rustc 1.99.1` + `qemu-aarch64 11.1.2` + `unwinding 0.2.10`, Suite 1C):**
   LLVM's AArch64 CIE emits `DW_CFA_def_cfa: WSP +0` and **zero initial register
   rules** for `W30` (`x30` / `LR`).
   - Under **DWARF for the Arm 64-bit Architecture (AAPCS64) §4.1** (implemented
     by `libgcc_s` and `llvm-libunwind`), callee-saved registers and `x30` (`LR`)
     default to **`SameValue`** when omitted from the CIE. At a stack root
     (`SP = stack_top`, `LR = root_call_return_pc`) that invokes `blr x20`
     without spilling `x30`, `SameValue` sets the unwound caller context to
     `(SP' = CFA = stack_top, PC' = LR = root_call_return_pc)`—an **exact
     fixed point**! In Suite 1C (`fiber_root_bad_sameval_a64`), `_Unwind_Backtrace`
     repeats the exact same PC **22 times** before hitting our 25-frame cap
     (`bad_sameval_bt_loop`: `rc = 22`), and an uncaught panic (`_Unwind_RaiseException`
     Phase 1, which has no frame cap) **hangs in an infinite loop**
     (`bad_sameval_uncaught_phase1_hang`: `timed_out = true` at `1.2 s`).
   - Conversely, a root FDE with `.cfi_offset x30, 0` (`fiber_root_bad_deref_a64`)
     dereferences `[stack_top]` and crashes with **`SIGSEGV` (`rc = -11`)** in
     both backtrace and Phase-1 unwind (`bad_deref_bt`, `bad_deref_uncaught`).
   - **Real-world unwinder divergence in `unwinding 0.2.10`:** Direct inspection
     of `unwinding-0.2.10/src/unwinder/frame.rs:145-169` reveals:
     ```rust
     new_ctx[Arch::SP] = cfa as _;
     new_ctx[Arch::RA] = 0;
     for (reg, rule) in row.registers() { ... }
     ```
     Because `gimli::UnwindTableRow::registers()` (`gimli 0.34.0`) yields only
     registers with an explicit CIE/FDE rule, `unwinding 0.2.10` treats an
     **unmentioned** `x30` as `RA = 0` (`Undefined`) rather than AAPCS64
     `SameValue`! In Suite 1C (`mode 8`, `fiber_root_omitted_a64`), omitting all
     `x30` CFI directives appears to "succeed" under `unwinding 0.2.10`
     (`bt_frames = 4, repeats = 0`), silently masking a bug that infinite-loops
     under `libgcc_s` / `llvm-libunwind` (and conversely causing `unwinding 0.2.10`
     to truncate asynchronous signal/interrupt unwinds prematurely in leaf
     functions where `x30` genuinely holds the caller return address in `SameValue`).
   - **Unique portable contract (`StackPoolAndCfi.stack_root_cfi_undefined_halts_cleanly`):**
     Emitting explicit `.cfi_undefined x30` (`DW_CFA_undefined: W30`) and
     `.cfi_undefined x29` halts cleanly across **both** AAPCS64 `SameValue`
     unwinders and `unwinding 0.2.10` (`good_bt`: `4` frames, `0` repeats;
     `good_catch`: `rc = 0, drops = 1`; `good_uncaught_end_of_stack`: returns
     `_URC_END_OF_STACK = 5`, `exit_code = 55`).
3. **13-opcode `Trusted.DwarfCfi` admission rule (extending the 12-opcode model):**
   `Trusted.DwarfCfi` should admit `DW_CFA_undefined` (`0x07`) as its 13th
   opcode **solely in FDEs explicitly declared as stack roots** (where `RA`—and
   optionally `FP`—must become `.undefined` before the first call instruction),
   while continuing to reject `DW_CFA_undefined` inside all ordinary function and
   inline-`asm!` FDEs so untrusted inline assembly cannot truncate caller
   unwinding. (Separately, kernel/runtime signal or restricted-mode frames such
   as Starnix `trampoline_arm64.S:101,167` and `corosensei`
   `src/arch/x86_64.rs:195,247` require explicit `zRS` `.cfi_signal_frame`,
   arbitrary-offset `DW_CFA_def_cfa_expression`, and AArch64 pseudo-register `32`
   `PC` recovery, which remain outside ordinary crate CFI admission; see
   **Boundaries**.)

---

### 2. `global_asm!` & Perlasm `.S` Multi-Entry Layout, `st_size == 0` Bugs, and Section-Wide Entry-Cutpoint Graphs (`SWECG`)

#### 2.1 Why `global_asm!` and Perlasm `.S` Shatter Per-Symbol Lifting

Basis: `source` + `execution` (`support/reproduce_all_probes.py`, `support/empirical_receipts.json`)

In `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da`, Rust's three
assembly forms take fundamentally different compiler paths:

- **`core::arch::asm!`** lowers to `MirTerminator::InlineAsm` inside a MIR body,
  preserving surrounding MIR CFG edges and register/clobber bindings.
- **`#[unsafe(naked)]` + `naked_asm!`** (`compiler/rustc_codegen_ssa/src/mir/naked_asm.rs:18-60,245-290`)
  automatically wraps a **single** Rust item in `.pushsection .text.<sym>,"ax"`,
  `.globl <sym>`, `.type <sym>, @function`, and `.size <sym>, . - <sym>`.
- **`core::arch::global_asm!`** (`compiler/rustc_codegen_llvm/src/asm.rs:413-526`)
  concatenates raw template strings and hands them directly to
  `llvm::append_module_inline_asm` (`L520`), **completely bypassing MIR**,
  function-section isolation, and automatic `.size` synthesis.

Inspecting production `.S` and `global_asm!` corpora confirms four pervasive
ELF object patterns that break per-symbol lifters:

1. **Missing `.size` directives (`st_size == 0` on `STT_FUNC` and `STT_NOTYPE`
   globals):**
   - In `aws/aws-lc@cd481c207e38f06aeb5766f4a1cdfce10a4c0af8`,
     `generated-src/linux-x86_64/crypto/fipsmodule/aesni-xts-avx512.S` (`120,490` B)
     exports `2` `.globl` functions (`aes_hw_xts_encrypt_avx512`,
     `aes_hw_xts_decrypt_avx512`) with **`0` `.size` directives** (`st_size = 0`).
   - `crypto/test/trampoline-x86_64.S` exports `39` `.globl` symbols with only
     `36` `.size` directives because `abi_test_unwind_start`,
     `abi_test_unwind_return`, and `abi_test_unwind_stop` are interior `.globl`
     code labels (`st_size = 0`) inside `abi_test_trampoline`.
   - `Amanieu/corosensei@4b5db4845204` (`src/arch/mod.rs:92-110`,
     `src/arch/x86_64.rs:297`) emits `asm_function_alt_entry!("stack_init_trampoline_return")`
     inside `stack_init_trampoline` as `.globl stack_init_trampoline_return; .type ..., @function`
     with **no matching `asm_function_end!`** (`st_size = 0` on ELF; `.alt_entry`
     on Mach-O).
2. **Symbol-to-symbol fallthroughs:** Fast-path wrappers (and prologue entry
   variants) omit `jmp` and fall directly through the next `.globl` label.
3. **Shared `.L` local tail-helpers across `.size`-bounded symbols:** `21` of
   `26` x86-64 `.S` files in `aws-lc` (`aesni-x86_64.S` has `9` globals and `20`
   sized local/global routines) and symmetric fiber trampolines (`fiber_enter` +
   `fiber_yield` sharing `.Lfiber_restore_common`) jump out of `[st_value, st_value + st_size)`
   into a shared `STB_LOCAL` helper.
4. **Backward cross-symbol jumps and inline `.text` constant pools:** Starnix
   `restricted_return_loop` (`trampoline_x64.S:164,171`) jumps **backward** to
   `.restricted_enter_loop_ret` inside the preceding symbol `restricted_enter_loop`,
   while Perlasm modules place `.quad`/`.byte` round constants inside `.text`
   addressed via `[rip + .Lconst]`.

#### 2.2 Empirical Failure Matrix of Naive ELF Lifters vs. `SWECG` (Suite 2)

Basis: `execution` (`support/reproduce_all_probes.py`, `support/empirical_receipts.json`) + `derived`

Suite 2 compiles both a 7-symbol `rustc 1.102.0-nightly` `.o` (`regular_asm_fn`,
`naked_single_fn`, and a 5-entry, 61-byte `.text.gasm_cluster` `global_asm!`
section containing fallthrough, `.Lshared_tail`, embedded `.quad 0x64` at `0x20`,
and a 2-entry backward cross-symbol branch) and a `gcc 15.2.0` Perlasm-style
`.S` object (`perlasm_specimen.o`, confirming `st_size = 0` on all 3 `.globl`
symbols):

| Symbol in `.text.gasm_cluster` (`61` B) | `.symtab` `(st_value, st_size)` | Runtime Result (`x = 7`) | Naive Lifter A: `[st_value, st_value + st_size)` | Naive Lifter B: `[st_value, next_global_sym)` | `SWECG` Section-Wide Cutpoint Lifter |
| :--- | :---: | :---: | :--- | :--- | :--- |
| `gasm_nosize_fast` (falls through to `0x04`) | `(0, 0)` | `144` | **`BUG_ZERO_BYTE_SLICE_VACUOUS`** (0 bytes checked!) | **`out_of_bounds_pc:4`** (fallthrough truncated at `0x04`) | **Verified** (`cutpoint 0x0 -> 0x4 -> 0x10`, `ret`) |
| `gasm_nosize_common` (`jmp .Lshared_tail` at `0x10`) | `(4, 0)` | `124` | **`BUG_ZERO_BYTE_SLICE_VACUOUS`** | **`out_of_bounds_pc:12`** (`[4, 10)` excludes `0x10`) | **Verified** (`cutpoint 0x4 -> 0x10`, `ret`) |
| `gasm_sized_with_shared_tail` (`.size = 6`, `jmp 0x10`) | `(10, 6)` | `154` | **`BUG_out_of_bounds_pc:6`** (`.Lshared_tail` outside `.size`!) | Slices `[10, 40)` (`30` B, includes `.Linline_const` at `0x20`!) | **Verified** (`cutpoint 0xa -> 0x10`, `ret`) |
| `gasm_two_entry_enter` (`.size = 12`, `0x28..0x34`) | `(40, 12)` | `107` | `OK` | `OK` (`12` B) | **Verified** (`cutpoint 0x28 -> 0x30`, `ret`) |
| `gasm_two_entry_alt` (2nd entry at `0x34`, `jmp 0x30`) | `(52, 0)` | `307` | **`BUG_ZERO_BYTE_SLICE_VACUOUS`** | **`out_of_bounds_pc:-4`** (backward jump into `gasm_two_entry_enter`!) | **Verified** (`cutpoint 0x34 -> 0x30`, `ret`) |

Across the entire 61-byte `.text.gasm_cluster` section, `SWECG` visits exactly
`15` instructions (`49` executable bytes, `8` `.Linline_const` read-only data
bytes, `4` alignment-padding bytes at `0x1c..0x20`, `exec_rodata_disjoint = true`,
`decode_errors = []`) and identifies the exact minimal 7-cutpoint set
`[0x0, 0x4, 0xa, 0x10, 0x28, 0x30, 0x34]`.

#### 2.3 Exact Section-Wide Entry-Cutpoint Graph (`SWECG`) Attribution Rules

Basis: `derived` + `execution` (`SectionWideAsmCfg.swecg_cutpoint_sound`, `swecg_verifies_five_entry_cluster`)

To verify `global_asm!` and external `.S` ELF relocatable objects without trusting
`.size` or symbol-partition heuristics, the lifter operates at **executable
section granularity** (`(S, R_S)` for each section `S` with `SHF_ALLOC | SHF_EXECINSTR`
and its `SHT_RELA` table `R_S`):

1. **Root Entry Set $E(S)$:** Collect every byte offset `sym.st_value` in `S`
   such that either (a) `sym` has non-local binding (`STB_GLOBAL` or `STB_WEAK`)
   and is imported by an `extern` declaration or exported from the crate, or (b)
   `sym` (including `STB_LOCAL`) is referenced as a relocation target in any
   code/data/vtable section (`SHT_RELA`, e.g., `leaq restricted_return_loop(%rip)`
   or `SimFileOperations` function pointers). **Never skip an entry because
   `st_size == 0`** (`canary_st_size_zero_vacuous_accepts_faulting_body`).
2. **Demand-Driven Reachable Instruction Closure $V_{\text{exec}}(S)$:** Starting
   from worklist $E(S)$, decode instructions over `[0, S.sh_size)` (resolving
   intra-section PC-relative branches directly and resolving relocated `call`/`jmp`
   targets exclusively via `R_S`). Fail closed on any out-of-section branch,
   unrelocated indirect jump without a proved jump-table bound, or mid-instruction
   overlapping jump target (unless explicitly proven safe, though disallowing
   overlapping instruction encodings is strictly cleaner).
3. **Code/Data Disjointness ($V_{\text{exec}}(S) \cap D_{\text{rodata}}(S) = \emptyset$):**
   Record every intra-section `[rip + disp]` memory load range in $D_{\text{rodata}}(S)$
   and enforce $V_{\text{exec}}(S) \cap D_{\text{rodata}}(S) = \emptyset$ (and zero
   writes to `S`), permitting Perlasm `.quad`/`.byte` constant pools inside
   `.text` while guaranteeing data bytes are never executed (`SwecgCertificate.dataReadSafe`).
4. **Cutpoint Attribution & Shared-Helper Deduplication:** Define cutpoints
   $C(S) = E(S) \cup \{pc \in V_{\text{exec}}(S) \mid |\text{preds}(pc)| > 1 \lor \text{hasBackEdge}(pc)\}$.
   Shared local helpers (`.Lshared_tail` at `0x10`, `.Lepilogue_in_enter` at
   `0x30`) automatically have $|\text{preds}(pc)| \ge 2$, becoming first-class
   cutpoints verified **once** against a relational summary (`cert.spec c`) with
   well-founded rank `cert.rank c` on acyclic fallthrough/tail edges
   (`SectionWideAsmCfg.swecg_cutpoint_sound`).

---

### 3. Temporally Disjoint C Ops-Table Vtables and COFE-Free `ForeignOwnable` Typestate

#### 3.1 Why Stack-Nested `LinkFrame`s Cannot Represent C Vtable Lifecycles—and Where Linux Drivers Break

Basis: `source` + `execution` (`support/reproduce_all_probes.py`, `support/empirical_receipts.json`)

In Fuchsia `fdf_sys` (`sdk/lib/driver/runtime/rust/fdf_sys/src/bindings.rs:120-205`)
and Rust-for-Linux (`rust/kernel/types.rs:32-153`, `rust/kernel/miscdevice.rs:260-355`),
ownership crosses FFI **temporally disjointly** across separate top-level C-to-Rust
calls:

1. `MiscDeviceRegistration::open` (`rust/kernel/miscdevice.rs:274`) executes
   `unsafe { (*raw_file).private_data = ptr.into_foreign() };` and returns `0` to
   Linux's `do_dentry_open` (`fs/open.c:1000`), **popping the Rust `open` stack
   frame completely**.
2. Later syscalls invoke `read_iter`, `write_iter`, or `unlocked_ioctl`, which
   call `<T::File as ForeignOwnable>::borrow(private)` or `borrow_mut(private)`.
3. Eventually `__fput` (`fs/file_table.c:486-518`) invokes `f_op->release`, which
   reclaims ownership via `ForeignOwnable::from_foreign(private)` (`miscdevice.rs:287`)
   and drops the Rust object.

Direct source audit of `torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2`
combined with our live `gcc 15.2.0` + `rustc 1.102.0-nightly` + Miri
(`-Zmiri-tree-borrows`) harness (Suite 3) exposes three distinct soundness
hazards:

| Lifecycle Hazard | Upstream Linux Mechanism (`torvalds/linux@5f22fb20497f`) | Native `gcc 15.2.0` + Rust Harness (`empirical_receipts.json`) | Miri `-Zmiri-tree-borrows` Outcome (`empirical_receipts.json`) |
| :--- | :--- | :--- | :--- |
| **Bug 1: `open` returns non-zero after `into_foreign`** | `do_dentry_open` (`fs/open.c:1000-1004`) sets `f->f_mode \|= FMODE_OPENED;` **only if `open(inode, f) == 0`** (`if (error) goto cleanup_all;`). When the caller later drops `struct file`, `__fput` (`fs/file_table.c:493`) checks `if (unlikely(!(mode & FMODE_OPENED))) goto out;` and **skips `f_op->release` completely**! (Note: by contrast, if `open` returns `0`, line `1004` sets `FMODE_OPENED` *before* line `1021`'s `O_DIRECT && !FMODE_CAN_ODIRECT` `-EINVAL` check, so caller `fput` *does* invoke `release` in that post-`1004` error path.) | `bug1_open_rc = -22` (`-EINVAL`), `bug1_drops = 0`, **`bug1_leaked_handles = 1`** (permanent kernel heap/resource leak; or dangling `private_data` if driver freed without clearing) | **`v1` Fails (`rc = 1`)**: `error: memory leaked: alloc... (Rust heap, size: 8, align: 8)` |
| **Bug 2: Reentrant `ioctl -> C -> ioctl` under `Box::borrow_mut`** | Whereas `<Arc<T> as ForeignOwnable>` (`rust/kernel/sync/arc.rs:370`) restricts `type BorrowedMut<'a> = ArcBorrow<'a, T>` (preventing `&mut T` creation), **`<Box<T, A> as ForeignOwnable>::borrow_mut`** (`rust/kernel/alloc/kbox.rs:543-548`) unconditionally executes `unsafe { &mut *ptr }` with **zero dynamic borrow tracking**! Any C helper called during `ioctl` (e.g., notifier, nested VFS/driver helper, or fault handler on the same `file`) that re-enters an ops callback on `private_data` creates aliasing `&mut T` while outer `ioctl`'s `FnEntry` `StrongProtector` is active | Outer `buggy_ioctl` caches `st.accum` across `c_reentrant_observer(f)`, silently overwriting the nested `+100` update (lost update) | **`v2` Immediate UB (`rc = 1`)**: `Undefined Behavior: read access through <...> at alloc...[0x0] is forbidden` |
| **Bug 3: Double `release` / post-`release` `ioctl` (`from_foreign` twice)** | Manual C ops wrappers or custom driver teardown paths invoking `ForeignOwnable::from_foreign(private)` without linear state consumption and `private_data` nulling | Unguarded `buggy_release` double-frees; `sound_release` nulls `private_data` and rejects a second call with `-22` (`sound_second_release_rc = -22`) | **`v3` Immediate UB (`rc = 1`)**: `constructing invalid value of type std::boxed::Box<u64>: encountered a dangling box (use-after-free)` |
| **Sound Guarded `ForeignHandlePool` Protocol** | Validate all fallible preconditions *before* `into_foreign` (or reclaim on error before returning non-zero); use `Shared(n)` (`&T` + interior `Cell`/lock) or dynamic `loan_state` failing closed with `-EBUSY` (`-16`) on reentrant `MutLoaned`; null `private_data` upon `Owned -> Freed` | `sound_reentrant_shared_val = 115`, `sound_reentrant_mut_ebusy = -16`, `sound_drops = 1`, `sound_live_after_fput = 0` | **`v4` Passes (`rc = 0`)** with zero UB and zero leaks |

#### 3.2 Why Step-Indexing / Iris COFEs Are Unnecessary: First-Order Linear `ForeignHandlePool`

Basis: `derived` + `execution` (`ForeignOwnableVtable.cofe_free_vtable_trace_sound`, `reentrant_shared_ioctl_arbitrary_depth_sound`)

Higher-order multi-language logics such as Melocoton and Cerise require Iris
COFEs (`ofeT`), step-indexing (`Nat`-indexed approximations), and impredicative
invariants (`inv N P`) only when untrusted C heaps store higher-order closures
whose semantic specifications quantify circularly over the heap world itself
(Landin's knot).

C subsystem ops tables (`struct file_operations`, `fdf_driver_ops_t`) do **not**
store higher-order closures in `private_data`:

1. The vtable (`static SOUND_FOPS: SimFileOperations`) is a **fixed, static vector
   of first-order code entry points** whose specs are stratified before any
   execution begins.
2. `file->private_data` is an **opaque first-order capability token** (`HandleId`)
   indexing into a ghost `ForeignHandlePool` mapping each `HandleId` to a finite
   5-state linear automaton:
   $$\text{HandleState} ::= \text{Unallocated} \mid \text{Owned} \mid \text{Shared}(n : \mathbb{N}) \mid \text{MutLoaned} \mid \text{Freed}$$
3. Across every C return boundary (when no callback for `file` is on the call
   stack), `VtableInv` asserts a purely first-order Kripke invariant:
   - If `fModeOpened = false`, then `privateData = none` and **every** `hid` is
     inactive (`Unallocated ∨ Freed`)—structurally ruling out Bug 1 leaks.
   - If `fModeOpened = true`, then `privateData = some hid` with `stateOf hid = Owned`
     and every `q ≠ hid` inactive.
4. During active callbacks:
   - Shared `borrow` (`reentrantSharedIoctl`) transitions `Owned -> Shared 0 ->
     Shared 1 -> ... -> Shared depth -> ... -> Owned`, allowing **unbounded**
     reentrant `C -> Rust -> C -> Rust` callback nesting (`reentrant_shared_ioctl_arbitrary_depth_sound`).
   - Exclusive `borrow_mut` (`checkedMutReentrantIoctl`) transitions
     `Owned -> MutLoaned -> Owned` and fails closed (`-EBUSY = -16`) if re-entered
     while `MutLoaned`—ruling out Bug 2 `&mut` aliasing UB.
   - `fputClose` (`from_foreign`) requires `stateOf hid = Owned` (so closing
     while `Shared n` or `MutLoaned` is active is rejected), transitions
     `Owned -> Freed`, and clears `fModeOpened := false, privateData := none`—ruling
     out Bug 3 double-free/UAF.

In `support/StackSwitchGlobalAsmAndForeignVtable.lean`, `cofe_free_vtable_trace_sound`
proves by plain structural induction over `evs : List VfsEvent`—using **only**
`[propext, Quot.sound]` (`0` `Classical.choice`, `0` COFEs, `0` step-indices)—that
every finite C VFS trace preserves `VtableInv` without leaks, aliasing, or UAF.

---

## Boundaries

To prevent over-generalizing these results, the following negative-space
boundaries apply:

- **Unsupported by Miri (`unsupported`):** Raw `asm!` / `global_asm!` stack
  pointer pivots (`mov rsp, ...`) are explicitly unsupported by Miri (`m1`,
  `exit_code = 1`). Suite 1A isolates the Tree Borrows `StrongProtector` state
  machine across suspended vs. active Rust frames using Wasmtime's thread-gate
  fiber isomorphism (`crates/fiber/src/miri.rs`); stack-pointer switching,
  guard-page faults, and DWARF `.eh_frame` unwinding are verified natively on
  x86-64 (`Suite 1B`) and under `qemu-aarch64` (`Suite 1C`), not inside Miri.
- **Known not to apply to stackless Rust `#[coroutine]` yields (`known not to apply`):**
  The dormant-stack `StrongProtector` hazard (`m2d`, where a foreign read of an
  activated `&mut T` causes immediate UB while suspended) **does not apply** to
  compiler-transformed stackless `#[coroutine]` blocks (`m2g`). Because
  `Coroutine::resume` returns `CoroutineState::Yielded` as an ordinary Rust
  return, its `FnEntry` protector ends at `yield`, allowing a foreign read while
  yielded to demote `Unique -> Frozen` legally so long as the coroutine only
  reads upon resumption.
- **Known not to apply to interior non-root FDEs (`known not to apply`):**
  Admitting `DW_CFA_undefined` (`0x07`) on `RIP`/`X30` applies **only** to
  designated stack-root FDEs (`_start`, `ThreadStart`, fiber root trampolines).
  Admitting `.cfi_undefined rip` inside an ordinary Rust function's inline
  `asm!` block remains unsound because it truncates unwinding before callers'
  `Drop` landing pads can run.
- **Known not to apply to higher-order self-referential C heap closures (`known not to apply`):**
  Our COFE-free `ForeignHandlePool` completeness proof relies on C storing
  first-order opaque handles (`void *private_data`) dispatched through static
  ops tables. If untrusted foreign code dynamically constructs and mutates
  self-referential higher-order function closures inside shared heap memory
  whose specifications quantify impredicatively over the heap invariant itself,
  step-indexed Kripke/Iris worlds become necessary.
- **Signal frames, `DW_CFA_def_cfa_expression` parent-stack links, and non-ELF
  targets (`not examined` / out of 13-opcode core):**
  - Cross-stack *linked* unwinding—where unwinding off the bottom of child
    Stack B automatically teleports into parent Stack A via `corosensei`'s
    `.cfi_signal_frame` + `DW_CFA_def_cfa_expression` (`[DW_OP_breg6 0, DW_OP_deref,
    DW_OP_plus_uconst 24]`, `src/arch/x86_64.rs:195,247`) or Starnix's
    `zx_restricted_state_t` CFI bridge (`.cfi_escape 0x11, 32, 0x40` on AArch64
    pseudo-register `32` `PC`, `trampoline_arm64.S:101,167`)—was inspected in
    source, but the mechanized 13-opcode `StackPoolAndCfi` unwinder models
    **isolated** stack roots (`DW_CFA_undefined` -> `.endOfStack` + explicit
    `catch_unwind` across fiber boundaries, as used by Wasmtime and Zircon thread
    roots) rather than automatic cross-stack unwind teleportation.
  - Windows x64 / UEFI PE32+ `.pdata`/`.xdata` SEH directives (`.seh_setframe`,
    `.seh_savereg`), Mach-O `.alt_entry` subsection-via-symbols splitting,
    32-bit ARM EHABI (`.ARM.exidx`), hardware Shadow Call Stack (`x18` in
    `trampoline_arm64.S:35,110`), AArch64 PAC (`paciasp`/`autiasp`), and x86-64
    CET shadow stacks (`RDSSP`/`RSTORSSP`/`SAVEPREVSSP`) were **not examined**
    by execution.
- **Concurrent multi-CPU `file_operations` (`unknown` without atomic typestate):**
  Suite 3 and `ForeignOwnableVtable` model sequential and arbitrarily deep
  single-thread reentrant `C -> Rust -> C` callbacks (`Cell`-backed `loan_state`
  or ghost `Shared(n)`/`MutLoaned`). On real SMP Linux kernels, `read_iter`,
  `write_iter`, and `unlocked_ioctl` execute concurrently across CPUs on the
  same `struct file *` without a VFS-level per-file mutex; therefore, production
  drivers must either restrict `ForeignOwnable` borrows to `&T` (`Shared` with
  `Sync` interior synchronization such as `SpinLock`/`Mutex`, which is why
  `Arc<T>`'s `BorrowedMut` is `ArcBorrow<'a, T>` rather than `&'a mut T`) or
  maintain an `AtomicIsize` loan counter. Whether any in-tree Linux 6.x/7.x Rust
  driver calls `<Box<T> as ForeignOwnable>::borrow_mut` inside an unlocked VFS
  callback was **not examined** across the full kernel tree; only `types.rs`,
  `kbox.rs`, `arc.rs`, and `miscdevice.rs` were audited directly.

---

## Evidence

### 1. Primary Source Inspections

All repository revisions below are full immutable 40-character Git commit SHAs:

- **Fuchsia (`https://fuchsia.googlesource.com/fuchsia@4799c98e7566bf11f1bb3f07dfea86173f00e336`):**
  - `src/starnix/kernel/syscall_loop/src/trampoline_x64.S:20-87`
    (`restricted_enter_loop`, `.restricted_enter_loop_top` at `L51`,
    `leaq restricted_return_loop(%rip), %rsi` at `L62`, `.restricted_enter_loop_ret`
    at `L73`) and `L95-173` (`restricted_return_loop`, `mov %rdi, %rsp` at `L97`,
    `.cfi_def_cfa r14, 0` + 17 `.cfi_offset` directives at `L121-141`, and
    cross-symbol `je .restricted_enter_loop_ret` / `jmp .restricted_enter_loop_top`
    at `L164,171`).
  - `src/starnix/kernel/syscall_loop/src/trampoline_arm64.S:19-89` and `L97-201`
    (`.cfi_signal_frame` at `L101`, `mov sp, x0` at `L104`, `.cfi_escape 0x11, 32, 0x40`
    for DWARF register 32 `PC` at `L167`, `cbz x0, .restricted_enter_loop_ret` at
    `L192`, `b .restricted_enter_loop_top` at `L199`).
  - `zircon/kernel/arch/x86/asm.S:20-49` (`x86_64_context_switch`),
    `zircon/kernel/arch/arm64/asm.S:22-70` (`arm64_context_switch`),
    `sdk/lib/c/threads/thread-start.cc:236-263` (`.cfi_undefined %%rip` at `L240`),
    `zircon/kernel/arch/riscv64/mp.cc:131` (`.cfi_undefined ra`), and
    `sdk/lib/driver/runtime/rust/fdf_sys/src/bindings.rs:120-205`.
- **Linux Kernel (`torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2`):**
  - `rust/kernel/types.rs:32-153` (`pub unsafe trait ForeignOwnable`).
  - `rust/kernel/alloc/kbox.rs:508-549` (`unsafe impl<T, A> ForeignOwnable for Box<T, A>`,
    with `unsafe fn borrow_mut<'a>(ptr: *mut c_void) -> &'a mut T { unsafe { &mut *ptr.cast() } }`
    at `L543-548`).
  - `rust/kernel/sync/arc.rs:366-402` (`ForeignOwnable for Arc<T>` setting
    `type BorrowedMut<'a> = ArcBorrow<'a, T>` at `L370`).
  - `rust/kernel/miscdevice.rs:260-355` (`open` storing `ptr.into_foreign()` at
    `L274`; `release` calling `from_foreign` at `L287`).
  - `fs/open.c:997-1037` (`do_dentry_open`: `error = open(inode, f); if (error) goto cleanup_all;`
    at `L1000-1002` before `f->f_mode |= FMODE_OPENED;` at `L1004`; post-`FMODE_OPENED`
    `O_DIRECT` check at `L1021-1022`) and `fs/file_table.c:486-518` (`__fput`
    skipping `release` when `!(mode & FMODE_OPENED)` at `L493`).
- **Coroutines, Unwinders, Compilers, and Perlasm (`REPORT.json`):**
  - `Amanieu/corosensei@4b5db4845204a4b2663d3f7f75866be4cc3c680d`:
    `src/arch/mod.rs:92-115` (`asm_function_alt_entry!` without `.size` on ELF),
    `src/arch/x86_64.rs:175-357`, `src/arch/aarch64.rs:190-210`.
  - `bytecodealliance/wasmtime@40e0d780e4bfa34325d342db5bcf492bea227e07`:
    `crates/fiber/src/miri.rs:1-261` and `crates/fiber/src/stackswitch/{x86_64,aarch64}.rs`.
  - `unwinding 0.2.10` (`crates.io`): `src/unwinder/frame.rs:134-172`
    (`new_ctx[Arch::RA] = 0;` at `L146`).
  - `aws/aws-lc@cd481c207e38f06aeb5766f4a1cdfce10a4c0af8`:
    `generated-src/linux-x86_64/crypto/fipsmodule/aesni-xts-avx512.S` (`0` `.size`
    directives across `2` `.globl` functions, SHA-1 `9fd0f115acd508d37994089155040029ac938f7c`),
    `crypto/test/trampoline-x86_64.S` (`3` interior `st_size = 0` `.globl` labels),
    and `crypto/fipsmodule/aesni-x86_64.S` (`9` globals, `20` `.size` routines,
    SHA-1 `cb186b7f08aa803176c2ed074ee644a49c910973`).
  - `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da`:
    `compiler/rustc_codegen_llvm/src/asm.rs:413-526` (`codegen_global_asm`) vs.
    `compiler/rustc_codegen_ssa/src/mir/naked_asm.rs:18-60,245-290` (`codegen_naked_asm`).

### 2. Preserved Support Artifacts in This Package

1. **`support/StackSwitchGlobalAsmAndForeignVtable.lean`** (`1,330` lines, pure
   `Init.*` Lean `v4.34.1`, `0` `sorry`, `0` warnings):
   - `SectionWideAsmCfg`: `canary_st_size_zero_vacuous_accepts_faulting_body`,
     `canary_st_size_rejects_shared_local_tail_helper`,
     `canary_next_sym_partition_breaks_fallthrough_and_cross_sym_jump`,
     `swecg_cutpoint_sound`, and `swecg_verifies_five_entry_cluster`.
   - `StackPoolAndCfi`: 13-opcode `CfiOp` (`DW_CFA_undefined`),
     `stack_root_cfi_undefined_halts_cleanly`, `canary_x64_missing_undef_reads_unmapped`,
     `canary_a64_missing_undef_sameval_loops_forever`,
     `two_entry_switch_preserves_protectors_and_disjointness`, and
     `dormant_stack_tree_borrows_complete_matrix`.
   - `ForeignOwnableVtable`: COFE-free `VtableWorld` (`HandleState`),
     `reentrant_shared_ioctl_arbitrary_depth_sound`, `cofe_free_vtable_trace_sound`,
     `canary_bug1_open_nonzero_after_into_foreign_leaks_handle`,
     `canary_bug2_reentrant_unguarded_borrow_mut_aliasing_ub`, and
     `canary_bug3_double_release_from_foreign_uaf`.
   - Verified with `#guard_msgs in #print axioms` across all 12 top-level
     theorems/canaries (within `{propext, Classical.choice, Quot.sound}`;
     `cofe_free_vtable_trace_sound` uses only `[propext, Quot.sound]`) and
     replayed through a fresh `trustLevel := 0`, `loadExts := false`,
     `level := .private` Lean kernel (`1,307` replayed constants).
2. **`support/reproduce_all_probes.py`**: Self-contained Python 3 driver running
   all five empirical suites inside `tempfile.TemporaryDirectory()` (leaving zero
   build artifacts behind) and emitting structured JSON receipts.
3. **`support/empirical_receipts.json`**: Recorded execution outputs from
   `reproduce_all_probes.py` on `2026-11-21` across Suite 1A (Miri dormant-stack
   Tree Borrows `m1`–`m2g`), Suite 1B (native x86-64 `global_asm!` 2-entry fiber
   trampolines), Suite 1C (`qemu-aarch64` bare-metal AArch64 2-entry fiber
   trampolines with `unwinding 0.2.10`), Suite 2 (`rustc` `global_asm!` + `gcc`
   `.S` ELF64 symbol/CFG lifters), and Suite 3 (`gcc 15.2.0` + Rust + Miri
   `ForeignOwnable` C ops-table harness).

---

## Revalidation

1. **Re-check the Lean `v4.34.1` mechanization (`~4.2 s`, zero external dependencies):**
   Compile `support/StackSwitchGlobalAsmAndForeignVtable.lean` with synchronous
   kernel typechecking enabled into a temporary `.olean` and verify zero
   diagnostics and zero `sorry`:
   ```bash
   TMP_OLEAN="$(mktemp /tmp/stack_switch_XXXXXX.olean)"
   trap 'rm -f "$TMP_OLEAN"' EXIT
   ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 lean \
     -DElab.async=false -Ddebug.skipKernelTC=false \
     support/StackSwitchGlobalAsmAndForeignVtable.lean -o "$TMP_OLEAN"
   ```
   Every `#guard_msgs in #print axioms` assertion at the bottom of the file will
   fail compilation immediately if any theorem acquires an unexpected axiom or if
   any `rfl` / inductive invariant breaks under a newer Lean 4 release.
2. **Re-run all five empirical compiler, Miri, QEMU AArch64, ELF64, and C vtable
   suites (`~40 s`):**
   ```bash
   python3 -B support/reproduce_all_probes.py
   ```
   Requires `rustc +nightly` with `miri`, `rustc +1.99.1` with target
   `aarch64-unknown-linux-gnu` (and cached `unwinding-0.2.10` + `gimli-0.34.0`
   for Suite 1C; Suite 1C gracefully reports `{"skipped": true}` if absent),
   `gcc`, `llvm-dwarfdump`, and `qemu-aarch64`. Diff the JSON output against
   `support/empirical_receipts.json`.
3. **Targeted upstream drift checks on newer Linux, Fuchsia, `rustc`, or `unwinding` versions:**
   - *`unwinding` crate AArch64 `RA` default:* Inspect `src/unwinder/frame.rs`
     around `new_ctx[Arch::RA] = 0;`. If upstream changes unmentioned `Arch::RA`
     initialization to `ctx[Arch::RA]` (`SameValue`), Suite 1C's
     `unwinding_crate_omitted_x30_treated_as_zero` (`mode 8`) will switch from
     4 frames (`0` repeats) to the 22-repeat loop of `bad_sameval_bt_loop`
     (`mode 2`), while `good_bt` (`.cfi_undefined x30`) must continue to pass.
   - *Linux `ForeignOwnable` & VFS `FMODE_OPENED`:* Diff `rust/kernel/alloc/kbox.rs`
     (`ForeignOwnable for Box<T, A>::borrow_mut`) and `fs/open.c` (`do_dentry_open`
     `FMODE_OPENED` placement relative to `open(inode, f)`).
   - *`rustc` `global_asm!` lowering:* Diff `compiler/rustc_codegen_llvm/src/asm.rs`
     (`codegen_global_asm`) to confirm whether module-level inline assembly still
     bypasses MIR and automatic `.size` emission.
