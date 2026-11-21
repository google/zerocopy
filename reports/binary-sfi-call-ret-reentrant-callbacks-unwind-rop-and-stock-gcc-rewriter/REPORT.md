# Multi-function PIC binary SFI `call`/`ret`, host-anchored Jump-Over FDE unwinding across reentrant callbacks, `Tree Borrows` × 4 KiB zero-copy arena sharing, and untrusted stock-GCC assembly rewriting in Lean 4

## Summary

Composing byte-level x86-64 Software Fault Isolation (`checkSfiObject`) with
real multi-function C libraries, reentrant `extern "C-unwind"` Rust callbacks,
DWARF `.eh_frame` stack unwinding, and zero-copy Rust slices exposes four
cross-cutting soundness and executability fractures—each invisible when
single-function SFI, DWARF CFI integrity, and `Tree Borrows` reentrant FFI are
studied in isolation:

1. **Fixing the surrogate-`ret` (`0xC3`) control-flow escape and the Linux
   `mmap_min_addr` `code_base = 0` trap (`support/PicMultiFnSfi.lean`).**
   Modeling `0xC3` (`ret`) as `{ s with halted := true }` rather than popping
   `[%rsp]` into `rip` causes a single-function SFI verifier to admit raw `0xC3`
   inside untrusted bundles (`raw_ret_0xc3_rop_escape`), while modeling masked
   indirect branches as `and eax, mask32; jmp rax` at `code_base = 0` faults on
   every Linux host with `vm.mmap_min_addr = 65536` and PIE ASLR
   (`legacy_abs32_indirect_jmp_null_page_fault`). Reserving read-only `%r15`
   (`codeBase`), read-only `%r14` (`arenaBase`), inductive 32-bit zero-extended
   `%r13` (`guest_sp < 2^32`), and address/branch scratch `%r11` alongside
   loader-owned Portal Bundles `0` (`codeBase + 0x00`: exit `ret`) and `1`
   (`codeBase + 0x20`: hostcall trampoline jump) collapses multi-function PIC
   SFI (`checkSfiPicMultiFn`) to `0` raw `0xC3`/`push`/`pop`/`leave` opcodes in
   untrusted bundles `>= 0x40`, 1-instruction guest-stack accesses
   `disp(%r14,%r13,1)` inside symmetric `+-64 KiB` `PROT_NONE` guards, and a
   single 3-instruction PIC indirect branch/return macro (`and r11d, mask32;
   lea r11, [r15 + r11*1]; jmp r11`), mechanized end-to-end in Lean `v4.34.1`
   (`checkSfiPicMultiFn_sound`, `140,312` bytes, `0` `sorry`, `567 ms` fresh
   kernel replay).
2. **Closing the `.eh_frame` unwind-redirect and reentrant guest-stack clobber
   hazards via a Host-Anchored Jump-Over FDE Trampoline
   (`support/reproduce_unwind_rop_and_reentrant_sfi.py`,
   `support/UnwindJumpOverAndTreeBorrows.lean`).** On both `rustc 1.99.1` and
   `rustc 1.102.0-nightly` + `gcc 15.2.0`, when sandboxed C calls a reentrant
   `extern "C-unwind"` Rust callback that panics into `std::panic::catch_unwind`:
   (a) any split-stack `.eh_frame` that recovers `CFA`, `RIP`, or callee-saved
   registers (`R12..R15`, `RBP`, `RBX`) from the writable guest stack redirects
   control outside the sandbox (`rc = 42`) or silently corrupts caller `r12`
   after `catch_unwind` (`r12 = 0x5555666677778888`); (b) omitting `.eh_frame`
   on `-fno-unwind-tables` SFI `.o` frames aborts in `_Unwind_RaiseException`
   Phase 1 (`error 5`, `SIGABRT`, `outer_drops = 0`); and (c) resetting
   `guest_sp` on nested `Host_0 -> SFI_1 -> Host_cb_2 -> SFI_3` overwrites
   `SFI_1`'s paused guest frame (`0x7777888811114286 != 0x3064`). Keeping host
   `%rsp` anchored on the host stack throughout SFI execution while `Portal 1 ->
   sfi_hostcall_trampoline` pushes `%r13` on the host stack with a custom
   `.cfi_def_cfa_offset 16` Jump-Over FDE leaps arbitrarily deep intra-sandbox
   call chains in **1 FDE hop per SFI activation with zero guest-memory reads**
   (`jump_over_fde_zero_guest_reads`,
   `jump_over_fde_double_nested_reentrant_unwind_sound`), verified identically
   on x86-64 silicon and on bundle-free AArch64 LFI (`[x27, wIdx, uxtw]`, `w26`
   watermark, `PROT_BTI` `SIGILL`, `FEAT_FPAC` `autia` `SIGILL`) under
   `qemu-aarch64 11.1.2 -cpu max`.
3. **Resolving the `Tree Borrows` `StrongProtector` × 4 KiB page-bleed tension
   for zero-copy Rust <-> SFI slices
   (`support/reproduce_zerocopy_tb_and_page_bleed.py`,
   `support/UnwindJumpOverAndTreeBorrows.lean`).** Hardware MMU permissions
   have `4,096`-byte granularity whereas Rust slice borrows have byte
   granularity: co-locating a writable `[0..64)` buffer and an immutable
   `[64..128)` slice on one `PROT_WRITE` SFI page lets an SFI-legal store
   silently overwrite the neighbor (`0xbad0c0decafebabe`), while Miri `0.1.0`
   (`-Zmiri-tree-borrows`) flags immediate Undefined Behavior whenever any
   protected `&[u8]` (`Frozen`), sibling `&mut [u8]` (`ReservedFrz`), reentrant
   callback `&[u8]`, or even an internal `Box<[u8]>` field (`Unique` recursive
   retag disabling the exposed wildcard ancestor!) coexists with a writable SFI
   arena. Sound zero-copy sharing splits cleanly into two patterns: (a) raw
   `*mut u8`-backed `SfiArena` + provenance-free `SfiSpan` (`u32` offset/length)
   with `&mut self` loan suspension across `sfi_enter` (`rc = 0` in Miri,
   `sfi_arena_loan_preserves_tree_borrows`), and (b) `4,096`-byte page-aligned
   `memfd_create` `PROT_READ` dual mappings or `PROT_NONE`-flanked `SfiBox`
   pages (`SIGSEGV`, `SEGV_ACCERR = 2`,
   `dual_mapped_prot_read_preserves_frozen_and_host_bytes`).
4. **Eliminating custom `lfi-clang` compiler dependencies via an untrusted
   `419`-LOC stock-`gcc 15.2.0 -O2 -S` assembly rewriter verified by Lean
   kernel reflection (`support/sfi_gcc_rewriter.py`,
   `support/bench_stock_gcc_sfi_workload.py`,
   `support/verify_lean_proofs_and_replay.py`).** Compiling a 5-function C
   workload (8-way PIC `switch` jump table, 64-bit polynomial checksum, LZ4/RLE
   back-reference block decompressor, streaming `extern "C-unwind"` Rust
   callback, and boundary tests) with stock `gcc 15.2.0 -O2 -fPIC -ffixed-...
   -S` and rewriting via `sfi_gcc_rewriter.py` + GNU `as 2.47`
   `.bundle_align_mode 5` produces a `2,048`-byte (`1,472` active bytes, `0`
   relocations in untrusted bundles) `.text.sfi` image that passes
   `checkSfiPicMultiFn 2048 stockGccWorkloadImg = true := rfl` in the Lean
   `v4.34.1` kernel (`3,811 ms` fresh replay of `15` constants) and runs at
   **`3,381.28 MiB/s`** vs. **`3,640.63 MiB/s`** native `-O2` (**`+7.67%`
   overhead**, `92.9%` of native throughput) inside a live `4 GiB + 2 * 64 KiB
   `PROT_NONE` Linux `mmap` arena.

> **Prefix-Decoding Errata (`FS:`/`GS:`, `0x67`, `0x66`):** In `support/PicMultiFnSfi.lean`, `scanPrefixes` accepted `0x64` (`FS:`), `0x65` (`GS:`), `0x67` (`addr32`), and `0x66` (`op16`) as flat/ignored legacy prefixes under a `fsBase = gsBase = 0` model. On stock Linux processes where `IA32_FS_BASE` (`%fs` TLS) is non-zero, `64 4f 89 04 2e` (`mov %r8, %fs:(%r14,%r13,1)`) passes unpatched `checkSfiPicMultiFn` yet writes outside the `4 GiB` arena envelope; similarly `0x67` truncates effective addresses to 32 bits and `0x66` causes Intel-vs-disassembler `rel16` branch-length desynchronization. Corpus package `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing` (`PicMultiFnSfiV2.lean`, `sfi_gcc_rewriter_v2.py`) repairs all four prefix classes, adds `--canary-mode=arena_guarded` for `-fstack-protector-strong`, and proves `checkSfiPicMultiFnV2_sound` over all `(fsBase, gsBase : BitVec 64)`.

## Applicability

These findings govern any binary verification or sandboxing pipeline that links
compiled C/assembly `.o`/`.a` objects into a Rust host process while claiming
memory isolation, callee-saved register preservation, `extern "C-unwind"` panic
recovery, reentrant Rust callbacks, or zero-copy slice access:

- **Subjects and pinned versions:**
  - **Theorem prover & kernel:** `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), standalone `prelude` + `Init.*` closure (`-DElab.async=false -Ddebug.skipKernelTC=false -j1`), verified via `(trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)` `base.toKernelEnv.replay`.
  - **Verification framework & neighboring baselines:** `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) and `lfi-project/lfi-verifier` (`8c3c47983572039b138f8fa15c12231f2655bbef`), extending corpus packages `byte-decoded-x86-64-sharded-lifting-dead-flag-collapse-and-binary-sfi-containment` (single-function `code_base = 0` SFI), `dwarf-eh-frame-unwinding-semantics-may-unwind-asm-and-cfi-poisoning` (inline-asm CFI poisoning), and `reentrant-ffi-mixed-mir-isa-call-stacks-tree-borrows-and-oracle-composition` (`Tree Borrows` FFI oracle composition).
  - **Rust, Miri, C, and AArch64 toolchains:** `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1`), `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`), `miri 0.1.0` (`-Zmiri-tree-borrows -Zmiri-permissive-provenance`), Debian `gcc 15.2.0-14` (`libgcc_s` Itanium/DWARF unwinder), GNU `binutils 2.47`, Debian `clang 19.1.7` (`--target=aarch64-linux-gnu -march=armv8.5-a -mbranch-protection=standard`), and `qemu-aarch64 11.1.2 -cpu max`.
  - **Host OS & hardware:** `Linux 7.1.6-1rodete1-amd64` (`vm.mmap_min_addr = 65536`) on Intel Xeon Ice Lake-SP (`Family 6 Model 106 Stepping 6`, `4,096`-byte base pages).
- **Operational preconditions:**
  - The host loader maps `.text.sfi` at `16`-byte/page-aligned `codeBase` (`codeBase + totalBytes < 2^64`, `totalBytes` a power-of-two multiple of `32` with `96 <= totalBytes <= 2^31`) with `PROT_READ | PROT_EXEC` (never `PROT_WRITE`) after `checkSfiPicMultiFn` succeeds and zero untrusted relocations remain.
  - The host allocates a `4 GiB + 2 * 64 KiB` virtual reservation via `mmap(..., PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE)` and enables `PROT_READ | PROT_WRITE` (or per-page `PROT_READ`) only within `[arenaBase, arenaBase + 4 GiB)`, leaving symmetric `[arenaBase - 64 KiB, arenaBase)` and `[arenaBase + 4 GiB, arenaBase + 4 GiB + 64 KiB)` unmapped/`PROT_NONE`.
  - Reentrant host callbacks are mediated exclusively through loader-synthesized Portal Bundle `1` (`codeBase + 0x20 -> sfi_hostcall_trampoline`) paired with `sfi_enter_trampoline` and an RAII `WatermarkGuard` on `SfiContext.guest_sp`.

## Findings

### Finding 1: Surrogate `ret` (`0xC3`) and zero-based `and eax, mask32; jmp rax` break on real x86-64 stacks and Linux `mmap_min_addr`, whereas a 4-register PIC + Portal architecture (`%r15`, `%r14`, `%r13`, `%r11`) closes multi-function SFI with zero TCB loop invariants

`Basis:` `normative` (Intel SDM Vol. 2B `RET` `0xC3` near-return semantics; System V AMD64 psABI 1.0 §3.2.1 register preservation), `source` (`lfi-project/lfi-verifier` `8c3c47983572039b138f8fa15c12231f2655bbef`), `execution` (`Linux 7.1.6` `vm.mmap_min_addr = 65536` in `support/unwind_rop_and_reentrant_results.json`), and `derived` (kernel-checked proofs in `support/PicMultiFnSfi.lean`).

When a machine model represents `rip : Nat` as a zero-based offset and gives
`0xC3` (`ret`) the surrogate transition `{ s with halted := true }`, two fatal
divergences from real x86-64 execution arise as soon as multi-function C code
uses a writable stack or indirect branches:

1. **Raw `0xC3` (`ret`) control-flow escape (`raw_ret_0xc3_rop_escape`):** On
   x86-64 hardware, `0xC3` executes `rip := Mem64[rsp]; rsp := rsp + 8`. In
   `PicMultiFnSfi.lean` (`RealX64State` with full 64-bit `rip : BitVec 64`),
   the 3-instruction bundle `[0x89, 0xC8, 0x49, 0x89, 0x14, 0x06, 0xC3]`
   (`mov eax, ecx; mov [r14 + rax*1], rdx; ret`) is accepted by any bundle
   checker that treats `.ret` as a benign halt (`legacyAdmitsRawRet`), yet
   when `%rsp` points into the writable guest stack (`arenaBase + 0x1000`), the
   SFI-confined store overwrites `[%rsp]` with `0x00007FFFDEAD0000` and `ret`
   pops `sf.rip = 0x00007FFFDEAD0000` outside `[codeBase, codeBase + 32)` with
   `sf.fault = false`. Conversely, if `%rsp` stays on the host stack and an
   intra-sandbox callee pushes or returns via `0xC3`, untrusted C mutates host
   `%rsp` or pops unaligned return slots.
2. **Linux `mmap_min_addr` + PIE ASLR null-page fault
   (`legacy_abs32_indirect_jmp_null_page_fault`):** On standard Linux kernels
   (`vm.mmap_min_addr = 65536 = 0x10000`), mapping `.text.sfi` at virtual
   address `0` is forbidden (`EPERM`/`ENOMEM`), and PIE ASLR places code near
   `0x0000555555554000`. Executing the unrelocated macro `25 e0 00 00 00; ff e0`
   (`and eax, 0xE0; jmp rax`) strips bits `63..32` of `%rax` and jumps to
   `0x0000000000000000 < 65536`, faulting immediately (`s3.fault = true`).

**Architectural collapse (`checkSfiPicMultiFn` in `support/PicMultiFnSfi.lean`):**
Both fractures disappear simultaneously without adding call-stack shadow memory
or complex bundle state machines by partitioning registers and reserving two
loader-owned 32-byte portal bundles at the start of `.text.sfi`:

| Surface | Architectural Role | Enforced Invariant in `checkSfiPicMultiFn` |
| :--- | :--- | :--- |
| `%rsp, %rbp, %rbx, %r12` | Host stack pointer & host CSRs / `&mut SfiContext` | Strictly read-only (`isPicHostProtectedReg = true`); `0xC3`, `push`, `pop`, `leave` rejected in all bundles `>= 0x40` (`checkSfiPicMultiFn_rejects_untrusted_ret`). |
| `%r15` | Read-only 64-bit PIC `codeBase` | Never written; added in the 3-instruction PIC indirect branch/return macro. |
| `%r14` | Read-only 64-bit `arenaBase` | Never written; base of `[arenaBase, arenaBase + 4 GiB)` flanked by `+-64 KiB` `PROT_NONE` guards (`SymmetricEnvBound = 65536 + 2^32 + 65536`). |
| `%r13` | 32-bit zero-extended `guest_sp` | Admitted as destination **only** in `isPicZext32DstReg` (`movRR32`, `movImm32`, `aluRR32`, `aluImm32`, `load32Zext`), preserving `(s.regs .r13).toNat < 2^32` at **every** single-instruction step! |
| `%r11` | Dedicated SFI address & PIC-target scratch | Reserved from C register allocation (`-ffixed-r11`), freeing all 6 SysV argument registers (`rdi..r9`) and return registers (`rax, rdx`). |
| Bundle `0` (`codeBase + 0x00`) | Loader-owned `portalReturn` (`0xC3` + NOPs) | Pops untouched host `[%rsp]` (`.Lsfi_after_guest`) into `rip` and transitions `exitKind := .portalReturn`. |
| Bundle `1` (`codeBase + 0x20`) | Loader-owned `portalHostcall` (`0xE9 rel32` + NOPs) | Jumps to host `sfi_hostcall_trampoline` (`exitKind := .portalHostcall`) with unmodified host `%rsp`. |

Because `(s.regs .r13).toNat < 2^32` is an inductive single-step invariant,
every guest-stack spill, reload, and call-frame push/pop (`movq %reg,
disp(%r14,%r13,1)` with `dispSymOk disp`: `disp in [-65536, +65528]`) is
verified as a **standalone 1-instruction operation** without a preceding
`mov r13d, r13d` prefix, intra-sandbox `call target` lowers to storing the
32-bit bundle-aligned return offset (`movl $.Lsfi_ret - __sfi_text_start,
%r11d; movq %r11, (%r14,%r13,1)`) + `jmp target` + `.p2align 5`, and
intra-sandbox `ret` lowers to `movl (%r14,%r13,1), %r11d; addl $8, %r13d` +
the single 3-instruction bundle-locked PIC jump macro (`andl $mask32, %r11d;
leaq (%r15,%r11,1), %r11; jmp *%r11`). When the top-level sandboxed C function
executes its masked `ret`, `sfi_enter_trampoline` pre-initializes `[r14 +
guest_sp] = 0`, so the masked `ret` lands deterministically on `codeBase + 0`
(Portal Bundle `0`)—and even if buggy or adversarial C overwrites its own
top-level return slot with an arbitrary 64-bit host pointer, `andl $mask32,
%r11d` + `leaq (%r15,%r11,1), %r11` confines `rip` to a 32-byte bundle boundary
inside `[codeBase, codeBase + totalBytes)` (`checkSfiPicMultiFn_sound` in
`support/PicMultiFnSfi.lean`, lines 2759–2808).

### Finding 2: Standard `.eh_frame` unwinding and stateless entry stubs fail across reentrant `extern "C-unwind"` callbacks, whereas a Host-Anchored Jump-Over FDE Trampoline leaps arbitrary SFI call depth in 1 FDE step with zero guest-stack reads

`Basis:` `normative` (DWARF v4/v5 §6.4 Call Frame Information; Itanium C++ EH ABI Level I `_Unwind_RaiseException` Phase 1/Phase 2), `execution` (live `rustc 1.99.1` & `rustc 1.102.0-nightly` + `gcc 15.2.0` on x86-64 Linux and `clang 19.1.7` + `qemu-aarch64 11.1.2 -cpu max` in `support/unwind_rop_and_reentrant_results.json`), and `derived` (`support/UnwindJumpOverAndTreeBorrows.lean`, Part A).

When a sandboxed C function invokes a reentrant `extern "C-unwind"` Rust
callback (`Host_0 -> SFI_1 -> Host_cb_2`) that either panics into an outer
`std::panic::catch_unwind` or re-enters the sandbox (`Host_cb_2 -> SFI_3`),
three distinct cross-layer failure modes occur if unwinding and `guest_sp`
state are not anchored on the host stack—all reproduced identically on
`rustc 1.99.1` and `rustc 1.102.0-nightly`:

| Discriminator Case | Mechanism | Live `rustc 1.99.1` & `1.102.0-nightly` Outcome (`support/unwind_rop_and_reentrant_results.json`) |
| :--- | :--- | :--- |
| `unsound_normal` | Split-stack SFI stub whose `.eh_frame` uses `DW_CFA_def_cfa_expression` / `DW_CFA_expression` into the guest stack, under normal non-panicking return | `rc = 0`, `ret = 0x64`, `r12 = 0x1122334455667788` (normal `ret` hides the `.eh_frame` defect completely). |
| `guest_fde_cfa_redirect` | Guest SFI store modifies the saved frame chain inside `[r14, r14 + 4 GiB)` before calling panicking `extern "C-unwind"` callback | `rc = 42`, `OUTCOME=UNWIND_REDIRECTED_OUTSIDE_SANDBOX` (`libgcc_s` reads modified guest-stack frame pointer during Phase 2, pivoting post-`catch_unwind` caller return to `outside_sandbox_sentinel`; `canary_guest_fde_unwind_rop_escape`). |
| `guest_fde_csr_corrupt` | Guest SFI store modifies only `[guest_sp + 8]` (saved `r12` slot) while keeping `CFA` and return `RIP` intact | `rc = 0`, `caught = true`, `r12 = 0x5555666677778888` (`corrupted = true`: `catch_unwind` succeeds normally while silently corrupting the safe Rust caller's callee-saved `r12`; `canary_guest_fde_csr_corrupt`). |
| `missing_fde_sfi_obj_abort` | SFI `.o` compiled with `-fno-unwind-tables -fno-asynchronous-unwind-tables` (`checkSfiPicMultiFn` hygiene) calls panicking callback directly | `rc = -6` (`SIGABRT`), `fatal runtime error: failed to initiate panic, error 5, aborting` (`_URC_END_OF_STACK` in Phase 1 skips all outer Rust `Drop` destructors). |
| `stateless_reentrant_clobber` | `Host_0 -> SFI_1 -> Host_cb_2 -> SFI_3` where entry stub resets `r13 := initial_top` (`0x80000`) | `rc = 0`, `got = 0x7777888811114286 != 0x3064` (`SFI_3` overwrites `SFI_1`'s paused guest stack frame; `canary_stateless_reentrant_clobbers_outer_guest_frame`). |
| `fixed_jump_over_fde_suite` | Host-Anchored Jump-Over FDE Trampoline (`sfi_enter_trampoline` + `sfi_hostcall_trampoline`) + `WatermarkGuard` across `Host_0 -> SFI_1 -> Host_cb_2 -> SFI_3 -> panic!()` | `rc = 0`, `reentrant = 0x3064`, `caught = true`, `r12 = 0x1122334455667788`, `outer_drops = 1`, `inner_drops = 2`, `wm_panic = 0x80000`, `post_panic = 0x6064`. |

**Why the Host-Anchored Jump-Over FDE works in 1 FDE hop with 16-byte ABI alignment:**
1. `sfi_enter_trampoline` saves `%rbp, %rbx, %r12, %r13, %r14, %r15` on the
   **host** stack (`subq $8, %rsp` -> `CFA = rsp + 64`), writes `0` to `[r14 +
   guest_sp]` (top-level return sentinel), and enters `r15 + entry_off` via
   `call *%rax`. That `call` pushes `.Lsfi_after_guest` onto the **host** stack
   (`CFA = rsp + 72`, with `rsp % 16 == 8`—the exact System V AMD64 function-entry
   congruence!).
2. Arbitrary intra-sandbox C calls (`D` nested guest frames) modify **only**
   `%r13` and `[r14 + r13]`; host `%rsp` remains bitwise identical to the moment
   after `call *%rax` (`rsp % 16 == 8`, `[rsp] == .Lsfi_after_guest`).
3. When any nested C function jumps to Portal Bundle `1` (`r15 + 0x20`), Portal
   `1` executes a direct `jmp sfi_hostcall_trampoline` (no `call`, so host
   `%rsp` is still untouched with `[rsp] == .Lsfi_after_guest` and `rsp % 16 ==
   8`!). `sfi_hostcall_trampoline` opens `.cfi_startproc` (initial default
   `CFA = rsp + 8`, `RIP = [CFA - 8] = .Lsfi_after_guest`!), executes a single
   `pushq %r13` (`.cfi_adjust_cfa_offset 8`, advancing `CFA = rsp + 16` AND
   aligning `rsp % 16 == 0` so XMM `movaps` inside `_Unwind_RaiseException`
   never `#GP`-faults!), updates `ctx.guest_sp = (r13d - 4096) & ~15` (`20(%r12)`
   in `#[repr(C)] SfiContext`), and calls `ctx.hostcall_fn`.
4. If `hostcall_fn` panics—even from inside a double-nested `SFI_3` activation
   with arbitrarily corrupted `guestMem`—`libgcc_s` unwinds
   `sfi_hostcall_trampoline` in **one** FDE step to `RIP = .Lsfi_after_guest`
   inside `sfi_enter_trampoline`, then unwinds `sfi_enter_trampoline` in a
   second FDE step back to the Rust `sfi_call` wrapper (`WatermarkGuard::drop`
   restores the outer `ctx.guest_sp` watermark!), reading **zero bytes** from
   `[r14, r14 + 4 GiB)` (`jump_over_fde_zero_guest_reads`,
   `jump_over_fde_double_nested_reentrant_unwind_sound`, and
   `reentrant_watermark_disjointness` in
   `support/UnwindJumpOverAndTreeBorrows.lean`).

**Cross-ISA validation on bundle-free AArch64 LFI (`qemu-aarch64 11.1.2 -cpu max`):**
Because AArch64 instructions have fixed `4`-byte width, LFI eliminates 32-byte
bundles completely (`ldr/str xDst, [x27, wIdx, uxtw]` with `x27 = arenaBase`,
`x28 = codeBase`, `w26 = guest_sp` watermark, and `and w16, w30, #mask; add
x30, x28, x16, uxtw; ret` return sequence), while hardware `FEAT_BTI` +
`FEAT_PAUTH`/`FEAT_FPAC` strengthen forward and host-trampoline edges:
- Nested reentrant callback + guest-stack-poisoned unwind via the AArch64
  Jump-Over FDE (`stp x29, x30, [sp, #-64]!` + `paciasp` / `autiasp` on the
  host `sp`): `rc = 0`, `r1 = 0x3064`, `caught = 0x4d`, caller `x19 =
  0x1122334455667788` intact, watermark `wm = 0x80000` restored, post-unwind
  `r2 = 0x6064`.
- Indirect `br x16` to a valid 4-byte instruction lacking `bti c` inside a
  `mprotect(..., PROT_READ | PROT_EXEC | PROT_BTI = 0x15)` page: deterministic
  `SIGILL` (`rc = -4`).
- Corrupting bit `56` of a `pacia`-signed link register before `autia` under
  `-cpu max` (`FEAT_FPAC`): synchronous `SIGILL` (`rc = -4`) at `autia` prior
  to `ret`.

### Finding 3: Sub-page `PROT_WRITE` sharing and live Rust references into writable SFI arenas violate both hardware page granularity and `Tree Borrows` `StrongProtector`—including recursive `Box<[u8]>` field retags

`Basis:` `normative` (PLDI 2025 `Tree Borrows` `10.1145/3735592`; `proofs-rs/lean-miri` `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), `execution` (Linux `7.1.6` `memfd_create`/`mmap`/`mprotect` + `miri 0.1.0 -Zmiri-tree-borrows -Zmiri-permissive-provenance` in `support/zerocopy_tb_and_page_bleed_results.json`), and `derived` (`support/UnwindJumpOverAndTreeBorrows.lean`, Part B).

Attempting "zero-copy" sharing between safe Rust and a `4 GiB` SFI arena
without coordinating both OS `4,096`-byte page protections and Rust's
abstract-machine `Tree Borrows` permissions fails along two orthogonal axes:

1. **Physical `4,096`-byte page write-bleed (`canary_4kib_subpage_bleed`):**
   `checkSfiPicMultiFn` guarantees only that untrusted stores stay within
   `[r14, r14 + 4 GiB)` (`+-64 KiB` guard). Co-locating a mutable 64-byte slice
   `[0..64)` and an immutable 64-byte slice `[64..128)` on the same `PROT_READ
   | PROT_WRITE` page (`64 / 4096 == 0 / 4096`) allows an SFI-verified store at
   `r14 + 64` to overwrite the immutable buffer with `0xbad0c0decafebabe`
   (`bleed_corrupted = true`, zero hardware traps).
2. **`Tree Borrows` `StrongProtector` and `Box<[u8]>` recursive-retag UB under
   Miri `0.1.0` (`-Zmiri-tree-borrows`):** Even when C accesses are 100%
   in-bounds of `[0, 4 GiB)`, exposing `r14` (`ptr.expose_provenance()`) and
   performing wildcard stores inside C interacts with every live Rust borrow
   derived from the same allocation:

| Miri `-Zmiri-tree-borrows` Case | Rust <-> SFI Aliasing Pattern | Live Miri `0.1.0` Verdict (`support/zerocopy_tb_and_page_bleed_results.json`) | Mechanized Lean Counterpart (`support/UnwindJumpOverAndTreeBorrows.lean`) |
| :--- | :--- | :--- | :--- |
| `ub_frozen` | Host holds protected `shared: &[u8]` (`Frozen`, `StrongProtector`) across writable SFI call | **UB** (`rc = 1`): `write access through <wildcard> at alloc866[0x0] is forbidden` | `canary_frozen_protector_ub` |
| `ub_sibling_mut` | Arena split via `split_at_mut(4096)` into `a` (passed by offset) and protected `b: &mut [u8]` (`ReservedFrz`); C writes `[r14 + 4096]` | **UB** (`rc = 1`): `write access through <wildcard> at alloc870[0x1000] is forbidden` | `canary_sibling_mut_protector_ub` |
| `ub_reentrant_cb` | Reentrant `Host_cb_2` creates `chunk: &[u8]` into writable arena, calls nested `SFI_3` (which writes `chunk[0]`), then reads `chunk[0]` | **UB** (`rc = 1`): `read access through <1894> at alloc874[0x0] is forbidden` (`Frozen -> Disabled` on foreign write!) | `canary_reentrant_cb_unprotected_frozen_then_read_ub` |
| `ub_box_backing` | `BadBoxSfiArena { buf: Box<[u8]>, r14_addr: usize }` exposes `r14_addr`, calls `self.with_slice_mut(...)`, and then calls `sfi_enter(&mut self)` (even after all slice borrows end!) | **UB** (`rc = 1`): `write access through <wildcard> at alloc878[0x0] is forbidden` (`Box<[u8]>` carries `Unique` noalias; retagging `&mut self` + writing through `self.buf` performs a foreign write on the exposed ancestor tag, transitioning it `Unique -> Disabled`!) | `canary_box_field_retag_disables_wildcard` |
| `ok_sfi_arena` | `SfiArena { raw_ptr: *mut u8, r14_addr: usize, ... }` + provenance-free `SfiSpan { off: u32, len: u32 }` + scoped `with_slice` / `with_slice_mut` suspended by `sfi_enter(&mut self)` across nested reentrancy | **PASS** (`rc = 0`): `MIRI_OK final_a=43 final_b=200` (`0` errors) | `sfi_arena_loan_preserves_tree_borrows` |

**Sound Zero-Copy Pattern Matrix:**
- **Mutable zero-copy (`SfiArena` + `SfiSpan`):** Backing `SfiArena` with a raw
  `*mut u8` (`alloc_zeroed` / `mmap`, **never** `Box<[u8]>` or `Vec<u8>`) keeps
  the single exposed root tag in `Unique` state; requiring `&mut self` on
  `sfi_enter` makes `rustc`'s borrow checker statically guarantee zero live
  child `&[u8]` or `&mut [u8]` tags during every SFI activation (including
  reentrant `SFI_3` entries inside callbacks, where callbacks receive `&mut
  SfiArena` + `SfiSpan` rather than holding `&[u8]` across nested calls).
- **Immutable zero-copy (`memfd_create` `PROT_READ` dual mapping):** Mapping a
  `4,096`-byte page-aligned `memfd_create` backing `PROT_READ | PROT_WRITE` on
  the host and `PROT_READ` at `[r14 + 0x10000, r14 + 0x11000)` flanked by
  `PROT_NONE` pages delivers exact zero-copy reads (`zc_read_matches = true`)
  while hardware-trapping any untrusted SFI store (`SIGSEGV = 11`,
  `SEGV_ACCERR = 2`) *before* memory is mutated (`host_unmutated = true`) or
  any abstract `Tree Borrows` write occurs
  (`dual_mapped_prot_read_preserves_frozen_and_host_bytes`).
- **Isolated mutable buffers (`SfiBox`):** Whole-page (`4,096`-byte multiple)
  `PROT_READ | PROT_WRITE` mappings flanked by `PROT_NONE` guard pages trap
  cross-buffer OOB stores (`SIGSEGV = 11`, `SEGV_ACCERR = 2`) at page
  boundaries; sub-`4,096`-byte tail slack `[len .. 4096)` must be
  zero-initialized so untrusted reads observe no host secrets.

### Finding 4: Stock `gcc 15.2.0 -O2 -S` + a `419`-LOC untrusted Python rewriter achieves `92.9%` of native `-O2` throughput (`+7.67%` overhead) and passes Lean `v4.34.1` kernel verification with zero `lfi-clang` toolchain TCB

`Basis:` `execution` (live `gcc 15.2.0 -O2` + GNU `as 2.47` + `rustc 1.99.1` benchmark in `support/stock_gcc_sfi_benchmark_results.json`; Lean `v4.34.1` kernel certificate & fresh replay in `support/lean_verification_and_replay_results.json`) and `derived` (`StockGccWorkloadCert.stockGccWorkload_verified` & `stockGccWorkload_pic_sfi_sound` generated by `support/verify_lean_proofs_and_replay.py`).

Because `checkSfiPicMultiFn` verifies raw `.text.sfi` object bytes directly in
the Lean kernel, the C compiler and SFI assembly rewriter sit **100% outside
the Trusted Computing Base**. Invoking stock Debian `gcc 15.2.0` with:

```text
gcc -O2 -fPIC -fvisibility=hidden -fno-tree-vectorize \
    -ffixed-rbp -ffixed-rbx -ffixed-r11 -ffixed-r12 -ffixed-r13 -ffixed-r14 -ffixed-r15 \
    -mno-red-zone -fno-stack-protector -fno-unwind-tables -fno-asynchronous-unwind-tables \
    -fcf-protection=none -S
```

and transforming the emitted AT&T `.s` file with `support/sfi_gcc_rewriter.py`
(`419` lines of Python) + GNU `as 2.47` (`.bundle_align_mode 5`) required
solving four real `-O2` code-generation subtleties:

1. **`RFLAGS`-preserving complex-address lowering:** `gcc 15.2.0 -O2` schedules
   memory loads *between* flag-setting instructions (`shrq $32, %rax`) and
   conditional branches (`jne`). Lowering general SIB/scaled memory operands via
   `leaq disp(base,idx,scale), %r11; .bundle_lock; movl %r11d, %r11d; movq
   (%r14,%r11,1), %dst; .bundle_unlock` uses only `lea` and `mov`—preserving
   all six status flags (`CF, PF, AF, ZF, SF, OF`) untouched!
2. **AT&T operand-order preservation on memory `cmp`/`test`:** Rewriting
   `cmpq %rdi, (%rsp)` loads `(%r14,%r13,1)` into `%r11` and emits `cmpq %rdi,
   %r11` (`%r11 - %rdi`), whereas `cmpq 8(%rsp), %rdx` loads `8(%r14,%r13,1)`
   into `%r11` and emits `cmpq %r11, %rdx` (`%rdx - %r11`), preserving exact
   unsigned/signed condition codes (`jb`, `jae`, `ja`, `jbe`).
3. **Relocation-free PIC `.rodata` jump tables:** Stock `gcc -O2 -fPIC` compiles
   8-way `switch` statements into `.section .rodata` `.long .Ltarget - .Ltable`
   relative tables loaded via `leaq .Ltable(%rip), %rdx; movslq (%rdx,%rdi,4),
   %rax; addq %rdx, %rax; jmp *%rax`. Rewriting `leaq .Ltable(%rip), %rdx` to
   an arena `.sfi_rodata` offset (`movl $0x10000 + off, %edx`) and rewriting
   each `.long` entry to `(.Ltarget - __sfi_text_start) - (0x10000 + (.Ltable -
   __sfi_rodata_start))` makes GCC's `movslq` + `addq` cancel the `.sfi_rodata`
   offset in integer arithmetic and yield the exact `.text.sfi` target offset
   for `movl %eax, %r11d; andl $0x7e0, %r11d; leaq (%r15,%r11,1), %r11; jmp
   *%r11` with **zero relocations** in `.text.sfi` (`>= 0x40`) or `.sfi_rodata`!
4. **Final-bundle terminal jump alignment (caught by Lean `rfl`):** Placing
   `jmp __sfi_portal_exit` at `off = 0..5` of the final bundle (`base = 2016`)
   followed by `.p2align 5` (`27` NOP bytes ending at `off + len = 32`) was
   rejected by `checkSfiPicSubtree 2048 1536 2048` in Lean `v4.34.1`, because a
   macro check that does not prune dead bytes after unconditional `jmpRel`
   requires the instruction *ending at byte 32* of the final bundle not to fall
   off `totalBytes`. Placing the 5-byte `0xE9` `jmp __sfi_portal_exit` at
   `off = 27..32` closed `StockGccWorkloadCert.stockGccWorkload_verified` by
   `rfl` with zero edits to `PicMultiFnSfi.lean`.

**Live Workload & Kernel Verification Summary (`64 KiB` RLE + LZ4 back-reference decompression + 64-bit checksum + 8-way `switch` + streaming `extern "C-unwind"` callback, `2,000` iterations = `128 MiB`):**

| Metric | Native `gcc 15.2.0 -O2` | Stock-GCC Rewritten PIC SFI (`sfi_gcc_rewriter.py`) | Ratio / Delta |
| :--- | :--- | :--- | :--- |
| `.text` / `.text.sfi` active bytes | `605 B` (`164` insns) | `1,472 B` (`46` bundles, `296` insns; padded to `2,048 B` = `64` bundles) | `2.433x` active code size |
| Untrusted bundle ELF relocations (`>= 0x40`) | `1` (`sfi_stream_cb`) | **`0`** (`1` loader relocation in Portal `1` at `0x21`) | `100%` relocation-free untrusted bundles |
| Per-`64 KiB` block latency (`2,000` iters) | `17,167.36 ns` | `18,484.15 ns` | **`+7.67%`** latency overhead |
| Sustained decompression + checksum throughput | `3,640.63 MiB/s` | **`3,381.28 MiB/s`** | **`92.9%`** of native `-O2` speed |
| `64`-bit OOB offset `0x1_0002_0080`, corrupted return slot, & mid-stream `panic!()` | Unprotected | Confined to `r14 + 0x20080`, confined to Portal `0`, & caught cleanly (`guest_sp = 0xF0000` restored) | `3 / 3` live containment checks passed |
| Lean `v4.34.1` kernel certificate (`StockGccWorkloadCert`) | N/A | `checkSfiPicMultiFn 2048 stockGccWorkloadImg = true := rfl` (`15` replayed constants in `3,811 ms`) | `0` `sorry`, axioms `{propext, Quot.sound, Classical.choice}` |

*Errata note on legacy prefixes and `-fstack-protector-strong`:* `PicMultiFnSfi.decodeX64` above models flat zero segment bases and unprefixed 64-bit addressing, so `checkSfiPicMultiFn` does not reject `0x64` (`FS:`), `0x65` (`GS:`), `0x67` (`addr32`), or `0x66` (`op16`) branch encodings, and `sfi_gcc_rewriter.py` targeted `-fno-stack-protector` input. For production Ring-3 Linux sandboxing with non-zero `%fs`/`%gs` bases and `-fstack-protector-strong` stack canaries, use `PicMultiFnSfiV2` and `sfi_gcc_rewriter_v2.py` in corpus package `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing`.

## Boundaries

The scope of this report is bounded explicitly across the four negative-space
categories:

- **Known not to apply:**
  - **Surrogate `ret` (`halted := true`) or raw `0xC3` admission in multi-function SFI:** Proven unsound under real `[%rsp]`-popping semantics whenever `%rsp` resides in writable guest memory (`raw_ret_0xc3_rop_escape`), and ABI-incompatible when `%rsp` remains on the protected host stack.
  - **Zero-based `and reg32, mask; jmp reg64` indirect branches on Linux:** Proven to jump into `[0, 65536)` and fault whenever `codeBase >= vm.mmap_min_addr` (`legacy_abs32_indirect_jmp_null_page_fault`).
  - **Guest-stack DWARF `.eh_frame` expressions (`DW_CFA_def_cfa_expression` / `DW_CFA_expression`) or `-fno-unwind-tables` frames without a host-anchored Jump-Over FDE:** Proven and demonstrated live to cause Phase-2 control/CSR corruption (`rc = 42`, `r12` clobber) or Phase-1 `_URC_END_OF_STACK` process abort (`error 5`, `SIGABRT`).
  - **Co-locating mutable and immutable zero-copy slices on one `4,096`-byte `PROT_WRITE` page, holding Rust `&[u8]`/`&mut [u8]` across writable SFI calls, or backing `SfiArena` with `Box<[u8]>`:** Proven and demonstrated under Linux `7.1.6` + Miri `0.1.0 -Zmiri-tree-borrows` to cause sub-page write bleed or `Tree Borrows` Undefined Behavior.
  - **Flat-segment (`fsBase = gsBase = 0`) decoding of `0x64`/`0x65` (`FS:`/`GS:`), `0x67` (`addr32`), or `0x66` (`op16`) inside untrusted SFI bundles:** Unpatched `PicMultiFnSfi.lean` silently ignored `0x64`/`0x65`/`0x67`, allowing `64 4f 89 04 2e` (`mov %r8, %fs:(%r14,%r13,1)`) to escape the `4 GiB` arena on stock glibc Linux threads; repaired in `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing` (`PicMultiFnSfiV2.lean`).
- **Unsupported (handled fail-closed by `checkSfiPicMultiFn` or `sfi_gcc_rewriter.py`):**
  - **SIMD/AVX2/FPU/string/atomic memory opcodes and read-modify-write memory ALU ops** (`vmovdqu`, `rep movsb`, `lock cmpxchg`, `addq %rax, (%rdi)`) in `PicMultiFnSfi.decodeX64` and `sfi_gcc_rewriter.py`: compiling with `-fno-tree-vectorize` avoids vector emission for scalar C workloads, and any unhandled instruction fails closed at rewrite time or is rejected (`DecodeFault.unsupported` -> `false`) by `checkSfiPicMultiFn`.
  - **Arbitrary indirect function-pointer calls across multiple external host functions without a dispatch index:** Portal `1` funnels untrusted hostcalls through a single host-controlled `ctx.hostcall_fn` entry point (which can multiplex tagged operations safely on the Rust side).
  - **Sub-page (`< 4,096` byte) hardware read-only zero-copy windows on x86-64 without MPK/PKEYs:** Standard x86-64 PTEs protect `4,096`-byte pages; sub-page immutable data must either be copied into an `SfiSpan` or placed on dedicated `PROT_READ` `memfd_create` pages.
- **Unknown (open empirical or specification questions):**
  - **Multi-threaded shared-arena SFI × C11/Rust atomic memory model (`Tree Borrows` + weak memory):** Our `SfiArena` loan discipline (`&mut self`) enforces single-thread exclusive access per `4 GiB` arena; concurrent multi-sandbox sharing of a single `4 GiB` arena with `LOCK`-prefixed or AArch64 LSE atomics requires concurrent `Tree Borrows` + TSO/Armv8 axiomatic memory-model composition.
  - **Hardware speculative execution (`Spectre-PHT` / `Spectre-BTB` / `RSB` underflow) across SFI portals:** Architectural `checkSfiPicMultiFn_sound` confines sequential execution, not transient microarchitectural speculation prior to branch resolution or `lfence` serialization.
- **Not examined:**
  - **Full AArch64 ISA mechanization in Lean 4:** Bundle-free AArch64 LFI + Jump-Over FDE + `PROT_BTI` + `FEAT_FPAC` was built and executed live under `qemu-aarch64 11.1.2 -cpu max` (`support/reproduce_unwind_rop_and_reentrant_sfi.py`), while the byte-level ISA decoder and machine soundness proof in `support/PicMultiFnSfi.lean` target x86-64.
  - **Windows x64 SEH (`.pdata`/`.xdata`) and 32-bit Arm EHABI (`.ARM.exidx`) unwinders:** Only DWARF `.eh_frame` / Itanium Level I & II (`libgcc_s`) on ELF targets was tested.
  - **Signal delivery (`sigaltstack` asynchronous signals arriving mid-sandbox):** Synchronous `SA_SIGINFO` page-fault traps were tested in `reproduce_zerocopy_tb_and_page_bleed.py`, but asynchronous POSIX signal handlers interrupting guest SFI code without `SA_ONSTACK` (which would push a signal frame onto host `%rsp`, safely outside the guest arena!) were not stress-tested.

## Evidence

All claims are backed by `11` self-contained, reproducible artifacts in
`support/`:

| File | Bytes | SHA-256 | Role & Key Verified Artifact |
| :--- | ---: | :--- | :--- |
| `support/PicMultiFnSfi.lean` | `140,312` | `d8dd79a6b4b8efda82206367c3412959a71c799b888729531c923b67f32fb52d` | Standalone `prelude` + `Init.*` Lean `v4.34.1` mechanization (`2,844` lines, `0` `sorry`, `11.08 s` compile, `567 ms` fresh kernel replay): variable-length x86-64 decoder + `decodeX64_prefix_invariant`, real `[%rsp]`-popping `RealX64State`, `raw_ret_0xc3_rop_escape`, `legacy_abs32_indirect_jmp_null_page_fault`, `checkSfiPicMultiFn`, and `checkSfiPicMultiFn_sound`. |
| `support/UnwindJumpOverAndTreeBorrows.lean` | `23,454` | `accc7a8344d4f4dacb2e3ca27be0c723953d49d7e9515312cf621669b5068830` | Standalone `prelude` + `Init.*` Lean `v4.34.1` mechanization (`456` lines, `0` `sorry`, `1.21 s` compile, `61 ms` fresh kernel replay): `canary_guest_fde_unwind_rop_escape`, `canary_guest_fde_csr_corrupt`, `canary_stateless_reentrant_clobbers_outer_guest_frame`, `reentrant_watermark_disjointness`, `jump_over_fde_zero_guest_reads`, `jump_over_fde_double_nested_reentrant_unwind_sound`, 4 `Tree Borrows`/4 KiB UB canaries, `sfi_arena_loan_preserves_tree_borrows`, and `dual_mapped_prot_read_preserves_frozen_and_host_bytes`. |
| `support/sfi_gcc_rewriter.py` | `16,005` | `71423a1578c0efe64ae09fec3be55b1c50e9f0110f4c395f866f2d26d27f26df` | Untrusted `419`-LOC Python AT&T assembly SFI rewriter converting stock `gcc 15.2.0 -O2 -fPIC -ffixed-... -S` output into 32-byte-bundled PIC multi-function SFI assembly with Portal Bundles `0` & `1` and relocation-free `.sfi_rodata` jump tables. |
| `support/bench_stock_gcc_sfi_workload.py` | `26,130` | `4875bcea54a63af89487992bd0f83fc4bcfa720230e9931ba8227381d2895d9b` | Compiles the 5-function C decompression + checksum + 8-way switch + streaming callback workload natively and via `sfi_gcc_rewriter.py`, checks ELF relocations, runs the `128 MiB` (`2,000 * 64 KiB`) benchmark + 3 live containment tests inside a `4 GiB + 2 * 64 KiB PROT_NONE` `mmap` arena, and exports `sfi_text_hex_2048b`. |
| `support/stock_gcc_sfi_benchmark_results.json` | `5,071` | `2fa173f927e38a53a464501307d76384b694cf4b1315c4157374f9afaec1bbcc` | Captured metrics (`3,640.63 MiB/s` native vs. `3,381.28 MiB/s` SFI, `+7.67%` overhead, `2.433x` active code size, `0` untrusted relocations) and exact `2,048`-byte `.text.sfi` hex (`SHA-256: 9fadbc9a...`). |
| `support/reproduce_unwind_rop_and_reentrant_sfi.py` | `31,139` | `076e10713a76d85ea3a5797b1ceb921b8facf9c1081488c79860b73528d59258` | End-to-end x86-64 (`rustc 1.99.1` & `rustc 1.102.0-nightly` + `gcc 15.2.0`) and AArch64 (`clang 19.1.7` + `qemu-aarch64 11.1.2 -cpu max`) discriminator suite for `.eh_frame` unwind-redirect, CSR corruption, missing-FDE abort, stateless reentrant stack clobber, Jump-Over FDE recovery, `PROT_BTI`, and `FEAT_FPAC`. |
| `support/unwind_rop_and_reentrant_results.json` | `4,974` | `2057512261b4bcdef68dfc32be447bdf65b5b2d2c412d7391ad7198c8e09786e` | Captured JSON receipts across all 6 x86-64 cases on both Rust toolchains plus all 3 AArch64 LFI cases under QEMU `-cpu max`. |
| `support/reproduce_zerocopy_tb_and_page_bleed.py` | `18,689` | `f2177cfcbbd209eb33b9d7231dad0663bb7a9d6d722ceb99057b3b0d0a62a3f3` | Linux `7.1.6` `memfd_create` / `PROT_READ` / `SfiBox` `SA_SIGINFO` harness and 5-case `cargo +nightly miri` (`-Zmiri-tree-borrows`) suite (`ub_frozen`, `ub_sibling_mut`, `ub_reentrant_cb`, `ub_box_backing`, `ok_sfi_arena`). |
| `support/zerocopy_tb_and_page_bleed_results.json` | `1,464` | `8124d5c9581a8940b58cfb14a905b0a238fd8b138675b32935bf72e2d1099b89` | Captured VM trap (`SIGSEGV = 11`, `SEGV_ACCERR = 2`) and Miri `0.1.0` `Tree Borrows` UB/OK verdicts. |
| `support/verify_lean_proofs_and_replay.py` | `17,008` | `74026f81754c8bd5dacb736b8915f60baacc6cd2eea0140872b247d67398e2b2` | Compiles `PicMultiFnSfi.lean`, `UnwindJumpOverAndTreeBorrows.lean`, and dynamically generated `StockGccWorkloadCert.lean` in `tempfile.TemporaryDirectory()`, then runs fresh-kernel `base.toKernelEnv.replay` (`trustLevel := 0`, `loadExts := false`, `level := .private`) across `14` theorems. |
| `support/lean_verification_and_replay_results.json` | `5,425` | `a9033c9bd0f9926edb1a8fe859ad4f4a955e12c5ba7a9e91e60eec13210216e1` | Captured Lean `v4.34.1` compile times (`11.08 s`, `1.21 s`, `16.26 s`), RSS (`303–566 MiB`), fresh-kernel replay times (`567 ms`, `61 ms`, `3,811 ms`), and exact transitive axiom sets (`<= 3` standard Lean axioms). |

## Revalidation

Every empirical claim and Lean `v4.34.1` theorem revalidates in isolated
temporary directories (`tempfile.TemporaryDirectory()`) without modifying the
report directory beyond refreshing JSON receipts if desired:

1. **Revalidate DWARF `.eh_frame` unwind-redirect, reentrant clobber, Jump-Over
   FDE, and AArch64 LFI (`PROT_BTI` + `FEAT_FPAC`) (~8 s):**
   ```bash
   python3 -B support/reproduce_unwind_rop_and_reentrant_sfi.py
   ```
   Expected terminal line: `ALL_UNWIND_SFI_AND_AARCH64_LFI_CHECKS_PASSED` (`exit 0`).

2. **Revalidate `4 KiB` page-bleed, `memfd_create` `PROT_READ` zero-copy window,
   `SfiBox`, and Miri `0.1.0` `-Zmiri-tree-borrows` (`Box` retag UB vs. raw
   `SfiArena`) (~12 s):**
   ```bash
   python3 -B support/reproduce_zerocopy_tb_and_page_bleed.py
   ```
   Expected terminal line: `ALL_ZEROCOPY_VM_AND_MIRI_TB_CHECKS_PASSED` (`exit 0`).

3. **Revalidate stock `gcc 15.2.0 -O2 -S` SFI rewriter (`sfi_gcc_rewriter.py`)
   and live `4 GiB` arena `128 MiB` decompression benchmark (~3 s):**
   ```bash
   python3 -B support/bench_stock_gcc_sfi_workload.py
   ```
   Expected terminal line: `STOCK_GCC_SFI_REWRITER_AND_BENCHMARK_PASSED` (`exit 0`), confirming `untrusted_bundle_relocations == 0`, exact decompression equivalence, and `~5-9%` SFI runtime overhead.

4. **Revalidate Lean `v4.34.1` proofs (`PicMultiFnSfi.lean`,
   `UnwindJumpOverAndTreeBorrows.lean`), the literal `2,048`-byte GCC `.o`
   certificate (`StockGccWorkloadCert.lean`), and fresh-kernel replay (~30 s):**
   ```bash
   python3 -B support/verify_lean_proofs_and_replay.py
   ```
   Expected terminal line: `ALL_LEAN_PROOFS_GCC_CERT_AND_FRESH_KERNEL_REPLAY_PASSED` (`exit 0`), confirming `0` compiler errors/warnings, `0` `sorryAx`, `0` `_inhabitedExprDummy`, and transitive axioms strictly within `{propext, Classical.choice, Quot.sound}` across all `14` audited theorems.

### Minimal Conditions Invalidating Findings

- A future `rustc` / LLVM / `libgcc_s` x86-64 ABI change altering stack pointer
  congruence at `call` entry (`rsp % 16 == 8`) or `#[repr(C)]` struct layout of
  `SfiContext` would invalidate the fixed displacements in
  `sfi_enter_trampoline` / `sfi_hostcall_trampoline` (caught immediately by
  `reproduce_unwind_rop_and_reentrant_sfi.py`).
- An evolution of `Tree Borrows` (`-Zmiri-tree-borrows`) changing how exposed
  wildcard provenance interacts with `Unique` root allocations or child slice
  protectors would be caught immediately by `reproduce_zerocopy_tb_and_page_bleed.py`.
- A future `gcc` optimization flag emitting vector/SIMD instructions despite
  `-fno-tree-vectorize` or read-modify-write memory ALU instructions would fail
  closed in `sfi_gcc_rewriter.py` or `checkSfiPicMultiFn` (caught immediately by
  `bench_stock_gcc_sfi_workload.py` and `verify_lean_proofs_and_replay.py`).
