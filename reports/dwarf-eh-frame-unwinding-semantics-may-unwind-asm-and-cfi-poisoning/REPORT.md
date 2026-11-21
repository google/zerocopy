# DWARF `.eh_frame` Unwinding Semantics, `may_unwind` Assembly Contracts, Non-`may_unwind` FDE Poisoning, and Dual-Role TCB Verification

## Summary

In non-unwinding leaf machine-code verification, `.eh_frame` Call Frame
Information (CFI) can be treated purely as an untrusted structural hint for
frame sizes and saved-register slots, isolated outside the Trusted Computing
Base (TCB) behind Statement-Origin Separation. That assumption fails
catastrophically in two distinct ways once stack unwinding (`-C panic=unwind`
or C++ `throw`) exists anywhere in the binary:

1. **Runtime execution of `.eh_frame` and `.gcc_except_table` across
   unwind-traversable frames (`options(may_unwind)` `asm!`, `naked_asm!`,
   `global_asm!`, `.S`, and compiled C/C++ `.o`):** During Phase 1 and Phase 2
   of Itanium Level I unwinding, `libgcc_s` / `libunwind` interprets `.eh_frame`
   DWARF CFI bytecode (`DW_CFA_*`) and `.gcc_except_table` Language-Specific
   Data Areas (LSDA) at runtime to compute caller `RSP`, return `RIP`, and
   callee-saved registers (`RBX`, `RBP`, `R12`–`R15` on System V AMD64).
   Omitting `.cfi_adjust_cfa_offset` inside `options(may_unwind)` `asm!` passes
   `1,000 / 1,000` normal-return executions while aborting on unwind (`rc = -6`,
   `_URC_END_OF_STACK`). Worse, keeping an accurate `CFA` while omitting
   `.cfi_rel_offset r12` passes `1,000 / 1,000` normal returns **and** allows
   `std::panic::catch_unwind` to succeed with exit code `0`, while **silently
   corrupting an immutable safe-Rust local variable** in the catching caller
   from `0x2222222222222222` to `0x7777777777777777`.
2. **Silent FDE poisoning of enclosing safe Rust functions by *non-`may_unwind`*
   `asm!` blocks:** Because function-scoped `asm!` shares the enclosing Rust
   function's `.cfi_startproc`..`.cfi_endproc` Frame Description Entry (FDE) in
   LLVM MC, a **zero-instruction** `asm!` block with **no `may_unwind`**
   (`options(nomem, nostack, preserves_flags)`) can corrupt `.eh_frame` and
   LSDA metadata for ordinary safe Rust panics later in the same function:
   - **Linear dead-branch layout poisoning:** Even when `asm!("nop\n
     .cfi_adjust_cfa_offset 16")` sits inside an `if !skip` branch that **never
     executes at runtime**, DWARF CFI evaluates FDE instructions linearly by
     code address from `initial_location` to `return_pc - 1`, shifting `CFA` by
     `+16` at downstream safe Rust calls and aborting `catch_unwind` (`rc = -6`).
   - **Zero-byte `.cfi_escape` safe-local corruption and ASLR leak:** A 0-byte
     `asm!(".cfi_escape 0x8c, 0x01", options(nomem, nostack, preserves_flags))`
     (`DW_CFA_offset r12, -8`) causes `catch_unwind` around a downstream safe
     Rust panic to succeed with exit code `0` while overwriting a pure safe-Rust
     `u64` local in the caller with the victim frame's ASLR-randomized `.text`
     return address (`RIP`, e.g., `0x00005613f164e3d2`).
   - **Default PIE `.cfi_personality` and `.cfi_lsda` hijacking:** A 0-byte
     non-`may_unwind` `asm!` emitting `.cfi_personality 0x9b, ...` (indirect
     PC-relative pointer to a function returning `_URC_CONTINUE_UNWIND = 8`) or
     `.cfi_lsda 0x1b, ...` (PC-relative pointer to a 9-byte LSDA with
     `cs_lpad = 0`) compiles and links cleanly in default PIE mode across
     `rustc` `1.99.1`, `1.100.0`, and `1.102.0-nightly`; `catch_unwind` succeeds
     with exit code `0` while **every safe Rust `Drop` destructor in the
     enclosing function is silently skipped (`drops = 0`)**.
3. **Upstream LLVM `23.1.5` `ShrinkWrap` stack-alignment miscompilation on
   `options(may_unwind)` `asm!`:** When a Rust function has a zero-stack-slot
   `Drop` guard in scope around `asm!(..., options(may_unwind))` (without
   `options(nostack)`), `rustc` lowers the `asm!` to `invoke ... asm sideeffect
   alignstack inteldialect unwind`. At `-O1`/`-O2`/`-O3`, `llvm::ShrinkWrap`
   (`llvm/lib/CodeGen/ShrinkWrap.cpp:302-381, 845-857`) fails to treat
   `INLINEASM` with `Extra_IsAlignStack` as requiring the stack frame, moving
   `pushq %rax` exclusively into the cold landing pad. The `asm!` block is
   entered with **`rsp % 16 == 8`** (`sp_mod_16 = 8`), violating Rust Reference
   rule `r[asm.options.supported-options.nostack]` and crashing `call` inside
   `asm!` during unwinding with `SIGSEGV` (`rc = -11`), whereas `-O0` and
   `-C llvm-args=-enable-shrink-wrap=false` preserve `rsp % 16 == 0`.
4. **Cross-language C/C++ unwinding boundaries (`gcc`/`g++` `15.2.0`):** On
   `x86_64-linux-gnu`, default `gcc -O2` enables `-fasynchronous-unwind-tables`
   (`.eh_frame` present, `.gcc_except_table` absent), allowing Rust panics to
   unwind cleanly across a C callback frame (`c_qsort_style_invoke`) into
   `catch_unwind`, **except** that GCC C `__attribute__((cleanup(...)))`
   handlers are silently skipped on unwind unless `-fexceptions` is passed.
   Conversely, compiling C with `-fno-unwind-tables
   -fno-asynchronous-unwind-tables` omits `.eh_frame` and aborts Phase 1
   (`error 5`, skipping all Rust `Drop` destructors). Under `-C panic=abort`,
   `rustc` lowers calls to `extern "C-unwind"` functions into `invoke ...
   landingpad cleanup` calling `panic_cannot_unwind()`, aborting C++ `throw`
   when an outer C++ handler exists while still exhibiting the Phase-1
   `EHAction::Cleanup` seam when no outer handler exists on the stack.
5. **Empirical `DW_CFA_*` census (`14,800+` FDEs) and Lean `v4.34.1` dual-role
   mechanization:** Across `5,079` FDEs in all `28` `rustc 1.99.1`
   `x86_64-unknown-linux-gnu` sysroot `.rlib`s, `100%` of FDEs use strictly
   `10` register/offset opcodes (`DW_CFA_advance_loc{,1,2}`, `DW_CFA_def_cfa`,
   `DW_CFA_def_cfa_offset`, `DW_CFA_def_cfa_register`, `DW_CFA_offset`,
   `DW_CFA_restore`, `DW_CFA_nop`, `DW_CFA_GNU_args_size`). Adding `2`
   remember/restore opcodes and `2` bounded `DW_OP_bregN` expression forms
   (`[DW_OP_breg6 disp, DW_OP_deref]` and `[DW_OP_breg6 disp]`, emitted by GCC
   `15.2.0` DRAP when combining `aligned(64)` with `alloca`) yields a minimal,
   loop-free, fail-closed `Trusted.DwarfCfi` evaluator mechanized in
   `support/DwarfEhFrameUnwindProbe.lean` (`1,297` lines, synchronous Lean
   `v4.34.1` compile `3.8 s`, standalone fresh-kernel private replay, axioms
   `{propext, Quot.sound}`). The mechanization proves **Rule 1** (universal
   non-unwinding `asm!` CFI delta neutrality) and **Rule 2** (zero-TCB
   Statement-Origin Separation on `nounwind`-closed subgraphs vs. kernel-checked
   `Trusted.DwarfCfi` + `CfiMatchesMachineState` soundness across arbitrarily
   nested heterogeneous `UnwindLinkFrame` call stacks into
   `TerminalOut.unwound` / `mirCatch`), alongside ten negative canaries.

## Applicability

This report governs formal machine-code, inline-assembly, and cross-language FFI
verification on **System V AMD64 ELF (`x86_64-unknown-linux-gnu`)** under a
closed three-axiom Lean 4 kernel ceiling (`{propext, Classical.choice,
Quot.sound}`).

Relationships among the subjects in `REPORT.json`:

- **Rust compiler and normative specification baselines:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`,
    bundled LLVM `23.1.1` at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) and
    `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`, bundled LLVM `23.1.5`
    at `0a5579eb649d3634a9c30ac873300cc2944fa070`): tested for stable `asm!` FDE
    poisoning (PoC B), cross-language C/C++ unwinding under `-C panic=unwind`
    and `-C panic=abort` (PoC C), feature gating of `may_unwind` (`E0658`) and
    `clobber_abi("C-unwind")`, and the `28`-`.rlib` sysroot FDE census (`1.99.1`).
  - `rust-lang/rust` `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`,
    bundled LLVM `23.1.5` at `0a5579eb649d3634a9c30ac873300cc2944fa070`): tested
    for `#![feature(asm_unwind)]` (`options(may_unwind)`) in PoC A, the LLVM
    `ShrinkWrap` `alignstack` miscompilation across `-O0`..`-O3`, and nightly
    parity on PoCs B and C.
  - `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`): supplies
    normative inline-assembly and FFI unwinding contracts (`r[asm.rules.unwind]`,
    `r[asm.options.supported-options.nostack]`, `r[items.fn.extern.unwind]`).
- **C/C++ compiler, runtime unwinder, and ELF inspection baseline:**
  `gcc` and `g++` `15.2.0` (`Debian 15.2.0-14`, `x86_64-linux-gnu`), runtime
  DSOs (`libgcc_s.so.1`, `libstdc++.so.6`, `libc.so.6`), GNU Binutils `2.47`
  (`readelf`, `objdump`, `objcopy`), and Debian LLVM `21.1.8`
  (`llvm-dwarfdump`).
- **Mechanization kernel and target trust architecture:**
  `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) and
  `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, specifically
  `Trusted.MirSemantics.TerminalOut` and `TrustedBoundary.lean` private-level
  kernel replay and Statement-Origin Separation).

Version-shared vs. version-specific behavior:

- **Shared across `1.99.1`, `1.100.0`, and `1.102.0-nightly`:** Instability of
  `options(may_unwind)` (`#![feature(asm_unwind)]`, `E0658` on stable),
  rejection of `clobber_abi("C-unwind")`, all seven non-`may_unwind` `asm!` FDE
  poisoning vectors (`B1`–`B7`), `-C panic=abort` lowering of `extern
  "C-unwind"` calls to `landingpad cleanup` + `panic_cannot_unwind`, and emitted
  `DW_CFA_*` opcode sets.
- **Nightly-only execution (`1.102.0-nightly`):** Direct execution of
  `options(may_unwind)` (`PoC A1`–`A4`), because stable `1.99.1` and `1.100.0`
  gate `options(may_unwind)` behind `#![feature(asm_unwind)]`.

Relation to adjacent corpus reports (built upon without duplication):

- `verifying-compiled-c-cpp-machine-code-in-lean4-lifting-and-cutpoint-scaling`
  establishes Statement-Origin Separation for untrusted `.eh_frame` cutpoint
  hints in **non-unwinding** C/C++ leaf proofs; this report establishes where
  that zero-TCB hint regime ends and how `.eh_frame` enters the TCB when
  unwinding is reachable.
- `rust-asm-goto-labels-sym-const-and-assembler-directive-hazards` catalogs
  `.init_array`, `.include`/`.incbin`, `.macro`, and unbalanced `.section`
  hazards; this report resolves the `.cfi_*`, `.cfi_escape`, `.cfi_personality`,
  and `.cfi_lsda` unwinding hazards and mechanizes the exact FDE neutrality rule.
- `compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026`,
  `coupled-backend-seam-verification-subregisters-vzeroupper-probestack-and-cfi`,
  `reentrant-ffi-mixed-mir-isa-call-stacks-tree-borrows-and-oracle-composition`,
  `unwinding-on-elf-and-macho-targets`, and
  `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking` establish
  two-phase Itanium LSDA semantics, outlined-thunk alignment, `LinkFrame`
  normal-return composition, and Mach-O/Windows unwind encodings; this report
  adds live x86-64 `asm!` FDE poisoning, the LLVM `ShrinkWrap` `may_unwind`
  miscompilation, the `14,800+`-FDE opcode census including GCC DRAP
  expressions, and unwind-traversable `UnwindLinkFrame` composition in Lean 4.

## Findings

### 1. Live `options(may_unwind)` CFI Corruption and Upstream LLVM `ShrinkWrap` Miscompilation (PoC A)

Basis: `normative` (`rust-lang/reference@c9cc32825b`: `src/inline-assembly.md` rules `r[asm.rules.unwind]`, `r[asm.options.supported-options.nostack]`) + `source` (`rust-lang/rust@3ef0c22cdb`: `compiler/rustc_codegen_ssa/src/mir/block.rs:348-395`, `compiler/rustc_builtin_macros/src/asm.rs`; `rust-lang/llvm-project@0a5579eb64`: `llvm/lib/CodeGen/ShrinkWrap.cpp:302-381, 845-857`) + `execution` (`support/reproduce_unwind_pocs_and_census.py`, `support/empirical_receipts.json`)

#### 1.1 Feature-Gate and `clobber_abi` Surface (`1.99.1`–`1.102.0-nightly`)

Across `rustc 1.99.1`, `1.100.0`, and `1.102.0-nightly`:

1. `options(may_unwind)` remains **unstable** (`error[E0658]: the 'may_unwind'
   option is unstable`, tracking issue `#93334`), requiring `#![feature(asm_unwind)]`.
2. `clobber_abi("C-unwind")` is **rejected** even under `#![feature(asm_unwind)]`
   (`error: invalid ABI for 'clobber_abi'; supported ABIs: 'C', 'system',
   'efiapi', 'win64', 'sysv64'`); assembly calling an `extern "C-unwind"`
   routine must spell `clobber_abi("C")` alongside `options(may_unwind)`.
3. On stable Rust (`1.99.1` / `1.100.0`), invoking an `extern "C-unwind"`
   function inside `asm!("call {cb}", ...)` **without** `options(may_unwind)` is
   immediate undefined behavior under `r[asm.rules.unwind]` if `cb` panics: in
   live execution (`poc_a` `a4_no_may_unwind_with_drop`), when `asm!` is the
   only call in a function holding a local `Guard`, `rustc` assigns the `asm!`
   terminator `UnwindAction::Unreachable`, omits `.gcc_except_table` entirely,
   and allows the panic to unwind straight through the frame into outer
   `catch_unwind` (`rc = 0`, `caught = true`) while **silently skipping local
   `Guard::drop` (`drops = 0`)**.

#### 1.2 Normal-Return Completeness vs. Unwind Corruption (`A1`, `A2`, `A3`)

Normal return (`ret`) restores `RSP` and callee-saved registers directly via
machine instructions (`add rsp, 8; pop r12; ret`) without reading `.eh_frame`.
Unwinding (`_Unwind_RaiseException` in `libgcc_s`) never executes instructions
after `call {cb}` and instead interprets the enclosing function's `.eh_frame`
FDE row at `return_pc - 1`:

| PoC A Variant (`rustc 1.102.0-nightly -C opt-level=2`) | `asm!(..., options(may_unwind))` Template | Normal Return (`1,000` runs) | Unwind Outcome Inside `std::panic::catch_unwind` | Safe Caller Local `v2` (`0x3333_3333_3333_3333` in `r12`) |
| :--- | :--- | :--- | :--- | :--- |
| **`A1`: Missing `.cfi_adjust_cfa_offset`** | `push rbx; sub rsp, 8; mov rbx, ...; call {cb}; add rsp, 8; pop rbx` | **`1,000 / 1,000` pass** (`rc = 0`) | **Aborts (`rc = -6`)** (`failed to initiate panic, error 5` / `SIGSEGV` if bogus `RIP` maps) | Process terminated |
| **`A2`: Valid CFA, missing `.cfi_rel_offset r12`** | `push r12; .cfi_adjust_cfa_offset 8; sub rsp, 8; .cfi_adjust_cfa_offset 8; mov r12, 0x7777...; call {cb}; ...` | **`1,000 / 1,000` pass** (`rc = 0`) | **`rc = 0`, `caught = true` (zero crash!)** | **Silently corrupted to `0x7777777777777777`!** |
| **`A3`: Full balanced CFI annotations** | Adds `.cfi_rel_offset r12, 0` after `push r12` and `.cfi_restore r12` after `pop r12` | **`1,000 / 1,000` pass** (`rc = 0`) | **`rc = 0`, `caught = true`** | **Preserved (`0x3333333333333333`)** |

**Key verification consequence (`A2`):** Testing or proving only that
`catch_unwind` succeeds without crashing is insufficient. Because `A2` supplies
exact `.cfi_adjust_cfa_offset` deltas, `libgcc_s` computes the exact caller
`CFA` and `RIP` and lands cleanly in `catch_unwind`, while keeping `R12`'s
default CIE rule (`sameValue`) so `0x7777777777777777` flows directly into an
unmodified safe-Rust variable in the outer caller.

#### 1.3 Upstream LLVM `23.1.5` `ShrinkWrap` `alignstack` Miscompilation (`A4`)

Under Rust Reference rule `r[asm.options.supported-options.nostack]`, omitting
`options(nostack)` guarantees that `rsp` is 16-byte aligned (`rsp % 16 == 0` on
System V AMD64) upon entering `asm!`, so an internal `call` pushes an 8-byte
return address and enters the callee with `(rsp - 8) % 16 == 8`. `rustc`
accordingly emits the LLVM `alignstack` modifier on the `invoke` instruction:

```llvm
%0 = invoke i64 asm sideeffect alignstack inteldialect unwind
  "mov rax, rsp", "={ax},~{dirflag},~{fpsr},~{flags},~{memory}"()
  to label %bb1 unwind label %cleanup
```

However, when the enclosing function has a cleanup landing pad that uses **zero
stack slots** (e.g., `ZeroStackGuard::drop` increments an `AtomicUsize` via
`lock inc qword ptr [rip + ...]` and calls `_Unwind_Resume`), compiling at
`-C opt-level=1`, `2`, or `3` produces:

| Compiler Flags (`rustc 1.102.0-nightly`, LLVM `23.1.5`) | Observed `rsp % 16` Inside `asm!(..., options(may_unwind))` | Effect When `asm!` Executes `call {cb}` and `cb` Panics |
| :--- | :---: | :--- |
| `-C opt-level=0` | **`0`** (compliant) | Clean unwind |
| `-C opt-level=1` / `2` / `3` (default) | **`8` (MISCOMPILED!)** | **`SIGSEGV` (`rc = -11`)** on aligned `movaps` inside `_Unwind_RaiseException` |
| `-C opt-level=2 -C llvm-args=-enable-shrink-wrap=false` | **`0`** (compliant) | Clean unwind |

**Exact root cause in `rust-lang/llvm-project@0a5579eb649d3634a9c30ac873300cc2944fa070`:**

1. In `a5_same_frame_drop_zero_rsp_delta` disassembly (`objdump -d -M intel`),
   entry block `0x0` begins directly with `0: e8 00 00 00 00 call maybe_panic`
   (**no** `push rax`), while `e: 50 push rax` is emitted solely inside the
   cold landing pad before `1a: call _Unwind_Resume`!
2. In `llvm/lib/CodeGen/ShrinkWrap.cpp:302-381`, `ShrinkWrapImpl::useOrDefCSROrFI`
   checks `MI.getOpcode() == FrameSetupOpcode`, `MI.getOpcode() ==
   FrameDestroyOpcode`, explicit CSR/SP operands, `RegMask`, and `FrameIndex`
   operands, **omitting** `MI.isInlineAsm() && (MI.getOperand(
   InlineAsm::MIOp_ExtraInfo).getImm() & InlineAsm::Extra_IsAlignStack)`.
3. Consequently, after scanning `MBB 0`, `Save` and `Restore` remain `nullptr`.
   When `performShrinkWrapping` (`ShrinkWrap.cpp:845-857`) visits `MBB 1`
   (`MBB->isEHPad() == true`), `updateSaveRestorePoints(*MBB_1)` sets
   `Save = MBB_1` and `Restore = MBB_1` (because `MBB 1` terminates in
   `unreachable`, `ArePointsInteresting()` stays `true`), placing the 8-byte
   alignment `push rax` exclusively inside the landing pad.
4. **Same-frame landing-pad invariant (`A4b`):** Even when `ShrinkWrap` is
   disabled so entry `rsp % 16 == 0`, if a function has an in-frame cleanup
   landing pad (`UnwindAction::Cleanup`) **and** `asm!(..., options(may_unwind))`
   shifts `rsp` across `call {cb}` (`push rbx; sub rsp, 8; call {cb}; add rsp, 8;
   pop rbx`), `libgcc_s` installs the **same-frame** landing pad via
   `_Unwind_SetIP(context, lpad)` **without** popping the current FDE (`RSP`
   remains shifted by `-16`), crashing the Rust landing pad with `SIGSEGV`
   (`rc = -11`) even when `.cfi_adjust_cfa_offset` is present. Thus an
   `options(may_unwind)` `asm!` block inside a function with local `Drop`
   cleanups must maintain `rsp == entry_asm_rsp` at every internal unwinding
   `call` site (using caller-allocated alignment rather than internal `push` /
   `sub rsp`).

---

### 2. Silent FDE Poisoning of Safe Rust Functions by *Non-`may_unwind`* `asm!` (PoC B)

Basis: `source` (`rust-lang/llvm-project@0a5579eb64`: `llvm/lib/MC/MCParser/AsmParser.cpp`, `llvm/lib/MC/MCDwarf.cpp`; `rust-lang/rust@58cf8f9c35`: `library/std/src/sys/personality/dwarf/eh.rs:66-172`) + `execution` (`support/reproduce_unwind_pocs_and_census.py`, `support/empirical_receipts.json`)

Every non-naked Rust function compiled with unwind tables wraps its entire body
in a single `.cfi_startproc`..`.cfi_endproc` FDE. Because LLVM's `AsmPrinter`
parses inline `asm!` templates inside that open `MCDwarfFrameInfo` context with
no directive filter or post-`asm!` state restoration, a **non-`may_unwind`**,
**0-instruction** `asm!(..., options(nomem, nostack, preserves_flags))` block on
**stable Rust (`1.99.1` and `1.100.0`)** and nightly (`1.102.0-nightly`) can
corrupt the enclosing function's FDE and LSDA for ordinary safe Rust calls later
in the same function:

| PoC B Vector (All Tested on Stable `1.99.1`, `1.100.0`, and Nightly `1.102.0`) | Injected `asm!` Directive (NO `may_unwind`, `0` or `1` `nop` bytes) | Normal Return | Downstream Safe Rust `panic!()` Caught by `catch_unwind` | Exact Mechanism in `libgcc_s` / `rust_eh_personality` |
| :--- | :--- | :--- | :--- | :--- |
| **`B1`: Unbalanced CFA offset** | `.cfi_adjust_cfa_offset 16` (`0` insn bytes) | `rc = 0`, `drops = 1` | **Aborts (`rc = -6`)** (`SIGSEGV` or `error 5`, `drops = 0`) | Shifts FDE `CFA` by `+16` at all subsequent PCs in the enclosing function |
| **`B2`: Dead-branch layout poisoning** | `if !skip { asm!("nop\n.cfi_adjust_cfa_offset 16"); }` called with `skip = true` (**never executed!**) | `rc = 0`, `drops = 1` | **Aborts (`rc = -6`, `drops = 0`)** | DWARF CFI executes FDE stream linearly by `.text` address `0 .. ret_pc - 1`, ignoring runtime CFG jumps |
| **`B3`: Return-address erasure** | `.cfi_undefined rip` (`0` insn bytes) | `rc = 0`, `drops = 1` | **Aborts (`rc = -6`, `error 5`, `drops = 0`)** | Sets column `16` (`RIP`) to `DW_CFA_undefined`; Phase 1 treats frame as bottom of stack (`_URC_END_OF_STACK`) |
| **`B4`: Raw `.cfi_escape` CFA override** | `.cfi_escape 0x0e, 0x40` (`DW_CFA_def_cfa_offset 64`, `0` insn bytes) | `rc = 0`, `drops = 1` | **Aborts (`rc = -6`, `error 5`, `drops = 0`)** | Emits raw DWARF CFI opcodes directly into `.eh_frame`, bypassing `.cfi_*` mnemonic filters |
| **`B5`: Raw `.cfi_escape` safe-local overwrite + ASLR leak** | `.cfi_escape 0x8c, 0x01` (`DW_CFA_offset r12, 1 * -8`, `0` insn bytes) | `rc = 0`, `v1` intact | **`rc = 0`, `caught = true`, safe local `v1` overwritten with `0x00005613f164e3d2`!** | Tells `libgcc_s` that caller's `R12` was saved at `[CFA - 8]` (the return `RIP` slot!), corrupting caller's safe local and leaking PIE `.text` ASLR slide |
| **`B6`: Default PIE `.cfi_personality` hijack** | `.cfi_personality 0x9b, DW_ref_skip_drops_personality` (`0` insn bytes) | `rc = 0`, `drops = 1` | **`rc = 0`, `caught = true`, **`drops = 0`** (all local `Drop`s skipped!)** | Encoding `0x9b` (`indirect \| pcrel \| sdata4`) links cleanly in PIE and replaces `rust_eh_personality` with a routine returning `_URC_CONTINUE_UNWIND` (`8`) |
| **`B7`: Default PIE `.cfi_lsda` hijack** | `.cfi_lsda 0x1b, EMPTY_LSDA_BYTES` (`[0xff, 0xff, 0x01, 0x05, 0x00, 0xff, 0x0f, 0x00, 0x00]`, `0` insn bytes) | `rc = 0`, `drops = 1` | **`rc = 0`, `caught = true`, **`drops = 0`** (all local `Drop`s skipped!)** | Encoding `0x1b` (`pcrel \| sdata4`) overrides `.gcc_except_table` with a valid LSDA whose `cs_lpad == 0` (`EHAction::None`), so `rust_eh_personality` itself skips all local `Drop`s |

**Critical TCB lesson from PoC B:** A verifier **cannot** ignore `.cfi_*` and
`.cfi_escape` directives merely because an `asm!` block lacks
`options(may_unwind)` or contains zero memory/stack instructions. Even if the
`asm!` block itself never unwinds—and even if it sits on a dynamically dead
branch—any mutation to the open FDE's `(CFA, regRules, savedRows, personality,
lsda)` state persists across all physically subsequent basic blocks in that Rust
function.

---

### 3. Cross-Language C Callback Unwinding and C++ `throw` Across `extern "C-unwind"` (PoC C)

Basis: `normative` (`rust-lang/reference@c9cc32825b`: `r[items.fn.extern.unwind]`) + `source` (`rust-lang/rust@58cf8f9c35`: `compiler/rustc_codegen_ssa/src/mir/block.rs:2199-2350`) + `execution` (`support/reproduce_unwind_pocs_and_census.py`, `support/empirical_receipts.json`)

#### 3.1 Intermediate GCC `15.2.0` C `.o` Frame (`catch_unwind -> c_qsort_style_invoke -> extern "C-unwind" rust_cb`)

Placing a separately compiled C `.o` function (`c_qsort_style_invoke`, with a
4-word `volatile` stack frame and a GCC `__attribute__((cleanup(c_cleanup_fn)))`
local variable) between two Rust `-C panic=unwind` frames yields three distinct
behaviors depending on GCC's unwind flags:

| GCC `15.2.0` Compilation Flags (`x86_64-linux-gnu`) | `.eh_frame` Emitted? | `.gcc_except_table` Emitted? | Normal Return (`cb` returns `100`) | Unwind (`cb` panics inside `catch_unwind`) |
| :--- | :---: | :---: | :--- | :--- |
| `-O2 -fno-exceptions -fno-asynchronous-unwind-tables -fno-unwind-tables` | **No** | No | `rc = 0` (`rdrops = 2, ccleanup = 1`) | **Aborts (`rc = -6`)**: Phase 1 hits missing FDE (`error 5`), **`rdrops = 0, ccleanup = 0`** |
| `-O2` (Debian x86-64 default) or `-O2 -fasynchronous-unwind-tables` | **Yes** | **No** | `rc = 0` (`rdrops = 2, ccleanup = 1`) | `rc = 0`, `caught = true`, **`rdrops = 2`, `ccleanup = 0`** (C cleanup silently skipped!) |
| `-O2 -fexceptions` | **Yes** | **Yes** (`__gcc_personality_v0`) | `rc = 0` (`rdrops = 2, ccleanup = 1`) | `rc = 0`, `caught = true`, **`rdrops = 2, ccleanup = 1`** (both Rust `Drop` and C cleanup run!) |

#### 3.2 G++ `15.2.0` `throw` Across `extern "C-unwind"` vs. `extern "C"` Under `-C panic=unwind` and `-C panic=abort`

Testing `g++ 15.2.0 -O2` (`try { rust_fn(1); } catch (const CppExn &e)`) calling
into a Rust `staticlib` compiled with `rustc 1.99.1` under both
`-C panic=unwind` and `-C panic=abort`:

| Rust Export Signature & Crate `-C panic` Mode | Emitted LLVM Landing Pad in Rust Export | Runtime Outcome When C++ Callee Executes `throw CppExn{77}` |
| :--- | :--- | :--- |
| `extern "C-unwind" fn` (`-C panic=unwind`, with local `BridgeGuard`) | `landingpad cleanup` -> `BridgeGuard::drop` -> `_Unwind_Resume` | **`rc = 0`, `caught_cpp = 77`, `rust_drops = 1`, `cpp_drops = 1`** |
| `extern "C" fn` (no local `Drop`, `-C panic=unwind`) | `landingpad filter [0 x ptr] zeroinitializer` -> `panic_cannot_unwind` | **Deterministic abort (`rc = -6`)**: `panic in a function that cannot unwind` |
| `extern "C" fn` (with local `Drop`, `-C panic=unwind`, outer C++ `catch` present) | `landingpad cleanup` -> `BridgeGuard::drop` -> `panic_cannot_unwind` | **Deterministic abort (`rc = -6`)** in Phase 2 (note: if *no* outer C++ `catch` exists on the stack, Phase 1 sees `EHAction::Cleanup` and aborts via `std::terminate` without running Phase 2 drops, per `unwinding-on-elf-and-macho-targets`) |
| **`extern "C-unwind" fn` (`-C panic=abort`, with or without local `Drop`!)** | `invoke @ext_cuw() unwind label %cleanup` with `landingpad { ptr, i32 } cleanup` -> `tail call panic_cannot_unwind()` | **Aborts (`rc = -6`)** (`panic in a function that cannot unwind`), preventing C++ `throw` from silently bypassing omitted `-C panic=abort` `Drop` glue |

Inspecting the exact LLVM IR emitted by `rustc 1.99.1 -C opt-level=2
-C panic=abort` (`support/empirical_receipts.json`) reveals a subtle codegen
seam: `cuw_in_abort_crate_with_drop` is aliased to `cuw_in_abort_crate_no_drop`,
and **both** emit `landingpad { ptr, i32 } cleanup` (`cs_action_entry = 0`,
`EHAction::Cleanup`) followed by `panic_cannot_unwind()`, rather than `filter
[0 x ptr] zeroinitializer` (`EHAction::Filter`). Consequently, when an outer C++
`try`/`catch` exists on the stack, Phase 2 enters `%cleanup` and aborts via
`panic_cannot_unwind()`; without an outer handler, Phase 1 hits
`_URC_END_OF_STACK` and `std::terminate()` aborts directly in `__cxa_throw`; and
under POSIX `pthread_exit` (`_UA_FORCE_UNWIND`), `EHAction::Cleanup` enters
`%cleanup` and aborts the process instead of allowing forced thread exit.

---

### 4. Empirical `.eh_frame` (`DW_CFA_*`) and `.gcc_except_table` Opcode Census (`14,800+` FDEs)

Basis: `execution` (`support/reproduce_unwind_pocs_and_census.py`, `support/empirical_receipts.json`) + `normative` (DWARF v4/v5 §6.4, LSB `.eh_frame` / `.gcc_except_table`)

#### 4.1 Opcode Distribution Across Hardened Profiles, Full Rust Sysroot, and System DSOs

| Artifact / Corpus | CIEs | FDEs | Observed CFA Base Registers | `advance_loc*` | `def_cfa` / `def_cfa_reg` / `def_cfa_off` | `offset` (`_ext_sf`) | `restore` / `register` / `undefined` | `remember` / `restore_state` | `GNU_args_size` | `def_cfa_expr` / `expression` |
| :--- | ---: | ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `rustc 1.99.1` sysroot (`28` `.rlib`s: `std`, `core`, `alloc`, `panic_unwind`, `compiler_builtins`, `jemalloc`, ...) | 315 | **5,079** | `RSP` (3,116), `RBP` (4,359) | 23,686 | 5,067 / 2,408 / 14,265 | 12,845 (0) | 405 / 0 / **0** | **0 / 0** | 361 | **0 / 0** |
| `rustc 1.99.1` & `1.102-nightly` (`-O2`/`-O3 +avx2`, `45 KiB` probe loop, `align(64)`, `10`-arg `catch_unwind`) | 1 | 4 | `RSP` (3), `RBP` (2), **`R11` (1)** | 34 | 3 / 3 / 24 | 6 (0) | 0 / 0 / 0 | 0 / 0 | 7 | **0 / 0** |
| `gcc 15.2.0` (`-O3 -mavx2 -fPIC -fexceptions -fstack-protector-strong -fstack-clash-protection -fcf-protection=full`) | 2 | 6 | `RSP` (6), `RBP` (3), **`R10` (2)**, **`R11` (1)** | 28 | 9 / 3 / 10 | 9 (0) | 0 / 0 / 0 | 4 / 4 | 1 | **1 / 2** |
| `g++ 15.2.0` (`-O2 -mavx2 -fPIC -fstack-protector-strong -fstack-clash-protection -fcf-protection=full`) | 1 | 4 | `RSP` (2), `RBP` (2) | 10 | 3 / 1 / 4 | 9 (0) | 0 / 0 / 0 | 2 / 2 | 2 | **0 / 0** |
| Debian `libstdc++.so.6` (`GCC 15.2`) | 2 | **5,343** | `RSP` (178), `RBP` (152) | 26,281 | 205 / 125 / 16,484 | 11,543 (0) | 3,725 / 0 / 0 | 2,810 / 2,810 | 179 | **1 / 0** (`.plt` stub only) |
| Debian `libgcc_s.so.1` (`GCC 15.2`) | 1 | 270 | `RSP` (17), `RBP` (18), `RCX` (4) | 1,395 | 25 / 14 / 810 | 593 (0) | 214 / 4 / 0 | 243 / 243 | 0 | **1 / 0** (`.plt` stub only) |
| Debian `libc.so.6` (`glibc`) | 3 (`zRS` sigreturn) | **3,919** | `RSP`, `RBP`, `R10`, `R11`, `RDI`, `RDX` | 19,759 | 79 / 65 / 17,469 | 5,984 (20) | 366 / 12 / 2 | 2,027 / 2,027 | 4 | **3 / 23** (`.plt` + `__restore_rt` / `swapcontext`) |

#### 4.2 Exact Minimal Fail-Closed `DW_CFA_*` Subset for `Trusted.DwarfCfi`

Basis: `execution` + `derived`

From the `14,800+`-FDE census, a TCB `Trusted.DwarfCfi` evaluator for linked
Rust, `.S`, and GCC/Clang C/C++ `.o` static archives does **not** need a
general Turing-capable DWARF expression stack machine:

1. **Core 12-Instruction Register/Offset Machine (covers `100%` of `rustc`/LLVM
   `.o` and sysroot `.rlib`s, and `99.9%+` of GCC/G++ functions):**
   - *PC advance & padding:* `DW_CFA_advance_loc` (`0x40|δ`),
     `DW_CFA_advance_loc1/2/4` (`0x02`–`0x04`), `DW_CFA_nop` (`0x00`).
   - *CFA register + signed/unsigned offset:* `DW_CFA_def_cfa` (`0x0c`),
     `DW_CFA_def_cfa_register` (`0x0d`), `DW_CFA_def_cfa_offset` (`0x0e`),
     `DW_CFA_def_cfa_sf` (`0x12`), `DW_CFA_def_cfa_offset_sf` (`0x13`),
     supporting GPRs `RSP` (`7`), `RBP` (`6`, standard FP and `and rsp, -32` /
     `-64` dynamic stack realignment), `R10` (`10`, GCC initial DRAP), and `R11`
     (`11`, LLVM and GCC `>= 9`-page stack-clash probe loops).
   - *Saved-register recovery:* `DW_CFA_offset` (`0x80|r`),
     `DW_CFA_offset_extended` (`0x05`), `DW_CFA_offset_extended_sf` (`0x11`),
     `DW_CFA_same_value` (`0x08`), `DW_CFA_restore` (`0xc0|r` / `0x06`), and
     `DW_CFA_register` (`0x09`).
   - *Epilogue / `.cold` split state stack:* `DW_CFA_remember_state` (`0x0a`)
     and `DW_CFA_restore_state` (`0x0b`), failing closed on stack underflow.
   - *Outgoing stack-argument size:* `DW_CFA_GNU_args_size` (`0x2e`), which
     leaves cross-frame caller recovery (`RSP := CFA`) unchanged while adding
     `args_size` to `RSP` if installing an **in-frame** landing pad
     (`_URC_INSTALL_CONTEXT`) around a call with `> 6` pushed arguments.
2. **Bounded 2-Template DRAP Expression Extension (covers `100%` of GCC `15.2.0`
   `aligned(64)` + `alloca()` functions):**
   When a single GCC function combines `> 16`-byte stack alignment with dynamic
   `alloca()` (`drap_fn` in `support/reproduce_unwind_pocs_and_census.py`), GCC
   spills the entry `CFA` pointer (`r10`) onto the realigned frame `[rbp - disp]`
   and emits **solely** two fixed DWARF expression shapes:
   - `DW_CFA_def_cfa_expression` (`0x0f`): `[DW_OP_breg6 (disp), DW_OP_deref]`
     $\implies \text{CFA} := \text{mem}_{64}[\text{RBP} + \text{disp}]$.
   - `DW_CFA_expression` (`0x10`): `reg, [DW_OP_breg6 (disp)]`
     $\implies \text{reg} := \text{mem}_{64}[\text{RBP} + \text{disp}]$ (needed
     because callee-saved pushes sit at fixed offsets from `RBP`, not from the
     pre-alignment `CFA`).
   Pattern-matching those two exact byte sequences (generalized over GPR `bregN`)
   and **failing closed** on all other `DW_CFA_def_cfa_expression` /
   `DW_CFA_expression` / `DW_CFA_val_expression` streams, `DW_CFA_undefined` on
   `RIP` or callee-saved registers, and `zRS` signal trampolines keeps
   `Trusted.DwarfCfi` structural, total without fuel, and ~150 lines of
   tactic-free Lean.

---

### 5. Dual-Role `.eh_frame` Architecture and Lean `v4.34.1` Mechanization

Basis: `derived` + `execution` (`support/DwarfEhFrameUnwindProbe.lean`, `support/empirical_receipts.json`)

To eliminate both TCB bloat on `nounwind` code and soundness holes on
unwinding/inline-`asm!` code, `.eh_frame` verification splits cleanly along two
mechanized rules:

#### 5.1 Rule 1: Universal Non-Unwinding `asm!` CFI Delta Neutrality

Every function-scoped `asm!` block spanning `[asmStart, asmEnd)` in an enclosing
Rust function's FDE (regardless of whether `options(may_unwind)` is set) must
satisfy:

1. **Zero CIE/FDE header overrides:** No `.cfi_personality`, `.cfi_lsda`,
   `.cfi_signal_frame`, or `.cfi_return_column` directives (`personalityHijacked
   = false ∧ lsdaOverride = none`).
2. **Exact CFI state delta neutrality across `[asmStart, asmEnd)`:** Evaluating
   the `asm!` block's CFI directives from the compiler's pre-`asm!` state
   `stPre = (asmStart, row, savedRows)` reaches `some (asmEnd, row, savedRows)`
   (preserving `row.cfa`, every register's `RegRule`, `row.argsSize`, and the
   `.cfi_remember_state` stack `savedRows`).

In `support/DwarfEhFrameUnwindProbe.lean`,
`DwarfUnwindProofs.rule1_asm_cfi_delta_preserves_downstream_fde` proves that for
any compiler prefix `preOps`, any neutral `asmOps` (including zero CFI
directives, balanced `push`/`pop` `.cfi_adjust_cfa_offset` + `.cfi_offset` /
`.cfi_restore`, or balanced `.cfi_remember_state` / `.cfi_restore_state`), and
any compiler suffix `postOps`, **every** downstream PC `queryPc >= asmStart +
asmByteLen` evaluates to the exact unpoisoned compiler `CfiRow`:

```lean
theorem rule1_asm_cfi_delta_preserves_downstream_fde ... :
    evalFdeAt fdeWithAsm queryPc = evalFdeAt fdeCompiler queryPc
```

Conversely, negative canaries `canary_poc_b1_zero_insn_cfa_shift_breaks_unwind`,
`canary_poc_b2_dead_branch_asm_poisons_linear_fde`,
`canary_poc_b3_undefined_rip_aborts_phase1`,
`canary_poc_b5_escape_offset_leaks_rip_into_caller_r12`, and
`canary_poc_b6_b7_personality_and_lsda_hijack_skip_drops` prove that violating
any clause of Rule 1 breaks downstream safe-Rust unwinding—even when the `asm!`
block emits 0 machine bytes or lies on a runtime-unexecuted dead branch.

#### 5.2 Rule 2: Unwind-Unreachable vs. Unwind-Traversable Partition Over `UnwindLinkFrame`

- **Regime 2A (`nounwind`-Closed Subgraphs — `.eh_frame` 100% Outside `Trusted`):**
  When every callee reachable from a foreign `.o`, `.S`, or `asm!` frame is
  `nounwind` (`CalleeBehavior.normalReturn`),
  `DwarfUnwindProofs.rule2a_nounwind_frame_eh_frame_irrelevant` proves that
  execution is syntactically independent of `fde : Option FdeRecord`.
  `LockedNounwindObligation.verify_nounwind_leaf_abi` consumes
  `UntrustedHints.EhFrameCutpointHint` inside its proof body while keeping its
  theorem type 100% free of `UntrustedHints.*` and `Trusted.DwarfCfi.*`
  constants (mechanically confirmed via standalone private-level kernel replay:
  `type_hints = 0`, `type_cfi = 0`, `val_hints = 3`).
- **Regime 2B (Unwind-Traversable Frames — `Trusted.DwarfCfi` +
  `CfiMatchesMachineState`):**
  Whenever an `options(may_unwind)` `asm!` call site, `naked_asm!` / `global_asm!`
  / `.S` frame, or compiled C/C++ `.o` call site invokes a callee that may
  unwind (`extern "C-unwind"` or C++ `throw`), the frame is pushed onto the
  heterogeneous stack as `UnwindLinkFrame.isaSuspended retPc (some fde)
  expectedCallerCtx`, carrying the proof obligation
  `CfiMatchesMachineState fde retPc expectedCallerCtx regsAtCall memAtCall`:
  - **`rule2b_stepUnwindFrame_sound`:** Proves that `stepUnwindFrame` succeeds
    with `.poppedToCaller callerRegs` and restores exact `caller.rsp`,
    `caller.rip`, and all six x86-64 callee-saved GPRs (`rbp`, `rbx`,
    `r12`–`r15`).
  - **`gcc_drap_expression_unwind_sound`:** Instantiates
    `rule2b_stepUnwindFrame_sound` on GCC `15.2.0`'s DRAP
    `DW_CFA_def_cfa_expression` (`derefBreg .rbp (-24)`) and `DW_CFA_expression`
    (`atBreg .rbp ...`) rules across symbolic `dynRsp` (`alloca` + 64-byte
    alignment), proving exact recovery of `(callerRsp, callerRip, savedRbp,
    savedR12, savedRbx)`.
  - **`rule2b_multi_frame_unwind_preserves_state`:** Proves by induction over
    any `ValidUnwindPrefix` of arbitrarily interleaved `isaSuspended` frames and
    `mirCleanup` (`Drop`) frames that `runStackUnwind` reaches either
    `TerminalOut.unwound finalMem` or an enclosing `mirCatch` (`catch_unwind`)
    with exact caller registers, LIFO `Drop` order, and memory invariants
    intact—whereas omitting CFA (`canary_poc_a1`), omitting `r12` save rules
    (`canary_poc_a2`), shrink-wrapping `alignstack` (`canary_llvm_shrinkwrap`),
    or linking `.eh_frame`-less C `.o` files (`canary_poc_c1`) provably fails.

## Boundaries

- **Dynamic ELF PLT (`DW_OP_breg16 RIP`) and POSIX signal frames (`zRS`):**
  **Known not to apply** to the 12-opcode + 2-DRAP-pattern `Trusted.DwarfCfi`
  subset without extension. As measured in Section 4.1, linked shared libraries
  (`libgcc_s.so.1`, `libstdc++.so.6`, `libc.so.6`) contain one linker-synthesized
  `.plt` FDE using `DW_OP_breg16 RIP+0, DW_OP_lit15, DW_OP_and, ...`, and
  `libc.so.6` contains `zRS` signal-return trampolines (`__restore_rt`, where
  `_Unwind_GetIPInfo` sets `ip_before_instr = 1` and skips the `retPc - 1`
  decrement). Static `.o`/`.a`/`.rlib` verification never traverses `.plt`
  resolver stubs mid-resolution, and Rust does not support unwinding out of
  asynchronous POSIX signal handlers (**unsupported** by Rust).
- **AArch64 / Windows x64 / 32-bit ARM EHABI in `DwarfEhFrameUnwindProbe.lean`:**
  **Not examined** in this package's live x86-64 execution probes (covered in
  neighboring corpus packages `compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026`,
  `unwinding-on-elf-and-macho-targets`, and
  `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`, including
  `DW_CFA_AARCH64_negate_ra_state` and Windows `.pdata`/`.xdata`).
- **Hardware shadow stacks (Intel CET `SHSTK` `_Unwind_Frames_Extra`):**
  **Not examined** on CET-enforced Linux kernels; while `-fcf-protection=full`
  `.o` emission was measured in Section 4, live hardware `SHSTK` SSP popping
  during `libgcc_s` Phase 2 requires CET shadow-stack kernel/CPU activation.
- **Upstream LLVM bug tracker filing status for the `ShrinkWrap` `may_unwind`
  `alignstack` miscompilation:** **Unknown** whether an upstream LLVM issue
  beyond general `inlineasm_br` shrink-wrapping items currently tracks the
  `InvokeInst` + `Extra_IsAlignStack` interaction documented in Section 1.3;
  until fixed upstream, verifiers and code generators targeting LLVM `23.1.x`
  must either forbid `options(may_unwind)` without `options(nostack)` when
  `ShrinkWrap` is enabled, emit an explicit frame/CSR anchor, or pass
  `-C llvm-args=-enable-shrink-wrap=false`.
- **Attractive stronger conclusion not established:** Satisfying Rule 1 (`evalFdeAt
  asmStart = evalFdeAt asmEnd`) on a non-`may_unwind` `asm!` block proves only
  that the `asm!` block does not corrupt `.eh_frame` for *subsequent* code; it
  does **not** by itself prove that the `asm!` block's machine instructions left
  the physical `rsp` and callee-saved registers unchanged at `asmEnd`—that
  machine-state obligation must still be discharged by the ordinary ISA proof of
  the `asm!` body.

## Evidence

1. **Lean `v4.34.1` Mechanization & Fresh-Kernel Replay
   (`support/DwarfEhFrameUnwindProbe.lean`, `1,297` lines):**
   - Pinned kernel: `leanprover/lean4` `v4.34.1`
     (`5045d0056413266e57c625dcd7c365b10e377c52`), compiled synchronously with
     `-DElab.async=false -Ddebug.skipKernelTC=false` (`3.23 s`, `2,912,896 B`
     `.olean`, `0` errors, `0` warnings) and replayed from `Init` at
     `trustLevel := 0, loadExts := false, level := .private` (`775` replayed
     constants).
   - Verified theorems (`15` `#guard_msgs in #print axioms` checks, all strictly
     within `{propext, Quot.sound}`, zero `Classical.choice`, zero `sorryAx`,
     zero `Lean.ofReduceBool`):
     - `LockedNounwindObligation.verify_nounwind_leaf_abi` (`type_hints = 0`,
       `type_cfi = 0`, `val_hints = 3`)
     - `DwarfUnwindProofs.evalOps_append_le` and
       `DwarfUnwindProofs.rule1_asm_cfi_delta_preserves_downstream_fde`
     - `DwarfUnwindProofs.canary_poc_b1_zero_insn_cfa_shift_breaks_unwind`,
       `canary_poc_b2_dead_branch_asm_poisons_linear_fde`,
       `canary_poc_b3_undefined_rip_aborts_phase1`,
       `canary_poc_b5_escape_offset_leaks_rip_into_caller_r12`,
       `canary_poc_b6_b7_personality_and_lsda_hijack_skip_drops`
     - `DwarfUnwindProofs.rule2a_nounwind_frame_eh_frame_irrelevant`
     - `DwarfUnwindProofs.rule2b_stepUnwindFrame_sound`,
       `DwarfUnwindProofs.gcc_drap_expression_unwind_sound`,
       `DwarfUnwindProofs.rule2b_multi_frame_unwind_preserves_state`
     - `DwarfUnwindProofs.canary_poc_a1_may_unwind_missing_cfa_corrupts_unwind`,
       `canary_poc_a2_may_unwind_missing_r12_corrupts_safe_local_on_catch`,
       `canary_llvm_shrinkwrap_invoke_alignstack_violation`,
       `canary_poc_c1_missing_c_eh_frame_aborts_and_skips_drops`
2. **Standalone Empirical Reproducer & Preserved Receipts
   (`support/reproduce_unwind_pocs_and_census.py`,
   `support/empirical_receipts.json`):**
   - Executes PoCs A, B, and C and the GCC DRAP `.eh_frame` probe inside
     `tempfile.TemporaryDirectory()` on `x86_64-unknown-linux-gnu` (`rustc
     1.99.1`, `1.100.0`, `1.102.0-nightly`, `gcc`/`g++ 15.2.0`, `llvm-dwarfdump
     21.1.8`, `readelf 2.47`).
   - Preserves complete opcode and LSDA counts across `5,079` Rust sysroot FDEs
     (`28` `.rlib`s) and `9,532` Debian system DSO FDEs (`libstdc++.so.6`,
     `libc.so.6`, `libgcc_s.so.1`), observed `2026-11-21`.
3. **Pinned Primary Source Citations:**
   - `rust-lang/llvm-project@0a5579eb649d3634a9c30ac873300cc2944fa070`:
     `llvm/lib/CodeGen/ShrinkWrap.cpp:302-381` (`ShrinkWrapImpl::useOrDefCSROrFI`)
     and `834-890` (`ShrinkWrapImpl::performShrinkWrapping` `isEHPad()` save-point
     placement).
   - `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and
     `58cf8f9c35b355199727627d07ae34a4e2846d67`:
     `compiler/rustc_codegen_ssa/src/mir/block.rs:348-395`
     (`codegen_asm_terminator`), `2199-2350` (`landing_pad_for_uncached`,
     `terminate_block`); `library/std/src/sys/personality/dwarf/eh.rs:66-172`
     (`find_eh_action`).
   - `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:
     `src/inline-assembly.md` (`r[asm.rules.unwind]`,
     `r[asm.options.supported-options.nostack]`), `src/items/functions.md`
     (`r[items.fn.extern.unwind]`).
   - `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
     `trusted/lean/Trusted/MirSemantics.lean:602-605` (`TerminalOut`),
     `trusted/audit/TrustedBoundary.lean` (private-level `importModules` +
     `toKernelEnv.replay`).

## Revalidation

1. **Replay the Lean `v4.34.1` mechanization synchronously (`~3.8 s`, zero
   external dependencies):**

   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/dwarf-eh-frame-unwinding-semantics-may-unwind-asm-and-cfi-poisoning/support/DwarfEhFrameUnwindProbe.lean
   ```

   Expected result: exit code `0` with empty stdout and stderr (all `15`
   `#guard_msgs in #print axioms` checks verified by the Lean kernel).

2. **Re-run the live x86-64 PoC A/B/C and DRAP `.eh_frame` reproducer (`~12 s`,
   cleans `/tmp` automatically):**

   ```bash
   python3 -B \
     reports/dwarf-eh-frame-unwinding-semantics-may-unwind-asm-and-cfi-poisoning/support/reproduce_unwind_pocs_and_census.py
   ```

   Discriminating checks to compare against `support/empirical_receipts.json`:
   - `poc_a.a4_sp_mod_16.stdout`: `"sp_mod_16=8"` confirms the LLVM `ShrinkWrap`
     `invoke asm alignstack` bug is still present; `"sp_mod_16=0"` indicates an
     upstream LLVM fix landed (cross-check `ShrinkWrap.cpp::useOrDefCSROrFI` for
     `InlineAsm::Extra_IsAlignStack`).
   - `poc_a.a2_panic` and `poc_b.b5_escape_r12`: `corrupted=true` with `rc=0`
     confirms `catch_unwind` still silently overwrites caller callee-saved
     locals on missing/poisoned register CFI rules.
   - `poc_b.b6_personality` and `poc_b.b7_lsda`: `caught=true drops=0` confirms
     LLVM MC still permits `.cfi_personality` and `.cfi_lsda` inside `asm!` to
     override the enclosing Rust function's unwind metadata.

3. **Validate corpus metadata and structural invariants from the corpus root:**

   ```bash
   python3 tools/reference.py catalog
   python3 tools/reference.py check
   ```
