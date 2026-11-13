# Unwinding on Windows Targets: x64/ARM64 `.pdata`/`.xdata`, `__CxxFrameHandler3`, `x86_64-pc-windows-gnu` Hybrid SEH, and 32-Bit `fs:[0]` SEH

## Summary

A verified drop-in replacement for `rustc` targeting the four Windows Tier 1 platforms (`x86_64-pc-windows-msvc`, `aarch64-pc-windows-msvc`, `i686-pc-windows-msvc`, and `x86_64-pc-windows-gnu`) must implement three distinct unwinding architectures and binary table formats:

1. **Table-Based `__CxxFrameHandler3` Funclets on `x86_64-pc-windows-msvc` and `aarch64-pc-windows-msvc` (`library/panic_unwind/src/seh.rs:55-387`, `compiler/rustc_codegen_llvm/src/intrinsic.rs:1364-1509`, `WinException.cpp:665-954`):** On all three MSVC targets, `requires-uwtable` is `true`, and `panic_unwind` throws a stack-allocated `Exception { canary: &raw const TYPE_DESCRIPTOR, data: Option<Box<dyn Any + Send>> }` via `_CxxThrowException` using an unmangled `TYPE_NAME = *b"rust_panic\0"`. Unlike Itanium DWARF landing pads, MSVC unwinding executes cleanup and catch funclets (`?dtor$N@...`, `?catch$N@...`) *on top of the throwing stack frame* while the unwinder holds the parent frame's establisher pointer (`RDX` on x64, `X29` on ARM64). Every parent function and catch funclet emits a `.pdata` `RUNTIME_FUNCTION` entry pointing to `.xdata` `UNWIND_INFO` with handler `__CxxFrameHandler3` and a 4-byte `@IMGREL` pointer to the parent's 40-byte `$cppxdata$<fn>` (`FuncInfo`, magic `0x19930522`), which indexes `$stateUnwindMap$`, `$tryMap$`, `$handlerMap$`, and `$ip2state$`.
2. **Hybrid SEH Frame Unwinding + GCC `.gcc_except_table` LSDA on `x86_64-pc-windows-gnu` (`library/std/src/sys/personality/gcc.rs:282-313`):** On 64-bit MinGW (`x86_64-pc-windows-gnu`), frame unwinding uses standard Windows x64 `.pdata` (`RUNTIME_FUNCTION`) and `.xdata` (`UNWIND_INFO`), NOT `.eh_frame`. However, `rustc` uses LLVM's `landingpad` / `resume` IR rather than funclets: the `.xdata` handler is `rust_eh_personality`, which immediately delegates to `libgcc`'s `_GCC_specific_handler(exceptionRecord, establisherFrame, contextRecord, dispatcherContext, rust_eh_personality_impl)`, and the language-specific data immediately following the `rust_eh_personality@IMGREL` word inside `.xdata` is a standard DWARF `.gcc_except_table` (`GCC_except_tableN`) parsed by `dwarf/eh.rs`.
3. **Frame-Based `fs:[0]` SEH and SafeSEH on `i686-pc-windows-msvc` (`X86WinEHState.cpp:246-450`, `WinException.cpp:48-54, 665-899`):** 32-bit Windows x86 does not use `.pdata` or PC-range tables. Instead, LLVM's `X86WinEHStatePass` allocates a 16-byte `CXXExceptionRegistration { void *SavedESP; EHRegistrationNode SubRecord; int32_t TryLevel; }` on the stack at `[ebp - 28 .. ebp - 16]` (plus an extra `[ebp - 40]` catch-object slot when `catchpad` is present), links `SubRecord` (`[ebp - 24]`) into the TEB `fs:[0]` exception list in the prologue, unlinks it before every `retl`, and inserts explicit `movl $state, -16(%ebp)` stores before every potentially throwing call. Each function with EH pads emits a 10-byte per-function thunk `___ehhandler$<fn>` (`movl $L__ehtable$<fn>, %eax; jmp ___CxxFrameHandler3`) and registers that thunk's symbol index in `.sxdata` via `.safeseh` alongside `@feat.00 = 1` so `link.exe /SAFESEH` (passed by default in `i686-pc-windows-msvc` `pre-link-args`) succeeds.
4. **Verification Scope for 32-Bit SEH:** Verifying 32-bit SEH requires proving five dynamic machine-state invariants that have no counterpart in table-based 64-bit unwinding: (a) strict LIFO `fs:[0]` registration/unregistration across all normal and exceptional exits (preventing dangling stack-frame nodes in `TEB.NtTib.ExceptionList`), (b) dominance and liveness of explicit `[ebp - 16]` `TryLevel` state-number stores across all call edges, (c) `SavedESP` (`[ebp - 28]`) maintenance across dynamic `alloca` / `inalloca` adjustments, (d) the `[ebp + 12]` establisher-frame pointer arithmetic shared between parent frames and outlined `?dtor$`/`?catch$` funclets, and (e) COFF `.sxdata` / `@feat.00 = 1` SafeSEH handler-table completeness.

## Applicability

These findings apply to `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and its bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), as well as `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), across the four Windows Tier 1 targets:
- `x86_64-pc-windows-msvc`
- `aarch64-pc-windows-msvc`
- `i686-pc-windows-msvc`
- `x86_64-pc-windows-gnu`

Note that `rustc_codegen_cranelift` (`compiler/rustc_codegen_cranelift/src/lib.rs:277-280`) explicitly rejects `PanicStrategy::Unwind` on all Windows targets (`"panic=unwind is not supported on Windows"`), so LLVM is currently the only reference implementation of Windows unwinding in the `rust-lang/rust` tree.

## Findings

### 1. Target Unwind Architecture Matrix Across Windows Tier 1

Basis: source + execution

All four Windows Tier 1 target specifications (`compiler/rustc_target/src/spec/base/{windows_msvc.rs,windows_gnu.rs}`) set `requires_uwtable: true`. Consequently, `Session::must_emit_unwind_tables` (`compiler/rustc_session/src/session.rs:1019-1054`) returns `true` even under `-C panic=abort` and `-C force-unwind-tables=no`.

| Property | `x86_64-pc-windows-msvc` | `aarch64-pc-windows-msvc` | `i686-pc-windows-msvc` | `x86_64-pc-windows-gnu` |
| :--- | :--- | :--- | :--- | :--- |
| Frame unwind mechanism | `.pdata` (`RUNTIME_FUNCTION`, 12 B) + `.xdata` (`UNWIND_INFO`) | `.pdata` (8 B, packed or `.xdata` ref) + `.xdata` (ARM64 `ExceptionData`) | Active stack `fs:[0]` `CXXExceptionRegistration` linked list | `.pdata` (`RUNTIME_FUNCTION`, 12 B) + `.xdata` (`UNWIND_INFO`) |
| IR EH representation | Funclets (`cleanuppad`, `catchswitch`, `catchpad`, `cleanupret`, `catchret`) | Funclets (`cleanuppad`, `catchswitch`, `catchpad`, `cleanupret`, `catchret`) | Funclets + `X86WinEHStatePass` (`fs:[0]` + `TryLevel` stores) | Itanium-style `landingpad` + `resume` (`_Unwind_Resume`) |
| Personality routine | `__CxxFrameHandler3` | `__CxxFrameHandler3` | `___ehhandler$<fn>` thunk $\to$ `___CxxFrameHandler3` | `rust_eh_personality` $\to$ `_GCC_specific_handler` |
| LSDA / handler table | 40-byte `$cppxdata$<fn>` (`FuncInfo`, `@IMGREL` refs, `IPToStateMap`) | 40-byte `$cppxdata$<fn>` (`FuncInfo`, `@IMGREL` refs, `IPToStateMap`) | 36-byte `L__ehtable$<fn>` (`FuncInfo`, VA32 refs, no `IPToStateMap` or `UnwindHelp`) | `.gcc_except_table` (`GCC_except_tableN`) inside `.xdata` |
| SafeSEH (`@feat.00` / `.sxdata`) | `@feat.00 = 0` | `"@feat.00" = 0` | `@feat.00 = 1` + `.safeseh ___ehhandler$<fn>` in `.sxdata` | `@feat.00 = 0` |
| Panic throw mechanism | `_CxxThrowException` (`library/panic_unwind/src/seh.rs`) | `_CxxThrowException` (`library/panic_unwind/src/seh.rs`) | `_CxxThrowException` (`thiscall` cleanup/copy) | `_Unwind_RaiseException` (`library/panic_unwind/src/gcc.rs`) |

### 2. x64 `.pdata` and `.xdata` Format (`x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu`)

Basis: normative + source + execution

In `llvm/include/llvm/Support/Win64EH.h:28-235` and `llvm/lib/MC/MCWin64EH.cpp`, each non-leaf x64 function (and each outlined x64 funclet on MSVC) emits a 12-byte `RUNTIME_FUNCTION` entry in `.pdata`:

```c
struct RuntimeFunction {
    uint32_t StartAddress;     // IMAGE_REL_AMD64_ADDR32NB (.text start)
    uint32_t EndAddress;       // IMAGE_REL_AMD64_ADDR32NB (.text end)
    uint32_t UnwindInfoOffset; // IMAGE_REL_AMD64_ADDR32NB (.xdata)
};
```

Frameless leaf functions that do not adjust `RSP` or save nonvolatile registers (`DropTracker::drop`, `frameless_leaf`, `passthrough_no_cleanup` in `support/probe_x86_64-pc-windows-msvc.s:16-24, 328-331, 519-520`) emit no `.seh_proc` directives and no `.pdata` entry; the Windows x64 unwinder unwinds any PC not covered by `.pdata` by dereferencing `[RSP]` as the return address and setting `RSP += 8`.

The `.xdata` `UNWIND_INFO` structure (`Win64EH.h:169-234`) has a 4-byte header followed by an array of 2-byte `UnwindCode` slots (sorted in descending order of prologue offset so the unwinder can undo operations in reverse):
- Byte 0: `Version : 3` (`1`, or `2` with `UOP_Epilog`), `Flags : 5` (`UNW_ExceptionHandler = 0x01`, `UNW_TerminateHandler = 0x02`, `UNW_ChainInfo = 0x04`). When a personality handler is present (`Flags = 0x03`), a 4-byte padding-aligned `@IMGREL` handler RVA and language-specific handler data follow `UnwindCodes[(NumCodes + 1) & ~1]`.
- Byte 1: `PrologSize` in bytes.
- Byte 2: `NumCodes` (count of 2-byte `UnwindCode` slots).
- Byte 3: `FrameRegister : 4` (`0` = none, `5` = `RBP`), `FrameOffset : 4` (scaled by 16 bytes; e.g., `leaq 64(%rsp), %rbp` in `catch_unwind_entry` encodes `FrameRegister = 5, FrameOffset = 4`, i.e., `0x45`).
- `UnwindCodes` (`Win64EH.h:30-45`, `support/readobj_x86_64-pc-windows-msvc.txt:421-625`):
  - `UWOP_PUSH_NONVOL` (`0`): `OpInfo` = register number (`RBX=3, RBP=5, RSI=6, RDI=7, R12..R15=12..15`), 1 slot.
  - `UWOP_ALLOC_LARGE` (`1`): `OpInfo = 0` $\implies$ next 1 slot is `size / 8`; `OpInfo = 1` $\implies$ next 2 slots are unscaled 32-bit byte size.
  - `UWOP_ALLOC_SMALL` (`2`): `size = OpInfo * 8 + 8` (`8..128` bytes), 1 slot.
  - `UWOP_SET_FPREG` (`3`): establishes frame pointer `FP = RSP + FrameOffset * 16`, 1 slot.
  - `UWOP_SAVE_NONVOL` (`4`) / `UWOP_SAVE_NONVOL_FAR` (`5`): saves GPR at scaled (`* 8`, 2 slots) or unscaled 32-bit (3 slots) offset.
  - `UWOP_SAVE_XMM128` (`8`) / `UWOP_SAVE_XMM128_FAR` (`9`): saves 128-bit `XMM6..XMM15` at scaled (`* 16`, 2 slots) or unscaled 32-bit (3 slots) offset.

### 3. ARM64 Windows `.pdata` and `.xdata` Format (`aarch64-pc-windows-msvc`)

Basis: normative + source + execution

On `aarch64-pc-windows-msvc` (`llvm/lib/MC/MCWin64EH.cpp`, `support/probe_aarch64-pc-windows-msvc.s`, `support/readobj_aarch64-pc-windows-msvc.txt:414-636`), every `.pdata` entry is 8 bytes:
- Word 0: `FunctionStart` (`IMAGE_REL_ARM64_ADDR32NB`).
- Word 1: Either packed unwind data (low 2 bits `Flag = 1` or `2` when no exception handler is present and the prologue/epilogue are canonical) or `ExceptionRecord` RVA in `.xdata` (`Flag = 0`, bit `[1:0] == 0b00`).

In `.xdata` (`readobj_aarch64-pc-windows-msvc.txt:418-635`), the ARM64 `ExceptionData` header encodes `FunctionLength` (in 4-byte instructions, bits `17:0`), `Version` (`0`, bits `19:18`), `X` (`ExceptionData` present bit `20`), `E` (`EpiloguePacked` bit `21`), `EpilogueCount` / `EpilogueOffset` (bits `26:22`), and `CodeWords` (bits `31:27`), followed by variable-length big-endian unwind bytecodes executed from top of prologue/epilogue:
- `0x00..0x3f` (`alloc_s`): `sub sp, sp, #(N * 16)` (e.g., `0x03` = `sub sp, #48`; `0x04` = `sub sp, #64`).
- `0x40..0x7f` (`save_fplr`): `stp x29, x30, [sp, #(N * 8)]` (e.g., `0x42` = `stp x29, x30, [sp, #16]`; `0x44` = `stp x29, x30, [sp, #32]`).
- `0x80..0xbf` (`save_fplr_x`): `stp x29, x30, [sp, #-(N + 1) * 8]!` (e.g., `0x81` = `stp x29, x30, [sp, #-16]!`, used by every outlined funclet in `probe_aarch64-pc-windows-msvc.s:92-199`).
- `0xe1` (`set_fp`): `mov x29, sp`.
- `0xe2, imm8` (`add_fp`): `add x29, sp, #(imm8 * 8)` (e.g., `0xe2 0x02` = `add fp, sp, #16`; `0xe2 0x04` = `add fp, sp, #32`).
- `0xe4` (`end`): end of unwind bytecode sequence.
- When `EpiloguePacked = Yes` (`nested_cleanups` in `readobj_aarch64-pc-windows-msvc.txt:555-568`), the epilogue reuses the tail of the prologue bytecode array starting at `EpilogueOffset = 2` (`0x44; 0x04; 0xe4` $\to$ `ldp x29, x30, [sp, #32]; add sp, #64; end`). When `EpiloguePacked = No` (`catch_unwind_entry`, lines `422-441`), explicit 4-byte `EpilogueScope` descriptors (`StartOffset`, `EpilogueStartIndex`) precede the bytecode array.

### 4. MSVC `panic_unwind`, Funclets, and `__CxxFrameHandler3` Tables

Basis: source + execution

#### 4.1 Throwing Rust Panics via `_CxxThrowException` (`library/panic_unwind/src/seh.rs:55-387`)
1. `Exception` layout (`seh.rs:56-66`): `#[repr(C)] struct Exception { canary: *const _TypeDescriptor, data: Option<Box<dyn Any + Send>> }` (24 bytes on 64-bit, 12 bytes on 32-bit). Because MSVC runs filter and cleanup funclets *before* unwinding the throwing stack frame, `throw_exception` allocates `Exception` directly on the stack of `throw_exception` (`let mut exception = ManuallyDrop::new(...)`) without an extra heap allocation (`seh.rs:308-316`).
2. `_ThrowInfo` and `__ImageBase`-relative pointers (`seh.rs:111-255, 338-369`): On 32-bit x86, `_ThrowInfo`, `_CatchableTypeArray`, and `_CatchableType` contain raw 32-bit pointers (`*mut u8`). On 64-bit x64 and ARM64, those fields are 32-bit RVAs (`u32`) relative to `__ImageBase`. Because Rust `static` initializers cannot subtract `&raw const __ImageBase` at compile time, `throw_exception` lazily writes the 5 `u32` offsets (`THROW_INFO.pmfnUnwind = exception_cleanup`, `pCatchableTypeArray`, `arrayOfCatchableTypes[0]`, `CATCHABLE_TYPE.pType = TYPE_DESCRIPTOR`, `copyFunction = exception_copy`) using `atomic_store::<_, SeqCst>` before calling `_CxxThrowException`.
3. Calling convention difference (`seh.rs:273-299`): On 32-bit x86, `exception_cleanup` (`extern "thiscall"`) and `exception_copy` (`extern "thiscall-unwind"`) use `thiscall` (`ECX` = `this`), whereas on 64-bit they use `"C"` / `"C-unwind"`.

#### 4.2 Funclet Lowering and `codegen_msvc_try` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:1364-1509`)
When lowering `catch_unwind`, `codegen_msvc_try` generates an internal `__rust_try` shim (inlineable into `catch_unwind_entry`) with two `catchpad` handlers on a single `catchswitch`:
1. `catchpad within %cs [&__rust_panic_type_info, i32 8, %slot]`: catches `rust_panic` by reference (`HT_IsReference = 8`) into stack slot `%slot`, loads `%ptr = load ptr, ptr %slot`, and calls `std::panicking::catch_unwind::cleanup(%ptr)`.
2. `catchpad within %cs [ptr null, i32 64, ptr null]`: catches any foreign C++ exception (`HT_IsStdDotDot = 64`), and calls `catch_unwind::cleanup(null)`, which sees `payload.is_null()` (`seh.rs:376-378`) and aborts via `__rust_foreign_exception()`.

Because `catch_unwind::cleanup` is itself invoked inside a `catchpad` funclet and cannot unwind (`UnwindAction::Terminate`), `rustc` wraps the call to `catch_unwind::cleanup` inside an inner `catchswitch` with `[null, 64, null]` (`?catch$3` and `?catch$6` on x64 in `support/probe_x86_64-pc-windows-msvc.s:90-160`), which calls `core::panicking::panic_cannot_unwind()`.

#### 4.3 Funclet Calling Convention and `$cppxdata$` (`FuncInfo`) Layout (`WinException.cpp:665-954`)
In `support/probe_x86_64-pc-windows-msvc.s` and `support/probe_aarch64-pc-windows-msvc.s`:
- **Cleanup funclets (`?dtor$N@...`):** Called by `__CxxFrameHandler3` during Phase 2 unwinding with the parent frame's establisher pointer in `RDX` (x64, where `EstablisherFrame = RSP_after_prologue`, so the funclet reconstructs `leaq 80(%rdx), %rbp` in `nested_cleanups` line `386`) or `X29` (ARM64, where `X29` already holds the parent's `FP`), and return via a normal `ret`. Cleanup funclets have `Flags = 0` in their `UNWIND_INFO` (`WinException.cpp:231-237`).
- **Catch funclets (`?catch$N@...`):** Called by `__CxxFrameHandler3` with the parent establisher pointer in `RDX` (x64) or `X29` (ARM64), execute the catch body, and return the continuation address in `RAX` / `X0` (`leaq .LBB1_9(%rip), %rax` on x64 line `129`; `adrp x0, .LBB1_3; add x0, x0, .LBB1_3` on ARM64 line `119`). The unwinder then unwinds the stack to the parent frame and jumps to the returned continuation address (marked with the `$ehgcr_1_9:` / `$ehgcr_1_3:` garbage-collection root symbol).
- **The `$cppxdata$<fn>` (`FuncInfo`) table (`WinException.cpp:713-899`, decoded by `support/decode_windows_eh.py`):**

| Offset (64-bit / 32-bit) | Field | Value in `catch_unwind_entry` (`probe_x86_64-pc-windows-msvc.s:229-319`) | Meaning |
| :--- | :--- | :--- | :--- |
| `+0` / `+0` | `MagicNumber` | `429065506` (`0x19930522`) | VC++8 (`__CxxFrameHandler3`) magic with `bbtFlags = 0` |
| `+4` / `+4` | `MaxState` | `7` | Number of states in `$stateUnwindMap$` (`0..6`) |
| `+8` / `+8` | `UnwindMap` | `$stateUnwindMap$@IMGREL` (VA32 on i686) | Array of `MaxState` `(int32_t ToState, ActionRVA)` pairs |
| `+12` / `+12` | `NumTryBlocks` | `3` | Number of `TryBlockMapEntry` records (`0` = outer `catch_unwind`, `1..2` = abort guards inside catch pads) |
| `+16` / `+16` | `TryBlockMap` | `$tryMap$@IMGREL` (VA32 on i686) | Array of `(TryLow, TryHigh, CatchHigh, NumCatches, HandlerArray)` (20 B each). Stored in pre-order (outer first) on 64-bit and post-order (inner first) on 32-bit (`WinEHPrepare.cpp:405-440`)! |
| `+20` / `+20` | `IPMapEntries` | `12` (`0` on i686) | Number of `(IP@IMGREL, int32_t State)` entries |
| `+24` / `+24` | `IPToStateMap` | `$ip2state$@IMGREL` (`0` on i686) | Sorted PC-to-state table (starts at `.Lfunc_begin0 -> -1`) |
| `+28` / (omitted on i686) | `UnwindHelp` | `48` on x64 (`-16(%rbp)`), `-16` on ARM64 (`[x29, #16]`) | Signed offset from establisher frame (`RSP` on x64, `FP` on ARM64) to the 8-byte stack slot initialized to `-2` (`movq $-2, -16(%rbp)`) used by `__CxxFrameHandler3` to track active unwind state |
| `+32` / `+28` | `ESTypeList` | `0` | Unused C++98 dynamic exception specification list |
| `+36` / `+32` | `EHFlags` | `1` (`FI_EHS_FLAG`) | Synchronous exceptions only (`1` unless `"eh-asynch"` module flag is set) |

Each `HandlerType` entry in `$handlerMap$` is 20 bytes on x64/ARM64 (`[Adjectives, Type@IMGREL, CatchObjOffset, Handler@IMGREL, ParentFrameOffset]`) and 16 bytes on i686 (omitting `ParentFrameOffset`).

### 5. `x86_64-pc-windows-gnu`: Hybrid SEH `.pdata`/`.xdata` with `.gcc_except_table`

Basis: source + execution

Inspecting `support/probe_x86_64-pc-windows-gnu.s:39-149` and `support/readobj_x86_64-pc-windows-gnu.txt:114-196` reveals how `x86_64-pc-windows-gnu` bridges Windows x64 SEH and Itanium DWARF LSDAs:
1. Every non-leaf function uses `.seh_proc`, `.seh_pushreg`, `.seh_stackalloc`, and `.seh_endprologue` to emit standard Windows x64 `.pdata` (`RUNTIME_FUNCTION`) and `.xdata` (`UNWIND_INFO`).
2. Instead of funclets or `__CxxFrameHandler3`, functions with landing pads emit `.seh_handler rust_eh_personality, @unwind, @except`, followed at the end of the function by `.seh_handlerdata`, `.text`, `.seh_endproc`, and `.section .xdata,"dr"` containing `GCC_except_tableN:`.
3. Because `.seh_handlerdata` switches the assembler to `.xdata` and emits the `UNWIND_INFO` header, unwind codes, and the 4-byte `IMAGE_REL_AMD64_ADDR32NB` relocation for `rust_eh_personality`, placing `.section .xdata,"dr"` with `GCC_except_tableN` immediately afterward lays out the DWARF LSDA directly at `UnwindInfo::getExceptionData()` (`DispatcherContext->HandlerData`).
4. At runtime, the Windows x64 OS unwinder (`RtlDispatchException` / `RtlUnwindEx`) invokes `rust_eh_personality(exceptionRecord, establisherFrame, contextRecord, dispatcherContext)` (`library/std/src/sys/personality/gcc.rs:294-311`), which tail-calls `libgcc`'s `_GCC_specific_handler(..., rust_eh_personality_impl)`. `_GCC_specific_handler` translates the Windows SEH two-pass dispatch into Itanium Level 1 calls (`_UA_SEARCH_PHASE` / `_UA_CLEANUP_PHASE`), sets `_Unwind_GetLanguageSpecificData(context)` to `DispatcherContext->HandlerData` (`GCC_except_tableN`), and installs landing-pad context with `RAX` = exception object and `RDX` = `0`. Landing pads resume unwinding by calling `_Unwind_Resume(%rcx)` (`probe_x86_64-pc-windows-gnu.s:101-102`).

### 6. 32-Bit x86 Frame-Based SEH (`i686-pc-windows-msvc`) and Verification Requirements

Basis: source + execution

#### 6.1 Concrete Prologue, State Numbering, and Epilogue (`support/probe_i686-pc-windows-msvc.s:33-65, 277-351`)
In `X86WinEHState.cpp:265-450`, `WinEHStateFnPassImpl` rewrites every function with `__CxxFrameHandler3` EH pads to maintain a stack-allocated `CXXExceptionRegistration` linked into `fs:[0]`. In `_nested_cleanups` (`probe_i686-pc-windows-msvc.s:277-314`):

```gas
_nested_cleanups:
    pushl   %ebp
    movl    %esp, %ebp
    pushl   %ebx                # [ebp - 4]
    pushl   %edi                # [ebp - 8]
    pushl   %esi                # [ebp - 12]  <-- 3 callee-saved GPRs always pushed!
    subl    $32, %esp
    movl    %esp, -28(%ebp)     # RegNode.SavedESP = esp (at [ebp - 28])
    movl    $-1, -16(%ebp)      # RegNode.TryLevel = -1  (at [ebp - 16])
    movl    $___ehhandler$nested_cleanups, -20(%ebp) # SubRecord.Handler (at [ebp - 20])
    leal    -24(%ebp), %ecx     # &RegNode.SubRecord     (at [ebp - 24])
    movl    %fs:0, %edx
    movl    %edx, -24(%ebp)     # SubRecord.Next = fs:[0]
    movl    %ecx, %fs:0         # fs:[0] = &RegNode.SubRecord
    ...
    movl    $0, -16(%ebp)       # Transition to TryLevel = 0 before call
    calll   *12(%ebp)
    ...
    movl    -24(%ebp), %eax     # Epilogue: unlink RegNode from fs:[0]
    movl    %eax, %fs:0
    addl    $32, %esp
    popl    %esi
    popl    %edi
    popl    %ebx
    popl    %ebp
    retl
```

Key architectural invariants of 32-bit `i686-pc-windows-msvc` SEH:
1. **Fixed `[ebp - 28 .. ebp - 16]` layout and mandatory `EBX`/`EDI`/`ESI` saves:** Every function using 32-bit MSVC EH pushes `EBP`, `EBX`, `EDI`, `ESI` (`[ebp - 4 .. ebp - 12]`) and places `CXXExceptionRegistration` immediately below them at `[ebp - 28 .. ebp - 16]`:
   - `[ebp - 28]`: `void *SavedESP`
   - `[ebp - 24]`: `EHRegistrationNode *Next` (the address registered in `fs:[0]`)
   - `[ebp - 20]`: `PEXCEPTION_ROUTINE Handler` (`$___ehhandler$<fn>`)
   - `[ebp - 16]`: `int32_t TryLevel` (initialized to `-1` before linking into `fs:[0]`)
2. **`[ebp + 12]` Establisher Pointer Adjustment in Outlined Funclets (`probe_i686-pc-windows-msvc.s:67-71, 105-108, 321-325`):** When the OS invokes `___ehhandler$<fn>`, `EstablisherFrame` is `&RegNode.SubRecord` = `ebp_parent - 24`. `__CxxFrameHandler3` sets `EBP = EstablisherFrame + 12 = ebp_parent - 12` before calling any `?dtor$` or `?catch$` funclet. Therefore, every outlined funclet begins with:
   ```gas
   pushl %ebp
   subl  $12, %esp     # (or pushl %eax in dtor)
   addl  $12, %ebp     # Reconstructs exact parent EBP!
   ```
   And when a `?catch$` funclet returns a continuation label (`movl $LBB1_6, %eax`), `LBB1_6` in the parent function must also execute `addl $12, %ebp; jmp LBB1_11` (`probe_i686-pc-windows-msvc.s:66-71`) because `__CxxFrameHandler3` jumps to the continuation target with `EBP = EstablisherFrame + 12`!
3. **SafeSEH (`.sxdata`, `@feat.00 = 1`, `/SAFESEH`):** On 32-bit x86 (`X86AsmBackend.cpp`, `WinException.cpp:48-54`), LLVM sets bit 0 of the absolute symbol `@feat.00 = 1` (`probe_i686-pc-windows-msvc.s:6`) to declare the object SafeSEH-compliant, and emits `.safeseh ___ehhandler$<fn>` for every generated handler thunk (`lines 476-478`). The assembler writes the 4-byte COFF symbol table indices (`10, 11, 12`) into the `.sxdata` section (`readobj_i686-pc-windows-msvc.txt:755-779`), which `link.exe /SAFESEH` (enabled by default in `compiler/rustc_target/src/spec/targets/i686_pc_windows_msvc.rs`, `tier1_target_specs_1991.txt:229`) sorts into the PE Load Config `SEHandlerTable`. If any object file lacks `@feat.00 & 1` or omits a handler from `.sxdata`, `link.exe /SAFESEH` refuses to link the binary.

#### 6.2 What Verifying 32-Bit Frame-Based SEH Would Require
Compared to 64-bit table-based unwinding (where unwind metadata in `.pdata`/`.xdata` is read-only static data and zero extra instructions execute on the non-throwing path), verifying 32-bit `i686-pc-windows-msvc` frame-based SEH in a verified compiler backend requires:
1. **Explicit TEB `fs:[0]` Ghost State in the Machine Semantics:** The operational semantics of `i386` must model the thread-local segment base `FS` (`TEB.NtTib.ExceptionList` at `fs:[0]`) as a mutable memory cell pointing to an acyclic stack-ordered linked list of active `EHRegistrationNode` frames.
2. **Prologue/Epilogue List-Maintenance Proofs:** Every function that installs `[ebp - 24]` into `fs:[0]` must prove that (a) `TryLevel` (`[ebp - 16]`) is initialized to `-1` *before* `movl %ecx, %fs:0` (so an asynchronous fault or stack-probe fault cannot observe an uninitialized `TryLevel`), and (b) every normal return path (`retl` or `musttail`) restores `fs:[0] = [ebp - 24]` *before* deallocating the stack frame (`addl $N, %esp; popl ...`). Failure to unlink before `retl` leaves `fs:[0]` pointing into deallocated stack memory, causing immediate arbitrary code execution on the next exception.
3. **Flow-Sensitive `TryLevel` Store Verification:** Instead of verifying a static PC-range map (`$ip2state$`), the backend must verify a dataflow invariant over the CFG: at every call instruction that is not proven `nounwind`, the memory slot `[ebp - 16]` holds the exact state integer `s` corresponding to the call's `UnwindAction` in `$stateUnwindMap$` and `$tryMap$` (where `$tryMap$` on 32-bit x86 must be emitted in **post-order**, inner try blocks before outer try blocks, opposite to 64-bit pre-order; `WinEHPrepare.cpp:409-439`).
4. **Funclet Frame-Pointer Shift (`ebp + 12`) and `SavedESP` (`[ebp - 28]`) Verification:** Every outlined `?dtor$` and `?catch$` funclet, and every `$ehgcr_` catch continuation block, must be verified under a entry precondition where `EBP_in = EBP_parent - 12`, proving that `addl $12, %ebp` recovers `EBP_parent` and that `movl %esp, -28(%ebp)` keeps `SavedESP` synchronized before any call inside a catch funclet or dynamic stack allocation.
5. **COFF `.sxdata` and `@feat.00` Emission Proof:** The object emitter must prove that `@feat.00` has bit `0` set (`1`) and that every symbol stored into `[ebp - 20]` (`___ehhandler$<fn>`) has its COFF symbol index emitted into `.sxdata`.

## Boundaries

- **Native Windows and Wine execution of the cross-compiled COFF objects:** Neither native Windows nor `wine` is installed on the Linux verification host (`which wine` returns `1`), and downloading the proprietary MSVC CRT / Windows SDK via `xwin --accept-license` is prohibited by license guardrails. All four Windows Tier 1 targets were compiled to LLVM IR (`.ll`), assembly (`.s`), and COFF objects (`.o`) using `rustc 1.99.1` and decoded with `llvm-readobj --unwind --sections --relocations --symbols` (`support/readobj_*.txt`) and `support/decode_windows_eh.py`.
- **Windows x64 Unwind Info Version 3 (`UNWIND_INFO` V3 / APX):** Inspected in `llvm/include/llvm/Support/Win64EH.h:236-322` (`DecodedUnwindInfoV3`), but `rustc 1.99.1` emits `UNWIND_INFO` Version 1 on `x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu`.

## Evidence

### Primary Upstream Sources

- `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):
  - `library/panic_unwind/src/seh.rs:55-387` (`Exception`, `ptr_t`, `_ThrowInfo`, `_CatchableTypeArray`, `_CatchableType`, `_TypeDescriptor`, `exception_cleanup`, `exception_copy`, `throw_exception`, `cleanup`).
  - `library/std/src/sys/personality/gcc.rs:282-313` (`rust_eh_personality` $\to$ `_GCC_specific_handler` on `x86_64` / `aarch64` `windows-gnu`).
  - `compiler/rustc_codegen_llvm/src/intrinsic.rs:1357-1509` (`codegen_msvc_try`, `__rust_panic_type_info`).
  - `compiler/rustc_codegen_llvm/src/builder.rs:1244-1305` (`cleanup_pad`, `catch_switch`, `catch_pad`, `cleanup_ret`, `catch_ret`).
  - `compiler/rustc_codegen_cranelift/src/lib.rs:277-280` (Cranelift rejection of `panic=unwind` on Windows).
- `rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`LLVM 23.1.1`):
  - `llvm/include/llvm/Support/Win64EH.h:28-235` (`UnwindOpcodes`, `UnwindCode`, `RuntimeFunction`, `UnwindInfo`).
  - `llvm/include/llvm/CodeGen/WinEHFuncInfo.h:40-136` (`CxxUnwindMapEntry`, `SEHUnwindMapEntry`, `WinEHHandlerType`, `WinEHTryBlockMapEntry`, `WinEHFuncInfo`).
  - `llvm/lib/CodeGen/WinEHPrepare.cpp:131-638` (`WinEHPrepareImpl`, `calculateCXXStateNumbers`, pre-order vs. post-order `TryBlockMap` on 64-bit vs. 32-bit, `colorFunclets`).
  - `llvm/lib/CodeGen/AsmPrinter/WinException.cpp:35-62, 170-307, 556-1076` (`endModule` `.safeseh`, `beginFunclet`, `endFuncletImpl`, `emitCSpecificHandlerTable`, `emitCXXFrameHandler3Table`, `computeIP2StateTable`, `emitExceptHandlerTable`).
  - `llvm/lib/Target/X86/X86WinEHState.cpp:188-450` (`CXXExceptionRegistration`, `SEHExceptionRegistration`, `emitExceptionRegistrationRecord`, `generateLSDAInEAXThunk`, `addStateStores`).
  - `llvm/lib/MC/MCWin64EH.cpp:1-1200` (x64 and ARM64 `.pdata`/`.xdata` binary emission).

### Preserved Package Support Artifacts

- `support/unwind_probe.rs`: Rust probe covering frameless leaves, passthrough frames, nested `Drop` cleanups, `extern "C"` boundaries, and `catch_unwind`.
- `support/probe_x86_64-pc-windows-msvc.s`, `support/probe_aarch64-pc-windows-msvc.s`, `support/probe_i686-pc-windows-msvc.s`, `support/probe_x86_64-pc-windows-gnu.s`: Generated assembly for all four Windows Tier 1 targets.
- `support/readobj_x86_64-pc-windows-msvc.txt`, `support/readobj_aarch64-pc-windows-msvc.txt`, `support/readobj_i686-pc-windows-msvc.txt`, `support/readobj_x86_64-pc-windows-gnu.txt`: Full `llvm-readobj --unwind --sections --relocations --symbols` dumps of the compiled COFF object files.
- `support/decode_windows_eh.py`: Standalone Python decoder for x64 `UNWIND_INFO` and `__CxxFrameHandler3` `FuncInfo` headers.

## Revalidation

```bash
# 1. Run the standalone Windows x64 UNWIND_INFO and FuncInfo decoder
python3 reports/unwinding-on-windows-targets-and-32bit-seh/support/decode_windows_eh.py

# 2. Recompile unwind_probe.rs for all four Windows Tier 1 targets and inspect COFF unwind info
for t in x86_64-pc-windows-msvc aarch64-pc-windows-msvc i686-pc-windows-msvc x86_64-pc-windows-gnu; do
  rustc +1.99.1-x86_64-unknown-linux-gnu --target "$t" --edition=2021 --crate-type=rlib -C opt-level=2 \
    --emit=obj="/tmp/probe_${t}.o" \
    reports/unwinding-on-windows-targets-and-32bit-seh/support/unwind_probe.rs
  "$(rustc +1.99.1-x86_64-unknown-linux-gnu --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-readobj" \
    --unwind "/tmp/probe_${t}.o" | head -n 45
done
```
