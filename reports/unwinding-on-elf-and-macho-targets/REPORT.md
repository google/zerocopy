# Unwinding, `.eh_frame` CFI, `.gcc_except_table` LSDAs, and Compact Unwind on ELF and Mach-O Targets

## Summary

A verified drop-in replacement for `rustc` targeting the four ELF and Mach-O Tier 1 platforms (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, and `aarch64-apple-darwin`) must satisfy the following binary, ABI, and runtime invariants for stack unwinding:

1. **DWARF `.eh_frame`, `.eh_frame_hdr`, and `rust_eh_personality` Two-Phase Contract (`library/std/src/sys/personality/gcc.rs:238-279`, `dwarf/eh.rs:66-172`):** On all four targets, `rustc` uses the Itanium C++ ABI Level 1 unwinding interface (`_Unwind_RaiseException`, `_Unwind_Resume`, `_Unwind_DeleteException`, `_Unwind_ForcedUnwind`) with `rust_eh_personality` (`version == 1`). Rust panics allocate a heap `Exception` (`library/panic_unwind/src/gcc.rs:54-73`) carrying `exception_class = u64::from_ne_bytes(*b"MOZ\0RUST")` and a per-`std` `canary: *const u8` (`&CANARY`). Notably, `rust_eh_personality` ignores `_exception_class` completely during both Phase 1 (`_UA_SEARCH_PHASE`) and Phase 2 (`_UA_CLEANUP_PHASE`): any `EHAction::Catch` stops Phase 1 (`_URC_HANDLER_FOUND`) even for foreign C++ exceptions, and foreign-exception rejection occurs only after Phase 2 enters `std::panicking::catch_unwind::cleanup` -> `__rust_panic_cleanup` (`library/panic_unwind/src/gcc.rs:85-108`), which checks `(*exception).exception_class != RUST_EXCEPTION_CLASS` (calling `_Unwind_DeleteException` + `__rust_foreign_exception()`) and `!ptr::eq(canary, &CANARY)`.
2. **`.gcc_except_table` LSDA Encoding and Action Semantics (`llvm/lib/CodeGen/AsmPrinter/EHStreamer.cpp:51-848`):** Every Rust function with cleanup, catch, or `UnwindTerminate` edges emits a Language-Specific Data Area (LSDA) with `lpStartEncoding = DW_EH_PE_omit` (`0xff`), `callSiteEncoding = DW_EH_PE_uleb128` (`0x01`), and sorted `[cs_start, cs_len, cs_lpad, cs_action_entry]` records relative to `func_start`:
   - **No landing pad (`cs_lpad == 0`):** `EHAction::None` (`_URC_CONTINUE_UNWIND` in both phases; used for `_Unwind_Resume` call sites).
   - **Pure cleanup (`cs_lpad != 0, cs_action_entry == 0`):** `EHAction::Cleanup(lpad)` (`_URC_CONTINUE_UNWIND` in Phase 1; `_URC_INSTALL_CONTEXT` in Phase 2, including under `_UA_FORCE_UNWIND`).
   - **Catch all (`cs_action_entry != 0, ttype_index > 0`):** `EHAction::Catch(lpad)` (`_URC_HANDLER_FOUND` in Phase 1; `_URC_INSTALL_CONTEXT` in Phase 2). `rustc`'s `codegen_gnu_try` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:1594-1646`) emits `landingpad { ptr, i32 } catch ptr null`, producing `ttype_index = 1` pointing to a 4-byte `0` NULL typeinfo entry.
   - **No-unwind filter (`cs_action_entry != 0, ttype_index < 0`):** `EHAction::Filter(lpad)`. `rustc`'s `terminate_block` (`compiler/rustc_codegen_ssa/src/mir/block.rs:2344-2351`, `builder.rs:1290-1294`) emits `landingpad { ptr, i32 } filter [0 x ptr] zeroinitializer`, producing `ttype_index = -1` (`0x7f` SLEB128) pointing to a `0x00` empty exception specification. In Phase 1, `rust_eh_personality` returns `_URC_HANDLER_FOUND` (forcing Phase 2 to run inner cleanups even when no `catch_unwind` exists on the stack); in Phase 2, it returns `_URC_CONTINUE_UNWIND` if `_UA_FORCE_UNWIND != 0` (`pthread_exit`), or `_URC_INSTALL_CONTEXT` to invoke `core::panicking::panic_cannot_unwind()`.
   - **Missing call-site range (`ip - 1` not covered by any call-site entry):** `find_eh_action` (`dwarf/eh.rs:121-122`) returns `EHAction::Terminate`, which returns `_URC_FATAL_PHASE1_ERROR` in Phase 1 and `_URC_FATAL_PHASE2_ERROR` in Phase 2.
3. **Behavioral Seam in `extern "C"` Functions with Local Destructors (`compiler/rustc_codegen_ssa/src/mir/block.rs:2187-2199`):** When an `extern "C"` function has no live local drops across an `extern "C-unwind"` call (`c_boundary_no_drop`), the call has `UnwindAction::Terminate(Abi)` (`filter [0 x ptr] zeroinitializer`, `EHAction::Filter`): an uncaught C++ exception stops Phase 1 at the `extern "C"` boundary, runs inner Rust `Drop`s in Phase 2, and aborts in `panic_cannot_unwind` (`exit 134`), while `pthread_exit` (`_UA_FORCE_UNWIND`) cleanly bypasses the filter (`PTHREAD_JOIN_OK drop_log=1`). However, if the `extern "C"` function has a local destructor in scope (`c_boundary_with_drop`), `ElaborateDrops` emits `UnwindAction::Cleanup(bb_cleanup)` ending in `TerminatorKind::UnwindTerminate(Abi)`, which `rustc_codegen_ssa` lowers to `landingpad cleanup` (`cs_action_entry = 0`, `EHAction::Cleanup`) rather than `filter [0 x ptr] zeroinitializer`. Consequently: (a) an uncaught C++ exception returns `_URC_CONTINUE_UNWIND` in Phase 1 and aborts in `__cxa_throw` (`std::terminate`) without running Phase 2 or any inner Rust destructors (`drop_log=0`); and (b) `pthread_exit` (`_UA_FORCE_UNWIND`) fails the `EHAction::Filter` guard at `gcc.rs:263` and enters `bb_cleanup`, aborting the entire process (`panic_cannot_unwind`, `exit 134`).
4. **Darwin `aarch64-apple-darwin` Compact Unwind vs. Asynchronous `uwtable(async)` Fallback (`AArch64AsmBackend.cpp:576-741`, `MCAsmBackend.cpp:123-135`, `lld/MachO/UnwindInfoSection.cpp:350-729`):** Although `aarch64-apple-darwin` uses Mach-O `__LD,__compact_unwind` (linked into `__TEXT,__unwind_info`), two independent LLVM checks force almost all non-leaf Rust functions to fall back to `UNWIND_ARM64_MODE_DWARF` (`0x03000000 | fde_offset`):
   - First, `MCAsmBackend::isDarwinCanonicalPersonality` (`llvm/lib/MC/MCAsmBackend.cpp:123-135`) only accepts `nullptr`, `___gxx_personality_v0`, or `___objc_personality_v0`. Every Rust function with `_rust_eh_personality` is rejected by `generateCompactUnwindEncoding` (`AArch64AsmBackend.cpp:593-595`) and emitted as a DWARF FDE in `__TEXT,__eh_frame`, leaving `Number of personality functions in array: 0x0` in `__TEXT,__unwind_info`.
   - Second, because `rustc` defaults to `uwtable(async)` (`compiler/rustc_codegen_llvm/src/attributes.rs:190-198`), `AArch64FrameLowering` emits epilogue CFI directives (`.cfi_def_cfa wsp, N` and `.cfi_restore`), which `generateCompactUnwindEncoding` (`AArch64AsmBackend.cpp:608, 618`) rejects even for functions without a personality. Thus, in default `rustc` builds on `aarch64-apple-darwin`, only zero-stack frameless leaves get `UNWIND_ARM64_MODE_FRAMELESS` (`0x02000000`); passing `-Z use-sync-unwind=yes` (`uwtable(sync)`) suppresses epilogue CFI and enables `UNWIND_ARM64_MODE_FRAME` (`0x04000000`) for personality-free non-leaf frames.

## Applicability

These findings apply to `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and its bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), as well as `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), across the four ELF and Mach-O Tier 1 targets:
- `x86_64-unknown-linux-gnu`
- `aarch64-unknown-linux-gnu`
- `i686-unknown-linux-gnu`
- `aarch64-apple-darwin`

They govern any compiler backend (`rustc_codegen_llvm`, `rustc_codegen_cranelift`, or a verified native backend) that emits `.eh_frame`, `.eh_frame_hdr`, `.gcc_except_table`, or Mach-O `__compact_unwind` / `__unwind_info` sections to interoperate with `libpanic_unwind`, `std::sys::personality::gcc::rust_eh_personality`, `libgcc_s`, and LLVM/Apple `libunwind`.

## Findings

### 1. Target Unwind Table Defaults and `uwtable` Emission Rules

Basis: source + execution

`Session::must_emit_unwind_tables` (`compiler/rustc_session/src/session.rs:1019-1054`) determines whether every generated function receives the LLVM `uwtable` attribute and module flag (`!("uwtable", i32 2)` for `Async` or `i32 1` for `Sync` in `compiler/rustc_codegen_llvm/src/context.rs:323-340`):

$$\text{must\_emit\_unwind\_tables} = \text{requires\_uwtable} \lor \text{force\_unwind\_tables}.\text{unwrap\_or}(\text{panic\_strategy}.\text{unwinds}() \lor \text{default\_uwtable})$$

| Target Triple | Binary Format | `default-uwtable` | `requires-uwtable` | `eh-frame-header` | Default `-C panic=unwind` | `-C panic=abort` (no `-C force-unwind-tables`) | Exception Return Data Registers (`UNWIND_DATA_REG`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | ELF64 | `true` | `false` | `true` | `uwtable(async)` | `uwtable(async)` (emitted due to `default-uwtable: true`) | `RAX` (DWARF `0`), `RDX` (DWARF `1`) |
| `aarch64-unknown-linux-gnu` | ELF64 | `true` | `false` | `true` | `uwtable(async)` | `uwtable(async)` (emitted due to `default-uwtable: true`) | `X0` (DWARF `0`), `X1` (DWARF `1`) |
| `i686-unknown-linux-gnu` | ELF32 | `true` | `false` | `true` | `uwtable(async)` | `uwtable(async)` (emitted due to `default-uwtable: true`) | `EAX` (DWARF `0`), `EDX` (DWARF `2`) |
| `aarch64-apple-darwin` | Mach-O 64 | `false` | `false` | `false` | `uwtable(async)` | Omitted (`0x00000000` in `__unwind_info` unless `C-unwind` pad present) | `X0` (DWARF `0`), `X1` (DWARF `1`) |

On the three Linux targets, `compiler/rustc_target/src/spec/base/linux.rs:17` sets `default_uwtable: true`, so `.eh_frame` is emitted even under `-C panic=abort` unless `-C force-unwind-tables=no` is explicitly passed. On `aarch64-apple-darwin`, `default_uwtable` is `false`, so `-C panic=abort` omits unwind tables for functions without `extern "C-unwind"` landing pads.

### 2. ELF `.eh_frame`, `.eh_frame_hdr`, and Pointer Encodings

Basis: normative + source + execution

Across the three Linux ELF targets and `aarch64-apple-darwin` (`support/probe_*.s`), LLVM's `MCDwarfFrameEmitter` (`llvm/lib/MC/MCDwarf.cpp:1406-2215`) emits `.eh_frame` with CIE version `1` and the following target-specific parameters:

| Parameter | `x86_64-unknown-linux-gnu` | `aarch64-unknown-linux-gnu` | `i686-unknown-linux-gnu` | `aarch64-apple-darwin` |
| :--- | :--- | :--- | :--- | :--- |
| Code alignment factor | `1` | `1` (or `4` in `ld`) | `1` | `1` |
| Data alignment factor | `-8` | `-8` | `-4` | `-8` |
| Return address column | `16` (`RIP`) | `30` (`X30` / `LR`) | `8` (`EIP`) | `30` (`X30` / `LR`) |
| Initial CFA | `RSP + 8` (`reg7 + 8`) | `SP + 0` (`reg31 + 0`) | `ESP + 4` (`reg4 + 4`) | `SP + 0` (`reg31 + 0`) |
| Augmentation (no LSDA) | `"zR"` | `"zR"` | `"zR"` | `"zR"` (omitted if Compact Unwind fits) |
| Augmentation (with LSDA) | `"zPLR"` | `"zPLR"` | `"zPLR"` | `"zPLR"` |
| Personality encoding (`P`) | `0x9b` (`indirect \| pcrel \| sdata4` via `.data.DW.ref.rust_eh_personality` COMDAT) | `0x9b` (`indirect \| pcrel \| sdata4` via `DW.ref.rust_eh_personality`) | `0x9b` (`indirect \| pcrel \| sdata4` via `DW.ref.rust_eh_personality`) | `0x9b` (`indirect \| pcrel \| sdata4` via `ARM64_RELOC_POINTER_TO_GOT` to `_rust_eh_personality`) |
| LSDA encoding (`L`) | `0x1b` (`pcrel \| sdata4`) | `0x1b` (`pcrel \| sdata4`) | `0x1b` (`pcrel \| sdata4`) | `0x10` (`pcrel \| absptr`, 8-byte signed difference) |
| FDE PC encoding (`R`) | `0x1b` (`pcrel \| sdata4`) | `0x1b` (`pcrel \| sdata4`) | `0x1b` (`pcrel \| sdata4`) | `0x10` (`pcrel \| absptr`, 8-byte signed difference) |

On ELF targets (`eh-frame-header: true`), the linker (`lld/ELF/SyntheticSections.cpp`) constructs `PT_GNU_EH_FRAME` (`.eh_frame_hdr`) with a 4-byte header (`version = 1`, `eh_frame_ptr_enc = 0x1b`, `fde_count_enc = 0x03` (`DW_EH_PE_udata4`), `table_enc = 0x3b` (`DW_EH_PE_datarel | DW_EH_PE_sdata4`)), followed by `eh_frame_ptr`, `fde_count`, and `fde_count` sorted 8-byte pairs `(initial_loc - eh_frame_hdr, fde_addr - eh_frame_hdr)` for $O(\log N)$ binary search via `dl_iterate_phdr`.

### 3. `.gcc_except_table` LSDA Layout and `rust_eh_personality` State Machine

Basis: source + execution

`library/std/src/sys/personality/dwarf/eh.rs:66-172` parses the `.gcc_except_table` (or `__TEXT,__gcc_except_tab` on Mach-O) pointed to by `_Unwind_GetLanguageSpecificData(context)`:

1. **Header:**
   - `start_encoding: u8` (`0xff` = `DW_EH_PE_omit`, so `lpad_base = func_start`).
   - `ttype_encoding: u8` (`0xff` if no type/filter table exists; `0x9b` = `DW_EH_PE_indirect | DW_EH_PE_pcrel | DW_EH_PE_sdata4` when a catch or filter clause exists, followed by `class_info_offset: uleb128`). Note that `eh.rs:84-87` discards the `class_info_offset` value without reading the type table because `rust_eh_personality` distinguishes `Cleanup`, `Catch`, and `Filter` solely by the sign of `ttype_index` in the action record (`eh.rs:162-170`).
   - `call_site_encoding: u8` (`0x01` = `DW_EH_PE_uleb128` on all DWARF CFI targets) and `call_site_table_length: uleb128`.
2. **Lookup IP adjustment (`gcc.rs:356-364`):** `rust_eh_personality` calls `ip = _Unwind_GetIPInfo(context, &mut ip_before_instr)` and queries the call-site table with `ip` if `ip_before_instr != 0` (signal frame) or `ip.wrapping_sub(1)` if `ip_before_instr == 0` (normal call return address, which points 1 byte past the `call`/`bl` instruction).
3. **Call-site table and action interpretation (`eh.rs:97-172`):**
   - If `func_start + cs_start <= query_ip < func_start + cs_start + cs_len`:
     - `cs_lpad == 0` $\implies$ `EHAction::None`.
     - `cs_lpad != 0` and `cs_action_entry == 0` $\implies$ `EHAction::Cleanup(lpad_base + cs_lpad)`.
     - `cs_lpad != 0` and `cs_action_entry > 0` $\implies$ reads `ttype_index: sleb128` at `action_table + (cs_action_entry - 1)`:
       - `ttype_index == 0` $\implies$ `EHAction::Cleanup(lpad)`
       - `ttype_index > 0` $\implies$ `EHAction::Catch(lpad)`
       - `ttype_index < 0` $\implies$ `EHAction::Filter(lpad)`
   - If no call-site entry covers `query_ip`, `find_eh_action` falls through (`eh.rs:122`) and returns `Ok(EHAction::Terminate)`! Thus, any call instruction omitted from the call-site table (such as a `nounwind` call in a function that otherwise has an LSDA) acts as an implicit abort barrier if it unexpectedly unwinds.
   - However, if a function has *no* LSDA (`lsda.is_null()`, `eh.rs:67-69`), `find_eh_action` returns `Ok(EHAction::None)` (`_URC_CONTINUE_UNWIND`), allowing exceptions to unwind transparently through any function that has no personality/LSDA.
4. **Phase 2 Context Installation (`gcc.rs:264-274`):** When installing `lpad`, `rust_eh_personality` sets `UNWIND_DATA_REG.0` to `exception_object`, sets `UNWIND_DATA_REG.1` to `0` (`null`, because generated Rust landing pads ignore the selector value), optionally signs `lpad` with `pacib lpad, sp` on `aarch64` `pauthtest`, calls `_Unwind_SetIP(context, lpad)`, and returns `_URC_INSTALL_CONTEXT`.

### 4. MIR `UnwindAction` Lowering and the `extern "C"` Local-Drop Seam

Basis: source + execution

In `Runtime(PostCleanup)` MIR, every potentially unwinding terminator carries one of four `UnwindAction` variants (`Continue`, `Unreachable`, `Terminate(UnwindTerminateReason)`, `Cleanup(BasicBlock)`), lowered in `compiler/rustc_codegen_ssa/src/mir/block.rs:216-313, 2177-2370`:

| MIR Construct | `rustc_codegen_llvm` Lowering | LSDA Representation | Phase 1 (`_UA_SEARCH_PHASE`) | Phase 2 (`_UA_CLEANUP_PHASE`) | Forced Unwind (`_UA_FORCE_UNWIND`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `UnwindAction::Continue` | Plain `call` (no `invoke`) | If fn has no LSDA: `lsda = 0` (`EHAction::None`). If fn has LSDA: `EHStreamer` emits gap entry `cs_lpad = 0, cs_action = 0` (`EHAction::None`) | `_URC_CONTINUE_UNWIND` | `_URC_CONTINUE_UNWIND` | `_URC_CONTINUE_UNWIND` |
| `UnwindAction::Unreachable` | Plain `call` marked `nounwind` | Omitted from LSDA call-site table (`EHAction::Terminate` if fn has LSDA, else `EHAction::None`) | `_URC_FATAL_PHASE1_ERROR` (if fn has LSDA) | `_URC_FATAL_PHASE2_ERROR` (if fn has LSDA) | `_URC_FATAL_PHASE2_ERROR` (if fn has LSDA) |
| `UnwindAction::Cleanup(bb)` | `invoke ... to label %ret unwind label %cleanup` (`landingpad { ptr, i32 } cleanup`) | `cs_lpad = Lcleanup - Lfunc_begin`, `cs_action_entry = 0` (`EHAction::Cleanup`) | `_URC_CONTINUE_UNWIND` | `_URC_INSTALL_CONTEXT` | `_URC_INSTALL_CONTEXT` |
| `UnwindAction::Terminate(r)` | `invoke ... to label %ret unwind label %terminate` (`landingpad { ptr, i32 } filter [0 x ptr] zeroinitializer`) | `cs_lpad = Lterm - Lfunc_begin`, `cs_action_entry = 1` $\to$ `ttype_index = -1` (`0x7f`), `EHAction::Filter` | `_URC_HANDLER_FOUND` | `_URC_INSTALL_CONTEXT` $\to$ `panic_cannot_unwind` / `panic_in_cleanup` | `_URC_CONTINUE_UNWIND` (`gcc.rs:263`) |
| `TerminatorKind::UnwindResume` | Loads `(exn0, exn1)` from `personality_slot` and emits `resume { ptr, i32 }` $\to$ `call _Unwind_Resume` | Covered by trailing `cs_lpad = 0, cs_action = 0` range | `_URC_CONTINUE_UNWIND` | `_URC_CONTINUE_UNWIND` | `_URC_CONTINUE_UNWIND` |

**Empirical verification of the `extern "C"` local-drop seam (`support/test_seams.rs`, `support/driver.cpp`, `support/driver2.cpp`):**
Running the native `x86_64-unknown-linux-gnu` C++/Rust harness establishes four distinct runtime outcomes:
1. **`cpp_through_c_unwind`:** Throwing `int(42)` from C++ across `extern "C-unwind" fn rust_c_unwind_nested` and `rust_inner_with_drop` into a C++ `try / catch (int)` runs all three Rust `Drop` guards in exact LIFO order (`CAUGHT_CPP=42 drop_log=143`, exit `0`).
2. **`rust_catch_cpp`:** Catching a C++ exception in `std::panic::catch_unwind` stops Phase 1 at `catch_unwind` (`ttype_index = 1`), runs `Guard(1)` in Phase 2, enters `__rust_panic_cleanup` (`library/panic_unwind/src/gcc.rs:88-90`), calls `_Unwind_DeleteException`, and aborts via `__rust_foreign_exception` (`fatal runtime error: Rust cannot catch foreign exceptions, aborting`, exit `134`).
3. **`cpp_no_drop` vs. `cpp_with_drop` (uncaught C++ exception across `extern "C"`):**
   - In `c_boundary_no_drop` (no local drops in the `extern "C"` frame), the call to `rust_inner_with_drop` has `UnwindAction::Terminate(Abi)` $\to$ `EHAction::Filter`. Phase 1 returns `_URC_HANDLER_FOUND`, Phase 2 runs `Guard(1)` in `rust_inner_with_drop`, and `c_boundary_no_drop` aborts via `panic_cannot_unwind` (`exit 134`).
   - In `c_boundary_with_drop` (which holds `let _g = Guard(2)`), the call has `UnwindAction::Cleanup(bb)` $\to$ `landingpad cleanup` (`cs_action_entry = 0`, `EHAction::Cleanup`). With no C++ `catch` higher on the stack, Phase 1 sees `EHAction::Cleanup`, returns `_URC_CONTINUE_UNWIND`, hits `_URC_END_OF_STACK`, and invokes C++ `std::terminate()` in Phase 1 **without running Phase 2 or dropping `Guard(1)` or `Guard(2)`** (`TERMINATE_HANDLER drop_log=0`, exit `99`).
4. **`pthread_no_drop` vs. `pthread_with_drop` (`pthread_exit` forced unwinding across `extern "C"`):**
   - In `c_boundary_no_drop`, `_Unwind_ForcedUnwind` runs `Guard(1)` (`drop_log=1`), matches `EHAction::Filter(_) if actions & _UA_FORCE_UNWIND != 0 => _URC_CONTINUE_UNWIND` (`gcc.rs:263`), and exits the thread cleanly (`PTHREAD_JOIN_OK drop_log=1`).
   - In `c_boundary_with_drop`, because the landing pad is encoded as `EHAction::Cleanup` instead of `EHAction::Filter`, `rust_eh_personality` installs the cleanup pad under `_UA_FORCE_UNWIND`, drops `Guard(2)`, and executes `panic_cannot_unwind`, **aborting the process during `pthread_exit`** (`exit 134`).

### 5. macOS `aarch64-apple-darwin` Compact Unwind (`__unwind_info`) and DWARF Fallback

Basis: source + execution

On `aarch64-apple-darwin`, the object emitter writes 32-byte records (`[range_start: u64, range_length: u32, compact_encoding: u32, personality: u64, lsda: u64]`) into `__LD,__compact_unwind` (`llvm/lib/MC/MCDwarf.cpp:1798-1859`), and the Mach-O linker (`lld/MachO/UnwindInfoSection.cpp:449-728`) folds adjacent identical LSDA-free records and packs them into `__TEXT,__unwind_info` (a version-1 header, common encodings array up to 127 entries, personality GOT offset array up to 3 entries, level-1 page index, LSDA descriptor array, and 4 KiB compressed/regular level-2 pages).

The 32-bit `compact_unwind_encoding_t` for `arm64` (`llvm/lib/Target/AArch64/MCTargetDesc/AArch64AsmBackend.cpp:517-547`) uses mode bits `27:24` (`0x0f000000`):
- `UNWIND_ARM64_MODE_FRAMELESS` (`0x02000000`): leaf or frameless function; bits `23:12` store `(stack_size / 16)`, and bits `11:0` store saved register pair flags (`X19_X20 = 0x1`, `X21_X22 = 0x2`, `X23_X24 = 0x4`, `X25_X26 = 0x8`, `X27_X28 = 0x10`, `D8_D9 = 0x100`, `D10_D11 = 0x200`, `D12_D13 = 0x400`, `D14_D15 = 0x800`).
- `UNWIND_ARM64_MODE_DWARF` (`0x03000000`): low 24 bits (`0x00ffffff`) hold the byte offset of the DWARF FDE in `__TEXT,__eh_frame`.
- `UNWIND_ARM64_MODE_FRAME` (`0x04000000`): standard frame (`stp x29, x30, [sp, #-16]!; mov x29, sp`) with saved register pairs in bits `11:0` contiguous below `x29`.

Linking `support/probe_aarch64-apple-darwin.o` with `rust-lld -flavor darwin` (`support/macho_dylib_unwind.txt`) and comparing default (`uwtable(async)`) against `-Z use-sync-unwind=yes` (`uwtable(sync)`, `support/probe_sync_darwin.s`) proves two critical implementation facts:
1. **`_rust_eh_personality` is never placed in `__unwind_info`'s personality array:** `MCAsmBackend::isDarwinCanonicalPersonality` (`llvm/lib/MC/MCAsmBackend.cpp:123-135`) returns `true` only for `nullptr`, `"___gxx_personality_v0"`, and `"___objc_personality_v0"`. Because `Ctxt->emitCompactUnwindNonCanonical()` defaults to `false`, every Rust function with `_rust_eh_personality` (`_catch_unwind_entry`, `_nested_cleanups`, `_nounwind_c_boundary`) is forced to `UNWIND_ARM64_MODE_DWARF` (`0x03000094`, `0x030000d8`, `0x03000118`), and its personality/LSDA are read from the `__TEXT,__eh_frame` CIE/FDE (`Personality functions: (count = 0)` in `__unwind_info`).
2. **Default `uwtable(async)` defeats `UNWIND_ARM64_MODE_FRAME` on non-leaf functions:** Under default `uwtable(async)`, `AArch64FrameLowering` emits epilogue `.cfi_def_cfa wsp, N` and `.cfi_restore` instructions (`support/probe_aarch64-apple-darwin.s:30-37, 297-328`), which cause `DarwinAArch64AsmBackend::generateCompactUnwindEncoding` (`AArch64AsmBackend.cpp:608, 618`) to bail out to `UNWIND_ARM64_MODE_DWARF` (`0x03000014` for `_passthrough_with_frame`, `0x03000048` for `_simple_nonleaf_call`). When compiled with `-Z use-sync-unwind=yes` (`support/probe_sync_darwin.s`), epilogue CFI is omitted and those exact functions encode as compact `0x04000001` (`UNWIND_ARM64_MODE_FRAME | X19_X20_PAIR`) and `0x04000000` (`UNWIND_ARM64_MODE_FRAME`), with their DWARF FDEs completely omitted from `__TEXT,__eh_frame` (`MCDwarf.cpp:2197-2205`).

### 6. Shrink-Wrapping, Prologue/Epilogue CFI, and `libgcc` vs. LLVM `libunwind`

Basis: source + execution

- **Prologue/epilogue CFI and shrink-wrapping (`llvm/lib/CodeGen/ShrinkWrap.cpp`, `PrologEpilogInserter.cpp`):** On `aarch64-unknown-linux-gnu` and `aarch64-apple-darwin`, when a function has both a normal return epilogue and an out-of-line cleanup landing pad following the epilogue (`support/probe_aarch64-apple-darwin.s:41-62`), LLVM emits `.cfi_remember_state` at the end of the prologue, emits `.cfi_def_cfa wsp, N` + `.cfi_restore` across the epilogue instructions, and emits `.cfi_restore_state` at the start of the landing pad (`LBB2_3`) so the unwinder uses the active frame state inside the landing pad while still having instruction-accurate CFI inside the epilogue. On `x86_64-unknown-linux-gnu` (`support/probe_x86_64-unknown-linux-gnu.s:54-62`), LLVM pops `%rbx`, `%r14`, `%r15` with `.cfi_def_cfa_offset 24, 16, 8` and restores `.cfi_def_cfa_offset 32` at `.LBB2_2` without `.cfi_restore`, because the stack slots still contain the saved register values until overwritten.
- **`libgcc_s` vs. LLVM/Apple `libunwind` (`libunwind/src/UnwindLevel1.c:110-448`):** Both implement the Itanium Level 1 ABI, but differ in four operational details relevant to a verified backend:
  1. **Shadow stack (CET / AArch64 GCS) unwinding (`UnwindLevel1.c:50-91, 221-293`):** LLVM `libunwind` counts `framesWalked` in Phase 2, verifies that the normal stack return address matches the shadow stack entry (`retInNormalStack != retInShadowStack => _URC_FATAL_PHASE2_ERROR`), and pops `framesWalked` shadow-stack frames via `_LIBUNWIND_POP_SHSTK_SSP` before jumping to the landing pad.
  2. **Phase 2 handler frame matching (`UnwindLevel1.c:178-179, 298-315`):** `libunwind` stores the Phase 1 handler frame's `SP` in `exception_object->private_2`, passes `_UA_CLEANUP_PHASE | _UA_HANDLER_FRAME` when `sp == exception_object->private_2`, and aborts immediately (`_LIBUNWIND_ABORT`) if the personality routine returns `_URC_CONTINUE_UNWIND` on that frame in Phase 2.
  3. **macOS `__register_frame` semantics (`compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:285-309`):** On Linux (`libgcc_s`), `__register_frame` takes a pointer to a null-terminated table of FDEs; on macOS (Apple `libunwind`), `__register_frame` registers a single FDE and must be called once per FDE skipping the CIE.
  4. **Validation and verification precedents:** Existing corpus package `compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026` provides an executable Lean 4.34.1 DWARF `.eh_frame` symbolic evaluator and relational verifier (`checkFunctionCFI`, `checkLSDA`) that checks CFA/register restoration invariants and detected the `rustc_codegen_cranelift` `UnwindAction::Terminate` bug (`compiler/rustc_codegen_cranelift/src/abi/mod.rs:901`, still present in `1.99.1`, where `UnwindAction::Terminate` is tagged with `EXCEPTION_HANDLER_CLEANUP = 0` instead of a negative `ttype_index` filter).

## Boundaries

- **32-bit ARM EHABI (`arm-unknown-linux-gnueabihf`) and Darwin SjLj (`armv7-apple-ios`):** Inspected in source (`library/std/src/sys/personality/gcc.rs:97-205` and `dwarf/eh.rs:57-65, 123-145`), where ARM EHABI requires the personality routine itself to step frames via `__gnu_unwind_frame` and stash `exception_object` in `r12` (`UNWIND_POINTER_REG`), but not executed as they are outside the 8 Tier 1 targets.
- **Native macOS execution of the linked `aarch64-apple-darwin` dylib:** The `aarch64-apple-darwin` object and Mach-O `.dylib` were compiled with `rustc 1.99.1` and linked with `rust-lld -flavor darwin` on Linux x86_64 to verify exact `__LD,__compact_unwind`, `__TEXT,__unwind_info`, and `__TEXT,__eh_frame` generation without accepting the proprietary Xcode SDK license; native macOS execution of `extern "C-unwind"` assembly frames is already preserved in `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`.

## Evidence

### Primary Upstream Sources

- `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):
  - `library/std/src/sys/personality/gcc.rs:51-91, 207-370` (`UNWIND_DATA_REG`, `rust_eh_personality_impl`, `rust_eh_personality`, `find_eh_action`).
  - `library/std/src/sys/personality/dwarf/eh.rs:19-271` (`find_eh_action`, `interpret_cs_action`, `read_encoded_offset`, `read_encoded_pointer`).
  - `library/panic_unwind/src/gcc.rs:48-112` (`CANARY`, `Exception`, `panic`, `cleanup`, `RUST_EXCEPTION_CLASS`).
  - `library/std/src/panicking.rs:544-601` (`catch_unwind`, `cleanup`, `do_call`, `do_catch`).
  - `compiler/rustc_codegen_llvm/src/intrinsic.rs:1336-1355, 1594-1713` (`catch_unwind_intrinsic`, `codegen_gnu_try`, `get_rust_try_fn`).
  - `compiler/rustc_codegen_llvm/src/builder.rs:1275-1304` (`cleanup_landing_pad`, `filter_landing_pad`, `resume`).
  - `compiler/rustc_codegen_llvm/src/attributes.rs:190-198, 501-503` (`uwtable_attr`).
  - `compiler/rustc_session/src/session.rs:1019-1054` (`must_emit_unwind_tables`).
  - `compiler/rustc_codegen_ssa/src/mir/block.rs:216-313, 395-406, 2177-2370` (`do_call`, `codegen_resume_terminator`, `landing_pad_for_uncached`, `terminate_block`).
  - `compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:18-240` and `gcc_except_table.rs:1-244`.
- `rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`LLVM 23.1.1`):
  - `llvm/lib/CodeGen/AsmPrinter/EHStreamer.cpp:51-848` (`computeActionsTable`, `computeCallSiteTable`, `emitExceptionTable`, `emitTypeInfos`).
  - `llvm/lib/MC/MCAsmBackend.cpp:123-135` (`isDarwinCanonicalPersonality`).
  - `llvm/lib/MC/MCDwarf.cpp:1798-1859, 2142-2215` (`EmitCompactUnwind`, `MCDwarfFrameEmitter::emit`).
  - `llvm/lib/Target/AArch64/MCTargetDesc/AArch64AsmBackend.cpp:514-741` (`generateCompactUnwindEncoding`).
  - `lld/MachO/UnwindInfoSection.cpp:101-732` (`UnwindInfoSectionImpl::finalize`, `writeTo`).
  - `libunwind/src/UnwindLevel1.c:110-448` (`unwind_phase1`, `unwind_phase2`, `unwind_phase2_forced`).
  - `libunwind/src/CompactUnwinder.hpp:494-705` (`CompactUnwinder_arm64`).

### Preserved Package Support Artifacts

- `support/unwind_probe.rs`, `support/probe_x86_64-unknown-linux-gnu.s`, `support/probe_aarch64-unknown-linux-gnu.s`, `support/probe_i686-unknown-linux-gnu.s`, `support/probe_aarch64-apple-darwin.s`, `support/probe_sync_darwin.s`: Cross-target assembly and unwind tables for frameless leaves, passthrough frames, nested cleanups, `extern "C"` boundaries, and `catch_unwind`.
- `support/macho_stubs.rs` and `support/macho_dylib_unwind.txt`: Standalone Mach-O `arm64` dynamic library linked via `rust-lld -flavor darwin` and decoded `llvm-objdump --unwind-info --dwarf=frames` output.
- `support/test_seams.rs`, `support/driver.cpp`, `support/driver2.cpp`: Executable C++/Rust/pthreads reproducers demonstrating C++ exceptions crossing `C-unwind`, foreign-exception abort in `catch_unwind`, and the `extern "C"` local-drop Phase 1 / `pthread_exit` seam.
- `support/decode_unwind_tables.py`: Standalone Python decoder for `.gcc_except_table` LSDAs and Compact Unwind / ARM64 unwind words.

## Revalidation

```bash
# 1. Run the standalone LSDA decoder self-test
python3 reports/unwinding-on-elf-and-macho-targets/support/decode_unwind_tables.py

# 2. Recompile and execute the C++/Rust/pthread_exit unwinding seam suite on x86_64-unknown-linux-gnu
rustc +1.99.1-x86_64-unknown-linux-gnu --edition=2021 --crate-type=staticlib -C opt-level=2 \
  reports/unwinding-on-elf-and-macho-targets/support/test_seams.rs -o /tmp/libtest_seams.a
g++ -O2 reports/unwinding-on-elf-and-macho-targets/support/driver.cpp /tmp/libtest_seams.a -lpthread -ldl -o /tmp/test_seams_bin
/tmp/test_seams_bin pthread_no_drop
/tmp/test_seams_bin cpp_with_drop || true
```
