# End-to-End Post-Link `FnAbi`, Drop Elaboration, DWARF LSDA Unwinding, and `-static-pie` Seam Analysis (`GNU ld` vs. `rust-lld`)

## Summary

`Basis: execution + source + normative + derived`

Verifying a multi-crate Rust executable end-to-end cannot decompose cleanly into independent per-pass proofs over `FnAbi` call lowering, `ElaborateDrops` MIR cleanup ladders, LLVM `.gcc_except_table` / `.eh_frame` emission, and ELF64 static linking, because soundness at run time depends on **four cross-layer invariants that span all four components simultaneously**. By auditing upstream `rust-lang/rust`, `rust-lang/llvm-project` / `llvm/llvm-project`, and `joshlf/anneal` at immutable 40-hex commits, executing a live multi-crate dual-linker matrix (`GNU ld 2.47` vs. bundled `rust-lld 22.1.6`) across `84` `std` unwind runs, `8` double-panic abort subprocesses, and `6` freestanding `#![no_std]` `-static-pie` executables ([probe_postlink_abi_unwind_crucible.py](support/probe_postlink_abi_unwind_crucible.py)), and mechanizing the composed 4-layer pipeline with sharpness counterexamples in synchronous kernel-checked `Lean v4.34.1` ([PostLinkAbiDropUnwindCrucible.lean](support/PostLinkAbiDropUnwindCrucible.lean)), we establish six core findings:

1. **Cross-crate `FnAbi` × `ElaborateDrops` `sret` unwind invariant (`PassMode::Direct`, `Pair`, `Cast`, `Indirect`):** Across `crate_callee` (`.rlib`) and `crate_caller` (`bin`), `PassMode::Direct` (`i64` in `%rdi`/`%rax`), `PassMode::Pair` (`16`-byte niche `Option<(NonZeroU64, u64)>` as `{ i64, i64 }` in `%rdi, %rsi` / `%rax, %rdx`), `PassMode::Cast` (`12`-byte `#[repr(C)] MixedCast12` under `extern "C-unwind"` as `{ i64, float }` in `%rdi, %xmm0` / `%rax, %xmm0`), and `PassMode::Indirect { on_stack: false }` (`>16`-byte `Drop` struct via caller-allocated `ptr sret([56 x i8]) align 8` in `%rdi`) produce identical outcomes and destructor traces across all `4` linker/optimization configurations (`21/21` scenarios each). Crucially, `ElaborateDrops::drop_flags_for_fn_rets` (`elaborate_drops.rs:433-451`) sets the return place's boolean drop flag to `true` **only** at the start of the normal `target` basic block when `unwind` is `UnwindAction::Cleanup(_)`, preventing the caller's landing pad from dropping an uninitialized `sret` stack slot when the callee panics before writing `*sret`.
2. **Trailing `noreturn` calls (`NoTrapAfterNoreturn = true`) and the `ret_rip - 1` FDE/LSDA boundary hazard:** On `x86_64-unknown-linux-gnu`, `rustc` sets `Options.TrapUnreachable = true` together with `Options.NoTrapAfterNoreturn = true` (`PassWrapper.cpp:377-397`). Consequently, **`284 / 798` (`35.6%`)** of linked FDEs at `-O0` (`252 / 581` = `43.4%` at `-O2`) end with a `5`- or `6`-byte `call` instruction at the literal final byte of the FDE (`ret_rip == fde_pc_end`) with **zero** trailing `ud2` or `nop`. In **`60` FDEs (`GNU ld`) and `61` FDEs (`rust-lld`)**, `fde_pc_end == next_fde.pc_begin` (`0` alignment bytes), so unadjusted `ret_rip` resolves in `.eh_frame_hdr` binary search to the **next function's FDE**; on non-16-byte-aligned ends, `ret_rip` lands in `GNU ld`'s multi-byte `NOP` sleds (`1,167` `nop`, `0` `int3`) or `rust-lld`'s `0xCC` trap padding (`5,322` `int3` at `-O0`, `3,596` at `-O2`), outside every FDE. Even *within* a single function, naive `ret_rip` misclassifies `.gcc_except_table` LSDA actions on **`74 / 132` (`56.1%`)** probe calls at `-O0` (`7 / 19` at `-O2`)—including dispatching a panicking constructor `DropToken::new` directly into the `Cleanup` landing pad that drops the not-yet-constructed local (`caller_stack_clash_loop_unwind+0x4e`, `ret_rip = 0x11684 == cs_1.start`). Subtracting `1` (`gcc.rs:333`: `ip.wrapping_sub(1)`) achieves **`132 / 132` (`100%`)** FDE and LSDA accuracy iff every unwinding call encodes `call_len >= 1` inside `[cs_start, cs_start + cs_len)`.
3. **Two-tier `#![no_std]` `-static-pie` `SIGSEGV` across crate boundaries (`GNU ld` vs. `rust-lld`):** Because `x86_64_unknown_linux_gnu` sets `plt_by_default = false` (`RtLibUseGOT = 1`) and `relax_elf_relocations = false`, cross-crate references emit legacy `R_X86_64_GOTPCREL`. In freestanding `#![no_std] #![no_main] -nostdlib -static-pie` builds without a `_DYNAMIC` `R_X86_64_RELATIVE` self-relocator:
   - An **inlined cross-crate `static` data load** (`48 8b`, `R_X86_64_GOTPCREL`) is relaxed by `GNU ld 2.47` to `lea` (`48 8d 05 f8 0f 00 00`, `0` dynamic relocs, **`EXIT_OK = 0`**), whereas `rust-lld 22.1.6` (`X86_64.cpp:958-989`) refuses to relax non-`X` `R_X86_64_GOTPCREL`, leaving `mov` reading an unrelocated `.got` slot (`R_X86_64_RELATIVE: 1`) and crashing with **`SIGSEGV` (`rc = -11`)**.
   - A **non-inlined cross-crate function call** emits `ff 15` (`call *callee@GOTPCREL(%rip)`) with legacy `R_X86_64_GOTPCREL`, which **neither `GNU ld 2.47` nor `rust-lld 22.1.6` can relax** (x86-64 psABI requires `R_X86_64_GOTPCRELX` to rewrite `ff 15 -> 67 e8`), causing **`SIGSEGV` (`rc = -11`) on both linkers** until `-Z relax-elf-relocations=yes` upgrades the call relocation to `R_X86_64_GOTPCRELX` (`67 e8 17 00 00 00` `addr32 call`, `0` dynamic relocs, **`EXIT_OK = 0` on both linkers**).
4. **Double-panic observable divergence between `DropStyle::Static` and `DropStyle::Open`:** During cross-crate unwind, `UnwindAction::Terminate(Reason::InCleanup)` lowers via `FunctionCx::terminate_block` (`block.rs:2077-2101`) to an LLVM `landingpad ... filter [0 x ptr] zeroinitializer` (`ttype_index = -1` in `.gcc_except_table`, decoded as `EHAction::Filter(lpad)` in `dwarf/eh.rs:168-170`) calling `core::panicking::panic_in_cleanup` (`SIGABRT`, `rc = -6`). When field `f0` of a 3-field struct panics during cross-crate unwind:
   - **`Static` drop (`caller_double_panic_static`):** `crate_caller`'s cleanup pad invokes `drop_in_place::<TripleFields>` (`shim.rs:379-402`), whose body starts outside cleanup mode and builds an internal cleanup half-ladder; **`f1` and `f2` both run to completion** before `_Unwind_Resume` hits `crate_caller`'s `filter` pad and aborts.
   - **`Open` drop (`caller_double_panic_open`, after moving `f2`):** `ElaborateDrops` expands the remaining fields inline inside `crate_caller`'s cleanup block (`data.is_cleanup = true`, `elaborate_drops.rs:361`), attaching `UnwindAction::Terminate(Reason::InCleanup)` directly to `f0`'s `drop` invoke; `f0`'s panic **aborts immediately without executing sibling `f1`**.
5. **Inline `4096`-byte stack-clash probe loop asynchronous DWARF CFA accuracy (`>32 KiB` frames):** For frames exceeding `ProbeChunk = 8 * 4096 = 32,768` B (`caller_stack_clash_loop_unwind`, `41,500`-byte buffer), `X86FrameLowering::emitStackProbeInlineGenericLoop` (`X86FrameLowering.cpp:788-942`) computes `%r11 = %rsp - 0xa000` (`40,960` B) and switches `.eh_frame` to `DW_CFA_def_cfa_register: r11` (`CFA = r11 + 40968` at `-O0`, `r11 + 40984` at `-O2`) across every instruction of the `sub $0x1000, %rsp; movq $0, (%rsp); cmp %r11, %rsp; jne` loop, then executes the non-page-multiple remainder `sub $0x268, %rsp` (`-O0`) / `sub $0x248, %rsp` (`-O2`) while CFA is still anchored on `%r11`, and atomically restores `CFA = rsp + 41584` (`-O0`) / `rsp + 41568` (`-O2`) on the next instruction boundary—maintaining exact `entry_rsp + 8` CFA invariance with zero single-instruction gap.
6. **Clean kernel-checked `Lean v4.34.1` composition & counterexample proof (`0` `sorry`, `0` `._unsafe_rec`) and Anneal TCB gap:** [PostLinkAbiDropUnwindCrucible.lean](support/PostLinkAbiDropUnwindCrucible.lean) (`1,106` lines, `51` source definitions/types, `21` theorems; `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec` across all `781` compiled `.olean` constants) proves `endToEnd_fourLayer_seam_preservation`, `stackClashInlineLoop_async_cfa_exact`, and sharpness counterexamples `CE1`–`CE3` in `13.314s` (`541.24 MiB` max RSS). At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst.TerminatorKind` maps `Drop` and `UnwindTerminate` to `.unsupported`, and `Trusted.MirSemantics.evalTerminator` faults `.unsupported` on `.call`, `.unwindResume`, and `cleanup = true` returns.

---

## Applicability

`Basis: source + execution`

**Examined subjects and how they relate:**

- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `x86_64-unknown-linux-gnu`):** The exact compiler binary and sysroot used for all multi-crate `.rlib`/binary builds, `-Z dump-mir=ElaborateDrops` dumps, `--emit=llvm-ir` signatures, and native runs, as well as all `compiler/` and `library/` primary-source citations.
- **`rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` (`LLVM / LLD 22.1.6`):** The exact `src/llvm-project` submodule pinned by `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and reported verbatim by bundled `rust-lld -flavor gnu --version`; cross-checked against upstream release tag `llvm/llvm-project@fc4aad7b5db3fff421df9a9637605b9ca5667881` (`llvmorg-22.1.6`).
- **`GNU ld (GNU Binutils for Debian) 2.47`:** Host system BFD ELF64 x86-64 linker compared head-to-head against bundled `rust-lld 22.1.6`. Note that because `x86_64-unknown-linux-gnu` defaults to `LinkerFlavor::Gnu(Cc::Yes, Lld::Yes)` (`compiler/rustc_target/src/spec/base/linux_gnu.rs:9`), passing `-Clink-self-contained=-linker` alone still passes `-fuse-ld=lld` to `cc` and fails when system `ld.lld` is absent; selecting `GNU ld` requires `-Clinker-flavor=gnu-cc -Zunstable-options -Clink-self-contained=-linker`.
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`Lean v4.34.1`) & `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:** Used to kernel-check [PostLinkAbiDropUnwindCrucible.lean](support/PostLinkAbiDropUnwindCrucible.lean) under synchronous kernel checking (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and audit current `Trusted.MirAst` / `Trusted.MirSemantics` / `TrustedBoundary` coverage.

**Configuration scope:**

- Multi-crate `std` specimens ([crate_callee.rs](support/specimens/crate_callee.rs), [crate_caller.rs](support/specimens/crate_caller.rs)) were compiled and executed under `-C panic=unwind` across `4` build profiles: `{GNU ld 2.47, rust-lld 22.1.6} × {(-C opt-level=0, default relax_elf_relocations=false), (-C opt-level=2, -Z relax-elf-relocations=yes)}`.
- Multi-crate freestanding `#![no_std] #![no_main]` specimens ([nostd_callee.rs](support/specimens/nostd_callee.rs), [nostd_caller.rs](support/specimens/nostd_caller.rs)) were compiled with `-C opt-level=2 -C panic=abort -C relocation-model=pie -C link-arg=-nostdlib -C link-arg=-static-pie` across `6` profiles covering `{inline data load, non-inlined cross-crate call} × {GNU ld 2.47, rust-lld 22.1.6} × {default, -Z relax-elf-relocations=yes}`.
- Exact byte layouts, register assignments (`%rdi`, `%rsi`, `%rax`, `%rdx`, `%xmm0`, `%r11`, `%rsp`), relocation numbers (`R_X86_64_*`), and `.eh_frame_hdr` / `.gcc_except_table` encodings apply specifically to `x86_64-unknown-linux-gnu` ELF64. MIR-level `ElaborateDrops` flag placement (`drop_flags_for_fn_rets`) and `Static` vs. `Open` cleanup-block semantics are target-independent in `rustc_mir_transform`.

---

## Findings

### 1. Four-Layer Upstream Architecture & Seam Contracts

`Basis: source + normative`

Direct inspection of `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` establishes how each layer produces obligations consumed downstream:

1. **Cross-crate `FnAbi` classification (`rustc_target` & `rustc_ty_utils`):**
   - `compiler/rustc_target/src/callconv/mod.rs:39-74` defines `PassMode::{Ignore, Direct, Pair, Cast, Indirect { attrs, meta_attrs, on_stack }}`.
   - `compiler/rustc_ty_utils/src/abi.rs:615-644` dispatches rustic ABIs (`extern "Rust"`) to `FnAbi::adjust_for_rust_abi` (`callconv/mod.rs:717-848`) and foreign ABIs (`extern "C"`, `extern "C-unwind"`) to `FnAbi::adjust_for_foreign_abi` -> `x86_64::compute_abi_info` (`compiler/rustc_target/src/callconv/x86_64.rs:178-265`).
   - Crucially, `adjust_for_rust_abi` (`callconv/mod.rs:745-816`) casts `BackendRepr::Memory` aggregates only when `size <= Pointer.size` (`8` B on x86-64) and forces `PassMode::Indirect { on_stack: false }` (`sret`) for any non-SIMD return `> 16` B, while keeping `BackendRepr::ScalarPair` in `PassMode::Pair`. Conversely, `extern "C-unwind"` runs full System V eightbyte classification (`x86_64.rs:29-173`), lowering a `12`-byte mixed integer/float struct (`{ u32, u32, f32 }`) to `PassMode::Cast` (`CastTarget::pair(Reg::i64(), Reg::f32())` in `%rdi, %xmm0` -> `%rax, %xmm0`) while keeping `fn_abi.can_unwind = true` (`abi.rs:601-606`).
2. **`ElaborateDrops` return-flag timing & `Static` vs. `Open` cleanup ladders (`rustc_mir_transform`):**
   - In `compiler/rustc_mir_transform/src/elaborate_drops.rs:433-451`, `drop_flags_for_fn_rets` iterates over `TerminatorKind::Call { destination, target: Some(tgt), unwind: UnwindAction::Cleanup(_), .. }` and inserts `set_drop_flag(Location { block: tgt, statement_index: 0 }, child, DropFlagState::Present)` **strictly at entry to `tgt`**, whereas lines `503-518` mark `destination` initialized *before* the call only when `unwind` is `Continue | Unreachable | Terminate(_)`.
   - At `rustc_codegen_ssa/src/mir/block.rs:239-268, 2126-2214`, `make_return_dest` passes `dest.val.llval` as the hidden `sret` pointer argument `%rdi` *before* `bx.invoke(...)`, while `store_return` runs only inside `fx.llbb(target)`. If the callee unwinds before writing `*sret`, `tgt` is bypassed; `drop_flags_for_fn_rets` is the exact invariant preventing the caller's cleanup block from dropping uninitialized `sret` stack bytes.
   - For aggregate cleanup, `DropStyle::Static` lowers to a single `drop(_local)` call targeting `InstanceKind::DropGlue`, synthesized by `build_drop_shim` (`compiler/rustc_mir_transform/src/shim.rs:379-402`) with **`Unwind::To(resume_block)`**—giving `drop_in_place::<T>` its *own* internal cleanup half-ladder (`elaborate_drop.rs:675-716`). By contrast, when any subpath of a local has been moved out (`DropStyle::Open`) and the enclosing drop sits on an unwind path (`data.is_cleanup == true`), `elaborate_drops.rs:361` passes **`Unwind::InCleanup`** directly to `open_drop`, omitting any sibling half-ladder and stamping `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)` onto every open-dropped field call site.
3. **`invoke` / `filter_landing_pad` lowering, `NoTrapAfterNoreturn`, and LSDA `ip - 1` lookup (`rustc_codegen_ssa`, `std`, & LLVM):**
   - `compiler/rustc_codegen_ssa/src/mir/block.rs:217-231, 1945-2103` lowers `UnwindAction::Terminate(reason)` on Linux ELF into an `invoke` targeting a cached `"terminate"` block containing `bx.filter_landing_pad(llpersonality)` (`compiler/rustc_codegen_llvm/src/builder.rs:1219-1223`: `landingpad { ptr, i32 } filter [0 x ptr] zeroinitializer`) followed by a call to `core::panicking::panic_in_cleanup` (`library/core/src/panicking.rs:233`).
   - `llvm/lib/CodeGen/AsmPrinter/EHStreamer.cpp:209-355` emits `.gcc_except_table` sorted `[cs_start, cs_start + cs_len)` ranges; an empty `filter` clause emits an action-table entry with `ttype_index = -1`.
   - At run time, `library/std/src/sys/personality/gcc.rs:323-339` queries `_Unwind_GetIPInfo(context, &mut ip_before_instr)` and computes `ip: if ip_before_instr != 0 { ip } else { ip.wrapping_sub(1) }`. `library/std/src/sys/personality/dwarf/eh.rs:99-172` scans `[func_start + cs_start, func_start + cs_start + cs_len)`, mapping `cs_lpad == 0` to `EHAction::None`, `cs_action == 0` (or `ttype_index == 0`) to `EHAction::Cleanup(lpad)`, `ttype_index > 0` to `EHAction::Catch(lpad)`, `ttype_index < 0` to `EHAction::Filter(lpad)` (installed directly by `gcc.rs:235-244`, executing `panic_in_cleanup`), and any table gap to `EHAction::Terminate`.
   - Crucially, `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:377-397` sets `Options.TrapUnreachable = true` **and** `Options.NoTrapAfterNoreturn = true` on all non-Wasm, non-Windows targets (explicitly noting at `L389-393` that Windows keeps post-noreturn traps only because SEH `.pdata` `RtlLookupFunctionEntry` lacks DWARF's `ip - 1` adjustment). On ELF x86-64, `SelectionDAGBuilder.cpp:3665-3671` therefore suppresses `ud2` after every `noreturn` call.

---

### 2. Multi-Crate `FnAbi` × `ElaborateDrops` Execution & Double-Panic Divergence

`Basis: execution + source`

Running [probe_postlink_abi_unwind_crucible.py](support/probe_postlink_abi_unwind_crucible.py) compiles `crate_callee.rs` (`rlib`) + `crate_caller.rs` (`bin`) across all `4` `std` build configurations (`gnu_ld_default`, `rust_lld_default`, `gnu_ld_relax_o2`, `rust_lld_relax_o2`). LLVM IR emission (`crate_callee.ll`) confirms the exact lowered cross-crate signatures:

```llvm
define i64 @callee_direct(i64 %x, i1 zeroext %should_panic) unnamed_addr #4 personality ptr @rust_eh_personality
define { i64, i64 } @callee_pair_niche(i64 %0, i64 %1, i1 zeroext %should_panic) unnamed_addr #4 personality ptr @rust_eh_personality
define { i64, float } @callee_cast_12({ i64, float } %0, i1 zeroext %should_panic) unnamed_addr #4 personality ptr @rust_eh_personality
define void @callee_indirect_sret(ptr sret([56 x i8]) align 8 %_0, i64 %seed, i1 zeroext %should_panic) unnamed_addr #4 personality ptr @rust_eh_personality
define void @callee_noreturn_panic(i64 %0) unnamed_addr #5 personality ptr @rust_eh_personality
```

Across all `4` configurations (`4 × 21 = 84` single-process runs), scenario outputs and destructor traces are **bit-for-bit identical** (`all_4_std_configs_identical_scenarios = true`):

| Cross-Crate `PassMode` Case | `cond_move` | `callee_panics` | Observed Outcome | Exact Post-Call Destructor Sequence (`crate_callee` -> `crate_caller`) |
| :--- | :--- | :--- | :--- | :--- |
| `Direct` (`u64`) | `false` / `true` | `false` | `ok:58` | `callee_direct_guard` -> `open_0`, `open_2`, `[cond_0 if !cm]`, `static_0`, `static_1` |
| `Direct` (`u64`) | `false` / `true` | `true` | `unwound` | `callee_direct_guard` -> `open_0`, `open_2`, `[cond_0 if !cm]`, `static_0`, `static_1` |
| `Pair` (`Option<(NonZeroU64, u64)>`) | `false` / `true` | `false` | `ok:618` | `callee_pair_guard` -> `open_0`, `open_2`, `[cond_0 if !cm]`, `static_0`, `static_1` |
| `Pair` (`Option<(NonZeroU64, u64)>`) | `false` / `true` | `true` | `unwound` | `callee_pair_guard` -> `open_0`, `open_2`, `[cond_0 if !cm]`, `static_0`, `static_1` |
| `Cast` (`MixedCast12`, `C-unwind`) | `false` / `true` | `false` | `ok:43` | `callee_cast12_guard` -> `open_0`, `open_2`, `[cond_0 if !cm]`, `static_0`, `static_1` |
| `Cast` (`MixedCast12`, `C-unwind`) | `false` / `true` | `true` | `unwound` | `callee_cast12_guard` -> `open_0`, `open_2`, `[cond_0 if !cm]`, `static_0`, `static_1` |
| `Indirect` (`BigSretDrop`, `sret`) | `false` / `true` | `false` | `ok:2011` | `callee_sret_guard` -> **`sret_ret_token`** -> `open_0`, `open_2`, `[cond_0 if !cm]`, `static_0`, `static_1` |
| `Indirect` (`BigSretDrop`, `sret`) | `false` / `true` | `true` | `unwound` | `callee_sret_guard` -> *(no `sret_ret_token`!)* -> `open_0`, `open_2`, `[cond_0 if !cm]`, `static_0`, `static_1` |

#### Double-Panic `Static` vs. `Open` Subprocess Comparison

Post-`ElaborateDrops` MIR (`2-2-004.ElaborateDrops.after.mir`) shows `caller_double_panic_static` has `4` cleanup basic blocks and `3` `unwind terminate(cleanup)` edges, whereas `caller_double_panic_open` (which moves `triple.f2` before the call) expands to `11` cleanup basic blocks and `6` `unwind terminate(cleanup)` edges. Executing both modes as isolated subprocesses across all `4` linked binaries (`8/8` runs) yields an invariant observable split before `SIGABRT` (`returncode = -6`, `"panic in a destructor during cleanup"` at `library/core/src/panicking.rs:233:5`):

| Subprocess Mode | Pre-Call Drop | Unwind Drops Executed Before `SIGABRT` (`-6`) | Sibling `f1` Executed? |
| :--- | :--- | :--- | :--- |
| `double_panic_static` (`DropStyle::Static`) | *(none)* | `callee_direct_guard` -> `dp_static_f0_bomb` -> **`dp_static_f1_sibling` -> `dp_static_f2_sibling`** | **Yes (`f1` and `f2` both run inside `drop_in_place`)** |
| `double_panic_open` (`DropStyle::Open`) | `dp_open_f2_moved` | `callee_direct_guard` -> `dp_open_f0_bomb` *(immediate `filter_landing_pad` abort)* | **No (`f1` skipped)** |

---

### 3. Post-Link ELF64 Layout, LSDA Call-Site Containment, & Trailing `noreturn` Off-By-One

`Basis: execution + source + normative`

Inspecting all `4` linked `std` binaries via [probe_postlink_abi_unwind_crucible.py](support/probe_postlink_abi_unwind_crucible.py) (`readelf -rW`, `objdump -d`, and direct binary decoding of `.eh_frame_hdr`, `.eh_frame`, and `.gcc_except_table`) establishes exact post-link invariants and linker differences:

| Build Configuration | Compile+Link (s) | Binary Size (B) | `.text` VA | `.eh_frame_hdr` VA / FDEs / Key Sign | `.text` Padding (`int3` / `nop`) | Probe `call` `ret_rip - 1` FDE Match | Naive `ret_rip` FDE Fail / LSDA Mismatch | Binary-Wide FDEs Ending at `call` (`gap == 0`) |
| :--- | ---: | ---: | :--- | :--- | :--- | ---: | ---: | ---: |
| `gnu_ld_default` (`-O0`) | `0.719` | `4,433,864` | `0x6070` | `0x57be0` / `798` / `798 neg, 0 pos` | `0` / `1,167` | **`132 / 132`** | `11` / **`74`** | **`284`** (**`60`** zero-gap) |
| `rust_lld_default` (`-O0`) | `0.470` | `4,478,048` | `0x1a280` | `0x10c30` / `793` / `0 neg, 793 pos` | `5,322` / `366` | **`132 / 132`** | `11` / **`74`** | **`284`** (**`61`** zero-gap) |
| `gnu_ld_relax_o2` (`-O2`, `relax=yes`) | `0.935` | `4,354,584` | `0x5060` | `0x4eb30` / `581` / `581 neg, 0 pos` | `0` / `939` | **`19 / 19`** | `4` / **`7`** | **`252`** (**`58`** zero-gap) |
| `rust_lld_relax_o2` (`-O2`, `relax=yes`) | `0.691` | `4,398,928` | `0x15720` | `0xd998` / `576` / `0 neg, 576 pos` | `3,596` / `386` | **`19 / 19`** | `4` / **`7`** | **`252`** (**`59`** zero-gap) |

Three concrete binary-level phenomena govern post-link unwind verification:

1. **GOT relaxation preserves instruction lengths (`7` B `48 8b -> 48 8d`, `6` B `ff 15 -> 67 e8`) and LSDA offsets:**
   - Under default `R_X86_64_GOTPCREL`, `GNU ld 2.47` rewrites `callee_direct+0x17` from `48 8b 05 00 00 00 00` (`mov`) to `48 8d 05 72 ea ff ff` (`lea -0x158e(%rip), %rax`), whereas `rust-lld 22.1.6` leaves it as `48 8b 05 ba 20 04 00` (`mov 0x420ba(%rip), %rax -> 0x64ef8`).
   - Under `-Z relax-elf-relocations=yes` (`210` `R_X86_64_GOTPCRELX` + `14` `R_X86_64_REX_GOTPCRELX` in `crate_caller.o`), **both** linkers rewrite `ff 15 00 00 00 00` (`call *got`, `6` B) in `caller_aligned_trailing_noreturn` to `67 e8 a9 13 00 00` (`addr32 call callee_noreturn_panic`, `6` B), preserving every `.gcc_except_table` `cs_start` and `cs_len` byte offset without shifting labels.
2. **Inter-function `0xCC` vs. `NOP` padding and `zero-gap` adjacent FDEs (`ret_rip == fde_pc_end`):**
   - In `caller_bare_trailing_noreturn` (`7` B: `50` `push %rax` + `6`-byte `call`), `ret_rip` equals `fde_pc_end` (`0x10b07` in `GNU ld`, `0x1f8e7` in `rust-lld`). The bytes at `ret_rip` are `66 0f 1f 84 00 00 00 00` (`nopw` sled) in `GNU ld` vs. `cc cc cc cc cc cc cc cc` (`int3` sled) in `rust-lld`.
   - Worse, across `58`–`61` functions per binary whose `fde_pc_end` lands on a `16`-byte alignment boundary—for example `std::rt::handle_rt_panic` in `gnu_ld_default` (`[0x99e0, 0x9a10)`, ending with `ff 15 50 b3 05 00` at `0x9a0a..0x9a10`)—**zero** `NOP` or `0xCC` bytes exist before `__rust_end_short_backtrace` at `0x9a10`. Unadjusted `ret_rip = 0x9a10` matches the next function's `.eh_frame_hdr` key `0x9a10`!
3. **Intra-function LSDA boundary off-by-one (`ret_rip == next_cs.cs_start`):**
   - In `caller_stack_clash_loop_unwind` (`gnu_ld_default`, `fn_va = 0x11650`), `.gcc_except_table` contains `cs_0 = [0x0, 0x54) -> None`, `cs_1 = [0x54, 0x16) -> Cleanup(lpad = +0x82)`, and `cs_2 = [0x6c, 0x11) -> Filter_Terminate(lpad = +0x160, ttype_index = -1)`.
   - The constructor call `DropToken::new("stack_clash_40k_guard")` sits at `rel_off = 0x4e..0x54` (`6`-byte `ff 15`). Its pushed `ret_rip` has `rel_off = 0x54 == cs_1.cs_start`. With `ret_rip - 1` (`0x53`), `rust_eh_personality` selects `cs_0` (`EHAction::None`); without `- 1`, `0x54` selects `cs_1` (`EHAction::Cleanup`), which would drop uninitialized `_guard` if `DropToken::new` panicked!

---

### 4. Inline `4096`-Byte Stack-Clash Loop Asynchronous DWARF CFA Verification

`Basis: execution + source`

In `caller_stack_clash_loop_unwind` (`[0u8; 41500]` > `32,768` B `ProbeChunk`), `readelf --debug-dump=frames-interp` and `objdump -d` across all `4` configurations confirm how `X86FrameLowering::emitStackProbeInlineGenericLoop` (`X86FrameLowering.cpp:868-938`) preserves exact asynchronous unwind state even with a non-page-multiple tail (`TailOffset != 0`):

- **`-O2` (`gnu_ld_relax_o2` at `0xcbf0` / `rust_lld_relax_o2` at `0x17ec0`):**
  1. `+0x00` (`41 56`, `push %r14`) -> at `+0x02`, `CFA = rsp + 16`; `+0x02` (`53`, `push %rbx`) -> at `+0x03`, `CFA = rsp + 24`.
  2. `+0x03..+0x0d` (`49 89 e3` `mov %rsp, %r11`; `49 81 eb 00 a0 00 00` `sub $0xa000, %r11`) -> at `+0x0d` (`0xcbfd` / `0x17ecd`), `.eh_frame` switches to **`CFA = r11 + 40984`** (`40,960 + 24 = 40,984`, equal to `entry_rsp + 8`).
  3. `+0x0d..+0x21` (`sub $0x1000, %rsp; movq $0x0, (%rsp); cmp %r11, %rsp; jne +0x0d`): across all `10` loop iterations (`40,960` B probed), `%rsp` mutates while `%r11` stays constant, so `CFA = r11 + 40984 == entry_rsp + 8` at every PC.
  4. `+0x21..+0x28` (`48 81 ec 48 02 00 00`, `sub $0x248, %rsp` = `584` B remainder): executes while `CFA` is *still* `r11 + 40984`. At `+0x28` (`0xcc18` / `0x17ee8`), `DW_CFA_def_cfa_register: rsp` and `DW_CFA_def_cfa_offset: 41568` (`40,984 + 584 = 41,568`) take effect at the exact same address, yielding `CFA = rsp + 41568 == entry_rsp + 8` with zero asynchronous CFA glitch, and live cross-crate panic unwinding through the `41.5 KiB` frame succeeds (`rc = 0`) on both linkers.

---

### 5. Multi-Crate Freestanding `#![no_std]` `-static-pie` Startup Matrix

`Basis: execution + source`

Linking [nostd_callee.rs](support/specimens/nostd_callee.rs) + [nostd_caller.rs](support/specimens/nostd_caller.rs) with `-C relocation-model=pie -C link-arg=-nostdlib -C link-arg=-static-pie` (no `_DYNAMIC` startup relocator) exposes **two distinct GOT hazards** across crate boundaries:

| `#![no_std]` `-static-pie` Configuration | Pre-Link Caller / Callee Relocs | Post-Link `_start` / Callee Bytes | `.rela.dyn` | Runtime Outcome |
| :--- | :--- | :--- | :--- | :--- |
| `nostd_inline_data_gnu_ld_default` | Caller: `1 GOTPCREL` (`mov`) | `48 8d 05 f8 0f 00 00` (`lea 0xff8(%rip), %rax` -> `0x2000`) | `{}` (`0` relocs) | **`EXIT_OK` (`rc = 0`)** |
| `nostd_inline_data_rust_lld_default` | Caller: `1 GOTPCREL` (`mov`) | `48 8b 05 f8 10 00 00` (`mov 0x10f8(%rip), %rax` -> `.got 0x2420`) | `RELATIVE: 1` | **`SIGSEGV` (`rc = -11`)** |
| `nostd_crosscrate_call_gnu_ld_default` | Caller: `1 GOTPCREL` (`call`)<br>Callee: `1 GOTPCREL` (`mov`) | `_start`: **`ff 15 ef 2f 00 00`** (`call *got`, unrelaxed!)<br>Callee: `48 8d 0d d6 0f 00 00` (`lea`, relaxed) | `RELATIVE: 1` | **`SIGSEGV` (`rc = -11`)** |
| `nostd_crosscrate_call_rust_lld_default` | Caller: `1 GOTPCREL` (`call`)<br>Callee: `1 GOTPCREL` (`mov`) | `_start`: **`ff 15 0f 11 00 00`** (`call *got`, unrelaxed!)<br>Callee: `48 8b 0d e6 10 00 00` (`mov`, unrelaxed!) | `RELATIVE: 2` | **`SIGSEGV` (`rc = -11`)** |
| `nostd_crosscrate_call_gnu_ld_relax_yes` | Caller: `1 GOTPCRELX` (`call`)<br>Callee: `1 REX_GOTPCRELX` (`mov`) | `_start`: **`67 e8 17 00 00 00`** (`addr32 call 0x1020`)<br>Callee: `48 8d 0d d6 0f 00 00` (`lea +0xfd6(%rip)`) | `{}` (`0` relocs) | **`EXIT_OK` (`rc = 0`)** |
| `nostd_crosscrate_call_rust_lld_relax_yes` | Caller: `1 GOTPCRELX` (`call`)<br>Callee: `1 REX_GOTPCRELX` (`mov`) | `_start`: **`67 e8 17 00 00 00`** (`addr32 call 0x1340`)<br>Callee: `48 8d 0d 4e ef ff ff` (`lea -0x10b2(%rip)`) | `{}` (`0` relocs) | **`EXIT_OK` (`rc = 0`)** |

Unlike single-crate static-PIE binaries (where intra-crate calls emit `e8` `R_X86_64_PLT32` so `GNU ld` succeeds by default), **crossing a `.rlib` crate boundary** causes `rustc` (`RtLibUseGOT = 1`) to emit `ff 15` with legacy `R_X86_64_GOTPCREL`, which **neither `GNU ld` nor `rust-lld` can relax** without `-Z relax-elf-relocations=yes` (`R_X86_64_GOTPCRELX`).

---

### 6. Kernel-Checked `Lean v4.34.1` Cross-Seam Proof, Counterexamples, & Anneal Audit

`Basis: execution (Lean kernel) + source + derived`

[PostLinkAbiDropUnwindCrucible.lean](support/PostLinkAbiDropUnwindCrucible.lean) (`1,106` lines, `781` compiled `.olean` constants: `16` inductives/structures, `370` definitions, `335` theorems; `21` source `theorem` declarations) mechanizes all four layers constructively via `List.foldr` (`unsafe_recs = []`, `non_safe = []`, axioms restricted to `[propext, Quot.sound]`, `[propext]`, or `[]`):

1. **Master End-to-End Composition (`endToEnd_fourLayer_seam_preservation`):** Under `(SC1)` `GotInitializedOrLeaRelaxed`, `(SC2)` `ValidUnwindCallSite` (`1 <= callLen`, `callVa + callLen <= callerFde.pcEnd` even when `callVa + callLen == nextFde.pcBegin`, and `[callVa + callLen - 1]` inside the cleanup LSDA entry), `(SC3)` `AbiValue.WellFormed`, and `(SC4)` `LadderNoPanic` + `updateSretDropFlag true` (`setAtTargetOnly`), `runEndToEndFourLayerSeam` preserves exact `Direct`/`Pair`/`Cast12`/`IndirectSret` return values on normal return, never drops uninitialized `sret` slots or moved-out `Open`/`Conditional` fields on unwind, and executes the exact expected destructor trace (`live_sret_normal_and_unwind_traces_match_binary`).
2. **Three Kernel-Checked Sharpness Counterexamples + Stack-Clash Proof:**
   - **`ce1_trailing_noreturn_and_lsda_boundary_sharpness` (`0` axioms):** Proves on live binary coordinates that unadjusted `ret_rip` hijacks `nextFde` when `gap == 0` (`0x9a10`), misses all FDEs across `0xCC`/`NOP` gaps (`0x10ae7`), and dispatches `DropToken::new` (`0x11684`) to `Cleanup(0x82)` on uninitialized storage, whereas `ret_rip - 1` resolves all three plus `Filter_Terminate(0x160)` (`0x116ad`) accurately.
   - **`ce2_static_pie_got_divergence_and_crosscrate_call_hazard` (`[propext]`):** Proves for all `0 < loadBias` that under `gotRelocated = false`, `GNU ld` succeeds and `rust-lld` faults on legacy `.gotpcrel` data `mov`, while **both** linkers fault on legacy `.gotpcrel` cross-crate `call *got` and **both** succeed under `.gotpcrelx`.
   - **`ce3_double_panic_static_vs_open_divergence` (`0` axioms) & `stale_drop_flag_causes_double_drop`:** Proves exact pre-abort trace divergence (`["callee_direct_guard", "dp_static_f0_bomb", "dp_static_f1_sibling", "dp_static_f2_sibling"]` vs. `["dp_open_f2_moved", "callee_direct_guard", "dp_open_f0_bomb"]`) and double-drop under stale flags.
   - **`stackClashInlineLoop_async_cfa_exact` (`[propext]`):** Proves symbolic `Int` invariance `cfaDuringProbeLoop = entryRsp + 8` and `cfaAfterProbeTail = entryRsp + 8` for arbitrary `(entryRsp, pushedBytes, boundOffset, tailOffset)`.
3. **Live `joshlf/anneal` TCB boundary (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** In `trusted/lean/Trusted/MirAst.lean:782-795`, `Drop`, `UnwindTerminate`, and indirect `Call` map to `TerminatorKind.unsupported`; in `trusted/lean/Trusted/MirSemantics.lean:953-972, 1543-1569`, projected moves/copies (`!place.projection.isEmpty`), `cleanup = true` returns, `.unwindResume`, `.assert`, and `.call` return `.fault .unsupported`. Extending Anneal to multi-crate unwinding requires modeling `sret` target-block initialization, `UnwindAction::Cleanup` vs. `Terminate`, and post-link `GOTPCRELX` / LSDA side conditions.

#### Quantitative & Validation Scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

| Dimension | Measured Value / Structural Guarantee | Basis |
| :--- | :--- | :--- |
| **`L1` Proof & Authoring Effort** | [PostLinkAbiDropUnwindCrucible.lean](support/PostLinkAbiDropUnwindCrucible.lean): `1,106` LOC (`54,402` B, `51` source defs/types, `21` source theorems); [probe_postlink_abi_unwind_crucible.py](support/probe_postlink_abi_unwind_crucible.py): `1,262` LOC (`49,854` B) + `4` Rust crate specimens (`473` LOC total) | Source + Execution |
| **`L2` Toolchain Build / Check Time** | Synchronous Lean `v4.34.1` kernel check: `13.314s` (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`); multi-crate `rustc` compile+link: `0.470s` (`rust-lld -O0`) vs. `0.719s` (`GNU ld -O0`), `0.691s` (`rust-lld -O2`) vs. `0.935s` (`GNU ld -O2`) | Execution (`lean`, `rustc`, `ld`, `rust-lld`) |
| **`L3` Seed Compile Latency** | Concrete Lean trace & LSDA witness evaluation (`decide` / `rfl`) completes inside the `13.314s` cold kernel check; per-function incremental certificate emission latency: **not measured** | Execution (Lean kernel) / scope boundary |
| **`L4` Generated Code Speed** | `84 / 84` `std` scenarios + `8 / 8` double-panic runs + `6 / 6` `#![no_std]` `-static-pie` runs executed natively (`EXIT_OK = 0`, `SIGABRT = -6`, `SIGSEGV = -11`); steady-state cycle/throughput microbenchmarking: **not measured** | Execution (native x86-64 binaries) / boundary |
| **`L5` Checker Throughput & Cold Start** | Pure-Python ELF64 + `.eh_frame_hdr` + `.eh_frame` + `.gcc_except_table` parser/auditor + `10` multi-crate builds + `98` native runs complete end-to-end in `~11s`; standalone Rust/Lean full-binary validator `MB/s`: **not measured** | Execution (`probe_postlink_abi_unwind_crucible.py`) |
| **`L6` Footprint (RAM / Binary)** | Lean `v4.34.1` max RSS: `541.24 MiB` (`554,232 KiB`); linked `std` ELF sizes: `4,354,584`–`4,433,864` B (`GNU ld`) vs. `4,398,928`–`4,478,048` B (`rust-lld`); captured JSON artifact: `607,083` B | Execution (`resource.getrusage`, `stat`) |
| **`C1` Spec / TCB Auditability** | `0` `sorryAx`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide` (`Lean.ofReduceBool`), `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`, `0` `@[extern]` across all `781` `.olean` constants (`[propext, Quot.sound]` / `[propext]` / `[]` only) | Execution (`#print axioms` + `.olean` audit at `trustLevel := 0`) |
| **`C2` Orthogonality** | Cleanly factors `FnAbi` register/memory marshaling, linker-parameterized `GOTPCREL`/`GOTPCRELX` rewriting, `.eh_frame_hdr`/LSDA `ip - 1` dispatch, and `ElaborateDrops` ladder execution via 4 explicit interface predicates | Derived from [PostLinkAbiDropUnwindCrucible.lean](support/PostLinkAbiDropUnwindCrucible.lean) |
| **`V1` Non-Vacuity / Negatives** | Kernel-checked sharpness counterexamples `CE1` (`0` axioms), `CE2` (`[propext]`), `CE3` (`0` axioms), and `stale_drop_flag_causes_double_drop`, paired with live `SIGSEGV (-11)` and `SIGABRT (-6)` native negative executions | Execution (Lean kernel + OS signal exits) |
| **`V2` Differential Fuzzing** | Exhaustive `4`-linker/opt × `21`-scenario `std` differential matrix + `6`-way `#![no_std]` `-static-pie` matrix + full-binary scan of `2,748` FDEs across `4` linked executables; randomized signature/CFG fuzzing: **not examined** | Execution (`probe_postlink_abi_unwind_crucible.py`) |
| **`V3` Weak Memory / Leakage** | Sequential single-thread call, unwind, and startup relocation semantics; concurrent `pthread_cancel` forced unwinding (`_UA_FORCE_UNWIND`) and speculative side channels: **not examined** | Explicit scope boundary |
| **`V4` Held-Out Replay** | Verified across `2` distinct linkers (`GNU ld 2.47`, `rust-lld 22.1.6`), `2` optimization/relocation regimes (`-O0` default vs. `-O2 -Z relax-elf-relocations=yes`), and `2` runtime profiles (`std` vs. `#![no_std]`); non-`x86_64` ISAs: **not examined** | Execution + scope boundary |

---

## Boundaries

`Basis: source + execution`

- **Non-`x86_64` ELF, Mach-O Compact Unwind, and Windows SEH `.pdata`:** `not examined` in execution. As `PassWrapper.cpp:389-396` documents, `Options.NoTrapAfterNoreturn = true` is `known not to apply` on Windows (where LLVM emits a trailing trap after `noreturn` calls so `RtlLookupFunctionEntry` keeps `ret_rip` inside `.pdata`) and Wasm.
- **Asynchronous signal-frame unwinding (`ip_before_instr != 0`) inside mid-instruction body code:** `not examined` dynamically. While Finding 4 verifies asynchronous `.eh_frame` CFA offsets (`%r11` -> `%rsp`) across every prologue instruction of the `4096`-byte stack-clash probe loop, async `SIGSEGV`/`SIGPROF` unwinding through arbitrary mid-block instructions with `'S'` CIE augmentation was not executed.
- **Forced unwinding (`_UA_FORCE_UNWIND`) across `filter_landing_pad`:** `known not to apply` to `CE3`'s immediate abort. In `library/std/src/sys/personality/gcc.rs:234`, `EHAction::Filter(_) if actions & uw::_UA_FORCE_UNWIND != 0 => uw::_URC_CONTINUE_UNWIND` explicitly bypasses `Terminate(InCleanup)` filter pads during C/POSIX forced stack unwinding (`pthread_cancel`).
- **`GNU ld 2.47` internal C source lines:** `unknown` at commit-SHA granularity (Debian's packaged `/usr/bin/ld` `2.47` binary was executed and disassembled directly rather than pinned to a Binutils git SHA; `rust-lld 22.1.6` is pinned to both `rust-lang/llvm-project` and `llvm/llvm-project` 40-hex commits).
- **Direct ingestion into `joshlf/anneal` `Trusted.MirSemantics`:** Currently `unsupported` by `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`TerminatorKind.call`, `.unwindResume`, `Drop`, and `UnwindTerminate` fail closed with `.unsupported`). [PostLinkAbiDropUnwindCrucible.lean](support/PostLinkAbiDropUnwindCrucible.lean) is a standalone foundation-only Lean `v4.34.1` formalization designed to specify the exact invariants a future multi-crate/unwind extension must enforce.

---

## Evidence

`Basis: source + execution + normative`

1. **Pinned Upstream Primary Sources (`Basis: source`):**
   - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:
     * `compiler/rustc_target/src/callconv/mod.rs:39-74, 717-848` (`PassMode`, `FnAbi::adjust_for_rust_abi`).
     * `compiler/rustc_target/src/callconv/x86_64.rs:16-173, 178-265` (SysV AMD64 eightbyte `Class`, `cast_target`, `sret` `make_indirect`).
     * `compiler/rustc_ty_utils/src/abi.rs:421-644` (`fn_abi_sanity_check`, `fn_abi_new_uncached`, `fn_abi_adjust_for_abi`).
     * `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:8, 11-12` (`plt_by_default = false`, `StackProbeType::Inline`, `static_position_independent_executables = true`) and `compiler/rustc_target/src/spec/mod.rs:2899` (`trap_unreachable: true`).
     * `compiler/rustc_mir_transform/src/elaborate_drops.rs:170-193, 361, 433-520` (`drop_style`, `Unwind::InCleanup` on `data.is_cleanup`, `drop_flags_for_fn_rets` at `target` block start vs. pre-call flag set).
     * `compiler/rustc_mir_transform/src/elaborate_drop.rs:609-624, 675-716` (`drop_halfladder`, `drop_ladder`) and `compiler/rustc_mir_transform/src/shim.rs:379-514` (`build_drop_shim` with `Unwind::To(resume_block)`).
     * `compiler/rustc_codegen_ssa/src/mir/block.rs:213-294, 595-690, 1144-1394, 1945-2214` (`do_call`, `codegen_drop_terminator`, `terminate_block`, `make_return_dest`, `store_return`) and `compiler/rustc_codegen_llvm/src/builder.rs:1219-1223` (`filter_landing_pad`).
     * `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:373, 377-397` (`X86RelaxRelocations`, `TrapUnreachable = true`, `NoTrapAfterNoreturn = true`).
     * `library/std/src/sys/personality/gcc.rs:209-249, 323-340` (`rust_eh_personality_impl`, `find_eh_action` `ip.wrapping_sub(1)`), `library/std/src/sys/personality/dwarf/eh.rs:66-172` (`.gcc_except_table` LSDA range scan & `ttype_index < 0 -> EHAction::Filter`), and `library/core/src/panicking.rs:233` (`panic_in_cleanup`).
   - `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` (cross-checked at `llvm/llvm-project@fc4aad7b5db3fff421df9a9637605b9ca5667881`):
     * `llvm/lib/CodeGen/AsmPrinter/EHStreamer.cpp:209-355, 379-430` (`computeCallSiteTable`, `emitExceptionTable`).
     * `llvm/lib/CodeGen/SelectionDAG/SelectionDAGBuilder.cpp:3263-3266, 3665-3671` (`TrapUnreachable` & `NoTrapAfterNoreturn` gating).
     * `llvm/lib/Target/X86/X86FrameLowering.cpp:683-942` (`emitStackProbeInlineGeneric`, `emitStackProbeInlineGenericLoop` `DW_CFA_def_cfa_register` `%r11` -> `%rsp`).
     * `llvm/lib/Target/X86/MCTargetDesc/X86ELFObjectWriter.cpp:215-237`, `lld/ELF/Arch/X86_64.cpp:93, 958-989, 1072-1110`, and `lld/ELF/SyntheticSections.cpp:580-669`.
   - `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/audit/TrustedBoundary.lean:1-250`, `trusted/lean/Trusted/MirAst.lean:77-92, 782-795`, `trusted/lean/Trusted/MirSemantics.lean:949-976, 1537-1570`.
2. **Normative Specifications (`Basis: normative`):**
   - System V Application Binary Interface — AMD64 Architecture Processor Supplement (`PassMode` eightbyte classification; `R_X86_64_GOTPCREL`, `R_X86_64_GOTPCRELX`, and `R_X86_64_REX_GOTPCRELX` relaxation preconditions).
   - Itanium C++ ABI: Exception Handling (`_Unwind_RaiseException` search/cleanup steps, LSDA call-site and action-record encoding) and Linux Standard Base Core Specification (`.eh_frame_hdr` version `1` binary-search table).
3. **Preserved Executable Artifacts & Captured Results (`Basis: execution`, observed `2026-11-21`):**
   - Multi-crate dual-linker probe harness: [probe_postlink_abi_unwind_crucible.py](support/probe_postlink_abi_unwind_crucible.py) (`49,854` B, `1,262` lines, SHA-256 `fdea2c94c87f54eb3d1210106bec2ccbdabc3e00372b7ffe1ea7ab3d203aa01b`).
   - Preserved multi-crate Rust source specimens:
     * [crate_callee.rs](support/specimens/crate_callee.rs) (`4,666` B, SHA-256 `b733cce0f85ae538b0f31adc7e6f510eaf2fbba5e59e90ecdcd70b7b1c0f2a91`)
     * [crate_caller.rs](support/specimens/crate_caller.rs) (`9,916` B, SHA-256 `32b9675d47f370ed3e0c5b4007886c7546ad88368f05447ddf24a77c5e9bd799`)
     * [nostd_callee.rs](support/specimens/nostd_callee.rs) (`1,196` B, SHA-256 `287b7ac1e1bf85989d817be1f3f136d05211787ace1b74969eb1d54a881806f5`)
     * [nostd_caller.rs](support/specimens/nostd_caller.rs) (`1,350` B, SHA-256 `911a0efce6fdffc121897334535aa077a080402395e56f3e056422c11fd89063`)
   - Complete captured disassembly, `.eh_frame_hdr`/LSDA tables, stack-clash CFI rows, and execution traces: [postlink_abi_unwind_crucible_results.json](support/postlink_abi_unwind_crucible_results.json) (`607,083` B, `19,031` lines, SHA-256 `b7d1de240272f99c41480a174148b315ce33126d7234a084cabe0bf3c683d3cd`).
   - Kernel-checked `Lean v4.34.1` proof module: [PostLinkAbiDropUnwindCrucible.lean](support/PostLinkAbiDropUnwindCrucible.lean) (`54,402` B, `1,106` lines, SHA-256 `5b9cf829a98b0e0e7a4e4637631d176b539c8eca9b462a56c505eef95c1b26fa`).

---

## Revalidation

`Basis: execution + source`

```bash
# 1. Re-run the full multi-crate rustc + GNU ld vs. rust-lld compilation, disassembly,
#    .eh_frame_hdr / .gcc_except_table LSDA containment check, stack-clash loop CFI audit,
#    double-panic subprocess comparison, and 6-way #![no_std] -static-pie startup matrix:
python3 reports/end-to-end-postlink-abi-drop-unwind-and-static-pie-seam-crucible/support/probe_postlink_abi_unwind_crucible.py \
  --out /tmp/revalidated_crucible_results.json

# 2. Synchronously kernel-check the Lean v4.34.1 cross-seam proof and sharpness counterexamples
#    with zero warnings and print all theorem axiom dependencies:
lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  reports/end-to-end-postlink-abi-drop-unwind-and-static-pie-seam-crucible/support/PostLinkAbiDropUnwindCrucible.lean
```

**Fastest discriminating checks after a toolchain or linker upgrade:**
- If `nostd_inline_data_rust_lld_default` changes from `SIGNAL_-11` (`SIGSEGV`) to `EXIT_OK` (`0`), check whether `rustc_target` enabled `relax_elf_relocations: true` by default on `x86_64-unknown-linux-gnu` (`X86ELFObjectWriter.cpp:215-237`) or whether LLD relaxed legacy `R_X86_64_GOTPCREL`.
- If `binary_wide_fde_ending_at_call_count` drops to `0`, check `PassWrapper.cpp:394-396` for changes to `Options.NoTrapAfterNoreturn`.
- If `double_panic_static` and `double_panic_open` stop diverging on `dp_static_f1_sibling`, inspect `elaborate_drops.rs:361` and `shim.rs:389-398` (`build_drop_shim` cleanup-mode lowering).
