# Stack Discipline, Inline and `__chkstk` Probes, Red Zones, Alignment, and Overflow Handling Across Tier 1 Targets

## Summary

A verified drop-in replacement for `rustc` targeting the 8 Tier 1 platforms must satisfy the following stack-frame layout, stack-probing, red-zone, alignment, and runtime overflow contracts:

1. **Stack Probing Per Target (`compiler/rustc_codegen_llvm/src/attributes.rs:338-369`, `X86FrameLowering.cpp:728-885`, `AArch64FrameLowering.cpp:704-720, 3852-3931`):**
   - **Linux (`x86_64`, `aarch64`, `i686`) and macOS (`aarch64-apple-darwin`):** All four Unix Tier 1 target specs set `stack-probes: {"kind": "inline"}`, which emits the LLVM function attribute `"probe-stack"="inline-asm"` (identical across `1.99.1`, `nightly-2026-09-30`, and `nightly-2026-11-12`). Both x86 and AArch64 use a **4096-byte (`4 KiB`) probe interval** (`StackProbeSize = 4096`, even on 16 KiB-page `aarch64-apple-darwin`), but differ in their **unprobed residual threshold**:
     - On `x86_64-unknown-linux-gnu` and `i686-unknown-linux-gnu`, frames $< 4096\text{ B}$ (`frame_3k`, `3104 B`) emit a plain `subq $3088, %rsp` with no probe; frames $\ge 4096\text{ B}$ (`frame_8k`) unroll up to 8 steps of `subq $4096, %rsp; movq $0, (%rsp)` (`subl`/`movl` on i686), and frames $> 32768\text{ B}$ (`8 * 4096`, `frame_70k`) emit a loop using `%r11` (x86_64) or `%eax` (i686) as the temporary CFA register (`.cfi_def_cfa_register %r11`).
     - On `aarch64-unknown-linux-gnu` and `aarch64-apple-darwin`, `AArch64::StackProbeMaxUnprobedStack` is **`1024` bytes** (`AArch64FrameLowering.cpp:705, 3918`)! Consequently, `frame_3k` (`3088 B > 1024 B`) emits `sub sp, sp, #3088; ldr xzr, [sp]`, `frame_8k` unrolls `sub sp, sp, #1, lsl #12; ldr xzr, [sp]`, and `frame_70k` loops with `x9` (`sub x9, sp, #17, lsl #12`) and probes the `2064 B` residual (`> 1024 B`) with an extra `ldr xzr, [sp]`.
   - **Windows (`x86_64-pc-windows-msvc`, `aarch64-pc-windows-msvc`, `i686-pc-windows-msvc`, `x86_64-pc-windows-gnu`):** The target specs omit `stack-probes` (`StackProbeType::None`), relying on LLVM's built-in Windows prologue probing at a `4096`-byte threshold (`frame_3k` has no probe):
     - `x86_64-pc-windows-msvc`: `movl $size, %eax; callq __chkstk; subq %rax, %rsp` (`__chkstk` probes without modifying `%rsp`).
     - `x86_64-pc-windows-gnu`: `movl $size, %eax; callq ___chkstk_ms; subq %rax, %rsp`.
     - `i686-pc-windows-msvc`: `movl $size, %eax; calll __chkstk` (`_alloca_probe` ABI: **decrements `%esp` by `%eax` inside `__chkstk`**!).
     - `aarch64-pc-windows-msvc`: `mov x15, #(size / 16); bl __chkstk; sub sp, sp, x15, lsl #4` (input in **`x15` scaled by 16 bytes**!).
2. **Red Zones (`support/stack_*.s`, `AArch64FrameLowering.cpp:538-563`):** Although three Tier 1 ABIs define a red zone below `SP`—`x86_64-unknown-linux-gnu` (`128 B`), `aarch64-apple-darwin` (`128 B`), and `aarch64-pc-windows-msvc` (`16 B`)—**only `x86_64-unknown-linux-gnu` actually uses the red zone in default `rustc` builds** (`movq %rdi, -64(%rsp)` with zero `subq %rsp` in `redzone_leaf`). On `aarch64-apple-darwin` and `aarch64-pc-windows-msvc`, `rustc` sets `frame-pointer: "non-leaf"`, and LLVM's `AArch64FrameLowering::canUseRedZone` (`line 562`) returns `false` whenever stack size $> 0$ and `uwtable` / frame-lowering constraints apply (`sub sp, sp, #80` emitted in `redzone_leaf` on both targets!).
3. **Runtime Stack Overflow Handling and Default Stack Sizes (`library/std/src/sys/pal/{unix,windows}/stack_overflow.rs`, `sys/thread/{unix,windows}.rs`):**
   - Spawned threads default to `DEFAULT_MIN_STACK_SIZE = 2 * 1024 * 1024` (`2 MiB`) on all 8 Tier 1 targets, overridable via `RUST_MIN_STACK` (`library/std/src/thread/lifecycle.rs:37-39`).
   - On Linux and macOS, `std::rt::init` installs `SA_SIGINFO | SA_ONSTACK` handlers for `SIGSEGV` and `SIGBUS` backed by an `mmap`ped alternate signal stack (`max(SIGSTKSZ, getauxval(AT_MINSIGSTKSZ))` + 1 `PROT_NONE` guard page) and records each thread's guard-page address range in a global `BTreeMap` (`thread_info.rs`) to distinguish stack overflow (`thread '...' has overflowed its stack` + `rtabort!`) from ordinary memory faults (which reset `SIG_DFL` and re-fault).
   - On Windows, `std` calls `AddVectoredExceptionHandler(0, Some(vectored_handler))` and calls `SetThreadStackGuarantee(&mut 0x5000)` (`20 KiB`) on both the main thread and every `std::thread::spawn` thread; when `EXCEPTION_STACK_OVERFLOW` (`0xC00000FD`) fires, the handler prints the overflow diagnostic and returns `EXCEPTION_CONTINUE_SEARCH`.
4. **LLVM vs. Cranelift Frame Size Ratios (`support/clif_vs_llvm_corpus.rs`):** Across the 5-function recursion/locals corpus on `x86_64-unknown-linux-gnu`, at `-C opt-level=0` Cranelift frames are $0.50\times\text{--}1.00\times$ the size of LLVM frames (`32 B` vs. `64 B` on `ackermann`; `400 B` vs. `400 B` on `recursive_parser_step`), whereas at `-C opt-level=2` Cranelift frames are $1.00\times\text{--}3.17\times$ larger than LLVM (`304 B` vs. `96 B` on `format_and_drop_frame`; `416 B` vs. `176 B` on `recursive_parser_step`) because Cranelift always pushes `%rbp` (`16 B` minimum frame) and does not perform LLVM's aggressive stack-slot coloring across lifetime markers.

## Applicability

These findings apply to `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), its bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, including `rustc_codegen_cranelift` `0.1.0`) across all 8 Tier 1 targets.

## Findings

### 1. Stack Probe Mechanisms, Thresholds, and Instruction Sequences Across All 8 Tier 1 Targets

Basis: source + execution

Compiling `support/stack_probe.rs` (`frame_3k` = `3072 B` local array, `frame_8k` = `8192 B`, `frame_70k` = `71680 B`) across all 8 Tier 1 targets (`support/stack_*.s`) establishes the exact probing rules:

| Target Triple | `target.stack_probes` | Probe Interval (`StackProbeSize`) | Unprobed Threshold | `frame_3k` (`~3.1 KiB`) | `frame_8k` (`~8.2 KiB`) | `frame_70k` (`~71.7 KiB`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `Inline` (`"probe-stack"="inline-asm"`) | `4096 B` | `4096 B` | Unprobed `subq $3088, %rsp` | Unrolled $2\times$ (`subq $4096, %rsp; movq $0, (%rsp)`) + `subq $16, %rsp` | Loop using `%r11` (`subq $69632, %r11; .cfi_def_cfa_register %r11`) + `subq $2064, %rsp` |
| `aarch64-unknown-linux-gnu` | `Inline` (`"probe-stack"="inline-asm"`) | `4096 B` | **`1024 B`** (`StackProbeMaxUnprobedStack`) | **Probed:** `sub sp, sp, #3088; ldr xzr, [sp]` | Unrolled $2\times$ (`sub sp, sp, #1, lsl #12; ldr xzr, [sp]`) | Loop using `x9` (`sub x9, sp, #17, lsl #12`) + `sub sp, sp, #2064; ldr xzr, [sp]` |
| `i686-unknown-linux-gnu` | `Inline` (`"probe-stack"="inline-asm"`) | `4096 B` | `4096 B` | Unprobed `subl $3076, %esp` | Unrolled $2\times$ (`subl $4096, %esp; movl $0, (%esp)`) + `pushl %eax` | Loop using `%eax` (`subl $69632, %eax; .cfi_def_cfa_register %eax`) + `subl $2052, %esp` |
| `aarch64-apple-darwin` | `Inline` (`"probe-stack"="inline-asm"`) | `4096 B` (despite 16 KiB OS page size!) | **`1024 B`** (`StackProbeMaxUnprobedStack`) | **Probed:** `sub sp, sp, #3088; ldr xzr, [sp]` | Unrolled $2\times$ (`sub sp, sp, #1, lsl #12; ldr xzr, [sp]`) | Loop using `x9` (`sub x9, sp, #17, lsl #12`) + `sub sp, sp, #2064; ldr xzr, [sp]` |
| `x86_64-pc-windows-msvc` | `None` (LLVM Win64 default) | `4096 B` | `4096 B` | Unprobed `subq $3120, %rsp` | `movl $8240, %eax; callq __chkstk; subq %rax, %rsp` | `movl $71728, %eax; callq __chkstk; subq %rax, %rsp` |
| `aarch64-pc-windows-msvc` | `None` (LLVM Win64 default) | `4096 B` | `4096 B` (`windowsRequiresStackProbe`) | Unprobed `sub sp, sp, #3088` | `mov x15, #513; bl __chkstk; sub sp, sp, x15, lsl #4` (`513 * 16 = 8208 B`) | `mov x15, #4481; bl __chkstk; sub sp, sp, x15, lsl #4` (`4481 * 16 = 71696 B`) |
| `i686-pc-windows-msvc` | `None` (LLVM Win32 default) | `4096 B` | `4096 B` | Unprobed `subl $3076, %esp` | `movl $8196, %eax; calll __chkstk` (`__chkstk` adjusts `%esp`!) | `movl $71684, %eax; calll __chkstk` (`__chkstk` adjusts `%esp`!) |
| `x86_64-pc-windows-gnu` | `None` (LLVM MinGW default) | `4096 B` | `4096 B` | Unprobed `subq $3120, %rsp` | `movl $8240, %eax; callq ___chkstk_ms; subq %rax, %rsp` | `movl $71728, %eax; callq ___chkstk_ms; subq %rax, %rsp` |

**Why AArch64 probes at `1024 B` (`frame_3k`) while x86 probes at `4096 B`:**
In `llvm/lib/Target/AArch64/AArch64FrameLowering.cpp:705, 3864-3930`, LLVM's AArch64 inline stack prober partitions a frame of size $F$ into $N = \lfloor F / 4096 \rfloor$ blocks of `4096` bytes (`AArch64::StackProbeMaxLoopUnroll = 4`, so $N \le 4$ unrolls and $N > 4$ emits a loop) plus a `ResidualSize = F % 4096`. Because outgoing call arguments or unprobed leaf frames are permitted up to `AArch64::StackProbeMaxUnprobedStack = 1024` bytes, line `3918` emits a volatile `ldr xzr, [sp]` whenever `ResidualSize > 1024`! Thus `frame_3k` (`ResidualSize = 3088 > 1024`) receives an explicit `ldr xzr, [sp]` on both `aarch64-unknown-linux-gnu` and `aarch64-apple-darwin`, whereas `frame_3k` on `x86_64` (`X86FrameLowering.cpp:762`, where `Offset + AlignOffset <= 4096`) emits no probe.

### 2. Red Zones, Stack Alignment, Frame Pointers, and Dynamic Stack Realignment

Basis: normative + source + execution

| Target Triple | ABI Red Zone | Red Zone Used by `rustc`? (`redzone_leaf`) | Call-Boundary SP Alignment | Incoming Arg Alignment (`i686`) | Default `frame-pointer` (`tier1_target_specs_1991.txt`) | Over-Aligned Frame (`Align64`) Dynamic Realignment Sequence (`support/stack_*.s`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `128 B` (`[rsp - 128 .. rsp)`) | **Yes** (`movq %rdi, -64(%rsp)`, 0 `subq %rsp`, `.stack_sizes = 0`) | `16 B` (`RSP % 16 == 0` before `callq`, `RSP % 16 == 8` at entry) | N/A | `MayOmit` (omitted unless alloca / realignment) | `pushq %rbp; movq %rsp, %rbp; andq $-64, %rsp; subq $128, %rsp` ... `movq %rbp, %rsp; popq %rbp` |
| `aarch64-unknown-linux-gnu` | `0 B` (AAPCS64 has no red zone) | **No** (`sub sp, sp, #80`, `.stack_sizes = 80`) | `16 B` (`SP % 16 == 0` at all times when accessed) | N/A | `NonLeaf` (`stp x29, x30, [sp, #-N]!; mov x29, sp`) | `stp x29, x30, [sp, #-16]!; mov x29, sp; sub x9, sp, #112; and sp, x9, #0xffffffffffffffc0` ... `mov sp, x29` |
| `i686-unknown-linux-gnu` | `0 B` | **No** (`subl $76, %esp`, `.stack_sizes = 92`) | **`16 B`** (`ESP % 16 == 0` before `calll`, `ESP % 16 == 12` at entry) | `4 B` (`f64:32:64`, `i64:32:64`) | `MayOmit` | `pushl %ebp; movl %esp, %ebp; andl $-64, %esp; subl $192, %esp` ... `movl %ebp, %esp; popl %ebp` |
| `aarch64-apple-darwin` | `128 B` (Apple ARM64 ABI) | **No in `rustc` for `80 B` locals** (`sub sp, sp, #80` in `redzone_leaf`) | `16 B` (`SP % 16 == 0` at all times) | N/A | `NonLeaf` (`stp x29, x30, [sp, #16]; add x29, sp, #16`) | `stp x29, x30, [sp, #-16]!; mov x29, sp; sub x9, sp, #112; and sp, x9, #0xffffffffffffffc0` ... `mov sp, x29` |
| `x86_64-pc-windows-msvc` | `0 B` (plus `32 B` caller shadow space above return address) | **No** (`subq $72, %rsp`) | `16 B` (`RSP % 16 == 0` before `callq`, plus `32 B` shadow space) | N/A | `MayOmit` | `pushq %rbp; subq $176, %rsp; leaq 128(%rsp), %rbp; .seh_setframe %rbp, 128; .seh_endprologue; andq $-64, %rsp` ... `leaq 48(%rbp), %rsp; popq %rbp` |
| `aarch64-pc-windows-msvc` | `16 B` (Windows ARM64 ABI, reserved for profiler/debugger) | **No** (`sub sp, sp, #80`) | `16 B` (`SP % 16 == 0` at all times) | N/A | `NonLeaf` | `stp x29, x30, [sp, #-16]!; mov x29, sp; .seh_set_fp; .seh_endprologue; sub x9, sp, #112; and sp, x9, #0xffffffffffffffc0` ... `mov sp, x29` |
| `i686-pc-windows-msvc` | `0 B` | **No** (`andl $-8, %esp; subl $88, %esp`) | **`4 B`** (`S32` in `data-layout`, NOT 16-byte aligned!) | `4 B` (`i64:64` requires `andl $-8, %esp` when 8-B locals exist) | `MayOmit` (forced when realigning `%esp` to `8 B` or `64 B`) | `pushl %ebp; movl %esp, %ebp; andl $-64, %esp; subl $128, %esp` ... `movl %ebp, %esp; popl %ebp` |
| `x86_64-pc-windows-gnu` | `0 B` (`32 B` caller shadow space) | **No** (`subq $72, %rsp`) | `16 B` | N/A | `MayOmit` | Same `.seh_setframe %rbp, 128` + `andq $-64, %rsp` after `.seh_endprologue` as `x86_64-pc-windows-msvc` |

**Two critical ABI contrasts for a verified backend:**
1. **`i686-pc-windows-msvc` vs. `i686-unknown-linux-gnu` stack alignment (`support/stack_i686-*.s`):** On `i686-unknown-linux-gnu`, `data-layout` specifies `S128` (`16-byte` stack alignment at call boundaries), so `movdqa %xmm0, (%esp)` in `overaligned_frame` and `redzone_leaf` can assume `ESP` is 16-byte aligned at entry (`ESP % 16 == 12`). On `i686-pc-windows-msvc`, `data-layout` specifies `S32` (**4-byte** stack alignment at call boundaries)! Consequently, even in `redzone_leaf` (`support/stack_i686-pc-windows-msvc.s:131-137`) and `access_all_tls` (`tls_i686-pc-windows-msvc.s`), simply having `u64` (`8-byte` aligned) stack locals forces LLVM to establish a frame pointer (`pushl %ebp; movl %esp, %ebp`) and dynamically realign the stack with `andl $-8, %esp`!
2. **Windows x64 dynamic realignment (`andq $-64, %rsp`) MUST occur *after* `.seh_endprologue` (`support/stack_x86_64-pc-windows-msvc.s:119-126`):** Because Windows x64 `UNWIND_INFO` has no unwind opcode for bitwise `AND` on `RSP`, a function with a 64-byte aligned local must establish a frame pointer in the prologue (`subq $176, %rsp; leaq 128(%rsp), %rbp; .seh_setframe %rbp, 128; .seh_endprologue`), and only execute `andq $-64, %rsp` *after* `.seh_endprologue` so the OS unwinder restores `RSP` from `RBP` (`leaq 48(%rbp), %rsp`) without needing to invert `andq $-64, %rsp`.

### 3. `std` Stack Overflow Detection, Guard Pages, and Default Stack Sizes

Basis: source + execution

1. **Default stack sizes (`library/std/src/sys/thread/{unix.rs:31,windows.rs:14}`, `thread/lifecycle.rs:37-39`):**
   - **Main thread:** Determined by the OS kernel and binary header: on Linux and macOS, the `RLIMIT_STACK` soft limit (typically `8 MiB`); on Windows, the PE optional header `SizeOfStackReserve` (`1 MiB` default in `link.exe` / `lld-link`). Note that `rustc` itself spawns a worker thread with a larger stack (default `8 MiB`, or `RUST_MIN_STACK` in `compiler/rustc_interface/src/util.rs:129-145`).
   - **Spawned threads (`std::thread::spawn`):** `Builder::spawn_unchecked_` chooses `self.stack_size.unwrap_or_else(|| env::var_os("RUST_MIN_STACK").and_then(...).unwrap_or(imp::DEFAULT_MIN_STACK_SIZE))`, where `DEFAULT_MIN_STACK_SIZE = 2 * 1024 * 1024` (`2 MiB`) across all 8 Tier 1 targets. On Unix (`sys/thread/unix.rs:74-98`), if `pthread_attr_setstacksize` returns `EINVAL`, `std` rounds `stack_size` up to `sys::pal::conf::page_size()` (`4 KiB` or `16 KiB`). On Windows (`sys/thread/windows.rs:31-37`), `CreateThread` is called with `STACK_SIZE_PARAM_IS_A_RESERVATION` (`0x00010000`).
2. **Unix guard pages and `sigaltstack` (`library/std/src/sys/pal/unix/stack_overflow.rs:101-621`):**
   - **Main thread (`init`, `lines 158-197, 425-544`):** On Linux (`install_main_guard_linux`), `std` does *not* call `mmap`/`mprotect` on the main thread stack (because mapping a manual guard page causes the Linux kernel to enforce a `1 MiB` `stack_guard_gap` above it, `#43052`); instead, it queries `pthread_getattr_np` + `pthread_attr_getstack` and records `stackaddr - page_size .. stackaddr` in `thread_info`. On macOS (`install_main_guard_default`, `lines 512-544`), `std` remaps the bottom page of the main stack (`pthread_get_stackaddr_np(th) - pthread_get_stacksize_np(th)`) with `mmap64(..., MAP_FIXED)` + `mprotect(..., PROT_NONE)` so overflowing the main stack raises `SIGBUS` (`KERN_PROTECTION_FAILURE`).
   - **Spawned threads (`current_guard`, `lines 546-620`):** Queries `pthread_getattr_np` + `pthread_attr_getguardsize` + `pthread_attr_getstack`. Because glibc $< 2.27$ placed the guard page *inside* `stackaddr .. stackaddr + guardsize` while glibc $\ge 2.27$ places it *below* (`stackaddr - guardsize .. stackaddr`), Linux `gnu` records the double-width range `stackaddr - guardsize .. stackaddr + guardsize` (`lines 603-612`).
   - **Alternate signal stack (`get_stack`, `lines 199-239, 303-315`):** Each thread allocates `sigstack_size + page_size` via `mmap64` (with `MAP_STACK` on Linux), where `sigstack_size = libc::SIGSTKSZ.max(getauxval(AT_MINSIGSTKSZ))` on Linux (supporting ARM64 SVE / x86 AMX dynamic signal frames), protects the lowest page with `PROT_NONE`, and registers `sigaltstack`.
3. **Windows `SetThreadStackGuarantee` and Vectored Exception Handler (`library/std/src/sys/pal/windows/stack_overflow.rs:7-41`):**
   - Both `stack_overflow::init()` (main thread, called from `rt::init`) and `thread_start` (`sys/thread/windows.rs:56`) call `SetThreadStackGuarantee(&mut 0x5000)` (`20,480` bytes = five `4 KiB` pages), ensuring that when the thread touches the OS `PAGE_GUARD` page at the bottom of its reserved stack and the OS cannot commit another page, at least `0x5000` bytes of stack remain mapped for `vectored_handler` to format and print `thread '...' (...) has overflowed its stack` when `ExceptionCode == EXCEPTION_STACK_OVERFLOW` (`0xC00000FD`).

### 4. LLVM vs. Cranelift Stack Frame Sizes and Recursion Depth Bounds

Basis: execution

Compiling the 5-function benchmark in `support/clif_vs_llvm_corpus.rs` on `x86_64-unknown-linux-gnu` with `rustc 1.99.1` (LLVM), `nightly-2026-11-12` (LLVM), and `nightly-2026-11-12 -Zcodegen-backend=cranelift` at both `-C opt-level=0` and `-C opt-level=2` yields the following total per-activation stack consumption (including the 8-byte pushed `RIP` return address):

| Function | LLVM `1.99.1` (`opt=0`) | LLVM `n1112` (`opt=0`) | Cranelift `n1112` (`opt=0`) | `opt=0` Ratio (CLIF / LLVM) | LLVM `1.99.1` (`opt=2`) | LLVM `n1112` (`opt=2`) | Cranelift `n1112` (`opt=2`) | `opt=2` Ratio (CLIF / LLVM) | Max Recursion Depth in `2 MiB` (`opt=2`, LLVM vs. CLIF) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `ackermann(m, n)` | `64 B` | `64 B` | `32 B` | `0.50x` | `32 B` (`3` pushes + `ret`) | `32 B` | `32 B` (`push %rbp` + `sub $16, %rsp`) | `1.00x` | `65,536` vs. `65,536` frames |
| `crc32c_step(acc, ptr, len)` | `96 B` | `96 B` | `64 B` | `0.67x` | `8 B` (frameless leaf) | `8 B` | `16 B` (`push %rbp; mov %rsp, %rbp`) | `2.00x` | Leaf (non-recursive) |
| `fib_tree_with_locals(n, [u64; 4])` | `176 B` | `176 B` | `160 B` | `0.91x` | `96 B` (`3` pushes + `sub $64, %rsp`) | `96 B` | `128 B` (`push %rbp` + `sub $112, %rsp`) | `1.33x` | `21,845` vs. `16,384` frames |
| `format_and_drop_frame(x, y)` | `192 B` | `192 B` | `176 B` | `0.92x` | `96 B` (`sub $88, %rsp`) | `96 B` | `304 B` (`push %rbp` + `sub $288, %rsp`) | `3.17x` | `21,845` vs. `6,898` frames |
| `recursive_parser_step(depth, &[u8])` | `400 B` | `400 B` | `400 B` | `1.00x` | `176 B` (`2` pushes + `sub $152, %rsp`) | `176 B` | `416 B` (`push %rbp` + `sub $400, %rsp`) | `2.36x` | `11,915` vs. `5,041` frames |

- **Why Cranelift is smaller at `opt-level=0` (`0.50x..1.00x`) but larger at `opt-level=2` (`1.00x..3.17x`):** At `opt-level=0`, LLVM's FastISel spills every SSA virtual register and debug/temporary copy across basic blocks without stack-slot coloring, whereas Cranelift only allocates stack slots for explicit `StackSlot` MIR locals plus register-allocator spills. At `opt-level=2`, LLVM's `StackColoring` pass merges disjoint `StorageLive`/`StorageDead` MIR locals and elides the frame pointer on `x86_64-unknown-linux-gnu`, whereas `rustc_codegen_cranelift` currently keeps separate stack slots for temporary `format_args!` / `Result` lowering structures and always emits a frame-pointer prologue (`pushq %rbp; movq %rsp, %rbp`).
- **Implication for a verified compiler specification:** Because Rust's language specification (FLS / Reference) does not fix stack frame sizes, recursion depth before stack overflow is an implementation-defined resource limit that already varies by up to **$3.17\times$** between in-tree `rustc` backends at `-C opt-level=2`. A verified backend can guarantee **exact absence of stack overflow** for any bounded call graph by emitting `.stack_sizes` (`-Z emit-stack-sizes`, preserved in `support/stack_*.s`) and checking the call-graph max-weight path against the thread stack reservation, as formalized in `regalloc2-symbolic-checker-stacking-and-quantitative-stack-bounds-2026`.

## Boundaries

- **Dynamic `alloca` (`llvm.stacksave` / `llvm.stackrestore` / `inlineStackProbeDyn`):** Safe Rust does not emit variable-length stack allocations (`MFI.hasVarSizedObjects()` is false unless `alloca` intrinsics or unsized rvalue placement features are used), so all standard Rust stack probes use fixed prologue sizes (`inlineStackProbeFixed`).
- **Hardware shadow stacks (Intel CET `SHSTK` / AArch64 `GCS`):** Not enabled by default on any of the 8 Tier 1 target specifications in `rustc 1.99.1`.

## Evidence

### Primary Upstream Sources

- `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):
  - `compiler/rustc_codegen_llvm/src/attributes.rs:200-223, 338-369` (`frame_pointer_type_attr`, `probestack_attr`).
  - `library/std/src/sys/pal/unix/stack_overflow.rs:101-621` and `stack_overflow/thread_info.rs` (Unix `SIGSEGV`/`SIGBUS` handler, `sigaltstack`, `AT_MINSIGSTKSZ`, Linux vs. macOS main-thread and spawned-thread guard pages).
  - `library/std/src/sys/pal/windows/stack_overflow.rs:6-41` (`SetThreadStackGuarantee(&mut 0x5000)`, `AddVectoredExceptionHandler`, `EXCEPTION_STACK_OVERFLOW`).
  - `library/std/src/sys/thread/unix.rs:31, 48-127` and `windows.rs:14, 20-61` (`DEFAULT_MIN_STACK_SIZE = 2 * 1024 * 1024`, thread startup stack overflow handler installation).
  - `library/std/src/thread/lifecycle.rs:37-39` (`RUST_MIN_STACK`).
- `rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`LLVM 23.1.1`):
  - `llvm/lib/Target/AArch64/AArch64FrameLowering.cpp:538-563, 704-720, 897-905, 3797-3931` (`canUseRedZone`, `StackProbeMaxUnprobedStack = 1024`, `windowsRequiresStackProbe`, `inlineStackProbeFixed`).
  - `llvm/lib/Target/X86/X86FrameLowering.cpp:725-920` (`emitStackProbeInlineGeneric`, `emitStackProbeInlineGenericBlock`, `emitStackProbeInlineGenericLoop`, `ProbeChunk = StackProbeSize * 8`).

### Preserved Package Support Artifacts

- `support/stack_probe.rs`: Probe exercising leaf red-zone usage (`redzone_leaf`), `3 KiB` / `8 KiB` / `70 KiB` frames (`frame_3k`, `frame_8k`, `frame_70k`), and 64-byte dynamic stack realignment (`overaligned_frame`).
- `support/stack_x86_64-unknown-linux-gnu.s`, `support/stack_aarch64-unknown-linux-gnu.s`, `support/stack_i686-unknown-linux-gnu.s`, `support/stack_aarch64-apple-darwin.s`, `support/stack_x86_64-pc-windows-msvc.s`, `support/stack_aarch64-pc-windows-msvc.s`, `support/stack_i686-pc-windows-msvc.s`, `support/stack_x86_64-pc-windows-gnu.s`: Generated assembly (with `-Z emit-stack-sizes` on ELF targets) across all 8 Tier 1 targets.
- `support/clif_vs_llvm_corpus.rs`: 5-function benchmark comparing LLVM (`1.99.1` and `nightly-2026-11-12`) against Cranelift (`nightly-2026-11-12 -Zcodegen-backend=cranelift`) stack frame sizes.

## Revalidation

```bash
# 1. Verify inline stack probes and .stack_sizes across x86_64 and aarch64 Linux
for t in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu; do
  rustc +nightly-2026-11-12 --target "$t" --edition=2021 --crate-type=rlib -C opt-level=2 \
    -Z emit-stack-sizes --emit=asm="/tmp/stack_${t}.s" \
    reports/rust-stack-discipline-probes-red-zones-and-overflow/support/stack_probe.rs
  grep -E "frame_3k:|frame_8k:|frame_70k:|sub.*sp|ldr.*xzr|movq.*\\(%rsp\\)" "/tmp/stack_${t}.s" | head -n 20
done

# 2. Compare LLVM vs. Cranelift frame sizes on x86_64-unknown-linux-gnu
rustc +nightly-2026-11-12 --edition=2021 --crate-type=rlib -C opt-level=2 \
  --emit=obj=/tmp/corpus_llvm.o reports/rust-stack-discipline-probes-red-zones-and-overflow/support/clif_vs_llvm_corpus.rs
rustc +nightly-2026-11-12 -Zcodegen-backend=cranelift --edition=2021 --crate-type=rlib -C opt-level=2 \
  --emit=obj=/tmp/corpus_clif.o reports/rust-stack-discipline-probes-red-zones-and-overflow/support/clif_vs_llvm_corpus.rs
```
