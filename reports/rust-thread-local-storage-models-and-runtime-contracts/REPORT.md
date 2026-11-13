# Thread-Local Storage Models, Access Sequences, Linker Relaxations, and Destructor Contracts Across Tier 1 Targets

## Summary

A verified drop-in replacement for `rustc` targeting the 8 Tier 1 platforms must implement two distinct standard-library `thread_local!` lowering strategies (`target_thread_local = true` on 7 targets vs. `target_thread_local = false` on `x86_64-pc-windows-gnu`), four architecture/OS native TLS access mechanisms, and three OS-specific thread-exit destructor registration contracts:

1. **Seven-Target Native `#[thread_local]` vs. `x86_64-pc-windows-gnu` OS-Key TLS (`library/std/src/sys/thread_local/mod.rs:36-58`, `tier1_target_specs_1991`):** Seven of the eight Tier 1 targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `aarch64-pc-windows-msvc`, `i686-pc-windows-msvc`) set `has_thread_local: true`. On those seven targets, `thread_local!` selects one of four `#[thread_local]` storage representations (`library/std/src/sys/thread_local/native/mod.rs:7-111`): bare `T` (`const` + `!needs_drop::<T>()`), `EagerStorage<T>` (`const` + `needs_drop::<T>()`), `LazyStorage<T, !>` (lazy + `!needs_drop::<T>()`), or `LazyStorage<T, ()>` (lazy + `needs_drop::<T>()`). On `x86_64-pc-windows-gnu`, `has_thread_local` is `false`: `thread_local!` lowers to `os::Storage<T, ALIGN>` (`library/std/src/sys/thread_local/os.rs:79-223`) backed by a global `LazyKey` (`TlsAlloc` / `TlsGetValue` / `TlsSetValue` + `InitOnceBeginInitialize`) and a heap-allocated `AlignedSystemBox<T, ALIGN>` allocated via `std::alloc::System` to support over-aligned thread-locals without touching the user `#[global_allocator]`.
2. **Compiler TLS Model Selection (`compiler/rustc_session/src/session.rs:963-965`, `compiler/rustc_codegen_llvm/src/context.rs:170-176, 669`, `consts.rs:413-415, 542-544`):** All 8 Tier 1 targets default to `TlsModel::GeneralDynamic` in their target specifications (`compiler/rustc_target/src/spec/mod.rs:2879`), overridable via `-Z tls-model={global-dynamic,local-dynamic,initial-exec,local-exec,emulated}`. `rustc_codegen_llvm` stamps `self.tls_model` onto every `#[thread_local]` global via `LLVMSetThreadLocalMode`; LLVM's target lowering then narrows `GeneralDynamic` to `LocalDynamic`, `InitialExec`, or `LocalExec` based on `dso_local`, linkage, `-C relocation-model`, and target format (with COFF and Mach-O ignoring ELF dynamic models in favor of `_tls_index` and `__thread_vars`, respectively).
3. **Target-Specific Native TLS Access Sequences (`support/tls_*.s`):**
   - **Linux ELF (`x86_64`, `aarch64`, `i686`):** In default PIC mode (`GeneralDynamic`), `x86_64` emits the 16-byte padded `data16; leaq sym@TLSGD(%rip), %rdi; data16; data16; rex64; callq __tls_get_addr@PLT` sequence; `i686` emits `leal sym@TLSGD(,%ebx), %eax; calll ___tls_get_addr@PLT`; and `aarch64` emits **TLSDESC** (`adrp x0, :tlsdesc:sym; ldr x1, [x0, :tlsdesc_lo12:sym]; add x0, x0, :tlsdesc_lo12:sym; .tlsdesccall sym; blr x1; mrs x23, TPIDR_EL0; ldr x8, [x23, x0]`). Under `initial-exec` and `local-exec`, accesses index directly off `%fs:0` (`x86_64`), `TPIDR_EL0` (`aarch64`), or `%gs:0` (`i686`).
   - **macOS (`aarch64-apple-darwin`):** Every TLS variable emits a 24-byte descriptor `[__tlv_bootstrap, 0, sym$tlv$init]` in `__DATA,__thread_vars`, an initializer in `__DATA,__thread_data` (or zero-initialized `__DATA,__thread_bss`), and accesses the variable via `adrp x0, sym@TLVPPAGE; ldr x0, [x0, sym@TLVPPAGEOFF]; ldr x8, [x0]; blr x8` (`tlv_get_addr`, which preserves all registers except `x0`, `x16`, `x17`, and `cc`).
   - **Windows MSVC (`x86_64`, `aarch64`, `i686`):** TLS variables are emitted in `.tls$` COMDAT sections and accessed via `_tls_index` and the TEB `ThreadLocalStoragePointer` (`%gs:88` on x64, `[x18, #88]` on ARM64, `%fs:__tls_array` = `%fs:0x2c` on i686) plus `sym@SECREL32` (`:secrel_hi12:` + `:secrel_lo12:` on ARM64).
4. **Destructor Registration Contracts (`library/std/src/sys/thread_local/{destructors,guard}/`):**
   - **Linux (`destructors/linux_like.rs:15-54`):** Weakly links `__cxa_thread_atexit_impl` and `__dso_handle`; when present (glibc $\ge 2.18$), registers `(dtor, ptr, &__dso_handle)` directly with libc so `dlclose` is prevented while a thread holds a live destructor, falling back to `destructors/list.rs` + a `pthread_key_create` guard (`guard/key.rs:8-31`) on older libc.
   - **macOS (`guard/apple.rs:9-31`):** Because calling `_tlv_atexit` while TLS destructors are already running is undefined behavior in `dyld`, `std` pushes all TLS destructors onto its own thread-local `DTORS: RefCell<Vec<(*mut u8, unsafe extern "C" fn(*mut u8)), System>>` (`destructors/list.rs:5-46`) and registers a single `_tlv_atexit(run_dtors, null)` callback per thread via `#[thread_local] static REGISTERED: Cell<bool>`.
   - **Windows (`guard/windows.rs:21-273`):** Rather than using static PE `.CRT$XL*` `PIMAGE_TLS_CALLBACK` entries (which the Windows loader skips for dynamically loaded DLLs), `std` allocates a process-wide Fiber-Local Storage slot via `FlsAlloc(Some(cleanup))`, sets `FlsSetValue(key, 1)` on each non-fiber thread (`!IsThreadAFiber()`), and—when `cleanup` resides in a DLL (`GetModuleHandleExW(cleanup) != GetModuleHandleW(null)`)—registers `atexit(free_fls_key_at_exit)` guarded by a `SeqCst` Dekker protocol (`ACTIVE_ENABLE_CALLS` vs. `AT_EXIT_HOOK_CALLED`) so `FlsFree` drains destructors on DLL unload without `STATUS_ACCESS_VIOLATION`.

## Applicability

These findings apply to `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), its bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) across all 8 Tier 1 targets.

## Findings

### 1. `thread_local!` Storage State Machines and Layout Invariants

Basis: source + execution

On the 7 Tier 1 targets with `target_thread_local = true`, `std::thread::local_impl::thread_local_inner!` (`library/std/src/sys/thread_local/native/mod.rs:51-111`) selects the underlying `#[thread_local]` static representation at compile time using `const { core::mem::needs_drop::<T>() }` and whether the initializer is `const { ... }`:

| Initializer Kind | `needs_drop::<T>() == false` | `needs_drop::<T>() == true` | ELF / COFF / Mach-O Section (`support/tls_*.s`) |
| :--- | :--- | :--- | :--- |
| `const { ... }` | Bare `#[thread_local] static VAL: T = INIT;` (`8 B` for `u64`, no state byte) | `EagerStorage<T>` (`#[repr(C)] { val: UnsafeCell<T>, state: Cell<State> }`, `16 B` for `u64`, `state` initialized to `State::Unregistered = 1` at offset `+8`) | `.tdata.<sym>` / `.tls$` / `__DATA,__thread_data` (`__thread_bss` if all-zero) |
| Lazy expression | `LazyStorage<T, !>` (`#[repr(C)] { value: UnsafeCell<MaybeUninit<T>>, state: Cell<State<!>> }`, `16 B` for `u64`, `state = Uninitialized (0)` at offset `+8`) | `LazyStorage<T, ()>` (`#[repr(C)] { value: UnsafeCell<MaybeUninit<T>>, state: Cell<State<()>> }`, `16 B` for `u64`, `state = Uninitialized (0)` at offset `+8`) | `.tbss.<sym>` / `.tls$` / `__DATA,__thread_bss` |

Critical semantic invariants enforced by `native/{eager.rs,lazy.rs}` and `mod.rs:25-34`:
1. **`val` / `value` is always placed at offset `0` (`#[repr(C)]`):** Both `EagerStorage<T>` (`eager.rs:13-18`) and `LazyStorage<T, D>` (`lazy.rs:30-35`) place `val`/`value` as the *first* field before `state` so that `#[rustc_align_static(N)]` on the enclosing static aligns the inner `T` directly at offset `0`.
2. **`EagerStorage<T>` discriminant encoding (`eager.rs:6-10`):** `enum State { Alive = 0, Unregistered = 1, Destroyed = 2 }`. Because `Alive = 0`, the fast path `if let State::Alive = self.state.get()` compiles to a single `ldrb w8, [x0, #8]; cbnz w8, slow_path` (`support/tls_aarch64-apple-darwin.s:45-46`) or `movzbl 8(%rax), %ecx; testl %ecx, %ecx; jne slow_path` (`support/tls_x86_64-unknown-linux-gnu.s:44-45`). In `.tdata`, `CONST_DROP` (`HasDrop(99)`) is emitted as `.ascii "c\0\0\0\0\0\0\0\x01"; .zero 7` (`99` in little-endian `u64` followed by `1 = Unregistered`).
3. **Reentrant initialization and panic-on-drop guards (`lazy.rs:87-99, 112-124`, `mod.rs:218-233`):** If a lazy initializer reentrantly initializes the same `thread_local!`, `self.state.replace(State::Alive)` observes `State::Alive` and drops the newly overwritten `old_value` without registering a duplicate destructor (`lazy.rs:96`). During thread teardown, both `eager::destroy` and `lazy::destroy` set `state = State::Destroyed` *before* calling `drop_in_place` (so reentrant `LocalKey::try_with` returns `Err(AccessError)` instead of aliasing `&mut T`) and wrap `drop_in_place` in `abort_on_dtor_unwind` (`rtabort!("thread local panicked on drop")`).
4. **No-allocator invariant (`mod.rs:25-34`, `destructors/list.rs:5-19`):** TLS access and destructor registration forbid calling the user `#[global_allocator]` (which may itself access TLS); `DTORS` in `list.rs` explicitly uses `Vec<..., std::alloc::System>` and calls `try_reserve(1)` with `rtabort!` on failure rather than invoking the alloc error hook.

### 2. Native TLS Access Sequences, Relocations, and Linker Relaxations Across All 8 Targets

Basis: normative + source + execution

Compiling `support/tls_probe.rs` across all 8 Tier 1 targets and across `-Z tls-model={global-dynamic,initial-exec,local-exec}` (`support/tls_*.s`) establishes the exact instruction sequences and relocations required from a backend:

| Target & Mode | Thread Pointer Base | Generated Instruction Sequence (`support/tls_*.s`) | Assembler Relocation Modifiers | Linker Relaxation Capabilities |
| :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` (`global-dynamic`, default) | `%fs:0` (Variant II, negative offsets from TCB) | `data16; leaq sym@TLSGD(%rip), %rdi; data16; data16; rex64; callq __tls_get_addr@PLT` | `R_X86_64_TLSGD` + `R_X86_64_PLT32` | GD $\to$ IE (`movq %fs:0, %rax; addq sym@GOTTPOFF(%rip), %rax`) or GD $\to$ LE (`movq %fs:0, %rax; leaq sym@TPOFF(%rax), %rax`); requires exact `0x66` / `0x66 0x66 0x48` prefix padding! |
| `x86_64-unknown-linux-gnu` (`initial-exec`) | `%fs:0` | `movq sym@GOTTPOFF(%rip), %rax; movq %fs:(%rax), %r14` | `R_X86_64_GOTTPOFF` | IE $\to$ LE (`leaq sym@TPOFF(%rax), ...` or `movq $sym@TPOFF, %rax`) when linking an executable |
| `x86_64-unknown-linux-gnu` (`local-exec`) | `%fs:0` | `movq %fs:sym@TPOFF, %r14` (or `movq %fs:0, %rcx; leaq sym@TPOFF(%rcx), %rcx`) | `R_X86_64_TPOFF32` | Already static offset |
| `aarch64-unknown-linux-gnu` (`global-dynamic` / TLSDESC, default) | `TPIDR_EL0` (Variant I, positive offsets after 16-B TCB) | `adrp x0, :tlsdesc:sym; ldr x1, [x0, :tlsdesc_lo12:sym]; add x0, x0, :tlsdesc_lo12:sym; .tlsdesccall sym; blr x1; mrs x23, TPIDR_EL0; ldr x8, [x23, x0]` | `R_AARCH64_TLSDESC_ADR_PAGE21`, `R_AARCH64_TLSDESC_LD64_LO12`, `R_AARCH64_TLSDESC_ADD_LO12`, `R_AARCH64_TLSDESC_CALL` | GD (TLSDESC) $\to$ IE (`adrp x0, :gottprel:sym; ldr x0, [x0, :gottprel_lo12:sym]; nop; nop`) or GD $\to$ LE (`movz x0, #:tprel_g1:sym; movk x0, #:tprel_g0_nc:sym; nop; nop`) gated by `.tlsdesccall` |
| `aarch64-unknown-linux-gnu` (`initial-exec`) | `TPIDR_EL0` | `adrp x9, :gottprel:sym; ldr x9, [x9, :gottprel_lo12:sym]; mrs x23, TPIDR_EL0; ldr x12, [x23, x9]` | `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21`, `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC` | IE $\to$ LE (`movz` + `movk`) |
| `aarch64-unknown-linux-gnu` (`local-exec`) | `TPIDR_EL0` | `mrs x23, TPIDR_EL0; add x8, x23, :tprel_hi12:sym; add x9, x8, :tprel_lo12_nc:sym; ldr x10, [x9]` | `R_AARCH64_TLSLE_ADD_TPREL_HI12`, `R_AARCH64_TLSLE_ADD_TPREL_LO12_NC` | Already static offset |
| `i686-unknown-linux-gnu` (`global-dynamic`, default) | `%gs:0` (Variant II, negative offsets from TCB) | `leal sym@TLSGD(,%ebx), %eax; calll ___tls_get_addr@PLT` (3-underscore `___tls_get_addr` `regparm(1)` in `%eax`!) | `R_386_TLS_GD`, `R_386_PLT32` | GD $\to$ IE (`movl %gs:0, %eax; addl sym@GOTNTPOFF(%ebx), %eax`) or GD $\to$ LE (`movl %gs:0, %eax; leal sym@NTPOFF(%eax), %eax`) |
| `i686-unknown-linux-gnu` (`initial-exec` / `local-exec`) | `%gs:0` | IE: `movl sym@GOTNTPOFF(%ebx), %eax; movl %gs:(%eax), %edi`<br>LE: `movl %gs:sym@NTPOFF, %edi` | `R_386_TLS_GOTIE` (`@GOTNTPOFF`), `R_386_TLS_LE` (`@NTPOFF`) | IE $\to$ LE |
| `aarch64-apple-darwin` (all `-Z tls-model` values) | Hidden inside `dyld` `tlv_get_addr` | `adrp x0, sym@TLVPPAGE; ldr x0, [x0, sym@TLVPPAGEOFF]; ldr x8, [x0]; blr x8` | `ARM64_RELOC_TLVP_LOAD_PAGE21`, `ARM64_RELOC_TLVP_LOAD_PAGEOFF12` (with `Lloh` linker optimization hints) | Linker may relax `@TLVPPAGE` + `ldr` to `add` if `__thread_vars` is within $\pm 4\text{ MiB}$, but `-Z tls-model` has no effect |
| `x86_64-pc-windows-msvc` (all `-Z tls-model` values) | `%gs:88` (`TEB.ThreadLocalStoragePointer` at `0x58`) | `movl _tls_index(%rip), %ecx; movq %gs:88, %rdx; movq (%rdx,%rcx,8), %rdx; leaq sym@SECREL32(%rdx), %rcx` | `IMAGE_REL_AMD64_REL32` (`_tls_index`), `IMAGE_REL_AMD64_SECREL` (`@SECREL32`) | None (implicit PE TLS via `_tls_used`) |
| `aarch64-pc-windows-msvc` (all `-Z tls-model` values) | `[x18, #88]` (`TEB` in `x18` + `0x58`) | `adrp x23, _tls_index; ldr x9, [x18, #88]; ldr w8, [x23, :lo12:_tls_index]; ldr x8, [x9, x8, lsl #3]; add x9, x8, :secrel_hi12:sym; ldr x10, [x9, :secrel_lo12:sym]` | `IMAGE_REL_ARM64_SECREL_HIGH12A`, `IMAGE_REL_ARM64_SECREL_LOW12A` (or `LOW12L`) | None |
| `i686-pc-windows-msvc` (all `-Z tls-model` values) | `%fs:__tls_array` (`%fs:0x2c`, `TEB + 44`) | `movl __tls_index, %eax; movl %fs:__tls_array, %ecx; movl (%ecx,%eax,4), %ecx; movl _sym@SECREL32(%ecx), %edi` | `IMAGE_REL_I386_DIR32` (`__tls_index`), `IMAGE_REL_I386_SECREL` (`@SECREL32`) | None |
| `x86_64-pc-windows-gnu` (`target_thread_local = false`) | OS TLS via `TlsGetValue` (`TEB.TlsSlots` / `TlsExpansionSlots`) | `#[thread_local]` rejected (`E0658` / target lacks support); `thread_local!` calls `guard::windows::enable()`, loads `LazyKey.key - 1`, and calls `TlsGetValue(%ecx)` | Standard COFF x64 calls | None |

**Three non-obvious instruction-level details a verified backend must preserve:**
1. **AArch64 Linux TLSDESC calling convention (`support/tls_aarch64-unknown-linux-gnu.s:21-25`):** Unlike `__tls_get_addr` on x86_64 (which is a normal SysV C call clobbering all caller-saved registers), the AArch64 TLSDESC resolver function (`blr x1` at `[x0]`, where `x0` points to the 16-byte GOT descriptor `[resolver_fn, arg]`) returns the thread-pointer offset in `x0` and **is required by the ABI to preserve all general-purpose and SIMD registers except `x0` and `cc` (`NZCV`)**! Furthermore, the `.tlsdesccall sym` directive must immediately precede `blr x1` so `ld`/`lld` can replace `blr x1` with `nop` during GD $\to$ IE/LE relaxation.
2. **macOS `tlv_get_addr` calling convention (`support/tls_aarch64-apple-darwin.s:21-38`):** Each variable's 24-byte `TLVDescriptor` in `__DATA,__thread_vars` contains `[thunk_ptr, pthread_key_t, offset]`. Initially `thunk_ptr` is `_tlv_bootstrap`; the dynamic linker replaces `thunk_ptr` with `_tlv_get_addr` and allocates a shared `pthread_key_t` for the Mach-O image. Calling `blr x8` (`_tlv_get_addr`) with `x0 = &TLVDescriptor` returns the thread-specific variable address in `x0` and **preserves all registers except `x0`, `x16`, `x17`, and `cc`**.
3. **32-bit i686 Linux `___tls_get_addr` ABI (`support/tls_i686-unknown-linux-gnu.s:259-260`):** On `i686-unknown-linux-gnu`, the dynamic resolver is spelled with **three** leading underscores (`___tls_get_addr@PLT`), takes its `tls_index*` argument in **`%eax`** (`__attribute__((regparm(1)))`, not on the stack), and requires `%ebx` to hold `_GLOBAL_OFFSET_TABLE_`.

### 3. Over-Aligned Thread-Locals (`align(64)`) and `dylib` / `cdylib` Constraints

Basis: source + execution

1. **Native TLS over-alignment (`support/tls_probe.rs:10-15`):** In `tls_probe.rs`, `RAW_TLS_ALIGN64` has `#[repr(align(64))]`. Across all 7 native-TLS targets, LLVM emits `.p2align 6, 0x0` ($2^6 = 64$ bytes) on the `.tdata` / `.tbss` / `__DATA,__thread_data` / `.tls$` section:
   - On ELF (`x86_64`, `aarch64`, `i686`), `.p2align 6` sets `p_align = 64` on the `PT_TLS` program header (`sh_addralign = 64`). Both `glibc` (`_dl_allocate_tls_storage`) and musl honor arbitrary power-of-two `PT_TLS.p_align` values for both static and `dlopen`-loaded modules.
   - On `aarch64-apple-darwin`, `__DATA,__thread_data` receives `.p2align 6, 0x0`, and `dyld` allocates each image's TLV buffer using `posix_memalign` with the maximum alignment of `__thread_data` / `__thread_bss`.
   - On Windows MSVC (`x86_64`, `aarch64`, `i686`), `.section .tls$,"dw",one_only,...` receives `.p2align 6, 0x0` (`IMAGE_SCN_ALIGN_64BYTES`), which sets `Alignment` in the PE `IMAGE_TLS_DIRECTORY` (`_tls_used`). On Windows 10 1809+ (`ntdll!LdrpAllocateTlsEntry`), the loader honors `IMAGE_TLS_DIRECTORY` alignment up to page size.
2. **OS-Key TLS over-alignment on `x86_64-pc-windows-gnu` (`library/std/src/sys/thread_local/os.rs:31-73, 98-153`):** Because `TlsAlloc` only stores a single pointer (`LPVOID`), `os::thread_local_inner!` parses `#[rustc_align_static(N)]` at compile time into the const generic `ALIGN` of `os::Storage<T, ALIGN>` and allocates `Value<T>` on the heap via `System.alloc(Layout::new::<Value<T>>().align_to(ALIGN))`.
3. **TLS in `dylib` and `cdylib` crates:**
   - **Linux ELF (`destructors/linux_like.rs:27-49`):** Passing `&raw const __dso_handle` as the third argument to `__cxa_thread_atexit_impl` causes `glibc` to increment the DSO's `l_tls_dtor_count` refcount, preventing `dlclose` from unmapping a `cdylib`'s code segment while any thread still has registered TLS destructors inside that `cdylib`.
   - **Windows DLLs (`guard/windows.rs:146-249`, `tier1_target_specs_1991.txt:133, 173, 213, 249`):** All four Windows Tier 1 target specs set `dll-tls-export: false` (`compiler/rustc_target/src/spec/base/windows_msvc.rs`), because PE DLLs cannot export implicit `.tls$` variables across DLL boundaries (`__declspec(dllimport)` on `_tls_index` is not supported across dynamic crates). Furthermore, prior to Windows Vista, the OS loader ignored implicit `.tls$` in `LoadLibrary`-loaded DLLs; on Windows 10+ (Rust's Tier 1 baseline), `ntdll` dynamically allocates `_tls_index` slots on `LoadLibrary`, and `std`'s `guard/windows.rs` detects when `std` is linked into a DLL (`cleanup_is_unloadable() == true`) and registers `atexit(free_fls_key_at_exit)` so `FreeLibrary` invokes `FlsFree(current_key)` and runs the unloading thread's TLS destructors before the DLL is unmapped.

## Boundaries

- **`TlsModel::Emulated` (`__emutls_get_address`):** Inspected in `compiler/rustc_codegen_llvm/src/back/write.rs:236` and `compiler/rustc_target/src/spec/base/{android.rs,openbsd.rs,cygwin.rs}`, where `rustc` enables LLVM's `-emulated-tls` pass, but not used by default on any of the 8 Tier 1 targets.
- **Runtime `dlopen` / `LoadLibrary` stress testing of TLS exhaustion:** Static code generation and object relocations were verified across all 8 Tier 1 targets; runtime exhaustion of glibc static TLS surplus (`DL_TLS_STATIC_SURPLUS`) or Windows `FLS_MAXIMUM_AVAILABLE` (`4080` slots on Windows 10 1903+) is bounded by the host OS loader rather than compiler code generation.

## Evidence

### Primary Upstream Sources

- `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):
  - `library/std/src/sys/thread_local/mod.rs:36-233` (dispatch between `no_threads`, `native`, and `os`; `destructors`, `guard`, `key`, and `abort_on_dtor_unwind`).
  - `library/std/src/sys/thread_local/native/mod.rs:1-139`, `eager.rs:1-81`, `lazy.rs:1-124` (the four native `#[thread_local]` storage representations and state machines).
  - `library/std/src/sys/thread_local/os.rs:1-274` (`Storage<T, ALIGN>`, `AlignedSystemBox<T, ALIGN>`, `destroy_value`).
  - `library/std/src/sys/thread_local/destructors/linux_like.rs:15-55` (`__cxa_thread_atexit_impl` and `__dso_handle`) and `list.rs:5-46` (`DTORS` `RefCell<Vec<..., System>>`).
  - `library/std/src/sys/thread_local/guard/apple.rs:9-32` (`_tlv_atexit`), `guard/windows.rs:19-273` (`FlsAlloc`, `EnableGuard`, `cleanup_is_unloadable`, `free_fls_key_at_exit`), and `guard/key.rs:8-60` (Unix fallback key).
  - `library/std/src/sys/thread_local/key/windows.rs:34-220` (`LazyKey`, `InitOnceBeginInitialize`, `TlsAlloc`, 5-round `run_dtors` loop).
  - `compiler/rustc_codegen_llvm/src/context.rs:170-176, 669` and `consts.rs:413-415, 542-544` (`to_llvm_tls_model` and `LLVMSetThreadLocalMode`).
  - `compiler/rustc_session/src/session.rs:963-965` (`Session::tls_model`).

### Preserved Package Support Artifacts

- `support/tls_probe.rs`: Probe exercising raw `#[thread_local] u64`, over-aligned `#[repr(align(64))]` `#[thread_local]`, and all four `thread_local!` quadrants (`CONST_NODROP`, `CONST_DROP`, `LAZY_NODROP`, `LAZY_DROP`).
- `support/tls_x86_64-unknown-linux-gnu.s`, `support/tls_initial-exec_x86_64-unknown-linux-gnu.s`, `support/tls_local-exec_x86_64-unknown-linux-gnu.s`: x86_64 Linux assembly across `global-dynamic`, `initial-exec`, and `local-exec`.
- `support/tls_aarch64-unknown-linux-gnu.s`, `support/tls_initial-exec_aarch64-unknown-linux-gnu.s`, `support/tls_local-exec_aarch64-unknown-linux-gnu.s`: AArch64 Linux assembly across TLSDESC `global-dynamic`, `initial-exec`, and `local-exec`.
- `support/tls_i686-unknown-linux-gnu.s`, `support/tls_initial-exec_i686-unknown-linux-gnu.s`, `support/tls_local-exec_i686-unknown-linux-gnu.s`: i686 Linux assembly across `global-dynamic`, `initial-exec`, and `local-exec`.
- `support/tls_aarch64-apple-darwin.s`, `support/tls_x86_64-pc-windows-msvc.s`, `support/tls_aarch64-pc-windows-msvc.s`, `support/tls_i686-pc-windows-msvc.s`, `support/tls_x86_64-pc-windows-gnu.s`: Generated assembly for macOS and all four Windows Tier 1 targets.

## Revalidation

```bash
# Recompile tls_probe.rs across Linux TLS models and Tier 1 targets with nightly-2026-11-12
for model in global-dynamic initial-exec local-exec; do
  rustc +nightly-2026-11-12 --target aarch64-unknown-linux-gnu --edition=2021 --crate-type=rlib \
    -C opt-level=2 -Z tls-model="$model" --emit=asm="/tmp/tls_${model}_aarch64.s" \
    reports/rust-thread-local-storage-models-and-runtime-contracts/support/tls_probe.rs
  grep -E "tlsdesc|gottprel|tprel_hi12" "/tmp/tls_${model}_aarch64.s" | head -n 6
done
```
