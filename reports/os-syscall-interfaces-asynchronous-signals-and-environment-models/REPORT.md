# Operating-System Syscall Interfaces, Asynchronous Signals, and Formal Environment Models

## Summary

Modeling the execution environment of compiled Rust programs across Linux,
macOS, and Windows—and drafting the operating-system entries of the formal
assumption ledger—requires reconciling three platform realities with formal
compiler verification precedents (`CakeML`, `CompCert`, `seL4`, `SibylFS`, and
`Anneal`):

1. **Two distinct OS boundary regimes (Raw Kernel Syscalls vs. Mandatory System
   DLL/Dylib Entry Points):**
   - **Linux (`x86_64`, `aarch64`, `riscv64gc`):** Exposes a **stable kernel
     syscall ABI** (`syscall`, `svc #0`, `ecall`). Rust programs reach the
     kernel both through `libc.so.6` / `musl` (`library/std/src/sys/pal/unix/`)
     and via direct inline-assembly syscalls (`std::sys::pal::unix::weak::syscall!`
     in `library/std/src/sys/pal/unix/weak/syscall.rs` and ecosystem crates such
     as `rustix`'s default `linux_raw` backend). Consequently, a verified Rust
     compiler targeting Linux must model both external C ABI calls and inline-asm
     kernel traps.
   - **macOS (`libSystem.B.dylib`) and Windows (`kernel32.dll`, `ntdll.dll`,
     `api-ms-win-core-*`):** Explicitly **forbid direct user-space syscall
     instructions** (`svc #0x80` on Darwin; `syscall` in `ntdll.dll` on Windows)
     because kernel trap numbers change across OS point releases. Every OS
     interaction in `std` (`library/std/src/sys/pal/unix/` on Darwin and
     `library/std/src/sys/pal/windows/` on Windows, backed by the 3,704-line
     binding table in `library/std/src/sys/pal/windows/c/windows_sys.rs`)
     crosses a standard platform C/stdcall dynamic symbol boundary.
2. **Formal environment models in verified compilers (`CompCert` events,
   `CakeML` `call_FFI`, `SibylFS` POSIX traces):**
   Verified compilers never formalize the host OS kernel inside the compiler's
   correctness proof. Instead, they parameterize target machine semantics by an
   **external interaction oracle** ($\mathcal{E}$) and prove simulation up to
   observable I/O traces (`CompCert` `common/Events.v` `eventval` traces and
   `extcall_properties`; `CakeML` `semantics/ffi/` byte-slice `call_FFI`
   transitions) subject to an explicit **frame-preservation contract**: external
   calls may read/write only architectural argument buffers and global/escaped
   memory, and must preserve callee-saved registers, non-escaped stack slots,
   and read-only code/data sections.
3. **Asynchronous interrupts, signals, and stack-frame invariants:**
   Hardware interrupts are transparent to user-space architectural state, but OS
   user-space asynchronous deliveries—POSIX signals (`SIGSEGV`, `SIGBUS`,
   `SIGALRM`, `SIGPROF`) and Windows Structured Exception Handling (SEH /
   Vectored Exception Handling)—execute user-space handler code on the interrupted
   thread. To prevent asynchronous signal corruption without modeling preemptive
   interleaving at every machine instruction, compiled code must enforce four
   machine-level invariants at every instruction boundary:
   - **Never write below the architectural stack pointer `sp`**, *except* within
     the 128-byte System V AMD64 red zone (`[rsp - 128, rsp)`) in leaf functions
     when `-C no-redzone` is not set.
   - **Maintain 16-byte `sp` alignment** at every potentially faulting or
     interruptible instruction on `aarch64` (hardware `SP` alignment fault if
     misaligned during memory access), `riscv64gc`, and `x86_64-pc-windows-*`.
   - **Sequential 4 KiB stack probing (`__rust_probestack` / inline probe loops)**
     when allocating frames $> 4\text{ KiB}$ so stack growth cannot jump over
     the OS guard page (`library/std/src/sys/pal/unix/stack_overflow.rs`, 738
     lines; `library/std/src/sys/pal/windows/stack_overflow.rs`, 41 lines).
   - **Alternate signal stack (`sigaltstack` / `SA_ONSTACK`) assumption:**
     `std::sys::pal::unix::stack_overflow` registers `SIGSEGV`/`SIGBUS` handlers
     on a dedicated `sigaltstack` (`SIGSTKSZ`), which must be recorded in the
     assumption ledger so stack-overflow faults do not write into an exhausted
     stack.

## Applicability

This report governs the **Target Machine Environment Model** and the **OS /
Loader / Runtime Assumption Ledger** (`ENV-LOAD-1` through `ENV-ASYNC-5`) for a
verified Rust compiler targeting `rustc` `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) across Linux (`x86_64`, `aarch64`,
`riscv64gc`), macOS (`aarch64-apple-darwin`, `x86_64-apple-darwin`), and Windows
(`x86_64-pc-windows-msvc`/`-gnullvm`, `aarch64-pc-windows-msvc`/`-gnullvm`).

- **Relationship to prior corpus reports:** Extends
  `riscv64-elf64-relocations-lp64d-abi-and-linux-ecall-runtime-2026` (RISC-V
  `ecall` and ELF loader mechanics) and
  `anneal-tcb-realizability-external-calls-and-mutation-testing` (Anneal's
  external call specification boundary in `joshlf/anneal` at
  `9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`).

## Findings

### 1. How Rust Programs Reach the Operating System (`std` and Direct Syscalls)

`Basis: source (rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67 library/std/src/sys/)`

Inspection of `library/std/src/sys/` at `58cf8f9c35b355199727627d07ae34a4e2846d67`
shows how the Rust standard library and ecosystem crates cross the OS boundary on
each platform:

| Platform | Primary `std` Modules (`library/std/src/sys/...`) | Boundary Mechanism | Direct Kernel Trap Usage (`syscall` / `svc` / `ecall`) |
| :--- | :--- | :--- | :--- |
| **Linux (`*-unknown-linux-gnu`, `*-musl`)** | `pal/unix/mod.rs` (387 lines), `pal/unix/stack_overflow.rs` (738 lines), `pal/unix/weak/syscall.rs` (19 lines), `pal/unix/weak/dlsym.rs` (104 lines), `alloc/unix.rs` (103 lines) | C ABI calls to `libc.so.6` / `musl` (`malloc`, `posix_memalign`, `free`, `read`, `write`, `mmap`, `sigaltstack`, `pthread_*`), plus `weak::syscall!` fallback for `getrandom`, `statx`, `clone3`, and `futex` (`pal/unix/sync/mutex.rs`, `condvar.rs`, `thread_parking.rs`). | **Yes, supported and widespread:** `rustix` (used by `cargo`, `fd`, `ripgrep`, `tokio`) defaults on Linux to its `linux_raw` backend, issuing raw kernel traps via `core::arch::asm!` without `libc`. |
| **macOS (`*-apple-darwin`)** | `pal/unix/mod.rs`, `pal/unix/stack_overflow.rs`, `pal/unix/time.rs` (231 lines), `alloc/unix.rs` | Dynamic C ABI calls into `/usr/lib/libSystem.B.dylib` (`libsystem_kernel.dylib`, `libsystem_c.dylib`, `libsystem_malloc.dylib`, `libsystem_pthread.dylib`). | **Prohibited:** Darwin kernel trap numbers (`svc #0x80` on AArch64, `syscall` with class `0x2000000` on x86_64) are private to `libSystem.B.dylib` and rejected by App Store / notarization checks. |
| **Windows (`*-pc-windows-msvc`, `*-gnu`, `*-gnullvm`)** | `pal/windows/mod.rs` (296 lines), `pal/windows/api.rs` (366 lines), `pal/windows/c/windows_sys.rs` (3,704 lines), `pal/windows/handle.rs` (362 lines), `pal/windows/stack_overflow.rs` (41 lines), `alloc/windows.rs` (218 lines) | PE32+ import table calls into `kernel32.dll` (`GetProcessHeap`, `HeapAlloc`, `HeapReAlloc`, `HeapFree`, `VirtualAlloc`, `CreateFileW`, `AddVectoredExceptionHandler`), `bcryptprimitives.dll` (`ProcessPrng`), `ws2_32.dll`, and `api-ms-win-core-synch-l1-2-0.dll` (`WaitOnAddress`, `WakeByAddressSingle`). | **Prohibited:** Windows NT system service numbers (`eax` in `ntdll.dll` `syscall` / `svc`) change between Windows 10/11 builds; all user code must call exported DLL symbols. |

### 2. Linux Kernel Syscall ABI Across `x86_64`, `aarch64`, and `riscv64gc`

`Basis: normative + source (Linux kernel arch/*/entry/ syscall ABI and rustix/libc conventions)`

Because Linux user-space programs may issue raw syscalls via `core::arch::asm!`
(or compiler-lowered intrinsic stubs), the target machine model for Linux must
specify the exact register effect of the trap instruction on each Tier 1 / target
architecture:

| Architectural Property | `x86_64` (`syscall`) | `aarch64` (`svc #0`) | `riscv64gc` (`ecall`) |
| :--- | :--- | :--- | :--- |
| **Syscall Number Register** | `rax` | `x8` | `a7` (`x17`) |
| **Argument Registers (1..6)** | `rdi`, `rsi`, `rdx`, `r10`, `r8`, `r9` *(note `r10` replaces SysV C ABI `rcx`!)* | `x0`, `x1`, `x2`, `x3`, `x4`, `x5` | `a0` (`x10`), `a1` (`x11`), `a2` (`x12`), `a3` (`x13`), `a4` (`x14`), `a5` (`x15`) |
| **Return Register(s)** | `rax` (primary; `rdx` for `pipe` on legacy ABIs) | `x0` | `a0` (`x10`), `a1` (`x11`) |
| **Error Encoding** | `rax` $\in [-4095, -1]$ (`0xfffff001..0xffffffffffffffff`) represents `-errno` | `x0` $\in [-4095, -1]$ represents `-errno` | `a0` $\in [-4095, -1]$ represents `-errno` |
| **Registers Clobbered by Kernel Trap** | **`rcx`** (stores return `rip`), **`r11`** (stores `rflags`), **`rflags`** (masked by `IA32_FMASK`) | `x0` (return value); Linux preserves `x1..x30`, `sp`, and SIMD/FP regs (`v0..v31`) across `svc #0` | `a0` (return value); Linux preserves `x1..x9`, `x11..x31`, and `f0..f31` across `ecall` |
| **Stack Pointer & Red Zone** | Kernel switches to ring-0 `rsp0` via TSS before pushing trap frame; user `rsp` and 128-byte red zone `[rsp-128, rsp)` are untouched by `syscall` itself (unlike signals!). | Kernel switches to `SP_EL1` on `svc #0`; user `SP_EL0` must be valid and 16-byte aligned if kernel copies `uaccess` buffers relative to `sp`. | Kernel swaps `sp` with `sscratch` in `stvec` handler; user `sp` (`x2`) is preserved. |

### 3. Formal OS Interface Models in Precedent Compilers (`CakeML`, `CompCert`, `seL4`, `SibylFS`)

`Basis: source + normative (CakeML/cakeml@f7318949, AbsInt/CompCert@74cbdbf0, seL4/l4v@6b4076ae, SibylFS SOSP 2015)`

| Precedent System | Formal Environment Mechanism | Memory & Register Frame Contract | Treatment of Out-of-Memory (OOM) & Nondeterminism |
| :--- | :--- | :--- | :--- |
| **CompCert 3.18 (`common/Events.v`, `common/Memory.v`)** | Parameterizes operational semantics by `extcall_sem : string -> signature -> genv -> list val -> mem -> trace -> val -> mem -> Prop`, axiomatized by `extcall_properties`. | External calls cannot modify blocks with non-global/non-public permissions (`Mem.unchanged_on`), cannot forge pointers to private stack frames, and must preserve `Mem.valid_block`. | `Mem.alloc` in `common/Memory.v` is total (infallible infinite memory); finite physical stack boundedness is recovered in `Stackingproof.v` / CompCertS via an explicit stack-size precondition. |
| **CakeML (`semantics/ffi/ffiScript.sml`)** | Models the OS as an abstract stateful oracle `ffi_state : 'ffi ffi_state` invoked via `call_FFI : 'ffi ffi_state -> mlstring -> word8 list -> word8 list -> 'ffi ffi_result`. | `call_FFI` reads a read-only configuration byte array `conf` and mutates *only* the passed mutable `word8 list` buffer `ws` in place; it has zero access to the ML heap or call stack. | Top-level theorem `compile_correct` explicitly allows target execution to terminate early with `Resource_limit_hit` whenever heap or stack allocation exceeds physical machine memory `ms`. |
| **seL4 (`seL4/l4v` @ `6b4076ae`)** | Models the kernel as a deterministic state monad wrapped in an explicit non-deterministic hardware/interrupt transition loop (`automaton`). | User-space register context is saved into the TCB (`tcbContext`) on trap entry (`handleSyscall` / `handleInterrupt`) and restored on `restore_user_context`. | All kernel allocations are pre-provisioned via explicit user-managed `Untyped` capabilities; kernel code never calls `malloc` or dynamically grows unbounded stacks. |
| **SibylFS (Ridge et al., SOSP 2015)** | Executable Lem/HOL4 transition specification of POSIX filesystem/descriptor calls (`open`, `read`, `write`, `pread`, `mmap`, `rename`, `fsync`). | Separates the **abstract OS state** (file descriptor table, open file descriptions, inode store, page cache) from user address space, interacting solely by copying byte slices into/out of user buffers. | Explicitly models POSIX error returns (`EIO`, `ENOSPC`, `EINTR`, partial `read`/`write` counts) as set-valued nondeterministic transitions checked against trace logs. |

### 4. Asynchronous Signals, Exceptions, and Stack-Frame Invariants

`Basis: source + normative (rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67 library/std/src/sys/pal/unix/stack_overflow.rs and System V / AAPCS64 / Win64 ABIs)`

An asynchronous event (a POSIX signal such as `SIGALRM`/`SIGURG`/`SIGWINCH`, or a
synchronous hardware fault such as `SIGSEGV`/`SIGBUS` on a guard page) can
interrupt compiled user-space instructions at any PC:

1. **Red-Zone vs. Signal Frame Placement:**
   - On **`x86_64` System V ELF** (`x86_64-unknown-linux-*`,
     `x86_64-apple-darwin`), the ABI reserves a **128-byte red zone** at
     `[rsp - 128, rsp)` that leaf functions may use for spill slots without
     decrementing `rsp`. When the OS kernel delivers a POSIX signal on the normal
     user stack (`SA_ONSTACK` not set), the kernel subtracts `128` from `rsp`
     *before* aligning and pushing `siginfo_t` and `ucontext_t`. Any compiler
     that writes at `rsp - 136` before decrementing `rsp` will have its data
     silently overwritten by an asynchronous signal!
   - On **`aarch64` (`AAPCS64` Linux/Windows)**, **`riscv64gc` (`LP64D`)**, and
     **`x86_64-pc-windows-*` (`Win64`)**, there is **0 bytes of red zone** in
     standard ELF/PE user space (note Darwin AArch64 defines a 128-byte red zone,
     unlike Linux AArch64). The compiler must **always decrement `sp` first**
     (`sub sp, sp, #N` or `stp x29, x30, [sp, #-N]!`) before storing to any new
     frame slot.
2. **Hardware `SP` Alignment Enforcement on AArch64:**
   - In Armv8-A / Armv9-A (`SCTLR_EL1.SA0 = 1`), any load or store using `sp` as
     the base register when `sp % 16 != 0` triggers an immediate hardware **SP
      Alignment Fault (`ESR_EL1.EC = 0b100110`, `SIGBUS`)**, and signal frame
     delivery requires `sp % 16 == 0` at every instruction. Thus the backend
     proof must establish $\forall \text{ step}, \text{sp} \equiv 0 \pmod{16}$ as
     a global machine invariant.
3. **Alternate Signal Stack (`sigaltstack`) and Stack Probes in `std`:**
   - Inspection of `library/std/src/sys/pal/unix/stack_overflow.rs` (lines 1–738
     at `58cf8f9c`) confirms that `std::rt::init` allocates a mmap'd alternate
     signal stack (`get_stackp`, `sigaltstack`) and installs a `SIGSEGV`/`SIGBUS`
     handler with `SA_SIGINFO | SA_ONSTACK`.
   - On Windows (`library/std/src/sys/pal/windows/stack_overflow.rs`, lines 1–41),
     `std` registers a Vectored Exception Handler (`AddVectoredExceptionHandler`)
     that intercepts `EXCEPTION_STACK_OVERFLOW` (`0xC00000FD`), supported by the
     Windows thread stack's reserved `MEM_GUARD` pages.
   - For either guard-page mechanism to catch stack exhaustion soundly, the
     compiler must emit **stack probes** (`__rust_probestack` or inline page-touch
     loops) whenever a function prologue allocates more than one page ($4096$
     bytes).

### 5. Operating-System Assumption Ledger Entries (`ENV-LOAD-1` .. `ENV-ASYNC-5`)

`Basis: derived (synthesized from Findings 1–4 and preserved in support/os_environment_assumption_ledger.json)`

Every compilation attestation for a verified Rust binary should include the
following five operating-system assumption ledger entries (preserved in
`support/os_environment_assumption_ledger.json`):

1. **`ENV-LOAD-1` (Program Loader, Relocation & TLS Initialization):** Prior to
   transferring control to the entry symbol (`_start` / `mainCRTStartup`), the OS
   program loader (`ld-linux`, `dyld`, or `ntdll!LdrInitializeThunk`) maps all
   loadable segments (`PT_LOAD`, `__TEXT`/`__DATA`, PE sections) at their
   relocated virtual addresses with declared `R`/`W`/`X` permissions, zero-fills
   `.bss`, resolves dynamic relocations (`R_*_RELATIVE`, `R_*_GLOB_DAT`,
   `R_*_JUMP_SLOT`), and initializes the architecture's Thread-Local Storage
   register (`fs:0` on x86-64 Linux, `tpidr_el0` on AArch64 Linux, `tp`/`x4` on
   RISC-V, `gs:[0x58]` on x86-64 Windows).
2. **`ENV-SYS-2` (External Call & Syscall Frame Preservation):** Every OS system
   call (`syscall`, `svc #0`, `ecall`) and external dynamic library call
   (`libc.so.6`, `libSystem.B.dylib`, `kernel32.dll`, `ntdll.dll`) conforms to
   the target ABI: it preserves all callee-saved registers, all read-only memory,
   and all private stack/heap allocations not reachable from passed pointer
   arguments, mutating only the architectural return/clobber registers and
   explicitly passed mutable out-buffers.
3. **`ENV-MEM-3` (Heap Allocator Disjointness & Alignment):** The system allocator
   invoked by `std::sys::alloc` (`posix_memalign`/`malloc`/`realloc` in
   `library/std/src/sys/alloc/unix.rs`; `HeapAlloc`/`HeapReAlloc` in
   `library/std/src/sys/alloc/windows.rs`) returns either null (on OOM) or a
   pointer aligned to the requested `Layout::align()` whose `[ptr, ptr + size)`
   range is disjoint from all live stack frames, static items, and currently
   allocated heap blocks.
4. **`ENV-STACK-4` (Guard Page Enforcement on Stack Overflow):** The OS maintains
   at least one unmapped or `PROT_NONE`/`PAGE_GUARD` page immediately below each
   thread's stack limit so that sequential 4 KiB stack probes trap deterministically
   before any stack pointer wrap-around or heap collision can occur.
5. **`ENV-ASYNC-5` (Asynchronous Signal & Exception Delivery Discipline):**
   Asynchronous OS signals and exceptions either terminate the process, execute
   on a disjoint `sigaltstack` (`SA_ONSTACK`), or—if delivered on the active user
   stack—preserve all memory at `[sp, stack_top)` (and `[rsp - 128, rsp)` on
   x86-64 System V targets) and restore all architectural registers upon `sigreturn`.

## Boundaries

- **Kernel-mode / bare-metal Ring-0/EL1 execution (`not examined` here):** This
  report models user-space ring-3/EL0/U-mode OS execution on Linux, macOS, and
  Windows. Bare-metal kernel verification (MMU page-table walks, `iretq`/`eret`/`sret`,
  DMA cache coherency) requires a privileged ISA model (such as `seL4` or `Islaris`
  EL1/EL2).
- **`io_uring` shared-memory ring buffers (`known not to apply` to synchronous
  syscall frame rules):** Asynchronous kernel completion rings (`io_uring` SQE/CQE
  mmap'd buffers or Windows IOCP buffers) allow the kernel to mutate user-space
  memory concurrently with user-space execution between syscalls; buffers handed
  to `io_uring` must be modeled as concurrent shared memory rather than
  synchronous call-bounded out-pointers.

## Evidence

1. **Rust `1.99.1` OS Platform Abstraction Layer (`library/std/src/sys/`):**
   - Repository: `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`
   - Files:
     - `library/std/src/sys/pal/unix/mod.rs` (387 lines)
     - `library/std/src/sys/pal/unix/stack_overflow.rs` (738 lines, `sigaltstack`
       and `SA_ONSTACK` registration)
     - `library/std/src/sys/pal/unix/weak/syscall.rs` (19 lines)
     - `library/std/src/sys/alloc/unix.rs` (103 lines)
     - `library/std/src/sys/pal/windows/mod.rs` (296 lines)
     - `library/std/src/sys/pal/windows/api.rs` (366 lines)
     - `library/std/src/sys/pal/windows/c/windows_sys.rs` (3,704 lines)
     - `library/std/src/sys/pal/windows/stack_overflow.rs` (41 lines,
       `AddVectoredExceptionHandler`)
     - `library/std/src/sys/alloc/windows.rs` (218 lines, `HeapAlloc`)
2. **Support artifacts preserved in this package:**
   - `support/os_environment_assumption_ledger.json`: Structured Linux syscall ABI
     table, OS reachability matrix, and 5 formal assumption ledger entries.
   - `support/verify_os_ledger.py`: Verification script validating the ledger.

## Revalidation

1. **Verify the preserved OS assumption ledger and syscall ABI table:**
   ```bash
   python3 reports/os-syscall-interfaces-asynchronous-signals-and-environment-models/support/verify_os_ledger.py \
     --ledger reports/os-syscall-interfaces-asynchronous-signals-and-environment-models/support/os_environment_assumption_ledger.json
   ```
2. **Check for changes to `std` OS entry points or stack-overflow handlers on a newer `rustc` revision:**
   ```bash
   git -C <rust-checkout> diff 58cf8f9c35b355199727627d07ae34a4e2846d67..<new-rev> -- \
     library/std/src/sys/pal/unix/stack_overflow.rs \
     library/std/src/sys/pal/windows/stack_overflow.rs \
     library/std/src/sys/alloc/
   ```
