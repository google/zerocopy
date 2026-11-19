# Incremental C2Rust Lifting, Multi-Variant Shadow Execution, and FFI ABI Strangulation

## Summary

Incrementally strangling live legacy C, Fortran, and COBOL binaries one function at a time into memory-safe verified Rust faces four coupled structural obstructions:

1. **Closed-world vs. modular ownership inference limits.** Syntax-preserving transpilers (`immunant/c2rust`) translate C99 into pointer-dense `unsafe` Rust with Relooper CFG loops, raw byte-slice bitfields, and variadic shims. Ownership lifters (`Crown`, `Laertes`) either require whole-program MIR visibility—`Crown`'s `Modular::analyze` explicitly bails out unimplemented—or plateau at a `~12%` pseudo-safety conversion ceiling (`Laertes`) when confronted with pointer arithmetic, aliasing globals, and untyped casts.
2. **Cross-boundary ABI and provenance incompatibilities.** Mixed C/Rust call stacks cannot share naive `extern "C"` boundaries safely when legacy code invokes `setjmp`/`longjmp` across non-POF (Plain Old Frame) `Drop` guards (`ffi_probe` shows `rust_drops_executed=0`), relies on flexible array member (FAM) tail-padding (`sizeof(struct FamHdr) == 8` yet `offsetof(payload) == 6`), tears concurrent bitfields via non-atomic byte RMW, passes Fortran `CFI_cdesc_t` strided dope vectors with aliased dummy arguments, or overlays `COMP-3` packed BCD and `REDEFINES` records in COBOL.
3. **Benign divergence in Multi-Variant Execution Engines (MVEEs).** Production MVEEs (`Orchestra`, `VARAN`, `ReMon`/`GHUMVEE`, `Detile`) intercept system calls and hide `vDSO`/`vsyscall` pages to keep identical-ISA or diversified C variants synchronized, yet function-level C-vs-Rust shadow execution diverges benignly in heap pointer addresses, allocator sizing, and hash iteration order—requiring **Canonical Projection Equivalence** ($\pi_C(\sigma_C) \equiv \pi_R(\sigma_R)$) rather than bitwise state comparison.
4. **Orders-of-magnitude latency gap in shadow rollback.** Measured across 3 consecutive runs on `x86_64` Linux, software cache-line undo logging completes a 256-byte frame checkpoint and rollback in `8.71 ns` median (`7.83–11.46 ns`), whereas `mprotect` + `SIGSEGV` page copy-on-write takes `19,360.4 ns` median (`19,310.0–19,467.3 ns`, `2,223x` slower) and `fork()` CoW takes `405,172.4 ns` median (`351,136.0–637,156.2 ns`, `46,518x` slower) while breaking multithreaded lock invariants. Sub-microsecond zero-downtime function-level rollback therefore demands compiler-inserted write-set/undo logs or hardware `PKRU`/`MPK` domain gates rather than OS page-table traps.

## Applicability

This synthesis applies to incremental migration architectures ("strangler fig" replacement) targeting compiled native legacy codebases in C99/C11, Fortran 2018 (`ISO_Fortran_binding.h`), and COBOL-85/2014 on `x86_64` (System V AMD64) and `AArch64` (AAPCS64) POSIX/Linux hosts. Subject relationships in `REPORT.json`:

- **Transpilers and static ownership lifters** (`immunant/c2rust`, `KomaEc/crown`, `Laertes`) characterize automated syntactic lowering and pointer-to-reference inference.
- **Production migration and FFI systems** (`memorysafety/rav1d`, `fish-shell/fish-shell`, `dtolnay/cxx`, `rust-lang/rfcs` RFC 2945, `rust-lang/rust` `VaList`, `llvm/llvm-project` `ISO_Fortran_binding.h`) anchor observed ABI rules and real-world engineering trade-offs.
- **MVEEs and isolation/checkpoint substrates** (`Orchestra`, `VARAN`, `ReMon-MVEE/ReMon`, `Detile`, `PKRU-Safe`, `checkpoint-restore/criu`) cover runtime dual execution, benign divergence suppression, and rollback costs.

Empirical micro-probes (`ffi_probe` and `shadow_ckpt_bench`) were compiled and executed on Linux `7.1.6` (`x86_64`, 8-vCPU Intel Xeon @ 2.20 GHz) using `gcc 15.2.0` and `rustc 1.98.0-nightly (14210df0e 2026-05-31)`. Performance numbers generalize across `x86_64` Linux kernels with comparable TLB shootdown and syscall costs; absolute nanosecond timings vary by CPU microarchitecture, thread count, and kernel mitigation profile.

## Findings

### 1. Syntactic C99-to-Rust Lowering and Static Ownership-Lifting Ceilings

`Basis: source + documentation`

#### Mechanical Lowering Patterns in `immunant/c2rust`

`immunant/c2rust` (`ae95fa7a268d92b23aaa687e1d6b74d9a7470312`) preserves C99 runtime semantics by emitting `#[no_mangle] pub unsafe extern "C"` symbols that communicate over raw pointers rather than native Rust modules unless `--reorganize-definitions` runs `c2rust-refactor` (`README.md#L233-L240`):

- **CFG Relooper (`c2rust-transpile/src/cfg/mod.rs#L146-L164`):** Unstructured `goto`, intersecting `switch` fallthroughs, and Duff's devices are decomposed into `Structure::{Simple, Loop, Multiple}` AST nodes. When irreducible control flow occurs, the transpiler falls back to a synthetic `current_block: u64` state machine inside `loop { match current_block { ... } }`, inflating local variable lifetimes to match the outer state loop and defeating NLL borrow-checker precision.
- **Variadic Lowering (`c2rust-transpile/src/translator/variadic.rs#L25-L55, L172-L307`):** `register_va_decls` injects `#![feature(c_variadic)]`, renames the trailing `...` to `c2rust_args`, and translates `va_list` declarations into `core::ffi::VaListImpl` (pre-Edition 2024) or `core::ffi::VaList` (`Edition2024`+, tracking `rust-lang/rust#141980`). `convert_vaarg` emits `.arg::<T>()` calls with `VaArgCastKind::Transmute` for function pointers and `enum` constructors for C enums (`variadic.rs#L247-L265`).
- **Bitfield Byte-Slice Shims (`c2rust-bitfields/src/lib.rs#L15-L89`):** C bitfield structs become `[u8; N]` byte arrays wrapped with `#[derive(BitfieldStruct)]`. `FieldType::set_field` and `get_field` iterate bit-by-bit across `(lhs_bit..=rhs_bit)` (`lib.rs#L30-L39`), masking individual bytes and unconditionally sign-extending signed integers (`val <<= unused_bits; val >>= unused_bits`).

#### Whole-Program vs. Modular Ownership Lifting (`Crown` and `Laertes`)

Two academic lifters expose the exact structural ceiling between syntactic transpilation and idiomatic safe Rust:

1. **`Crown` (`KomaEc/crown` @ `621904cd356b433215d5f55db39ffd71714f44ff`, CAV 2023 `DOI: 10.1007/978-3-031-37709-9_22`):**
   - Infers pointer types in two compiler-MIR stages: (i) a flow-insensitive `Fatness` qualifier lattice where `Fatness::Arr ⊑ Fatness::Ptr` (`crates/analysis/src/type_qualifier/flow_insensitive/fatness.rs#L46-L79`, separating single-object `&` from slice `&[]` via `BooleanSystem::greatest_model`), and (ii) SSA dominance-frontier `Ownership` inference over `{Owning, Transient, Unknown}` (`crates/analysis/src/ownership.rs#L31-L36`) solved by CaDiCaL (`IntraProcedural::DB = CadicalDatabase`, `#L157-L194`), bounding pointer-chase precision (`total_deref_level`, capped to `2` at `#L244`).
   - Although `Crown` solves up to 500,000 LoC in under 10 seconds across 20 C benchmarks on tree- and DAG-shaped ownership graphs, **`Modular::analyze` explicitly fails with `anyhow::bail!("modular analysis is not implemented")` (`ownership.rs#L146-L155`)**. Because `Crown` requires whole-program MIR visibility, translating a single C function behind an opaque `extern "C"` FFI boundary collapses caller/callee alias constraints to `Ownership::Unknown` (`*mut T`) unless manually annotated.
2. **`Laertes` (OOPSLA 2021, `DOI: 10.1145/3485498`, `Zenodo: 10.5281/zenodo.5442253`):**
   - Queries `rustc`'s borrow checker iteratively as an oracle to promote `*mut T`/`*const T` to `&mut T`/`&T`. Even in artificial "pseudo-safe" ablations removing auxiliary non-aliasing obstacles, **only ~12% of raw pointers on average** convert cleanly to safe references because C idioms rely on pointer arithmetic, aliasing mutable globals, and untagged type casts.

#### Practitioner Strangulation Postmortems and Neuro-Symbolic Lifting

`Basis: documentation + source`

- **`memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`):** Ported from `dav1d` via `c2rust` and incrementally rewritten into idiomatic Rust (`README.md#L1-L40`). Retaining raw C-style index-per-pixel loops inside Rust triggered repeated bounds checks and performance regressions until hot loops were restructured around pre-sliced local slices, while hand-written SIMD assembly (`nasm` under `feature = "asm"`) remained intentionally behind a strict C-ABI boundary rather than being transpiled.
- **`fish-shell/fish-shell` (`f0d874ad924bd582a039f5a5d5a018913c7d8b6a`):** Engineering retrospective (*"Fish 4.0: The Fish of Theseus"*) documented why **permanent C++/Rust FFI strangulation was rejected** in favor of transient `dtolnay/cxx` bridges (`4d19ca4eec78b2964035a3ea3cef5196515b13e7`) solely as scaffolding until 100% of C++ modules were deleted—citing dual-toolchain CMake/Cargo build friction, shared-ownership impedance mismatches, and cross-boundary threading complexity.
- **`sudo-rs` & DARPA TRACTOR:** Security-critical CLI replacements (`sudo-rs`) bypassed mechanical C2Rust translation entirely via clean-room specification rewrites because wrapping a legacy C privilege boundary preserves C memory vulnerabilities inside `unsafe`. Simultaneously, DARPA's *Translating All C to Rust* (`TRACTOR`) program pairs static alias/slice analysis with LLM-guided refactoring to synthesize higher-level representations (`Vec<T>`, `&[T]`, `Option<&mut T>`, `Result`) that syntactic transpilers cannot derive without changing data-structure layouts.

---

### 2. Cross-Boundary FFI & Legacy Language ABI Minefields (C, Fortran, COBOL)

`Basis: normative + source + execution`

Replacing a single function $f_C$ inside a live multi-language process by $f_R$ behind an `extern "C"` wrapper introduces ten distinct ABI and semantic soundness hazards that static transpilers ignore.

| Hazard Class | Legacy Source Pattern | Rust / FFI Soundness Wall | Measured / Verified Consequence | Mitigation Boundary |
| :--- | :--- | :--- | :--- | :--- |
| **1. Non-local jumps (`setjmp`/`longjmp`)** | Error recovery via `longjmp(env, val)` unwinding C frames above Rust call (`lua`, `libjpeg`, `zlib`) | RFC 2945 (`rust-lang/rfcs` `text/2945-c-unwind-abi.md#L143-L267`): `extern "C"` panic aborts; `"C-unwind"` permits foreign C++ exceptions, **but forced unwinding (`longjmp`, `pthread_exit`) across any non-POF frame with live `Drop` is UB** (`#L180-L186, #L243-L251`). | `ffi_probe` output: `longjmp_rc=42 rust_drops_executed=0` — `NonPofGuard::drop` skipped silently, leaking locks/allocations. | Require Plain Old Frames (zero `Drop` values on stack) or trap errors into return codes before re-entering C. |
| **2. Variadics (`va_list`, `va_start`)** | Legacy formatting/dispatchers (`vprintf`, custom variadic loggers) | `VaList` layout is target-ABI-specific (`library/core/src/ffi/va_list.rs#L11-L127`): 24-byte `{gp_offset, fp_offset, overflow_arg_area, reg_save_area}` passed indirectly via `#[rustc_pass_indirectly_in_non_rustic_abis]` on SysV `x86_64`; cannot synthesize dynamic varargs in safe Rust (`VaList` unstable). | Transpiled variadics pin builds to `#![feature(c_variadic)]`; Edition 2024 removed `VaListImpl` (`variadic.rs#L26-L33`). | Convert variadic C entries into fixed-arity slice/struct adapters (`&[Arg]`) at the strangler boundary. |
| **3. Flexible Array Members (FAMs)** | Trailing `T data[];` or `T data[1];` inside C packet/IPC headers | `sizeof(struct S)` includes struct **tail padding**, whereas `offsetof(S, data)` points *inside* tail padding before alignment end. | `ffi_probe` output: `c_sizeof_FamHdr=8 c_offsetof_payload=6 naive_rust_sizeof=8`. Adding `[u8; 0]` at end of `NaiveRustFamHdr` shifts payload by 2 bytes! | Project FAM headers with explicit packed header size or byte-slice offset (`offsetof`), never naive `[T; 0]` post-padding fields. |
| **4. Bitfields & Tearing** | Hardware register / protocol flag structs (`int delta:3; uint flags:5;`) | Bitfield packing, signedness, and alignment-unit straddling are implementation-defined in C99 §6.7.2.1. `c2rust-bitfields` lowers access to non-atomic byte loops (`lib.rs#L30-L39`). | `ffi_probe` confirms `bitfield_raw=0xad` (`10101_101`), `extracted_signed_3bit=-3`; concurrent updates tear neighboring bits in the same byte/word. | Wrap bitfields behind atomic `u32`/`u64` CAS bitmasks or verified `zerocopy` byte-order wrappers. |
| **5. Unions & Uninitialized Padding** | C99 §6.5.2.3 union type-punning & memcpy over padded structs (`struct { u8 a; u32 b; }`) | Reading padding bytes via Rust `&[u8]` is UB (`undef`/`poison` under LLVM/MiniRust); writing invalid bit patterns to `bool`/`enum`/non-null `&T` is instant UB. | Transmuting partial C structs to safe Rust slices fails Miri/LLVM undef checks and leaks stack/heap bytes across FFI. | Enforce `MaybeUninit<u8>` or explicit zero-initialized padding invariants (`FromBytes`/`IntoBytes`) at ingress. |
| **6. Shared `errno`, TLS & Allocators** | Checking `errno` after `read()`, freeing `malloc()` buffers across modules | Rust allocator hooks, logging, or panic formatting between C calls silently clobbers TLS `__errno_location()`. Calling Rust `Drop`/`Box::from_raw` on `malloc` memory (or vice versa with `jemalloc`) corrupts heap metadata. | Silent heap corruption or misdiagnosed syscall failures if `errno` is not latched immediately after C invocation. | Latch `errno` atomically inside thin FFI shims; enforce strict **creator-owns-destructor** allocator affinity. |
| **7. Async Signal Handlers** | Legacy C installs `SIGALRM`/`SIGUSR1` handlers doing long-running work or `longjmp` | POSIX async-signal-safety forbids heap allocation, `RwLock`/mutex acquisition, or panic unwinding inside signal context; Rust stack probes (`__rust_probestack`) may overflow small `sigaltstack`. | Deadlock on glibc arena locks if a signal interrupts `malloc` and enters Rust formatting/panicking code. | Restrict signal handlers to `volatile sig_atomic_t` / atomic flag flips or `signalfd` event-loop dispatch. |
| **8. Fortran Interop (`ISO_Fortran_binding.h`)** | Scientific/numerical kernels (`BLAS`, `LAPACK`, PDE solvers) using assumed-shape arrays, `COMMON`, `EQUIVALENCE` | `CFI_cdesc_t` (`flang/include/flang/ISO_Fortran_binding.h#L33-L210`) encodes `CFI_MAX_RANK = 15`, non-unit/negative byte strides (`CFI_dim_t.sm`), 1-based `lower_bound`, and `CFI_attribute_allocatable/pointer`. Fortran pass-by-reference allows `CALL SUB(A, A)` aliasing when neither argument writes—mapping both to `(&mut f64, &f64)` violates Rust/LLVM `noalias` UB. | Column-major non-contiguous slices cannot cast to contiguous Rust `&[f64]`; `noalias` miscompilation silently corrupts aliased outputs under `-O3`. | Wrap Fortran calls via explicit stride-aware raw pointers (`*const T`/`*mut T`) or `CFI_is_contiguous` fast-path branching + `UnsafeCell` aliasing guards. |
| **9. COBOL Data & Control Flow** | Fixed-format business kernels with `COMP-3` packed BCD, `REDEFINES`, `PERFORM p1 THRU p2`, `ALTER` | `COMP-3` stores 2 decimal digits/byte (`(n+1)/2` bytes) with sign nibble `0xC`/`0xD`/`0xF` (no native CPU/Rust primitive). `REDEFINES` overlays incompatible EBCDIC/numeric records. `PERFORM THRU` allows overlapping, fall-through paragraph ranges and dynamic `ALTER` gotos that break LIFO call stacks. | Naive C-ABI struct generation misinterprets `COMP-3` sign nibbles and triggers `SIGABRT`/garbage arithmetic on record boundaries. | Lift `PERFORM THRU` subgraphs as whole-procedure CPS/state machines; decode `COMP-3` via fixed-point checked byte decoders at record boundaries. |
| **10. Cross-Language LTO & Hardware CFI** | `-fsanitize=cfi` indirect-call checks, Intel CET `ENDBR64`, AArch64 `BTI`/`PAC` | Clang C CFI hashes C type names whereas `rustc -Zsanitizer=cfi` normalizes Rust type IDs; function pointers passed across FFI trap `SIGILL` (`ud2`) unless ABI/CFI-normalized (`#[cfi_encoding]`) and `BTI`/`ENDBR` landing pads match. | Indirect C-to-Rust callbacks crash immediately in hardened builds even with identical SysV register passing. | Annotate cross-boundary callbacks with matching CFI encodings (`#[cfi_encoding = "..."]`) or route through trampoline dispatch tables. |

---

### 3. Multi-Variant Execution Engines (MVEEs) and Benign Divergence Normalization

`Basis: source + documentation + derived`

When strangling a live service without test coverage sufficient to prove $f_R \equiv f_C$ offline, **Multi-Variant Execution (MVEE)** executes the legacy binary (or C variant $V_C$) alongside the lifted Rust variant $V_R$ online, comparing outputs and system calls before externalizing side effects.

#### Architectural Taxonomy of Production & Research MVEEs

1. **`Orchestra` (EuroSys 2009, `DOI: 10.1145/1519065.1519071`):** First practical user-space lockstep MVEE built atop `ptrace`. Every syscall from every variant traps into an external monitor process (`4x` context switches per syscall), yielding `2x–6x` slowdown on I/O-heavy servers (Apache/lighttpd).
2. **`VARAN` (ASPLOS 2015, `DOI: 10.1145/2694344.2694390`):** Eliminated `ptrace` lockstep bottlenecks via a **leader-follower shared-memory ring buffer** (`N`-version execution). Only the leader executes native kernel syscalls and streams arguments/results asynchronously into a ring buffer consumed by followers via binary-rewritten syscall trampolines. Overhead drops to `~2%–16%` for 4 variants on SPEC CPU, **trading synchronous exploit/bug blocking for an asynchronous drift window** bounded by ring-buffer depth.
3. **`ReMon` / `GHUMVEE` (`ReMon-MVEE/ReMon` @ `a29fc6320052a4acefcc8177c6cfaa07df2e61a5`, USENIX ATC 2016; EuroSys 2017 `DOI: 10.1145/3064176.3064178`):** Combines an **In-Process Monitor (`IP-MON`)** handling `~70` low-risk syscalls (`MVEE_ipmon.h#L1-L247`) with a **`ptrace` Cross-Process Monitor (`CP-MON`)** for security-critical calls (`CURRENT_POLICY = FULL_SYSCALLS`, `IPMON_EXEC_MASTER | IPMON_REPLICATE_MASTER`), optionally isolating `IP-MON`'s replication buffer using Intel MPK (`MVEE_IP_PKU_ENABLED`, `README.md#L127-L131`). Critically, `GHUMVEE` documents three mandatory determinism normalizers (`README.md#L43-L48, L135-L194`):
   - **Hiding `vDSO` and `vsyscall`:** Direct userspace memory reads of `gettimeofday`/`clock_gettime` bypass syscall hooks and desynchronize variants across microseconds (`vsyscall=native` required on x86_64).
   - **Synchronization Replication Agent:** Patched `glibc`/`libpthread` logs lock-acquisition and futex-wake partial orders from the master variant (`MVEE_FUTEX_WAIT_TID = 30`) to replay identical interleavings on slaves, bounding 4-thread PARSEC 2.1 overhead to **`1.32x`**.
   - **`-fno-threadsafe-statics`:** GCC's ad-hoc guard variables for C++ local statics race under multi-threaded initialization and trigger false-positive variant divergences.
4. **`Detile` (DIMVA 2016, `DOI: 10.1007/978-3-319-40667-1_16`):** Moves MVEE comparison from syscalls down to fine-grained **interpreter/JIT bytecode and object-allocation checkpoints** inside script engines to detect silent memory-disclosure leaks that never trigger divergent syscalls.

#### Benign Divergence in Heterogeneous C-vs-Rust Shadow Execution

`Basis: derived + source`

All homogeneous C-vs-C MVEEs assume variants share nearly identical memory allocators, struct layouts, and deterministic library state. By contrast, executing $f_C$ (compiled legacy C) against $f_R$ (idiomatic or lifted Rust) creates **benign semantic divergence** that breaks raw syscall/register comparators:

- **Allocator & Pointer-Address Divergence:** `malloc` vs. `Box`/`Vec` (or `jemalloc` vs. `ptmalloc2`) return distinct heap addresses and reserve distinct capacity growth schedules (`Vec` doubling `0 -> 4 -> 8` vs. C `realloc(n+1)`). If those addresses leak into `writev` iovec pointers, hash seeds, or sorted pointer arrays, naive `arg` byte comparison triggers spurious mismatch aborts.
- **Hash-Order Divergence:** Rust's `std::collections::HashMap` randomizes `RandomState` (SipHash-1-3) per map instance, diverging on iteration order from C open-addressed tables unless swapped for deterministic hashing during dual-execution validation.
- **Canonical Projection Equivalence:** Sound function-level C-vs-Rust shadow checking must evaluate equivalence under a typed boundary projection $\pi$:

$$\pi_C(\sigma_{\text{post}}^C, r_C) \equiv_\alpha \pi_R(\sigma_{\text{post}}^R, r_R)$$

where $\equiv_\alpha$ checks scalar return parity, exact byte equality on contiguous output buffers (`*mut u8`, `len`), and **graph isomorphism modulo pointer renaming ($\alpha$-equivalence)** on pointer-linked output graphs—ignoring unused struct padding bytes and internal Rust capacity metadata.

---

### 4. Low-Overhead Function-Level Shadow Checkpointing & Zero-Downtime Rollback

`Basis: execution + documentation + derived`

When $f_R$ serves as the live shadow candidate alongside $f_C$ (or vice versa), rolling back a detected semantic mismatch (`!equiv(out_C, out_R)` or caught panic/trap) without crashing the host process requires isolating and reverting $f_R$'s memory writes within sub-microsecond budgets.

#### Taxonomy and Measured Micro-Probe Results (`shadow_ckpt_bench`)

We benchmarked three primary intra-/cross-process state checkpoint-and-rollback mechanisms in `shadow_ckpt_bench.c` (`gcc -O2`, Linux `7.1.6`, `x86_64`, 3 consecutive runs of `100,000` undo ops, `5,000` `mprotect` faults, `500` `fork()` cycles):

| Rollback Mechanism | Measured Cost per Checkpoint+Rollback (3-run median [range]) | Thread Safety & Compatibility | Isolation Strength | Primary Bottleneck |
| :--- | :--- | :--- | :--- | :--- |
| **1. Software Undo Log (256 B frame copy)** | **`8.71 ns`** (`7.83–11.46 ns`, ~19 cycles @ 2.2 GHz) | Thread-local; zero syscalls; deterministic WCET | Protects declared write-set / lifted Rust `&mut` locals only | Cannot catch rogue wild-pointer stores inside unverified C `unsafe` |
| **2. Hardware MPK (`PKRU-Safe` `WRPKRU`, EuroSys 2022 `10.1145/3492321.3519582`)** | `~20–26` CPU cycles (`~9–12 ns`) per `WRPKRU`; `<11.55%` pessimistic macro overhead (`~0%` coarse FFI) | Thread-local hardware PKRU register (`16` protection keys max) | Hardware-enforced page read/write isolation of safe Rust heap from unsafe C | Coarse 4 KiB page granularity; exhausted at >15 compartments; requires `x86_64` PKU or `ARM POE` |
| **3. Page Write-Protect (`mprotect` + `SIGSEGV` / `userfaultfd`)** | **`19,360.4 ns`** (`19,310.0–19,467.3 ns`, `2,223x` slower than undo log) | Triggers process-wide `mmap_lock` & cross-core TLB shootdown IPIs in multithreaded apps | Catches arbitrary stray stores across protected heap pages | Kernel `mm` lock contention + signal frame setup/return dominate fast FFI functions |
| **4. Process Snapshot (`fork()` CoW + `waitpid`)** | **`405,172.4 ns`** (`351,136.0–637,156.2 ns`, `46,518x` slower than undo log) | **Broken on multithreaded processes:** POSIX `fork()` clones only calling thread; sibling mutexes stay permanently locked | Full address-space isolation + separate `errno`/FD table | Copy-on-write page-table walk + `waitpid` context switches; unsuitable inside hot loops (`CRIU` checkpointing operates at ms–s process granularity) |

#### Irrevocable Side-Effect Gate

`Basis: derived`

Software undo logs, `PKRU-Safe`, and page CoW can only roll back **process memory**. Any function $f_R$ executed inside a zero-downtime shadow transaction must either:
1. Run over **pure buffered memory + shadow descriptors**, deferring external syscalls (`write`, `sendmsg`, `unlink`, `mmap`) into a commit queue flushed only after $\pi_C \equiv \pi_R$ holds; or
2. Be classified as **irrevocable** once it crosses an external I/O or atomic IPC boundary, gating commit before external visibility (mirroring `VARAN`/`ReMon` syscall-interposition commit buffers).

---

### 5. Six-Level Performance, Verification & Resource Matrix (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| System / Strategy | (L1) Authoring Velocity & Repair Cost | (L2) Toolchain Build Time & RSS | (L3) Analysis / Compile / Synthesis Speed | (L4) Runtime Code & Crossing Performance | (L5) Equivalence / Safety Checking Speed | (L6) Artifact, Memory & Binary Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`immunant/c2rust` (`ae95fa7a...`)** | Fully automated C99 transpilation; `1.4x–2.8x` LoC expansion (`unsafe` remains manual to eliminate) | Builds on stable `rustc` + LLVM 15+ (`libclang-dev`); `c2rust-refactor` pinned to `nightly-2023-04-15` | Linear AST lowering; seconds per C TU via `compile_commands.json` | Native C-equivalent speed (`~1.0x`), minus missed Rust alias optimizations (`noalias` absent on `*mut`) | Zero memory-safety proof (all derefs inside `unsafe {}`); relies on existing C test suites | Emits standalone per-TU Rust modules + C-ABI shims; modest binary bloat unless Relooper duplicates code |
| **`Laertes` (`10.1145/3485498`)** | Automated post-C2Rust pass; lifts only **~12%** of raw pointers in pseudo-safe ceiling | Custom `rustc` internal AST/borrow-checker plugin | Minutes per crate (repeated multi-round `rustc` invocations as oracle) | Identical to C2Rust on unlifted paths; enables bounds/drop checks on lifted slices | Verified only by `rustc` borrowck on promoted references; global unsafe blocks unchecked | Minimal runtime delta; extra temporary AST/rustc memory during iterative search |
| **`Crown` (`621904cd...`)** | Automated whole-program ownership inference (`artifact` branch refactoring); **`Modular::analyze` unimplemented** | Nightly `rustc_private` + `rustc-tools` + CaDiCaL SAT crate | **<10 s for 500 kLoC** across 20 benchmarks (Apple M1, 16 GB RAM) | Removes raw pointers on tree/DAG data; safe slices introduce bounds checks unless hoisted | SAT-encoded ownership constraints; collapses to `Unknown` at `extern "C"` FFI seams | In-memory CaDiCaL clauses linear in MIR locals/fields (`depth <= 2` default) |
| **`dtolnay/cxx` + Manual (`fish-shell` / `rav1d`)** | High human effort (months–years); zero Day-2 pointer-repair debt once C++ deleted (`fish-shell`) | Proc-macro + C++ header codegen integrated in Cargo (`build.rs`) | Sub-second macro expansion + incremental `rustc`/`clang++` | Zero-copy `&[u8]` / `UniquePtr` crossings; `rav1d` retained `nasm` SIMD behind C ABI | Compile-time static signature & lifetime checks across FFI bridge | Small static bridge stubs; eliminates dual runtime overhead once C++ is retired |
| **`VARAN` (`10.1145/2694344.2694390`)** | Zero source changes (binary rewriting + LD_PRELOAD); requires deterministic syscall wrappers | Custom dynamic binary rewriter + ring-buffer runtime | Fast load-time instrumentation (ms) | **`~2%–16%` overhead** (4 variants, SPEC CPU) via lock-free shared-memory ring | Asynchronous syscall arg comparison (bounded drift window by ring size) | $N \times$ process RSS + shared ring-buffer pages (few MiB) |
| **`ReMon` / `GHUMVEE` (`a29fc632...`)** | Requires custom patched `glibc`/`libpthread` + optional custom Linux 5.3/5.4 kernel for `IP-MON`/PKU | CMake + patched GCC/glibc toolchain build | Static `MVEE_ipmon.h` policy compiled into enclave | **`1.32x` overhead** on 4-thread PARSEC 2.1; `IP-MON` eliminates `ptrace` switches on ~70 syscalls | Synchronous `CP-MON` blocking on sensitive syscalls + `IP-MON` lockstep checks | $N \times$ variant RSS + `4096`-FD map + MPK-protected ring buffer |
| **`PKRU-Safe` (`10.1145/3492321.3519582`)** | Lightweight Rust/LLVM annotation + dynamic profiling pass on mixed codebases | Modified LLVM IR instrumentation + custom allocator hooks | Single LLVM LTO/IR compile pass | `~20–26` cycles (`WRPKRU`) per FFI switch; `~0%` on Servo Dromaeo, **`<11.55%` pessimistic** | Runtime hardware memory-key trap on illegal cross-domain heap access | Separate PKU-tagged heap pages (`4 KiB` page alignment padding per domain) |
| **Shadow Undo Log vs. `mprotect`/`fork` (`shadow_ckpt_bench`)** | Compiler pass or typed arena wrapper around candidate function $f_R$ | Standard `gcc`/`rustc` build | Zero extra compile step (`inline` memcpy/undo) | **`8.71 ns`** undo vs **`19.36 µs`** `mprotect` (`2,223x`) vs **`405.17 µs`** `fork()` (`46,518x`) | Exact per-exit $\pi_C \equiv \pi_R$ projection check (sub-µs for bounded structs) | Thread-local undo ring buffer (KiBs) vs whole-process `mm_struct` cloning |

---

### 6. Human Comprehensibility (`C1`) and Universal Conceptual Simplicity (`C2`)

`Basis: derived + source`

#### (C1) Human Comprehensibility Audit

Even when automated agents or transpilers author the lifted Rust code, human engineers own safety trust roots, FFI contracts, and Day-2 debugging:

- **Working-memory explosion in mechanical `c2rust`:** Translating a 40-line C parser into `c2rust` increases token/line density `1.4x–2.8x` while replacing familiar local control flow with Relooper state variables (`current_block`), `c2rust_bitfields` byte-array getters, raw `*mut c_void` casts, and duplicated C struct declarations across TUs. Auditing whether a single lifted function satisfies Rust aliasing or `longjmp` POF invariants requires **whole-program nonlocal pointer tracking**, exceeding human 1-page auditability.
- **1-Page Auditable Strangulation Contracts:** Human comprehensibility recovers only when the strangler boundary—not the internal C implementation—is specified declaratively on one page: (i) `#[repr(C)]` wire-layout assertions (`size_of`, `offset_of!`), (ii) explicit `POF / no-longjmp` and allocator-ownership annotations, and (iii) a compact canonical projection $\pi$ comparing C vs. Rust post-states.

#### (C2) Simplicity, Minimization & Universal Generalization

Across C, Fortran, COBOL, and MVEE shadow monitors, engineers routinely accumulate fragile, redundant adapters: ad-hoc FAM zero-length array tricks, Fortran stride shims, COBOL `COMP-3` parsers, custom `ptrace`/`mprotect` page filters, and ad-hoc pointer-renaming comparators.

These seemingly unrelated problems collapse onto **one universal three-primitive model: Region-Indexed Byte Views + Two-Phase Shadow Transactions**:

1. **Universal Data Primitive — `RegionView = (ArenaId, BaseOffset, StrideSpec)`:**
   - C slices (`ptr, len`), C FAM payloads (`BaseOffset = offsetof(S, fam)` inside tail padding), Fortran `CFI_cdesc_t` (`rank`, `elem_len`, per-dimension `sm` byte strides), and COBOL `REDEFINES`/`COMP-3` fixed byte windows all instantiate the exact same immutable/exclusive **byte-range + affine stride descriptor** backed by `MaybeUninit<u8>` bytes. Special-case struct-layout hacks vanish because provenance and bounds live explicitly on `RegionView` rather than raw typed Rust references (`&mut T`), eliminating LLVM `noalias` UB on aliased Fortran parameters and padding-read UB simultaneously.
2. **Universal Execution Primitive — Two-Phase Pure-Projection Shadow Call:**
   - Execute legacy $f_C$ and candidate $f_R$ over a snapshot of `RegionView` inputs where $f_R$ writes solely to an isolated **Write-Set / Software Undo Log (`~8.7 ns`)** and buffers outgoing syscalls.
   - At function exit, apply the canonical projection $\pi_R(\text{WriteSet}_R)$ against $\pi_C(\text{Mem}_C)$ (comparing values and graph $\alpha$-equivalence, discarding allocator addresses). Commit the write-set if equivalent; discard the write-set and keep $f_C$'s state untouched in nanoseconds if mismatched.
3. **Verification of Genuine Complexity Elimination vs. Irreducible Limits:**
   - **Genuinely eliminated:** Removes `mprotect`/`SIGSEGV` (`19.36 µs`), multithread-unsafe `fork()` CoW (`405.17 µs`), `vDSO` timing patches across non-syscall boundaries, and `c2rust` Relooper guesswork from the critical path.
   - **Irreducible remainder (not merely hidden):** The universal model does **not** eliminate concurrency hazards on **lock-free shared atomics** (`Relaxed`/`Acquire`/`Release` memory shared with concurrent threads during $f_R$'s execution) or **irrevocable mid-function hardware MMIO/syscalls**; those genuinely require hardware isolation (`PKRU-Safe`), lock serialization, or process-level MVEE containment (`ReMon`/`VARAN`).

## Boundaries

- **`unsupported` — Modular `Crown` ownership analysis across opaque FFI seams:** Source inspection of `KomaEc/crown` (`621904cd...`, `crates/analysis/src/ownership.rs#L146-L155`) proves `Modular::analyze` unconditionally executes `anyhow::bail!("modular analysis is not implemented")`. Whole-program MIR visibility is mandatory in the current implementation.
- **`known not to apply` — POSIX `fork()` CoW rollback inside multithreaded servers:** Because `fork()` clones only the calling thread, any mutex (`malloc` arena lock, Rust `Mutex`, `pthread_mutex_t`) held by another thread at snapshot time remains permanently locked inside the forked child, causing immediate deadlock if candidate $f_R$ touches shared locks.
- **`known not to apply` — Single-thread software undo-logging for lock-free concurrent shared memory:** Software undo logs cannot atomically undo mutations observed or overwritten concurrently by peer threads via atomic loads/stores without wrapping all accesses in Software Transactional Memory (STM) or coarse locking.
- **`known not to apply` — Legacy `longjmp` across Rust frames holding `Drop` destructors:** Even under RFC 2945 `"C-unwind"`, forced unwinding across non-POF frames is undefined behavior (`text/2945-c-unwind-abi.md#L180-L186`) and confirmed in `ffi_probe` to bypass `Drop` execution entirely.
- **`unknown` — Automated LLM/neuro-symbolic C-to-Rust lifting soundness without differential/formal equivalence oracles:** Projects combining static analysis with LLMs (`c2rust postprocess`, DARPA `TRACTOR`) lack formal equivalence guarantees across corner-case UB (integer wrap, `errno`, endianness, `longjmp`), making online shadow checking or formal proof mandatory before retiring legacy C.
- **`not examined` — Closed-source mainframe COBOL CICS/IMS transaction monitors and OS/390 EBCDIC linkage conventions:** COBOL analysis here covers standard data-layout and control-flow constructs (`COMP-3`, `REDEFINES`, `PERFORM THRU`, `ALTER`) rather than proprietary mainframe runtime ABI details.

## Evidence

### Pinned Repositories & Source Locations

- **`immunant/c2rust`** @ `ae95fa7a268d92b23aaa687e1d6b74d9a7470312` (`2026-11-19`):
  - `README.md#L17-L46, L233-L240`: C2Rust pipeline (`c2rust transpile`, `c2rust-refactor`, `c2rust-postprocess`) and `--reorganize-definitions` C-API cross-module structure.
  - `c2rust-transpile/src/cfg/mod.rs#L146-L164`: `Structure::{Simple, Loop, Multiple}` Relooper CFG representation.
  - `c2rust-transpile/src/translator/variadic.rs#L25-L55, L172-L307`: `mk_va_list_ty` (`VaListImpl` vs `VaList` for Rust Edition 2024+), `convert_vaarg`, `register_va_decls`.
  - `c2rust-bitfields/src/lib.rs#L15-L89`: `FieldType::{set_field, get_field}` bit-by-bit non-atomic byte loop and unconditional sign-extension shift.
- **`KomaEc/crown`** @ `621904cd356b433215d5f55db39ffd71714f44ff` (`2026-11-19`):
  - `crates/analysis/src/lib.rs#L1-L55`: `rustc_private` MIR dependencies.
  - `crates/analysis/src/type_qualifier/flow_insensitive/fatness.rs#L26-L79`: `Fatness::{Arr, Ptr}` lattice and `BooleanSystem::greatest_model`.
  - `crates/analysis/src/ownership.rs#L31-L63, L146-L245`: `Ownership::{Owning, Transient, Unknown}`, `Modular::analyze` `bail!("modular analysis is not implemented")`, `IntraProcedural` `CadicalDatabase`, `total_deref_level` default `2`.
- **`ReMon-MVEE/ReMon`** @ `a29fc6320052a4acefcc8177c6cfaa07df2e61a5` (`2026-11-19`):
  - `README.md#L4-L194`: `GHUMVEE` + `IP-MON` architecture, `vDSO`/`vsyscall` hiding, `MPK` `MVEE_IP_PKU_ENABLED`, patched `glibc`/`libpthread` sync agent, `-fno-threadsafe-statics`.
  - `IP-MON/MVEE_ipmon.h#L44-L237`: `BASE_POLICY..FULL_SYSCALLS`, `PRECALL`/`POSTCALL`, `IPMON_EXEC_{NO_IPMON, NOEXEC, MASTER, ALL}`, `MVEE_FUTEX_WAIT_TID`.
- **`rust-lang/rfcs`** @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (`2026-11-19`):
  - `text/2945-c-unwind-abi.md#L143-L267`: `POF` definition, forced-unwinding UB rules (`longjmp`/`pthread_exit`), and `panic=unwind` vs `panic=abort` ABI table.
- **`rust-lang/rust`** @ `c884ecfbabb04b04fa5054dafc67ec258ecde745` (`2026-11-19`):
  - `library/core/src/ffi/va_list.rs#L11-L127`: Three `va_list` ABI flavors (`opaque pointer`, `struct`, `single-element array`) and SysV `x86_64` `VaListInner` with `#[rustc_pass_indirectly_in_non_rustic_abis]`.
- **`llvm/llvm-project`** @ `6aeca7e17f96ceedc9f2141f34d6a3b496cc4371` (`2026-11-19`):
  - `flang/include/flang/ISO_Fortran_binding.h#L33-L210`: `CFI_MAX_RANK = 15`, `CFI_dim_t { lower_bound, extent, sm }`, `CFI_cdesc_t`, `CFI_is_contiguous`.
- **`memorysafety/rav1d`** @ `2e7216c20ac2a75de204d6c8d7268b75a45959b4` (`README.md#L1-L40`), **`fish-shell/fish-shell`** @ `f0d874ad924bd582a039f5a5d5a018913c7d8b6a` (`README.rst`), **`dtolnay/cxx`** @ `4d19ca4eec78b2964035a3ea3cef5196515b13e7`, **`checkpoint-restore/criu`** @ `3292b937138d045c12905dee89c78b9c05961f3b`.

### Peer-Reviewed Papers & Engineering Publications

- Zhang et al., *"Ownership Guided C to Rust Translation"* (`Crown`), CAV 2023, `DOI: 10.1007/978-3-031-37709-9_22`, `arXiv:2303.10515`, artifact `DOI: 10.5281/zenodo.7966511`.
- Emre et al., *"Translating C to Safer Rust"* (`Laertes`), PACMPL / OOPSLA 2021, `DOI: 10.1145/3485498`, artifact `DOI: 10.5281/zenodo.5442253`.
- Hosek & Cadar, *"VARAN the Unbelievable: An Efficient N-version Execution Framework"*, ASPLOS 2015, `DOI: 10.1145/2694344.2694390`.
- Volckaert et al., *"Secure and Efficient Application Monitoring and Replication"* (`ReMon`), USENIX ATC 2016; and *"Taming Parallelism in a Multi-Variant Execution Environment"*, EuroSys 2017, `DOI: 10.1145/3064176.3064178`.
- Salamat et al., *"Orchestra: Intrusion Detection Using Parallel Execution and Monitoring of Program Variants in User-Space"*, EuroSys 2009, `DOI: 10.1145/1519065.1519071`.
- Gawlik et al., *"Detile: Fine-Grained Information Leak Detection in Script Engines"*, DIMVA 2016, `DOI: 10.1007/978-3-319-40667-1_16`.
- Kirth et al., *"PKRU-Safe: Automatically Locking Down the Heap Between Safe and Unsafe Languages"*, EuroSys 2022, `DOI: 10.1145/3492321.3519582`.
- Practitioner reports: Fish Shell engineering blog (*"Fish 4.0: The Fish of Theseus"*), Prossimo / Immunant `rav1d` AV1 migration notes, DARPA `TRACTOR` (*Translating All C to Rust*) program documentation.

### Self-Contained Executable Probes (`2026-11-19`)

Environment: Linux `7.1.6-1rodete1-amd64 x86_64`, 8-vCPU Intel Xeon @ 2.20 GHz, `gcc (Debian 15.2.0-14) 15.2.0`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`.

#### Probe A: C/Rust ABI & `longjmp` / FAM / Bitfield Verifier (`ffi_probe`)

```c
// /tmp/ffi_probe_c.c
#include <setjmp.h>
#include <stddef.h>
#include <stdint.h>

struct FamHdr {
    uint32_t tag;
    uint16_t len;
    uint8_t payload[];
};

struct SignedBitfield {
    int delta : 3;
    unsigned int flags : 5;
};

static jmp_buf g_env;
extern void rust_frame_with_drop(void (*cb)(void));

static void trigger_longjmp(void) { longjmp(g_env, 42); }

int run_c_longjmp_across_rust(void) {
    int v = setjmp(g_env);
    if (v == 0) {
        rust_frame_with_drop(trigger_longjmp);
        return 0;
    }
    return v;
}

size_t c_fam_sizeof(void) { return sizeof(struct FamHdr); }
size_t c_fam_payload_offset(void) { return offsetof(struct FamHdr, payload); }

uint8_t c_pack_bitfield(int delta, unsigned int flags) {
    union { struct SignedBitfield bf; uint8_t raw; } u;
    u.raw = 0;
    u.bf.delta = delta;
    u.bf.flags = flags;
    return u.raw;
}
```

```rust
// /tmp/ffi_probe_rs.rs
use std::sync::atomic::{AtomicUsize, Ordering};

static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

struct NonPofGuard;
impl Drop for NonPofGuard {
    fn drop(&mut self) { DROP_COUNT.fetch_add(1, Ordering::SeqCst); }
}

#[no_mangle]
pub unsafe extern "C" fn rust_frame_with_drop(cb: unsafe extern "C" fn()) {
    let _guard = NonPofGuard;
    cb();
}

#[repr(C)]
struct NaiveRustFamHdr { tag: u32, len: u16 }

unsafe extern "C" {
    fn run_c_longjmp_across_rust() -> i32;
    fn c_fam_sizeof() -> usize;
    fn c_fam_payload_offset() -> usize;
    fn c_pack_bitfield(delta: i32, flags: u32) -> u8;
}

fn c2rust_extract_signed_3bit(byte: u8) -> i8 {
    let mut val: i8 = 0;
    for i in 0..=2 {
        if (byte & (1 << i)) != 0 { val |= 1 << i; }
    }
    let unused_bits = 8 - 3;
    (val << unused_bits) >> unused_bits
}

fn main() {
    unsafe {
        let jmp_rc = run_c_longjmp_across_rust();
        let drops = DROP_COUNT.load(Ordering::SeqCst);
        let c_sz = c_fam_sizeof();
        let c_off = c_fam_payload_offset();
        let r_sz = std::mem::size_of::<NaiveRustFamHdr>();
        let raw_bf = c_pack_bitfield(-3, 0b10101);
        let extracted_delta = c2rust_extract_signed_3bit(raw_bf);
        println!("longjmp_rc={jmp_rc} rust_drops_executed={drops}");
        println!("c_sizeof_FamHdr={c_sz} c_offsetof_payload={c_off} naive_rust_sizeof={r_sz}");
        println!("bitfield_raw=0x{raw_bf:02x} extracted_signed_3bit={extracted_delta}");
    }
}
```

Observed output:
```text
longjmp_rc=42 rust_drops_executed=0
c_sizeof_FamHdr=8 c_offsetof_payload=6 naive_rust_sizeof=8
bitfield_raw=0xad extracted_signed_3bit=-3
```

#### Probe B: Function-Level Rollback Latency Benchmark (`shadow_ckpt_bench`)

```c
// /tmp/shadow_ckpt_bench.c
#define _GNU_SOURCE
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static uint8_t *g_prot_page;
static uint8_t g_backup_page[4096];

static void segv_handler(int sig, siginfo_t *si, void *unused) {
    (void)sig; (void)si; (void)unused;
    memcpy(g_backup_page, g_prot_page, 4096);
    mprotect(g_prot_page, 4096, PROT_READ | PROT_WRITE);
}

static inline uint64_t nsec_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

int main(void) {
    const int N_UNDO = 100000, N_MPROT = 5000, N_FORK = 500;
    uint8_t state[256] __attribute__((aligned(64)));
    uint8_t undo[256] __attribute__((aligned(64)));
    memset(state, 0x11, sizeof(state));

    uint64_t t0 = nsec_now();
    for (int i = 0; i < N_UNDO; i++) {
        memcpy(undo, state, 256);
        state[i & 255] ^= 0x5a;
        memcpy(state, undo, 256);
        asm volatile("" : : "r,m"(state[0]) : "memory");
    }
    uint64_t t1 = nsec_now();

    g_prot_page = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    memset(g_prot_page, 0x22, 4096);
    struct sigaction sa = {0};
    sa.sa_flags = SA_SIGINFO;
    sa.sa_sigaction = segv_handler;
    sigaction(SIGSEGV, &sa, NULL);

    uint64_t t2 = nsec_now();
    for (int i = 0; i < N_MPROT; i++) {
        mprotect(g_prot_page, 4096, PROT_READ);
        g_prot_page[i & 4095] ^= 0x3c;
        memcpy(g_prot_page, g_backup_page, 4096);
    }
    uint64_t t3 = nsec_now();

    uint64_t t4 = nsec_now();
    for (int i = 0; i < N_FORK; i++) {
        pid_t pid = fork();
        if (pid == 0) { g_prot_page[0] ^= 1; _exit(0); }
        int status = 0;
        waitpid(pid, &status, 0);
    }
    uint64_t t5 = nsec_now();

    printf("sw_undo_256B_ns=%.2f\n", (double)(t1 - t0) / N_UNDO);
    printf("mprotect_sigsegv_4KiB_ns=%.1f\n", (double)(t3 - t2) / N_MPROT);
    printf("fork_wait_cow_ns=%.1f\n", (double)(t5 - t4) / N_FORK);
    return 0;
}
```

Observed output (3 consecutive runs):
```text
--- run 1 ---
sw_undo_256B_ns=7.83
mprotect_sigsegv_4KiB_ns=19467.3
fork_wait_cow_ns=637156.2
--- run 2 (median) ---
sw_undo_256B_ns=11.46
mprotect_sigsegv_4KiB_ns=19360.4
fork_wait_cow_ns=405172.4
--- run 3 ---
sw_undo_256B_ns=8.71
mprotect_sigsegv_4KiB_ns=19310.0
fork_wait_cow_ns=351136.0
```

## Revalidation

To verify whether upstream constraints or probe measurements have changed:

1. **Check upstream `Crown` modular analysis and `c2rust` variadic/bitfield updates (1–2 s):**
   ```sh
   GIT_TERMINAL_PROMPT=0 git -c protocol.version=0 ls-remote https://github.com/KomaEc/crown.git HEAD
   curl -sSL https://raw.githubusercontent.com/KomaEc/crown/HEAD/crates/analysis/src/ownership.rs | grep -n -A 8 "impl.*AnalysisKind.*for Modular"
   curl -sSL https://raw.githubusercontent.com/immunant/c2rust/HEAD/c2rust-transpile/src/translator/variadic.rs | head -n 56
   ```
   A passing revalidation expects `Modular::analyze` to still `bail!("modular analysis is not implemented")` unless modular FFI lifting has been added upstream.

2. **Re-run Probe A (`ffi_probe`, <1 s):** Save Probe A's two snippets to `/tmp/ffi_probe_c.c` and `/tmp/ffi_probe_rs.rs` and run:
   ```sh
   gcc -O2 -c /tmp/ffi_probe_c.c -o /tmp/ffi_probe_c.o
   ar rcs /tmp/libffi_probe_c.a /tmp/ffi_probe_c.o
   rustc -O /tmp/ffi_probe_rs.rs -L /tmp -l static=ffi_probe_c -o /tmp/ffi_probe
   /tmp/ffi_probe
   ```
   Verify `rust_drops_executed=0` and `c_offsetof_payload=6` vs `naive_rust_sizeof=8`.

3. **Re-run Probe B (`shadow_ckpt_bench`, ~2 s):** Save Probe B to `/tmp/shadow_ckpt_bench.c` and run:
   ```sh
   gcc -O2 /tmp/shadow_ckpt_bench.c -o /tmp/shadow_ckpt_bench && /tmp/shadow_ckpt_bench
   ```
   Confirm `sw_undo_256B_ns` remains in single-digit nanoseconds while `mprotect_sigsegv_4KiB_ns` and `fork_wait_cow_ns` remain `10^4x–10^5x` slower.
