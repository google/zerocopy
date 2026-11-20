# Cross-Boundary Rust/C Aliasing, Dead-Store Elimination, Memory-Barrier Contracts, and Thread-Local Destructor Reentrancy

## Summary

Cross-language compilation and shared runtime execution expose two classes of Rust/C Foreign Function Interface (FFI) soundness hazards invisible when Rust and C translation units are checked separately:

1. **Cross-Language Aliasing, Dead-Store Elimination (DSE), and `asm!` Barrier Contracts:**
   - Under Cross-Language LTO (`-Clinker-plugin-lto` + `clang -flto=thin`; linker-plugin/bitcode mechanics in `cross-language-lto-linker-plugin-bitcode-and-llvm-ir-semantics`), `DeadStoreElimination` (`MemorySSA` over `@llvm.lifetime.end.p0` / `free`) dissolves the `extern "C"` boundary and deletes inlined C `memset` zeroization ahead of Rust scope exit or deallocation.
   - Fusing C effective-type TBAA (`!tbaa`, `ISO/IEC 9899:2024` §6.5p7) with Rust capability provenance (`noalias`, `!alias.scope` / `!noalias` via `InlineFunction.cpp:1220-1282`) causes silent miscompilation when Rust legally type-puns memory passed to C helpers (`GCC 15.2.0 -O2` forwarding stale supervisor privilege `0x100` past `*alias_raw = 0`) or holds a raw pointer in C concurrent with `&mut [u8]`.
   - Live `rustc 1.98.0-nightly` (`14210df0e27c` / `LLVM 22.1.6`) probes confirm `compiler/rustc_codegen_llvm/src/asm.rs:293-343`: `compiler_fence(Ordering::SeqCst)` (`fence syncscope("singlethread")`) and `asm!(..., options(nomem))` (`memory(inaccessiblemem: readwrite)`) both fail to stop DSE of `ptr::write_bytes`—with `options(nomem)` spilling 32 secret bytes onto `(%rsp)..31(%rsp)` before deleting `@llvm.memset`. `options(readonly)` (`memory(read, inaccessiblemem: readwrite)`, matching `zeroize::optimization_barrier`) preserves prior writes (`ModRefInfo::Ref`) yet permits load-forwarding across `asm!` in bidirectional FFI/trap-frame handoffs, which require default `ModRefInfo::ModRef` (omitting both `nomem` and `readonly`).

2. **Hosted `thread_local!` Destructor Teardown, Late Initialization Leaks, and Cyclic Resurrection:**
   - On `glibc 2.41` (`74f59e9271cb`), worker-thread teardown runs `__call_tls_dtors` (`__cxa_thread_atexit_impl`) strictly *before* `__nptl_deallocate_tsd` (`pthread_create.c:453-456`), so C `pthread_key_create` destructors probing Rust `LocalKey::try_with` observe `State::Destroyed` (`AccessError`; `LocalKey::with` aborts across non-`"C-unwind"` `extern "C"`).
   - Main-thread `exit()` (`stdlib/exit.c:43-149`) runs `__call_tls_dtors` -> `atexit`/`__cxa_atexit` -> `_dl_fini` (`.fini_array`) while **skipping POSIX TSD destructors completely**. Lazy `LocalKey` slots first initialized inside `atexit` or `.fini_array` enter `State::Alive` *after* `__call_tls_dtors` returned and leak `Drop`; on `musl v1.2.5` (`0784374d5614`, lacking `__cxa_thread_atexit_impl`), Rust falls back to `guard/key.rs` (`pthread_key_create`), causing main-thread `exit()` to skip Rust `thread_local!` destructors altogether.
   - `std::sys::thread_local::native` (`lazy.rs:112-123`, `eager.rs:64-74`) makes `State::Destroyed` absorbing (`0` resurrections), whereas `os::Storage::destroy_value` (`os.rs:222-244`) resets `key` to `null_mut()` after `drop(ptr)`, permitting cyclic cross-slot resurrection up to `PTHREAD_DESTRUCTOR_ITERATIONS = 4` (observed `cyc_a=4, cyc_b=4, leaked_blocks=1`) and starving `guard/key.rs:38-59`'s `DEFER -> RUN` `rt::thread_cleanup`.

## Applicability

These findings govern Rust/C FFI verification and runtime boundary contracts across the seven subjects in `REPORT.json`:

- **Compiler & Aliasing (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `llvm/llvm-project@1780833aa0f119a425d7f993aaac29d03cb04da6`, `GCC 15.2.0`):** Inspection of `TypeBasedAliasAnalysis.cpp`, `ScopedNoAliasAA.cpp`, `InlineFunction.cpp`, `DeadStoreElimination.cpp`, `CodeGenTBAA.cpp`, and `rustc_codegen_llvm` (`asm.rs`, `intrinsic.rs`), paired with `x86_64-unknown-linux-gnu` IR/assembly execution probes on `rustc 1.98.0-nightly` (`LLVM 22.1.6`) and `gcc 15.2.0 -O2 -fstrict-aliasing`.
- **Hosted TLS Runtime (`bminor/glibc@74f59e9271cbb4071671e5a474e7d4f1622b186f`, `kraj/musl@0784374d561435f7c787a555aeab8ede699ed298`, `rust-lang/rust` `std::sys::thread_local`):** Inspection of `std::thread::LocalKey`, `std::sys::thread_local::{mod.rs, native/{eager.rs, lazy.rs}, os.rs, destructors/{linux_like.rs, list.rs}, guard/key.rs, key/unix.rs}`, `glibc 2.41`, and `musl v1.2.5`, verified by mixed Rust+C execution on `glibc 2.41`.
- **Zeroization (`RustCrypto/utils@77d1a3e6c2e8c28f49189258abb5d4405c0f1330`):** Inspection of `zeroize/src/{lib.rs, barrier.rs, bulk.rs}`.

**Scope Split with Prior Corpus Reports:** Bitcode containers and `-Clinker-plugin-lto` plumbing belong to `cross-language-lto-linker-plugin-bitcode-and-llvm-ir-semantics`; register/SIMD spills and `LFENCE` hoisting to `compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences`; per-target TLS relocations to `rust-thread-local-storage-models-and-runtime-contracts`; and intra-Rust `Tree Borrows` / `Stacked Borrows` to `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes`.

## Findings

### 1. Cross-Language Aliasing Algebra Mismatch: C Effective-Type TBAA vs. Rust Capability Provenance

`Basis: normative + source + derived`

Separate compilation treats `extern "C"` calls as opaque memory-effect barriers (unless marked `readonly`/`memory(none)`). Cross-language ThinLTO dissolves that barrier and merges two incompatible aliasing models inside one LLVM IR function:

1. **C Effective-Type TBAA (`ISO/IEC 9899:2024` §6.5p7; Krebbers *CPP 2013*, DOI `10.1007/978-3-319-03545-1_4`):**
   - C prohibits accessing an object through an lvalue of incompatible effective type outside compatible aggregates or character types. `clang/lib/CodeGen/CodeGenTBAA.cpp:48-82` roots nominal `!tbaa` metadata at `"Simple C/C++ TBAA"` (placing `"omnipotent char"` directly underneath) and stamps `(BaseType, AccessType, Offset)` tags on C memory operations.
   - In `llvm/lib/Analysis/TypeBasedAliasAnalysis.cpp:327-338, 443-480, 630-676`, `matchAccessTags(A, B)` returns `true` (`MayAlias`) if either tag is `nullptr` (line `639`), protecting direct Rust-vs.-C pairs. However, when **both** instructions carry non-null C `!tbaa` tags (e.g., two C helpers inlined into a Rust caller sharing one buffer), `getLeastCommonType` and `mayBeAccessToSubobjectOf` (`lines 547-625`) return **`AliasResult::NoAlias`** unless one path descends through `"omnipotent char"` or matches a common struct offset.

2. **Rust Structural Capability Provenance (`noalias` / `ScopedNoAliasAA`):**
   - Rust emits **zero `!tbaa` tags** and permits arbitrary raw-pointer, `union`, or `transmute` punning under reference capability lifetimes (Stacked Borrows, *POPL 2020* DOI `10.1145/3371109`; Tree Borrows, *PLDI 2025* DOI `10.1145/3735592`).
   - Instead, `rustc` attaches parameter `noalias` attributes to `&T` (`noalias readonly` absent `UnsafeCell`) and `&mut T` / `&mut [u8]` (`noalias`). `llvm/lib/Transforms/Utils/InlineFunction.cpp:1220-1282` (`AddAliasScopeMetadata`) lowers each `noalias` parameter into a disjoint alias-scope domain (`createAnonymousAliasScopeDomain`), emits `@llvm.experimental.noalias.scope.decl`, and attaches `!alias.scope` / `!noalias` metadata checked by `ScopedNoAliasAA.cpp:68-208`.

**Observed `rustc 1.98.0-nightly -O` `!alias.scope` / `!noalias` Metadata (`noalias_inline.ll`):**
Inlining `inner_mut_slice(dst: &mut [u8], src: &[u8])` inside `caller_with_raw(p: *mut u8, n: usize)` (`dst = p[0..n]`, `src = p[1..1+n]`) emits:

```llvm
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
bb1.i:
  %_3.i = load i8, ptr %_6, align 1, !alias.scope !7, !noalias !4, !noundef !9
  store i8 %_3.i, ptr %p, align 1, !alias.scope !4, !noalias !7
bb2:
  %0 = getelementptr inbounds nuw i8, ptr %p, i64 2
  %_8.i = load i8, ptr %0, align 1, !alias.scope !7, !noalias !4, !noundef !9
  store i8 %_8.i, ptr %_6, align 1, !alias.scope !4, !noalias !7
  ret i8 %_3.i
```

Because `!alias.scope !4` (`dst`) and `!noalias !7` (`src`) are mutually non-aliasing, `ret i8 %_3.i` skips reloading `dst[0]`, and `AAMDNodes::merge` (`TypeBasedAliasAnalysis.cpp:482-491`) keeps both `!tbaa` and `!alias.scope`/`!noalias` active after cross-language inlining so **either** analysis returning `NoAlias` authorizes DSE and load forwarding.

---

### 2. Dead-Store Elimination and Store-to-Load Reordering of Zeroization and Trap-Frame Writes

`Basis: source + execution + derived`

In `llvm/lib/Transforms/Scalar/DeadStoreElimination.cpp:995-1160, 2765-2818`, `DSEPass` walks backward over `MemorySSA` from every `MemoryDef` and `isMemTerminatorInst` (`@llvm.lifetime.end.p0`, `free`) to delete `isRemovable(DefI)` stores invisible on function return (`eliminateDeadWritesAtEndOfFunction`). Across FFI boundaries, three hazards occur:

1. **Cross-Module `memset` Deletion Under ThinLTO:**
   - Moving `memset(buf, 0, n)` into an `extern "C"` C file fails under `-Clinker-plugin-lto` + `-flto=thin` (extending Yang et al., *USENIX Security '17*, pp. 1025–1040, and Simon, Chisnall, and Anderson, *IEEE EuroS&P 2018*, DOI `10.1109/EuroSP.2018.00009`): inlining the C wrapper exposes `@llvm.memset` before `@llvm.lifetime.end.p0` / `__rust_dealloc`, allowing `DSEPass` to delete the wipe cleanly.

2. **TBAA Privilege-Drop Miscompilation on Trap Frames (`GCC 15.2.0 -O2 -fstrict-aliasing`):**
   - When Rust passes `&mut TrapFrame` to two inlined C helpers accessing `struct trap_frame *` (`uint32_t sstatus`) and `uint64_t *` raw words, TBAA sees disjoint subtrees and forwards stale architectural state across the clear:
     ```c
     struct trap_frame { uint32_t sstatus; uint32_t sepc_lo; };
     uint32_t c_update_and_read_sstatus(struct trap_frame *tf, uint64_t *alias_raw) {
         tf->sstatus = 0x100; // Supervisor SPP
         *alias_raw = 0;      // Clear via uint64_t* word view
         return tf->sstatus;  // TBAA forwards 0x100 when tf == (void*)alias_raw!
     }
     ```
     Observed `x86_64` disassembly:
     ```asm
     c_update_and_read_sstatus:
         movl    $256, (%rdi)
         movl    $256, %eax    ; <-- Stale 0x100 forwarded across *alias_raw = 0!
         movq    $0, (%rsi)
         ret
     ```
     Stripping `!tbaa` on cross-language IR ingestion or compiling C FFI units with `-fno-strict-aliasing` prevents this miscompilation.

3. **`noalias` Breach Across Stateful C Contexts:**
   - If a C struct caches a raw `*mut u8` into a buffer simultaneously accessed in Rust via `&mut [u8]` passed to an inlined FFI call, `AddAliasScopeMetadata` marks the `&mut [u8]` accesses `!noalias` against the cached C pointer, authorizing DSE of Rust writes or reordering of C loads.

---

### 3. Formal Memory-Barrier Contracts for `extern "C"` and `core::arch::asm!`

`Basis: normative + source + execution`

Direct inspection of `compiler/rustc_codegen_llvm/src/asm.rs:293-345` and `intrinsic.rs:611-651` (`rust-lang/rust@14210df0e27c`), `RustCrypto/utils@77d1a3e6c2e8` (`zeroize/src/{barrier.rs, bulk.rs}`), and live `rustc 1.98.0-nightly -O` IR/assembly yields the 6-variant contract lattice in Table 1:

| Source Idiom / Barrier | `rustc` Lowering (`asm.rs:332-343` / `intrinsic.rs`) | LLVM `MemoryEffects` & Constraints | Stack Wipe Preserved? | Observed `rustc -O` Machine Code / Pathology | Bidirectional FFI / Trap-Frame Soundness? |
| :--- | :--- | :--- | :---: | :--- | :--- |
| **1. Plain `ptr::write_bytes(p, 0, 32)`** | `@llvm.memset.p0.i64` | None | **No** | Stack buffer & wipe completely deleted | **Unsound** |
| **2. `write_bytes` + `compiler_fence(SeqCst)`** | `fence syncscope("singlethread") seq_cst` | Single-thread ordering; no pointer escape | **No** | `movzbl (%rdi),%edi; callq *%rsi; #MEMBARRIER; retq` — wipe deleted | **Unsound** (does not escape `alloca`) |
| **3. `write_bytes` + `asm!("...", in(reg) p, options(nomem, nostack, preserves_flags))`** | `InlineAsmOptions::NOMEM` (`asm.rs:339-340`) | `memory(inaccessiblemem: readwrite)`, no `~{memory}` | **No** (**secret kept, wipe deleted!**) | `movups` copies 32B secret onto `(%rsp)..31(%rsp)`, then **DSE deletes `@llvm.memset`**, leaving secret on stack! | **Unsound** |
| **4. `write_bytes` + `asm!("...", in(reg) p, options(readonly, nostack, preserves_flags))`** (`zeroize::optimization_barrier`, `barrier.rs:65-70`) | `InlineAsmOptions::READONLY` (`asm.rs:341-342`) | `memory(read, inaccessiblemem: readwrite)`, `"r,~{memory}"` | **Yes** (`xorps; movaps` kept) | Zeroes stack `16(%rsp)` and `(%rsp)` before `# rax` | **Insufficient for writes by callee/asm**: `memory(read)` lets GVN reuse pre-barrier loads! |
| **5. `write_bytes` + `asm!("...", in(reg) p, options(nostack, preserves_flags))`** (Default `ModRef`, matching `black_box`) | Neither `NOMEM` nor `READONLY` (`asm.rs:293-298`, `intrinsic.rs:630`) | Full `ModRef` (`nounwind`), `"r,~{memory}"` | **Yes** (`xorps; movaps` kept) | Preserves prior writes AND invalidates stale caller loads | **Sound** for both zeroization and bidirectional trap-frame / CSR / FFI handoffs |
| **6. `ptr::write_volatile` loop** (`zeroize` fallback, `bulk.rs:64-94`) | `store volatile i8/u128` | Volatile architectural write | **Yes** (if at true address) | Vulnerable to SROA keeping secret in `%xmm0` if caller never spilled | **Only** guards volatile addresses |

**Observed `rustc 1.98.0-nightly -O` IR Excerpt (`barriers.ll`):**
```llvm
; wipe_asm_nomem: secrets copied to %buf via memcpy, @llvm.memset ELIMINATED by DSE!
  call void @llvm.memcpy.p0.p0.i64(ptr ... %buf, ptr ... %secret, i64 32, i1 false)
  call void asm sideeffect inteldialect "/* ${0:q} */", "r"(ptr nonnull %buf) #5 ; memory(inaccessiblemem: readwrite)
; wipe_asm_readonly (#6 = memory(read, inaccessiblemem: readwrite)) & wipe_asm_default_modref (#4 = nounwind):
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 1 dereferenceable(32) %buf, i8 0, i64 32, i1 false)
  call void asm sideeffect inteldialect "/* ${0:q} */", "r,~{memory}"(ptr nonnull %buf) #4
```

Thus, unilateral post-use zeroization requires at least `ModRefInfo::Ref` (`options(readonly)` with the buffer address passed via `in(reg) p`, or `ISO/IEC 9899:2024` §7.26.6.2 `memset_explicit`), whereas bidirectional trap-frame, CSR, or C FFI synchronization strictly requires `ModRefInfo::ModRef` (omitting both `nomem` and `readonly`). Note that `core::hint::black_box` (`intrinsic.rs:611-651`) emits full `ModRef` `"r,~{memory}"` assembly, though storing the input to `result_place` can spill secrets into the x86-64 red zone.

---

### 4. Hosted `thread_local!` Destructor Teardown Ordering Across glibc, musl, POSIX TSD, and ELF `.fini_array`

`Basis: normative + source + execution`

In `rust-lang/rust@14210df0e27c`, `LocalKey::try_with` (`library/std/src/thread/local.rs:457-463`) returns `Err(AccessError)` once a thread-local slot enters `State::Destroyed`, and `LocalKey::with` (`lines 422-430`) panics via `panic_access_error`. Table 2 summarizes exact teardown order across `glibc 2.41` (`74f59e9271cb`) and `musl v1.2.5` (`0784374d5614`):

| Lifecycle Event | `glibc 2.41` Execution Order | `musl v1.2.5` Execution Order | Cross-Boundary Hazard |
| :--- | :--- | :--- | :--- |
| **Worker thread exit** (`start_thread` return, `pthread_create.c:452-460`) | 1. `__call_tls_dtors()` (`cxa_thread_atexit_impl.c:147-165`, LIFO across C++ `thread_local` + Rust `native` TLS)<br>2. `__nptl_deallocate_tsd()` (`nptl_deallocate_tsd.c:22-93`, $\le 4$ rounds of POSIX `pthread_key_create` dtors)<br>3. `__libc_thread_freeres()` | 1. `__pthread_tsd_run_dtors()` (`pthread_key_create.c:77-96`, $\le 4$ rounds; Rust `guard::key::enable` pops `DTORS` on round 1) | On **glibc**, C `pthread_key_create` dtors execute **after** Rust `thread_local!` dtors have marked all Rust slots `Destroyed` (`AccessError`); `LocalKey::with` panics across `extern "C"` and aborts. |
| **Main thread `exit()`** (`stdlib/exit.c:43-149`) | 1. `__call_tls_dtors()` (`exit.c:50-51`)<br>2. `__exit_funcs` (`atexit`/`__cxa_atexit` LIFO, `exit.c:59-134`)<br>3. `_dl_fini()` (`.fini_array` in reverse dependency order, `dl-fini.c:46-138`)<br>4. `_IO_cleanup()` -> `_exit(status)`<br>*(POSIX TSD dtors **NOT** run!)* | 1. `__funcs_on_exit()` (`atexit`/`__cxa_atexit`, `atexit.c:26-37`)<br>2. `__libc_exit_fini()` (`.fini_array` + `_fini`, `exit.c:16-22`)<br>3. `__stdio_exit()` -> `_Exit(code)`<br>*(POSIX TSD dtors **NOT** run!)* | **(a) `glibc`:** Lazy `LocalKey` first touched inside `atexit` or `.fini_array` initializes *after* `__call_tls_dtors` finished, silently leaking `Drop`.<br>**(b) `musl v1.2.5`:** Lacking `__cxa_thread_atexit_impl`, Rust uses `guard/key.rs` (`pthread_key_create`), so main-thread `exit()` skips **all** Rust `thread_local!` destructors (`IEEE Std 1003.1-2024`: TSD dtors do not run on `exit()`). |
| **Last worker exits** (`pthread_create.c:495-497`) | Runs worker TLS + TSD cleanup, then calls `exit(0)` (`__nptl_nthreads == 0`) | Same POSIX `exit(0)` contract | Main-thread slots were already torn down on `pthread_exit`, or leaked on `_exit`. |

**Observed Mixed Rust+C Execution Trace (`glibc 2.41`, `tls_c.c` + `tls_main.rs`):**
```text
EVENT:rust_tls_drop:TLS_MAIN(self_reentry_ok=false)
EVENT:c_pthread_key_dtor(rust_alive=-1)
EVENT:worker_joined
EVENT:rust_tls_drop:TLS_MAIN(self_reentry_ok=false)
EVENT:c_atexit(rust_alive=-1,late_lazy=1)
EVENT:c_fini_array(rust_alive=-1,cyc_a=4,cyc_b=4,leaked_blocks=1)
```

This trace confirms: (1) on the worker thread, `TLS_MAIN` dropped first (`self_reentry_ok=false`), followed by `c_pthread_key_dtor` observing `rust_alive=-1` (`AccessError`); (2) on main-thread `exit(0)`, `TLS_MAIN` dropped inside `__call_tls_dtors`, after which `c_atexit` observed `rust_alive=-1` while lazily initializing `TLS_LATE` (`late_lazy=1`), which **never** emitted `EVENT:rust_late_lazy_drop_ran`; and (3) main-thread `c_pthread_key_dtor` never ran at `exit(0)`. Note also `cxa_thread_atexit_impl.c:112-113` and `destructors/list.rs:24-39`: initializing a distinct lazy `LocalKey` *during* `__call_tls_dtors` (or `list::run`, which drops its `RefMut` before `dtor(t)`) *does* prepend/push it for destruction in the ongoing teardown loop, whereas `System` allocator calls using destructor-bearing TLS hit `rtabort!` (`list.rs:10-12`).

---

### 5. Reentrancy State Machines and Cyclic Cross-Slot Resurrection (`native` vs. `os::Storage`)

`Basis: source + execution + derived`

Comparing `library/std/src/sys/thread_local/native/{eager.rs, lazy.rs}` against `os.rs` and `guard/key.rs` reveals a decisive divergence in state-machine monotonicity:

1. **`native::{EagerStorage, LazyStorage}` (`eager.rs:5-75`, `lazy.rs:22-124`):**
   - Forms a monotone lattice `Initial/Uninitialized -> Alive -> Destroyed`.
   - Recursive reinitialization of the same slot during `LazyStorage::get_or_init_slow` (`lazy.rs:80-99`) observes `State::Alive` on `self.state.replace(State::Alive)` and drops `old_value` (`assume_init_drop`) without registering a duplicate destructor (`D::register_dtor` runs only on `State::Uninitialized`).
   - Pre-drop `Destroyed` assignment (`lazy.rs:116-122`, `eager.rs:70-73`) blocks self-reentrancy during `Drop` (`AccessError`, avoiding `&mut T` + `&T` Stacked/Tree Borrows UB), and because `Destroyed` has zero outgoing transitions, each slot's destructor runs **at most once** (`0` resurrections).

2. **`os::Storage<T, ALIGN>` (`os.rs:79-244`) and `guard::key::enable` (`guard/key.rs:37-59`):**
   - `os::Storage` stores an `AlignedSystemBox<T, ALIGN>` inside a `pthread_key_t` / `TlsAlloc` slot (`os.rs:99-152, 165-219`). While `destroy_value` (`os.rs:222-244`) sets sentinel `1` (`ptr::without_provenance_mut(1)`) across `drop(ptr)` to block *self*-reentrancy (`ptr.addr() == 1` at line `187`), line `239` immediately resets the key to **`ptr::null_mut()`** upon returning and calls `guard::enable()` (`os.rs:242`).
   - Consequently, any downstream destructor accessing slot $A$ after $A$ finished dropping observes `null`, allocates a fresh `AlignedSystemBox<T>`, and re-arms TSD (`specific_used = true` in `glibc/nptl/nptl_deallocate_tsd.c:39`; `self->tsd_used = 1` in `musl/src/thread/pthread_key_create.c:83`).
   - Mutually resurrecting keys $A \leftrightarrow B$ iterate up to `PTHREAD_DESTRUCTOR_ITERATIONS = 4` (`bits/local_lim.h:67-69`; `cyc_a=4, cyc_b=4` in the live probe above) before glibc/musl abandon remaining non-null slots (`leaked_blocks=1`). Worse, because `os::Storage::destroy_value` resets `guard::key`'s `CLEANUP` key back to `DEFER` after every user destructor (`guard/key.rs:38-59`), cyclic cross-slot resurrection lasting $\ge 3$ rounds exhausts the 4-round budget before `CLEANUP` reaches `RUN`, silently starving `crate::rt::thread_cleanup()`.

## Boundaries

- **known not to apply:**
  - Placing `memset` or trap-frame stores in a separate C translation unit does **not** prevent DSE or TBAA reordering under `-Clinker-plugin-lto` + `-flto=thin`.
  - `compiler_fence(Ordering::SeqCst)` and `asm!(..., options(nomem))` do **not** inhibit LLVM DSE of preceding stack zeroization (`ptr::write_bytes`).
  - `zeroize::optimization_barrier` (`options(readonly)`) does **not** prevent GVN/CSE load forwarding across inline assembly that writes memory (`ModRefInfo::Mod` requires omitting `readonly`).
  - Native `#[thread_local]` slots (`native::{EagerStorage, LazyStorage}`) cannot resurrect on the same thread once transitioned to `State::Destroyed`.
- **unsupported:**
  - Unwinding Rust panics across non-`"C-unwind"` `extern "C"` TLS/atexit/TSD callbacks (`abort_on_dtor_unwind` in `mod.rs:207-221` aborts).
  - Exporting implicit PE `.tls$` variables across Windows DLLs (`dll-tls-export: false`).
- **unknown:**
  - Whether LLVM byte-type proposals or `-Zsanitizer=cfi` TypeSanitizer integration will resolve cross-language `!tbaa` conflicts without stripping `!tbaa` on ThinLTO ingestion.
  - Concurrent `dlclose` / `_dl_close_worker` (`l_tls_dtor_count` atomic wait) interactions with cyclic `os::Storage` resurrection under preemptive thread scheduling.
- **not examined:**
  - Bare-metal `no_std` per-CPU (`gs:` / `tp` / `TPIDR_EL1`) teardowns bypassing `std::sys::thread_local`, and dynamic Windows `FlsAlloc` / `ConvertThreadToFiber` cyclic resurrection beyond static inspection.

## Evidence

### Normative Specifications and Peer-Reviewed Papers

- `ISO/IEC 9899:2024` (C23): §6.5p7 (effective-type strict aliasing) and §7.26.6.2 (`memset_explicit`); `IEEE Std 1003.1-2024` (POSIX.1-2024 `pthread_key_create`); Itanium C++ ABI 1.86 (`__cxa_thread_atexit`).
- Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung. *Tree Borrows.* PACMPL / PLDI 2025, DOI `10.1145/3735592`.
- Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, and Derek Dreyer. *Stacked Borrows.* PACMPL / POPL 2020, DOI `10.1145/3371109`.
- Laurent Simon, David Chisnall, and Ross Anderson. *What You Get Is What You C.* IEEE EuroS&P 2018, DOI `10.1109/EuroSP.2018.00009`.
- Zhaomo Yang, Brian Johannesmeyer, Anders Trier Olesen, Sorin Lerner, and Kirill Levchenko. *Dead Store Elimination (Still) Considered Harmful.* USENIX Security '17, pp. 1025–1040.
- Robbert Krebbers. *Aliasing Restrictions of C11 Formalized in Coq.* CPP 2013, DOI `10.1007/978-3-319-03545-1_4`.

### Primary Upstream Repository Citations

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`): `compiler/rustc_codegen_llvm/src/{asm.rs:293-345, intrinsic.rs:611-651}`, `library/std/src/thread/local.rs:422-463`, `library/std/src/sys/thread_local/{mod.rs:26-222, native/eager.rs:5-75, native/lazy.rs:22-124, os.rs:79-244, destructors/linux_like.rs:15-55, destructors/list.rs:5-41, guard/key.rs:8-59, key/unix.rs:25-50}`.
- `llvm/llvm-project@1780833aa0f119a425d7f993aaac29d03cb04da6`: `llvm/lib/Analysis/{TypeBasedAliasAnalysis.cpp:327-676, ScopedNoAliasAA.cpp:68-234}`, `clang/lib/CodeGen/CodeGenTBAA.cpp:48-82`, `llvm/lib/Transforms/Utils/InlineFunction.cpp:1220-1310`, `llvm/lib/Transforms/Scalar/DeadStoreElimination.cpp:995-1160, 2765-2818`.
- `bminor/glibc@74f59e9271cbb4071671e5a474e7d4f1622b186f` (`glibc-2.41`): `stdlib/{cxa_thread_atexit_impl.c:19-165, exit.c:41-150}`, `nptl/{pthread_create.c:452-498, nptl_deallocate_tsd.c:22-93}`, `elf/dl-fini.c:24-154`, `sysdeps/unix/sysv/linux/bits/local_lim.h:67-69`.
- `kraj/musl@0784374d561435f7c787a555aeab8ede699ed298` (`v1.2.5`): `src/exit/{exit.c:16-31, atexit.c:26-66}`, `src/thread/pthread_key_create.c:77-96`.
- `RustCrypto/utils@77d1a3e6c2e8c28f49189258abb5d4405c0f1330`: `zeroize/src/{barrier.rs:51-71, bulk.rs:6-94, lib.rs:177-211, 785-801}`.

## Revalidation

Run these three self-contained checks in `/tmp/ffi_tls_reval` (`rustc 1.98.0-nightly` + `gcc 15.2.0` on Linux `x86_64`):

```bash
mkdir -p /tmp/ffi_tls_reval && cd /tmp/ffi_tls_reval

cat << 'EOF' > barriers.rs
#![crate_type = "lib"]
use core::{arch::asm, ptr, sync::atomic::{compiler_fence, Ordering}};
#[unsafe(no_mangle)] pub unsafe fn wipe_fence(s: &[u8; 32], f: fn(u8)) {
    let mut b = *s; f(b[0]); unsafe { ptr::write_bytes(b.as_mut_ptr(), 0, 32); }
    compiler_fence(Ordering::SeqCst);
}
#[unsafe(no_mangle)] pub unsafe fn wipe_nomem(s: &[u8; 32], f: fn(u8)) {
    let mut b = *s; f(b[0]); let p = b.as_mut_ptr();
    unsafe { ptr::write_bytes(p, 0, 32); asm!("/* {0} */", in(reg) p, options(nomem, nostack, preserves_flags)); }
}
#[unsafe(no_mangle)] pub unsafe fn wipe_readonly(s: &[u8; 32], f: fn(u8)) {
    let mut b = *s; f(b[0]); let p = b.as_mut_ptr();
    unsafe { ptr::write_bytes(p, 0, 32); asm!("/* {0} */", in(reg) p, options(readonly, nostack, preserves_flags)); }
}
#[unsafe(no_mangle)] pub unsafe fn wipe_modref(s: &[u8; 32], f: fn(u8)) {
    let mut b = *s; f(b[0]); let p = b.as_mut_ptr();
    unsafe { ptr::write_bytes(p, 0, 32); asm!("/* {0} */", in(reg) p, options(nostack, preserves_flags)); }
}
EOF
rustc --edition=2024 -O --emit=llvm-ir barriers.rs -o barriers.ll
grep -E "define void @wipe_|llvm.memset|memory\(|~\{memory\}" barriers.ll

cat << 'EOF' > tbaa_a.c
#include <stdint.h>
struct trap_frame { uint32_t sstatus; uint32_t sepc_lo; };
uint32_t c_update_and_read_sstatus(struct trap_frame *tf, uint64_t *alias_raw) {
    tf->sstatus = 0x100; *alias_raw = 0; return tf->sstatus;
}
EOF
gcc -O2 -fstrict-aliasing -S tbaa_a.c -o - | grep -A6 "c_update_and_read_sstatus:"

cat << 'EOF' > tls_c.c
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
extern int32_t rust_probe_tls_alive(void);
extern int32_t rust_probe_tls_late_lazy(void);
extern void rust_record_event(const char *ev);
static pthread_key_t k_tsd, k_a, k_b;
static int ca = 0, cb = 0, bal = 0;
static void d_tsd(void *x) { (void)x; char b[64]; snprintf(b, 64, "c_pthread_key_dtor(rust_alive=%d)", rust_probe_tls_alive()); rust_record_event(b); }
static void d_a(void *p) { free(p); bal--; ca++; int *q = malloc(4); *q = ca; bal++; pthread_setspecific(k_b, q); }
static void d_b(void *p) { free(p); bal--; cb++; int *q = malloc(4); *q = cb; bal++; pthread_setspecific(k_a, q); }
static void on_exit_cb(void) { printf("EVENT:c_atexit(rust_alive=%d,late_lazy=%d)\n", rust_probe_tls_alive(), rust_probe_tls_late_lazy()); fflush(stdout); }
__attribute__((destructor)) static void on_fini(void) { printf("EVENT:c_fini_array(rust_alive=%d,cyc_a=%d,cyc_b=%d,leaked_blocks=%d)\n", rust_probe_tls_alive(), ca, cb, bal); fflush(stdout); }
void c_setup(void) { pthread_key_create(&k_tsd, d_tsd); pthread_key_create(&k_a, d_a); pthread_key_create(&k_b, d_b); atexit(on_exit_cb); }
void c_arm(int cyc) { pthread_setspecific(k_tsd, (void*)1); if (cyc) { int *p = malloc(4); *p = 0; bal++; pthread_setspecific(k_a, p); } }
EOF
cat << 'EOF' > tls_main.rs
use std::ffi::{CStr, c_char};
unsafe extern "C" { fn c_setup(); fn c_arm(cyc: i32); }
struct MonitoredSlot(&'static str);
impl Drop for MonitoredSlot { fn drop(&mut self) { println!("EVENT:rust_tls_drop:{}(self_reentry_ok={})", self.0, TLS_MAIN.try_with(|_| ()).is_ok()); } }
struct LateSlot;
impl Drop for LateSlot { fn drop(&mut self) { println!("EVENT:rust_late_lazy_drop_ran"); } }
thread_local! { static TLS_MAIN: MonitoredSlot = const { MonitoredSlot("TLS_MAIN") }; static TLS_LATE: LateSlot = LateSlot; }
#[unsafe(no_mangle)] pub extern "C" fn rust_probe_tls_alive() -> i32 { TLS_MAIN.try_with(|_| 1).unwrap_or(-1) }
#[unsafe(no_mangle)] pub extern "C" fn rust_probe_tls_late_lazy() -> i32 { TLS_LATE.try_with(|_| 1).unwrap_or(-1) }
#[unsafe(no_mangle)] pub unsafe extern "C" fn rust_record_event(ev: *const c_char) { println!("EVENT:{}", unsafe { CStr::from_ptr(ev) }.to_string_lossy()); }
fn main() {
    unsafe { c_setup(); } TLS_MAIN.with(|_| {}); unsafe { c_arm(0); }
    std::thread::spawn(|| { unsafe { c_arm(1); } TLS_MAIN.with(|_| {}); }).join().unwrap();
    println!("EVENT:worker_joined");
}
EOF
gcc -O2 -c tls_c.c -o tls_c.o && rustc --edition=2024 -O tls_main.rs -Clink-arg=tls_c.o -o tls_main && ./tls_main
```

Expected results: `wipe_fence` and `wipe_nomem` omit `@llvm.memset`, whereas `wipe_readonly` and `wipe_modref` preserve it; `c_update_and_read_sstatus` sets `movl $256, %eax` ahead of `movq $0, (%rsi)`; and `./tls_main` prints `rust_tls_drop:TLS_MAIN` before `c_pthread_key_dtor(rust_alive=-1)`, omits `rust_late_lazy_drop_ran`, and prints `cyc_a=4,cyc_b=4,leaked_blocks=1`.
