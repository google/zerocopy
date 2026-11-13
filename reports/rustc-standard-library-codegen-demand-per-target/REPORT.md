# Standard-Library Code-Generation Demand Across Tier 1 Targets in Rust 1.99.1

## Summary

Compiling the Rust 1.99.1 standard-library stack (`core`, `alloc`, `std`,
`compiler_builtins`, `panic_unwind`, `panic_abort`, `std_detect`, `unwind`, and
`rtstartup`) from source or linking against its prebuilt `.rlib` artifacts
across the eight Tier 1 targets (`x86_64-unknown-linux-gnu`,
`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-unknown-linux-gnu`,
`aarch64-apple-darwin`, `aarch64-pc-windows-msvc`, `i686-unknown-linux-gnu`,
and `i686-pc-windows-msvc`) imposes a sharply stratified set of code-generation
requirements:

1. **Source-level intrinsic, target-feature, inline-assembly, and ABI inventory
   (`947,056` LOC across `1,515` non-test `.rs` files):**
   - **Intrinsics:** `core` declares **313 `#[rustc_intrinsic]` functions**
     (`library/core/src/intrinsics/mod.rs` and `fallback.rs`) and invokes `171`
     distinct intrinsics across `563` call sites (led by `transmute_unchecked`
     `114`, `unlikely` `29`, `abort` `21`, `atomic_cxchg` `15`, and
     `atomic_cxchgweak` `15`), while `alloc` declares `1` (`const_deallocate`)
     and calls `11` (`17` sites), `std` calls `36` (`48` sites), and
     `compiler_builtins` calls `3` (`unchecked_div`, `unchecked_rem`, `abort`).
   - **SIMD & target features:** `core` (including `core_arch` and `core_simd`)
     contains **19,695 `#[target_feature(enable = "...")]` annotations** across
     `121` distinct target features (`5,578` `sve`, `5,269` `neon`, `2,669`
     `avx512f`, `2,511` `avx512vl`, `1,887` `sve2`, `938` `avx512fp16`, `847`
     `avx512bw`), **`3,251` `extern "unadjusted"`** platform-intrinsic
     declarations, and **`32` `#[repr(simd)]`** vector types. No other
     standard-library crate uses `#[target_feature]` or `#[repr(simd)]`.
   - **Inline assembly:** Concentrated in `core` (`199` `asm!` sites, including
     `34` in `x86` and `5` in `x86_64`), `compiler_builtins` (`90` sites across
     `asm!`, `global_asm!`, and `naked_asm!`, including `13` on `x86_64`, `8` on
     `x86`, `9` on `aarch64`, and `17` on `arm`), `std` (`30` `asm!` sites),
     `std_detect` (`6` `asm!` sites, `4` on `aarch64` reading `mrs` system
     registers), and `unwind` (`1` site). `alloc`, `panic_unwind`,
     `panic_abort`, and `rtstartup` contain **zero** inline assembly.
2. **Minimal external runtime interface of `core` and `alloc` across all 8 Tier 1 targets:**
   Inspecting the compiled `.rlib` object files (`llvm-nm --no-llvm-bc`) shows
   that `libcore` (`649`–`1,213` defined symbols, `2.49`–`3.28 MB`) requires
   only **6 to 10 external symbols** on any Tier 1 target:
   - `1` panic hook (`_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind`),
   - `1` exception-handling personality (`rust_eh_personality` on ELF/Mach-O/MinGW
     or `__CxxFrameHandler3` on Windows MSVC),
   - `3`–`4` memory primitives (`memcpy`, `memcmp`, `memset`, plus `bcmp` on
     Linux ELF), and
   - `1`–`3` compiler-rt arithmetic/float libcalls (`__udivti3` on 64-bit
     targets or `__udivdi3`/`__aulldiv` on `i686`, plus `__extendhfsf2` and
     `__truncsfhf2` for `f16` conversions on x86/i686; `aarch64-apple-darwin`
     also references `_bzero`, and `x86_64/i686-pc-windows-msvc` reference
     `_fltused`).
   `liballoc` (`161`–`358` defined symbols, `0.74`–`1.08 MB`) adds only the
   **5 `___rustc` allocator shim symbols** (`__rust_alloc`, `__rust_dealloc`,
   `__rust_realloc`, `__rust_alloc_error_handler`,
   `__rust_no_alloc_shim_is_unstable_v2`), `_Unwind_Resume` (on DWARF targets),
   and `memmove`/`strlen`.
3. **Target-divergent atomics, unwinding, weak linkage, TLS, and special sections in `std` and `compiler_builtins`:**
   - **128-bit atomics:** Baseline `target_has_atomic` includes `"128"` on five
     Tier 1 targets (`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`,
     `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, and
     `aarch64-pc-windows-msvc`), but **omits `"128"` on baseline
     `x86_64-unknown-linux-gnu`** (`cpu=x86-64` lacks `+cmpxchg16b`) and both
     `i686` targets (which stop at `"64"` via `cmpxchg8b`). On
     `aarch64-unknown-linux-gnu`, default `+outline-atomics` causes
     `compiler_builtins` (`405` `.rcgu.o` objects) to emit `223` weak definitions
     and `112` internal references to `__aarch64_{cas,ldadd,ldclr,ldeor,ldset,swp}{1,2,4,8,16}_{relax,acq,rel,acq_rel}`
     gated by `__aarch64_have_lse_atomics`.
   - **Weak-linkage OS feature probing:** On Linux GNU targets, `libstd` emits
     **10 weak undefined ELF symbols (`STB_WEAK`)** on `x86_64` and `aarch64`
     (`__cxa_thread_atexit_impl`, `__dso_handle`, `copy_file_range`,
     `getrandom`, `gettid`, `pidfd_getpid`, `pidfd_spawnp`,
     `posix_spawn_file_actions_addchdir`, `posix_spawn_file_actions_addchdir_np`,
     `statx`) and **14 weak undefined symbols** on `i686-unknown-linux-gnu`
     (adding `__clock_gettime64`, `__clock_nanosleep_time64`, `__futimens64`,
     and `__utimensat64`).
   - **TLS & startup sections:** `std` uses `18` `#[thread_local]` attributes
     and `23` `thread_local!` macros, lowering to ELF `.tdata`/`.tbss`, Mach-O
     `__thread_vars`/`__thread_data`/`__thread_bss` (`_tlv_bootstrap`), and
     PE/COFF `.tls$` + `.CRT$XCT`/`.CRT$XLA`/`.CRT$XLB` TLS callbacks. In
     addition, `std` places `ARGV_INIT_ARRAY` in `.init_array.00099` on Linux
     ELF and `.CRT$XCT` on Windows, while `rtstartup` (`rsbegin.o` / `rsend.o`,
     `648 B` total) exists exclusively on `x86_64-pc-windows-gnu` to bracket
     `.eh_frame`, `.ctors.65535`, and `.dtors.65535`.

## Applicability

These findings apply to **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`, official release channel manifest
`channel-rust-1.99.1.toml` SHA-256
`fb152be80975c194aa5fc684b2aec3a6e14e2b855efe2faa4e5f8ae6e590f463`) across all
eight Tier 1 targets:

- **Exact observation:** Source-level counts were extracted from `s1991/library/`
  (plus `compiler_builtins 0.1.160`) after stripping all line and block
  comments (`//`, `///`, `//!`, `/* ... */`) so documentation doctests do not
  pollute attribute or ABI counts. Object-level symbol and section counts were
  extracted directly from the 72 crate-target pairs in the official Rust 1.99.1
  `rust-std` sysroot using LLVM 23.1.1's `llvm-nm` and `llvm-readobj`. MIR
  construct counts were extracted by compiling `core`, `alloc`, `unwind`, and
  `panic_abort` with `RUSTC_BOOTSTRAP=1 rustc +1.99.1 -C opt-level=3 --emit=mir`.

## Findings

### 1. Source-level codegen feature census across the 9 standard-library crates

Basis: source

Table 1 summarizes the comment-stripped source census across the nine
standard-library crates in `rust-lang/rust`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`).

| Crate | Non-Test `.rs` Files | Lines of Code | `#[rustc_intrinsic]` Decl / Call Sites (Unique) | `#[target_feature]` Attrs (Unique Features) | Inline `asm!` / `global_asm!` / `naked_asm!` Sites | `#[thread_local]` Attr / `thread_local!` Macro | `#[link_section]` Attrs | `#[link]` Attrs (`dylib` / `static`) | Non-Rust `extern` ABIs |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `core` (+ `core_arch`, `core_simd`) | `479` | `679,211` | `313` decl / `563` calls (`171` unique) | `19,695` (`121` features) | `199` (`160` arch-shared, `34` `x86`, `5` `x86_64`) | `1` / `0` | `0` | `0` | `"unadjusted"` (`3,251`), `"rust-call"` (`28`), `"C"` (`12`) |
| `alloc` | `93` | `67,583` | `1` decl / `17` calls (`11` unique) | `0` | `0` | `0` / `1` | `0` | `0` | `"rust-call"` (`6`), `"C"` (`1`) |
| `std` | `646` | `149,280` | `0` decl / `48` calls (`36` unique) | `0` | `30` (`asm!` in `sys/pal` & `backtrace`) | `18` / `23` | `2` (`.init_array.00099`, `.CRT$XCT`) | `23` (`22` `dylib`, `1` `static`) | `"C"` (`153`), `"system"` (`27`), `"efiapi"` (`18`) |
| `compiler_builtins` (`0.1.160`) | `240` | `44,755` | `0` decl / `6` calls (`3` unique) | `0` | `90` (`49` `asm!`, `15` `global_asm!`, `26` `naked_asm!`) | `0` / `0` | `0` | `3` (`dylib`) | `"C"` (`187`), `"aapcs"` (`28`), `"custom"` (`13`) |
| `panic_unwind` | `5` | `647` | `0` / `0` | `0` | `0` | `0` / `0` | `0` | `0` | `"C"` (`5`), `"system-unwind"` (`1`) |
| `panic_abort` | `3` | `131` | `0` / `0` | `0` | `0` | `0` / `0` | `0` | `0` | `"C"` (`3`) |
| `std_detect` | `43` | `4,716` | `0` / `0` | `0` | `6` (`4` `aarch64`, `1` `s390x`, `1` `loongarch`) | `0` / `0` | `0` | `1` (`dylib`) | `"system"` (`2`), `"C"` (`1`) |
| `unwind` | `4` | `576` | `0` / `0` | `0` | `1` (`wasm`) | `0` / `0` | `0` | `16` (`12` `dylib`, `4` `static`) | `"C"` (`33`), `"C-unwind"` (`3`) |
| `rtstartup` | `2` | `157` | `0` / `0` | `0` | `0` | `0` / `0` | `4` (`.eh_frame` `2`, `.ctors.65535` `1`, `.dtors.65535` `1`) | `0` | `"C"` (`5`) |

Key structural observations from the source census:

- **Top intrinsics called in `core`:** `transmute_unchecked` (`114`), `unlikely`
  (`29`), `abort` (`21`), `atomic_cxchg` (`15`), `atomic_cxchgweak` (`15`),
  `unchecked_sub` (`14`), `is_val_statically_known` (`11`), `assume` (`10`),
  `likely` (`9`), `const_eval_select` (`9`), `exact_div` (`8`), `atomic_load`
  (`8`), `atomic_store` (`8`), `copy` (`7`), `compare_bytes` (`7`),
  `write_bytes` (`7`), `three_way_compare` (`6`), `ctlz_nonzero` (`6`),
  `cttz_nonzero` (`6`), and `vtable_size`/`vtable_align`.
- **Tier 1 `#[target_feature]` distribution in `core::arch`:** On `aarch64`,
  the dominant features are `sve` (`5,578`), `neon` (`5,269`), `sve2` (`1,887`),
  `fcma` (`130`), `fp16` (`123`), `sve2-aes` (`76`), `i8mm` (`70`), `aes`
  (`68`), and `dotprod` (`44`). On `x86`/`x86_64`, the dominant features are
  `avx512f` (`2,669`), `avx512vl` (`2,511`), `avx512fp16` (`938`), `avx512bw`
  (`847`), `avx2` (`480`), `avx` (`322`), `sse2` (`297`), `avx512dq` (`287`),
  `sse4.1` (`163`), `avx10.2-512` (`145`), `fma` (`139`), `ssse3` (`96`), and
  `sse` (`95`).

### 2. Per-target `.rlib` object, symbol, and foreign import census across all 8 Tier 1 targets

Basis: execution

Table 2 reports the exact `.rlib` sizes, `.rcgu.o` object counts, defined
symbols, weak symbols, and undefined non-Rust foreign symbol imports across all
eight Tier 1 targets in the official Rust 1.99.1 toolchain (`llvm-nm --no-llvm-bc`
and `llvm-readobj --sections`).

| Tier 1 Target | `core` (`.rlib` Size / Def / Foreign `U`) | `alloc` (`.rlib` Size / Def / Foreign `U`) | `std` (`.rlib` Size / Def / Weak `w` / Foreign `U`) | `compiler_builtins` (`.rlib` Size / Objs / Def / Weak `W` / Foreign `U`) | `panic_unwind` (Def / Foreign `U` & Personality) | `panic_abort` (Def / Foreign `U`) | `std_detect` (Def / Foreign `U`) | `unwind` & `rtstartup` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `3.14 MB` / `730` / `9` (`memcpy`, `memcmp`, `memset`, `bcmp`, `__udivti3`, `__extendhfsf2`, `__truncsfhf2`, `rust_eh_personality`, `rust_begin_unwind`) | `1.03 MB` / `179` / `10` (`5` `__rust_alloc*`, `_Unwind_Resume`, `rust_eh_personality`, `memcpy`, `memmove`, `strlen`) | `12.24 MB` / `1,825` / `10` weak / `175` foreign (`135` libc/POSIX, `15` pthread/TLS, `12` `_Unwind_*`, `7` `__rust_*`, `6` mem) | `4.61 MB` / `309` objs / `880` def / `222` weak `W` / `19` foreign (`__addtf3..__unordtf2`, `fma`, `__udivti3`) | `11` def / `9` (`_Unwind_RaiseException`, `_Unwind_Resume`, `_Unwind_DeleteException`, `rust_eh_personality`, `5` `__rust_*`) | `2` def / `1` (`__rust_abort`) | `27` def / `0` foreign (uses `cpuid` inline asm) | `unwind`: `0` def; `rtstartup`: absent |
| `x86_64-pc-windows-msvc` | `2.49 MB` / `1,211` / `9` (`memcpy`, `memcmp`, `memset`, `_fltused`, `__udivti3`, `__extendhfsf2`, `__truncsfhf2`, `__CxxFrameHandler3`, `rust_begin_unwind`) | `0.75 MB` / `358` / `9` (`5` `__rust_alloc*`, `__CxxFrameHandler3`, `memcpy`, `memmove`, `strlen`) | `6.01 MB` / `3,286` / `0` weak / `164` foreign (`143` Win32/NT `__imp_*`, `7` `__rust_*`, `6` CRT, `4` mem, `2` SEH, `1` `_tls_index`) | `3.05 MB` / `233` objs / `1,334` def / `157` weak / `20` foreign (`__CxxFrameHandler3`, `_fltused`, `__chkstk`, `f128` helpers) | `28` def / `7` (`__CxxFrameHandler3`, `_CxxThrowException`, `??_7type_info@@6B@`, `__ImageBase`, `3` `__rust_*`) | `8` def / `1` (`__rust_abort`) | `28` def / `0` foreign | `unwind`: `3` def; `rtstartup`: absent |
| `x86_64-pc-windows-gnu` | `2.83 MB` / `721` / `6` (`memcpy`, `memcmp`, `memset`, `__udivti3`, `rust_eh_personality`, `rust_begin_unwind`) | `0.89 MB` / `178` / `10` (`5` `__rust_alloc*`, `_Unwind_Resume`, `rust_eh_personality`, `memcpy`, `memmove`, `strlen`) | `9.24 MB` / `1,667` (`9` objs, includes `windows_link` imports) / `0` weak / `179` foreign (`102` Win32, `56` MinGW/CRT, `9` `_Unwind_*`) | `3.12 MB` / `243` objs / `712` def / `0` weak / `16` foreign (`___chkstk_ms`, `__udivti3`, `f128` helpers) | `13` def / `9` (`_Unwind_RaiseException`, `_Unwind_Resume`, `_Unwind_DeleteException`, `rust_eh_personality`, `5` `__rust_*`) | `5` def / `1` (`__rust_abort`) | `8` def / `0` foreign | `unwind`: `3` def; **`rtstartup` (`rsbegin.o` + `rsend.o`): `648 B`, `10` syms** |
| `aarch64-unknown-linux-gnu` | `3.28 MB` / `649` / `7` (`memcpy`, `memcmp`, `memset`, `bcmp`, `__udivti3`, `rust_eh_personality`, `rust_begin_unwind`) | `1.08 MB` / `161` / `10` (`5` `__rust_alloc*`, `_Unwind_Resume`, `rust_eh_personality`, `memcpy`, `memmove`, `strlen`) | `12.87 MB` / `1,785` / `10` weak / `189` foreign (`150` libc/POSIX + outline-atomics, `14` pthread/TLS, `12` `_Unwind_*`) | `4.88 MB` / `405` objs / `835` def / `223` weak `W` / `117` internal+foreign (`112` `__aarch64_cas*`/`ldadd*` outline atomics) | `11` def / `9` (`_Unwind_RaiseException`, `_Unwind_Resume`, `_Unwind_DeleteException`, `rust_eh_personality`, `5` `__rust_*`) | `2` def / `1` (`__rust_abort`) | `9` def / `12` (`getauxval`, `open`, `read`, `close`, `memcpy`, `5` `__rust_alloc*`, `_Unwind_Resume`) | `unwind`: `0` def; `rtstartup`: absent |
| `aarch64-apple-darwin` | `2.64 MB` / `1,204` / `7` (`_memcpy`, `_memcmp`, `_memset`, `_bzero`, `___udivti3`, `_rust_eh_personality`, `rust_begin_unwind`) | `0.85 MB` / `245` / `10` (`5` `__rust_alloc*`, `__Unwind_Resume`, `_rust_eh_personality`, `_memcpy`, `_memmove`, `_strlen`) | `9.83 MB` / `2,615` / `0` weak / `199` foreign (`151` libSystem/Darwin, `25` pthread/`_tlv_bootstrap`, `11` `__Unwind_*`) | `3.53 MB` / `373` objs / `2,794` def / `0` weak / `20` foreign (`_sysctlbyname`, `___aarch64_have_lse_atomics`, `___stack_chk_guard`) | `20` def / `9` (`__Unwind_RaiseException`, `__Unwind_Resume`, `__Unwind_DeleteException`, `_rust_eh_personality`, `5` `__rust_*`) | `14` def / `1` (`__rust_abort`) | `140` def / `1` (`_sysctlbyname`) | `unwind`: `5` def; `rtstartup`: absent |
| `aarch64-pc-windows-msvc` | `2.49 MB` / `1,206` / `6` (`memcpy`, `memcmp`, `memset`, `__udivti3`, `__CxxFrameHandler3`, `rust_begin_unwind`) | `0.74 MB` / `354` / `9` (`5` `__rust_alloc*`, `__CxxFrameHandler3`, `memcpy`, `memmove`, `strlen`) | `5.97 MB` / `3,278` / `0` weak / `164` foreign (`143` Win32/NT `__imp_*`, `7` `__rust_*`, `6` CRT, `4` mem, `2` SEH, `1` `_tls_index`) | `3.06 MB` / `271` objs / `1,526` def / `194` weak / `21` foreign (`__CxxFrameHandler3`, `__chkstk`, `_fltused`, `copysign`) | `30` def / `7` (`__CxxFrameHandler3`, `_CxxThrowException`, `??_7type_info@@6B@`, `__ImageBase`, `3` `__rust_*`) | `8` def / `1` (`__rust_abort`) | `83` def / `1` (`IsProcessorFeaturePresent`) | `unwind`: `3` def; `rtstartup`: absent |
| `i686-unknown-linux-gnu` | `2.65 MB` / `728` / `10` (`memcpy`, `memcmp`, `memset`, `bcmp`, `__udivdi3`, `__extendhfsf2`, `__truncsfhf2`, `_GLOBAL_OFFSET_TABLE_`, `rust_eh_personality`, `rust_begin_unwind`) | `0.84 MB` / `178` / `11` (`5` `__rust_alloc*`, `_Unwind_Resume`, `rust_eh_personality`, `_GLOBAL_OFFSET_TABLE_`, `memcpy`, `memmove`, `strlen`) | `10.24 MB` / `1,834` / `14` weak / `178` foreign (`138` libc/POSIX, `15` pthread/TLS, `12` `_Unwind_*`, `7` `__rust_*`, `6` mem) | `3.74 MB` / `308` objs / `860` def / `214` weak `W` / `27` foreign (`__divdi3`, `__udivdi3`, `__moddi3`, `__umoddi3`, `__muldi3`, `__ashldi3`, `__lshrdi3`) | `11` def / `10` (`_Unwind_RaiseException`, `_Unwind_Resume`, `_Unwind_DeleteException`, `rust_eh_personality`, `_GLOBAL_OFFSET_TABLE_`, `5` `__rust_*`) | `2` def / `2` (`__rust_abort`, `_GLOBAL_OFFSET_TABLE_`) | `25` def / `2` (`bcmp`, `_GLOBAL_OFFSET_TABLE_`) | `unwind`: `0` def; `rtstartup`: absent |
| `i686-pc-windows-msvc` | `2.55 MB` / `1,213` / `9` (`_memcpy`, `_memcmp`, `_memset`, `__aulldiv`, `__fltused`, `___extendhfsf2`, `___truncsfhf2`, `___CxxFrameHandler3`, `rust_begin_unwind`) | `0.76 MB` / `321` / `9` (`5` `__rust_alloc*`, `___CxxFrameHandler3`, `_memcpy`, `_memmove`, `_strlen`) | `6.18 MB` / `3,038` / `0` weak / `164` foreign (`141` Win32/NT `__imp_*`, `8` CRT `__aulldiv`/`__aullrem`, `7` `__rust_*`, `4` mem, `2` SEH) | `3.39 MB` / `276` objs / `1,415` def / `194` weak / `19` foreign (`___CxxFrameHandler3`, `__aulldiv`, `__aullrem`, `__alloca_probe`) | `26` def / `6` (`___CxxFrameHandler3`, `__CxxThrowException@8`, `??_7type_info@@6B@`, `3` `__rust_*`) | `8` def / `1` (`__rust_abort`) | `90` def / `1` (`_memcmp`) | `unwind`: `3` def; `rtstartup`: absent |

### 3. Target-by-target codegen mechanisms: atomics, unwinding, TLS, and special sections

Basis: source + execution

Table 3 contrasts the target-specific codegen mechanisms across the eight Tier 1
targets (`rustc +1.99.1 --print cfg --target <triple>` and `llvm-readobj --sections`).

| Mechanism | `x86_64-unknown-linux-gnu` | `i686-unknown-linux-gnu` | `aarch64-unknown-linux-gnu` | `aarch64-apple-darwin` | `x86_64-pc-windows-gnu` | `x86_64` / `aarch64` / `i686-pc-windows-msvc` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`target_has_atomic` widths** | `8, 16, 32, 64, ptr` *(no `128` at default `cpu=x86-64`)* | `8, 16, 32, 64, ptr` (`cmpxchg8b`) | `8, 16, 32, 64, 128, ptr` (`+outline-atomics`) | `8, 16, 32, 64, 128, ptr` (`apple-m1` LSE `cas`/`casp`) | `8, 16, 32, 64, 128, ptr` (`+cmpxchg16b` enabled in target spec) | `x86_64` & `aarch64`: `8..128, ptr`; `i686`: `8..64, ptr` |
| **Unwinding ABI & Sections** | Itanium DWARF (`rust_eh_personality`, `_Unwind_Resume`, `.eh_frame`, `.gcc_except_table`) | Itanium DWARF (`rust_eh_personality`, `_Unwind_Resume`, `.eh_frame`) | Itanium DWARF (`rust_eh_personality`, `_Unwind_Resume`, `.eh_frame`) | Mach-O Compact Unwind + DWARF (`_rust_eh_personality`, `__LD,__compact_unwind`, `__TEXT,__eh_frame`) | SEH with GCC personality (`rust_eh_personality` wrapping `_GCC_specific_handler`, `.pdata`, `.xdata`) | MSVC C++ EH over SEH (`__CxxFrameHandler3`, `_CxxThrowException`, `.pdata`, `.xdata`; plus `.sxdata` SafeSEH on `i686`) |
| **Thread-Local Storage (TLS)** | ELF `.tdata` / `.tbss` (`__tls_get_addr`, `__cxa_thread_atexit_impl`) | ELF `.tdata` / `.tbss` (`___tls_get_addr`, `__cxa_thread_atexit_impl`) | ELF `.tdata` / `.tbss` (`__tls_get_addr`, `__cxa_thread_atexit_impl`) | Mach-O `__DATA,__thread_vars`, `__thread_data`, `__thread_bss` (`_tlv_bootstrap`, `_tlv_atexit`) | PE `.tls$` (`_tls_used`, `.CRT$XLA` / `.CRT$XLB` / `.CRT$XLC` TLS callbacks) | PE `.tls$` (`_tls_index`, `_tls_used`, `.CRT$XLB` TLS destructor callback) |
| **Startup / Init Sections** | `.init_array.00099` (`ARGV_INIT_ARRAY` capturing `argc`/`argv`/`envp`) | `.init_array.00099` (`ARGV_INIT_ARRAY`) | `.init_array.00099` (`ARGV_INIT_ARRAY`) | Reads `_NSGetArgc` / `_NSGetArgv` / `_NSGetEnviron` dynamically | `rsbegin.o` / `rsend.o` (`.ctors.65535`, `.dtors.65535`, `.eh_frame` registration) + `.CRT$XCT` | `.CRT$XCT` / `.CRT$XCU` initializer tables |
| **Runtime CPU Detection (`std_detect`)** | Inline `cpuid` + `xgetbv` (`0` OS syscalls) | Inline `cpuid` + `xgetbv` (`0` OS syscalls) | Linux `getauxval(AT_HWCAP)` + `/proc/cpuinfo` fallback (`open`/`read`/`close`) + `mrs` | Darwin `sysctlbyname("hw.optional.*")` | Inline `cpuid` + `xgetbv` (`0` OS syscalls) | `x86_64`/`i686`: `cpuid`; `aarch64`: Win32 `IsProcessorFeaturePresent` |

### 4. MIR construct frequency distribution across the standard library

Basis: execution

Emitting post-cleanup MIR (`RUSTC_BOOTSTRAP=1 rustc +1.99.1 -C opt-level=3
--emit=mir`) for `core` (`10,948` functions, `41,232` basic blocks, `28.58 MB`
MIR text), `alloc` (`3,538` functions, `21,818` basic blocks, `14.12 MB` MIR
text), `unwind`, and `panic_abort` establishes the exact MIR construct mix a
verified backend must lower to compile `no_std` and `alloc` programs (Table 4).

| MIR Category | Construct | `core` Count (`%` of Category) | `alloc` Count (`%` of Category) | Combined `core + alloc` Share |
| :--- | :--- | :--- | :--- | :--- |
| **Statements** (`163,305` in `core`; `101,241` in `alloc`) | `Assign(Place, Rvalue)` | `60,612` (`37.12%`) | `37,898` (`37.43%`) | `37.24%` |
| **Statements** | `StorageDead(Local)` | `53,679` (`32.87%`) | `33,128` (`32.72%`) | `32.81%` |
| **Statements** | `StorageLive(Local)` | `49,014` (`30.01%`) | `30,215` (`29.84%`) | `29.95%` |
| **Terminators** (`40,192` in `core`; `21,431` in `alloc`) | `Return` | `11,224` (`27.93%`) | `3,659` (`17.07%`) | `24.15%` |
| **Terminators** | `Call` | `11,202` (`27.87%`) | `5,590` (`26.08%`) | `27.25%` |
| **Terminators** | `Goto` | `8,254` (`20.54%`) | `5,431` (`25.34%`) | `22.21%` |
| **Terminators** | `SwitchInt` | `6,813` (`16.95%`) | `4,537` (`21.17%`) | `18.42%` |
| **Terminators** | `Assert` | `1,395` (`3.47%`) | `74` (`0.35%`) | `2.38%` |
| **Terminators** | `Unreachable` | `932` (`2.32%`) | `728` (`3.40%`) | `2.69%` |
| **Terminators** | `Drop` | `236` (`0.59%`) | `989` (`4.61%`) | `1.99%` |
| **Terminators** | `UnwindResume` | `133` (`0.33%`) | `423` (`1.97%`) | `0.90%` |
| **Rvalues** (`60,612` in `core`; `37,898` in `alloc`) | `Use` / `Copy` / `Move` | `29,144` (`48.08%`) | `6,973` (`18.40%`) | `36.66%` |
| **Rvalues** | `BinaryOp` (incl. `WithOverflow` / `Unchecked` / `Offset`) | `12,972` (`21.40%`) | `4,075` (`10.75%`) | `17.31%` |
| **Rvalues** | `Cast` (`PtrToPtr`, `IntToInt`, `Transmute`, `PointerCoercion`) | `7,417` (`12.24%`) | `10,279` (`27.12%`) | `17.96%` |
| **Rvalues** | `Aggregate` (tuples, ADTs, arrays, raw slices) | `7,085` (`11.69%`) | `9,601` (`25.33%`) | `16.94%` |
| **Rvalues** | `Ref` (`&` / `&mut`) | `1,534` (`2.53%`) | `3,436` (`9.07%`) | `5.05%` |
| **Rvalues** | `Discriminant` | `1,262` (`2.08%`) | `1,384` (`3.65%`) | `2.69%` |
| **Rvalues** | `UnaryOp` (`Not`, `Neg`, `PtrMetadata`) | `789` (`1.30%`) | `829` (`2.19%`) | `1.64%` |
| **Rvalues** | `RawPtr` (`&raw const` / `&raw mut`) | `356` (`0.59%`) | `1,311` (`3.46%`) | `1.69%` |
| **Rvalues** | `Repeat` (`[x; N]`) & `NullaryOp` (`SizeOf`, `AlignOf`, `UbChecks`) | `53` (`0.09%`) | `10` (`0.03%`) | `0.06%` |

## Boundaries

- **Prebuilt `.rlib` monomorphization horizon:** The object-level symbol counts
  in Table 2 measure pre-monomorphized machine code inside the shipped
  `libcore`, `liballoc`, and `libstd` `.rlib` archives. Generic functions in
  `core`, `alloc`, and `std` (stored as serialized MIR inside `.rmeta` sections)
  are monomorphized into downstream crates when instantiated; their full source
  and MIR surface is captured by the source census (Section 1) and the full-crate
  MIR dump (Section 4).
- **Tier 2 and Tier 3 targets:** Targets outside the eight Tier 1 triples (such
  as `wasm32`, `riscv64gc`, `thumbv7em-none-eabihf`, or `s390x`) were not
  included in the binary `.rlib` inspection; arch-specific `core::arch` source
  files for those targets exist in `library/stdarch` and are gated out by
  `#[cfg(target_arch = "...")]` on Tier 1 builds.

## Evidence

- **Standard-library source tree:** `rust-lang/rust` commit
  `58cf8f9c35b355199727627d07ae34a4e2846d67`, directories `library/core`,
  `library/alloc`, `library/std`, `library/compiler-builtins`,
  `library/panic_unwind`, `library/panic_abort`, `library/std_detect`,
  `library/unwind`, `library/rtstartup`, `library/stdarch/crates/core_arch`, and
  `library/portable-simd/crates/core_simd`.
- **Official Rust 1.99.1 Tier 1 `rust-std` binary artifacts:**
  `channel-rust-1.99.1.toml` (`fb152be80975c194aa5fc684b2aec3a6e14e2b855efe2faa4e5f8ae6e590f463`),
  inspected via `llvm-nm --no-llvm-bc` and `llvm-readobj --sections` across all
  eight Tier 1 target directories.
- **Preserved support datasets:**
  - `support/stdlib_codegen_demand_per_target.json` — complete machine-readable
    census containing the 313 declared intrinsics, top called intrinsics,
    target features by architecture, inline assembly counts, per-target `.rlib`
    symbol/section inventories, and MIR construct counts.
  - `support/stdlib_target_rlib_matrix.csv` — flat 72-row CSV matrix of all
    8 Tier 1 targets $	imes$ 9 standard-library crates.

## Revalidation

To revalidate the per-target symbol and section census on a newer `rustc`
release, run `llvm-nm --no-llvm-bc` and `llvm-readobj --sections` on
`$(rustc --print sysroot)/lib/rustlib/<target>/lib/lib{core,alloc,std,compiler_builtins,panic_unwind,panic_abort,std_detect,unwind}-*.rlib`
and compare against `support/stdlib_target_rlib_matrix.csv`.
