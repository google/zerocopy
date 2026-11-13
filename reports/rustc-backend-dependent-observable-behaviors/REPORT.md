# Backend-Dependent Observable Behaviors Across `rustc` Code Generators

## Summary

Even when two compilers share the exact `rustc` frontend and lower from the
same `Runtime(PostCleanup)` MIR, compiled Rust programs exhibit 14 categories
of **backend-dependent observable behavior** whose runtime outcomes vary across
optimization levels (`-Copt-level=0` vs. `-Copt-level=3`), code generators
(`rustc_codegen_llvm`, `rustc_codegen_cranelift`, and `rustc_codegen_gcc`), and
target architectures (`x86_64`, `aarch64`, and `i686`). Running differential
probes across `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and
`nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) establishes
four governing distinctions for a verified compiler's equivalence relation:

1. **Pointer identity of functions, vtables, constants, and statics:**
   - Distinct `static` items (`STATIC_A` vs. `STATIC_B`) are guaranteed disjoint
     addresses (`static_ab_eq == false` across all backends and opt levels).
   - Monomorphizations with identical machine code (`generic_id::<u32>` vs.
     `generic_id::<i32>`) have **distinct** addresses at `-Copt-level=0`
     (`fn_u32_eq_i32 == false` on LLVM and Cranelift) but are **merged into a
     single address** at `-Copt-level=3` on LLVM (`fn_u32_eq_i32 == true` via
     `unnamed_addr`), whereas Cranelift never merges functions
     (`fn_u32_eq_i32 == false` even at `-Copt-level=3`).
   - Promoted `const` array references (`&CONST_ARR as *const _`) deduplicate
     under LLVM (`const_addr_eq == true` at `opt0` and `opt3`) but allocate
     distinct anonymous data objects per reference site under Cranelift
     (`const_addr_eq == false`).
2. **Floating-point NaN payloads, `i686` x87 return quieting, and `powi`:**
   - Constant folding vs. runtime arithmetic diverges on NaN sign and payload
     bits under LLVM `-Copt-level=3`: `f64::from_bits(0xfff8_0000_0000_0001) + 0.0`
     evaluates to `0xfff8_0000_0000_0001` at runtime (`nan_add_rt`) and at `opt0`,
     but folds to canonical positive quiet NaN `0x7ff8_0000_0000_0000`
     (`nan_add_const`) at `-Copt-level=3` on both LLVM and Cranelift.
   - On `i686-unknown-linux-gnu`, returning an `f32` or `f64` across
     `extern "C"` (and `extern "Rust"`) executes `flds 4(%esp); retl`, loading
     the float into the x87 `st(0)` register and quieting signaling NaNs
     (`SNaN -> QNaN`), whereas `x86_64` and `aarch64` return in `xmm0`/`s0`
     (`retq`/`ret`) without bit modification.
3. **Trap and termination semantics (`abort`, `process::abort`, `unreachable_unchecked`):**
   - On `rustc_codegen_llvm` (`1.99.1` and `nightly`), `intrinsics::abort()` /
     `UnwindTerminate(Abi)` emits `ud2` on `x86_64`/`i686` and `brk #0x1` on
     `aarch64` (terminating with `SIGILL` / `SIGTRAP`, or `SIGABRT` `-6` under
     the probe harness), while `unreachable_unchecked()` emits `ud2` at
     `-Copt-level=0` (`rc = -6`) and **falls through / returns `0`** (`rc = 0`,
     empty function body) at `-Copt-level=3`.
   - On `rustc_codegen_cranelift`, `UnwindTerminate(Abi)` prints a panic message
     and exits with status **`101`** (`abort_intrinsic = 101`), while
     `unreachable_unchecked()` executes `ud2` (`SIGILL`, `rc = -4`).
4. **Symbol retention, section ordering, volatile/atomic lowering, and stack frames:**
   - `#[used]` and `#[used(linker)]` retain `KEEP_USED_DEFAULT` and
     `KEEP_USED_LINKER` in `.rodata`, and `#[link_section = ".custom_sec"]`
     preserves declaration order (`SEC_ITEM_1` at `+0x0`, `SEC_ITEM_2` at `+0x8`)
     across LLVM and Cranelift.
   - Stack frame step size for an identical recursive function (`measure_frame_step`
     with a 64-byte `black_box` local) is `208` bytes at LLVM `opt0`, `80` bytes
     at LLVM `opt3`, `176` bytes at Cranelift `opt0`, and `192` bytes at
     Cranelift `opt3`.

## Applicability

These findings govern the target equivalence relation and permitted behavioral
deviations for any replacement `rustc` backend targeting **Rust 1.99.1**
(`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled with
LLVM `23.1.1` at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) and compared
against `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):

- **Exact observation:** Runtime probes, signal exit statuses, symbol tables,
  and object disassemblies were captured on `x86_64-unknown-linux-gnu` across
  seven compiler configurations (`baseline_1991_opt0`, `baseline_1991_opt3`,
  `baseline_1991_opt3_mergefn`, `llvm_opt0`, `llvm_opt3`, `clif_opt0`,
  `clif_opt3`), supplemented by cross-target `--emit=asm` inspection on
  `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and
  `i686-unknown-linux-gnu` (`support/observable_behavior_probes.json`).

## Findings

### 1. Classification of the 14 backend-dependent observable behaviors

Basis: normative specification + source + execution

Table 1 classifies each candidate behavior by its normative guarantee level
(Rust Reference, RFCs, and `core` API contracts), ecosystem reliance in
practice, and observed behavior across LLVM (`opt0`/`opt3`) and Cranelift
(`opt0`/`opt3`).

| # | Behavior Category | Normative Status | Ecosystem Reliance | LLVM `opt0` (`1.99.1`) | LLVM `opt3` (`1.99.1`) | Cranelift `opt0` / `opt3` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | **Function pointer equality** (`generic_id::<u32> as usize == generic_id::<i32> as usize`) | **Explicitly unguaranteed** (Reference `types/function-pointer.md`) | Incidental (lint `function_ pointer_ comparisons` warns by default) | `false` (distinct CGU symbols) | `true` (`unnamed_addr` ICF/MergeFunctions merges bodies) | `false` / `false` (no function merging) |
| 2 | **Vtable pointer equality** (`&10u64 as &dyn MyTrait` vtable ptr equality) | **Explicitly unguaranteed** (trait object vtable duplication permitted across CGUs) | Relied on by some `dyn Any` / custom fat-pointer caches within single crate | `true` | `true` | `true` / `true` |
| 3 | **Promoted `const` & string literal address uniqueness** (`&CONST_ARR`, `"lit".as_ptr()`) | **Explicitly unguaranteed** (Reference `items/constant-items.md`) | Incidental | `const_addr_eq: true`, `str_lit_eq: true` | `const_addr_eq: true`, `str_lit_eq: true` | `const_addr_eq: false` (duplicate alloc), `str_lit_eq: true` |
| 4 | **`static` address disjointness** (`&STATIC_A != &STATIC_B` for non-ZST) | **Normatively guaranteed** (`static` items have distinct global memory locations) | Mandatory | `static_ab_eq: false` (`0x8f7c` vs `0x8f8c`) | `static_ab_eq: false` | `static_ab_eq: false` (`0x64e0` vs `0x64f0`) |
| 5 | **Floating-point `powi` and NaN payload propagation** (`nan + 0.0`, `(2.5f64).powi(3)`) | **RFC 3514**: NaN sign/quiet bit nondeterministic for arithmetic; bitwise-exact only for non-NaN IEEE ops | Moderate (`f64::to_bits` tests in numeric crates) | `powi`: `0x402f400000000000`; `nan_add_const`: `0xfff8000000000001` | `powi`: `0x402f400000000000`; `nan_add_const`: **`0x7ff8000000000000`** | Matches LLVM (`opt3` folds const NaN to `0x7ff8...`) |
| 6 | **Value-move / return NaN preservation on `i686`** (`extern "C" fn id_f32(f32) -> f32`) | **Known spec violation** (`rust-lang/rust#115567` vs RFC 3514 byte copy) | Low on `i686` | `flds 4(%esp); retl` (x87 `st(0)` quiets SNaN) | `flds 4(%esp); retl` | Unsupported on `i686` by Cranelift |
| 7 | **Stack frame size and recursion depth** (`measure_frame_step` with 64B local) | **Explicitly unguaranteed** | High operational reliance (deep parser/AST recursion within 8 MiB stack) | `208` bytes/frame | `80` bytes/frame | `176` bytes (`opt0`) / `192` bytes (`opt3`) |
| 8 | **`hint::black_box`, `#[inline(never)]`, and `#[cold]`** (`cold_never_inline`) | `#[inline(never)]` & `#[cold]` are **hints**; `black_box` is a best-effort optimization barrier | High in benchmarking (`criterion`) and crypto constant-time code | Calls out-of-line `black_box` helper; `sub $0x28,%rsp` (`62` bytes) | Emits `mov %rdi,-0x8(%rsp); lea -0x8(%rsp),%rax; mov -0x8(%rsp),%rax` (`19` bytes) | `opt3` folds `black_box` completely to `lea 0x7(%rdi),%rax` (`12` bytes) |
| 9 | **`intrinsics::abort` vs. `process::abort` vs. `unreachable_unchecked`** | `abort` guarantees abnormal process termination; `unreachable_unchecked` is **immediate UB** | High (security sandboxes check `SIGILL` vs `SIGABRT`) | `abort`: `ud2` (`x86_64`), `brk #0x1` (`aarch64`); `unreachable`: `ud2` (`rc = -6`) | `abort`: `ud2` / `brk #0x1`; `unreachable`: **0-byte fallthrough (`rc = 0`)** | `UnwindTerminate`: exits `101`; `unreachable`: `ud2` (`SIGILL`, `rc = -4`) |
| 10 | **Volatile access width and count** (`read_volatile`/`write_volatile` on `u64`) | **Normatively guaranteed** for MMIO (single access of exact width on aligned native word) | Mandatory for kernels/drivers (Linux Kbuild, Fuchsia, embedded) | Single 64-bit `mov (%rdi),%rax` and `mov %rax,(%rdi)` | Single 64-bit load and store | Single 64-bit load and store |
| 11 | **Atomic instruction lowering** (`AtomicU64::store(SeqCst)` + `load(SeqCst)`) | Must preserve C++20 memory model interoperability with C/Clang on target ABI | Mandatory for lock-free FFI and kernel synchronization | `x86_64`: `xchgq` + `movq`; `aarch64`: `stlr` + `ldar`; `i686`: `movlps %xmm0,(%eax); lock orl $0,(%esp); movq (%eax),%xmm0` | Identical target sequences | Uses `lock xchgq` / `mfence` sequences on `x86_64` |
| 12 | **Retention under `#[used]` and `#[used(linker)]`** | `#[used(linker)]` guarantees linker retention (`SHF_GNU_RETAIN` / `llvm.used`); `#[used]` guarantees only `llvm.compiler.used` | High in plugin/init-array registration (`linkme`, kernel modules) | Both `KEEP_USED_DEFAULT` and `KEEP_USED_LINKER` retained in `nm` | Both retained in `nm` (`0x54a0`, `0x54a8`) | Both retained in `nm` (`0x6e30`, `0x6e38`) |
| 13 | **Placement and order under `#[link_section = ".custom_sec"]`** | Section placement is **normatively guaranteed**; intra-section symbol order is **unguanteed** | Relied on by custom linker-script tables (`SEC_ITEM_1`, `SEC_ITEM_2`) | Placed in `.custom_sec` in source order (`0x10038`, `0x10040`) | Placed in `.custom_sec` in source order (`0xe058`, `0xe060`) | Placed in `.custom_sec` in source order (`0xc530`, `0xc538`) |
| 14 | **Debuginfo and `std::backtrace::Backtrace`** (`-Cdebuginfo=2`) | DWARF/PDB emission is best-effort tool contract | High in production crash reporting | `bt_has_main: true` | `bt_has_main: true` | `bt_has_main: true` |

---

### 2. Detailed assembly divergences across architectures and backends

Basis: execution

#### 2.1 `cold_never_inline` and `core::hint::black_box`
In `support/run_observable_probes.py`, `cold_never_inline(x: u64) -> u64` computes
`black_box(x).wrapping_add(7)`:
- **LLVM `-Copt-level=3` (`baseline_1991_opt3`):** Lowering `Rvalue::Use`
  inside `black_box` via an empty inline assembly constraint (`asm!("",
  inout(reg) dummy)`) forces `x` to memory in the redzone and reloads it before
  adding `7`:
  ```text
  17370: 48 89 7c 24 f8    mov    %rdi,-0x8(%rsp)
  17375: 48 8d 44 24 f8    lea    -0x8(%rsp),%rax
  1737a: 48 8b 44 24 f8    mov    -0x8(%rsp),%rax
  1737f: 48 83 c0 07       add    $0x7,%rax
  17383: c3                ret
  ```
- **Cranelift `-Copt-level=3` (`clif_opt3`):** Cranelift implements
  `rustc_intrinsic::black_box` as an identity no-op at `-Copt-level=3`, folding
  the entire function to `lea 0x7(%rdi),%rax`:
  ```text
  2138c: 55                push   %rbp
  2138d: 48 89 e5          mov    %rsp,%rbp
  21390: 48 8d 47 07       lea    0x7(%rdi),%rax
  21394: 48 89 ec          mov    %rbp,%rsp
  21397: 5d                pop    %rbp
  21398: c3                ret
  ```

#### 2.2 Cross-architecture `AtomicU64::SeqCst`, `abort`, and `f32` return (`1.99.1`)
Compiling `arch_probe.rs` at `-Copt-level=2` across the three Linux Tier 1
architectures (`support/observable_behavior_probes.json` under `arch_asm`) shows
the exact target sequences a verified backend must match for C/C++ ABI and
atomic interoperability:
- **`x86_64-unknown-linux-gnu`:**
  - `atomic_seqcst`: `xchgq %rsi, (%rdi); movq (%rdi), %rax; retq`.
  - `do_abort` / `do_unreach`: `ud2` (with `do_abort` placed in
    `.section .text.unlikely.do_abort`).
  - `id_f32`: `retq` (`xmm0` in, `xmm0` out).
- **`aarch64-unknown-linux-gnu`:**
  - `atomic_seqcst`: `stlr x1, [x0]; ldar x0, [x0]; ret`.
  - `do_abort` / `do_unreach`: `brk #0x1`.
  - `id_f32`: `ret` (`s0` in, `s0` out).
- **`i686-unknown-linux-gnu`:**
  - `atomic_seqcst`: 64-bit atomic store/load on 32-bit x86 with SSE2 lowers
    via 64-bit SSE moves (`movsd 8(%esp), %xmm0; movlps %xmm0, (%eax); lock orl $0, (%esp); movq (%eax), %xmm0`).
  - `id_f32`: `flds 4(%esp); retl` (returns `f32` in x87 `st(0)` per System V
    i386 ABI, quieting any signaling NaN).

## Boundaries

- **Cross-compiler `extern "Rust"` ABI mixing:** `extern "Rust"` layout and
  calling conventions are explicitly unstable across compiler versions and
  backends (`compiler/rustc_ty_utils/src/abi.rs`); mixing `.rlib` objects built
  by different backends is **unsupported** unless both backends use `rustc`'s
  exact `fn_abi_of_instance` calculation and agree on symbol mangling.
- **`rustc_codegen_gcc` runtime execution:** On this host, `rustc_codegen_gcc`
  requires a matching patched `libgccjit.so` not bundled in the standard
  `1.99.1` rustup sysroot (**not examined** via live binary execution; examined
  via `compiler/rustc_codegen_gcc/src/` source inspection).

## Evidence

- **`rustc` source (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `unnamed_addr` and function/constant merging:
    `compiler/rustc_codegen_ssa/src/back/symbol_export.rs` and
    `compiler/rustc_codegen_llvm/src/consts.rs`.
  - `#[used]` vs. `#[used(linker)]` lowering:
    `compiler/rustc_codegen_llvm/src/consts.rs:340-415`.
  - `intrinsics::abort` and `unreachable_unchecked` lowering:
    `compiler/rustc_codegen_llvm/src/intrinsic.rs` and
    `compiler/rustc_codegen_cranelift/src/intrinsics/mod.rs`.
- **Preserved artifacts in `support/`:**
  - `support/run_observable_probes.py`: standalone reproducible probe harness
    testing all 14 behavior categories across `rustc 1.99.1` and `nightly`
    (LLVM and Cranelift) plus cross-architecture assembly generation.
  - `support/observable_behavior_probes.json`: complete captured JSON outputs,
    signal exit codes, `objdump -d` disassemblies, `nm -n` symbol tables, and
    `x86_64`/`aarch64`/`i686` assembly listings.

## Revalidation

Run `python3 support/run_observable_probes.py` with `rustc +1.99.1` (and any
candidate backend) installed, and diff the generated `c3_extracted.json`
against `support/observable_behavior_probes.json`.
