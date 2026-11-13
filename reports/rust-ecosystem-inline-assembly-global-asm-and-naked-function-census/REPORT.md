# Empirical Census of Rust Inline Assembly (`asm!`), `global_asm!`, Naked Functions (`naked_asm!`), and External C/Assembler Objects

## Summary

Designing an inline-assembly front end and verification pipeline for a drop-in
`rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) replacement requires
knowing which assembly constructs real-world Rust code actually invokes and how
they differ from external `.S`/`.s`/`.asm` files compiled via `cc-rs`. Scanning
the Rust `1.99.1` standard library (`core`, `std`, `stdarch`, `panic_unwind`),
`compiler-builtins`, and **3,680 unique crates** in the crates.io corpus
(including the top 100 crates by recent download volume; see
`rustc-experimental-corpora-and-harness-conventions`) establishes four governing
facts:

1. **Standard library and `compiler_builtins` footprint (`269` macro invocations across `47` files):**
   - `library/std/src` contains **11 files** using inline assembly (`28` `asm!`
     and `2` `global_asm!` blocks, `0` naked functions), confined entirely to
     platform ABIs and enclaves (`os/fortanix_sgx`, `os/xous`, `sys/pal/sgx`,
     `sys/pal/vexos`, `sys/pal/windows`, `sys/personality/gcc.rs`,
     `sys/stdio/teeos.rs`, `sys/thread/xous.rs`, `sys/thread_local/key/xous.rs`)
     plus 1 external `.S` file. Notably, standard Linux and macOS `std::sys`
     paths use zero `asm!` blocks in `std` (relying on `libc` or `core::arch`).
   - `library/core/src` contains **2 files** with `2` `asm!` invocations and `1`
     `#[unsafe(naked)]` item, while `library/stdarch/crates/core_arch/src`
     contains **21 files** with **204 `asm!` invocations** (used for CPUID,
     system registers `mrs`/`msr`, barriers, and instructions lacking LLVM
     intrinsics).
   - `library/compiler-builtins/compiler-builtins/src` contains **13 Rust files**
     with **35 direct assembly macro invocations** (`21` `asm!`, `13`
     `naked_asm!`, `1` `global_asm!`) and **21 `#[unsafe(naked)]` attributes**
     (yielding **42 total assembly/naked sites** when counting the macro-expanded
     outline-atomic templates in `aarch64_outline_atomics.rs` and `macros.rs`),
     plus **26 external `.S`/`.s` assembly files** for legacy C-ABI targets.
2. **Ecosystem census across 3,680 crates (`87` crates with Rust `asm!`, `28` with external `.S`/`.asm`):**
   Across 3,680 unique crates in the local crates.io cache:
   - Only **87 crates (2.36%)** contain Rust `asm!`, `naked_asm!`, or
     `global_asm!`, totaling **1,294 macro invocations** (`1,198` `asm!`
     [92.6%], `88` `naked_asm!` [6.8%], and `8` `global_asm!` [0.6%]).
   - Among the **top 100 crates by recent download volume**, only **3 crates**
     contain Rust inline assembly (`rustix`: `193` `asm!` + `1` `global_asm!`,
     `67,120,441` recent downloads; `getrandom`: `9` `asm!`, `94,118,203`
     downloads; and `parking_lot` / `parking_lot_core`: `3` `asm!`, `61,408,912`
     downloads).
   - **28 crates (0.76%)** ship external `.S`/`.s`/`.asm` assembly files built
     via `cc` in `build.rs` (led by `aws-lc-sys` [`951` files], `gmp-mpfr-sys`
     [`927`], `rav1e` [`94`], `ring` [`90`], `libffi-sys` [`48`], `psm` [`25`],
     and `blake3` [`12`]), which bypass `rustc`'s inline assembler entirely and
     arrive at the linker as foreign ELF/Mach-O/COFF `.o`/`.a` objects.
3. **Option, operand, and register-class concentration:**
   - Across the 1,294 ecosystem assembly blocks, **`nostack` (`704` uses, 54.4%)**
     and **`preserves_flags` (`505`, 39.0%)** dominate `options(...)`, followed
     by `nomem` (`232`), `readonly` (`121`), `pure` (`112`), `att_syntax` (`87`),
     `noreturn` (`34`), and a single use of `may_unwind` (`1`, in `unwinding`).
   - Among operand kinds (`4,584` total operands), **`lateout` (`1,681`, 36.7%)**
     and **`in` (`1,611`, 35.1%)** account for 71.8% of all operands, followed by
     `out` (`452`), `inlateout` (`445`), `inout` (`189`), `const` (`132`), `sym`
     (`71`), and `clobber_abi` (`3`).
   - Among register classes, **`reg` (`2,487` uses, 91.5%)** and **`xmm_reg` /
     `ymm_reg` / `zmm_reg` (`201` uses, 7.4%)** account for **98.9%** of all
     register-class operands; explicit register constraints (`in("eax")`,
     `in("x8")`, `inout("rcx")`, `lateout("rax")`) are used almost exclusively
     for OS syscall numbers/arguments (`rustix`, `syscalls`, `std::os::xous`)
     and `cpuid`/`xgetbv`.
4. **Instruction and directive footprint inside Rust `asm!` templates:**
   Real-world Rust `asm!` templates are overwhelmingly short (median **1–4
   instructions**):
   - **System call and trap instructions:** `syscall`, `svc`, `int`, `ecall`.
   - **Privileged / CPU-state / barrier instructions:** `mrs`, `msr`, `cpuid`,
     `rdtsc`, `rdtscp`, `xgetbv`, `isb`, `dsb`, `dmb`, `wfi`, `wfe`, `cli`,
     `sti`, `hlt`, `invlpg`, `lgdt`, `lidt`, `csrr`, `csrw`, `sfence.vma`.
   - **Atomics and spin/CAS loops:** `lock cmpxchg16b`, `lock xadd`, `ldaxr`/`stlxr`,
     `ldrex`/`strex`, `pause`, `yield`.
   - **Stack switching and unwinding:** `mov rsp, ...`, `.cfi_def_cfa_offset`,
     `.cfi_offset`, `.cfi_undefined` (`wasmtime-internal-fiber`, `unwinding`,
     `compiler_builtins::probestack`).

## Applicability

This census applies to **Rust 1.99.1** (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
`library/compiler-builtins`, and the **3,680 unique crates** in the local
crates.io snapshot (`index.crates.io-1949cf8c6b5b557f`). Complete machine-readable
counts and download weights are preserved in `support/asm_census.json`.

## Findings

### 1. Summary across `std`, `core`, `stdarch`, `compiler_builtins`, and `crates.io`

Basis: source + execution (`support/asm_census.json`)

Table 1 compares the assembly footprint across the five examined codebases.

| Codebase / Corpus | Files with Rust `asm!` / `naked` | `asm!` | `naked_asm!` | `global_asm!` | `#[unsafe(naked)]` | External `.S`/`.s`/`.asm` Files | Top `options(...)` | Top Operand Forms |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- | :--- |
| `library/std/src` (`1.99.1`) | 11 | 28 | 0 | 2 | 0 | 1 | `nostack` (`11`), `att_syntax` (`7`), `preserves_flags` (`4`), `noreturn` (`4`) | `inlateout` (`105`), `in` (`27`), `inout` (`8`), `out` (`3`) |
| `library/core/src` (`1.99.1`) | 2 | 2 | 0 | 0 | 1 | 0 | `nostack` (`2`) | `in` (`2`) |
| `library/stdarch/crates/core_arch/src` | 21 | 204 | 0 | 0 | 0 | 0 | `nostack` (`200`), `pure` (`118`), `nomem` (`116`), `preserves_flags` (`84`) | `in` (`316`), `lateout` (`112`), `out` (`27`), `inout` (`7`) |
| `library/compiler-builtins` | 13 | 21 | 13 (`+7` macro) | 1 | 21 | 26 | `nostack` (`21`), `preserves_flags` (`17`), `pure` (`2`), `nomem` (`2`), `raw` (`1`) | `inout` (`26`), `in` (`17`), `sym` (`5`), `out` (`5`) |
| `crates.io` corpus (`3,680` unique crates; `87` with Rust asm) | 284 | 1,198 | 88 | 8 | 91 | 2,369 (in `28` crates) | `nostack` (`704`), `preserves_flags` (`505`), `nomem` (`232`), `readonly` (`121`), `pure` (`112`) | `lateout` (`1,681`), `in` (`1,611`), `out` (`452`), `inlateout` (`445`) |

---

### 2. Detailed breakdown of `library/std` (11 files) and `compiler_builtins` (13 files)

Basis: source (`library/std/src/`, `library/compiler-builtins/compiler-builtins/src/`)

Table 2 lists all 11 files in `library/std/src` and all 13 files in
`compiler_builtins/src` containing inline assembly or naked functions.

| Repository Component | File Path | `asm!` | `naked_asm!` | `global_asm!` | `#[unsafe(naked)]` | Functional Purpose & Target ISA |
| :--- | :--- | ---: | ---: | ---: | ---: | :--- |
| `library/std/src` | `os/fortanix_sgx/arch.rs` | 2 | 0 | 0 | 0 | x86-64 SGX `ENCLU` (`EGETKEY`, `EREPORT`) leaf calls |
| `library/std/src` | `os/xous/ffi.rs` | 14 | 0 | 0 | 0 | RISC-V / ARM Xous microkernel `ecall` / `svc` syscall wrappers |
| `library/std/src` | `sys/pal/sgx/abi/mem.rs` | 1 | 0 | 0 | 0 | SGX enclave relative-address relocation load (`lea`) |
| `library/std/src` | `sys/pal/sgx/abi/mod.rs` | 0 | 0 | 1 | 0 | SGX entry/exit trampoline (`global_asm!`) |
| `library/std/src` | `sys/pal/sgx/abi/usercalls/alloc.rs` | 3 | 0 | 0 | 0 | SGX usercall shared-memory volatile accesses |
| `library/std/src` | `sys/pal/vexos/mod.rs` | 0 | 0 | 1 | 0 | ARMv7-A VEXos boot header and startup section (`global_asm!`) |
| `library/std/src` | `sys/pal/windows/mod.rs` | 3 | 0 | 0 | 0 | Windows `_fltused` / TEB access and fastfail (`int 0x29`) |
| `library/std/src` | `sys/personality/gcc.rs` | 1 | 0 | 0 | 0 | ARM EHABI `_Unwind_VRS_Set` helper |
| `library/std/src` | `sys/stdio/teeos.rs` | 1 | 0 | 0 | 0 | Huawei TEEOS debug console write |
| `library/std/src` | `sys/thread/xous.rs` | 1 | 0 | 0 | 0 | Xous thread yield syscall |
| `library/std/src` | `sys/thread_local/key/xous.rs` | 2 | 0 | 0 | 0 | Xous TLS `$tp` register read/write |
| `compiler_builtins` | `probestack.rs` | 0 | 3 | 0 | 4 | `__rust_probestack` on `x86_64` and `i686` (`naked_asm!` with `.cfi_def_cfa_offset`) |
| `compiler_builtins` | `x86_64.rs` | 0 | 1 | 0 | 1 | `___chkstk_ms` / `__chkstk` on `x86_64-pc-windows-*` |
| `compiler_builtins` | `x86.rs` | 0 | 2 | 0 | 2 | `_chkstk` and `___chkstk_ms` on 32-bit `i686-pc-windows-*` |
| `compiler_builtins` | `aarch64.rs` | 0 | 1 | 0 | 1 | `__chkstk` on `aarch64-pc-windows-*` (`x15`-based page probe) |
| `compiler_builtins` | `aarch64_outline_atomics.rs` | 0 | 0 (`+4` macro) | 0 | 4 | `__aarch64_{cas,swp,ldadd,ldclr,ldeor,ldset}*` runtime LSE dispatch |
| `compiler_builtins` | `arm.rs` | 0 | 4 | 0 | 4 | `__aeabi_uidivmod`, `__aeabi_idivmod`, `__aeabi_uldivmod`, `__aeabi_ldivmod` |
| `compiler_builtins` | `int/udiv.rs` & `specialized_div_rem/mod.rs` | 2 | 2 | 0 | 2 | Hardware divide/remainder fast paths |
| `compiler_builtins` | `mem/x86_64.rs` | 12 | 0 | 0 | 0 | `rep movsb` / `rep movsq` / `rep stosb` bulk memory primitives |
| `compiler_builtins` | `sync/{arm_linux.rs,thumbv6k.rs}` | 4 | 0 | 0 | 0 | ARM Linux kernel `__kuser_cmpxchg` / `__kuser_memory_barrier` and `ldrex`/`strex` |
| `compiler_builtins` | `hexagon.rs` & `macros.rs` | 3 | 0 | 1 | 3 | Hexagon `dfcmp` helpers and naked symbol wrapper macros |

---

### 3. Top ecosystem crates using Rust `asm!` vs. external `cc`-compiled assembly

Basis: execution (`support/asm_census.json`)

Table 3 lists the top crates in the corpus using Rust `asm!`/`naked_asm!`/`global_asm!`
alongside the top crates using external `.S`/`.s`/`.asm` files compiled via `cc`.

| Category | Crate (`Version`) | Top-100? | Recent Downloads | `asm!` | `naked_asm!` | `global_asm!` | External `.S`/`.asm` | Dominant Instructions / Directives & Purpose |
| :--- | :--- | :---: | ---: | ---: | ---: | ---: | ---: | :--- |
| **Rust `asm!`** | `getrandom` (`0.3.4`) | **Yes** | 94,118,203 | 9 | 0 | 0 | 0 | `syscall` (`x86_64`), `svc 0` (`aarch64`/`arm`), `ecall` (`riscv`), `rdrand`/`rdseed` |
| **Rust `asm!`** | `rustix` (`1.1.2`) | **Yes** | 67,120,441 | 193 | 0 | 1 | 0 | Linux raw syscalls (`syscall`, `svc 0`, `int 0x80`, `ecall`) across 7 architectures |
| **Rust `asm!`** | `parking_lot_core` (`0.9.12`) | **Yes** | 61,408,912 | 3 | 0 | 0 | 0 | Spin-loop `pause` / `yield` and thread-pointer access |
| **Rust `asm!`** | `portable-atomic` (`1.11.1`) | No | — | 114 | 0 | 0 | 0 | `lock cmpxchg16b`, `vmovdqa` (128-bit atomic load/store on AVX), `ldxp`/`stxp`, `casp`, RISC-V AMO |
| **Rust `asm!`** | `private-gemm-x86` (`0.1.19`) | No | — | 129 | 0 | 0 | 0 | Unrolled AVX2/AVX-512 `vfmadd231pd`, `vbroadcastsd`, `vmovupd` microkernels |
| **Rust `asm!`** | `x86` (`0.52.0`) & `x86_64` (`0.15.2`) | No | — | 148 | 0 | 0 | 0 | OS kernel ring-0 instructions: `lgdt`, `lidt`, `ltr`, `invlpg`, `rdmsr`, `wrmsr`, `in`/`out`, `iretq`, `swapgs` |
| **Rust `asm!`** | `syscalls` (`0.6.18`) & `redox_syscall` | No | — | 116 | 0 | 0 | 0 | Multi-arch syscall tables (`syscall`, `svc`, `ecall`) |
| **Rust `asm!`** | `cortex-m` (`0.7.7`) | No | — | 48 | 0 | 0 | 0 | Embedded ARM Cortex-M `mrs`, `msr`, `cpsid`, `cpsie`, `wfi`, `wfe`, `bkpt`, `isb`, `dsb`, `dmb` |
| **Rust `asm!`** | `unwinding` (`0.2.8`) & `wasmtime-internal-fiber` | No | — | 20 | 27 | 0 | 0 | Context save/restore (`naked_asm!`) with `.cfi_def_cfa_offset`, `.cfi_offset`, `.cfi_undefined` |
| **Rust `asm!`** | `libm` (`0.2.15`) & `half` (`2.7.1`) | No | — | 29 | 0 | 0 | 0 | Hardware `sqrtss`/`sqrtsd`, `vcvtph2ps`, `vcvtps2ph` |
| **External `cc` Asm** | `aws-lc-sys` (`0.32.0`) | No | — | 0 | 0 | 0 | **951** | Perlasm-generated BoringSSL/AWS-LC `.S`/`.asm` crypto kernels linked via `cc`/`cmake` |
| **External `cc` Asm** | `gmp-mpfr-sys` (`1.6.8`) | No | — | 0 | 0 | 0 | **927** | GNU MP mpn `.asm` multi-precision bignum kernels |
| **External `cc` Asm** | `rav1e` (`0.8.1`) | No | — | 0 | 0 | 0 | **94** | Hand-written NASM/GAS `.S`/`.asm` AV1 video encoder SIMD kernels |
| **External `cc` Asm** | `ring` (`0.17.14`) | No | — | 0 | 0 | 0 | **90** | BoringSSL Perlasm `.S`/`.asm` AES-GCM, ChaCha20-Poly1305, SHA-256, P-256, Ed25519 |
| **External `cc` Asm** | `psm` (`0.1.26`) & `blake3` (`1.8.2`) | No | — | 0 | 0 | 0 | **37** | Stack manipulation (`psm` `.s`) and AVX-512/NEON `blake3` `.S`/`.asm` |

---

### 4. Directives, mnemonics, and privileged instructions inside Rust `asm!`

Basis: execution (`support/asm_census.json`)

1. **Assembler directives used inside Rust `asm!`/`naked_asm!`/`global_asm!`:**
   Across `std`, `compiler_builtins`, and all 87 crates in the corpus using Rust
   assembly, only **18 distinct assembler directives** appear in templates:
   - *DWARF CFI unwind directives (in `compiler_builtins::probestack`, `unwinding`, `wasmtime-internal-fiber`):*
     `.cfi_startproc`, `.cfi_endproc`, `.cfi_def_cfa_offset`, `.cfi_adjust_cfa_offset`,
     `.cfi_offset`, `.cfi_def_cfa_register`, `.cfi_undefined`, `.cfi_escape`.
   - *Section & symbol directives (in `global_asm!` and `std::sys::pal`):*
     `.section`, `.pushsection`, `.popsection`, `.text`, `.globl`/`.global`,
     `.type`, `.size`, `.balign`/`.p2align`/`.align`.
   - *Data & raw instruction encoding:* `.byte`, `.word`, `.long`, `.quad`,
     `.inst`/`.insn` (used to encode new ISA extensions such as RISC-V/ARM
     instructions on older assemblers).
2. **Privileged and system instructions (`aggregate_privileged_mnemonics` in `support/asm_census.json`):**
   Across the corpus, privileged/system mnemonics break down into:
   - **System calls (`278` occurrences):** `syscall` (`142`), `svc` (`84`),
     `ecall` (`34`), `int` (`18`).
   - **System register & CSR access (`164` occurrences):** `mrs` (`68`), `msr`
     (`52`), `csrr`/`csrw`/`csrs`/`csrc` (`31`), `rdmsr`/`wrmsr` (`13`).
   - **Synchronization, cache, and TLB barriers (`96` occurrences):** `isb`
     (`34`), `dsb` (`29`), `dmb` (`19`), `invlpg`/`sfence.vma` (`14`).
   - **CPU feature & timestamp queries (`41` occurrences):** `cpuid` (`16`),
     `rdtsc`/`rdtscp` (`15`), `xgetbv`/`xsetbv` (`10`).
   - **Interrupt & halt control (`38` occurrences):** `cli`/`sti` (`16`), `wfi`/`wfe`
     (`12`), `hlt` (`6`), `iretq`/`eret`/`sret` (`4`).

## Boundaries

- **Linux kernel in-tree `rust/` subtree (`torvalds/linux`):** While the Linux
  kernel's `rust/kernel/` and `arch/*/include/asm/` patterns match the OS kernel
  crates in the corpus (`x86`, `x86_64`, `cortex-m`, `polyhal`, `moana`,
  `linux-unsafe` — using `asm!` for `mrs`/`msr`, `csrr`, `cpuid`, `rdtsc`, and
  `.pushsection "__ex_table"` / `static_branch` jump labels), a full `torvalds/linux`
  tree was not cloned locally; kernel-crate equivalents from `crates.io` were
  analyzed instead.
- **Macro-generated assembly strings (`concat!`, `macro_rules!`):** Our static
  scanner extracts string literals inside `asm!(...)`, `naked_asm!(...)`, and
  `global_asm!(...)` invocations; dynamic token-paste macros are counted at their
  macro definition site.

## Evidence

- **Rust 1.99.1 (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `library/std/src/` (`11` files with `asm!`/`global_asm!`).
  - `library/core/src/` (`2` files with `asm!`).
  - `library/stdarch/crates/core_arch/src/` (`21` files with `204` `asm!` blocks).
  - `library/compiler-builtins/compiler-builtins/src/` (`13` files with `35`
    direct + `7` macro-wrapped assembly blocks and `21` `#[unsafe(naked)]`
    functions).
- **Ecosystem crate cache (`index.crates.io-1949cf8c6b5b557f`):**
  - `3,680` unique unpacked crates cross-referenced against
    `rustc-experimental-corpora-and-harness-conventions/support/crates_manifest.json`.
- **Preserved support artifacts:**
  - `support/asm_census.json`: Complete per-codebase and per-crate inline
    assembly, `global_asm!`, `naked_asm!`, `#[unsafe(naked)]`, and external
    `.S`/`.asm` census with download weights.
  - `support/probe_asm_census.py`: Standalone scanner script.

## Revalidation

Run `python3 support/probe_asm_census.py` against a newer `rust-lang/rust`
checkout and cargo registry cache to recompute `support/asm_census.json`.
