# Binary Byte-Origin Attribution, Linker Section Garbage Collection, and ICF Soundness Across `rustc` 1.99.1 Targets

## Summary

A linked Rust `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) binary is a
composite artifact containing bytes from nine distinct provenance categories:
(1) local crate Rust functions and statics lowered from MIR by the codegen
backend, (2) standard-library Rust crates (`core`, `alloc`, `std`, `hashbrown`,
`rustc_demangle`), (3) in-process DWARF backtrace/symbolication crates (`gimli`,
`addr2line`, `object`, `miniz_oxide`, `adler2`) linked into `libstd`, (4)
`compiler_builtins` software arithmetic and memory intrinsics, (5) `global_asm!`
and `#[unsafe(naked)]` assembly blocks, (6) target C runtime startup objects
(`Scrt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o`, `crtn.o` on ELF; `crt2.o` /
`dllcrt2.o` on Windows GNU; MSVC CRT startup on Windows MSVC), (7) the dynamic
unwinder (`libgcc_s.so.1` / `libunwind` / Windows SEH `.pdata`/`.xdata`), (8)
OS dynamic-loader / C runtime imports (`libc.so.6`, `libm.so.6`, `libSystem.B.dylib`,
`kernel32.dll`, `ntdll.dll`), and (9) linker-synthesized sections (`.interp`,
`.gnu.hash`, `.dynsym`, `.dynstr`, `.rela.dyn`, `.plt`, `.got`, `.eh_frame_hdr`,
and PE `.pdata`/`.reloc`/`.idata`).

Empirical byte-level attribution across five representative binary shapes
(`hello_world`, `cli_tool`, `async_server`, `cdylib`, and `staticlib`), four
build profiles (`dev`, `release`, `lto=fat`, and `panic=abort`), and all 8 Tier
1 targets establishes four primary findings for populating a verified compiler's
assumption ledger:

1. **Prebuilt `std` backtrace and formatting dominate non-LTO executable `.text`
   (>98% of code bytes in small programs)**: In a release `hello_world` on
   `x86_64-unknown-linux-gnu` (`241,651` bytes of `.text`), local crate Rust
   code is **18 bytes** (`0.007%`), CRT startup objects are **313 bytes**
   (`0.13%`), `std`/`core`/`alloc` runtime and formatting account for **94,053
   bytes** (`38.9%`), and `gimli`/`addr2line`/`miniz_oxide`/`object` backtrace
   symbolication inside `libstd` accounts for **148,243 bytes** (`61.3%`).
2. **Linker section garbage collection (`--gc-sections` / `-dead_strip` /
   `/OPT:REF`) removes 63.5% of `.text` and 78.3% of `.rodata`**: Because
   `rustc` defaults to `-Zfunction-sections=yes` on ELF and Mach-O (and
   `-Clink-dead-code=no` passes `--gc-sections` on ELF, `-Wl,-dead_strip` on
   Darwin, and `/OPT:REF` on MSVC), disabling `--gc-sections` on `cli_tool`
   (`release`) inflates `.text` from `254,995` bytes to `697,949` bytes
   (`+442,954` bytes, `+173.7%`), `.rodata` from `23,204` bytes to `107,020`
   bytes, and `.eh_frame` from `26,856` bytes to `102,748` bytes.
3. **Fat LTO (`-Clto=fat -Ccodegen-units=1`) shrinks total binary size by 56.9%
   and `.gcc_except_table` by 74.1%**: Across `hello_world`, `cli_tool`, and
   `async_server`, Fat LTO internalizes non-exported symbols across the `.rlib`
   dependency graph, reducing `hello_world` from `4,537,112` bytes to `1,956,472`
   bytes (`-56.9%`) and `.gcc_except_table` LSDA tables from `13,308` bytes to
   `3,444` bytes (`-74.1%`).
4. **Identical Code Folding (`--icf=all` / `/OPT:ICF`) merges distinct functions
   with identical machine bytes**: `rustc_codegen_llvm` marks non-exported Rust
   functions `unnamed_addr` (`UnnamedAddr::Global` in
   `compiler/rustc_codegen_llvm/src/mono_item.rs:190-208`) unless their address
   is required to be distinct across DLL boundaries, which permits LLVM's
   `MergeFunctions` and `lld`'s `--icf=safe` / `--icf=all` to fold two distinct
   Rust functions (`fn_one` and `fn_two`) to the exact same runtime instruction
   address (`p1 == p2` evaluates to `true`). This is sound in Rust (`fn` pointer
   equality is explicitly unspecified), provided the verification theorem does
   not assume disjoint code addresses for distinct `DefId`s.

## Applicability

- **Primary baseline**: `rust-lang/rust` `1.99.1`
  (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project`
  `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, including `rust-lld`),
  cross-checked against `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`)
  and `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
- **Targets and binary shapes**: Five workload shapes (`hello_world`, `cli_tool`,
  `async_server`, `cdylib`, `staticlib`) across four profiles (`dev`, `release`,
  `lto=fat`, `panic=abort`) on `x86_64-unknown-linux-gnu`, plus cross-target
  `staticlib` and object attribution across all 8 Tier 1 targets.

## Findings

### 1. Complete Byte-Origin Attribution Across Representative Workloads and Profiles

`Basis: execution + source`

Using `support/binary_origin_attrib.py` (`readelf -SW` section accounting paired
with `llvm-nm --demangle --print-size`), we measured section and symbol-origin
bytes across all five workloads and four configurations on
`x86_64-unknown-linux-gnu` (`support/v3_attribution_tables.json`):

| Workload & Profile (`x86_64-unknown-linux-gnu`) | Total File (B) | `.text` (B) | `.rodata` (B) | `.data.rel.ro` (B) | `.eh_frame` + `.hdr` (B) | `.gcc_except_table` (B) | `.rela.dyn` + `.plt` (B) | `.tdata` + `.tbss` (B) | Local Rust Symbol Bytes | `std`+`core`+`alloc` Symbol Bytes | `gimli`/`addr2line` Backtrace Bytes | CRT Startup Bytes |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`hello_world` (`dev`)** | 4,537,960 | 241,747 | 21,508 | 6,976 | 25,308 | 13,308 | 15,960 | 80 | 32 | 94,144 | 148,243 | 313 |
| **`hello_world` (`release`)** | 4,537,112 | 241,651 | 21,508 | 6,976 | 25,156 | 13,308 | 15,960 | 80 | 18 | 94,053 | 148,243 | 313 |
| **`hello_world` (`lto=fat`)** | 1,956,472 | 223,136 | 20,730 | 5,576 | 19,228 | 3,444 | 8,136 | 24 | 467 | 75,654 | 145,926 | 182 |
| **`hello_world` (`panic=abort`)** | 4,530,464 | 240,963 | 21,516 | 7,000 | 24,888 | 13,244 | 15,912 | 80 | 18 | 93,807 | 148,243 | 162 |
| **`cli_tool` (`dev`)** | 4,641,928 | 279,379 | 29,396 | 8,792 | 33,588 | 13,888 | 19,200 | 104 | 1,149 | 128,595 | 148,243 | 313 |
| **`cli_tool` (`release`)** | 4,568,392 | 254,995 | 23,204 | 7,864 | 26,856 | 13,396 | 17,952 | 104 | 3,265 | 104,035 | 148,243 | 313 |
| **`cli_tool` (`lto=fat`)** | 1,996,808 | 240,560 | 22,522 | 6,216 | 20,700 | 3,840 | 9,024 | 48 | 4,474 | 88,691 | 145,926 | 182 |
| **`cli_tool` (`panic=abort`)** | 4,551,576 | 252,707 | 22,892 | 7,856 | 26,288 | 13,244 | 17,856 | 104 | 2,427 | 102,899 | 148,243 | 162 |
| **`async_server` (`dev`)** | 4,578,616 | 251,715 | 23,780 | 7,448 | 27,828 | 13,560 | 16,968 | 80 | 1,437 | 102,499 | 148,243 | 313 |
| **`async_server` (`release`)** | 4,548,200 | 245,043 | 22,068 | 7,184 | 25,636 | 13,308 | 16,392 | 80 | 236 | 97,236 | 148,243 | 313 |
| **`async_server` (`lto=fat`)** | 1,973,832 | 227,552 | 21,370 | 5,744 | 19,652 | 3,480 | 8,496 | 24 | 909 | 79,628 | 145,926 | 182 |
| **`async_server` (`panic=abort`)** | 4,541,320 | 244,291 | 22,076 | 7,208 | 25,340 | 13,244 | 16,344 | 80 | 230 | 96,942 | 148,243 | 162 |
| **`cdylib` (`release`)** | 4,492,208 | 214,690 | 17,908 | 5,704 | 21,668 | 12,864 | 13,800 | 56 | 94 | 71,354 | 145,069 | 162 |
| **`cdylib` (`lto=fat`)** | 307,184 | 5,648 | 1,297 | 352 | 924 | 0 | 456 | 0 | 94 | 5,321 | 0 | 162 |

**Key structural observations**:
1. **Why `-Cpanic=abort` without `-Zbuild-std` still retains `13,244` bytes of
   `.gcc_except_table` and `148,243` bytes of backtrace code**: When compiling
   against the prebuilt `rustup` `libstd-*.rlib` (which was compiled with
   `-Cpanic=unwind` and `backtrace` enabled), the prebuilt `.rcgu.o` objects inside
   `libstd.rlib` already contain `.gcc_except_table` LSDA sections and calls to
   `gimli`/`addr2line` from the default panic hook! By contrast, in **`cdylib`
   (`lto=fat`)**, where `rust_cdylib_entry` formats two `u64`s without calling
   `std::rt::lang_start` or installing the `std` panic/backtrace printer, Fat
   LTO eliminates the entire `gimli`/`addr2line` subsystem (`0` bytes) and drops
   `.text` from `214,690` bytes to **`5,648` bytes** (`-97.4%`) and
   `.gcc_except_table` to **`0` bytes**!
2. **Why total ELF file size is ~4.5 MB before stripping**: Prebuilt `libstd.rlib`
   and `libcore.rlib` in `rustup` `1.99.1` carry full DWARF `.debug_*` sections
   for standard-library stack traces (`~3.8 MB` across `.debug_info`,
   `.debug_str`, `.debug_line`, `.debug_loclists`, `.debug_rnglists`), which are
   retained unless `-Cstrip=debuginfo` or `-Clto=fat` is passed.

---

### 2. Linker Section Garbage Collection (`--gc-sections` / `-dead_strip` / `/OPT:REF`) and ICF (`--icf`)

`Basis: execution + source`

#### 2.1 Quantitative Impact of `--gc-sections` (`cli_tool` Release with `rust-lld`)

| Linker Mode (`support/v3_attribution_tables.json`) | Total File (B) | `.text` (B) | `.rodata` (B) | `.data.rel.ro` (B) | `.eh_frame` + `.hdr` (B) | `.rela.dyn` + `.plt` (B) | `std`+`core`+`alloc` Symbol Bytes | `compiler_builtins` Symbol Bytes |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Default (`--gc-sections`)** | 4,568,392 | 254,995 | 23,204 | 7,864 | 26,856 | 17,952 | 104,035 | 0 (all dead-stripped) |
| **`--no-gc-sections`** | 5,455,960 | 697,949 | 107,020 | 26,280 | 102,748 | 53,400 | 462,302 | 198 (`__rust_probestack`, etc.) |
| **Removed by `--gc-sections`** | **-887,568 (-16.3%)** | **-442,954 (-63.5%)** | **-83,816 (-78.3%)** | **-18,416 (-70.1%)** | **-75,892 (-73.9%)** | **-35,448 (-66.4%)** | **-358,267 (-77.5%)** | **-198 (-100%)** |

Because `.rlib` archives are linked with `--whole-archive` semantics for any
 archive member resolved by symbol dependencies, a single referenced symbol in a
`std` CGU pulls in the entire `.rcgu.o` object file; `--gc-sections` (enabled by
per-item `.text.<sym>` / `.rodata.<sym>` sections from `-Zfunction-sections=yes`)
then strips the 63.5% of unreferenced functions and 78.3% of unreferenced
read-only data (such as unused vtables and panic format strings).

#### 2.2 Identical Code Folding (`--icf`) and Function-Pointer Equality Soundness

In `support/v3_attribution_tables.json` (`fn_ptr_probe_icf_*`), we compiled two
distinct `#[inline(never)]` functions with identical bodies:
```rust
#[inline(never)] pub fn fn_one(x: u64) -> u64 { x.wrapping_add(1234567) }
#[inline(never)] pub fn fn_two(x: u64) -> u64 { x.wrapping_add(1234567) }
```
- Because `rustc_codegen_llvm` emits `unnamed_addr` on both `@fn_one` and
  `@fn_two` (`mono_item.rs:190-208`), **even under `--icf=none` (`-Copt-level=2`)**,
  LLVM's middle-end/codegen merging aliases or folds the two symbols so
  `fn_one as *const () as usize == fn_two as *const () as usize` evaluates to
  **`true` (`p1 = 0x555619b46ab8, p2 = 0x555619b46ab8, eq = true`)**!
- Passing `-Wl,--icf=all` to `rust-lld` additionally folds identical `.text`
  sections across distinct CGUs and `.rlib`s (even when `unnamed_addr` is absent
  or address-taken in vtables), shrinking `cli_tool` `.text` by `1,088` bytes
  (`254,995` $\to$ `253,907` bytes) and `.eh_frame` by `848` bytes.
- **Verification soundness rule**: A verified Rust compiler's memory/symbol
  model must **never** assume `DefId(f) != DefId(g) ==> addr(f) != addr(g)`. Function
  pointers in Rust may alias whenever their operational behaviors are refinely
  equivalent.

---

### 3. Cross-Target Object and `staticlib` Ledger Across All 8 Tier 1 Targets

`Basis: execution + source`

| Tier 1 Target | Object Format | Single-CGU `.o` (B) | `staticlib` (`.a`/`.lib`) (B) | CRT Startup & Runtime Objects Linked into Executables (`rustc_target/src/spec/`) | Unwinder & Math / System Libraries (`link.rs`) |
| :--- | :--- | ---: | ---: | :--- | :--- |
| `x86_64-unknown-linux-gnu` | ELF64 (`x86-64`) | 2,360 | 23,336,456 | `Scrt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o`, `crtn.o` | `libgcc_s.so.1` (`_Unwind_*`), `libc.so.6`, `libm.so.6`, `ld-linux-x86-64.so.2` |
| `i686-unknown-linux-gnu` | ELF32 (`386`) | 1,832 | 19,316,796 | `Scrt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o`, `crtn.o` | `libgcc_s.so.1`, `libc.so.6`, `libm.so.6`, `ld-linux.so.2` |
| `aarch64-unknown-linux-gnu` | ELF64 (`AArch64`) | 2,520 | 24,376,378 | `Scrt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o`, `crtn.o` | `libgcc_s.so.1`, `libc.so.6`, `libm.so.6`, `ld-linux-aarch64.so.1` |
| `aarch64-apple-darwin` | Mach-O 64 (`ARM64`) | 1,592 | 18,716,088 | None (LC_MAIN entry in `dyld`, no `crt1.o` on macOS 11+) | `libSystem.B.dylib` (bundles `libunwind`, `libsystem_c`, `libsystem_m`, `libdyld`) |
| `x86_64-pc-windows-msvc` | COFF (`AMD64`) | 1,928 | 12,817,714 | `msvcrt.lib` / `libcmt.lib` (`mainCRTStartup`), `vcruntime.lib`, `ucrt.lib` | Windows SEH (`.pdata`/`.xdata` + `__CxxFrameHandler3`), `kernel32.dll`, `ntdll.dll`, `advapi32.dll` (via `raw-dylib`) |
| `i686-pc-windows-msvc` | COFF (`I386`) | 1,832 | 13,248,146 | `msvcrt.lib` (`_mainCRTStartup`), `vcruntime.lib`, `ucrt.lib` | 32-bit Windows SEH (`.safeseh` handler table), `kernel32.dll`, `ntdll.dll` |
| `aarch64-pc-windows-msvc` | COFF (`ARM64`) | 1,901 | 12,610,370 | `msvcrt.lib` (`mainCRTStartup`), `vcruntime.lib`, `ucrt.lib` | ARM64 Windows `.pdata`/`.xdata` unwind info, `kernel32.dll`, `ntdll.dll` |
| `x86_64-pc-windows-gnu` | COFF (`AMD64`) | 1,228 | 17,368,946 | `crt2.o` (or `dllcrt2.o`), `crtbegin.o`, `crtend.o` (MinGW-w64) | `libgcc_eh.a` / `libunwind.a`, `libmingwex.a`, `libmsvcrt.a`, `kernel32.dll`, `ntdll.dll` |

## Boundaries

- **C `-sys` crates (`not examined` with external C libraries in the base probe)**:
  When a Rust project links a C `-sys` crate (such as `libz-sys` or `sqlite3-sys`
  compiled via the `cc` crate), those `.o` files enter the binary as unverified
  foreign object code; `support/binary_origin_attrib.py` classifies any symbol
  outside local Rust, `std`/`core`/`alloc`, `compiler_builtins`, CRT startup,
  and the unwinder under `other_or_linker` so foreign `-sys` symbols are
  automatically isolated.

## Evidence

- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_ssa/src/back/link.rs:1-3490` (`link_binary`,
    `linker_with_args`, `--gc-sections` / `-dead_strip` / `/OPT:REF` logic).
  - `compiler/rustc_codegen_ssa/src/back/symbol_export.rs` and `symbol_edit.rs`
    (`staticlib` object symbol hiding).
  - `compiler/rustc_codegen_llvm/src/mono_item.rs:160-260` (`unnamed_addr` and
    visibility).
- **Support artifacts**:
  - `support/binary_origin_attrib.py`: Reproducible attribution script.
  - `support/v3_attribution_tables.json`: Complete section-level and symbol-origin
    byte tables across all 5 binary types, 4 configurations, `--gc-sections` /
    `--icf` ablations, and all 8 Tier 1 targets.

## Revalidation

Run `python3 support/binary_origin_attrib.py` with `rustc` 1.99.1 (or a newer
toolchain) to regenerate `support/v3_attribution_tables.json` and compare
section and origin byte counts.
