# rustc Object File Formats, Sections, Symbols, COMDATs, and Relocations Across Tier 1 Targets

## Summary

`rustc` emits relocatable object files (`.o` / `.obj`) through two distinct paths:
LLVM's integrated `MCObjectStreamer` backend (`compiler/rustc_codegen_llvm/src/back/write.rs`)
for codegen units and `rustc`'s direct `object::write::Object` serializer
(`compiler/rustc_codegen_ssa/src/back/metadata.rs`, using `object 0.37.3`) for
synthetic metadata and linker-symbol wrapper objects (`lib.rmeta`, `lib.rmeta-link`,
`rmeta.o`, and `symbols.o`). Across the eight Tier 1 targets in `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `22.1.1`), those two paths produce
three container families—ELF (`ELF64` on `x86_64` and `aarch64`, `ELF32` on `i686`),
Mach-O 64-bit (`MH_OBJECT` on `aarch64-apple-darwin`), and PE/COFF (`IMAGE_FILE_MACHINE_AMD64`,
`IMAGE_FILE_MACHINE_I386`, and `IMAGE_FILE_MACHINE_ARM64` across the four Windows targets)—and
exercise only a tightly bounded subset of each specification's relocation, section,
symbol, and COMDAT encodings:

1. **Bounded relocation subsets**: Across all **2,865** object files inside the
   prebuilt `rustc 1.99.1` Tier 1 sysroot `.rlib` archives (**1,584,454** total
   relocations) and **80** object files compiled from a 10-crate stratified sample
   (**67,429** relocations), `rustc` emits only **10** of 43 ELF x86-64 relocation
   types, **10** of 44 ELF i386 relocation types (encoded in `SHT_REL` rather than
   `SHT_RELA`), **19** of >130 ELF AArch64 relocation types, **11** of 11 Mach-O
   ARM64 relocation types (plus **7** of 8 `LC_LINKER_OPTIMIZATION_HINT` kinds),
   **5** COFF AMD64 relocation types (`4` on `x86_64-pc-windows-gnu`), **5** COFF
   i386 relocation types, and **12** COFF ARM64 relocation types.
2. **Per-function section splitting vs subsection atomization**: `TargetOptions::default()`
   (`compiler/rustc_target/src/spec/mod.rs:2892`) sets `function_sections: true`,
   emitting one `.text.<sym>` / `.data.<sym>` / `.rodata.<sym>` / `.bss.<sym>` section
   per symbol on ELF and Windows MSVC targets, with two Tier 1 overrides:
   `aarch64-apple-darwin` sets `function_sections: false` and relies on Mach-O's
   `MH_SUBSECTIONS_VIA_SYMBOLS` (`0x2000`) header flag so `ld64`/`ld64.lld` splits
   sections on symbol boundaries, and `x86_64-pc-windows-gnu` sets `function_sections: false`
   in `compiler/rustc_target/src/spec/targets/x86_64_pc_windows_gnu.rs:26` to avoid
   GNU `ld.bfd` COFF section-table scaling bottlenecks.
3. **Synthetic object invariants for hardware CFI/BTI/PAC**: Because ELF linkers
   compute output `.note.gnu.property` feature bits (`GNU_PROPERTY_X86_FEATURE_1_IBT | SHSTK`
   on x86-64, `GNU_PROPERTY_AARCH64_FEATURE_1_BTI | PAC` on AArch64) as the bitwise
   AND across all relocatable inputs, `rustc`'s synthetic object writer
   (`compiler/rustc_codegen_ssa/src/back/metadata.rs:129-175`) unconditionally injects
   a `.note.gnu.property` section with `pr_data = 0x3` into every `lib.rmeta`,
   `lib.rmeta-link`, `rmeta.o`, and `symbols.o` on `x86_64`, `i686`, and `aarch64` ELF
   targets whenever the binary format is ELF.

## Applicability

- **Pinned toolchain**: `rustc 1.99.1 (58cf8f9c3 2026-03-23)`, commit
  `58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled LLVM `22.1.1`
  (`519b92f53a7a2de5fe0db9df5cd4bc9fb1ea8ff6`), `object 0.37.3`.
- **Target matrix**: All eight Rust Tier 1 targets:
  - `x86_64-unknown-linux-gnu` (`elf`, 64-bit, `SHT_RELA`)
  - `i686-unknown-linux-gnu` (`elf`, 32-bit, `SHT_REL`)
  - `aarch64-unknown-linux-gnu` (`elf`, 64-bit, `SHT_RELA`)
  - `aarch64-apple-darwin` (`mach-o`, 64-bit, `MH_OBJECT`)
  - `x86_64-pc-windows-msvc` (`coff`, 64-bit, `IMAGE_FILE_MACHINE_AMD64`)
  - `x86_64-pc-windows-gnu` (`coff`, 64-bit, `IMAGE_FILE_MACHINE_AMD64`)
  - `i686-pc-windows-msvc` (`coff`, 32-bit, `IMAGE_FILE_MACHINE_I386`)
  - `aarch64-pc-windows-msvc` (`coff`, 64-bit, `IMAGE_FILE_MACHINE_ARM64`)
- **Downstream consumers**: Verified assemblers, object encoders, and linkers
  targeting `rustc` output (see `verified-assemblers-encoders-linkers-and-object-format-models`).

## Findings

### 1. Container Headers, Code Models, TLS Models, and Default Codegen Flags

`compiler/rustc_target/src/spec/mod.rs:2849-2999` defines `TargetOptions::default()`,
and each Tier 1 target spec overrides only target-specific fields. Across all eight
Tier 1 targets (`--print target-spec-json` in `support/tier1_target_specs.json`):

| Target | Container & Machine | Reloc Model | Code Model | TLS Model | `function-sections` | `plt-by-default` | Default CPU / Features |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `ELF64-x86-64` (`EM_X86_64 = 62`) | `pic` | `small` | `initial-exec` (bins) / `global-dynamic` (rlibs/dylibs) | `true` | `false` (`-Zplt` off) | `x86-64` (`+sse2`) |
| `i686-unknown-linux-gnu` | `ELF32-i386` (`EM_386 = 3`) | `pic` | `small` | `global-dynamic` | `true` | `true` | `pentium4` (`+sse2`) |
| `aarch64-unknown-linux-gnu` | `ELF64-aarch64` (`EM_AARCH64 = 183`) | `pic` | `small` | `global-dynamic` (TLSDESC) | `true` | `true` | `generic` (`+v8a`, `+neon`) |
| `aarch64-apple-darwin` | `Mach-O 64-bit arm64` (`CPU_TYPE_ARM64 = 0x0100000c`) | `pic` | `small` | `global-dynamic` (`__thread_vars`) | `false` (`MH_SUBSECTIONS_VIA_SYMBOLS`) | `true` | `apple-m1` (`+v8.4a`, `+aes`, `+sha2`, `+lse`, `+rcpc`, `+zcm`, `+zcz`) |
| `x86_64-pc-windows-msvc` | `COFF-x86-64` (`0x8664`) | `pic` | `small` | `implicit-dynamic` (`.tls$`) | `true` | `false` | `x86-64` (`+sse2`, `+cx16`, `+sahf`) |
| `x86_64-pc-windows-gnu` | `COFF-x86-64` (`0x8664`) | `pic` | `small` | `implicit-dynamic` (`.tls$`) | `false` | `false` | `x86-64` (`+sse2`, `+cx16`) |
| `i686-pc-windows-msvc` | `COFF-i386` (`0x014c`) | `dynamic-no-pic` | `small` | `implicit-dynamic` (`.tls$`) | `true` | `true` | `pentium4` (`+sse2`) |
| `aarch64-pc-windows-msvc` | `COFF-ARM64` (`0xaa64`) | `pic` | `small` | `implicit-dynamic` (`.tls$`) | `true` | `true` | `generic` (`+v8a`, `+neon`, `+fp-armv8`) |

Key container-level invariants verified in `rustc 1.99.1`:

1. **`SHT_RELA` vs `SHT_REL` on ELF**: `x86_64-unknown-linux-gnu` and
   `aarch64-unknown-linux-gnu` emit explicit-addend `SHT_RELA` (`0x4`, 24-byte
   `Elf64_Rela` entries), whereas `i686-unknown-linux-gnu` emits implicit-addend
   `SHT_REL` (`0x9`, 8-byte `Elf32_Rel` entries with the addend stored inline in
   the relocated instruction/data bytes).
2. **Mach-O `MH_SUBSECTIONS_VIA_SYMBOLS` and `LC_BUILD_VERSION`**: Every
   `aarch64-apple-darwin` `.o` file emitted by LLVM or `object::write` carries
   `MH_OBJECT` (`0x1`) with `flags = 0x2000` (`MH_SUBSECTIONS_VIA_SYMBOLS`), plus
   `LC_BUILD_VERSION` (`platform = MACOS`, `minos = 11.0.0`, `sdk = 0.0` when built
   without an Xcode SDK) and `LC_LINKER_OPTIMIZATION_HINT` (`cmd = 0x2e`).
   Because `object::write::Object::new(BinaryFormat::MachO, ...)` in
   `compiler/rustc_codegen_ssa/src/back/metadata.rs:94-99` expressly sets
   `FileFlags::MachO { subsections_via_symbols: true }`, synthetic `rmeta.o` and
   `symbols.o` objects also preserve subsection dead-stripping compatibility.
3. **COFF extended section counts (BigObj) and `@feat.00`**: When `-Zfunction-sections`
   (on by default for `*-pc-windows-msvc`) causes a single `.o` file to exceed
   `65,279` (`0xfeff`) sections, LLVM automatically upgrades the container header to
   COFF BigObj (`AnonObjectHeaderBigObj`, machine/version `0x0000` / `0xffff` with
   a 32-bit section count and class ID `D1BAA1C7-BAEE-4ba9-AF20-FAF66AA4DCB8`).
   Every LLVM-emitted COFF object defines an absolute symbol `@feat.00` (`StorageClass = Static`,
   `SectionNumber = -1`):
   - Default `@feat.00` value: `0x800` (`IMAGE_DLL_CHARACTERISTICS_EX_CET_COMPAT` / SDL check) on
     `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, and `aarch64-pc-windows-msvc`;
     `0x801` (`0x800 | 0x1` `/SAFESEH` registered exception handlers) on `i686-pc-windows-msvc`.
   - With `-C control-flow-guard=checks`: `@feat.00` adds `0x800` (CFG bit `0x0800`) and
     emits `.gfids$y` (4-byte symbol-table indices of address-taken functions).
   - With `-Z ehcont-guard` (`x86_64-pc-windows-msvc`): `@feat.00` becomes `0x4800`
     (adding `0x4000` EH continuation metadata bit) and emits `.giats$y` and `.gehcont$y`.

### 2. Standard, Compiler-Specific, and Ecosystem Sections

Across `compiler/rustc_codegen_llvm/` and `compiler/rustc_codegen_ssa/src/back/metadata.rs`,
`rustc` emits the following section families (verified empirically in
`support/t8_probe_summary.json` and `support/t8_full_census.json`):

| Section Family | ELF (`x86_64`, `i686`, `aarch64`) | Mach-O (`aarch64-apple-darwin`) | PE/COFF (`*-pc-windows-*`) | Generator & Source Citation |
| :--- | :--- | :--- | :--- | :--- |
| Code (`fn`) | `.text.<mangled>` (`SHF_ALLOC \| SHF_EXECINSTR`, plus `SHF_GROUP` if generic/inline) | `__TEXT,__text` (`S_REGULAR \| S_ATTR_PURE_INSTRUCTIONS \| S_ATTR_SOME_INSTRUCTIONS`) | `.text` (`IMAGE_SCN_CNT_CODE \| IMAGE_SCN_MEM_EXECUTE \| IMAGE_SCN_MEM_READ`, plus `IMAGE_SCN_LNK_COMDAT` on MSVC) | LLVM `MCObjectFileInfo` + `rustc_codegen_llvm/src/base.rs` |
| Read-only data | `.rodata.<mangled>`, `.rodata.cst{4,8,16,32}` (`SHF_MERGE \| SHF_STRINGS`), `.data.rel.ro.<mangled>` | `__TEXT,__const`, `__TEXT,__literal{4,8,16}`, `__TEXT,__cstring` (`S_CSTRING_LITERALS`), `__DATA,__const` | `.rdata` (`IMAGE_SCN_CNT_INITIALIZED_DATA \| IMAGE_SCN_MEM_READ`, COMDAT on MSVC) | LLVM `TargetLoweringObjectFile` |
| Writable data & BSS | `.data.<mangled>`, `.bss.<mangled>` (`SHT_NOBITS`, `SHF_ALLOC \| SHF_WRITE`) | `__DATA,__data`, `__DATA,__bss` (`S_ZEROFILL`), `__DATA,__common` | `.data`, `.bss` (`IMAGE_SCN_CNT_UNINITIALIZED_DATA \| IMAGE_SCN_MEM_READ \| IMAGE_SCN_MEM_WRITE`) | LLVM `TargetLoweringObjectFile` |
| Thread-Local Storage (`#[thread_local]`) | `.tdata.<sym>` (`SHF_ALLOC \| SHF_WRITE \| SHF_TLS`), `.tbss.<sym>` (`SHT_NOBITS \| SHF_TLS`) | `__DATA,__thread_vars` (`S_THREAD_LOCAL_VARIABLES`, 24-byte `tlv_descriptor`), `__DATA,__thread_data` (`S_THREAD_LOCAL_REGULAR`), `__DATA,__thread_bss` (`S_THREAD_LOCAL_ZEROFILL`) | `.tls$` (`IMAGE_SCN_CNT_INITIALIZED_DATA \| IMAGE_SCN_MEM_READ \| IMAGE_SCN_MEM_WRITE`) | `compiler/rustc_codegen_llvm/src/consts.rs:195-248` |
| Crate metadata (`.rmeta`) | `.rmeta` (`SHF_EXCLUDE = 0x80000000` in `lib.rmeta`; `SHF_ALLOC` in dylib `rmeta.o`) | `__DWARF,.rmeta` (`S_ATTR_DEBUG` in `lib.rmeta`) or `__DATA,__llvmbc` / `.rmeta` in dylibs | `.rmeta` (`IMAGE_SCN_MEM_READ \| IMAGE_SCN_LNK_REMOVE` in `lib.rmeta`; `IMAGE_SCN_MEM_READ` in DLL `rmeta.o`) | `compiler/rustc_codegen_ssa/src/back/metadata.rs:181-285` |
| Embedded bitcode (`-C embed-bitcode=yes`) | `.llvmbc` and `.llvmcmd` (`SHF_EXCLUDE = 0x80000000`) | `__LLVM,__bitcode` and `__LLVM,__cmdline` | `.llvmbc` and `.llvmcmd` (`IMAGE_SCN_LNK_REMOVE = 0x00000800`) | `compiler/rustc_codegen_llvm/src/back/write.rs:940-1008` |
| GDB auto-load script | `.debug_gdb_scripts` (`SHF_ALLOC \| SHF_MERGE \| SHF_STRINGS`, `entsize=1`, `gdb_load_rust_pretty_printers.py`) | *(omitted on Mach-O)* | `.debug_gdb_scripts` (`x86_64-pc-windows-gnu` only) | `compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs:28-92` |
| Unwind & exception tables | `.eh_frame` (`SHT_X86_64_UNWIND` on x86-64, `SHT_PROGBITS` on i686/aarch64), `.gcc_except_table.<fn>` | `__TEXT,__eh_frame`, `__TEXT,__unwind_info` (compact unwind), `__TEXT,__gcc_except_tab` | `.pdata` (3 $	imes$ `u32` `RUNTIME_FUNCTION`), `.xdata` (unwind codes + LSDA) on x64/ARM64; `.sxdata` on i686 | LLVM `MCDwarf` / `Win64EH` / `CompactUnwind` |
| Non-executable stack marker | `.note.GNU-stack` (`SHT_PROGBITS`, `flags = 0x0`, size `0`) | *(implicit in Mach-O)* | *(implicit in PE `NX_COMPAT`)* | `compiler/rustc_target/src/spec/mod.rs:2898` (`emit_stack_sizes`) |
| Hardware CFI/BTI/PAC property note | `.note.gnu.property` (`SHT_NOTE = 0x7`, `SHF_ALLOC`, owner `"GNU "`) | *(encoded via pointer-auth relocs / subtarget)* | `.gfids$y`, `.giats$y`, `.gehcont$y` + `@feat.00` | LLVM `X86AsmBackend` / `AArch64AsmBackend` and `metadata.rs:129-175` |
| Identical Code Folding address-taken table | `.llvm_addrsig` (`SHT_LLVM_ADDRSIG = 0x6fff4c03`, `SHF_EXCLUDE`) | `__DATA,__llvm_addrsig` *(when enabled)* | `.llvm_addrsig` (`IMAGE_SCN_LNK_REMOVE = 0x800`) | LLVM `MCObjectStreamer::emitAddrsig` |
| Embedded linker directives | *(none)* | `LC_LINKER_OPTIMIZATION_HINT` (`0x2e`) | `.drectve` (`IMAGE_SCN_LNK_INFO \| IMAGE_SCN_LNK_REMOVE = 0x00100a00`) | `compiler/rustc_codegen_llvm/src/back/write.rs` / LLVM COFF backend |

#### Ecosystem `#[link_section]` and Compiler-Assisted Section Conventions

Empirical compilation of ecosystem idioms across all eight Tier 1 targets (`support/t8_probe_summary.json`) demonstrates the exact section and symbol lowering used by popular crates (`ctor`, `linkme`, `objc2`, Windows TLS/CRT callbacks):

1. **Static initializers (`ctor`, `.init_array` / `__mod_init_func` / `.CRT$XCU`)**:
   - ELF targets (`x86_64`, `i686`, `aarch64`): `#[link_section = ".init_array"]`
     emits a `SHT_PROGBITS` (or `SHT_INIT_ARRAY` when merged by the linker) section
     named `.init_array` with a pointer relocation (`R_X86_64_64`, `R_386_32`, or
     `R_AARCH64_ABS64`) to the initializer function.
   - `aarch64-apple-darwin`: `#[link_section = "__DATA,__mod_init_func"]` emits a
     regular `__DATA,__mod_init_func` section with an `ARM64_RELOC_UNSIGNED`
     8-byte pointer relocation.
   - Windows targets (`*-pc-windows-*`): `#[link_section = ".CRT$XCU"]` emits a
     `.CRT$XCU` (`IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ`) section
     with an `IMAGE_REL_AMD64_ADDR64` / `IMAGE_REL_I386_DIR32` /
     `IMAGE_REL_ARM64_ADDR64` relocation; the PE linker sorts `.CRT$XCA` ..
     `.CRT$XCU` .. `.CRT$XCZ` lexicographically by the `$` suffix and merges them
     into `.rdata`.
2. **Distributed slices (`linkme`)**:
   - ELF (`#[link_section = "linkme_ITEMS"]`): Emits a valid C-identifier section
     `linkme_ITEMS` (`SHF_ALLOC | SHF_WRITE`), enabling GNU `ld` and `lld` to
     auto-synthesize `__start_linkme_ITEMS` and `__stop_linkme_ITEMS`.
   - Mach-O (`#[link_section = "__DATA,__linkme"]`): Emits segment `__DATA`,
     section `__linkme`, resolved via `section$start$__DATA$__linkme` and
     `section$end$__DATA$__linkme`.
   - Windows COFF (`#[link_section = ".linkme$a"]`, `.linkme$b`, `.linkme$z`):
     Relies on COFF `$` lexicographic section-suffix sorting between sentinel
     sections `.linkme$a` and `.linkme$z`.
3. **Objective-C metadata (`objc2` and `#[rustc_objc_class]` / `#[rustc_objc_selector]`)**:
   `compiler/rustc_codegen_llvm/src/va_arg.rs` and `compiler/rustc_codegen_llvm/src/context.rs`
   lower `#[rustc_objc_class = "MyRustObjcClass"]` and `#[rustc_objc_selector = "initWithVal:"]`
   on `aarch64-apple-darwin` into four specialized Mach-O sections:
   - `__TEXT,__objc_methname` (`S_CSTRING_LITERALS = 0x2`): Null-terminated selector string `"initWithVal: "`.
   - `__DATA,__objc_selrefs` (`S_LITERAL_POINTERS | S_ATTR_NO_DEAD_STRIP = 0x10000005`): 8-byte pointer to `__TEXT,__objc_methname`.
   - `__DATA,__objc_classrefs` (`S_REGULAR | S_ATTR_NO_DEAD_STRIP = 0x10000000`): 8-byte reference to `_OBJC_CLASS_$_MyRustObjcClass`.
   - `__DATA,__objc_imageinfo` (`S_REGULAR = 0x0`): 8-byte Objective-C image info header.

### 3. Symbol Attributes, Visibilities, `#[used]`, and Mangling

`compiler/rustc_codegen_llvm/src/base.rs:95-190` (`linkage_to_llvm` and
`visibility_to_llvm`) and `compiler/rustc_codegen_llvm/src/consts.rs:285-360`
lower Rust item attributes to container symbol flags:

| Rust Construct | LLVM Linkage / List | ELF Symbol (`st_bind` / `st_other` / Section) | Mach-O Symbol (`n_type` / `n_desc`) | COFF Symbol (`StorageClass` / COMDAT) |
| :--- | :--- | :--- | :--- | :--- |
| Exported non-generic `pub fn` / `#[no_mangle]` | `ExternalLinkage`, `Default` visibility | `STB_GLOBAL`, `STV_DEFAULT` | `N_SECT \| N_EXT` (`0x0f`) | `IMAGE_SYM_CLASS_EXTERNAL (2)`, COMDAT `IMAGE_COMDAT_SELECT_NODUPLICATES (1)` on MSVC |
| Internal / non-exported item | `InternalLinkage` or `ExternalLinkage` + `Hidden` | `STB_LOCAL` or `STB_GLOBAL` + `STV_HIDDEN` (`0x02`) | `N_SECT` (local) or `N_SECT \| N_EXT \| N_PEXT` (`0x1f`, private external) | `IMAGE_SYM_CLASS_STATIC (3)` or `EXTERNAL` (unexported unless in `.def` / `-export:`) |
| Shared generic / `#[inline]` monomorphization | `WeakODRLinkage` or `LinkOnceODRLinkage` | `STB_WEAK`, `STV_HIDDEN` (or `STV_DEFAULT` in dylib), inside `SHT_GROUP` (`GRP_COMDAT = 0x1`) | `N_SECT \| N_EXT (\| N_PEXT)`, `N_WEAK_DEF` (`0x0080`) | `IMAGE_SYM_CLASS_EXTERNAL (2)`, COMDAT `IMAGE_COMDAT_SELECT_ANY (2)` |
| `#[linkage = "extern_weak"]` | `ExternalWeakLinkage` | `STB_WEAK`, `SHN_UNDEF` | `N_UNDF \| N_EXT`, `N_WEAK_REF` (`0x0040`) | Weak external (`IMAGE_SYM_CLASS_WEAK_EXTERNAL = 105`) |
| `#[used]` / `#[used(compiler)]` | `@llvm.compiler.used` (`add_compiler_used_global`) | Preserved past LLVM passes; **no** `SHF_GNU_RETAIN`, **no** `N_NO_DEAD_STRIP`, **no** `-include:` | Preserved past LLVM passes; **no** `N_NO_DEAD_STRIP` (`0x0020`) | Preserved past LLVM passes; **no** `.drectve` `/INCLUDE:` |
| `#[used(linker)]` (`#![feature(used_with_arg)]`) | `@llvm.used` (`add_used_global`) | Section gets `SHF_GNU_RETAIN` (`0x00200000`) | Symbol gets `N_NO_DEAD_STRIP` (`0x0020` in `n_desc`) | Emits `/INCLUDE:<sym>` (or `-include:<sym>` on MinGW) into `.drectve` |

Critical empirical verification from `support/t8_probe_summary.json`:

1. **`#[used(compiler)]` vs `#[used(linker)]`**: In `rustc 1.99.1`, bare `#[used]`
   defaults to `#[used(compiler)]` (`@llvm.compiler.used`). On ELF, `#[used(compiler)]`
   emits `.data.USED_COMPILER` with flags `SHF_ALLOC | SHF_WRITE` (`0x3`), whereas
   `#[used(linker)]` emits `.data.USED_LINKER` with flags
   `SHF_ALLOC | SHF_WRITE | SHF_GNU_RETAIN` (`0x200003`). On `aarch64-apple-darwin`,
   `#[used(linker)]` sets `N_NO_DEAD_STRIP` (`0x0020`) on `_USED_LINKER`. On Windows
   targets, `#[used(linker)]` appends `/INCLUDE:USED_LINKER` (`x86_64`/`aarch64` MSVC),
   `/INCLUDE:_USED_LINKER` (`i686-pc-windows-msvc`), or `-include:USED_LINKER`
   (`x86_64-pc-windows-gnu`) to the `.drectve` section.
2. **Symbol mangling and ABI decorations**:
   - Default symbol mangling in `rustc 1.99.1` is `"legacy"` (`_ZN...E`), with `"v0"`
     (`_R...`) selectable via `-C symbol-mangling-version=v0`.
   - On `aarch64-apple-darwin` and `i686-pc-windows-msvc`, the target ABI prepends
     a leading underscore (`_`) to all C and Rust symbols (unless suppressed via LLVM's
     `` raw symbol prefix, as used for `__imp__<sym>` on `i686-pc-windows-msvc`).
   - On `i686-pc-windows-msvc`, `stdcall`, `fastcall`, and `vectorcall` functions carry
     byte-count suffixes (`_foo@8`, `@foo@8`, `foo@@8`), handled during import-library
     and `.def` generation by `compiler/rustc_codegen_ssa/src/back/linker.rs` and
     `compiler/rustc_codegen_llvm/src/common.rs:140-185`.

### 4. COMDAT Groups, Associative Sections, and Mach-O Subsection Splitting

The three container formats represent duplicate-elimination and section-level GC
dependencies through completely different mechanisms:

| Target Family | Mechanism | Empirical Census Across `rustc 1.99.1` Sysroot `.rlib`s (`support/t8_full_census.json`) |
| :--- | :--- | :--- |
| ELF (`x86_64`, `i686`, `aarch64`) | `SHT_GROUP` (`0x11`) sections with flag `GRP_COMDAT (0x1)` and `SHF_GROUP (0x200)` on member sections (`.text.<sym>`, `.rodata.<sym>`, `.gcc_except_table.<sym>`) | `x86_64-unknown-linux-gnu`: **4,016** `GRP_COMDAT` groups across 420 `.o` files; `i686`: **3,991** across 354 `.o` files; `aarch64`: **4,009** across 451 `.o` files. Only `GRP_COMDAT` (`0x1`) is ever emitted. |
| Mach-O (`aarch64-apple-darwin`) | No section groups; `MH_SUBSECTIONS_VIA_SYMBOLS (0x2000)` splits every section at each non-`L`-prefixed symbol into an independent atom, and weak symbols use `N_WEAK_DEF (0x0080)` | **0** section groups across 419 sysroot `.o` files; **100%** of `.o` files carry `MH_SUBSECTIONS_VIA_SYMBOLS`. Compact unwind (`__LD,__compact_unwind`) implicitly associates with each function atom. |
| COFF (`*-pc-windows-msvc`) | Auxiliary Section Definition records carrying a 1-byte `Selection` kind and an `AssocSection` index | Across `x86_64-pc-windows-msvc` (317 `.o` files): **`IMAGE_COMDAT_SELECT_ASSOCIATIVE (5)`**: **7,784** (linking `.pdata` and `.xdata` to their `.text` section so `/OPT:REF` keeps or drops unwind info with its function); **`IMAGE_COMDAT_SELECT_NODUPLICATES (1)`**: **6,514** (non-generic functions/statics under `-Zfunction-sections`); **`IMAGE_COMDAT_SELECT_ANY (2)`**: **539** (generic/inline monomorphizations); **`IMAGE_COMDAT_SELECT_LARGEST (6)`**: **1**. |
| COFF (`x86_64-pc-windows-gnu`) | `IMAGE_COMDAT_SELECT_ANY (2)` and `SAME_SIZE (3)` only for weak/linkonce items (because `function-sections` is `false` and unwind uses DWARF/SEH in `.pdata`/`.xdata` per-object) | Across 277 `.o` files: **`IMAGE_COMDAT_SELECT_ANY (2)`**: **211**; **`IMAGE_COMDAT_SELECT_SAME_SIZE (3)`**: **1**; `NODUPLICATES`: **0**; `ASSOCIATIVE`: **0**. |

### 5. Complete Empirical Relocation Census Across All 8 Tier 1 Targets

Inspecting all **2,865** object files inside every `.rlib` of the `rustc 1.99.1`
sysroot (`libstd`, `libcore`, `liballoc`, `libcompiler_builtins`, `libunwind`,
`libgimli`, `libobject`, `libmemchr`, `libaddr2line`, `libadler2`, `libminiz_oxide`,
`libhashbrown`, `libcfg_if`, `librustc_demangle`, `libpanic_unwind`, `libpanic_abort`,
`libstd_detect`, `libsysroot`) and **80** object files compiled from the 10-crate
sample (`bitflags`, `byteorder`, `bytes`, `hashbrown`, `itoa`, `memchr`, `once_cell`,
`regex_syntax`, `ryu`, `unicode_ident` at `-C opt-level=3`, `support/t8_full_census.json`)
establishes the exact set of relocation types `rustc 1.99.1` emits:

#### 5.1 `x86_64-unknown-linux-gnu` (`ELF64`, `SHT_RELA` — 10 Relocation Kinds)

| Relocation Kind | ELF Code | Sysroot `.rlib` Count (420 `.o` files) | 10-Crate Sample Count (10 `.o` files) | Primary Emission Context |
| :--- | ---: | ---: | ---: | :--- |
| `R_X86_64_64` | `1` | 177,162 | 122 | 64-bit absolute pointers in `.data.rel.ro`, `.eh_frame`, and `.debug_*` |
| `R_X86_64_32` | `10` | 108,436 | 0 | 32-bit DWARF `.debug_*` section offsets (zero in stripped `-O3` sample crates) |
| `R_X86_64_PC32` | `2` | 31,093 | 4,769 | RIP-relative data/rodata addressing, jump tables, `.eh_frame` FDE PC-relative pointers |
| `R_X86_64_GOTPCREL` | `9` | 17,616 | 1,683 | Direct GOT loads (`call *foo@GOTPCREL(%rip)` under `-Zplt=no` and external symbol references) |
| `R_X86_64_PLT32` | `4` | 8,754 | 758 | Direct PC-relative `call` / `jmp` to functions (`call foo@PLT`) |
| `R_X86_64_GOTTPOFF` | `22` | 195 | 0 | Initial-exec TLS offset loads via GOT (`mov foo@GOTTPOFF(%rip), %reg`) |
| `R_X86_64_TLSGD` | `19` | 181 | 0 | General-dynamic TLS (`__tls_get_addr` argument pair) |
| `R_X86_64_REX_GOTPCRELX` | `42` | 84 | 0 | Relaxable REX-prefixed GOT load (`movq sym@GOTPCREL(%rip), %reg`, emitted by C/assembly in `libbacktrace`/`compiler_builtins`) |
| `R_X86_64_DTPOFF32` | `21` | 28 | 0 | TLS offset within module (`.debug_info` TLS location descriptions and local-dynamic TLS) |
| `R_X86_64_TLSLD` | `20` | 16 | 0 | Local-dynamic TLS module ID lookup |

#### 5.2 `i686-unknown-linux-gnu` (`ELF32`, `SHT_REL` — 10 Relocation Kinds)

| Relocation Kind | ELF Code | Sysroot `.rlib` Count (354 `.o` files) | 10-Crate Sample Count (10 `.o` files) | Primary Emission Context |
| :--- | ---: | ---: | ---: | :--- |
| `R_386_32` | `1` | 291,073 | 122 | 32-bit absolute pointers in `.data.rel.ro` and `.debug_*` |
| `R_386_GOTOFF` | `9` | 14,815 | 4,781 | Offset from `_GLOBAL_OFFSET_TABLE_` to local/hidden data and rodata |
| `R_386_PLT32` | `4` | 13,641 | 1,419 | PC-relative function calls via PLT (`plt-by-default: true`) |
| `R_386_PC32` | `2` | 8,108 | 708 | `__x86.get_pc_thunk.*` calls and `.eh_frame` PC-relative encodings |
| `R_386_GOTPC` | `10` | 3,091 | 629 | PC-relative offset to `_GLOBAL_OFFSET_TABLE_` in PIC prologues |
| `R_386_GOT32` | `3` | 985 | 124 | 32-bit GOT slot offset for external symbols |
| `R_386_TLS_GD` | `18` | 181 | 0 | General-dynamic TLS (`___tls_get_addr`) |
| `R_386_GOT32X` | `43` | 82 | 0 | Relaxable GOT load (from assembled C/ASM runtime inputs) |
| `R_386_TLS_LDO_32` | `32` | 23 | 0 | Local-dynamic TLS offset |
| `R_386_TLS_LDM` | `19` | 14 | 0 | Local-dynamic TLS module lookup |

#### 5.3 `aarch64-unknown-linux-gnu` (`ELF64`, `SHT_RELA` — 19 Relocation Kinds)

| Relocation Kind | ELF Code | Sysroot `.rlib` Count (451 `.o` files) | 10-Crate Sample Count (10 `.o` files) | Primary Emission Context |
| :--- | ---: | ---: | ---: | :--- |
| `R_AARCH64_ABS64` | `257` | 202,296 | 122 | 64-bit absolute addresses in `.data.rel.ro`, vtables, and `.debug_*` |
| `R_AARCH64_ABS32` | `258` | 116,221 | 0 | 32-bit `.debug_*` section offsets |
| `R_AARCH64_CALL26` | `283` | 17,234 | 1,297 | `bl` 26-bit PC-relative branch-with-link ($\pm 128	ext{ MiB}$) |
| `R_AARCH64_ADR_PREL_PG_HI21` | `275` | 9,202 | 2,520 | `adrp` 4 KiB page-relative high 21 bits ($\pm 4	ext{ GiB}$) |
| `R_AARCH64_ADD_ABS_LO12_NC` | `277` | 8,669 | 2,367 | `add` low 12-bit page offset paired with `adrp` |
| `R_AARCH64_PREL32` | `261` | 4,271 | 523 | 32-bit PC-relative offsets in `.eh_frame` and relative jump tables |
| `R_AARCH64_JUMP26` | `282` | 1,136 | 93 | Tail-call / unconditional `b` 26-bit PC-relative branch |
| `R_AARCH64_ADR_GOT_PAGE` | `311` | 1,042 | 124 | `adrp` to GOT entry page |
| `R_AARCH64_LD64_GOT_LO12_NC` | `312` | 1,035 | 124 | `ldr` 64-bit pointer from GOT page offset |
| `R_AARCH64_PREL64` | `260` | 846 | 0 | 64-bit PC-relative pointer in `.eh_frame` |
| `R_AARCH64_LDST{64,8,128,32,16}_ABS_LO12_NC` | `286,278,299,285,284` | 645 (total) | 172 (total) | Folded `ldr`/`str` low-12-bit page offsets (`LDST64`: 472/84; `LDST8`: 98/39; `LDST128`: 35/15; `LDST32`: 31/24; `LDST16`: 9/10) |
| `R_AARCH64_TLSDESC_{ADR_PAGE21,LD64_LO12,ADD_LO12,CALL}` | `562,563,564,569` | 195 each (780 total) | 0 | 4-instruction TLSDESC sequence (`adrp` + `ldr` + `add` + `blr`) |

#### 5.4 `aarch64-apple-darwin` (`Mach-O 64-bit arm64` — 11 Relocation Kinds & 7 LOH Kinds)

| Relocation / LOH Kind | Mach-O Code | Sysroot `.rlib` Count (419 `.o` files) | 10-Crate Sample Count (10 `.o` files) | Primary Emission Context |
| :--- | ---: | ---: | ---: | :--- |
| `ARM64_RELOC_UNSIGNED` | `0` | 87,857 | 797 | 64-bit/32-bit absolute pointers in `__DATA,__const`, `__LD,__compact_unwind`, and DWARF |
| `ARM64_RELOC_BRANCH26` | `2` | 17,460 | 1,389 | `bl` / `b` 26-bit branch instructions |
| `ARM64_RELOC_PAGEOFF12` | `4` | 9,465 | 2,542 | `add` / `ldr` / `str` 12-bit page offset |
| `ARM64_RELOC_PAGE21` | `3` | 9,342 | 2,542 | `adrp` 21-bit page delta |
| `ARM64_RELOC_SUBTRACTOR` | `1` | 3,099 | 495 | Paired with `UNSIGNED` for `A - B` relative offsets (jump tables, `.eh_frame`) |
| `ARM64_RELOC_GOT_LOAD_PAGE21` | `5` | 670 | 124 | `adrp` for GOT slot page |
| `ARM64_RELOC_GOT_LOAD_PAGEOFF12` | `6` | 670 | 124 | `ldr` from GOT slot |
| `ARM64_RELOC_ADDEND` | `10` | 630 | 120 | 24-bit signed addend prefix immediately preceding `PAGE21` / `PAGEOFF12` / `BRANCH26` |
| `ARM64_RELOC_TLVP_LOAD_PAGE21` | `8` | 188 | 0 | `adrp` for `__DATA,__thread_vars` TLV descriptor |
| `ARM64_RELOC_TLVP_LOAD_PAGEOFF12` | `9` | 188 | 0 | `ldr` / `add` for TLV descriptor |
| `ARM64_RELOC_POINTER_TO_GOT` | `7` | 26 | 0 | 32-bit PC-relative pointer to GOT slot (e.g. compact unwind personality pointers) |
| **LOH**: `LOH_ARM64_ADRP_ADD` | `2` | 8,855 | 2,369 | `adrp` + `add` candidate for single-instruction `adr` relaxation |
| **LOH**: `LOH_ARM64_ADRP_LDR` | `3` | 399 | 158 | `adrp` + `ldr` candidate for PC-relative `ldr` literal relaxation |
| **LOH**: `LOH_ARM64_ADRP_LDR_GOT_LDR` | `4` | 375 | 87 | `adrp` + GOT `ldr` + dereference `ldr` relaxation |
| **LOH**: `LOH_ARM64_ADRP_LDR_GOT` | `7` | 292 | 37 | `adrp` + GOT `ldr` candidate for `adr` relaxation when target is local |
| **LOH**: `LOH_ARM64_ADRP_ADRP` | `1` | 22 | 33 | Redundant `adrp` sharing same 4 KiB page |
| **LOH**: `LOH_ARM64_ADRP_ADD_LDR` | `5` | 20 | 8 | `adrp` + `add` + `ldr` candidate for immediate offset `ldr` |
| **LOH**: `LOH_ARM64_ADRP_LDR_GOT_STR` | `8` | 1 | 0 | `adrp` + GOT `ldr` + `str` relaxation |

#### 5.5 Windows COFF Targets (`x86_64`, `i686`, `aarch64`)

| Target | Sysroot `.o` / Relocs | Sample `.o` / Relocs | Relocation Kinds Emitted (`sysroot count` / `sample count`) |
| :--- | :--- | :--- | :--- |
| `x86_64-pc-windows-msvc` | 317 / 71,710 | 10 / 4,949 | **5 kinds**: `IMAGE_REL_AMD64_REL32 (4)` (`44,043` / `4,824`), `IMAGE_REL_AMD64_ADDR32NB (3)` (`24,499` / `3` in `.pdata`/`.xdata`), `IMAGE_REL_AMD64_SECREL (11)` (`2,174` / `0` in debug/TLS), `IMAGE_REL_AMD64_SECTION (10)` (`566` / `0`), `IMAGE_REL_AMD64_ADDR64 (1)` (`428` / `122` in vtables/data) |
| `x86_64-pc-windows-gnu` | 277 / 215,174 | 10 / 4,949 | **4 kinds**: `IMAGE_REL_AMD64_SECREL (11)` (`111,090` / `0` in DWARF), `IMAGE_REL_AMD64_ADDR64 (1)` (`64,087` / `122`), `IMAGE_REL_AMD64_REL32 (4)` (`35,442` / `4,824`), `IMAGE_REL_AMD64_ADDR32NB (3)` (`4,555` / `3`) |
| `i686-pc-windows-msvc` | 316 / 55,729 | 10 / 5,919 | **5 kinds**: `IMAGE_REL_I386_DIR32 (6)` (`31,739` / `4,376`), `IMAGE_REL_I386_REL32 (20)` (`21,158` / `1,543`), `IMAGE_REL_I386_SECREL (11)` (`2,158` / `0`), `IMAGE_REL_I386_SECTION (10)` (`567` / `0`), `IMAGE_REL_I386_DIR32NB (7)` (`107` / `0`) |
| `aarch64-pc-windows-msvc` | 311 / 73,291 | 10 / 5,700 | **12 kinds**: `IMAGE_REL_ARM64_PAGEBASE_REL21 (4)` (`23,048` / `2,542`), `IMAGE_REL_ARM64_BRANCH26 (3)` (`21,493` / `1,389`), `IMAGE_REL_ARM64_PAGEOFFSET_12A (5)` (`21,365` / `1,475`), `IMAGE_REL_ARM64_ADDR32NB (2)` (`2,704` / `3`), `IMAGE_REL_ARM64_SECREL (8)` (`1,986` / `0`), `IMAGE_REL_ARM64_PAGEOFFSET_12L (6)` (`1,696` / `168`), `IMAGE_REL_ARM64_SECTION (7)` (`566` / `0`), `IMAGE_REL_ARM64_ADDR64 (1)` (`414` / `122`), `IMAGE_REL_ARM64_REL21 (14)` (`12` / `0`), `IMAGE_REL_ARM64_BRANCH19 (12)` (`3` / `1`), `IMAGE_REL_ARM64_SECREL_LOW12A (9)` (`2` / `0`), `IMAGE_REL_ARM64_SECREL_HIGH12A (10)` (`2` / `0`) |

### 6. Synthetic Metadata and Symbol Wrapper Objects (`metadata.rs` & `link.rs`)

`rustc` constructs four kinds of non-LLVM object files directly in Rust via the
`object` crate (`compiler/rustc_codegen_ssa/src/back/metadata.rs:85-285` and
`compiler/rustc_codegen_ssa/src/back/link.rs:2818-2860`):

1. **`lib.rmeta` (inside `.rlib` archives)**: Created by `create_compressed_metadata_file`
   (`metadata.rs:235-285`), which wraps the raw `.rmeta` metadata payload inside an
   `object::write::Object` with section `.rmeta` (or `__DWARF,.rmeta` on Mach-O)
   marked `SHF_EXCLUDE` (`0x80000000`) on ELF and `IMAGE_SCN_LNK_REMOVE` (`0x800`)
   on COFF so native linkers ignore the section while `ar` indexes the exported symbol
   `rust_metadata_<crate_name>_<stable_crate_id>`.
2. **`rmeta.o` (linked into `dylib` / `proc-macro` crates)**: Created by
   `create_wrapper_file` (`metadata.rs:181-225`), placing the compressed `.rmeta`
   bytes into a non-excluded `SectionKind::ReadOnlyData` `.rmeta` section with
   an exported `SymbolSection::Section(section)` symbol `rust_metadata_<crate>_<hash>`
   so downstream `rustc` invocations can read crate metadata directly from a `.so`,
   `.dylib`, or `.dll` without an `.rlib`.
3. **`symbols.o` (`add_linked_symbol_object`, `link.rs:2818-2860`)**: Generated when
   linking `dylib`, `cdylib`, `proc-macro`, or executables that require forced
   symbol references (`__rust_alloc_error_handler_should_panic_v2`, bundled staticlib
   symbols, or `#[used(linker)]` symbols on targets without linker retain flags).
4. **Mandatory `.note.gnu.property` injection (`metadata.rs:129-175`)**:
   `add_gnu_property_note` checks `BinaryFormat::Elf` and injects a 32-byte (ELF64) or
   28-byte (ELF32) `.note.gnu.property` section (`SHT_NOTE`, `SHF_ALLOC`, alignment 8
   or 4) with `GNU_PROPERTY_X86_FEATURE_1_AND (0xc0000002)` = `0x3` (`IBT | SHSTK`) on
   `Architecture::X86_64` / `I386` and `GNU_PROPERTY_AARCH64_FEATURE_1_AND (0xc0000000)` =
   `0x3` (`BTI | PAC`) on `Architecture::Aarch64`. Without this note on synthetic
   objects, `ld.lld` and `ld.bfd` clear CET/BTI/PAC bits on the entire output binary.

## Boundaries

1. **Inline assembly (`asm!`/`global_asm!`) and C/ASM runtime objects**: Pure Rust
   MIR/LLVM IR codegen never emits relaxable `R_X86_64_REX_GOTPCRELX` / `R_386_GOT32X`
   in the 10-crate sample (`0` occurrences), because LLVM's MC relaxation is only
   triggered on specific instruction forms present in C/assembly sources bundled into
   `libbacktrace` / `compiler_builtins` (84 and 82 occurrences in sysroot `.rlib`s).
   User `asm!` blocks can additionally trigger target-specific branch or literal
   relocations outside the pure-Rust codegen subset.
2. **Non-default code models and sanitizer flags**: Passing `-C code-model=large`,
   `-C relocation-model=static`, `-Z sanitizer=address|hwaddress|cfi|kcfi`, or
   `-Z instrument-coverage` introduces additional sections (`__llvm_prf_*`,
   `.ASAN_*`, `.kcfi_traps`) and large-code-model relocations (`R_X86_64_GOT64`,
   `R_X86_64_PLTOFF64`, `R_AARCH64_MOVW_UABS_G0..G3`) not present in default Tier 1 builds.

## Evidence

- **Target specification dump**: `support/tier1_target_specs.json` (complete
  `rustc +1.99.1 --print target-spec-json` across all 8 Tier 1 targets).
- **Full sysroot & 10-crate relocation/section/symbol/COMDAT census**:
  `support/t8_full_census.json` and `support/run_t8_full_census.py` (2,865 sysroot
  `.o` files with 1,584,454 relocations and 80 sample-crate `.o` files with 67,429
  relocations).
- **Targeted multi-feature section & attribute probe**:
  `support/t8_probe_summary.json` and `support/run_t8_probe.py` (`#[used(compiler)]`,
  `#[used(linker)]`, `.init_array` / `__mod_init_func` / `.CRT$XCU`, `linkme_ITEMS`,
  `#[rustc_objc_class]` / `#[rustc_objc_selector]`, `#[thread_local]`,
  `-Zcf-protection=full`, `-Zbranch-protection=bti,pac-ret,leaf`,
  `-Ccontrol-flow-guard=checks`, `-Zehcont-guard`).
- **Pinned `rustc 1.99.1` source citations**:
  - `compiler/rustc_target/src/spec/mod.rs:2849-2999` (`TargetOptions::default()`)
  - `compiler/rustc_codegen_ssa/src/back/metadata.rs:85-285` (`create_object_file`, `add_gnu_property_note`, `create_wrapper_file`, `create_compressed_metadata_file`)
  - `compiler/rustc_codegen_ssa/src/back/link.rs:2818-2860` (`add_linked_symbol_object`)
  - `compiler/rustc_codegen_llvm/src/base.rs:95-190` (`linkage_to_llvm`, `visibility_to_llvm`)
  - `compiler/rustc_codegen_llvm/src/consts.rs:195-360` (`#[thread_local]`, `#[used]`)
  - `compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs:28-92` (`.debug_gdb_scripts`)

## Revalidation

Run `python3 support/run_t8_full_census.py` and `python3 support/run_t8_probe.py`
with `rustc +1.99.1` and the `llvm-tools` component installed for all 8 Tier 1 targets.
Revalidate whenever upgrading the pinned `rustc` or bundled LLVM major version, or
when expanding a verified object encoder/linker's supported relocation table.
