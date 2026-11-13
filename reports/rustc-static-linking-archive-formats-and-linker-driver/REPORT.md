# rustc Static Linking, Archive Formats (.rlib and staticlib), and Linker Driver Protocol Across Tier 1 Targets

## Summary

`rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) manages static archive
construction (`rlib` and `staticlib`), import-library synthesis (`raw-dylib`), and
native linker invocation inside `compiler/rustc_codegen_ssa/src/back/{archive,link,linker,rmeta_link,symbol_edit,symbol_export}.rs`:

1. **In-process archive synthesis via `ar_archive_writer 0.5.1`**: `ArArchiveBuilder`
   (`compiler/rustc_codegen_ssa/src/back/archive.rs:145-410`) writes GNU (`ArchiveKind::Gnu`),
   BSD/Darwin (`ArchiveKind::Darwin64`), and Windows COFF (`ArchiveKind::Coff`) `.rlib`
   and `.a`/`.lib` archives directly in Rust without invoking system `ar` or `ranlib`,
   supporting thin archives (`!<thin>\n` via `-Z packed-bundled-libs=no`) and
   deterministic zeroed timestamps/UIDs/GIDs. Every `.rlib` embeds `lib.rmeta` and a
   second object `lib.rmeta-link` (`compiler/rustc_codegen_ssa/src/back/rmeta_link.rs:1-132`,
   section `.rmeta-link`) recording the exact list of `rust_object_files` and bundled
   `native_lib_filenames` inside the archive.
2. **Self-contained `rust-lld` dispatch on all three Linux Tier 1 targets**: In
   `rustc 1.99.1`, `x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, and
   `aarch64-unknown-linux-gnu` all default to `linker-flavor: gnu-lld-cc` and
   `link-self-contained: {"components": ["linker"]}`, causing `add_lld_args`
   (`compiler/rustc_codegen_ssa/src/back/link.rs:3212-3288`) to pass
   `-B<sysroot>/lib/rustlib/<host>/bin/gcc-ld` and `-fuse-ld=lld` to `cc`, which
   executes the `lld-wrapper` binary `gcc-ld/ld.lld` and routes into bundled
   `bin/rust-lld -flavor gnu` (LLVM `22.1.1`).
3. **In-process vs external `raw-dylib` synthesis**: `#[link(name = "...", kind = "raw-dylib")]`
   synthesizes COFF Short Import Libraries in-process via
   `ar_archive_writer::write_import_library` (`archive.rs:76-142`) on `*-pc-windows-msvc`
   (including `bcryptprimitives.dll` and `api-ms-win-core-synch-l1-2-0.dll` bundled inside
   prebuilt `libstd-*.rlib`) and synthesizes in-memory ELF `ET_DYN` `.so` stubs via
   `create_elf_raw_dylib_stub` (`compiler/rustc_codegen_ssa/src/back/link/raw_dylib.rs:218-489`)
   on ELF targets, but falls back to invoking external `*-w64-mingw32-dlltool` on
   `x86_64-pc-windows-gnu` (`archive.rs:90-96`) when linking with GNU `ld.bfd`.

## Applicability

- **Pinned toolchain**: `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
  `ar_archive_writer 0.5.1`, `object 0.37.3`, bundled `rust-lld` `22.1.1`.
- **Target matrix**: All eight Rust Tier 1 targets (`x86_64-unknown-linux-gnu`,
  `i686-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`,
  `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `i686-pc-windows-msvc`,
  `aarch64-pc-windows-msvc`).

## Findings

### 1. Archive Formats (`.rlib`, `staticlib`), `lib.rmeta`, and `lib.rmeta-link`

`compiler/rustc_codegen_ssa/src/back/archive.rs:254-305` selects the `ar_archive_writer::ArchiveKind`
from the target's object format (`sess.target.binary_format`):

| Target Family | `ArchiveKind` | Magic & Header Format | Symbol Table Index Member(s) | String Table Member |
| :--- | :--- | :--- | :--- | :--- |
| ELF (`x86_64`, `i686`, `aarch64-unknown-linux-gnu`) | `ArchiveKind::Gnu` (or `Gnu64` when $>4\text{ GiB}$) | `!<arch>\n` (or `!<thin>\n`), 60-byte ASCII headers | `/` (big-endian 32-bit count + offsets + null-terminated symbol names; `/SYM64/` for 64-bit offsets) | `//` (extended filenames $>15$ bytes, `/offset` references) |
| Mach-O (`aarch64-apple-darwin`) | `ArchiveKind::Darwin64` (or `Bsd`) | `!<arch>\n`, `#1/<len>` inline filename prefix | `__.SYMDEF` or `__.SYMDEF_64` (8-byte `ranlib` structs + string pool; sorted if `__.SYMDEF SORTED`) | Inline `#1/<len>` prepended to member payload |
| Windows (`*-pc-windows-msvc`, `x86_64-pc-windows-gnu`) | `ArchiveKind::Coff` (on MSVC) / `ArchiveKind::Gnu` (on MinGW) | `!<arch>\n`, 60-byte ASCII headers | First `/` member (big-endian 32-bit offsets) + Second `/` member (COFF little-endian sorted member table + 16-bit indices + lexical symbol table) | `//` (long member names) |

#### Internal Layout of a `rustc 1.99.1` `.rlib` Archive

Inspecting the prebuilt `rustc 1.99.1` sysroot `libstd-*.rlib` and `libcore-*.rlib`
archives (`compiler/rustc_codegen_ssa/src/back/link.rs:942-1085`, `link_rlib`) shows
that every `.rlib` contains up to four member classes:

1. **Codegen unit object files (`<crate>-<hash>.<cgu>.rcgu.o`)**: One `.o` file per
   codegen unit (plus `allocator_shim.rcgu.o` when the crate defines or requires an
   allocator shim).
2. **`lib.rmeta` (`METADATA_FILENAME`)**: Compressed crate metadata wrapped in an
   excluded `.rmeta` object section (`SHF_EXCLUDE` on ELF, `IMAGE_SCN_LNK_REMOVE` on
   COFF, `__DWARF,.rmeta` with `S_ATTR_DEBUG` on Mach-O) exporting
   `rust_metadata_<crate>_<hash>`. Only emitted when `-Zembed-metadata=yes` (default).
3. **`lib.rmeta-link` (`RMETA_LINK_FILENAME`, `compiler/rustc_codegen_ssa/src/back/rmeta_link.rs:1-132`)**:
   An excluded object file containing a `.rmeta-link` section (`__DWARF,.rmeta-link`
   on Mach-O) that serializes `RmetaLink { rust_object_files: Vec<String>, native_lib_filenames: Vec<String> }`.
   When `-Z packed-bundled-libs=no` is enabled, `rustc` extracts or references `.rcgu.o`
   and bundled native libraries using `lib.rmeta-link` so native linkers do not scan
   non-object metadata payloads.
4. **Bundled native static libraries (`-l static=+bundle,...`) and synthesized
   `raw-dylib` import libraries**: On `*-pc-windows-msvc` and `x86_64-pc-windows-gnu`,
   `libstd-*.rlib` directly embeds COFF short import stubs (`bcryptprimitives.dll_imports_indirect.lib`
   members `bcryptprimitives.dll`, `api-ms-win-core-synch-l1-2-0.dll`, etc.) generated
   from `#[link(name = "...", kind = "raw-dylib")]`.

#### `staticlib` Symbol Hiding and Renaming (`symbol_edit.rs`)

When building `--crate-type=staticlib`, `compiler/rustc_codegen_ssa/src/back/symbol_edit.rs:1-300`
supports rewriting every archive member's symbol table in memory via the `object` crate
before writing the output `.a` / `.lib`:

- `-Z staticlib-hide-internal-symbols=yes`: Downgrades all defined global symbols that
  are **not** in the crate's `exported_symbols` list from global binding to hidden/private
  visibility (`STV_HIDDEN` on ELF, `N_PEXT` on Mach-O; rejected with a diagnostic on
  COFF because COFF lacks a per-symbol hidden visibility bit on `IMAGE_SYM_CLASS_EXTERNAL`).
- `-Z staticlib-rename-internal-symbols=yes`: Rewrites non-exported defined and undefined
  symbol names across all member `.o` files by appending a deterministic crate-specific
  disambiguator suffix, preventing duplicate-symbol collisions when two Rust `staticlib`
  archives are linked into the same C/C++ executable.

### 2. Linker Driver Flavors, Self-Contained `rust-lld`, and Command-Line Order

`compiler/rustc_codegen_ssa/src/back/link.rs:1440-1890` (`link_natively` and
`linker_with_args`) and `compiler/rustc_codegen_ssa/src/back/linker.rs` construct the
native linker invocation for `bin`, `dylib`, `cdylib`, `proc-macro`, and `test` outputs.

#### Bundled `rust-lld` and the `gcc-ld/` Wrapper Protocol

Every `rustc 1.99.1` host toolchain distributes two sets of LLD binaries under
`<sysroot>/lib/rustlib/<host>/bin/`:

- `bin/rust-lld`: Multi-flavor LLVM `22.1.1` linker binary requiring `-flavor gnu|darwin|link|wasm`
  as its first argument (or inferring the flavor from `argv[0]`).
- `bin/gcc-ld/{ld.lld,ld64.lld,lld-link,wasm-ld}`: Identical `lld-wrapper` binaries
  that locate `../rust-lld` and exec it with the flavor implied by their filename.
  When `LinkerFlavor` is a CC wrapper (`gnu-lld-cc` or `darwin-lld-cc`), `add_lld_args`
  (`link.rs:3212-3288`) passes `-B<sysroot>/lib/rustlib/<host>/bin/gcc-ld` and
  `-fuse-ld=lld` to `cc`, causing `gcc` or `clang` to invoke `gcc-ld/ld.lld` (or
  `gcc-ld/ld64.lld`).

#### Tier 1 Default Linker Flavor & Driver Matrix (`support/t9_link_args_matrix.json`)

| Target | Default `linker-flavor` | Default `linker` | `link-self-contained` | Pre-Link CRT Objects (`bin`) | Key Flags Passed by `rustc` (`bin` / `cdylib`) | Post-Link CRT / Default Libs |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `gnu-lld-cc` | `cc` (+ `gcc-ld/ld.lld`) | `{"components": ["linker"]}` | *(managed by `cc`)* | `-m64 -Wl,--eh-frame-hdr -Wl,-z,noexecstack -Wl,-B.../gcc-ld -fuse-ld=lld -Wl,--as-needed -Wl,-z,relro,-z,now -pie` (`-shared` + `-Wl,--version-script=...` for `cdylib`) | `-lgcc_s -lutil -lrt -lpthread -lm -ldl -lc` |
| `i686-unknown-linux-gnu` | `gnu-lld-cc` | `cc` (+ `gcc-ld/ld.lld`) | `{"components": ["linker"]}` | *(managed by `cc`)* | `-m32 -Wl,--eh-frame-hdr -Wl,-z,noexecstack -Wl,-B.../gcc-ld -fuse-ld=lld -Wl,--as-needed -Wl,-z,relro,-z,now -pie` | `-lgcc_s -lutil -lrt -lpthread -lm -ldl -lc` |
| `aarch64-unknown-linux-gnu` | `gnu-lld-cc` | `cc` (+ `gcc-ld/ld.lld`) | `{"components": ["linker"]}` | *(managed by `cc`)* | `-Wl,--eh-frame-hdr -Wl,-z,noexecstack -Wl,-B.../gcc-ld -fuse-ld=lld -Wl,--as-needed -Wl,-z,relro,-z,now -pie` | `-lgcc_s -lutil -lrt -lpthread -lm -ldl -lc` |
| `aarch64-apple-darwin` | `darwin-cc` | `cc` | `off` | *(none)* | `-arch arm64 -mmacosx-version-min=11.0.0 -Wl,-dead_strip` (`-dynamiclib -Wl,-dylib -Wl,-exported_symbols_list,...` for `cdylib`) | `-lSystem -lc -lm` |
| `x86_64-pc-windows-msvc` | `msvc` | `link.exe` (or `rust-lld -flavor link`) | `off` | *(none)* | `/NOLOGO /LARGEADDRESSAWARE /SAFESEH:NO /NXCOMPAT /DYNAMICBASE /HIGHENTROPYVA /MANIFEST:EMBED /SUBSYSTEM:... /ENTRY:mainCRTStartup` (`/DLL /DEF:...` for `cdylib`) | `windows.0.52.0.lib kernel32.lib advapi32.lib ntdll.lib userenv.lib ws2_32.lib dbghelp.lib msvcrt.lib /defaultlib:msvcrt` |
| `x86_64-pc-windows-gnu` | `gnu-cc` | `x86_64-w64-mingw32-gcc` (or `ld.bfd`) | `true` (CRT objects in sysroot) | `crt2.o` (`dllcrt2.o` for DLL), `rsbegin.o` | `-fno-use-linker-plugin -Wl,--dynamicbase -Wl,--disable-auto-image-base -Wl,--large-address-aware -Wl,--high-entropy-va` (`-shared -Wl,--out-implib=...` for `cdylib`) | `-lwindows.0.52.0 -lmingwex -lmingw32 -lgcc -lmsvcrt -luser32 -lkernel32` + `rsend.o` |
| `i686-pc-windows-msvc` | `msvc` | `link.exe` | `off` | *(none)* | `/NOLOGO /LARGEADDRESSAWARE /SAFESEH /NXCOMPAT /DYNAMICBASE /MANIFEST:EMBED` | `windows.0.52.0.lib ... msvcrt.lib` |
| `aarch64-pc-windows-msvc` | `msvc` | `link.exe` | `off` | *(none)* | `/NOLOGO /LARGEADDRESSAWARE /NXCOMPAT /DYNAMICBASE /HIGHENTROPYVA /MANIFEST:EMBED` | `windows.0.52.0.lib ... msvcrt.lib` |

#### Canonical Linker Argument Ordering (`linker_with_args`, `link.rs:2995-3490`)

`rustc` emits linker arguments in a strict 12-stage topological sequence so single-pass
and group-aware linkers resolve symbols predictably:

1. **Flavor/Architecture Prefix & Self-Contained CRT Startup**: `-m64`/`-m32`/`-arch arm64`,
   `-Wl,--eh-frame-hdr`, `-Wl,-z,noexecstack`, `-B<sysroot>/bin/gcc-ld -fuse-ld=lld`,
   and pre-link CRT objects (`crt2.o`/`dllcrt2.o`, `rsbegin.o`).
2. **Primary Crate Codegen Objects & Metadata Wrapper**: `<crate>.<cgu>.rcgu.o`,
   `allocator_shim.rcgu.o`, `rmeta.o` (for `dylib`/`proc-macro`), and `symbols.o`.
3. **Output Mode & Security Hardening**: `-pie` / `-shared` / `-dynamiclib` / `/DLL`,
   `-Wl,-z,relro,-z,now`, `/NXCOMPAT /DYNAMICBASE /HIGHENTROPYVA`.
4. **Dead-Code Elimination & Optimization Flags**: `-Wl,--gc-sections` (on ELF when
   enabled), `-Wl,-dead_strip` (on Mach-O), `/OPT:REF,ICF` or `/OPT:REF,NOICF` (on MSVC).
5. **Symbol Export Restriction Script**:
   - ELF (`GccLinker::export_symbols`, `linker.rs:765-835`): Passes
     `-Wl,--version-script=<tmp>/list` containing `{ global: sym1; sym2; local: *; };`
     (or `-Wl,--dynamic-list=<tmp>/list` for executables exporting symbols to plugins).
   - Mach-O (`linker.rs:836-865`): Passes `-Wl,-exported_symbols_list,<tmp>/list` with
     `_`-prefixed symbols.
   - Windows (`MsvcLinker::export_symbols`, `linker.rs:1195-1245`): Passes `/DEF:<tmp>/list.def`
     containing `LIBRARY ... EXPORTS sym1 sym2`, and on `x86_64-pc-windows-gnu` also passes
     `<tmp>/list.def` directly alongside `-Wl,--out-implib=...`.
6. **Local Native Libraries andTopological Upstream `.rlib` Chain**:
   `link_local_crate_native_libs_and_dependent_crate_libs` (`link.rs:3495-3890`) walks
   the dependency DAG in topological order (dependents before dependencies), wrapping
   `.rlib` groups in `-Wl,-Bstatic ... -Wl,-Bdynamic` on ELF and emitting
   `-Wl,--whole-archive <lib> -Wl,--no-whole-archive` (`-force_load` on Mach-O,
   `/WHOLEARCHIVE:<lib>` on MSVC) when `+whole-archive` is requested.
7. **Compiler-Builtins & Unwind Runtime**: `libcompiler_builtins-<hash>.rlib` (placed
   after all Rust `.rlib`s so intrinsics like `__multi3`, `memcpy`, and outline atomics
   satisfy any unresolved references from `core`/`std`) and `libunwind-<hash>.rlib`.
8. **System Dynamic Libraries (`#[link(kind = "dylib")]`)**: `-Bdynamic -l...` on ELF,
   `-lSystem` on Mach-O, `.lib` import libraries and `/defaultlib:msvcrt` on MSVC.
9. **Post-Link CRT Objects**: `rsend.o` on `x86_64-pc-windows-gnu`.

> **Note on Gold Linker Deprecation (`link.rs:1636-1655`)**: `warn_if_linked_with_gold`
> explicitly warns whenever `ld.gold` is detected (`warning: gold linker is deprecated
> and will not be supported by rustc in the future`).

### 3. `raw-dylib` Import Library and Stub Shared Object Synthesis

`rustc` allows linking against external DLLs and shared objects without a vendor SDK
import library via `#[link(name = "...", kind = "raw-dylib")]`:

1. **Windows MSVC & `windows-gnullvm` (`compiler/rustc_codegen_ssa/src/back/archive.rs:76-142`)**:
   `create_dll_import_lib` maps every foreign symbol (`PeImportType`) to an
   `ar_archive_writer::COFFShortExport` (handling `@N` stdcall/fastcall byte suffixes,
   `#[link_ordinal(N)]`, `import_name_type`, and `data: true` for statics) and calls
   `ar_archive_writer::write_import_library` in-process to write a COFF Short Import
   Library (`<dll>_imports_indirect.lib`).
2. **Windows MinGW (`x86_64-pc-windows-gnu`, `archive.rs:90-96` and `455-560`)**:
   Because GNU `ld.bfd` has longstanding bugs linking LLVM-style short import libraries
   (failing to synthesize thunks or mistaking import headers for regular objects),
   `create_mingw_dll_import_lib` writes a temporary `.def` file and invokes
   `x86_64-w64-mingw32-dlltool` (`--temp-prefix`, `--output-lib`, `--input-def`).
   When `rust-lld` / `lld` is used instead (`windows-gnullvm`), `rustc` uses the
   in-process `ar_archive_writer` path.
3. **ELF Targets (`compiler/rustc_codegen_ssa/src/back/link/raw_dylib.rs:218-489`)**:
   `create_raw_dylib_elf_stub_shared_objects` calls `create_elf_raw_dylib_stub` to
   build a minimal in-memory `ET_DYN` ELF shared object (`<soname>.so`) using
   `object::write::elf::Writer`:
   - Emits `.dynsym`, `.dynstr`, `.hash`, `.dynamic` (with `DT_SONAME` set to the
     library name), and—whenever any symbol specifies an `@version` suffix—`.gnu.version`
     (`SHT_GNU_versym`) and `.gnu.version_d` (`SHT_GNU_verdef`) tables.
   - All symbols are emitted as `SHN_ABS` (`st_shndx = 1` / dummy section) with
     `STB_GLOBAL` (or `STB_WEAK`) binding and `STT_FUNC` / `STT_OBJECT` type so
     `ld.lld` / `ld.bfd` records the `DT_NEEDED` entry and symbol version bindings
     at link time without needing the runtime `.so` on disk.

### 4. Linker Semantics Required by Rust Programs

Any linker (including a verified linker) consuming `rustc` outputs must uphold six
behavioral invariants:

1. **Section Garbage Collection (`--gc-sections` / `-dead_strip` / `/OPT:REF`) vs
   Retained Roots**:
   - On ELF, `--gc-sections` discards unreferenced `.text.*`/`.data.*`/`.rodata.*`
     sections unless the section carries `SHF_GNU_RETAIN` (`0x00200000`, emitted for
     `#[used(linker)]`), is type `SHT_INIT_ARRAY`/`SHT_FINI_ARRAY`/`SHT_NOTE`, or is
     reachable from `_start` / exported dynamic symbols.
   - On Mach-O, `-dead_strip` discards unreferenced subsection atoms unless marked
     `S_ATTR_NO_DEAD_STRIP` (`0x10000000`, e.g., `__DATA,__objc_*`) or `N_NO_DEAD_STRIP`
     (`0x0020`, `#[used(linker)]`).
   - On COFF, `/OPT:REF` discards unreferenced COMDAT sections unless rooted by `/ENTRY`,
     `/EXPORT`, or `.drectve` `/INCLUDE:<sym>`, and must traverse
     `IMAGE_COMDAT_SELECT_ASSOCIATIVE` (`5`) edges from `.text` to `.pdata`/`.xdata`
     (keep the unwind section iff its associated `.text` section is kept).
2. **Identical Code Folding (`/OPT:ICF` vs `/OPT:NOICF` and `.llvm_addrsig`)**:
   In `compiler/rustc_codegen_ssa/src/back/linker.rs:1170-1190`, `MsvcLinker::optimize`
   passes `/OPT:REF,ICF` at `-C opt-level=2|3` and `/OPT:REF,NOICF` at `-C opt-level=s|z`
   or when `-C link-dead-code` is set. Because Rust guarantees distinct function pointer
   addresses Only when a function's address is taken (or via `.llvm_addrsig` safe-ICF in
   `lld`), `lld-link` and `ld.lld --icf=safe` consult `.llvm_addrsig` (`SHT_LLVM_ADDRSIG`)
   to avoid folding address-significant functions or read-only statics.
3. **Auto-Synthesized Section Boundary Symbols (`__start_<sec>` / `__stop_<sec>`)**:
   For any ELF section whose name is a valid C identifier (e.g., `linkme_ITEMS`), the
   linker must synthesize `SHF_ALLOC` boundary symbols `__start_<sec>` (start VA) and
   `__stop_<sec>` (end VA) with `STV_HIDDEN` or `STV_DEFAULT` visibility when referenced
   by an undefined symbol; on Mach-O, `ld64`/`ld64.lld` synthesizes
   `section$start$<seg>$<sect>` and `section$end$<seg>$<sect>`.
4. **Weak Symbol Resolution (`#[linkage = "extern_weak"]`)**:
   An unresolved `STB_WEAK` (`ELF`), `N_WEAK_REF` (`Mach-O`), or
   `IMAGE_SYM_CLASS_WEAK_EXTERNAL` (`COFF`) reference must resolve to VA `0` (null
   pointer) without causing an undefined-symbol error; `libstd` relies on this for
   `__pthread_key_create`, `getrandom`, `statx`, and `__cxa_thread_atexit_impl`.
5. **Range-Extension Thunks / Branch Veneers (`AArch64` $\pm 128\text{ MiB}$)**:
   Because `R_AARCH64_CALL26` and `R_AARCH64_JUMP26` (`ARM64_RELOC_BRANCH26`,
   `IMAGE_REL_ARM64_BRANCH26`) have a signed 26-bit instruction offset ($\pm 128\text{ MiB}$),
   the linker must synthesize an `adrp x16, <target> + add x16, x16, :lo12:<target> + br x16`
   veneer whenever a `.text` section exceeds $128\text{ MiB}$ (`x16`/`IP0` is architectural
   intra-procedure-call scratch register).
6. **AArch64 Cortex-A53 Errata Mitigation (`843419` and `835769`)**:
   `ld.lld` and `ld.bfd` implement `--fix-cortex-a53-843419` (default-enabled in
    several distros and Android/embedded toolchains), scanning the final 4 KiB page
   offsets (`0xff8` / `0xffc`) of `adrp` followed by load/store sequences and patching
   problematic instructions with a branch to a linker-generated veneer.

## Boundaries

1. **Linker-plugin LTO (`-Clinker-plugin-lto`)**: Requires the external linker to load
   `LLVMgold.so` or run `lld` bitcode merging over `.llvmbc` sections. On Windows with
   `-C prefer-dynamic`, `rustc` explicitly rejects `-C linker-plugin-lto`
   (`compiler/rustc_session/src/session.rs:1419-1424`) because ThinLTO bitcode merging
   cannot synthesize the `__imp_` data stubs required by `.rlib` consumers.
2. **External `dlltool` requirement on `x86_64-pc-windows-gnu` with `ld.bfd`**:
   While `*-pc-windows-msvc` and ELF targets synthesize `raw-dylib` stubs purely
   in-process, `x86_64-pc-windows-gnu` still shells out to `x86_64-w64-mingw32-dlltool`
   whenever `raw-dylib` is compiled in user crates.

## Evidence

- **Complete 8-target $\times$ 4-crate-type `--print link-args` matrix**:
  `support/t9_link_args_matrix.json` and `support/run_t9_link_args.py` (`bin`, `cdylib`,
  `dylib`, and `proc-macro` across all 8 Tier 1 targets).
- **Pinned `rustc 1.99.1` source citations**:
  - `compiler/rustc_codegen_ssa/src/back/archive.rs:76-410` (`create_dll_import_lib`, `create_mingw_dll_import_lib`, `ArArchiveBuilder`)
  - `compiler/rustc_codegen_ssa/src/back/rmeta_link.rs:1-132` (`RmetaLink`, `.rmeta-link`)
  - `compiler/rustc_codegen_ssa/src/back/symbol_edit.rs:1-300` (`apply_edits`)
  - `compiler/rustc_codegen_ssa/src/back/link.rs:942-3890` (`link_rlib`, `link_staticlib`, `link_natively`, `add_lld_args`, `linker_with_args`)
  - `compiler/rustc_codegen_ssa/src/back/linker.rs:765-1245` (`GccLinker::export_symbols`, `MsvcLinker::export_symbols`, `/OPT:REF,ICF`)
  - `compiler/rustc_codegen_ssa/src/back/link/raw_dylib.rs:218-489` (`create_elf_raw_dylib_stub`)

## Revalidation

Run `python3 support/run_t9_link_args.py` with `rustc +1.99.1` and all 8 Tier 1
`rust-std` targets installed to regenerate `support/t9_link_args_matrix.json` and verify
any changes in default `linker-flavor`, `link-self-contained`, CRT object ordering, or
export-script generation.
