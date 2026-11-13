# rustc Dynamic Linking, Runtime Loader Contracts, Proc-Macro Loading, and Mach-O Code Signing Across Tier 1 Targets

## Summary

Dynamic linking in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) spans
four distinct runtime contracts—ELF `ld-linux.so`, Mach-O `dyld` (with Apple Silicon
kernel code-signing enforcement), Windows PE `ntdll.dll` loader (`LdrLoadDll`), and
`rustc`'s own host `proc-macro` loader (`compiler/rustc_metadata/src/host_dylib.rs`):

1. **Full RELRO and PLT-less indirect calls by default on Linux**: All three Linux
   Tier 1 targets set `relro-level: full`, causing `rustc` to pass `-Wl,-z,relro,-z,now`
   and emit `PT_GNU_RELRO` with `DT_FLAGS = BIND_NOW` (`0x8`) and `DT_FLAGS_1 = NOW | PIE`
   (`0x8000001`). On `x86_64-unknown-linux-gnu` (`plt-by-default: false`), `rustc` sets
   LLVM module flag `"RtLibUseGOT" = 1`, replacing lazy PLT jumps with direct indirect
   calls through the eagerly bound GOT (`call *sym@GOTPCREL(%rip)`).
2. **Windows `dllimport` ambiguity and compiler-synthesized `__imp_` data stubs**:
   Because an upstream `.rlib` is compiled before `rustc` knows whether a downstream
   crate will link it statically or via a `dylib` (`-C prefer-dynamic`),
   `compiler/rustc_codegen_llvm/src/consts.rs:421-458` marks cross-crate Rust static
   references on Windows as `dllimport`, and `create_msvc_imps`
   (`compiler/rustc_codegen_llvm/src/back/write.rs:1318-1365`) emits a companion
   `\x01__imp_<sym> = &<sym>` (`\x01__imp__<sym>` on `i686`) pointer global for every
   externally visible static definition so static linking resolves `__imp_` references
   locally without a DLL import library.
3. **Mandatory Mach-O `arm64` ad-hoc code signing (`LC_CODE_SIGNATURE`)**: On
   `aarch64-apple-darwin`, the XNU kernel kills any executable or `.dylib` (`SIGKILL`,
   `EXC_BAD_ACCESS (CODESIGNING)`) that lacks a valid `LC_CODE_SIGNATURE` load command
   (`0x1d`) with `CS_ADHOC | CS_LINKER_SIGNED` (`0x20002`) and SHA-256 4,096-byte page
   hashes. Both Apple `ld` and bundled `rust-lld -flavor darwin` (`ld64.lld`) synthesize
   this signature automatically at link time, and `rustc` avoids any post-link in-place
   modification of Mach-O binaries that would invalidate page hashes.

## Applicability

- **Pinned toolchain**: `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
  bundled LLVM `22.1.1`.
- **Target matrix**: All eight Rust Tier 1 targets and all dynamically linked crate types
  (`bin`, `dylib`, `cdylib`, `proc-macro`).

## Findings

### 1. Loader Hardening, PLT/GOT Dispatch, and Dynamic Tables Across Tier 1 `libstd`

Inspecting the prebuilt `rustc 1.99.1` shared libraries (`libstd-d5b8ce5bd730e27c.so`,
`libstd-0a5ef625bc21ff5e.dylib`, `std-6e5eb0ca82d4d25a.dll`, etc. in
`support/t10_std_dylibs.json`) and target specifications (`support/tier1_target_specs.json`)
establishes the exact loader flags and dynamic dependencies per target:

| Target | Prebuilt `std` Shared Library | `plt-by-default` | RELRO / Const Data Protection | ASLR / CFI / NX Flags | Runtime `DT_NEEDED` / Imported Libraries |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `libstd-d5b8ce5bd730e27c.so` (`ELF64`) | `false` (`RtLibUseGOT`) | `PT_GNU_RELRO` + `DT_FLAGS = BIND_NOW` (`full`) | `PIE`, `PT_GNU_STACK` (`RW-`), `.note.gnu.property` (`IBT \| SHSTK`) | `libc.so.6`, `ld-linux-x86-64.so.2`, `libgcc_s.so.1`, `libm.so.6`, `libpthread.so.0`, `libdl.so.2`, `librt.so.1` |
| `i686-unknown-linux-gnu` | `libstd-aa15dc21fc33c18c.so` (`ELF32`) | `true` (`R_386_PLT32`) | `PT_GNU_RELRO` + `DT_FLAGS = BIND_NOW` (`full`) | `PIE`, `PT_GNU_STACK` (`RW-`) | `libc.so.6`, `ld-linux.so.2`, `libgcc_s.so.1`, `libm.so.6`, `libpthread.so.0`, `libdl.so.2`, `librt.so.1` |
| `aarch64-unknown-linux-gnu` | `libstd-0a5ae4a7c83e4fa1.so` (`ELF64`) | `true` (`R_AARCH64_CALL26`) | `PT_GNU_RELRO` + `DT_FLAGS = BIND_NOW` (`full`) | `PIE`, `PT_GNU_STACK` (`RW-`), `.note.gnu.property` (`BTI \| PAC`) | `libc.so.6`, `ld-linux-aarch64.so.1`, `libgcc_s.so.1`, `libm.so.6`, `libpthread.so.0`, `libdl.so.2`, `librt.so.1` |
| `aarch64-apple-darwin` | `libstd-0a5ef625bc21ff5e.dylib` (`Mach-O arm64`) | `true` (`__TEXT,__stubs`) | `__DATA_CONST` (`__got`, `__const`, `SG_READ_ONLY = 0x10`) | `MH_PIE`, `MH_TWOLEVEL` (`0x80`), `MH_NO_REEXPORTED_DYLIBS`, `LC_CODE_SIGNATURE` | `/usr/lib/libSystem.B.dylib` (`LC_ID_DYLIB = @rpath/libstd-0a5ef625bc21ff5e.dylib`) |
| `x86_64-pc-windows-msvc` | `std-6e5eb0ca82d4d25a.dll` (`PE32+ AMD64`) | `false` (`__imp_` IAT) | Read-only `.rdata` (IAT placed in `.rdata`) | `HIGH_ENTROPY_VA`, `DYNAMIC_BASE`, `NX_COMPAT` | `KERNEL32.dll`, `ntdll.dll`, `ADVAPI32.dll`, `USERENV.dll`, `WS2_32.dll`, `bcryptprimitives.dll`, `api-ms-win-core-synch-l1-2-0.dll`, `VCRUNTIME140.dll`, `VCRUNTIME140_1.dll`, `api-ms-win-crt-*.dll` |
| `x86_64-pc-windows-gnu` | `std-ccdc6db25525003a.dll` (`PE32+ AMD64`) | `false` (`__imp_` IAT) | Read-only `.rdata` | `HIGH_ENTROPY_VA`, `DYNAMIC_BASE`, `NX_COMPAT` | `KERNEL32.dll`, `ntdll.dll`, `ADVAPI32.dll`, `USERENV.dll`, `WS2_32.dll`, `bcryptprimitives.dll`, `api-ms-win-core-synch-l1-2-0.dll`, `msvcrt.dll` |
| `i686-pc-windows-msvc` | `std-2f3cd61b82bf79cf.dll` (`PE32 i386`) | `true` | Read-only `.rdata`, `/SAFESEH` | `DYNAMIC_BASE`, `NX_COMPAT`, `LARGE_ADDRESS_AWARE` | `KERNEL32.dll`, `ntdll.dll`, `ADVAPI32.dll`, `USERENV.dll`, `WS2_32.dll`, `bcryptprimitives.dll`, `api-ms-win-core-synch-l1-2-0.dll`, `VCRUNTIME140.dll`, `api-ms-win-crt-*.dll` |
| `aarch64-pc-windows-msvc` | `std-d2f6bc9ffdded061.dll` (`PE32+ ARM64`) | `true` | Read-only `.rdata` | `HIGH_ENTROPY_VA`, `DYNAMIC_BASE`, `NX_COMPAT` | `KERNEL32.dll`, `ntdll.dll`, `ADVAPI32.dll`, `USERENV.dll`, `WS2_32.dll`, `bcryptprimitives.dll`, `api-ms-win-core-synch-l1-2-0.dll`, `VCRUNTIME140.dll`, `api-ms-win-crt-*.dll` |

#### Symbol Preemption vs `assume_dso_local`

Unlike C/C++ shared libraries compiled with `-fPIC` on ELF (which allow symbol
interposition of all global definitions unless `-fno-semantic-interposition` or
`-Bsymbolic` is passed), `rustc` calls `cx.assume_dso_local(llval, true)`
(`compiler/rustc_codegen_llvm/src/callee.rs:153` and `base.rs:195-245`) on local and
hidden definitions and marks non-exported symbols `STV_HIDDEN`. Consequently, intra-DUs
and intra-binary references use direct PC-relative addressing (`R_X86_64_PC32`,
`R_AARCH64_ADR_PREL_PG_HI21`) rather than GOT indirection, and only externally
imported symbols or dynamically exported `dylib` APIs traverse the GOT/PLT.

### 2. `dylib` vs `cdylib` Symbol Export Levels (`symbol_export.rs`)

`compiler/rustc_codegen_ssa/src/back/symbol_export.rs:1-450` partitions exported
symbols by `SymbolExportLevel`:

1. **`SymbolExportLevel::C` (`cdylib` and `bin` with exported symbols)**:
   Exports only user-designated C ABI entry points—items carrying `#[no_mangle]`,
   `#[export_name = "..."]`, or `#[rustc_std_internal_symbol]`. All Rust-ABI functions,
   generics, vtables, and upstream `.rlib` dependencies are localized (`local: *;` in
   the ELF version script, omitted from Mach-O `-exported_symbols_list`, and omitted
   from Windows `.def`).
2. **`SymbolExportLevel::Rust` (`dylib` and `proc-macro`)**:
   Exports `SymbolExportLevel::C` plus all reachable public Rust items, trait impl
   methods, drop glues, static variables, and shared monomorphizations (`-Zshare-generics=yes`),
   plus `rust_metadata_<crate>_<hash>` from `rmeta.o`.
3. **Thread-Local Storage (`#[thread_local]`) Export Shims on Windows/macOS**:
   When a `dylib` exports a `#[thread_local]` static on a target where `has_thread_local`
   is false or DLL boundaries cannot directly import `.tls$` offsets (`symbol_export.rs:215-260`),
   `rustc` synthesizes and exports a wrapper function `__rust_tls_shim_<symbol>` that
   returns the thread-local address across the DLL boundary.

### 3. Windows `dllimport` and Compiler-Synthesized `__imp_` Stubs

Windows PE/COFF distinguishes direct static symbol references (`call foo` / `mov rax, [BAR]`)
from DLL Import Address Table (IAT) references (`call [__imp_foo]` / `mov rax, [__imp_BAR]`
followed by dereference):

1. **Function calls vs Static data**: If code compiled without `dllimport` calls a
   function `foo` that turns out to reside in a DLL, `link.exe` and `lld-link`
   automatically resolve `foo` to a 6-byte indirect jump thunk (`jmp qword ptr [__imp_foo]`)
   from the DLL's import library. However, for **static data** (`static BAR: u32`), the
   instruction `lea rax, [rip + BAR]` cannot be fixed up by the linker if `BAR` resides
   in another DLL at an unknown runtime base address.
2. **Always-`dllimport` cross-crate statics (`compiler/rustc_codegen_llvm/src/consts.rs:421-458`)**:
   Because `rustc` compiles `.rlib` crates before knowing whether downstream crates will
   link them statically or dynamically (`-C prefer-dynamic`), `consts.rs:442-457` marks
   every reference to an external Rust crate's `static` item (and externally implementable
   static items) with LLVM `DLLImportStorageClass`, generating loads through `__imp_<sym>`
   (or `__imp__<sym>` on `i686`). For `extern` native library functions, `callee.rs:145-151`
   marks them `dllimport` on MSVC (`!matches!(tcx.sess.target.env, Env::Gnu | Env::Uclibc)`),
   whereas MinGW relies on GNU `ld` / `lld` auto-import and jump thunks.
3. **`create_msvc_imps` (`compiler/rustc_codegen_llvm/src/back/write.rs:1318-1365`)**:
   Whenever `cgcx.msvc_imps_needed` is true (`tcx.sess.target.is_like_windows && (lto == Thin || crate_types.contains(Rlib)) && !linker_plugin_lto`,
   `compiler/rustc_codegen_ssa/src/back/write.rs:2306-2315`), `create_msvc_imps` iterates
   over every externally visible non-function global variable and alias in the LLVM module
   (excluding `__llvm_profile_*`) and emits a read-only pointer global initialized to
   the symbol's address:
   - Prefix on `x86_64` and `aarch64`: `b"\x01__imp_"` (where `\x01` suppresses LLVM
     symbol mangling).
   - Prefix on `i686` (`target_arch == "x86"`): `b"\x01__imp__"` (adding the extra
     cdecl leading underscore).
   When the `.rlib` is linked statically into a final executable or DLL, these
   compiler-emitted `__imp_<sym>` globals satisfy the `dllimport` loads locally, and
   `/OPT:REF` strips any unused `__imp_` pointers.

### 4. Mach-O Two-Level Namespaces, `@rpath`, and Mandatory `arm64` Code Signing

On `aarch64-apple-darwin`, dynamic linking is governed by three Mach-O / XNU kernel
mechanisms:

1. **Two-Level Symbol Namespaces (`MH_TWOLEVEL = 0x80`)**:
   Every Mach-O executable and `.dylib` emitted by `rustc` sets `MH_TWOLEVEL` in the
   `mach_header_64.flags` word. Each undefined symbol in `LC_DYLD_INFO_ONLY` /
   `LC_DYLD_CHAINED_FIXUPS` records the 1-based ordinal of the specific `LC_LOAD_DYLIB`
   command that provides it (`libSystem.B.dylib = ordinal 1`), preventing flat-namespace
   symbol collisions at load time unless `-Wl,-flat_namespace` is explicitly passed.
2. **Install Names (`LC_ID_DYLIB`) and `@rpath`**:
   Prebuilt `libstd-0a5ef625bc21ff5e.dylib` sets `LC_ID_DYLIB` to
   `@rpath/libstd-0a5ef625bc21ff5e.dylib`. When `-C rpath=yes` is enabled
   (`compiler/rustc_codegen_ssa/src/back/rpath.rs`), `rustc` embeds `LC_RPATH` load
   commands using `@loader_path/...` relative to the output binary.
3. **Mandatory `arm64` Ad-Hoc Code Signature (`LC_CODE_SIGNATURE = 0x1d`)**:
   On Apple Silicon (`aarch64-apple-darwin`), the XNU kernel refuses to map any
   executable page (`VM_PROT_EXECUTE`) unless it is covered by a valid code signature
   in the `__LINKEDIT` segment referenced by `LC_CODE_SIGNATURE` (`0x1d`).
   Inspecting `libstd-0a5ef625bc21ff5e.dylib` (`support/t10_std_dylibs.json`) and a
   `cdylib` cross-linked on Linux via `rust-lld -flavor darwin` verifies the exact blob
   layout synthesized by `ld64` and `ld64.lld`:

| Field | Offset / Value in `libstd-0a5ef625bc21ff5e.dylib` | Semantics |
| :--- | :--- | :--- |
| Load command | `LC_CODE_SIGNATURE (0x1d)`, `dataoff = 5,500,880`, `datasize = 37,712` | Points to the end of `__LINKEDIT` |
| Outer container | `CS_SuperBlob` (`magic = 0xfade0cc0`, `length = 37,712`, `count = 1`) | Contains 1 `CS_BlobIndex` (`type = 0` `CSSLOT_CODEDIRECTORY`, `offset = 20`) |
| `CS_CodeDirectory` | `magic = 0xfade0c02`, `version = 0x20400` | CodeDirectory v2.4.0 supporting `execSegBase` / `execSegLimit` / `execSegFlags` |
| `flags` | `0x00020002` (`CS_LINKER_SIGNED = 0x20000 \| CS_ADHOC = 0x00002`) | Ad-hoc linker-generated signature (no Apple Developer certificate required for local execution) |
| `hashType` / `hashSize` / `pageSize` | `hashType = 2` (`CS_HASHTYPE_SHA256`), `hashSize = 32`, `pageSize = 12` ($2^{12} = 4,096\text{ B}$) | 32-byte SHA-256 digest over every 4 KiB page from offset `0` up to `codeLimit` (`5,500,880`) |
| `ident` | `"libstd-0a5ef625bc21ff5e"` | Null-terminated signing identifier derived from the output filename |

   > **Kernel caching hazard on in-place binary overwrites**: XNU caches validated
   > code-signing page hashes by vnode (`ubc_cs_blob_get`). Overwriting an existing
   > Mach-O binary in place (`open(O_WRONLY | O_TRUNC)` or `mmap`) rather than unlinking
   > or atomically renaming (`rename(2)`) causes the kernel to compare new code pages
   > against stale cached SHA-256 hashes and immediately deliver `SIGKILL` (`Code Signature Invalid`).
   > Both `rust-lld` and `rustc`'s output placement (`link.rs`) unlink/rename output
   > binaries rather than truncating in place.

### 5. Host `proc-macro` Dynamic Loading Protocol (`host_dylib.rs`)

`compiler/rustc_metadata/src/host_dylib.rs:1-147` loads compiled `proc-macro` shared
libraries into the running `rustc` process:

1. **Registration symbol discovery (`dlsym_proc_macros`, `host_dylib.rs:31-65`)**:
   Every `proc-macro` crate exports a single symbol named
   `__rustc_proc_macro_decls_<stable_crate_id>__` of type `&'static [ bridge::client::ProcMacro ]`,
   synthesized by `compiler/rustc_builtin_macros/src/proc_macro_harness.rs`.
2. **Windows 5-attempt `LoadLibraryExW` retry loop (`load_dylib`, `host_dylib.rs:78-115`)**:
   On Windows (`#[cfg(windows)]`), `load_dylib` calls
   `libloading::os::windows::Library::load_with_flags(path, LOAD_LIBRARY_SEARCH_DLL_LOAD_DIR | LOAD_LIBRARY_SEARCH_DEFAULT_DIRS)`
   in a retry loop up to **5 attempts** with exponential sleep (`10ms`, `20ms`, `40ms`,
   `80ms`) whenever `GetLastError()` returns `ERROR_SHARING_VIOLATION (32)` or
   `ERROR_LOCK_VIOLATION (33)`, mitigating transient file locks held by Windows Defender
   or antivirus scanners immediately after the linker closes the `.dll`.
3. **Intentional library leak (`std::mem::forget(lib)`, `host_dylib.rs:58-63`)**:
   Once loaded, `dlsym_proc_macros` calls `std::mem::forget(lib)` so `dlclose` /
   `FreeLibrary` is **never** called during the `rustc` process lifetime, preventing
   dangling references to `'static` string slices, thread-local destructors, or
   registered callbacks owned by the proc-macro dylib.

## Boundaries

1. **Cross-crate Rust ABI stability**: `SymbolExportLevel::Rust` (`dylib`) does not
   provide a stable ABI across compiler versions or flags; `rustc` mixes the
   `StableCrateId` hash into both symbol names and the `.so`/`.dylib`/`.dll` filename.
2. **Notarization and Gatekeeper on macOS**: While `CS_ADHOC | CS_LINKER_SIGNED`
   (`0x20002`) satisfies Apple Silicon kernel execution requirements for locally built
   binaries, binaries distributed over the internet carrying the `com.apple.quarantine`
   extended attribute require an Apple Developer ID signature (`codesign -s ... --options runtime`)
   and Apple notarization.

## Evidence

- **Empirical inspection of all 8 Tier 1 `libstd` dynamic libraries**:
  `support/t10_std_dylibs.json` and `support/run_t10_t11_probe.py` (ELF dynamic tables,
  `PT_GNU_RELRO`, `BIND_NOW`, Mach-O `LC_CODE_SIGNATURE` `CS_SuperBlob` / `CS_CodeDirectory`
  header parse, and Windows PE `DLLCharacteristics`, `TLSDirectory`, `BaseReloc`, and
  imported DLL lists).
- **Pinned `rustc 1.99.1` source citations**:
  - `compiler/rustc_codegen_ssa/src/back/symbol_export.rs:1-450` (`SymbolExportLevel`)
  - `compiler/rustc_codegen_llvm/src/back/write.rs:1318-1365` (`create_msvc_imps`)
  - `compiler/rustc_codegen_llvm/src/consts.rs:421-468` (Windows `dllimport` on cross-crate statics)
  - `compiler/rustc_codegen_llvm/src/callee.rs:45-155` (`dllimport` on foreign functions and `assume_dso_local`)
  - `compiler/rustc_metadata/src/host_dylib.rs:1-147` (`dlsym_proc_macros`, `load_dylib` retry loop, `std::mem::forget`)

## Revalidation

Run `python3 support/run_t10_t11_probe.py` against a `rustc +1.99.1` toolchain with all
8 Tier 1 `rust-std` components installed to regenerate `support/t10_std_dylibs.json`
and verify dynamic headers, `PT_GNU_RELRO`, `LC_CODE_SIGNATURE`, and PE import tables.
