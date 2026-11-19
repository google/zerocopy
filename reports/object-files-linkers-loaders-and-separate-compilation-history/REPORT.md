# Object Files, Linkers, Loaders, and the History of Separate Compilation

## Summary

Single-file translation units, textual `#include` interfaces, untyped `.o` byte sections joined by string-matching linkers, and flat-namespace dynamic loaders are historical compromises shaped by 1950s–1980s memory limits and Unix/C backward compatibility, not laws of machine execution:

1. **Textual interfaces and untyped `.o` files grew out of kilobyte-scale RAM budgets.** Early PDP-11 Unix (24 KB RAM total, 12 KB kernel) forced one-pass translation and textual `#include` (added c. 1972–1973) in place of compiled interface artifacts. At modern scale, textual expansion produces up to 2,000× compiler input blow-up (`4.2 MB` source → `>8 GB` preprocessed in measured C++ builds), while `.o` files discard types, CFGs, aliasing, and effects—requiring name mangling, COMDAT deduplication, and bolt-on summary LTO (ThinLTO) to recover cross-unit analysis.
2. **String-matching linkers silently accept ABI and ODR corruption.** ELF `SHT_GROUP` / `GRP_COMDAT` (`gABI v4.2`) and `lld` (`comdatGroups.try_emplace(signature, this).second`) deduplicate solely by signature string—first-seen wins without checking sizes or payload bytes. Reversing link order silently flips surviving program semantics with exit code `0` and empty stderr (confirmed live on Linux `x86_64`, GCC 15.2.0 / GNU `ld` 2.47).
3. **ELF, Mach-O, and PE/COFF diverge sharply on dynamic symbol scoping.** ELF constructs a flat breadth-first global scope (`main` → `LD_PRELOAD` → `DT_NEEDED` BFS) where `STV_DEFAULT` DSO symbols are preemptible, blocking intra-DSO inlining under GCC `-fPIC` (whereas Clang `-fPIC` defaults to `-fhalf-no-semantic-interposition`, not full `-fno-semantic-interposition`). Under default `glibc` (`dl_dynamic_weak == 0`), an earlier `STB_WEAK` stops search and overrides a later `STB_GLOBAL`; `RTLD_LOCAL` splits C++ vtable/`type_info` identity across plugins unless patched by `STB_GNU_UNIQUE` (which permanently pins the DSO `NODELETE`). By contrast, Apple `dyld` defaults to two-level `(libOrdinal, symbol)` binding (still requiring global weak-def coalescing via `BIND_SPECIAL_DYLIB_WEAK_LOOKUP` for C++), and Windows PE/COFF binds every import explicitly to `(dll_name, name_or_ordinal)` in the IAT.
4. **Shipped counterexamples prove string-matching flat linkers are contingent.** Multics (1968) used hardware-trapped per-process linkage sections over `<segment>|[entry]` pairs; Xerox PARC Mesa/Cedar (1970s–1986) checked version-stamped `.bcd` interfaces in its Binder and Loader; Project Oberon (1992/2013) checked whole-module `.smb` structural checksums (including hidden GC pointers) in `Modules.Load` and linked by integer indices with zero string matching; Crelier (1994) refined this to per-item structural fingerprints; Swift's resilient ABI decouples layout evolution via runtime metadata, value witness tables, and dispatch thunks; and the WebAssembly Component Model wires structurally typed imports/exports explicitly at instantiation time with no ambient namespace.
5. **Irreducible constraints remain.** $O(\text{changed\_unit})$ incremental rebuild latency at $10^7+$ LOC, bounded per-action build memory, cross-vendor binary distribution without source, ASLR/`W^X` code-sharing physics, and the specialization-versus-indirection trade-off for cross-boundary generics are non-contingent constraints that any clean-slate architecture must satisfy.

## Applicability

This report documents the historical origins, normative binary-format rules, production linker/loader implementations, and architectural counterexamples for separate compilation, static linking, and dynamic loading.

### Subject Relationships

The sixteen subjects in `REPORT.json` span four coordinated groups:

- **Normative specifications:** ELF gABI v4.2 (`xinuos/gabi` @ `4ff978d04d78cbd308705a782f34a189118d11cd`), Microsoft PE/COFF (`MicrosoftDocs/win32` @ `ca8274decead49403d70ceeed4af8d4ca74eaf11`), Swift Library Evolution & Type Metadata ABI (`swiftlang/swift` @ `466f30162134b2c16b0f05c05d766cdd151236a5`), and WebAssembly Component Model (`WebAssembly/component-model` @ `585526aa1f2c7f76f07557d16e265dede38b3acb`).
- **Production implementations:** LLVM `lld`/ThinLTO/Clang (`llvm/llvm-project` @ `ffcd0a522aedc16a966e3efb9a97a336be8ddb57`), `glibc` `ld.so` (`bminor/glibc` @ `04e750e75b73957cf1c791535a3f4319534a52fc`), and Apple `dyld-1378` (`apple-oss-distributions/dyld` @ `fd8d0c4d52320ebf64db34f3cb280310d905c5ae`).
- **Primary historical and design literature:** Daley & Dennis (1968), Swinehart et al. (1985/1986), Gingell et al. (1987), Stroustrup (1988), Wirth & Gutknecht (1992/2013 `ORB.Mod`/`Modules.Mod`), Ritchie (1993), Crelier (1994), Pike (2012), and Johnson et al. (2017).
- **Executable probe:** `support/verify_linking_models.py` runs deterministic Python models of ELF, Mach-O, PE/COFF, Oberon/Crelier, and COMDAT behavior plus live Linux `x86_64` ELF checks (verified on GCC 15.2.0, GNU `ld` 2.47, `glibc` 2.43, Python 3.13.15).

### Corpus Cross-References

Rust-specific object tables and formal verifier inventories live in adjacent packages and are not duplicated here:
- `verified-assemblers-encoders-linkers-and-object-format-models` (CompCertELF, Linksem, CakeML, MM0).
- `rustc-object-files-sections-symbols-comdats-and-relocations` (`rustc`/LLVM MC section/mangling/relocation catalogs).
- `rustc-static-linking-archive-formats-and-linker-driver` (archive emission and linker driver).
- `rustc-dynamic-linking-loader-contracts-and-code-signing` (`dylib`/`cdylib`, `rpath`, code signing).
- `cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts` (cross-DSO vtable uniqueness and open-world LTO).

## Findings

### 1. Translation Units, Textual Interfaces, and Bolt-On Whole-Program Optimization

Basis: documentation + normative + source + execution

#### 1.1 Core-Memory Origins of Single-File Compilation and `#include`

- **PDP-11 memory budgets (Ritchie 1993):** The first DEC PDP-11 at Bell Labs (1970) had **24 KB of core memory** (**12 KB** for the Unix kernel, a tiny user partition, and the remainder as a RAM disk). Thompson's B compiler had been squeezed into **8 KB** on the PDP-7, mandating one-pass immediate code emission with no whole-program AST or external symbol-table persistence—a constraint inherited directly by C.
- **Origin of the C preprocessor (1972–1973):** Ritchie records that the preprocessor was added around 1972–1973 at Alan Snyder's urging (inspired by BCPL `GET` and PL/I `%INCLUDE`) as an optional external pass invoked only when a file began with `#`. Without RAM for compiled interface tables, **re-lexing and re-parsing source text became the interface contract**.
- **$O(N \times M)$ textual expansion vs. binary export data (Pike 2012):** After ANSI C (1989) popularized `#ifndef` include guards so headers transitively included all dependencies, compiler input scaled quadratically with program size. Pike measured a production C++ binary of ~2,000 files totaling **4.2 MB** concatenated that expanded via `#include` to **>8 GB** fed to the compiler (~**2,000×** blow-up). Go instead embeds transitive public-interface export data at the front of each compiled package object file so compiling package `A` importing `B` opens **exactly one file** (`B`'s object), reducing input volume ~**50×** and eliminating header/object drift.

#### 1.2 Untyped Relocatable Objects and String-Matching Linkers

Relocatable objects evolved from mainframe assemblers through Unix `a.out`, COFF, and SVR4 ELF (`xinuos/gabi` v4.2) so tiny linkers could stream raw byte sections and apply address arithmetic patches:

- **Information-destroying container:** Even `.bss` derives from **Block Started by Symbol** in mid-1950s IBM 704 UA-SAP assembly (zero-initialized `SHT_NOBITS` storage). An ELF `ET_REL` object flattens a typed program into untyped byte blobs (`.text`, `.rodata`, `.data`, `.bss`), a string-indexed symbol table (`.symtab` + `.strtab`), and offset-patching relocations (`SHT_REL`/`SHT_RELA`, `gabi_06-reloc.rst`). CFGs, aliasing, effects, and layouts are discarded and later retrofitted as unverified side tables (`.eh_frame`, `.debug_*`, `.gcc_except_table`, `.llvm_stackmaps`, `.note.gnu.property`).
- **Legacy linker constraints codified in C:** Accommodating mainframe linkers (OS/360, Fortran 77), ANSI C89 (`X3.159-1989` §5.2.4.1) guaranteed at least **31 significant characters** for internal identifiers/macros but only **6 significant case-insensitive characters** for external identifiers (raised to 31 case-sensitive in C99). Fortran `COMMON` survived as C tentative definitions (`SHN_COMMON`) silently merging uninitialized globals across TUs until **GCC 10 (2020)** switched to `-fno-common` by default.
- **Name mangling as a linker workaround (Stroustrup 1988, pp. 379–380):** Stroustrup wrote candidly that C++'s encoding scheme *"uses the name encoding scheme to 'trick' the linker into doing type checking"* because *"getting an improved linker into use is typically a hard and slow process."* Mangling encodes function parameter types (and function-pointer parameter return types, e.g., `f(int (*)(char*))` → `f__FPFPc_i`), but **omits non-template function return types, global variable types, struct layouts, and all `extern "C"` declarations**. Mismatched struct layouts or ABI flags (`-fshort-enums`, differing `#define` guards, incompatible target features) link silently with exit code `0`.

#### 1.3 Monomorphization Spray, COMDAT Deduplication, and Silent ODR Corruption

To support templates/generics without centralized instantiation repositories (`-frepo` failed on build friction), C++ and Rust emit duplicate instantiations across TUs and rely on linker COMDAT deduplication:

- **ELF `SHT_GROUP` / `GRP_COMDAT` (`xinuos/gabi` `03-sheader.rst:758-827`):** `SHT_GROUP` groups interdependent sections (code, literals, unwind/debug) under one signature symbol (`sh_link` → `.symtab`, `sh_info` → symbol index) with flag `GRP_COMDAT = 0x1`. Duplication is defined **solely by signature string equality**; the linker retains one group and discards all duplicates without any size or byte-content check.
- **`lld` first-seen discard (`llvm/llvm-project` `lld/ELF/InputFiles.cpp:648-664`):**

```cpp
// llvm/llvm-project @ ffcd0a522aedc16a966e3efb9a97a336be8ddb57
// lld/ELF/InputFiles.cpp:648-663
if (LLVM_LIKELY(sec.sh_type == SHT_GROUP)) {
  StringRef signature = getShtGroupSignature(objSections, sec);
  ...
  bool keepGroup = !flag || ignoreComdats ||
                   ctx.symtab->comdatGroups
                       .try_emplace(CachedHashStringRef(signature), this)
                       .second;
```

- **PE/COFF contrast (`MicrosoftDocs/win32` `pe-format.md:1104-1125`):** COFF defines six selection modes—`NODUPLICATES` (`1`), `ANY` (`2`), `SAME_SIZE` (`3`), `EXACT_MATCH` (`4`), `ASSOCIATIVE` (`5`), and `LARGEST` (`6`). Modes `3` and `4` reject mismatched duplicates, yet C++ compilers emit `IMAGE_COMDAT_SELECT_ANY` because differing debug info or optimization levels break byte identity—leaving silent ODR corruption intact on Windows too.
- **Empirical confirmation (`support/verify_linking_models.py`):** Linking two `x86_64` ELF objects (`tu_a.o`, `tu_b.o`) whose `odr_group_sig` `GRP_COMDAT` groups define `odr_fn` returning `42` vs. `99` under GCC 15.2.0 / GNU `ld` 2.47 yields `42` for `[main_odr.o, tu_a.o, tu_b.o]` and `99` for `[main_odr.o, tu_b.o, tu_a.o]`—both exiting `0` with **zero linker warnings**.

#### 1.4 Bolt-On Cross-Module Optimization: Full LTO vs. ThinLTO

Full LTO restores whole-program optimization by merging every TU's IR into one monolithic serial link step, exhausting RAM and destroying incremental parallelism at scale. **LLVM ThinLTO** (`Johnson, Amini & Li, CGO 2017`; `llvm/lib/LTO/LTO.cpp:137-143, 406-497`; `llvm/lib/Transforms/IPO/FunctionImport.cpp`) splits LTO into three phases:

1. *Parallel compile:* Emits LLVM bitcode plus compact per-module **summaries** (call graph, instruction counts, references, linkage, GUIDs).
2. *Serial summary-only thin link (zero IR loaded):* Merges summaries into a `ModuleSummaryIndex`, resolves prevailing COMDAT/linkonce copies via `thinLTOResolvePrevailingInIndex` (`LTO.cpp:492`, promoting prevailing `linkonce` to `weak` and downgrading non-prevailing copies to `available_externally`), computes dead-symbol elimination and internalization, and plans cross-module imports (`ComputeCrossModuleImport` / `computeImportForModule`: CGO 2017 default limit 100 instructions with `0.7` per-hop decay; hot PGO limit `300` with decay `1.0`).
3. *Parallel backends + incremental caching:* Each TU imports only chosen callee IR bodies in parallel, cached by `computeLTOCacheKey` (`LTO.cpp:137-143`, hashing module ID, import/export sets, and resolved ODR linkages).

ThinLTO remains strictly **compiler-version-locked**: LLVM bitcode has no stable cross-version ABI, and cross-language LTO (`-Clinker-plugin-lto`) requires matching LLVM versions plus careful alignment of frontend IR attributes (`noalias`, `noundef`, TBAA).

---

### 2. Dynamic Linking Semantics: ELF Flat Namespace vs. Mach-O Two-Level vs. PE/COFF

Basis: normative + source + documentation + execution

#### 2.1 ELF Flat Namespace, Semantic Interposition, and `glibc` Lookup Nuances

SunOS 4 shared libraries (`Gingell, Lee, Dang & Weeks, USENIX Summer 1987`) and SVR4 ELF (`xinuos/gabi`) designed `.so` files as **drop-in semantic replacements for static `.a` archives** to share physical `libc`/X11 pages via PIC + `mmap` + COW without source annotations. That choice entrenched six subtle invariants:

1. **Breadth-first global scope (`gabi_08-dynamic.rst:623-631`; `glibc/elf/rtld.c:843-855, 1820-1827`):** Startup search order is: (a) `main` executable, (b) `LD_PRELOAD` (or `--preload`, `/` paths stripped for setuid), (c) breadth-first `DT_NEEDED` traversal (all level-1 dependencies, then level-2, etc.).
2. **Default preemptibility (`gabi_05-symtab.rst:333-349`; `lld/ELF/Symbols.cpp:355-386`):** Every `STV_DEFAULT` symbol defined in a shared library is preemptible even by *intra-DSO* callers. `lld`'s `elf::computeIsPreemptible` returns `false` for non-`STV_DEFAULT` symbols and non-`-shared` executables, but `true` for every `STV_DEFAULT` symbol in a `-shared` link unless suppressed by `-Bsymbolic`, `-Bsymbolic-non-weak`, `-Bsymbolic-functions`, or `-Bsymbolic-non-weak-functions` (with `--dynamic-list` overriding back to preemptible).
3. **Compiler optimization tax — GCC vs. Clang (`clang/lib/Driver/ToolChains/Clang.cpp:6061-6086`):**
   - **GCC `-fPIC` default (`-fsemantic-interposition`):** Treats all `STV_DEFAULT` functions as interposable, blocking intra-DSO inlining and IPO and forcing PLT calls. Compiling `libpython` with `-fno-semantic-interposition` in Fedora 32 (and upstream CPython 3.10+ `--enable-shared --with-optimizations`) yielded **5%–27%** `pyperformance` speedups.
   - **Clang `-fPIC` ELF default (`-fhalf-no-semantic-interposition`):** Direct inspection of `Clang.cpp:6061-6086` disproves the claim that Clang defaults to full `-fno-semantic-interposition`. Explicit `-fsemantic-interposition` matches GCC (`dso_preemptable`); explicit `-fno-semantic-interposition` emits `.Lfoo$local` aliases (`dso_local`) on `x86`, `AArch64`, and `RISC-V` to bypass the PLT; **the default (neither flag)** passes **`-fhalf-no-semantic-interposition`** (`Clang.cpp:6079-6080`), allowing intra-module IPO/inlining while omitting local aliases so surviving calls remain PLT-interposable.
4. **`STV_PROTECTED` vs. `DF_SYMBOLIC` (`gabi_05-symtab.rst:344-349`; `gabi_08-dynamic.rst:395-406`):** `STV_PROTECTED` binds *internal* references locally (immune to `LD_PRELOAD`) while keeping the symbol exported; external callers still bind to an earlier global interposer (verified live in `support/verify_linking_models.py`: inside `libtarget.so`, `LD_PRELOAD` hijacked `default_fn` `10→77` while `protected_fn` stayed `20`, printing `7720` vs. baseline `1020`). `DF_SYMBOLIC` (`-Bsymbolic`, replacing deprecated `DT_SYMBOLIC`) searches the defining DSO's own table before the global scope for all internal references. Protected *data* symbols remain fragile under non-PIE copy relocations (`R_X86_64_COPY`), policed by `_dl_check_protected_symbol` (`dl-lookup.c:476-478`).
5. **Runtime `STB_WEAK` reversal (`glibc/elf/dl-lookup.c:480-499`):** Unlike static linkers (where `STB_GLOBAL` overrides `STB_WEAK`), default `glibc` (`GLRO(dl_dynamic_weak) == 0`) falls straight through from `STB_WEAK` to `STB_GLOBAL`, terminating search on the **first** weak definition encountered unless deprecated `LD_DYNAMIC_WEAK` is enabled:

```c
// bminor/glibc @ 04e750e75b73957cf1c791535a3f4319534a52fc
// elf/dl-lookup.c:480-498
switch (ELFW(ST_BIND) (sym->st_info))
  {
  case STB_WEAK:
    if (__glibc_unlikely (GLRO(dl_dynamic_weak))) {
      if (! result->s) { result->s = sym; result->m = (struct link_map *) map; }
      break;
    }
    [[fallthrough]];
  case STB_GLOBAL:
    result->s = sym; result->m = (struct link_map *) map;
    return 1;
```

6. **`dlopen(RTLD_LOCAL | RTLD_GLOBAL)` and `STB_GNU_UNIQUE` (`dl-open.c:86-133`; `dl-lookup.c:204-332, 500-504`):** `RTLD_LOCAL` omits a plugin from `_ns_main_searchlist`, so two `RTLD_LOCAL` plugins carrying weak C++ vtables/`type_info` (`_ZTI...`) resolve to distinct addresses, breaking pointer-equality `typeid`/`dynamic_cast` and cross-plugin exceptions (see `cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts`). To rescue C++ inline/template static locals across `RTLD_LOCAL`, GCC/glibc added `STB_GNU_UNIQUE`: `do_lookup_unique` registers the symbol in a namespace-global table (`_ns_unique_sym_table`) and calls **`mark_nodelete(map, flags)`** (`dl-lookup.c:315-324`), permanently inhibiting `dlclose` for that DSO.

#### 2.2 Apple Mach-O Two-Level Namespaces (`dyld`)

Apple `dyld` (`apple-oss-distributions/dyld` @ `fd8d0c4d52320ebf64db34f3cb280310d905c5ae`, `dyld/Loader.cpp:2853-3095`) defaults to **two-level namespaces (`MH_TWOLEVEL`)**:

- **Direct `(libOrdinal, symbolName)` binding (`Loader.cpp:2853-2865`):** `ld64` stamps every import with the 1-based `LC_LOAD_DYLIB` ordinal (`libOrdinal`) inside `LC_DYLD_CHAINED_FIXUPS` (`mach_o/ChainedFixups.cpp`) or legacy bind opcodes (`mach_o/BindOpcodes.cpp`). `Loader::resolveSymbol` jumps directly in $O(1)$ to `dependent(state, libOrdinal - 1)` for `libOrdinal > 0`—preventing accidental sibling interposition (`DYLD_INSERT_LIBRARIES` cannot hijack two-level references without `DYLD_FORCE_FLAT_NAMESPACE` or explicit `__DATA,__interpose` tables). Special ordinals handle `BIND_SPECIAL_DYLIB_SELF` (`0`), `BIND_SPECIAL_DYLIB_MAIN_EXECUTABLE` (`-1`), and opt-in `BIND_SPECIAL_DYLIB_FLAT_LOOKUP` (`-2`, scanning `state.loaded`/`state.delayLoaded` while skipping `hiddenFromFlat()` images except `this`).
- **Global weak-def coalescing escape hatch (`BIND_SPECIAL_DYLIB_WEAK_LOOKUP`, `Loader.cpp:2914-3088`):** To preserve C++ ODR uniqueness for `N_WEAK_DEF` symbols (`operator new`, RTTI, template statics), `dyld` scans all unhidden `hasWeakDefs` images (allocating `state.weakDefMap` once `weakDefResolveSymbolCount > 5000`, `Loader.cpp:2968-2972`). Unlike default `glibc`, `dyld` continues scanning so a **later non-weak definition overrides an earlier weak-def** (`Loader.cpp:3024-3030`) and patches overridden targets inside `dyld_shared_cache` via `JustInTimeLoader::cacheWeakDefFixup` (`Loader.cpp:3050-3072`). Modern Mach-O binaries rely on eager chained fixups and `PrebuiltLoader` closures rather than lazy PLT stubs.

#### 2.3 Windows PE/COFF Explicit Import and Export Tables

Windows PE/COFF (`MicrosoftDocs/win32` @ `ca8274decead49403d70ceeed4af8d4ca74eaf11`, `pe-format.md:1246-1390, 1550-1566`) makes the DLL boundary explicit in both source and object metadata:

- **`.edata` Export Directory Table (`IMAGE_EXPORT_DIRECTORY`):** Exports only explicitly annotated symbols (`__declspec(dllexport)` or `.def`) via three RVA arrays: Export Address Table (RVAs or forwarder strings), sorted Name Pointer Table, and 16-bit Ordinal Table.
- **`.idata` Import Directory Table (`IMAGE_IMPORT_DESCRIPTOR`):** One descriptor per imported DLL pairs an immutable **Import Lookup Table (ILT)** (name/hint or ordinal) with an **Import Address Table (IAT)** patched eagerly at load time (with opt-in Delay-Load Import Tables for lazy DLL loading, `pe-format.md:1246-1265`).
- **No PLT and no diamond collision:** `__declspec(dllimport)` lets the compiler emit direct indirect calls/loads through the IAT (`call [__imp_foo]`), eliminating ELF-style PLT trampolines and ambient interposition while allowing side-by-side diamond DLLs (`crypto_v1.dll` and `crypto_v2.dll` exporting identically named `hash`) to coexist in one process without collision (at the cost of `dllimport`/`dllexport` header macro boilerplate and import `.lib` stubs).

#### 2.4 Dynamic Linking Comparison Matrix

| Dimension | System V ELF (`glibc` / `lld`) | Apple Mach-O (`dyld-1378`) | Windows PE/COFF (Win32) |
|---|---|---|---|
| **Namespace scope** | Flat process-global BFS (`main` → `LD_PRELOAD` → `DT_NEEDED`) | Two-level `(libOrdinal, symbol)` (`MH_TWOLEVEL`) | Explicit `(dll_name, name_or_ordinal)` IAT |
| **Intra-DSO preemption** | Preemptible by default (`STV_DEFAULT` in `-shared`) | Non-preemptible for two-level binds; explicit `__DATA,__interpose` | Non-preemptible; internal direct, cross-DLL via IAT |
| **`-fPIC` IPO default** | GCC: `-fsemantic-interposition`; Clang: `-fhalf-no-semantic-interposition` | Direct internal calls | Explicit `dllimport`/`dllexport` |
| **Export default** | Export all non-local unless `-fvisibility=hidden` / version script | Export all non-local unless `-fvisibility=hidden` | Hidden by default; explicit `dllexport`/`.def` |
| **Lazy binding** | `DT_JMPREL` + PLT/GOT; disabled by `DF_BIND_NOW`/`-z now` | Mostly eager `LC_DYLD_CHAINED_FIXUPS` + `PrebuiltLoader` | Eager IAT; opt-in Delay-Load Import Table |
| **Weak / vague linkage** | Default `glibc`: first `STB_WEAK` stops search and beats `STB_GLOBAL` | `BIND_SPECIAL_DYLIB_WEAK_LOOKUP`; later strong beats weak-def | No cross-DLL weak coalescing; single `dllexport` owner |
| **Plugin isolation** | `RTLD_LOCAL` splits RTTI unless `STB_GNU_UNIQUE` (pins `NODELETE`) | `hiddenFromFlat()` isolates flat/weak scans | No flat namespace; explicit DLL binding |
| **COMDAT modes** | `GRP_COMDAT` (`0x1`) only (signature-only, first wins) | Linker `N_WEAK_DEF` coalescing | 6 modes (`NODUPLICATES`..`LARGEST`); C++ uses `ANY` |
| **Unloading** | `glibc`: refcounted, blocked by `NODELETE`/`STB_GNU_UNIQUE`/TLS dtors; `musl`: no-op | Refcounted; pins shared-cache & dynamic-ref images | `FreeLibrary` refcounted; `DllMain` under loader lock |

---

### 3. Loader Startup, Initialization Ordering, TLS Models, and Unloading Hazards

Basis: normative + source + documentation

- **ELF initialization sequence (`xinuos/gabi` `08-dynamic.rst:860-944`; `glibc/elf/dl-init.c:25-127`):** `_dl_init` runs (1) `DF_1_INITFIRST` (`dl-init.c:86-90`), (2) the executable's `DT_PREINIT_ARRAY` (forbidden in DSOs; executes before system libraries initialize, `dl-init.c:93-107`), and (3) DSOs in reverse dependency order (`l_initfini[i]` descending, `dl-init.c:119-121`), executing `DT_INIT` then `DT_INIT_ARRAY`. Ordering among sibling `DT_NEEDED` entries is **unspecified** (`08-dynamic.rst:880-881`), ordering across cyclic `DT_NEEDED` graphs is **undefined** (`08-dynamic.rst:874`), and intra-binary C++ static constructors across `.o` files have unspecified order (the static initialization order fiasco). On Windows, `DllMain(DLL_PROCESS_ATTACH)` runs under the process-wide **OS loader lock**, risking deadlock on thread joins, synchronization, or `LoadLibrary`. Language-level designs avoid these pitfalls: Go specifies acyclic package-DAG `init()`, Java specifies lazy per-class locked `<clinit>`, Swift uses lazy `dispatch_once` globals, Rust forbids user life-before-main by policy, and Wasm runs explicit `start` functions only on instantiation.
- **ELF Thread-Local Storage (`Drepper 2003/2005`):** Retrofits per-thread storage via `%fs` (`x86_64`) / `TPIDR_EL0` (`AArch64`) across four access models plus `TLSDESC`: **Local Exec (`LE`)** (direct thread-pointer offset, executables only), **Initial Exec (`IE`)** (GOT offset into startup static TLS block; sets `DF_STATIC_TLS` and causes `dlopen` to fail if surplus static TLS is exhausted), and **Local/Global Dynamic (`LD`/`GD`)** (calls `__tls_get_addr` / `TLSDESC` to index the per-thread Dynamic Thread Vector, relaxed by the static linker into `IE`/`LE` with instruction-sequence rewrites and `nop` padding).
- **`dlclose` unsoundness:** Unmapping code/data in a multithreaded native process risks dangling function pointers, vtables, `type_info`, `'static` references, and concurrent thread teardown races. Even `glibc` (`elf/dl-close.c:177-184`) inhibits unloading whenever `l_nodelete_active` is set (including implicitly by `STB_GNU_UNIQUE` in `dl-lookup.c:315-324`) or `atomic_load_acquire(&l->l_tls_dtor_count) != 0`. **`musl` libc** intentionally implements `dlclose` as a POSIX-compliant **permanent no-op** (`wiki.musl-libc.org/functional-differences-from-glibc.html`), trading infinite-plugin address-space reclamation for elimination of latent dangling-pointer and TLS-teardown races.

---

### 4. Architectural Counterexamples That Avoided String-Matching Linkers

Basis: normative + source + documentation + execution

#### 4.1 Multics Dynamic Segment Linking (Daley & Dennis, CACM 1968)

On the GE 645, Multics unified files and virtual memory into up to $2^{14}$ segments of up to $2^{18}$ 36-bit words (`Daley & Dennis 1968`, pp. 306–312). Procedure segments were strictly **pure** (non-self-modifying) so processes shared physical code despite assigning independent per-process segment numbers:

- External references took the **two-part segment-qualified form `<D>|[x]`**, resolving segment name `D` via the directory hierarchy ("making it known" as process-local segment number `d#α`) and resolving entry `x` strictly inside `D`'s own embedded symbol table.
- Each pure procedure owned a per-process **linkage section** addressed via hardware base register **`lp`** (linkage pointer, base pair 2 alongside `ap`, `bp`, `sp`). Unlinked slots held indirect word pairs tagged with fault code **`ft`**; the first access trapped to the supervisor, resolved `<D>|[x]`, and overwrote the private indirect word with generalized address `d#α|x` ("snapping the link"). Procedure calls targeted a 2-instruction stub in the callee's linkage section that reloaded `lp` before branching to pure code.
- **Boundary of the precedent:** Multics eliminated static link-editing and flat global symbol collision in 1968 and pioneered per-process indirection tables (precursor to GOT/PLT and two-level lookup), but its trap still matched symbolic character strings `<D>|[x]` rather than static structural type hashes.

#### 4.2 Xerox PARC Mesa & Cedar: Version-Stamped `.bcd` Files and the Binder (1970s–1986)

Scaling to **>100 configurations** on Xerox Alto/Dandelion/Dorado workstations (`Swinehart, Zellweger, Beach & Hagmann, TOPLAS 1986`; `Swinehart et al. 1985`), Mesa and Cedar replaced textual headers and untyped linkers with:

- Compiled **`DEFINITIONS` (interface)** and **`PROGRAM` (implementation)** modules emitted as **Binary Configuration Descriptions (`.bcd`)** carrying binary symbol tables and globally unique **48-bit version stamps**.
- A separate configuration language (`C/Mesa`) specifying `IMPORTS`/`EXPORTS` wiring across modules and subconfigurations. Both the static **Binder** and dynamic **Cedar Loader** verified that every exported interface's **name and version stamp** matched the exact stamp expected by every importer (`Swinehart et al. 1985`, §"Compiler, Binder, and Loader").
- **Side-by-side private configurations:** Developers routinely bound experimental Imager/Viewers/Tioga builds into a **hiding configuration** that omitted re-exports, testing new implementations concurrently inside the live workstation without colliding with production tools (`Swinehart et al. 1985`, §"Developing New Versions").

#### 4.3 Project Oberon `.smb` Checksums (`Wirth & Gutknecht 1992/2013`) vs. Crelier Fingerprinting (`1994`)

Project Oberon achieved type-safe, zero-string-matching dynamic linking in **665 total lines** (`ORB.Mod` = 440 lines, `Modules.Mod` = 225 lines):

- **`ORB.Mod:256-361` (`.smb` generation and checksum key):** `ORB.Export` writes every exported declaration (`obj.expo`)—constants, variables, procedure export indices (`exno`), and full structural types via `OutType` (including record sizes, exported field offsets, AND **`FindHiddenPointers` at lines 270–279**, serializing byte offsets of *unexported* pointer fields inside exported records for GC safety). After 4-byte padding, `ORB.Export` sums all 32-bit words into a 32-bit `key` (`sum := sum + x`, lines 350–351). Body-only edits leave `sum = oldkey` (zero client recompilation); interface changes halt with `"new symbol file inhibited"` (line 357) unless `newSF` is explicitly enabled.
- **`Modules.Mod:45-186` (key-checked integer-table loader):** `Modules.Load` reads `(impname, impkey)` from `.rsc`, recursively loads each dependency, and asserts **`IF impmod.key = impkey`** (line 73), aborting with `error(3, name1)` ("key conflict") and rolling back `refcnt` on mismatch. All cross-module code (`fixorgP`), data (`fixorgD`), and type-descriptor (`fixorgT`) fixups index directly via integer `(mno, pno/vno)` tables (`impmod.ent + pno*4`, lines 135–179)—**zero string symbol matching** at link/load time.
- **Granularity refinement — Crelier (1994) (`ETH Diss. 10650`):** Because Wirth's whole-module word sum changes even on **monotonic additive exports** (appending a new procedure invalidates untouched clients), Régis Crelier's OP2 compiler replaced the monolithic module key with **per-item structural fingerprints** (`pb`/`pv`) and layered `.smb` prefixes—rejecting ABI breaks while keeping untouched clients binary-compatible across additive exports (verified side-by-side in `support/verify_linking_models.py`).

#### 4.4 C++20 Modules & BMIs, Swift Resilience, and WebAssembly Component Model

- **C++20 Modules / BMIs (`ISO/IEC 14882:2020`; Clang `StandardCPlusPlusModules`):** Compiles module interfaces into precompiled **Binary Module Interfaces** (`.pcm`/`.gcm`/`.ifc`) and **Reduced BMIs** (`--precompile-reduced-bmi`), eliminating macro leakage and repeated header parsing. However, BMIs serialize compiler-private ASTs with strict compiler, version, and dialect-flag lock-in (Clang explicitly notes incompatibility with `cl.exe`), require a build-graph dependency-scanning pre-pass (`clang-scan-deps` / P1689R5), and still hand untyped `.o` files to legacy string-matching linkers.
- **Swift Resilient Library Evolution (`swiftlang/swift` `LibraryEvolution.rst:115-207`, `TypeMetadata.rst:11-20`):** Breaks the "frozen C layout vs. binary updatability" dilemma. Resilient structs/enums hide their size, alignment, and field offsets behind unique runtime **Type Metadata** records, **Value Witness Tables** (`size`/`stride`/`copy`/`destroy`), **Field Offset Vectors**, property accessors, and protocol **dispatch thunks**, allowing unspecialized generic code to cross dynamic ABI boundaries. Performance-critical types opt out explicitly via `@frozen` (locking layout) and `@inlinable` (publishing bodies in `.swiftinterface`, where subsequent body edits do not retroactively alter prebuilt clients).
- **WebAssembly Component Model (`WebAssembly/component-model` `Explainer.md:33-97, 248-273, 722-730, 929-969`):** Replaces untyped symbols with structurally typed WIT interfaces lowered/lifted via the deterministic **Canonical ABI** (`canon lift`/`canon lower`). Shared-nothing instantiation passes every import explicitly—eliminating ambient namespaces, enabling clean multi-version coexistence (`wasi:keyvalue/store@0.1.0` alongside other versions/backends via unique import names + `implements` metadata), and delivering `LD_PRELOAD`-style virtualization through explicit wrapper composition.

#### 4.5 Interface and Linking Artifact Comparison

| System / Artifact | Interface Representation | Link/Load Type-Checked? | Body-Only Edit Keeps Binary Compat? | Polyglot / Cross-Compiler? | Namespace Model |
|---|---|---|---|---|---|
| **C / C++ headers + ELF** | Re-parsed text + untyped `.o` | String match (+ param mangling) | Yes (unchecked) | C ABI subset only | Flat process-global BFS |
| **C++20 BMI** | Compiler-private serialized AST | Compile-time only (`.o` untyped) | Reduced BMI curbs rebuilds | **No** (compiler/flag locked) | Module names (flat linker) |
| **Go package export data** | Transitive binary section in `.a` | Compile-time + export hash | Yes | Single-language (Go) | Package-path qualified |
| **Rust `.rmeta` + SVH** | Binary metadata + Strict Version Hash | Checked by `rustc` (not `ld`) | Only if SVH preserved | Single-language (`rustc`) | Crate-hash mangled |
| **Mesa / Cedar `.bcd`** | Compiled symtab + 48-bit stamp | **Yes** (Binder + Loader) | Yes | Mesa/Cedar family | Explicit `C/Mesa` config |
| **Oberon `.smb` / `.rsc`** | Exported types + hidden GC ptrs + 32-bit key | **Yes** (`impmod.key = impkey`) | **Yes** (checksum invariant) | Single-language (Oberon) | Integer `(mno, pno/vno)` |
| **Crelier OP2 (1994)** | Layered `.smb` + per-item fingerprints | **Yes** (per-item match) | **Yes** (+ additive exports) | Single-language (Oberon-2) | Per-item fingerprinted |
| **Swift Resilience** | `.swiftinterface` + runtime metadata | Compile-time + runtime metadata | **Yes** (+ resilient field adds) | Swift (+ ObjC/C interop) | Module + Mach-O 2-level |
| **Wasm Component Model** | Binary WIT structural types | **Yes** (structural validation) | **Yes** (shared-nothing) | **Yes** (polyglot) | Explicit instantiation wiring |

---

### 5. Contingency vs. Irreducible Constraint Matrix

Basis: derived

Each classification carries an explicit warrant: a **contrasting precedent** (for historical contingencies) or a **complexity, hardware, or organizational bound** (for irreducible constraints and trade-offs).

| Property / Mechanism | Classification | Warrant |
|---|---|---|
| Textual `#include` re-parsing | **Historical contingency** | *Precedents:* Mesa `.bcd`, Oberon `.smb`, Go single-file export data, Swift `.swiftinterface`, Wasm WIT eliminate $O(N \times M)$ text expansion. |
| 1 source file = 1 compilation/optimization unit | **Historical contingency** | *Precedents:* Smalltalk/Lisp per-method, Unison per-definition hashes, Zig per-declaration builds, and ThinLTO summary-driven cross-module backends decouple optimization scope from files. |
| Type/layout/effect-oblivious string-matching linkers | **Historical contingency** | *Precedents:* Mesa/Cedar Binder stamps, Oberon `Modules.Load` keys, Crelier fingerprints, and Wasm Component validation perform fast $O(\text{interface})$ link/load checking. |
| ELF flat global namespace & default interposition | **Historical contingency** | *Precedents:* Multics `<segment>|[entry]`, PE explicit IAT, Mach-O `MH_TWOLEVEL`, and Wasm explicit wiring prevent accidental hijacking and avoid 5–27% IPO/PLT loss while keeping interposition explicit. |
| Silent first-wins COMDAT deduplication | **Historical contingency** | *Precedents:* PE/COFF already specifies `SAME_SIZE`/`EXACT_MATCH` modes; content-addressed caches verify structural identity instead of discarding mismatches by mangled name. |
| Ambient static-init order & unsafe `dlclose` | **Historical contingency** | *Precedents:* Go acyclic `init()`, Java lazy `<clinit>`, Wasm explicit `start`, and `musl` no-op `dlclose` avoid startup races and dangling-code teardown hazards. |
| 6-char external names & `COMMON` tentative merging | **Historical contingency** | *Provenance:* OS/360 and Fortran 77 linker limits in C89 §5.2.4.1 / `-fcommon`; retired in C99+ and GCC 10 (`-fno-common`). |
| $O(\text{changed\_unit})$ incremental builds & bounded RAM at $10^7+$ LOC | **Irreducible constraint** | *Complexity bound:* Whole-program re-parsing or monolithic LTO scales $\Omega(\text{total LOC})$ in time/RAM; modular boundaries with early cutoff or compact summaries (ThinLTO) are necessary for sublinear rebuilds. |
| Separate binary distribution without source across vendors/languages | **Irreducible constraint** | *Organizational boundary:* OS libraries, proprietary plugins, and polyglot components ship independently on staggered schedules; a stable binary/typed interface contract is mandatory. |
| ASLR, `W^X` pure code pages, page sharing, TLB/icache locality | **Irreducible constraint** | *Hardware/security physics:* Page-granular `R-X` / `RW-` (`W^X`) permissions forbid patching shared `.text` pages per process, requiring PC-relative code or per-process writable indirection tables (Multics linkage section, GOT, IAT, chained fixups). |
| Specialization vs. indirection across binary boundaries | **Irreducible trade-off** | *Information-theoretic bound:* Unboxed layout-specialized code requires concrete layouts/bodies at specialization time (compile-time IR, ThinLTO, JIT/install AOT); hiding layout evolution across a binary boundary (Swift resilience, Wasm Canonical ABI) requires runtime indirection or deferred translation. |
| Whole-module interface hash vs. per-item fingerprinting | **Irreducible trade-off** | *Invalidation granularity:* Whole-module keys (`ORB.Mod`) yield minimal $O(1)$ loader code at the cost of false invalidations on additive exports; per-item fingerprints (Crelier 1994) avoid false invalidations at higher metadata/hashing complexity. |

---

### 6. Summary of Executable Verification Probe Findings

Basis: execution

`support/verify_linking_models.py` passes all deterministic model assertions and live Linux `x86_64` ELF checks (GCC 15.2.0, GNU `ld` 2.47, `glibc` 2.43, Python 3.13.15):

- **ELF model:** Confirms BFS scope `["main", "libpreload.so", "libtarget.so", "libstrong.so", "libbase.so"]`, `LD_PRELOAD` intra-DSO preemption of `STV_DEFAULT`, local intra-DSO binding of `STV_PROTECTED`, default `glibc` `dl_dynamic_weak=False` stopping at earlier `STB_WEAK` (vs. `True` continuing to `STB_GLOBAL`), `RTLD_LOCAL` splitting `_ZTI3Foo` while `STB_GNU_UNIQUE` unifies `_ZZ3barvE5cache` and sets `nodelete=True`, and cycle detection on mutual `DT_NEEDED`.
- **Mach-O & PE/COFF models:** Confirms Mach-O `libOrdinal > 0` immunity to `libInterpose.dylib`, opt-in flat preemption, `BIND_SPECIAL_DYLIB_WEAK_LOOKUP` strong-over-weak coalescing, and PE/COFF side-by-side diamond isolation (`crypto_v1.dll` vs. `crypto_v2.dll`).
- **Oberon vs. Crelier models:** Confirms body-only edits pass both, ABI-breaking layout edits and hidden GC pointer additions fail both (`res=3` in Oberon), and monotonic additive exports invalidate Oberon's whole-module key while preserving Crelier per-item client fingerprints.
- **COMDAT model:** Confirms ELF `GRP_COMDAT` yields `4` vs. `16` depending on input order while COFF `SAME_SIZE` and `EXACT_MATCH` reject the mismatch.
- **Live Linux `x86_64` ELF probes:** (1) `GRP_COMDAT` link-order flip produced `42` vs. `99` with exit code `0` and empty stderr; (2) `LD_PRELOAD` flipped `libtarget.so::call_both()` from `1020` to `7720` (`default_fn` hijacked `10→77`, `protected_fn` kept `20`); (3) `dlsym(RTLD_DEFAULT, "plugin_exported_sym")` printed `0 1` across `RTLD_LOCAL` then `RTLD_GLOBAL`.

## Boundaries

- **not examined:** AIX XCOFF, HP-UX SOM, Plan 9 static-only linking, Solaris `-Bdirect`, `STT_GNU_IFUNC` resolver ordering edge cases, ELF symbol versioning (`DT_VERDEF`/`DT_VERNEED`) internals, `dlmopen()` namespace limits, JVM class-file verification, .NET CLR/ReadyToRun, Windows SxS/COM/WinRT, IBM i TIMI install-time translation, and Rust-specific CGU/object mechanics (covered by the five cross-referenced corpus packages).
- **unknown:** Whether any language-neutral binary interface standard can simultaneously deliver zero-overhead cross-compiler generic specialization, ABI-resilient layout evolution, and compact proof-carrying certificates without shipping compiler-internal IR or install-time AOT; distro-wide `-fno-semantic-interposition` speedup distributions beyond published workloads like Fedora/CPython (`5–27%`); and whether a single mechanized operational semantics covers the complete modern `glibc` `ld.so` feature set (`dlmopen`, `RTLD_DEEPBIND`, `STB_GNU_UNIQUE`, `IFUNC`, symbol versioning, TLS relaxation, concurrent `dlopen`/`dlclose`).
- **known not to apply:**
  - *Multics (1968) did not perform static structural type checking at link time:* Daley & Dennis (1968) documents two-part symbolic `<segment>|[entry]` lookup + fault-driven snapping, not type-hashed interfaces.
  - *Clang does not default to full `-fno-semantic-interposition` on ELF `-fPIC`:* `Clang.cpp:6079-6080` defaults to `-fhalf-no-semantic-interposition` (IPO allowed, no `.Lfoo$local` aliases).
  - *`STB_GLOBAL` does not override an earlier `STB_WEAK` under default `glibc`:* `dl-lookup.c:482-498` stops on the first `STB_WEAK` unless `LD_DYNAMIC_WEAK` is set.
  - *Mach-O two-level namespaces do not eliminate all global symbol scans:* C++ `N_WEAK_DEF` symbols still coalesce process-wide via `BIND_SPECIAL_DYLIB_WEAK_LOOKUP` (`dyld/Loader.cpp:2914-3088`).
- **unsupported:** Cross-compiler or cross-version interchange of C++20 BMIs (Clang/GCC/MSVC); general `dlclose` unloading on `musl` (permanent no-op) or on `glibc` for DSOs with resolved `STB_GNU_UNIQUE` symbols (`NODELETE`) or live per-thread TLS destructors; and content/size-checked COMDAT validation in ELF `SHT_GROUP` (`GRP_COMDAT` specifies signature-only matching).

## Evidence

All sources and executions were observed on `2026-11-19`.

### Normative Specifications and Pinned Sources

| Subject | Coordinates (Repo @ SHA / Path / Symbols / Lines) | Claims Grounded |
|---|---|---|
| **ELF gABI v4.2** | `xinuos/gabi` @ `4ff978d04d78cbd308705a782f34a189118d11cd` — `docsrc/elf/03-sheader.rst:758-840`, `05-symtab.rst:333-349`, `08-dynamic.rst:264-472, 623-631, 860-944` | `SHT_GROUP`/`GRP_COMDAT`, `STV_DEFAULT`/`STV_PROTECTED`, BFS scope, `DF_SYMBOLIC`, `DT_PREINIT_ARRAY`/`DT_INIT_ARRAY` ordering |
| **LLVM / `lld` / Clang** | `llvm/llvm-project` @ `ffcd0a522aedc16a966e3efb9a97a336be8ddb57` — `lld/ELF/InputFiles.cpp:648-664`, `lld/ELF/Symbols.cpp:288-295, 355-386`, `clang/lib/Driver/ToolChains/Clang.cpp:6061-6086`, `llvm/lib/LTO/LTO.cpp:137-143, 406-497`, `llvm/lib/Transforms/IPO/FunctionImport.cpp` | `comdatGroups.try_emplace`, `computeIsPreemptible`, `-fhalf-no-semantic-interposition`, ThinLTO prevailing resolution & cache key |
| **`glibc` `ld.so`** | `bminor/glibc` @ `04e750e75b73957cf1c791535a3f4319534a52fc` — `elf/dl-lookup.c:204-332, 337-519, 761-800`, `elf/dl-init.c:25-127`, `elf/dl-open.c:78-133`, `elf/dl-close.c:174-184, 765-775`, `elf/rtld.c:843-855, 1818-1827` | `LD_PRELOAD` scope order, default `dl_dynamic_weak == 0`, `do_lookup_unique` + `NODELETE`, `_dl_init`, `l_tls_dtor_count` |
| **Apple `dyld-1378`** | `apple-oss-distributions/dyld` @ `fd8d0c4d52320ebf64db34f3cb280310d905c5ae` — `dyld/Loader.cpp:2721-2740, 2832-2850, 2853-3095`, `dyld/JustInTimeLoader.cpp:717-749` | Two-level `libOrdinal`, `BIND_SPECIAL_DYLIB_*`, `weakDefMap`, strong-over-weak coalescing, `cacheWeakDefFixup` |
| **Microsoft PE/COFF** | `MicrosoftDocs/win32` @ `ca8274decead49403d70ceeed4af8d4ca74eaf11` — `desktop-src/Debug/pe-format.md:1104-1125, 1246-1390, 1550-1566` | 6 `IMAGE_COMDAT_SELECT_*` modes, `.idata` ILT/IAT & Delay-Load, `.edata` `IMAGE_EXPORT_DIRECTORY` |
| **Wasm Component Model** | `WebAssembly/component-model` @ `585526aa1f2c7f76f07557d16e265dede38b3acb` — `design/mvp/Explainer.md:33-97, 248-273, 722-730, 929-969` | Typed WIT imports/exports, `canon lift`/`canon lower`, explicit instantiation, virtualization, multi-version coexistence |
| **Swift ABI Docs** | `swiftlang/swift` @ `466f30162134b2c16b0f05c05d766cdd151236a5` — `docs/LibraryEvolution.rst:115-207`, `docs/ABI/TypeMetadata.rst:11-20` | Resilient layouts, Type Metadata, Value Witness Tables, `@frozen`, `@inlinable` |

### Primary Literature & Documentation

- Daley & Dennis (1968), CACM 11(5):306–312, DOI `10.1145/363095.363139` (`multicians.org/daley-dennis.html`).
- Swinehart, Zellweger, Beach & Hagmann (1986), ACM TOPLAS 8(4):419–490, DOI `10.1145/6465.6469`; predecessor *The Structure of Cedar* (SIGPLAN 1985).
- Gingell, Lee, Dang & Weeks (1987), *Shared Libraries in SunOS*, USENIX Summer 1987, pp. 131–147.
- Stroustrup (1988), *Type-safe Linkage for C++*, Computing Systems 1(4):371–403 (`usenix.org/publications/compsystems/1988/fall_stroustrup.pdf`).
- Wirth & Gutknecht (1992/2013), *Project Oberon* (`people.inf.ethz.ch/wirth/ProjectOberon/Sources/{ORB,Modules}.Mod.txt`).
- Ritchie (1993), *The Development of the C Language*, HOPL-II, DOI `10.1145/155360.155580` (`bell-labs.com/usr/dmr/www/chist.html`).
- Crelier (1994), *Separate Compilation and Module Extension*, ETH Diss. 10650, DOI `10.3929/ethz-a-000945227`.
- Cardelli (1997), POPL 1997, DOI `10.1145/263699.263735`; Levine (1999), *Linkers and Loaders*, ISBN `978-1558604964`; Drepper (2003/2005), *ELF Handling For Thread-Local Storage*; musl wiki (`wiki.musl-libc.org/functional-differences-from-glibc.html`).
- Pike (2012), *Go at Google*, SPLASH 2012 (`go.dev/talks/2012/splash.article`); Johnson, Amini & Li (2017), *ThinLTO*, CGO 2017, DOI `10.1109/CGO.2017.7863733`; Clang docs (`clang.llvm.org/docs/StandardCPlusPlusModules.html`).

### Execution Record

- **Probe:** `python3 -B reports/object-files-linkers-loaders-and-separate-compilation-history/support/verify_linking_models.py`
- **Host (`2026-11-19`):** Linux `x86_64`, Python 3.13.15, GCC 15.2.0, GNU `ld` 2.47, `glibc` 2.43. Exit code `0`:
  - `elf_model`: all 7 assertions `true` (`startup_bfs_scope = ["main", "libpreload.so", "libtarget.so", "libstrong.so", "libbase.so"]`).
  - `macho_pe_models`: all 3 assertions `true`.
  - `oberon_crelier_models`: all 4 assertions `true`.
  - `comdat_model`: `elf_comdat_order_ab_value = 4`, `elf_comdat_order_ba_value = 16`, COFF `SAME_SIZE` & `EXACT_MATCH` caught ODR.
  - `live_elf_probes`: `status = "executed"`, `arch = "x86_64"`, `live_comdat_ab_vs_ba = [42, 99]`, `live_preload_base_vs_interposed = [1020, 7720]`, `live_dlopen_local_vs_global_visible = "0 1"`.

## Revalidation

1. **Historical literature (1968–2017):** Immutable primary records; revalidate only if errata are published.
2. **Executable probe:** Re-run `python3 -B reports/object-files-linkers-loaders-and-separate-compilation-history/support/verify_linking_models.py` on any target toolchain to recheck both deterministic models and live Linux ELF `cc`/`ld`/`ld.so` invariants.
3. **Narrow upstream diffs:** Check `xinuos/gabi` (`03-sheader.rst`, `05-symtab.rst`, `08-dynamic.rst`) past `4ff978d04d78cbd308705a782f34a189118d11cd`; `llvm/llvm-project` (`lld/ELF/{InputFiles,Symbols}.cpp`, `clang/lib/Driver/ToolChains/Clang.cpp`, `llvm/lib/LTO/LTO.cpp`) past `ffcd0a522aedc16a966e3efb9a97a336be8ddb57`; `bminor/glibc` (`elf/dl-{lookup,init,close}.c`) past `04e750e75b73957cf1c791535a3f4319534a52fc`; `apple-oss-distributions/dyld` (`dyld/Loader.cpp`) past `fd8d0c4d52320ebf64db34f3cb280310d905c5ae`; `MicrosoftDocs/win32` (`pe-format.md`) past `ca8274decead49403d70ceeed4af8d4ca74eaf11`; `swiftlang/swift` (`docs/LibraryEvolution.rst`) past `466f30162134b2c16b0f05c05d766cdd151236a5`; and `WebAssembly/component-model` (`design/mvp/Explainer.md`) past `585526aa1f2c7f76f07557d16e265dede38b3acb`.
