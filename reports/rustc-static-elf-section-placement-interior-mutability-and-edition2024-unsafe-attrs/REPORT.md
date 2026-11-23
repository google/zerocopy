# `rustc` Static ELF Section Placement Under Interior Mutability and Relocations, and Edition 2024 `#[unsafe(...)]` Linker Attribute Safety Enforcement

## Summary

Across `rustc` MIR/CTFE interning (`compiler/rustc_const_eval/src/interpret/intern.rs`), LLVM codegen (`compiler/rustc_codegen_llvm/src/consts.rs`), and LLVM ELF section selection (`llvm/lib/Target/TargetLoweringObjectFile.cpp` and `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp`), `static` placement in ELF relocatable objects is determined neither by the syntactic absence of `static mut` alone nor purely by zero-initialization. Instead, three structural properties plus the target relocation model form a deterministic classifier `(mutOrInt, hasReloc, isZero, relocModel)` across four ELF output families (`.rodata`, `.data.rel.ro`, `.data`, and `.bss`) and two section types (`SHT_PROGBITS` vs. `SHT_NOBITS`):

1. **Freeze-sensitivity during const interning decides `isConstant()` on LLVM globals (`source`, `execution`).** In `intern_const_alloc_recursive`, `InternKind::Static(Mutability::Not)` assigns `base_mutability = Mutability::Not` if and only if `ret.layout.ty.is_freeze(*ecx.tcx, ecx.typing_env)` is `true`, and `Mutability::Mut` otherwise (`compiler/rustc_const_eval/src/interpret/intern.rs:222-235`); nested promoted/tail allocations receive `inner_mutability = Mutability::Not`, whereas `InternKind::Static(Mutability::Mut)` marks both root and nested allocations `Mutability::Mut` (`L236-240`). `codegen_static_item` forwards that root mutability to LLVM IR via `if alloc.mutability.is_not() { llvm::set_global_constant(g, true); }` (`compiler/rustc_codegen_llvm/src/consts.rs:537-539` in `rust-lang/rust@0259d5e9a81c6af08e40f8c204f2c0c41dca1647`, identical at `L474-476` of `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). Consequently, any non-`mut` `static` containing `UnsafeCell`, `AtomicU64`, or `Mutex` lowers to an LLVM `global` (non-`constant`) just like `static mut`, whereas nested immutable allocations remain `constant`.
2. **Immutable all-zero statics do NOT enter `.bss`; only mutable or interior-mutable all-zero statics without relocations enter `.bss` (`source`, `execution`).** LLVM's `isSuitableForBSS` (`llvm/lib/Target/TargetLoweringObjectFile.cpp:82-99`) rejects any global with `GV->isConstant()` (`"Leave constant zeros in readonly constant sections, so they can be shared."`, `L90-91`), non-null/non-undef initializer (including relocations), or an explicit `section`. Thus `pub static CAT2_IMM_ALL_ZERO: [u8; 64] = [0u8; 64]` emits into `.rodata.CAT2_IMM_ALL_ZERO` (`SHT_PROGBITS`, `SHF_ALLOC` = `A`), while `SyncCell<u64>` / `AtomicU64` zero-initialized emit into `.bss.*` (`SHT_NOBITS`, `SHF_WRITE | SHF_ALLOC` = `WA`). Assigning an explicit `#[unsafe(link_section = ".bss")]` to a non-zero `static` compiles to LLVM IR cleanly but fails at object emission with `error: BSS section '.bss...' cannot have non-zero bytes`.
3. **Immutable pointer-bearing statics split on `relocModel`, whereas interior-mutable pointer-bearing statics NEVER use `.data.rel.ro` (`source`, `execution`).** In `TargetLoweringObjectFile::getKindForGlobal` (`L300-368`), an immutable global whose constant initializer `C->needsRelocation()` is `true` selects `SectionKind::getReadOnlyWithRel()` -> `.data.rel.ro.*` (`PROGBITS`, `WA` + `.rela.data.rel.ro.*`) under PIC, so `ld.so` can patch dynamic relocations before `PT_GNU_RELRO` remaps those pages read-only (`PROT_READ`) prior to user execution; under `-C relocation-model=static`, it stays in `.rodata.*` (`PROGBITS`, `A` + `.rela.rodata.*`). Conversely, a `SyncCell<&'static u64>` omits `constant` in LLVM IR, hits `!GVar->isConstant()`, and unconditionally enters `.data.*` (`PROGBITS`, `WA`), remaining writable across the entire process lifetime.
4. **Explicit `#[unsafe(link_section = ".rodata")]` on an interior-mutable static silently poisons section/segment protections (`source`, `execution`).** LLVM's `getELFKindForNamedSection` (`llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp:456-496`) infers `SectionKind::getBSS()` for `.bss*` and TLS kinds for `.tdata*`/`.tbss*`, but leaves `.rodata` untouched. Placing `SyncCell<u64>` into `".rodata"` retains `SectionKind::getData()`, emitting input section `.rodata` with `WA`. At link time on `x86_64-unknown-linux-gnu`:
   - `GNU ld 2.47` merges `.rodata` flags to `WA` AND drops `PT_GNU_RELRO` entirely (`15 -> 13` program headers), putting `.rodata`, `.data.rel.ro`, `.got`, `.init_array`, `.data`, and `.bss` into a single `RW` `PT_LOAD` segment so writes to `.rodata` scalars, `.rodata` zero arrays, and `.data.rel.ro` records all succeed instead of trapping with `SIGSEGV`;
   - `LLD 22.1.6` (`rust-lld`) promotes output `.rodata` to `WAMS` and moves it into an `RW` `PT_LOAD` segment (writes to `.rodata` survive) while preserving `PT_GNU_RELRO` (writes to `.data.rel.ro` still `SIGSEGV`).
5. **Edition 2024 `#[unsafe(...)]` attribute gating enforces an explicit front-end witness while preserving codegen identity (`normative`, `source`, `execution`).** `NoMangleParser`, `ExportNameParser` (`compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs`), and `LinkSectionParser` (`attributes/link_attrs.rs`) declare `unsafe_since: Some(Edition2024)`. `check_attribute_safety` (`safety.rs:51-54`) triggers `UnsafeAttrOutsideUnsafe` iff `path_span.edition() >= unsafe_since`. In `rustc 1.98.0-nightly (14210df0e)`, Edition 2021 bare attributes and Edition 2024 `#[unsafe(...)]` attributes yield byte-for-byte identical LLVM IR (`sha256: e1c7de84...`) and ELF `.o` files (`sha256: 0fb74abe...`), and `-F unsafe-code` rejects both (`unsafe(no_mangle)` and bare `no_mangle`). Because `check_attribute_safety` checks `path_span.edition()` rather than the downstream crate edition, a macro defined in an Edition 2021 dependency can emit bare `#[no_mangle]` inside an Edition 2024 crate without error.
6. **Mechanized Lean 4 model and Anneal boundary (`source`, `derived`).** A standalone 1,412-line `Lean v4.34.1` development (`support/StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean`) with zero `sorry`, zero `omega`/`bv_decide`/`native_decide`/`Classical.choice`, zero `partial def`, and zero `._unsafe_rec` compiler auxiliaries machine-checks the 5/6-case classifier (`classifyStaticSection`), two-phase relocation + `PT_GNU_RELRO` freeze + post-RELRO runtime write safety (`wellTypedTrace_safe_and_preserves_immutable`), 5 explicit fault/contamination/macro counterexamples (`ce1`–`ce5`), and Edition 2024 attribute codegen equivalence (`codegen_equivalence_2021_bare_to_2024_unsafe`). Meanwhile, inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean`, `trusted/rustc-capture/src/driver.rs`) establishes that Anneal models single-function post-cleanup MIR `Body`/`Program` units (`MirProfileVersion == 1`, 64-bit) and does not represent module-level `static` items, ELF section/linkage attributes, or cross-static relocations.

## Applicability

This report relates nine durable upstream subjects recorded in `REPORT.json`, distinguishing directly executed behavior from source-audited upstream HEAD revisions and mathematically modeled properties:

| Subject | Exact Revision / Version | Role in This Report | Applicability Scope & Relationship |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`) | Executed compiler (`execution` + `source`) | All compiler CLI outputs, LLVM IR globals, `.o`/`.so`/PIE binaries, and `SIGSEGV` runtime exits in `support/probe_results.json` were produced by this compiler on `x86_64-unknown-linux-gnu`. |
| `rust-lang/rust` | `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` (`HEAD` as of `2026-11-23`) | Upstream source (`source`) | Audited and diffed against `14210df0e`. Static mutability forwarding (`consts.rs`, `intern.rs`) and `path_span.edition()` attribute gating match behaviorally; `UNSAFE_CODE` emission moved into `safety.rs` (`L116-126`) and generic `no_mangle`/`export_name` became a hard error (`rustc_lint/src/builtin.rs:859`). |
| `llvm/llvm-project` | `fc4aad7b5db3fff421df9a9637605b9ca5667881` (`llvmorg-22.1.6`) | Executed compiler LLVM baseline (`source`) | File hashes for `TargetLoweringObjectFile.cpp` and `TargetLoweringObjectFileImpl.cpp` match `rust-lang/llvm-project@08c84e69a` byte-for-byte. |
| `llvm/llvm-project` | `229f673cd9cd804c579440dbd6e9cc0509f3a3c3` (`HEAD` as of `2026-11-23`) | Upstream LLVM comparison (`source`) | Diffed against `llvmorg-22.1.6`: adds `!metadata_section_kind` and GOFF special-casing while keeping the ELF `.rodata`/`.data.rel.ro`/`.data`/`.bss` classification logic equivalent. |
| `rust-lang/llvm-project` | `08c84e69a84d95936296dfcab0e38b34100725d5` (`LLD 22.1.6`) | Executed linker + Rust LLVM fork (`execution` + `source`) | Supplies bundled `rust-lld` (`Linker: LLD 22.1.6`) executed in PIE linking and `llvm-readobj`/`llvm-objdump` inspection. |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Language reference (`normative` / `documentation`) | Defines static read-only placement semantics (`r[items.static.read-only]`, `r[items.static.sync]`, `r[items.static.mut]`) and ABI attribute contracts (`r[abi.no_mangle.*]`, `r[abi.link_section.*]`, `r[abi.export_name.*]`). |
| GNU Binutils (`ld` / `readelf`) | `2.47` (`GCC Debian 15.2.0-14` wrapper) | Executed ELF linker & inspector (`execution`) | Executed as default host linker (`gnu_ld_bfd`) producing PIE ELF binaries and `readelf -S -W`, `-s -W`, `-l -W`, `-r -W` dumps. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Verification boundary subject (`source`) | Audited to characterize the boundary between Anneal's MIR AST/capture scope and module-level static ELF placement/attributes. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Theorem prover kernel (`derived`) | Executes kernel typechecking of `support/StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean` (`support/lean_check_receipt.json`). |

All empirical execution results apply directly to ELF targets on `x86_64-unknown-linux-gnu` under `--edition 2021` / `--edition 2024`, PIC (default PIE/cdylib codegen) vs. `-C relocation-model=static`, `-C opt-level=0/2`, and GNU `ld.bfd` `2.47` vs. `rust-lld` `22.1.6`. Behavior on non-ELF object formats (Mach-O, COFF/PE, Wasm, XCOFF, GOFF), targets where `-C relocation-model=ropi`/`rwpi` is active, target architectures with constant pointer-authentication relocations (`containsConstantPtrAuth`), LTO/ThinLTO bitcode merges across differing linkers, and editions prior to 2021 beyond the parser rule is determined by source inspection alone or marked out of scope under **Boundaries**.

**Relation between the Lean formalization and compiler subjects (`derived` modeling bridge):** `StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean` is a mathematical abstraction written directly against the audited semantics of `intern.rs`, `consts.rs`, `TargetLoweringObjectFile.cpp`, `safety.rs`, `codegen_attrs.rs`, `link_attrs.rs`, `codegen_ssa/src/codegen_attrs.rs`, and `symbol_export.rs`. It does **not** verify LLVM C++ or `rustc` Rust source code by extraction or translation validation; rather, every theorem proved in Lean is conditional on the faithful correspondence of its abstract `classifyStaticSection`, `loadProgram`, `applyAllRelocs`, `applyRelroProtect`, `execRuntimeTrace`, and `checkAttributeSafety` definitions to the audited compiler stages and linker behaviors. Where real toolchains can deviate from that clean idealized pipeline (e.g., cross-edition macro expansion or `#[unsafe(link_section = ".rodata")]` causing GNU `ld` `2.47` to drop `PT_GNU_RELRO`), the Lean model explicitly captures the violation as counterexamples rather than hiding it under an implicit hypothesis.

## Findings

### 1. Normative Model and Rust Frontend Rules for Statics

`Basis: normative (rust-lang/reference) + source (rust-lang/rust)`

In the Rust Reference (`src/items/static-items.md` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), static items represent single program-lifetime allocations rather than inlineable value definitions (`r[items.static.intro]`):

- **Disjointness vs. immutable sharing (`r[items.static.storage-disjointness]`, `src/items/static-items.md:19`):** Non-zero-sized `static` allocations are disjoint from other `static`, heap, and stack allocations, except that immutable `static` storage may overlap allocations without a unique address such as promoted values and `const` items.
- **Read-only eligibility (`r[items.static.read-only]`, `L28`):** "Non-`mut` static items that contain a type that is not interior mutable may be placed in read-only memory."
- **Thread-safety check (`wfcheck.rs` & `check.rs`, `rust-lang/rust` HEAD `0259d5e9a`):** During HIR typechecking, `check_item_type` (`compiler/rustc_hir_analysis/src/check/check.rs:804-820`) runs `check_static_inhabited`, `check_static_linkage`, and `wfcheck::check_static_item(tcx, def_id, ty, /* should_check_for_sync */ true)`. Inside `wfcheck.rs:1258-1289`, non-foreign `static` items require `Sized` and, whenever `!is_foreign_item && mutability == Mutability::Not && !is_thread_local`, enforce `ty: Sync`; `static mut` items skip `Sync` (`r[items.static.mut.sync]`) and instead gate reads/writes behind `unsafe` blocks (`r[items.static.mut.safety]`). Notice that `#[unsafe(link_section)]` or custom `import_linkage` adds `LinkageType` validation (`check.rs:750-759` only for `import_linkage`), without verifying linker section permissions.

### 2. Freeze-Sensitive Const Interning and LLVM `set_global_constant` Forwarding

`Basis: source (rust-lang/rust@0259d5e9a, rust-lang/rust@14210df0e) + execution`

The bridge between Rust's type-level interior mutability and LLVM's `constant` vs. `global` IR marker occurs across two compiler modules whose logic is identical across `14210df0e` (`rustc 1.98.0-nightly`) and `0259d5e9a` (`HEAD`):

1. **CTFE interning (`compiler/rustc_const_eval/src/interpret/intern.rs:215-241`):** `intern_const_alloc_recursive` separates root allocation mutability from nested allocations:

```rust
    let (base_mutability, inner_mutability, is_static) = match intern_kind {
        InternKind::Constant | InternKind::Promoted => {
            (Mutability::Not, Mutability::Not, false)
        }
        InternKind::Static(Mutability::Not) => {
            (
                // Outermost allocation is mutable if `!Freeze` i.e. contains interior mutable types.
                if ret.layout.ty.is_freeze(*ecx.tcx, ecx.typing_env) {
                    Mutability::Not
                } else {
                    Mutability::Mut
                },
                // Inner allocations are never mutable. They can only arise via the "tail
                // expression" / "outer scope" rule, and we treat them consistently with `const`.
                Mutability::Not,
                true,
            )
        }
        InternKind::Static(Mutability::Mut) => {
            (Mutability::Mut, Mutability::Mut, true)
        }
    };
```

Here `Ty::is_freeze` returns `false` if and only if the type contains any `UnsafeCell<T>` (including wrappers such as `AtomicU64`, `Cell<T>`, `Mutex<T>`, or `SyncCell<T>`) outside indirect indirections (`&T`, `&mut T`, `*const T`, `*mut T`, or ZST markers such as `PhantomData`). Consequently:
- A `static` of type `ImmRelocRecord { tag: u64, target: &'static u64 }` IS `Freeze`, so `base_mutability = Mutability::Not`.
- A `static` of type `SyncCell<&'static u64>` or `AtomicU64` is `!Freeze`, so `base_mutability = Mutability::Mut`, even though declared without `mut`.
- A `static mut` marks both `base_mutability` and `inner_mutability` as `Mutability::Mut`.

2. **LLVM IR codegen (`compiler/rustc_codegen_llvm/src/consts.rs:536-539` HEAD; `L473-476` executed `14210df0e`):** In `codegen_static_item`, after constructing the initializer byte/pointer struct via `const_alloc_to_llvm` and applying `set_global_alignment` + `llvm::set_initializer(g, v)`:

```rust
        // Forward the allocation's mutability (picked by the const interner) to LLVM.
        if alloc.mutability.is_not() {
            llvm::set_global_constant(g, true);
        }
```

Meanwhile, `static_addr_of_impl` (`consts.rs:341` HEAD) unconditionally sets `llvm::set_global_constant(gv, true)` for constant/promoted addresses. Afterward, `codegen_static_item` forwards any `#[unsafe(link_section = "...")]` directly to LLVM via `base::set_link_section(g, attrs)` (`consts.rs:571` HEAD; `L506` in `14210df0e`, which wrapped `set_link_section` inside the `else` branch of `if target.is_like_wasm ...` — identical for ELF targets), and registers `USED_COMPILER` -> `llvm.compiler.used` vs. `USED_LINKER` -> `llvm.used` (`L649-677` HEAD, `L511-538` `14210df0e`).

### 3. LLVM 5/6-Category ELF Section Classifier (`isSuitableForBSS` + `getKindForGlobal`)

`Basis: source (llvm/llvm-project@fc4aad7b5, 229f673cd; rust-lang/llvm-project@08c84e69a) + execution`

Once `rustc` emits an LLVM `GlobalVariable`, LLVM's `TargetLoweringObjectFile::getKindForGlobal` (`llvm/lib/Target/TargetLoweringObjectFile.cpp:277-368` in `llvmorg-22.1.6`; `L280-379` in HEAD `229f673cd`) and `TargetLoweringObjectFileImpl.cpp` (`L456-562, 616-632, 822-869`) completely govern ELF section placement, `sh_type`, `sh_flags`, and `.rela.*` generation when no explicit `section` attribute overrides placement:

1. **The `isSuitableForBSS` gate (`TargetLoweringObjectFile.cpp:82-99`):**
```cpp
static bool isSuitableForBSS(const GlobalVariable *GV) {
  const Constant *C = GV->getInitializer();

  // Must have zero initializer.
  if (!isNullOrUndef(C))
    return false;

  // Leave constant zeros in readonly constant sections, so they can be shared.
  if (GV->isConstant())
    return false;

  // If the global has an explicit section specified, don't put it in BSS.
  if (GV->hasSection())
    return false;

  // Otherwise, put it in BSS!
  return true;
}
```
Notice the ordering inside `getKindForGlobal`: `if (isSuitableForBSS(GVar) && !TM.Options.NoZerosInBSS)` runs BEFORE `if (GVar->isConstant())`, yet because `isSuitableForBSS` returns `false` on `GV->isConstant()`, an immutable all-zero `static` (`static Z: [u8; 64] = [0; 64]`) is **excluded from `.bss`**, falls into `if (GVar->isConstant())` (`!C->needsRelocation()`), and enters `.rodata.*` (`SHT_PROGBITS`, `SHF_ALLOC` = `A`). LLVM's rationale (`L89`) is read-only page sharing (and mergeability/hardware write protection), which would be violated by `.bss` (`SHF_WRITE | SHF_ALLOC`). Conversely, zero-initialized `!Freeze` (`AtomicU64::new(0)`, `SyncCell(UnsafeCell::new(0))`) and `static mut Z: u64 = 0` have `GV->isConstant() == false` and satisfy `isNullOrUndef(C) == true` (zeroinitializer with no relocations), so they enter `.bss.*` (`SHT_NOBITS`, `WA`), occupying zero bytes in the object file.

2. **The constant-global relocation branch (`TargetLoweringObjectFile.cpp:300-367` in `llvmorg-22.1.6`; `L308-378` in HEAD):**
When `GVar->isConstant()` is `true`:
- **No relocations (`!C->needsRelocation()`):** Returns `SectionKind::getReadOnly()` (or `MergeableConst*` / `Mergeable*CString` if `hasGlobalUnnamedAddr()`), mapped by `getSectionPrefixForGlobal` (`TargetLoweringObjectFileImpl.cpp:619-620`) to `.rodata` (or `.lrodata` for large globals), `SHT_PROGBITS`, `SHF_ALLOC` (`A`). Note that `CAT1_IMM_SCALAR: u64 = 42` in `probe_results.json` has `local_unnamed_addr` vs non-unnamed_addr (`@CAT1_IMM_SCALAR = constant ...` because `&CAT1_IMM_SCALAR` was taken!) — either way, in `.o` under `-fdata-sections`-style unique section naming, it emits `.rodata.CAT1_IMM_SCALAR` (`PROGBITS`, `A`).
- **Relocations present (`C->needsRelocation()`):**
  - Under PIC (`Reloc::PIC_` with `needsDynamicRelocation()` true, or any constant containing PtrAuth): returns `SectionKind::getReadOnlyWithRel()`, mapped at `TargetLoweringObjectFileImpl.cpp:629-630` to `.data.rel.ro.*`, `SHT_PROGBITS`, `SHF_WRITE | SHF_ALLOC` (`WA`), paired with `.rela.data.rel.ro.*` (`SHT_RELA`, `SHF_INFO_LINK` = `I`).
  - Under static/non-dynamic relocation models (`ReloModel == Reloc::Static || ReloModel == Reloc::ROPI || ReloModel == Reloc::RWPI || ReloModel == Reloc::ROPI_RWPI || !C->needsDynamicRelocation()` when `!containsConstantPtrAuth(C)`): returns `SectionKind::getReadOnly()`, emitting `.rodata.*` (`PROGBITS`, `A`) paired with `.rela.rodata.*`, because the static linker patches every address at link time with no runtime `ld.so` mutation required.

3. **The non-constant branch (`TargetLoweringObjectFile.cpp:366-367`):** If `!GVar->isConstant()` and `isSuitableForBSS` is false (either non-zero initializer OR initializer contains a relocation even if numeric bytes happen to be zero, because a global pointer relocation fails `isNullOrUndef(C)`!), `getKindForGlobal` falls through to `return SectionKind::getData()`, emitting `.data.*` (`SHT_PROGBITS`, `WA`, plus `.rela.data.*` if relocations exist). Crucially, **`SyncCell<&'static u64>` NEVER reaches `.data.rel.ro`**, because only `GVar->isConstant()` ever checks `getReadOnlyWithRel()`. Putting `SyncCell<&'static u64>` into `.data.rel.ro` would cause `PT_GNU_RELRO` to `mprotect(..., PROT_READ)` it before `main`, trapping subsequent interior mutations with `SIGSEGV`.

| Category | Rust `static` Shape (Default Visibility / `#[unsafe(no_mangle)]`) | CTFE `alloc.mutability` | LLVM IR Global Modifier | Reloc Model | ELF Output Section Family | `sh_type` | `sh_flags` | Relocation Section |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Cat 1** | Immutable scalar / struct (`!UnsafeCell`, non-zero) | `Not` (`Freeze`) | `constant` | PIC & Static | `.rodata.<sym>` | `PROGBITS` | `A` | None |
| **Cat 2** | Immutable all-zero array (`[u8; 64] = [0; 64]`) | `Not` (`Freeze`) | `constant zeroinitializer` | PIC & Static | `.rodata.<sym>` (NOT `.bss`!) | `PROGBITS` | `A` | None |
| **Cat 3a** | Immutable w/ `&'static T` relocation (PIC / PIE / `cdylib`) | `Not` (`Freeze`) | `constant <{ ..., ptr @... }>` | PIC | `.data.rel.ro.<sym>` | `PROGBITS` | `WA` (frozen `R` post-RELRO) | `.rela.data.rel.ro.<sym>` |
| **Cat 3b** | Immutable w/ `&'static T` relocation (`-C relocation-model=static`) | `Not` (`Freeze`) | `constant <{ ..., ptr @... }>` | Static | `.rodata.<sym>` | `PROGBITS` | `A` | `.rela.rodata.<sym>` |
| **Cat 4** | Interior-mutable non-zero (`AtomicU64::new(7)`, `SyncCell(8)`) | `Mut` (`!Freeze`) | `global` | PIC & Static | `.data.<sym>` | `PROGBITS` | `WA` | None |
| **Cat 5** | Interior-mutable all-zero (`AtomicU64::new(0)`, `SyncCell(0)`) | `Mut` (`!Freeze`) | `global zeroinitializer` | PIC & Static | `.bss.<sym>` | `NOBITS` | `WA` | None |
| **Cat 6** | Interior-mutable w/ `&'static T` (`SyncCell<&'static u64>`) | `Mut` (`!Freeze`) | `global ptr @...` | PIC & Static | `.data.<sym>` (NEVER `.data.rel.ro`) | `PROGBITS` | `WA` | `.rela.data.<sym>` |
| **Cat 7** | `static mut` non-zero / all-zero | `Mut` | `global` | PIC & Static | `.data.<sym>` / `.bss.<sym>` | `PROGBITS` / `NOBITS` | `WA` | If relocs |

Live execution (`support/probe_results.json`, `group_b_static_five_category_sections`, `rustc 1.98.0-nightly 14210df0e`) reproduced every single row above identically in both LLVM IR (`@CAT1_IMM_SCALAR`, `@CAT2_IMM_ALL_ZERO`, `@CAT3_IMM_WITH_RELOC`, `@CAT4A_ATOMIC_NONZERO`, `@CAT4B_UNSAFECELL_NONZERO`, `@CAT5A_ATOMIC_ZERO`, `@CAT5B_UNSAFECELL_ZERO`, `@CAT6_UNSAFECELL_WITH_RELOC`, `@CAT7A_STATIC_MUT_NONZERO`, `@CAT7B_STATIC_MUT_ZERO`) and ELF sections/relocations in `sec5.o` across `reloc_model_pic` and `reloc_model_static`:
- Under PIC: `.data.rel.ro.CAT3_IMM_WITH_RELOC` (`PROGBITS`, `WA`, size `16`) + `.rela.data.rel.ro.CAT3_IMM_WITH_RELOC` (`R_X86_64_64` at `0x8` -> `CAT1_IMM_SCALAR + 0`), and `.data.CAT6_UNSAFECELL_WITH_RELOC` (`PROGBITS`, `WA`, size `8`) + `.rela.data.CAT6_UNSAFECELL_WITH_RELOC` (`R_X86_64_64` at `0x0` -> `CAT1_IMM_SCALAR + 0`).
- Under `-C relocation-model=static`: `CAT3_IMM_WITH_RELOC` moved to `.rodata.CAT3_IMM_WITH_RELOC` (`PROGBITS`, `A`, size `16`) + `.rela.rodata.CAT3_IMM_WITH_RELOC`, while `CAT6_UNSAFECELL_WITH_RELOC` remained in `.data.CAT6_UNSAFECELL_WITH_RELOC` (`PROGBITS`, `WA`).

### 4. Explicit `#[unsafe(link_section)]` ELF Flag Inheritance and Cross-Section RELRO Contamination

`Basis: source (llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp) + execution`

When a `static` carries `#[unsafe(link_section = "...")]` (`GV->hasSection() == true`), LLVM routes it through `TargetLoweringObjectFileELF::getExplicitSectionGlobal` -> `selectExplicitSectionGlobal` (`TargetLoweringObjectFileImpl.cpp:822-875`):

```cpp
  // Infer section flags from the section name if we can.
  Kind = getELFKindForNamedSection(SectionName, Kind);

  unsigned Flags = getELFSectionFlags(Kind, TM.getTargetTriple());
...
  MCSectionELF *Section = Ctx.getELFSection(
      SectionName, getELFSectionType(SectionName, Kind), Flags, ...);
```

Here the incoming `Kind` is computed by `SectionKind::getReadOnly()` if `GVar->isConstant()` and `SectionKind::getData()` if `!GVar->isConstant()` (determined via `getKindForGlobal` / caller classification, though `isSuitableForBSS` returns `false` when `GV->hasSection()`). Inside `getELFKindForNamedSection` (`L456-496`), LLVM checks only special coverage/metadata names, `.bss` / `.bss.*` / `.sbss*` (forcing `SectionKind::getBSS()` -> `SHT_NOBITS`, `WA`), `.tdata*` (`ThreadData`), and `.tbss*` (`ThreadBSS`). **It does NOT canonicalize `.rodata` to `SectionKind::getReadOnly()`!** Meanwhile, MC enforces type/flag compatibility when emitting `.bss` sections.

This asymmetry produces four empirical behaviors observed directly in `probe_results.json`:

1. **Custom section names inherit Rust mutability flags (`sec5.o`):**
   - `CAT8A_LINKSEC_IMM: u64 = 123` with `link_section = ".custom_sec_imm"` -> `.custom_sec_imm` (`PROGBITS`, `A`, size `8`).
   - `CAT8B_LINKSEC_CELL: SyncCell<u64> = 456` with `link_section = ".custom_sec_mut"` -> `.custom_sec_mut` (`PROGBITS`, `WA`, size `8`).
2. **Immutable zero scalar forced into `.bss.custom_imm` vs. non-zero rejection:**
   - `CAT8C_LINKSEC_DOT_BSS_IMM: u64 = 0` with `link_section = ".bss.custom_imm"` -> emits LLVM IR `constant [8 x i8] zeroinitializer, section ".bss.custom_imm"`, then `getELFKindForNamedSection` overrides `Kind` to `BSS`, yielding `.bss.custom_imm` (`NOBITS`, `WA`, size `8`).
   - Non-zero `u64 = 0xDEAD_BEEF` with `#[unsafe(link_section = ".bss")]` or `".bss.custom_nz"` passes Rust frontend parsing and LLVM IR lowering, then aborts at object emission (`rc = 1`): `error: BSS section '.bss' cannot have non-zero bytes` (tested cleanly in `nonzero_in_bss_rejected`).
3. **`SyncCell<u64>` forced into `".rodata"` emits `WA` `.rodata` (`CAT8D_LINKSEC_CELL_IN_RODATA`):**
   - In `sec5.o`, `#[unsafe(link_section = ".rodata")] pub static CAT8D_LINKSEC_CELL_IN_RODATA: SyncCell<u64> = SyncCell(UnsafeCell::new(789))` emits input section `.rodata` with **`PROGBITS`, `WA`**!
4. **Full-binary segment & `PT_GNU_RELRO` fallout (`linked_pie_clean` vs. `linked_pie_with_rodata_cell_hazard`):**
   Adding a single `#[unsafe(no_mangle)] #[unsafe(link_section = ".rodata")] pub static HAZARD_CELL_IN_RODATA: SyncCell<u64>` into an otherwise clean PIE binary (`IMM_SCALAR`, `IMM_ALL_ZERO`, `IMM_RELRO`, `CELL_NONZERO`, `CELL_ZERO`, `ATOMIC_ZERO`, `CELL_REL`) yields drastically different link-time and runtime memory-protection behavior between `GNU ld 2.47` (`ld.bfd`) and `LLD 22.1.6` (`rust-lld`):

| Linked PIE Mode & Linker | Output `.rodata` Flags & Segment | Output `PT_GNU_RELRO` | `check_readonly` | `write_rodata` | `write_rodata_zero` | `write_relro` | `write_cells` | `write_hazard_cell_in_rodata` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Clean PIE + `GNU ld 2.47`** | `PROGBITS`, `A` (`0x43000`, inside `R` `LOAD`) | Present (`0x529b8..0x55000`, `15` phdrs) | `rc=0` (`IMM_OK`) | `rc=-11` (`SIGSEGV`) | `rc=-11` (`SIGSEGV`) | `rc=-11` (`SIGSEGV`) | `rc=0` (`CELLS_OK:88:99:123:99`) | N/A |
| **Clean PIE + `LLD 22.1.6`** | `PROGBITS`, `AMS` (`0x4b90`, inside `R` `LOAD`) | Present (`0x50ce0`, `12` phdrs) | `rc=0` (`IMM_OK`) | `rc=-11` (`SIGSEGV`) | `rc=-11` (`SIGSEGV`) | `rc=-11` (`SIGSEGV`) | `rc=0` (`CELLS_OK:88:99:123:99`) | N/A |
| **Hazard PIE (`WA .rodata`) + `GNU ld 2.47`** | **`WA`** (`0x43000`), merged into **`RW` `LOAD` `04`**! | **ABSENT (`15 -> 13` phdrs!)** | `rc=0` (`IMM_OK`) | **`rc=0` (`UNEXPECTED_SURVIVED`)** | **`rc=0` (`UNEXPECTED_SURVIVED`)** | **`rc=0` (`UNEXPECTED_SURVIVED`!)** | `rc=0` (`CELLS_OK:88:99:123:99`) | `rc=0` (`HAZARD_SURVIVED:777`) |
| **Hazard PIE (`WA .rodata`) + `LLD 22.1.6`** | **`WAMS`** (`0x51770`), moved into **`RW` `LOAD` `05`**! | **Preserved** (`0x4b6c0`, `12` phdrs, `LOAD 04`) | `rc=0` (`IMM_OK`) | **`rc=0` (`UNEXPECTED_SURVIVED`)** | **`rc=0` (`UNEXPECTED_SURVIVED`)** | **`rc=-11` (`SIGSEGV`)** | `rc=0` (`CELLS_OK:88:99:123:99`) | `rc=0` (`HAZARD_SURVIVED:777`) |

In the `GNU ld 2.47` hazard build (`readelf -l -W`), `LOAD` segment `04` collapses `.rodata .eh_frame_hdr .eh_frame .gcc_except_table .note.gnu.property .note.ABI-tag .tdata .init_array .fini_array .data.rel.ro .dynamic .got .data .bss` into a single `RW` mapping (`0x43000`, `MemSiz 0x12ab0`) and eliminates `PT_GNU_RELRO` altogether — allowing runtime writes to corrupt both `.rodata` constants (`IMM_SCALAR`, `IMM_ALL_ZERO`) and `.data.rel.ro` (`IMM_RELRO`) with exit code `0`. Under `LLD 22.1.6`, `.rodata` alone shifts from `R` `LOAD 02` (`AMS`) into `RW` `LOAD 05` (`WAMS`), stripping hardware write protection from every `.rodata` constant and zero array while keeping `PT_GNU_RELRO` intact on `LOAD 04` (`.tdata .fini_array .init_array .data.rel.ro .dynamic .got .got.plt .relro_padding`).

### 5. Edition 2024 `#[unsafe(no_mangle)]` / `#[unsafe(export_name)]` / `#[unsafe(link_section)]` Safety Gate

`Basis: normative (rust-lang/reference) + source (rust-lang/rust@0259d5e9a, 14210df0e) + execution`

Because `#[no_mangle]` / `#[export_name]` can collide in the flat linker symbol namespace (breaking Rust type/ABI assumptions, `r[abi.no_mangle.unsafe]`, `r[abi.export_name.unsafe]`) and `#[link_section]` can violate section permission invariants (as in Finding 4 above, `r[abi.link_section.unsafe]`) without any `unsafe {}` block at call sites, Edition 2024 promotes them to `AttributeSafety::Unsafe { unsafe_since: Some(Edition2024), note }`:

1. **Parser declarations (`rust-lang/rust@0259d5e9a`):**
   - `ExportNameParser` (`compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs:112-152`, `SAFETY` at `L117-120`, `ON_DUPLICATE = WarnButFutureError`): rejects `\0` (`NullOnExport`, `E0648`, `L138-143`) and `""` (`EmptyExportName`, `L144-149`), allows `Static`, `Fn`, `Method(Inherent | Trait { body: true } | TraitImpl)`, warns on `Field | Arm | MacroDef | MacroCall`.
   - `NoMangleParser` (`codegen_attrs.rs:417-436`, `SAFETY` at `L421-424`, `ON_DUPLICATE = Warn`): allows `Fn`, `Static`, `Method(Inherent | TraitImpl)`, `AllowSilent(Target::Const)` (deferred to `InvalidNoMangleItems`), errors on `Closure`/`Param`. Additionally, `rustc_lint/src/builtin.rs` (`L843-905` HEAD) enforces `#[deny(no_mangle_const_items)]` on `const` items and check `requires_monomorphization`: **divergence observed between executed and HEAD `rustc`!** In executed `rustc 1.98.0-nightly (14210df0e)`, `#[unsafe(no_mangle)] pub fn bad_gen<T>(x: T) -> T` compiled with **`rc = 0`** emitting a warning (`#[warn(no_mangle_generic_items)]` on by default), whereas `rust-lang/rust` HEAD (`0259d5e9a`, `rustc_lint/src/builtin.rs:858-863`) calls `cx.tcx.dcx().emit_err(BuiltinNoMangleGeneric { ... })`, making it a hard error. Non-ASCII identifiers fail with `E0754` (`probe_results.json`: `rc = 1`).
   - `LinkSectionParser` (`compiler/rustc_attr_parsing/src/attributes/link_attrs.rs:492-560`, `SAFETY` at `L520-523`, `ON_DUPLICATE = WarnButFutureError`): rejects `\0` (`NullOnLinkSection`), validates only `BinaryFormat::MachO` (`segment,section` via `check_link_section_macho`), leaving `BinaryFormat::Elf` / `Coff` / `Wasm` / `Xcoff` section names completely unvalidated (`L557: {}`).

2. **Gate state machine & macro-span edition carve-out (`compiler/rustc_attr_parsing/src/safety.rs:25-124` HEAD; `L25-115` `14210df0e`):**
   - `(AttributeSafety::Unsafe { .. }, Safety::Unsafe(..))` -> permitted in ALL editions (both Edition 2021 `#[unsafe(...)]` and Edition 2024 `#[unsafe(...)]`).
   - `(AttributeSafety::Unsafe { unsafe_since, .. }, Safety::Default)` -> evaluates `let path_span = attr_path.span; let emit_error = match unsafe_since { None => true, Some(unsafe_since) => path_span.edition() >= unsafe_since };` (`L51-54` HEAD; `L48-51` `14210df0e`). When `emit_error` is `true`, emits `UnsafeAttrOutsideUnsafe` hard error; otherwise emits the allow-by-default future-compatibility lint `UNSAFE_ATTR_OUTSIDE_UNSAFE`.
   - `(AttributeSafety::Normal, Safety::Unsafe(unsafe_span))` -> hard error `InvalidAttrUnsafe` (`error: used is not an unsafe attribute`, `normal_attr_with_unsafe_rejected`, `rc = 1`).
   - **Cross-edition macro bypass (verified live in `cross_edition_macro_ed2021_in_ed2024`):** Because `path_span.edition()` reflects the edition where the attribute name token was created rather than the consumer crate edition (explicitly noted for macro hygiene in `safety.rs:45-50`), compiling a `macro_rules! def_bare_nm` crate under `--edition 2021` that expands `#[no_mangle] pub static $name: u64 = $val;` inside an `--edition 2024` consumer crate succeeds cleanly (`consumer_ed2024_rc = 0`, zero errors) and exports `GLOBAL DEFAULT MACRO_ED2021_IN_2024` in `.rodata.MACRO_ED2021_IN_2024`.

3. **Bit-identical LLVM IR & `.o` emission across Edition 2021 and Edition 2024 (`execution`):**
   Compiling `{NM_STATIC, EXP_STATIC, LS_STATIC, nm_fn}` across `(ed2021_bare, ed2021_unsafe_accepted, ed2024_unsafe_accepted)` produced:
   - Identical LLVM IR SHA-256 across all three: `e1c7de842899b749b6157684aaee7964105066a32c0225c6a2a9e110ea80e534` (`@NM_STATIC`, `@_RNvCsgFjGwHfqpjk_10attr_probe9LS_STATIC ... section ".custom_ro_sec"`, `@custom_exp_sym`);
   - Identical ELF `.o` SHA-256 across all three: `0fb74abebb116b3d888c44ee4c413c5d6f0ec8d0fd483cc6a0b0ab0600b569c0` (`1368` bytes).

4. **`UNSAFE_CODE` refactor (`14210df0e` vs. `0259d5e9a`) & `-F unsafe-code` parity:**
   In executed `rustc 1.98.0-nightly (14210df0e)`, `-F unsafe-code` rejects all three attributes on statics and `no_mangle` functions identically in Edition 2021 bare (`ed2021_bare_forbid_unsafe_code`, `rc = 1`, 4 errors) and Edition 2024 `#[unsafe(...)]` (`ed2024_unsafe_forbid_unsafe_code`, `rc = 1`, 4 errors). Internally, `14210df0e` checked `UNSAFE_CODE` in an early AST visitor (`compiler/rustc_lint/src/builtin.rs:274-337`) covering `ItemKind::Fn`, `ItemKind::Static`, and `AssocItemKind::Fn` (note `L328-336` omitted `sym::link_section` on `AssocItemKind::Fn`!), whereas upstream HEAD `0259d5e9a` unified `UNSAFE_CODE` emission directly into `AttributeParser::check_attribute_safety` (`safety.rs:116-126`) for every `AttributeSafety::Unsafe` item.

5. **`export_name` precedence, reachability, and `cdylib` symbol export (`source`, `execution`):**
   - `process_builtin_attrs` (`compiler/rustc_codegen_ssa/src/codegen_attrs.rs:73, 96, 109-111`) sets `symbol_name = Some(*name)` unconditionally on `AttributeKind::ExportName`, whereas `AttributeKind::NoMangle` sets `symbol_name = Some(name)` only `if codegen_fn_attrs.symbol_name.is_none()`. Live probe `mix_no_mangle_export_both_orders` confirms `UNUSED_ATTRIBUTES` warnings in both orders (`#[unsafe(no_mangle)] #[unsafe(export_name = ...)]` and reversed) while exporting `@exp_wins_first` and `@exp_wins_second` in `.rodata.exp_wins_*`.
   - `CodegenFnAttrs::contains_extern_indicator` (`compiler/rustc_middle/src/middle/codegen_fn_attrs.rs:269-287`) returns `true` if `symbol_name.is_some()` (including `no_mangle`/`export_name`) or external `linkage`, but **ignores `link_section`**. In `reachable.rs:435-458` and `symbol_export.rs:35-53, 634-660`, only `contains_extern_indicator()` promotes `symbol_export_level` to `SymbolExportLevel::C` (exceeding `Cdylib`'s export threshold). Live probe `private_attr_cdylib_export` shows that in `libcd.so` (`--crate-type cdylib`):
     - private `#[unsafe(no_mangle)] static PRIV_NM` and `#[unsafe(export_name = "priv_exp")] static PRIV_EXP` are **exported** in `.dynsym` (`51: ... GLOBAL DEFAULT 9 PRIV_NM`, `52: ... GLOBAL DEFAULT 9 priv_exp`);
     - `#[used] #[unsafe(link_section = ".priv_used_sec")] static PRIV_LS_USED` keeps `.priv_used_sec` in the `.so` section table (`PROGBITS`, `Ao`, size `8`; `AR` in `.o` via `SHF_GNU_RETAIN`), yet is **absent from `.dynsym`** (`SymbolExportLevel::Rust`);
     - unreferenced private `#[unsafe(link_section = ".priv_unreferenced_sec")] static PRIV_LS_ONLY` is omitted from the linked `libcd.so` section table and `.dynsym` (though still visible as `LOCAL DEFAULT` in `--emit=obj` `lib.o`).

### 6. Mechanized Lean 4 Soundness Model and Counterexamples

`Basis: derived (support/StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean, Lean v4.34.1)`

The standalone Lean 4 development (`1,412` lines, `624` constants in namespace `StaticElfSectionPlacementAndUnsafeAttrsSoundness`, checked under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` in `3.2864` s, zero `sorry`/`omega`/`bv_decide`/`native_decide`/`Classical.choice`/`partial`/`._unsafe_rec`) formalizes three interlocking components:

1. **Exact 5/6-case classifier (`StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean:360-437`):**
```lean
noncomputable def classifyStaticSection
    (rm : RelocModel) (mutOrInt hasReloc isZero : Bool) : PlacementTarget :=
  if mutOrInt then
    if hasReloc then
      { secKind := .data, progBits := .progbits, flags := .flagsWA, hasRela := true }
    else if isZero then
      { secKind := .bss, progBits := .nobits, flags := .flagsWA, hasRela := false }
    else
      { secKind := .data, progBits := .progbits, flags := .flagsWA, hasRela := false }
  else
    if hasReloc then
      match rm with
      | .pic =>
        { secKind := .dataRelRo, progBits := .progbits, flags := .flagsWA, hasRela := true }
      | .staticModel =>
        { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := true }
    else
      { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := false }
```
Verified classifier theorems (all axiom-free `[]`):
- `classify_immutable_never_bss` (`L379-381`): `(classifyStaticSection rm false hasReloc isZero).secKind ≠ .bss ∧ (classifyStaticSection rm false hasReloc isZero).progBits = .progbits`
- `classify_immutable_zero_lands_in_rodata` (`L387-389`): `classifyStaticSection rm false false true = { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := false }`
- `classify_pic_immut_reloc_is_dataRelRo` (`L392-394`): `classifyStaticSection .pic false true isZero = { secKind := .dataRelRo, progBits := .progbits, flags := .flagsWA, hasRela := true }`
- `classify_static_immut_reloc_is_rodata` (`L397-399`): `classifyStaticSection .staticModel false true isZero = { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := true }`
- `classify_interior_mut_always_writable` (`L402-405`): `flags = .flagsWA ∧ secKind ≠ .rodata ∧ secKind ≠ .dataRelRo`
- `classify_bss_iff` (`L419-421`): `secKind = .bss ↔ (mutOrInt = true ∧ hasReloc = false ∧ isZero = true)`
- `classify_nobits_iff_bss` (`L429-431`) and `classify_rela_iff_hasReloc` (`L435-436`).

2. **Two-phase loader, RELRO freeze, and runtime safety (`L645-935`):**
`loadProgram` maps `PROGBITS` from `d.initBytes` and `NOBITS` as `replicateZero d.initBytes.length`, setting initial page permissions `permOfFlags`. Under hypotheses `(hdist : DistinctSymIds es)` and `(hbounds : ∀ e ∈ todo, RelocsInBounds e.decl)`:
- `load_preserves_init_bytes` (`L645`): `(loadEmittedSym (emitWithClassifier rm d)).loadedBytes = d.initBytes` (uses `[propext, Quot.sound]` from `List` extensionality helpers).
- `pic_reloc_sym_is_rw_at_load` (`L661`): any declaration with `d.hasReloc = true` under `.pic` gets `perm = .rw`.
- `pic_applyAllRelocs_succeeds` (`L740-747`): `applyAllRelocs st todo = .ok st' ∧ PicPreRelroInv st' allEs` (zero `relocTrap` / `oobFault`).
- `applyRelroProtect_establishes_postRelroMemSafeInv` (`L824-828`): freezing `.dataRelRo` symbols to `.ro` establishes `PostRelroMemSafeInv (applyRelroProtect st) es` (`immutable -> perm = .ro`, `interiorMut/staticMut -> perm = .rw`).
- `wellTypedTrace_safe_and_preserves_immutable` (`L905-916`): across any list of `WellTypedRuntimeOp` operations (where writes target only `hasInteriorOrMut = true` symbols in bounds), `execRuntimeTrace st ops = .ok st'`, `PostRelroMemSafeInv st' es` holds inductively, and every immutable symbol retains bit-identical `loadedBytes`.

3. **Mechanized fault counterexamples (`L1017-1084`, `L1338-1344`):**
   - `ce1_rodata_write_trap_on_unsafecell`: placing `interiorMut` (`[7, 0, ...]`) in `.rodata` (`flagsA`) makes a `WellTypedRuntimeOp` write fault with `execRuntimeOp st (.write 1 0 88) = .fault .sigsegv`.
   - `ce2_rodata_relocation_trap_on_pic_imm_ref`: placing a relocated immutable static in `.rodata` (`flagsA`) under PIC faults with `applyAllRelocs ... = .fault .relocTrap`.
   - `ce3_bss_data_loss_on_nonzero_init`: placing non-zero `[42, 0, ...]` in `.bss` (`NOBITS`) yields `loaded.loadedBytes[0]? = some 0 ∧ ce3NonZeroDecl.initBytes[0]? = some 42 ∧ loaded.loadedBytes ≠ ce3NonZeroDecl.initBytes`.
   - `ce4_link_section_rodata_contaminates_segment`: `linkSectionFlagsOverride` with `sName = 0` (`.rodata`) on `classifyStaticSection .pic true false false` retains `flagsWA`, so `mergeElfFlags immDefault.flags cellInRodataFlags = .flagsWA` and `permOfFlags (...) = .rw`.
   - `ce5_cross_edition_macro_bypass`: an `AttrUse` with `kind := .noMangle`, `annot := .bare`, `pathSpanEdition := .ed2021` passes `checkAttributeSafety` without error even when `crateEdition = .ed2024`.

4. **Edition 2024 attribute gate, codegen equivalence, and end-to-end composition (`L1207-1410`):**
   - `edition2024_gate_requires_unsafe_witness` (`L1207-1211`): `expectedSafetyOf u.kind = .unsafeSince2024 → u.pathSpanEdition = .ed2024 → isAttrError (checkAttributeSafety u) = false → u.annot = .unsafeWrapped`.
   - `unsafe_wrapper_rejected_on_normal_attrs` (`L1223-1227`): `#[unsafe(used)]` / `#[unsafe(inline)]` always return `.errInvalidAttrUnsafe`.
   - `codegen_equivalence_2021_bare_to_2024_unsafe` (`L1296-1304`): mapping `wrapForEdition2024` across bare Edition 2021 attributes passes `checkAllAttrs` in both editions and yields equal `CodegenAttrs` (`processBuiltinAttrs`) and `SymbolExportLevel`.
   - `export_name_precedence_over_no_mangle_both_orders` (`L1316-1322`) and `link_section_alone_does_not_export_c_symbol` (`L1327-1332`).
   - `end_to_end_static_placement_and_attr_soundness` (`L1354-1374`): composes Edition 2024 attribute gating (`∀ u ∈ attrs, expectedSafetyOf u.kind = .unsafeSince2024 → u.annot = .unsafeWrapped`) with PIC loading, dynamic relocation (`applyAllRelocs ... = .ok stReloc`), RELRO protection, safe runtime trace execution (`execRuntimeTrace (applyRelroProtect stReloc) ops = .ok stEnd`), and immutable byte preservation.

### 7. Anneal Verification Boundary

`Basis: source (joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613)`

Inspecting `trusted/lean/Trusted/MirAst.lean` (`L50-92`, `855-944`) and `trusted/rustc-capture/src/driver.rs` (`L25-84`) establishes that Anneal's MIR formalization at `c131b320eeeb26ef692e5afd5ec8db49ee518613` models single-crate post-cleanup runtime MIR `Body` and `Program` values parameterized by `pointerWidthBits` (`64`), `mirProfileVersion` (`1`), and `VerificationScope` (`.unit` or `.crate`). Module-level `static` items (`DefKind::Static`), LLVM `GlobalVariable::isConstant()` attributes, ELF section classifiers, `PT_GNU_RELRO` loader semantics, and linkage/section attributes (`#[unsafe(no_mangle)]`, `#[unsafe(export_name)]`, `#[unsafe(link_section)]`, `#[used]`) are outside `Trusted.MirAst` and unverified by Anneal's function-body theorem pipeline (`CrateTheorem`/`UnitTheorem`/`BodyVerified`), confirming the exact motivation for verifying those invariants at the `rustc`/LLVM/ELF layer documented here.

## Boundaries

The following boundaries apply strictly to this report's claims:

- **Not examined:**
  - Non-ELF binary formats (`BinaryFormat::MachO`, `Coff`, `Wasm`, `Xcoff`, `GOFF`), even though `link_attrs.rs:549-557` and `consts.rs:551-570` show special-cased frontend/LLVM paths (`check_link_section_macho`, `wasm.custom_sections`).
  - Thread-local statics (`#[thread_local]`, `.tdata` / `.tbss`, TLS relocation models), `-Z sanitize=hwaddress/address`, large code models (`TM.isLargeGlobalValue(GO)` -> `.lrodata`/`.ldata`/`.lbss`/`.ldata.rel.ro`), and explicit linker scripts overriding default GNU `ld` or `LLD` orphan/flag merging.
  - Relocatable link (`ld -r`) behavior or Full LTO / ThinLTO bitcode-merging interactions when cross-crate objects mix `-C relocation-model` or conflicting `section` attributes.
  - Non-`x86_64` ELF architectures (e.g., `aarch64-unknown-linux-gnu` constant PtrAuth relocations or ARM `ROPI`/`RWPI` execution).
- **Unknown:**
  - Whether future releases of `GNU ld` beyond `2.47` will change its `PT_GNU_RELRO` drop heuristic when an input `.rodata` section carries `SHF_WRITE`, or emit a diagnostic by default without `--fatal-warnings` / `--warn-rwx-segments`.
  - Whether proc-macro token re-spanning edge cases beyond declarative `macro_rules!` (`diag_span.from_expansion()` branch at `safety.rs:56-65`) alter suggestion formatting across all macro crates (only diagnostic suggestion formatting depends on `not_from_proc_macro`; the hard-error condition `path_span.edition() >= unsafe_since` is invariant).
- **Known not to apply:**
  - The Edition 2024 `#[unsafe(...)]` requirement does **not** trigger hard errors on macro-generated `#[no_mangle]`/`#[export_name]`/`#[link_section]` whose `path_span` originates from an Edition <= 2021 crate, even when expanded inside an Edition 2024 crate (established by both `safety.rs:53` and live execution `cross_edition_macro_ed2021_in_ed2024`).
  - `#[unsafe(link_section)]` alone does **not** make a private `static` reachable across codegen or export its symbol in `.dynsym` of a `cdylib` (`reachable.rs:444`, `symbol_export.rs:641`, `private_attr_cdylib_export`).
  - The Lean theorem `end_to_end_static_placement_and_attr_soundness` does **not** guarantee absence of `PT_GNU_RELRO` stripping or `.rodata` flag escalation in real binaries that use `#[unsafe(link_section = ".rodata")]` on interior-mutable statics; that counterexample is proved separately in `ce4_link_section_rodata_contaminates_segment` and confirmed empirically under both `GNU ld 2.47` and `LLD 22.1.6`.
  - Executed `rustc 1.98.0-nightly (14210df0e)` does **not** make `#[unsafe(no_mangle)]` on generic functions a hard error (`rc = 0`, warning `no_mangle_generic_items`), whereas `rust-lang/rust` HEAD (`0259d5e9a`, `rustc_lint/src/builtin.rs:859`) upgrades it to hard error `BuiltinNoMangleGeneric`.
- **Unsupported:**
  - Non-zero initializers placed into `.bss` / `.bss.*` via `#[unsafe(link_section = ...)]` are explicitly unsupported at ELF object emission (`error: BSS section '...' cannot have non-zero bytes`, `nonzero_in_bss_rejected`).
  - `#[unsafe(...)]` on normal (non-unsafe) built-in attributes such as `used` and `inline` is unconditionally rejected across all editions (`InvalidAttrUnsafe`, `normal_attr_with_unsafe_rejected`).
  - Modeling `static` allocations, custom ELF sections, or dynamic relocations is unsupported by `joshlf/anneal@c131b320e`'s `Trusted.MirAst` (`MirProfileVersion = 1` captures per-function MIR bodies without module-level globals).

## Evidence

All primary evidence was gathered on `2026-11-23` and is preserved inside this package's `support/` directory so every claim can be audited and reproduced without external state:

### 1. Pinned Upstream Primary Sources (`support/pin_receipt.json`, 42/42 verified)

Verification receipt `support/pin_receipt.json` (`sha256: 2bfb3af67d8216551ec9aecc42e8c9da405b2ec0417aa6040c89630904641f52`) records exact byte sizes and SHA-256 hashes resolved against immutable 40-hex Git commits via `support/verify_pins.py`:

| Repository & Immutable Commit | Examined Paths & Narrow Line Ranges |
| :--- | :--- |
| `rust-lang/rust` @ `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_attr_parsing/src/safety.rs` (`L25-126`), `attributes/codegen_attrs.rs` (`L112-152`, `417-436`), `attributes/link_attrs.rs` (`L492-560`), `diagnostics.rs` (`L917-923`); `compiler/rustc_passes/src/check_attr.rs` (`L1210-1239`), `reachable.rs` (`L435-458`); `compiler/rustc_codegen_llvm/src/consts.rs` (`L473-580`, `649-677`); `compiler/rustc_codegen_ssa/src/codegen_attrs.rs` (`L58-116`), `back/symbol_export.rs` (`L35-53`, `634-660`); `compiler/rustc_middle/src/middle/codegen_fn_attrs.rs` (`L269-287`); `compiler/rustc_const_eval/src/interpret/intern.rs` (`L179-259`); `compiler/rustc_hir_analysis/src/check/{check.rs:750-820, wfcheck.rs:1258-1289}`; `compiler/rustc_lint/src/builtin.rs` (`L843-905`); `compiler/rustc_lint_defs/src/builtin.rs` (`L5084-5090`) |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_attr_parsing/src/safety.rs` (`L25-115`), `attributes/{codegen_attrs.rs:101-141,337-356, link_attrs.rs:461-525}`; `compiler/rustc_passes/src/check_attr.rs` (`L1699-1729`); `compiler/rustc_codegen_llvm/src/consts.rs` (`L470-550`); `compiler/rustc_const_eval/src/interpret/intern.rs`; `compiler/rustc_lint/src/builtin.rs` (`L250-337`) |
| `llvm/llvm-project` @ `fc4aad7b5db3fff421df9a9637605b9ca5667881` (`llvmorg-22.1.6`) | `llvm/lib/Target/TargetLoweringObjectFile.cpp` (`L82-99`, `277-368`, sha256 `cbbdd2bc...`); `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp` (`L456-554`, `616-632`, `822-875`, sha256 `e5f34146...`) |
| `llvm/llvm-project` @ `229f673cd9cd804c579440dbd6e9cc0509f3a3c3` (`HEAD`) | `llvm/lib/Target/TargetLoweringObjectFile.cpp` (`L280-379`, sha256 `69addfd6...`); `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp` (sha256 `3f429b37...`) |
| `rust-lang/llvm-project` @ `08c84e69a84d95936296dfcab0e38b34100725d5` | Byte-identical `TargetLoweringObjectFile.cpp` (`cbbdd2bc...`) and `TargetLoweringObjectFileImpl.cpp` (`e5f34146...`) + bundled `LLD 22.1.6` (`rust-lld`) |
| `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/items/static-items.md` (`L1-146`), `src/abi.md` (`L1-192`), `src/attributes/codegen.md` |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` (`L50-92`, `855-944`), `trusted/lean/Trusted/MirSemantics.lean`, `trusted/audit/TrustedBoundary.lean`, `trusted/rustc-capture/src/driver.rs` (`L1-100`) |
| `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `Lean v4.34.1` toolchain & `src/Init/Prelude.lean` |

### 2. Live Execution Harness & Output Specimen (`support/probe_results.json`)

- **Harness:** `support/probe_static_section_placement_and_edition2024_attrs.py`
- **Recorded outputs:** `support/probe_results.json`
- **Executed environment:**
  - `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`host: x86_64-unknown-linux-gnu`, `LLVM version: 22.1.6`)
  - `GNU readelf (GNU Binutils for Debian) 2.47`
  - `GNU ld 2.47` (`GCC: (Debian 15.2.0-14) 15.2.0`) and bundled `rust-lld` (`Linker: LLD 22.1.6 (/checkout/src/llvm-project/llvm 08c84e69a84d95936296dfcab0e38b34100725d5)`)
- **Key recorded measurements:**
  - Edition 2021 bare vs. Edition 2021 `#[unsafe(...)]` vs. Edition 2024 `#[unsafe(...)]` bit-identity (`llvm_ir_sha256: e1c7de842899b749b6157684aaee7964105066a32c0225c6a2a9e110ea80e534`, `obj_sha256: 0fb74abebb116b3d888c44ee4c413c5d6f0ec8d0fd483cc6a0b0ab0600b569c0`, `1368` bytes).
  - Rejection of bare Edition 2024 (`rc = 1`), `-F unsafe-code` across both editions (`rc = 1`), `#[unsafe(used)]`/`#[unsafe(inline)]` (`rc = 1`), non-zero `.bss` (`rc = 1`), `\0`/empty/non-ASCII `export_name`/`no_mangle` (`rc = 1`), and acceptance of cross-edition Edition 2021 macro expansion in Edition 2024 (`consumer_ed2024_rc = 0`).
  - Clean vs. `#[unsafe(link_section = ".rodata")] SyncCell<u64>` PIE binaries linked with both `GNU ld 2.47` and `LLD 22.1.6`, proving runtime `rc = -11` (`SIGSEGV`) vs. `rc = 0` (`UNEXPECTED_SURVIVED` / `HAZARD_SURVIVED:777`) and `PT_GNU_RELRO` disappearance (`15 -> 13` phdrs) under `GNU ld 2.47`.

### 3. Mechanized Lean 4 Receipt (`support/lean_check_receipt.json`)

- **Formalization:** `support/StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean` (`1,412` lines, `sha256: 489a4017a1065facc9e01ae9b6899d29a42e60df0a19cf14f9ea13c37fbf49e5`)
- **Audit checker & receipt:** `support/check_lean.py` -> `support/lean_check_receipt.json`
- **Verified metrics:**
  - `lean_version`: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`
  - Flags: `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`
  - Resource usage: `wall_clock_sec: 3.2864`, `max_rss_kib: 540212`
  - Environment & token checks: `namespace_constants: 624`, `is_unsafe: 0`, `is_partial: 0`, `unsafe_rec_helpers: 0`, `user_axioms: 0`, all banned token counts (`sorry`, `omega`, `bv_decide`, `native_decide`, `Classical.choice`, `partial_def`, `unsafe_def`, `plain_def_without_noncomputable`, `deriving_clause`, `user_axiom`, `user_opaque`) = `0`.
  - `#print axioms` across all 25 checked theorems contains exclusively `[]`, `[propext]`, or `[propext, Quot.sound]`; `forbidden_axioms_present: false`, `all_checks_passed: true`.

## Revalidation

To revalidate all findings cleanly inside `/tmp` without mutating any repository worktree:

1. **Re-run the live `rustc`, LLVM IR, ELF, and PIE `SIGSEGV`/contamination probe suite:**
   ```bash
   cp support/probe_results.json /tmp/prev_probe_results.json
   python3 support/probe_static_section_placement_and_edition2024_attrs.py
   diff -u /tmp/prev_probe_results.json support/probe_results.json
   ```
   A clean exit (`rc = 0`) confirms: (a) Edition 2024 bare-attribute rejection + Edition 2021/2024 LLVM IR and `.o` bit-identity + Edition 2021 macro bypass, (b) all 8 categories in PIC and static relocation models, (c) `nonzero_in_bss_rejected`, and (d) `GNU ld` vs. `LLD` `.rodata`/`PT_GNU_RELRO` runtime behavior. To test only whether an updated linker fixes `.rodata` `WA` contamination or `PT_GNU_RELRO` stripping, inspect `group_b_static_five_category_sections.linked_pie_with_rodata_cell_hazard` in `support/probe_results.json`.

2. **Re-verify the Lean 4.34.1 formalization and purity/axiom audit:**
   ```bash
   python3 support/check_lean.py
   ```
   Wait for exit code `0` and confirm `all_checks_passed: true`, `forbidden_axioms_present: false`, `unsafe_rec_helpers: 0`, and `is_partial: 0` in `support/lean_check_receipt.json` (using Lean `v4.34.1` and `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`).

3. **Check narrow upstream source regions for drift against newer `rustc` / `llvm` commits:**
   - Diff `compiler/rustc_const_eval/src/interpret/intern.rs` around `intern_const_alloc_recursive` (`Ty::is_freeze` check) and `compiler/rustc_codegen_llvm/src/consts.rs` around `codegen_static_item` (`llvm::set_global_constant(g, true)`).
   - Diff `compiler/rustc_attr_parsing/src/safety.rs` (`check_attribute_safety`, `path_span.edition() >= unsafe_since` + `UNSAFE_CODE` emission) and `attributes/{codegen_attrs.rs, link_attrs.rs}` (`ExportNameParser`, `NoMangleParser`, `LinkSectionParser`).
   - Diff `llvm/lib/Target/TargetLoweringObjectFile.cpp` (`isSuitableForBSS`, `getKindForGlobal`) and `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp` (`getELFKindForNamedSection`, `selectExplicitSectionGlobal`).

4. **Verify pinned upstream file SHAs (requires network access to `raw.githubusercontent.com`):**
   ```bash
   python3 support/verify_pins.py --out /tmp/reval_pins.json
   ```
   Confirm `files_verified == files_checked` (`42/42`) and `all_verified: true`.

5. **Run corpus validation from the corpus root:**
   ```bash
   python3 tools/reference.py check
   ```
