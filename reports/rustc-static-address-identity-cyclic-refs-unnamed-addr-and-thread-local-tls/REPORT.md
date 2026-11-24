# `rustc` `static` Address Identity, `unnamed_addr` Constant Deduplication, Two-Phase Cyclic Initialization, and `#[thread_local]` ELF Lowering

## Summary

- **`static` allocations preserve link-time address identity by omitting `unnamed_addr`, whereas `const`/promoted allocations emit `private unnamed_addr constant` and permit mergeable deduplication** (`Basis: normative, source, execution, derived`): The Rust Reference guarantees that every byte-sized `static` item has a single fixed allocation disjoint from every other `static`, heap, and stack allocation (`items.static.intro`, `items.static.storage-disjointness`), while explicitly permitting `const` and promoted references (`&[1u64, 2]`) to overlap or duplicate (`items.const.behavior`, `items.const.static-temporary`). In `rustc_codegen_llvm`, `static_addr_of_mut` applies `llvm::Linkage::PrivateLinkage` and `llvm::UnnamedAddr::Global`, and `static_addr_of_impl` marks the global constant via `set_global_constant(gv, true)`. By contrast, `codegen_static_item` emits static definitions via `declare_global` / `get_static_inner` without calling `set_unnamed_address`. LLVM `ConstantMerge` refuses to fold two globals unless at least one carries `UnnamedAddr::Global` (`hasGlobalUnnamedAddr()`) and `GV->hasLocalLinkage()`, and LLVM `TargetLoweringObjectFile::getKindForGlobal` routes non-`unnamed_addr` constants to `.rodata.<sym>` (`PROGBITS`, `SHF_ALLOC`) while routing `unnamed_addr` constants to `SHF_MERGE` sections (`.rodata.cst16`, `PROGBITS`, `SHF_ALLOC | SHF_MERGE`).
- **Optimization under `-O2` may assign `local_unnamed_addr` to uncompared exported statics without breaking address distinctness** (`Basis: source, execution, derived`): LLVM `GlobalOpt`'s `processGlobal` sets `UnnamedAddr::Local` (not `UnnamedAddr::Global`) on externally visible uncompared globals (`!GS.IsCompared`) and leaves compared internal globals (`S_PRIV_1 == S_PRIV_2`) with `unnamed_addr` stripped (`GlobalValue::UnnamedAddr::None`). Because `ConstantMerge::makeMergeable` checks `hasGlobalUnnamedAddr()`, two identical exported statics (`@S_DUP_1`, `@S_DUP_2`) and two identical internal statics (`@S_PRIV_1`, `@S_PRIV_2`) remain distinct allocations at both `-O0` and `-O2`, whereas merging one `static` with one `unnamed_addr` promoted constant merges the constant into the static and strips `UnnamedAddr::Global` from the survivor (`New->setUnnamedAddr(GlobalValue::UnnamedAddr::None)`), matching `items.static.storage-disjointness` and `rustc_const_eval`'s CTFE pointer-comparison rules.
- **Direct value cycles trigger `E0391` / `E0080`, whereas address-of cycles through `static` succeed via two-phase allocation reservation (`reserve_and_set_static_alloc`)** (`Basis: source, execution, derived`): During CTFE, evaluating a `static` operand inside `InterpCx::eval_global` sees `self.tcx.is_static(gid.instance.def_id())` and returns an opaque reserved `AllocId` from `tcx.reserve_and_set_static_alloc` without triggering `eval_static_initializer`; `create_static_alloc` sizes the allocation from type layout alone (`GlobalAlloc::Static(did).size_and_align`) before running the initializer body. Therefore `static A: Node = Node(10, &B); static B: Node = Node(20, &A);` and `static SELF_NODE: Node = Node(42, &SELF_NODE);` build relocation pointers without touching memory bytes. Conversely, reading a static's value (`static A: u32 = B; static B: u32 = A;`) invokes `Memory::get_global_alloc` -> `before_alloc_access`, firing `tcx.eval_static_initializer(def_id)` (mutual `E0391` query cycle) or matching `machine.static_root_ids` (`ConstEvalErrKind::RecursiveStatic`, `E0080`). Mutual `const` reference cycles (`const A: Node = Node(10, &B);`) fail `E0391` because non-`static` constants do not bypass `eval_to_allocation_raw` in `eval_global`.
- **`#[thread_local]` statics emit `.tdata` / `.tbss` (`SHF_TLS`), route accesses through `@llvm.threadlocal.address.p0`, and obey PIE relaxation over `global-dynamic`/`local-dynamic`** (`Basis: source, execution, derived`): On ELF x86-64, `codegen_static_item` propagates `self.tls_model` (`-Z tls-model` or target default) to `llvm::set_thread_local_mode`, `StaticBuilderMethods::get_static` wraps the symbol in `call ptr @llvm.threadlocal.address.p0`, and `global_root_pointer` forbids ordinary non-TLS globals from capturing pointers to `is_thread_local_static` items. LLVM `isSuitableForBSS` places zero-initialized mutable TLS (`Cell::new(0)`) into `.tbss.<sym>` (`NOBITS`, `WAT`), non-zero mutable TLS (`Cell::new(7)`) into `.tdata.<sym>` (`PROGBITS`, `WAT`), and `Freeze` zero-initialized TLS (`u64 = 0`, `GV->isConstant()`) into `.tdata.<sym>` (`PROGBITS`, `WAT`). For PIE executables (`--crate-type=bin`), `LLVMRustSetModulePIELevel` enables `TargetMachine::getTLSModel` to upgrade `global-dynamic` and `local-dynamic` to `InitialExec` (`R_X86_64_GOTTPOFF`), whereas in `--crate-type=cdylib` objects all four TLS models retain their distinct relocations (`R_X86_64_TPOFF32`, `R_X86_64_GOTTPOFF`, `R_X86_64_TLSGD`, `R_X86_64_TLSLD` + `R_X86_64_DTPOFF32`) and `local-exec` fails shared-library linking (`cdylib_link_returncode = 1`).
- **Constructive Lean v4.34.1 mechanization verifies all four core theorems and two counterexamples without `Classical.choice` or `_unsafe_rec`** (`Basis: derived, execution`): `support/StaticAddressIdentityCyclesAndTlsModelsSoundness.lean` (1,739 lines; 58 proved theorems) compiles under Lean `v4.34.1` with `-Ddebug.skipKernelTC=false -DwarningAsError=true -DElab.async=false`, achieving zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, zero `partial def`, zero user axioms, and zero `._unsafe_rec` constants across all 657 namespace symbols audited via Lean MetaM.
- **Implication for Anneal MIR verification**: At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst.ConstLit` models only `.scalar (bits : BitVec 128)` and `.zeroSized`, intentionally excluding `Rvalue::ThreadLocalRef` and static/constant pointer provenance until static identity, TLS non-interference, and provenance disjointness are incorporated into the trusted MIR semantics.

## Applicability

- **Target architecture and toolchain empirically exercised (`Basis: execution`)**: All live compilation, LLVM IR inspection, `opt` constant-merge ablation, ELF section/relocation inspection, and multithreaded Linux runtime executions were performed on `x86_64-unknown-linux-gnu` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`rust-lang/rust` commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), bundled `LLVM version: 22.1.6` (aligned with `llvm/llvm-project` release tag `llvmorg-22.1.6`, commit `fc4aad7b5db3fff421df9a9637605b9ca5667881`), and GNU `readelf` 2.47 (`support/probe_results.json`).
- **Upstream evolution checked against repository HEAD (`Basis: source`)**: Source mechanisms across `compiler/rustc_codegen_llvm`, `compiler/rustc_const_eval`, `compiler/rustc_middle`, `compiler/rustc_session`, and `llvm/lib/{Target,Transforms,CodeGen}` were cross-verified against `rust-lang/rust` HEAD `058c701055c4b6f60f622d616afc0349911c38c3` (and intermediate revision `49d734536222bf28bb6d07d885b3a81d145981da`) as well as `llvm/llvm-project` HEAD `9e1b2c3446261ab1a5063f442453510903ca80b8`. Across all three `rust-lang/rust` revisions, `static_addr_of_mut`, `eval_static_initializer_provider`, `create_static_alloc`, `to_llvm_tls_model`, `parse_tls_model`, and `Session::tls_model` preserve identical control flow (only shifted line offsets are noted in Section `## Evidence`).
- **Normative and formal scope (`Basis: normative, source, derived`)**: Language semantics are anchored to `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`; Anneal MIR AST boundaries are anchored to `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`; and the Lean mechanization (`support/StaticAddressIdentityCyclesAndTlsModelsSoundness.lean`) is kernel-checked under `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Conditions that invalidate direct transfer (`Basis: normative, source, execution`)**: Emulated TLS targets (`TlsModel::Emulated`), WebAssembly `wasm.custom_sections` (`consts.rs` L487-504), Windows COFF `dllimport` TLS stubs (`consts.rs` L361-404), ELF linkers that strip unreferenced `SHF_MERGE` entries differently than ELF GNU/LLD defaults, `-C relocation-model=static`, zero-sized types (`static ZST: () = ();`, where `items.static.storage-disjointness` exempts 0-byte statics), and `#[link_section]` overrides (`isSuitableForBSS` returns `false` at `TargetLoweringObjectFile.cpp` L94-95) behave differently as detailed in `## Boundaries`.

## Findings

### 1. Normative and Compiler Separation: `static` Address Identity vs. `unnamed_addr` Constant/Promoted Deduplication

#### 1.1 Normative Contract (`rust-lang/reference`)

`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` separates `static` items from `const` and promoted items along two axes (`Basis: normative`):

1. **Address identity & storage disjointness (`src/items/static-items.md` L12-20):** Every `static` item defines a single allocation in the program; all references and raw pointers to that static refer to that same allocation (`items.static.intro`). When a `static` has size `>= 1` byte, `items.static.storage-disjointness` requires its storage to be disjoint from every other non-ZST `static`, heap, and stack allocation, while explicitly allowing immutable `static` storage to overlap allocations that themselves lack a unique address (`const` items and promoted rvalues).
2. **Value-only identity for `const` and promoted references (`src/items/constant-items.md` L10-24):** A `const` item is not bound to a unique memory location (`items.const.intro`) and is conceptually copied inline at every use (`items.const.behavior`). Taking a reference to an eligible constant expression (`&[1u64, 2]`) yields a `'static` reference via promotion (`items.const.static-temporary`), with no guarantee that two references to the same constant share an address—or stay disjoint from distinct constants.

CTFE pointer comparison mirrors this split verbatim in `compiler/rustc_const_eval/src/const_eval/machine.rs` (`14210df0` L345-384) (`Basis: source`): when two allocations compared for pointer equality are distinct non-ZST `GlobalAlloc::Static` allocations tested strictly in-bounds (`a_offset < a_info.size && b_offset < b_info.size`), CTFE returns `0` (`false`, definitely unequal), explicitly citing `items.static.intro` and `items.static.storage-disjointness`. Whenever at least one allocation is non-`static` (e.g., `GlobalAlloc::Memory`), CTFE conservatively returns `2` (runtime equality unknown at compile time) because constant allocations can overlap immutable statics or be duplicated across codegen units.

#### 1.2 `rustc_codegen_llvm` IR Attributes: `unnamed_addr` on Promoteds vs. Omission on `static`

Inside `compiler/rustc_codegen_llvm/src/consts.rs` (`14210df0` L236-286, `058c7010` L296-345, `49d73453` L294-316), promoted rvalues and anonymous constant allocations pass through `CodegenCx::static_addr_of_mut` and `static_addr_of_impl` (`Basis: source`):

- `static_addr_of_mut` defines a fresh symbol via `generate_local_symbol_name(kind)` (producing names such as `@alloc_011d402fc2fd12f79ff2bc7691f0df1d`), assigns `llvm::Linkage::PrivateLinkage` (`consts.rs` `14210df0` L254), initializes and aligns it (L255-256), and unconditionally marks **`llvm::set_unnamed_address(gv, llvm::UnnamedAddr::Global)`** (L257; `058c7010` L316).
- `static_addr_of_impl` caches `(cv -> gv)` per CGU in `self.const_globals`, upgrades alignment if reused, and sets `llvm::set_global_constant(gv, true)` (`14210df0` L270-285).

In contrast, `static` items enter `CodegenCx::codegen_static_item` (`14210df0` L410-539) and `get_static_inner` (`14210df0` L307-408) (`Basis: source`):

- Neither `get_static_inner` nor `codegen_static_item` ever calls `llvm::set_unnamed_address`.
- `codegen_static_item` propagates the static's interned mutability (`if alloc.mutability.is_not() { llvm::set_global_constant(g, true); }`, L474-476), sets alignment (L468), marks `assume_dso_local(g, true)` (L471), applies `self.tls_model` when `CodegenFnAttrFlags::THREAD_LOCAL` is set (L480-482), and attaches `llvm.compiler.used` / `llvm.used` if requested (L511-538).

#### 1.3 Why LLVM `-O2` Adds `local_unnamed_addr` Yet Never Merges Statics (`GlobalOpt` + `ConstantMerge` + `TargetLoweringObjectFile`)

Empirical inspection at `-C opt-level=0` vs. `-C opt-level=2` (`support/probe_results.json` L10-72) exposes an important subtlety that distinguishes `unnamed_addr` (`UnnamedAddr::Global`) from `local_unnamed_addr` (`UnnamedAddr::Local`) (`Basis: source, execution, derived`):

1. **At `-O0` (`probe_results.json` L10-39):**
   - `pub static S: u64 = 123` emits `@S = constant [8 x i8] c"{\00...", align 8`.
   - `pub static S_DUP_1: u64` and `pub static S_DUP_2: u64` emit `@S_DUP_1 = constant [8 x i8] ...` and `@S_DUP_2 = constant [8 x i8] ...`.
   - Private `static S_PRIV_1` and `static S_PRIV_2` emit `internal constant [8 x i8] ...` (no `unnamed_addr`).
   - Constant/promoted slice `&[1u64, 2]` (`const C: &[u64] = &[1, 2];`) emits a single CGU-deduplicated **`@alloc_011d402fc2fd12f79ff2bc7691f0df1d = private unnamed_addr constant [16 x i8] ...`**.
   - ELF sections show `.rodata.S`, `.rodata.S_DUP_1`, `.rodata.S_DUP_2`, and internal `.rodata.*S_PRIV_{1,2}` all have `PROGBITS ... A` (no `SHF_MERGE`), whereas `@alloc_011d402fc2fd12f79ff2bc7691f0df1d` lands in `.rodata.cst16 PROGBITS ... 10 AM` (`SHF_ALLOC | SHF_MERGE`, entry size `0x10 = 16`).
2. **At `-O2` (`probe_results.json` L42-72):**
   - Exported `@S_DUP_1` and `@S_DUP_2` acquire **`local_unnamed_addr constant`**! Why? `GlobalOpt::processGlobal` (`llvm/lib/Transforms/IPO/GlobalOpt.cpp` `fc4aad7b` L1656-1670) runs `GlobalStatus::analyzeGlobal(&GV, GS)`; if the global's address is never compared inside the current module (`!GS.IsCompared`), `processGlobal` sets `UnnamedAddr::Global` for `hasLocalLinkage()` globals and **`UnnamedAddr::Local`** for externally visible globals (`!GV.hasLocalLinkage()`, L1663-1664). Because `@S_DUP_1` and `@S_DUP_2` are exported library items with no address comparisons inside the library crate (`GS.IsCompared = false`), `GlobalOpt` upgrades them to `local_unnamed_addr` (`UnnamedAddr::Local`) while the binary probe still observes `STATIC_DUP_EQ=false`.
   - Meanwhile, private `static S_PRIV_1` and `S_PRIV_2` ARE compared inside `get_priv_statics_eq()`; `GlobalStatus` records `GS.IsCompared = true` (`GlobalStatus.cpp` L160 context / L1662 guard), blocking `GlobalOpt` from setting `unnamed_addr` (`internal constant`, keeping `UnnamedAddr::None`), and emitting runtime false (`STATIC_PRIV_DUP_EQ=false`).
3. **Why `local_unnamed_addr` does not permit `ConstantMerge` (`llvm/lib/Transforms/IPO/ConstantMerge.cpp` `fc4aad7b` L91-132, L198-204):**
   - `replace()` asserts `Old->hasLocalLinkage()` (L129) and the second pass skips `!GV.hasLocalLinkage()` (L203), so externally visible statics cannot be erased.
   - Even for two `private`/`internal` globals, `makeMergeable(Old, New)` (L104-113) requires at least one of them to satisfy `hasGlobalUnnamedAddr()` (L105: `if (!Old->hasGlobalUnnamedAddr() && !New->hasGlobalUnnamedAddr()) return CanMerge::No;`). Furthermore, if `!Old->hasGlobalUnnamedAddr()`, LLVM strips global unnamed_addr from the survivor (`New->setUnnamedAddr(GlobalValue::UnnamedAddr::None)`, L110-111).
   - **Ablation via `opt -passes=constmerge` (`probe_results.json` L74-100):** Passing two `private unnamed_addr` globals (`@UA_1`, `@UA_2`) folds them into `@UA_2` (`merged_to_single: true`); passing two `private constant` globals (`@ST_1`, `@ST_2`, `none`) leaves both separate (`preserved_distinct: true`); and passing one `private constant` `@ST_1`, one `private constant` `@ST_2`, and one `private unnamed_addr constant` `@UA_2` folds `@ST_1` into `@UA_2`, **strips `unnamed_addr` off `@UA_2`** (`@UA_2 = private constant ...`), and leaves `@ST_2` untouched (`total_surviving_globals: 2`), directly realizing `items.static.storage-disjointness` (promoted/unnamed constants may coalesce into at most one static, never fusing two statics together!).
4. **ELF object-file `SHF_MERGE` guard (`TargetLoweringObjectFile.cpp` `fc4aad7b` L300-311):** `getKindForGlobal` explicitly checks `if (!GVar->hasGlobalUnnamedAddr()) return SectionKind::getReadOnly();` ("If the global is required to have a unique address, it can't be put into a mergable section: just drop it into the general read-only section instead"). Thus neither `UnnamedAddr::None` nor `UnnamedAddr::Local` can enter linker-merged `.rodata.cst*` (`SHF_MERGE`) sections.

| Artifact / Allocation Kind | `rustc_codegen_llvm` Origin | LLVM `UnnamedAddr` (`-O0`) | LLVM `UnnamedAddr` (`-O2`) | `ConstantMerge` Eligible (`Old` replaceable) | ELF Section Class (`TargetLoweringObjectFile`) |
| --- | --- | --- | --- | --- | --- |
| Promoted slice `&[1u64, 2]` / `const C` | `static_addr_of_mut` (`consts.rs:236-259`) | `Global` (`private unnamed_addr`) | `Global` (`private unnamed_addr`) | Yes (pair merges; strips if paired with static) | `.rodata.cst16` (`PROGBITS AM`, `SHF_MERGE`) |
| Exported `static S_DUP_1` (uncompared locally) | `codegen_static_item` (`consts.rs:410-539`) | `None` (`constant`) | `Local` (`local_unnamed_addr`) | No (`!hasLocalLinkage()`, `!hasGlobalUnnamedAddr()`) | `.rodata.S_DUP_1` (`PROGBITS A`, unique) |
| Internal `static S_PRIV_1` (address compared) | `codegen_static_item` (`consts.rs:410-539`) | `None` (`internal constant`) | `None` (`GS.IsCompared = true`) | No (`!hasGlobalUnnamedAddr()`) | `.rodata.*S_PRIV_1` (`PROGBITS A`, unique) |
| Mixed (`static ST_1`, `static ST_2`, `unnamed_addr UA_2`) | Mixed constant + static | Mixed (`None`, `Global`) | `UA_2` downgraded to `None` after absorbing `ST_1` | Only one static absorbed into `UA_2`; `ST_1`/`ST_2` stay disjoint | Surviving `UA_2` -> `.rodata` (non-mergeable); `ST_2` stays separate |

### 2. Why Direct Value Cycles Fail `E0391`/`E0080` While Address-Of `static` Cycles Succeed

#### 2.1 Query Architecture and Two-Phase `reserve_and_set_static_alloc`

`compiler/rustc_const_eval` and `compiler/rustc_middle/src/mir/interpret` decouple **allocation identity + byte-layout reservation** from **initializer value evaluation** (`Basis: source, derived`):

1. **`reserve_and_set_static_alloc` (`compiler/rustc_middle/src/mir/interpret/mod.rs` `14210df0` L488-493):** Computes `salt = 0` ("Statics have a guaranteed unique address, no salt added") and calls `self.reserve_and_set_dedup(GlobalAlloc::Static(static_id), salt)` (`L462-480`). This allocates a fresh deterministic `AllocId` and inserts `id -> GlobalAlloc::Static(static_id)` into `alloc_map` **without reading or evaluating `static_id`'s initializer query**.
2. **`GlobalAlloc::size_and_align` (`middle/mir/interpret/mod.rs` `14210df0` L354-394):** For non-nested `GlobalAlloc::Static(def_id)`, size and alignment come strictly from **`tcx.type_of(def_id)` -> `tcx.layout_of(...)`** plus codegen alignment attributes—explicitly commented as needed to `"* avoid cycle errors in case of self-referential statics"` (`L375`).
3. **`InterpCx::eval_global` (`const_eval/src/interpret/eval_context.rs` `14210df0` L586-600):** When MIR inside an initializer evaluates a reference to another global item:
   - If `self.tcx.is_static(gid.instance.def_id())`, `eval_global` calls `self.tcx.reserve_and_set_static_alloc(gid.instance.def_id())` (`L592`) and constructs a lazy `ConstAlloc { alloc_id, ty }` -> `MPlaceTy` without querying `eval_static_initializer`!
   - If `!is_static(...)` (any `const` item), `eval_global` invokes `self.ctfe_query(|tcx| tcx.eval_to_allocation_raw(...))` (`L597`), forcing immediate recursive constant evaluation.
4. **Evaluator Entry & Initializer Storage (`eval_queries.rs` `14210df0` L26-64, `interpret/util.rs` `14210df0` L75-93):** When `eval_static_initializer_provider(tcx, def_id)` (`L337-346`) evaluates `static A`'s body, `setup_for_eval` sees `InternKind::Static(_)` and calls `create_static_alloc`, which reserves `A`'s `AllocId`, sets `ecx.machine.static_root_ids = Some((alloc_id, static_def_id))` (`util.rs` L90), inserts uninitialized storage for `A`, and proceeds. Evaluating `&B` inside `A`'s initializer creates a pointer (`Pointer::from(alloc_id_B)`) in register/aggregate slots without loading from `B`'s memory.
5. **Memory-Read Trigger (`memory.rs` `14210df0` L660-703, `const_eval/machine.rs` `14210df0` L997-1021):** Reading *bytes* out of `alloc_id` triggers `before_alloc_access`:
   - If `Some(alloc_id) == machine.static_root_ids.map(|(id, _)| id)` (and stack is non-empty), CTFE immediately aborts with `Err(ConstEvalErrKind::RecursiveStatic).into()` (`machine.rs` L1007-1008) -> `error[E0080]`.
   - If `machine.static_root_ids.is_some()` and `alloc_id` resolves to another `GlobalAlloc::Static(other_def_id)`, CTFE executes **`tcx.eval_static_initializer(other_def_id)?`** (`machine.rs` L1017), propagating through the Rust query system (`E0391` on any cycle!).

#### 2.2 Live `rustc` Reproduction of All Four Dependency Topologies

Live executions (`support/probe_results.json` L103-151) confirm every branch of this compiler architecture (`Basis: execution`):

1. **Mutual static value cycle (`static A: u32 = B; static B: u32 = A;`):** Exits `1` with **`error[E0391]: cycle detected when evaluating initializer of static A`** (`probe_results.json` L104-105), matching the query edge fired by `before_alloc_access` (`machine.rs` L1017).
2. **Direct self-value cycle (`static A: u32 = A;`):** Exits `1` with **`error[E0080]: encountered static that tried to access itself during initialization`** (`probe_results.json` L108-109), matching `machine.rs` L1007-1008 (`RecursiveStatic`), rather than `E0391`.
3. **Mutual `const` reference cycle (`const A: Node = Node(10, &B); const B: Node = Node(20, &A);`):** Exits `1` with **`error[E0391]: cycle detected when simplifying constant for the type system A`** (`probe_results.json` L112-113) because `eval_global` routes non-static `const`s eagerly through `eval_to_allocation_raw` (`eval_context.rs` L597) instead of `reserve_and_set_static_alloc`.
4. **Mutual and self address-of cycles through `static` (`static A: Node = Node(10, &B); static B: Node = Node(20, &A); static SELF_NODE: Node = Node(42, &SELF_NODE);`):** Compiles cleanly (`rc = 0`) and prints **`CYC_REF_OK=10,20 ROUNDTRIP=10,20 SELF_CYCLE_EQ=true AB_DISTINCT=true`** (`probe_results.json` L116-124). MIR dump shows direct symbolic static allocations (`alloc1 (static: B)`, `alloc2 (static: A)`, `alloc5 (static: SELF_NODE)` with `A` pointing to `alloc1` and `B` pointing to `alloc2`, L127-149), and LLVM IR lowers them into circular relocations `@_RNvCs3JFuYcwBINv_7cyc_ref1A = internal constant <{ ptr, [4 x i8], [4 x i8] }> <{ ptr @_RNvCs3JFuYcwBINv_7cyc_ref1B, ... }>`, `@_RNvCs3JFuYcwBINv_7cyc_ref1B = ... <{ ptr @_RNvCs3JFuYcwBINv_7cyc_ref1A, ... }>`, and `@_RNvCs3JFuYcwBINv_7cyc_ref9SELF_NODE = ... <{ ptr @_RNvCs3JFuYcwBINv_7cyc_ref9SELF_NODE, ... }>` (L121-123).

### 3. `#[thread_local]` Lowering, `.tdata`/`.tbss` Section Placement, and `-Z tls-model` Resolution

#### 3.1 `rustc` Session Flag -> LLVM Module IR -> `llvm.threadlocal.address.p0`

Tracing `rustc` from CLI parsing through MIR codegen (`Basis: source`):

1. **CLI & Target Resolution:** `compiler/rustc_session/src/options.rs` (`14210df0` L1717, `058c7010` L1951) parses `-Z tls-model` via `parse_tls_model` into `UnstableOptions::tls_model: Option<TlsModel>` (`rustc_target::spec::TlsModel`, `target/spec/mod.rs` `14210df0` L1003). `Session::tls_model(&self)` (`session.rs` `14210df0` L744-746, `058c7010` L379-381) resolves `self.opts.unstable_opts.tls_model.unwrap_or(self.target.tls_model)`.
2. **Codegen Context Mapping:** `to_llvm_tls_model` (`context.rs` `14210df0` L170-178, `058c7010` L177-185) maps `GlobalDynamic`, `LocalDynamic`, `InitialExec`, and `LocalExec` directly to `llvm::ThreadLocalMode` variants (and maps `TlsModel::Emulated` to `GeneralDynamic`). `create_module` (`context.rs` `14210df0` L252-266) calls `LLVMRustSetModulePICLevel` for PIC/PIE and **`LLVMRustSetModulePIELevel(llmod)`** whenever `reloc_model == RelocModel::Pie` or all crate types are `CrateType::Executable` (`L259-264`).
3. **Static Attribute & MIR Rvalue Emission:** Both `get_static_inner` (`consts.rs` L355-357) and `codegen_static_item` (`consts.rs` L480-482) invoke `llvm::set_thread_local_mode(g, self.tls_model)` when `CodegenFnAttrFlags::THREAD_LOCAL` is set. Every MIR read/address computation (`Rvalue::ThreadLocalRef(def_id)` in `rustc_codegen_ssa/src/mir/rvalue.rs` `14210df0` L646-676) calls `bx.get_static(def_id)` (or calls a cross-crate `ThreadLocalShim` if `needs_thread_local_shim`), which emits `self.call_intrinsic("llvm.threadlocal.address", &[self.val_ty(global)], &[global])` (`builder.rs` `14210df0` L1478-1482). LLVM prevents hoisting a TLS base address across coroutine suspension points or thread switches by keeping accesses wrapped in `@llvm.threadlocal.address.p0` through IR optimizations until `SelectionDAGBuilder` lowers `Intrinsic::threadlocal_address` (`SelectionDAGBuilder.cpp` `fc4aad7b` L8176-8179) directly to target TLS ISD nodes (`@TLS_NONZERO`, etc.).
4. **CTFE Provenance Guard:** `rustc_const_eval/src/interpret/memory.rs` (`14210df0` L197-201) forbids non-TLS globals or constants from storing a pointer to a `#[thread_local]` static (`bug!("global memory cannot point to thread-local static")`), ensuring all accesses go through dynamic per-thread `ThreadLocalRef`. Furthermore, `llvm::ConstantMerge` explicitly skips all thread-local globals (`isUnmergeableGlobal` returns true on `GV->isThreadLocal()`, `ConstantMerge.cpp` L98).

#### 3.2 `.tdata` vs. `.tbss` Anomaly on Zero-Initialized `Freeze` TLS (`isSuitableForBSS`)

Why does `#[thread_local] static TLS_FREEZE_ZERO: u64 = 0;` land in **`.tdata`** (`PROGBITS`, occupying file bytes) instead of **`.tbss`** (`NOBITS`)? Primary-source analysis and empirical `readelf -S -W` output resolve this cleanly (`Basis: source, execution`):

- In `codegen_static_item` (`consts.rs` L474-476), `TLS_FREEZE_ZERO` is an immutable `Freeze` type (`u64`), so `alloc.mutability.is_not()` sets `llvm::set_global_constant(g, true)` (`constant [8 x i8] zeroinitializer`), whereas `Cell<u64>` has `UnsafeCell` (`!Freeze`) -> `Mutability::Mut` -> mutable LLVM `global`.
- Inside LLVM `TargetLoweringObjectFile::getKindForGlobal` (`TargetLoweringObjectFile.cpp` `fc4aad7b` L265-275), a thread-local variable enters `.tbss` (`ThreadBSSLocal`/`ThreadBSS`) **only if `isSuitableForBSS(GVar)` returns true**.
- `isSuitableForBSS` (`TargetLoweringObjectFile.cpp` L82-99) explicitly rejects constant globals (`if (GV->isConstant()) return false;`, L90-91) so read-only zeros can stay in shared/read-only sections. On TLS globals, however, `GVar->isThreadLocal()` is checked *before* the non-TLS `isConstant()` branch (L265 vs. L300), so failing `isSuitableForBSS` drops `TLS_FREEZE_ZERO` straight to `SectionKind::getThreadData()` -> `.tdata.TLS_FREEZE_ZERO PROGBITS WAT`!
- **Verified ELF object output (`probe_results.json` L187-189, L530-532):**
  - `.tdata.TLS_FREEZE_ZERO PROGBITS ... WAT` (constant zero `u64` -> `PROGBITS` `.tdata`!)
  - `.tdata.TLS_NONZERO PROGBITS ... WAT` (non-zero `Cell::new(7)` -> `PROGBITS` `.tdata`)
  - `.tbss.TLS_ZERO NOBITS ... WAT` (zero `Cell::new(0)` -> `NOBITS` `.tbss`)
- In the linked PIE binary (`readelf -l`, `probe_results.json` L239), all `.tdata` + `.tbss` sections pack into a single ELF `PT_TLS` program header (`TLS ... 0x000028 0x000070 R 0x8`, where `FileSiz = 0x28` < `MemSiz = 0x70`, covering `.tbss` zero-fill per thread!).

#### 3.3 PIE Upgrade vs. `cdylib` TLS Model Preservation Matrix

Empirical measurements across all four `-Z tls-model` values on both `--crate-type=bin` (PIE) and `--crate-type=cdylib` (`probe_results.json` L154-725) confirm `TargetMachine::getTLSModel` (`TargetMachine.cpp` L262-287) (`Basis: source, execution`):

| `-Z tls-model` | LLVM IR Attribute on `#[thread_local]` | `--crate-type=bin` (PIE) Relocation & x86-64 Code | `--crate-type=cdylib` `.o` Relocation & Disasm | `cdylib` Link Result & Multithread Binary Check |
| --- | --- | --- | --- | --- |
| `local-exec` | `thread_local(localexec)` | `R_X86_64_TPOFF32` (`%fs:0x0`) | `R_X86_64_TPOFF32` (`addq/movq %fs:0x0`) | `cdylib` link **FAILS (`rc=1`)**; PIE binary runs cleanly (`TLS_MAIN=7 TLS_CHILD=99 TLS_ZERO_MAIN=0 TLS_ZERO_CHILD=123`) |
| `initial-exec` | `thread_local(initialexec)` | `R_X86_64_GOTTPOFF` (GOT-indirect `%fs:(%rax)`) | `R_X86_64_GOTTPOFF` (`movq (%rip), %rax` + `%fs:(%rax)`) | `cdylib` links (`rc=0`); PIE binary runs cleanly |
| `global-dynamic` | `thread_local` | **Upgraded to `R_X86_64_GOTTPOFF` (`InitialExec`)** because `LLVMRustSetModulePIELevel` sets `IsPIE = true` | Preserved: `R_X86_64_TLSGD` + `R_X86_64_PLT32 __tls_get_addr` | `cdylib` links (`rc=0`); PIE binary runs cleanly |
| `local-dynamic` | `thread_local(localdynamic)` | **Upgraded to `R_X86_64_GOTTPOFF` (`InitialExec`)** under PIE | Preserved: `R_X86_64_TLSLD` (`__tls_get_addr`) + `R_X86_64_DTPOFF32` | `cdylib` links (`rc=0`); PIE binary runs cleanly |

### 4. Kernel-Checked Lean v4.34.1 Mechanization (`support/StaticAddressIdentityCyclesAndTlsModelsSoundness.lean`)

`support/StaticAddressIdentityCyclesAndTlsModelsSoundness.lean` (1,739 total lines; 58 proved theorems; 0 `sorry`; 0 `Classical.choice`; 0 `omega`/`bv_decide`/`native_decide`; 0 `partial def`; 0 `._unsafe_rec`; 0 user axioms) formalizes a small-step/structural-recursion semantics of the three subsystems (`Basis: derived, execution`):

1. **Two-Phase Static/Const Initializer Graph (`evalDeclInitializer` via `reserveStatics` + structural `evalExprAux`, L300-1015):**
   - Models `InitExpr` nodes (`.litNat`, `.pair`, `.addrOf target`, `.readVal target`) and `DeclKind` (`.staticItem` vs. `.constItem`), distinguishing value-dependency edges `exprValueDeps` (where `.addrOf target` adds `target` **only if `target` is `.constItem`**, whereas `.addrOf` to `.staticItem` has no value edge!) from `.readVal target` (always adds a value edge).
   - **Main Theorem 1 — `two_phase_static_acyclicity_soundness` (L828-887, axioms `[propext, Quot.sound]`):** Whenever `rank : Nat → Nat` strictly decreases along all `exprValueDeps` edges (`rank v < rank d.declId`), every declaration in `decls` evaluates via `evalDeclInitializer` to `.ok` with injective reserved static `allocId`s (`1000 + d.declId`) — **even when `static` initializers contain arbitrary `addrOf` cycles** (explicitly witnessed on concrete mutual-ref + self-ref `static` cycles in `static_addr_of_cycle_concrete_witness`, L888).
   - **Main Theorem 2 — `value_cycle_e0391_necessity` (L969-996, axioms `[propext]`):** Any self-value dependency (`self_value_cycle_never_ok`, L900 -> `E0080`) or mutual `.readVal` cycle (`A` reading `B`, `B` reading `A`, `value_cycle_readval_never_ok`, L921) never returns `.ok` regardless of fuel, concretely emitting `E0391` on both mutual static value cycles (`mutual_value_cycle_emits_e0391`, L997, `[]` axioms) and mutual `const` reference cycles (`const_ref_cycle_e0391_contrast`, L1010, `[]` axioms).
2. **`unnamed_addr` Constant Deduplication & `static` Disjointness (`rustcLowerToLlvm` -> `globalOptRefine` -> `applyConstantMergePair`, L1016-1370):**
   - **Main Theorem 3a — `unnamed_addr_dedup_preserves_all_deref_observations` (L1191-1250, axioms `[propext]`):** Merging any valid `canMergeGlobals gOld gNew = true` pair (including two promoted `private unnamed_addr constant` items) preserves `obsDerefByte` across every symbol `s` and every byte offset `off`.
   - **Main Theorem 3b — `non_unnamed_addr_static_preserves_address_distinctness` (L1258-1288, axioms `[propext]`):** Two distinct `static` items `s1 ≠ s2` (even when `globalOptRefine` marks uncompared exported statics with `unnamedAddr = .none` vs. `canMergeGlobals` checks `.global_` — specifically `exported_static_local_unnamed_addr_still_unmergeable`, L1289-1309) satisfy `canMergeGlobals = false` and `obsPtrEq m' s1 s2 = false`.
   - **`mixed_merge_downgrades_survivor_and_preserves_static_disjointness` (L1310-1370, axioms `[propext]`):** Mechanizes LLVM `ConstantMerge.cpp` L110-111: absorbing one promoted `unnamed_addr` constant `ua` into a non-`unnamed_addr` static `st1` sets the survivor's `unnamedAddr := .none`, blocking any second distinct static `st2` from subsequently merging (`obsPtrEq = false`), preserving `items.static.storage-disjointness`.
3. **ELF TLS Section Classification, Relocations & Thread Non-Interference (L1371-1680):**
   - Classifies `.tdata` vs. `.tbss` (`freeze_zero_tls_in_tdata_not_tbss` L1456, `cell_zero_tls_in_tbss_not_tdata` L1459, `cell_nonzero_tls_in_tdata` L1462) and PIE vs. `cdylib` relocation lowering (`tls_model_pie_upgrades_dynamic_and_cdylib_rejects_localexec`, L1465).
   - **Main Theorem 4 — `tls_noninterference_trace` (L1610-1633, empty axioms `[]`):** Across ANY finite sequence of thread spawns and TLS writes `ops : List TlsOp` where no operation targets thread `t2` (`opTargetTid op ≠ t2`), every `#[thread_local]` byte read `tlsRead (execTlsTrace st ops) (llvmThreadLocalAddress t2 off)` returns the exact pre-trace value for thread `t2`, complemented by `tls_write_updates_self_preserves_other_slots_and_threads` (L1634) and `tls_main_child_concrete_witness` (L1677).
4. **Sharpness Counterexamples (L1681-1739):**
   - `ce1_erroneous_unnamed_addr_on_static_breaks_disjointness` (L1694): proves that omitting the no-`unnamed_addr` discipline on `static` items causes `ConstantMerge` to fuse `s1` and `s2` (`obsPtrEq = true`).
   - `ce2_sharing_tls_ptr_across_threads_violates_isolation` (L1727): proves why `memory.rs` (`global_root_pointer`) forbids leaking a single thread's TLS pointer into a cross-thread global constant (`99 ≠ 7`).

### 5. Mapping to Anneal Verified Compilation Scope (`joshlf/anneal`)

Examining `trusted/lean/Trusted/MirAst.lean` (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, L504-600) establishes the exact gap between Anneal's current stateless/scalar MIR slice and Rust's global/TLS semantics (`Basis: source, derived`):

- `ConstLit` currently admits only `.scalar (bits : BitVec 128)` and `.zeroSized` (`MirAst.lean` L504-507), and `Rvalue` explicitly excludes `Rvalue::ThreadLocalRef(DefId)` from lowered syntax (`MirAst.lean` L570-597 notes unmodeled variants fail closed as `.unsupported` during MIR capture).
- Extending Anneal past scalar/local memory to verify safe/unsafe pointers derived from `&'static T`, `&'static [u64]` promoted slices, cyclic `static` graphs, or `#[thread_local]` statics requires:
  1. Preserving the two-level provenance distinction in `Trusted.MirSemantics`: `static` allocations MUST remain pointer-disjoint from each other and from other statics (`&S1 != &S2`), whereas promoted/constant `GlobalAlloc::Memory` pointers MUST treat cross-provenance raw address equality (`usize` / thin-pointer equality) as non-deterministic (`2` in CTFE `machine.rs:360-384`), never asserting inequality `&C1 != &C2`.
  2. Modeling two-phase static reservation without requiring a globally acyclic pointer graph on address-of edges (only value-dependency reads require acyclicity).
  3. Keeping `#[thread_local]` slots indexed by thread ID `(tid, sym, off)` rather than as process-global addresses, preventing unsound cross-thread aliasing of `ThreadLocalRef` addresses across `Rvalue::ThreadLocalRef` / coroutine yield points.

## Boundaries

- **Non-ELF object formats and emulated TLS (`known not to apply` / `not examined`) (`Basis: source`)**:
  - `known not to apply`: Target triples using emulated TLS (`TlsModel::Emulated`), Mach-O TLV descriptors (`__thread_vars`/`__thread_data`/`__thread_bss`), Windows COFF TLS directories (`.tls$`), and WebAssembly custom-section statics (`consts.rs` L487-504) use distinct IR/object representations and do **not** emit ELF `.tdata`/`.tbss` sections or `R_X86_64_{TPOFF32,GOTTPOFF,TLSGD,TLSLD,DTPOFF32}` relocations.
  - `not examined`: Empirical compilation and disassembly were restricted to `x86_64-unknown-linux-gnu`; `aarch64` TLSDESC (`Options.EnableTLSDESC`) and `gnu2` TLS dialects were not compiled or benchmarked.
- **Zero-sized `static` items (`known not to apply`) (`Basis: normative, source`)**:
  - `known not to apply`: `rust-lang/reference` (`src/items/static-items.md` L19) restricts `items.static.storage-disjointness` to statics with *"a size of at least 1 byte"*; CTFE pointer equality (`const_eval/machine.rs` L349) mirrors this by checking strict in-bounds offsets (`a_offset < a_info.size && b_offset < b_info.size`), returning `2` (indeterminate) for ZST or one-past-the-end pointers. Zero-sized `static` items are outside our address-disjointness claims.
- **User `#[link_section]`, `#[used]`, `internal`/`extern "C"` statics with relocations, and mutable non-TLS statics (`known not to apply` / `not examined`) (`Basis: source, execution`)**:
  - `known not to apply`: Any `static` carrying `#[link_section]` triggers `GV->hasSection() == true`, bypassing `isSuitableForBSS` (`TargetLoweringObjectFile.cpp` L94-95) and excluding it from `ConstantMerge` (`ConstantMerge.cpp` L96). Any global whose initializer contains relocations (`C->needsRelocation()`) leaves `.rodata` for `.data.rel.ro` (`TargetLoweringObjectFile.cpp` L305).
  - `not examined`: Linker-time ICF (`--icf=safe`/`--icf=all` in LLD vs. GNU `ld`) across multiple compilation units (cross-CGU ThinLTO/LTO behavior) was `not examined` empirically beyond `opt -passes=constmerge` single-module IR passes and single-crate object/PIE/`cdylib` builds.
- **Non-`const` interior mutability on `#[thread_local] static` vs. `std::thread::LocalKey` lazy/OS wrappers (`not examined`) (`Basis: source`)**:
  - `not examined`: This report examines direct `#[cfg_attr(..., thread_local)]` / `#![feature(thread_local)]` LLVM IR and ELF lowering directly on `#[thread_local] static`. Library `thread_local! { ... }` fallback paths (`pthread_key_create` / lazy destructors on non-native TLS targets) were `not examined` in this run.
- **Rustc version drift between `1.98.0-nightly` and newer upstream revisions (`unknown`) (`Basis: source, execution`)**:
  - `unknown`: Live binary compilation was performed on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`). While upstream source inspection against `rust-lang/rust` HEAD (`058c701055c4b6f60f622d616afc0349911c38c3`) and `49d734536222bf28bb6d07d885b3a81d145981da`, as well as `llvm/llvm-project` HEAD (`9e1b2c3446261ab1a5063f442453510903ca80b8`), showed identical control flow in the audited functions, any runtime behavioral shift introduced in LLVM 23+ or future LTO passes without re-execution remains `unknown` for those uncompiled toolchains.
- **CTFE query stack internals outside `rustc_const_eval` (`unsupported` / `not examined`) (`Basis: derived`)**:
  - `unsupported`: `StaticAddressIdentityCyclesAndTlsModelsSoundness.lean` models idealized CTFE query graphs, single-hop `ConstantMerge` pair reductions, ELF section classification rules, and abstract trace-level multi-thread TLS banks rather than full MIR statement execution, Rust borrow checking, stack/frame retagging, or x86-64 machine-code semantics. Consequently, Lean proofs provide foundational soundness for those abstractions and do **not** verify LLVM instruction selection or ELF dynamic linker `ld.so` relocation math end-to-end.

## Evidence

### Normative Anchors (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`)

- [`src/items/static-items.md`](https://github.com/rust-lang/reference/blob/c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c/src/items/static-items.md): `items.static.intro` (L12-13), `items.static.storage-disjointness` (L18-19), `items.static.init` (L24-25), `items.static.read-only` (L27-28).
- [`src/items/constant-items.md`](https://github.com/rust-lang/reference/blob/c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c/src/items/constant-items.md): `items.const.intro` (L10-11), `items.const.behavior` (L13-14), `items.const.static-temporary` (L22-23).

### Compiler Source Anchors (`rust-lang/rust` & `llvm/llvm-project` & `joshlf/anneal`)

- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (with `058c701055c4b6f60f622d616afc0349911c38c3` HEAD offsets noted):**
  - `compiler/rustc_codegen_llvm/src/consts.rs`: `static_addr_of_mut` (`14210df0` L236-259; `058c7010` L296-318; `49d73453` L294-316) calls `set_linkage(gv, PrivateLinkage)` and `set_unnamed_address(gv, UnnamedAddr::Global)`; `static_addr_of_impl` (`14210df0` L264-286) sets `set_global_constant(gv, true)` and caches in `self.const_globals`; `get_static_inner` (`14210df0` L307-408) sets `set_thread_local_mode(g, self.tls_model)` on TLS; `codegen_static_item` (`14210df0` L410-539) forwards mutability (`L474-476`), sets `self.tls_model` (`L480-482`), and omits `set_unnamed_address`.
  - `compiler/rustc_codegen_llvm/src/context.rs`: `to_llvm_tls_model` (`14210df0` L170-178; `058c7010` L177-185); `LLVMRustSetModulePIELevel` (`14210df0` L259-265).
  - `compiler/rustc_codegen_llvm/src/builder.rs`: `StaticBuilderMethods::get_static` (`14210df0` L1474-1488) emits `self.call_intrinsic("llvm.threadlocal.address", ...)`.
  - `compiler/rustc_codegen_ssa/src/mir/rvalue.rs`: `Rvalue::ThreadLocalRef` (`14210df0` L646-676) lowers local TLS via `bx.get_static` and cross-crate TLS via `InstanceKind::ThreadLocalShim`.
  - `compiler/rustc_const_eval/src/const_eval/eval_queries.rs`: `setup_for_eval` (`14210df0` L26-64; `058c7010` L54-91), `eval_static_initializer_provider` (`14210df0` L337-346; `058c7010` L391-400).
  - `compiler/rustc_const_eval/src/interpret/util.rs`: `create_static_alloc` (`14210df0` L75-93; `058c7010` L79-96) calls `GlobalAlloc::Static(...).size_and_align`, `reserve_and_set_static_alloc`, and initializes `ecx.machine.static_root_ids`.
  - `compiler/rustc_const_eval/src/interpret/eval_context.rs`: `InterpCx::eval_global` (`14210df0` L586-600) skips evaluation via `reserve_and_set_static_alloc` iff `is_static`.
  - `compiler/rustc_const_eval/src/const_eval/machine.rs`: `before_alloc_access` (`14210df0` L997-1021) triggers `RecursiveStatic` (`E0080`) or `tcx.eval_static_initializer` (`E0391`); pointer comparison (`14210df0` L345-384).
  - `compiler/rustc_const_eval/src/interpret/memory.rs`: `global_root_pointer` (`14210df0` L190-217) rejects pointers from non-TLS constants/globals into `is_thread_local_static`.
  - `compiler/rustc_middle/src/mir/interpret/mod.rs`: `GlobalAlloc::size_and_align` (`14210df0` L354-394), `reserve_and_set_dedup` (L462-480), `reserve_and_set_static_alloc` (L490-493).
  - `compiler/rustc_session/src/{options.rs,session.rs}` & `compiler/rustc_target/src/spec/mod.rs`: `parse_tls_model` (`14210df0` L1717; `058c7010` L1951), `Session::tls_model` (`14210df0` L744-746; `058c7010` L379-381), `pub enum TlsModel` (`14210df0` L1003; `058c7010` L1012).
- **`llvm/llvm-project@fc4aad7b5db3fff421df9a9637605b9ca5667881` (with HEAD `9e1b2c3446261ab1a5063f442453510903ca80b8` verified via `support/verify_pins.py`):**
  - `llvm/lib/Transforms/IPO/ConstantMerge.cpp`: `isUnmergeableGlobal` (L91-101), `makeMergeable` (L104-113, `New->setUnnamedAddr(GlobalValue::UnnamedAddr::None)` at L111), `replace` (L115-132), `mergeConstants` (L134-215).
  - `llvm/lib/Transforms/IPO/GlobalOpt.cpp`: `processGlobal` (L1648-1685; `UnnamedAddr::Local` assignment for external globals at L1663-1664).
  - `llvm/lib/Target/TargetLoweringObjectFile.cpp`: `isSuitableForBSS` (L82-99; rejects `GV->isConstant()` at L90-91), `getKindForGlobal` (L248-315; `isThreadLocal()` at L265-275, `!hasGlobalUnnamedAddr()` at L309-310).
  - `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp`: `getELFSectionFlags` (L549-560, `SHF_TLS`/`SHF_MERGE`), `SelectSectionForGlobal` (L938-955).
  - `llvm/lib/Target/TargetMachine.cpp`: `getSelectedTLSModel` (L185-200) and `getTLSModel` (L262-287, `IsSharedLibrary = RM == Reloc::PIC_ && !IsPIE` at L265).
  - `llvm/lib/CodeGen/SelectionDAG/SelectionDAGBuilder.cpp`: `Intrinsic::threadlocal_address` lowering (L8176-8179).
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
  - `trusted/lean/Trusted/MirAst.lean` (L504-600) and `trusted/audit/TrustedBoundary.lean` (L1-90).
- **Primary-Source Pin Receipt:** `support/verify_pins.py` verified 49/49 files across all 8 commits (`all_verified: true`) in [`support/pin_receipt.json`](support/pin_receipt.json).

### Empirical Execution Receipts ([`support/probe_static_identity_cycles_and_tls.py`](support/probe_static_identity_cycles_and_tls.py) & [`support/probe_results.json`](support/probe_results.json))

- **`unnamed_addr` vs. `static` & `-O2` `local_unnamed_addr` (`probe_results.json` L6-72):**
  - `-O0`: `@S = constant ...`, `@S_DUP_1 = constant ...`, `@S_DUP_2 = constant ...`, `@alloc_011d402fc2fd12f79ff2bc7691f0df1d = private unnamed_addr constant [16 x i8] ...`; `readelf -S -W` shows `.rodata.S`, `.rodata.S_DUP_{1,2}` (`PROGBITS A`) vs `.rodata.cst16` (`PROGBITS AM 0x10`); binary stdout `STATIC_ADDR_EQ=true STATIC_DUP_EQ=false STATIC_PRIV_DUP_EQ=false CONST_EQ_PROMOTED=true CONST_EQ_DUP=true`.
  - `-O2`: `@S_DUP_1` and `@S_DUP_2` emit `local_unnamed_addr constant`, internal `@_RNvCsaOB7WAnZlIb_19static_vs_const_lib8S_PRIV_1` and `@_RNvCsaOB7WAnZlIb_19static_vs_const_lib8S_PRIV_2` remain `internal constant` (`GS.IsCompared = true`), and binary stdout stays `STATIC_ADDR_EQ=true STATIC_DUP_EQ=false STATIC_PRIV_DUP_EQ=false CONST_EQ_PROMOTED=true CONST_EQ_DUP=true`.
- **`opt -passes=constmerge` ablation (`probe_results.json` L74-100):**
  - Unnamed pair: `merged_to_single: true` (`@UA_2 = private unnamed_addr constant ...`, `%eq = icmp eq ptr @UA_2, @UA_2`).
  - Non-`unnamed_addr` pair: `preserved_distinct: true` (`@ST_1` and `@ST_2` survive separately).
  - Mixed triple (`@ST_1`, `@ST_2`, `@UA_2`): `total_surviving_globals: 2`, survivor `@UA_2` stripped to `@UA_2 = private constant ...`, `@ST_2` preserved separate.
- **Cycle checks (`probe_results.json` L103-151):**
  - `cyclic_static_value_e0391`: `rc = 1`, `error[E0391]: cycle detected when evaluating initializer of static A`.
  - `cyclic_static_self_value`: `rc = 1`, `error[E0080]: encountered static that tried to access itself during initialization`.
  - `cyclic_const_ref_e0391`: `rc = 1`, `error[E0391]: cycle detected when simplifying constant for the type system A`.
  - `cyclic_static_address_of_lazy_alloc`: `rc = 0`, runtime stdout `CYC_REF_OK=10,20 ROUNDTRIP=10,20 SELF_CYCLE_EQ=true AB_DISTINCT=true`.
- **`#[thread_local]` & `-Z tls-model` matrix (`probe_results.json` L153-725):**
  - Object sections: `.tdata.TLS_FREEZE_ZERO PROGBITS WAT`, `.tdata.TLS_NONZERO PROGBITS WAT`, `.tbss.TLS_ZERO NOBITS WAT`.
  - Binary `PT_TLS`: `TLS 0x0556b0 ... 0x000028 0x000070 R 0x8`.
  - Multithread execution (under all 4 TLS models): `TLS_MAIN=7 TLS_CHILD=99 TLS_ZERO_MAIN=0 TLS_ZERO_CHILD=123 TLS_PTR_DISTINCT=true`.
  - `cdylib` relocations: `local-exec` (`R_X86_64_TPOFF32`, `cdylib_link_returncode = 1`); `initial-exec` (`R_X86_64_GOTTPOFF`, `rc = 0`); `global-dynamic` (`R_X86_64_TLSGD` + `__tls_get_addr`, `rc = 0`); `local-dynamic` (`R_X86_64_TLSLD` + `__tls_get_addr` + `R_X86_64_DTPOFF32`, `rc = 0`).

### Mechanized Lean v4.34.1 Receipt ([`support/StaticAddressIdentityCyclesAndTlsModelsSoundness.lean`](support/StaticAddressIdentityCyclesAndTlsModelsSoundness.lean) & [`support/lean_check_receipt.json`](support/lean_check_receipt.json))

- Lean compiler version: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.
- Standalone flags: `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`standalone_exit_code = 0`).
- Metrics verified by [`support/check_lean.py`](support/check_lean.py): `1,739` total lines (`1,596` non-empty, `1,376` code lines), `51` `noncomputable def`s (`0` plain/partial defs), `58` theorems checked across `657` namespace constants in MetaM, `0` `_unsafe_rec`, `0` `isUnsafe`, `0` user axioms, `0` opaques, **`0` `Classical.choice`**, **`0` `sorryAx`**, **`0` `Lean.ofReduceBool`/`Lean.trustCompiler`**.
- Axiom footprints confirmed for all main theorems and counterexamples (`lean_check_receipt.json` L37-142): `two_phase_static_acyclicity_soundness` (`[propext, Quot.sound]`), `value_cycle_e0391_necessity` (`[propext]`), `mutual_value_cycle_emits_e0391` (`[]`), `const_ref_cycle_e0391_contrast` (`[]`), `unnamed_addr_dedup_preserves_all_deref_observations` (`[propext]`), `non_unnamed_addr_static_preserves_address_distinctness` (`[propext]`), `exported_static_local_unnamed_addr_still_unmergeable` (`[propext]`), `mixed_merge_downgrades_survivor_and_preserves_static_disjointness` (`[propext]`), `tls_noninterference_trace` (`[]`), `tls_write_updates_self_preserves_other_slots_and_threads` (`[propext]`), `ce1_erroneous_unnamed_addr_on_static_breaks_disjointness` (`[propext]`), `ce2_sharing_tls_ptr_across_threads_violates_isolation` (`[propext]`).

## Revalidation

1. Re-run the empirical `rustc`, LLVM `opt`, `readelf`, and multithreaded Linux TLS probe script cleanly in temporary directories and regenerate `support/probe_results.json`:

   ```bash
   python3 reports/rustc-static-address-identity-cyclic-refs-unnamed-addr-and-thread-local-tls/support/probe_static_identity_cycles_and_tls.py
   ```

2. Re-verify the standalone Lean v4.34.1 mechanization, pure-source hygiene (0 `sorry`, 0 `omega`, 0 `Classical.choice`, all `def`s `noncomputable`), MetaM `_unsafe_rec == 0` constant audit, and `#print axioms` footprints:

   ```bash
   python3 reports/rustc-static-address-identity-cyclic-refs-unnamed-addr-and-thread-local-tls/support/check_lean.py
   ```

3. Re-verify all 8 pinned upstream commits and 49 cited source files against live upstream snapshots (providing `--local-anneal-git` when offline or unauthenticated on private forks):

   ```bash
   python3 reports/rustc-static-address-identity-cyclic-refs-unnamed-addr-and-thread-local-tls/support/verify_pins.py --local-anneal-git <path-to-anneal-repo>
   ```

4. Recompute the corpus catalog and validate the `reference-corpus/1` schema, headings, subjects, topics, and self-contained presentation rules:

   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
