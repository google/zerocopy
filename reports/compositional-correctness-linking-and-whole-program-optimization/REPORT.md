# Compositional Correctness, Multi-Language Linking, ThinLTO Summary Importing, and Whole-Program Optimization

## Summary

A verified Rust compiler cannot assume that an entire binary is compiled as a single closed translation unit: standard Cargo builds partition each crate into multiple Codegen Units (CGUs), share generic monomorphizations across `rlib` dependencies (`-Zshare-generics`), run multi-module ThinLTO or FatLTO across CGUs and upstream crates, and link verified Rust code with unverified Rust crates, C FFI libraries, and language runtimes (`core`, `alloc`, `compiler_builtins`, `libunwind`). Synthesizing primary-source inspection of `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`), `llvm/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`23.1.1`), and `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (`3.18`) with eight compositional compiler-verification frameworks (`CompCert Linking.v`, `SepCompCert`, `Compositional CompCert`, `CompCertM`, `CompCertO`, `CCR`, `DimSum`, and Robust/Secure Compilation) yields four foundational results, mechanized in Lean `v4.34.1` ([`support/CompositionalLinkingAndThinLtoWpoProbe.lean`](support/CompositionalLinkingAndThinLtoWpoProbe.lean), 320 lines, 8 theorems, zero `sorryAx`):

1. **Compositional Separate Compilation and Environment Assumptions Across Eight Frameworks:**
   - Syntactic pass-commutation linking (`CompCert` `Linking.v` and `SepCompCert` POPL 2016) requires all linked units to share a homogeneous memory model and pass pipeline (`TransfLink`).
   - Open-simulation and interaction frameworks (`Compositional CompCert` POPL 2015, `CompCertM` POPL 2020, `CompCertO` POPL 2021) parameterize module transitions by ABI calling conventions and Kripke memory-injection worlds (`ro @ c_injp @ wt_c @ ca_injp`), assuming that any external or unverified callee preserves read-only globals, private stack frames, and callee-saved registers.
   - Specification-indexed and event-based frameworks (`CCR` POPL 2023 and `DimSum` POPL 2023) replace shared global memory with per-symbol Hoare contracts (`FnContract`) or angelic/demonic event streams (`ModTrans`), enabling horizontal linking (`horizontal_link_sound`) across heterogeneous languages (Rust MIR, C, and assembly) without exposing internal pass representations.
   - By contrast, **Robust / Secure Compilation** (Abate et al. CSF 2019; Patrignani et al. TOPLAS 2019) drops all behavioral assumptions on the unverified context and enforces trace-property preservation (`RTP` / `RSC`) dynamically via SFI/Wasm sandboxing or hardware capabilities.
2. **Closed-World Whole-Program Optimizations (WPO) Under Separate Compilation:**
   - In CompCert 3.18 (`backend/Unusedglob.v` and `Unusedglobproof.v`), global dead-code elimination computes the transitive closure `used_globals` from `prog_main` and `prog_public`. It commutes with separate compilation (`TransfUnusedglobLink`) **if and only if** every symbol referenced across compilation units is declared in `prog_public` (`prog_public p1 = prog_public p2`) and private (`~In id (prog_public p)`) definitions do not collide across units.
   - Similarly, in `rustc` (`compiler/rustc_monomorphize/src/partitioning.rs:529-615, 757-968`) and LLVM (`lib/Transforms/IPO/{Internalize,SCCP,DeadArgumentElimination,GlobalDCE,WholeProgramDevirt}.cpp`), **Internalization**, **Interprocedural Constant Propagation (`IPSCCP`)**, **Dead-Argument Elimination (`DAE`)**, **Global DCE**, and **Devirtualization** are sound under separate compilation if and only if the transformed symbol is excluded from the external root set (`GUIDPreservedSymbols` $\cup$ `ExportLists`, which in `rustc` must explicitly preserve `#[no_mangle]`, `#[used]`, entrypoints, naked functions, weak lang items, and `RUSTC_STD_INTERNAL_SYMBOL` allocator shims `__rg_alloc`/`__rdl_alloc`). Theorem `wpo_internalize_ipsccp_sound` proves soundness under this closed-world premise, and `canary_open_world_ipsccp_unsound` proves that specializing an externally callable symbol in-place without cloning violates semantic preservation when an unrecorded external caller invokes it.
3. **How ThinLTO Summary-Based Importing and `rustc`'s `-Zshare-generics` Symbol Conventions Enter a Verification Theorem:**
   - Inspection of `compiler/rustc_codegen_llvm/src/back/lto.rs:345-780` and `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:1213-1584` shows that `rustc` ThinLTO builds a combined `ModuleSummaryIndex` across all CGUs and upstream `rlib` bitcode modules (`LLVMRustCreateThinLTOData`, passing `ImportEnabled = false` to `computeDeadSymbolsWithConstProp` at line 1314 to prevent premature static internalization bug `#60184`), and then runs four per-module transformations (`lto.rs:735-770`):
     1. `LLVMRustPrepareThinLTORename` (`renameModuleForThinLTO`: promotes internal symbols in `ExportLists` to hidden globals with `.llvm.<guid>` suffixes);
     2. `LLVMRustPrepareThinLTOResolveWeak` (`thinLTOFinalizeInModule`: resolves duplicate `LinkOnceODR`/`WeakODR` copies to the single prevailing copy selected by `getFirstDefinitionForLinker` and propagates summary attributes);
     3. `LLVMRustPrepareThinLTOInternalize` (`thinLTOInternalizeModule`: marks non-exported symbols `InternalLinkage`); and
     4. `LLVMRustPrepareThinLTOImport` (`FunctionImporter::importFunctions`: copies cross-module function bodies from `ModuleMap` into the importing CGU with **`available_externally`** linkage solely for inlining and interprocedural analysis, after which `available_externally` bodies are dropped prior to object emission).
   - In `compiler/rustc_symbol_mangling/src/lib.rs:274-319` and `partitioning.rs:215-256, 874-909`, generic functions and `#[inline]` cross-crate instances compiled under `-Zshare-generics` (`InstantiationMode::GloballyShared { may_conflict: true }`) include the instantiating crate ID (`upstream_monomorphization`) in their v0/legacy mangled symbol hash and are emitted with `LinkOnceODR`/`WeakODR` linkage. Both ThinLTO `available_externally` importing and linker deduplication of shared generics depend on the **Symbol Coherence (`WeakOdrCoherent`) Premise**: every `WeakODR` copy and `available_externally` summary body bearing symbol `GUID` must refine the same specification `c` (`thinLto_summary_import_sound` vs. `canary_incoherent_weak_odr_unsound`).
4. **Conditional Mixed-Binary Theorems and Their Four Classic Pitfalls:**
   - Conditional theorems ("if the unverified parts meet their contracts, the verified parts meet theirs") are subject to four soundness hazards: (a) **circular rely-guarantee vacuity** (`(P -> Q) /\ (Q -> P)` satisfied by `P = Q = False`, `canary_circular_assumption_vacuity`), which must be broken by well-founded call-depth or step-index induction (`conditional_mixed_binary_sound`); (b) **reentrant callbacks observing half-updated private ADT invariants** (`canary_reentrant_callback_invariant_breach`), requiring all module invariants to be re-established before any external call; (c) **stack/borrow frame aliasing across FFI**, requiring disjoint public/private frame partitioning; and (d) **unwinding across non-unwinding ABIs** (`extern "C"`), requiring `UnwindAction::Terminate(Reason::Abi)` landing-pad filters.

## Applicability

The findings in this report apply to multi-CGU and multi-crate Rust compilation, ThinLTO and FatLTO optimization pipelines, and FFI/mixed-binary verification across:
1. **`rust-lang/rust` (`1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67`)**: `compiler/rustc_monomorphize/src/partitioning.rs`, `compiler/rustc_symbol_mangling/src/{lib,v0,legacy}.rs`, `compiler/rustc_codegen_ssa/src/back/{lto,symbol_export}.rs`, `compiler/rustc_codegen_llvm/src/back/lto.rs`, and `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp`.
2. **`llvm/llvm-project` (`23.1.1`, commit `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)**: `llvm/lib/Transforms/IPO/{FunctionImport,Internalize,DeadArgumentElimination,SCCP,GlobalDCE,WholeProgramDevirt}.cpp`, `llvm/include/llvm/IR/ModuleSummaryIndex.h`, and `llvm/lib/LTO/LTO.cpp`.
3. **Compositional Compiler Verification Precedents**: CompCert 3.18 (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`), CompCertO (`SJTU-PLV/CompCert@e3d03ed822a7aaf452b7022c347187ed1efc1c12`, POPL 2021), SepCompCert (POPL 2016), Compositional CompCert (POPL 2015), CompCertM (POPL 2020), CCR (POPL 2023), DimSum (POPL 2023), and Robust/Secure Compilation (CSF 2019 / TOPLAS 2019).
4. **Mechanized Verification Environment**: Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) in [`support/CompositionalLinkingAndThinLtoWpoProbe.lean`](support/CompositionalLinkingAndThinLtoWpoProbe.lean).

## Findings

### 1. Composing With Unverified and Heterogeneous Code: Eight Precedent Frameworks

Basis: source + normative literature ([`support/compositional_and_wpo_matrix.json`](support/compositional_and_wpo_matrix.json); `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` `common/Linking.v`; `SJTU-PLV/CompCert@e3d03ed822a7aaf452b7022c347187ed1efc1c12` `common/Smallstep.v:1572-1603`).

| Framework | Core Composition Mechanism | What It Assumes About the External / Unverified Environment | Support for Heterogeneous Languages & Callbacks |
| :--- | :--- | :--- | :--- |
| **CompCert 3.18 (`Linking.v`)** | Syntactic `Linker` typeclass + `TransfLink` pass commutation (`separate_transf_c_program_correct`) | All linked units are compiled by the exact same CompCert pipeline; external syscalls obey `extcall_properties` (`Events.v:232-310`) | Homogeneous C-to-Asm only; mutual recursion among C units |
| **SepCompCert (POPL 2016)** | Per-unit `match_prog` relation with `TransfIfLink` (`Compiler.v:212-220`) | Linked units share CompCert's closed-world `Genv` and block+offset memory model at the target/IR boundary | Homogeneous IRs; allows mixing `-O0` and `-O2` CompCert units |
| **Compositional CompCert (POPL 2015)** | Interaction semantics (`AtExternal`/`AfterExternal`) + structured memory injections | Environment transitions obey structured memory-injection growth and rely-guarantee permission invariants (never overwriting caller-private blocks) | Links CompCert C with VST separation-logic proofs and hand-verified assembly; supports reentrant callbacks |
| **CompCertM (POPL 2020)** | Refinement Under Self-related Contexts (`RUSC`) + mixed C/Asm operational state | Context modules are self-related under a fixed finite ladder of Kripke memory relations (`freerg`, `injp`) | Links C and hand-written assembly with mutual recursion |
| **CompCertO (POPL 2021)** | Open simulations parameterized by Kripke simulation conventions $\mathbb{R} : \mathsf{callconv}\;\mathit{li}_A\;\mathit{li}_B$ | Environment queries and replies satisfy the calling convention $\mathbb{R} = \mathsf{ro} \cdot \mathsf{c\_injp} \cdot \mathsf{wt\_c} \cdot \mathsf{ca\_injp}$ (read-only globals preserved, memory injection grows monotonically, ABI registers/stack slots typed and framed) | Full horizontal (`link`) and vertical (`comp`) composition across C, Clight, and Asm with callbacks |
| **CCR (POPL 2023)** | Conditional Contextual Refinement combining CompCert refinement with Iris Hoare triples (`cond_refines`) | Unverified/external imports satisfy their declared separation-logic Hoare triples (pre/postconditions + ghost PCM frame preservation) at every call | Links verified code, Iris-specified modules, and assembly under conditional specs |
| **DimSum (POPL 2023)** | Decentralized angelic/demonic event-stream transitions (`ModTrans`) | Connected modules satisfy the event-stream protocol wrapper (no shared memory type required) | Links arbitrary languages (Rust/Rec, C heaps, flat Asm) with arbitrary reentrant callbacks |
| **Robust / Secure Compilation (CSF 2019 / TOPLAS 2019)** | Robust Trace Property Preservation (`RTP` / `2HP` / `RSC`) via dynamic checks, SFI/Wasm sandboxing, or capabilities | **Zero behavioral trust** in the unverified context; assumes only that hardware/runtime enforces the sandbox/capability boundary | Protects verified module invariants against adversarial contexts via dynamic boundary wrappers |

---

### 2. Whole-Program Optimization (WPO), ThinLTO Summary Importing, and `rustc` Symbol Conventions

Basis: source (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` `backend/Unusedglob.v`; `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` `compiler/rustc_monomorphize/src/partitioning.rs`, `compiler/rustc_symbol_mangling/src/lib.rs`, `compiler/rustc_codegen_llvm/src/back/lto.rs`, `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp`; `llvm/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` `llvm/lib/Transforms/IPO/*.cpp`).

#### 2.1 How CompCert States Closed-World Facts (`Unusedglob.v` and `TransfUnusedglobLink`)

In CompCert 3.18 (`driver/Compiler.v:245, 288`), `Unusedglob.transform_program` is the sole interprocedural dead-global elimination pass in the pipeline. To make a closed-world reachability optimization sound under separate compilation (`separate_transf_c_program_correct`), CompCert's `Unusedglobproof.v` states two explicit linking conditions in `match_prog`:
1. **Identical Public Root Interface (`prog_public p1 = prog_public p2`):** Every compilation unit carries an explicit list `prog_public : list ident` of externally visible symbols (corresponding to C declarations without `static`). `Unusedglob` seeds its worklist with `prog_public p` and eliminates only definitions `id` such that `~In id (prog_public p)` and `id` is unreachable from `prog_public p`.
2. **Closed Cross-Unit Reference Discipline:** CompCert's `Linker` for `AST.program` rejects linking two units if unit $A$ references a symbol `id` defined in unit $B$ unless `id` is declared in `prog_public` of both units. Consequently, any symbol kept private (`~In id (prog_public p)`) is guaranteed to have zero references from any other compilation unit linked later.

#### 2.2 Correctness Arguments for the Five Classical WPO Passes Under Separate Compilation

In `rustc` and LLVM 23.1.1, five whole-program optimizations rely on an analogous partition of symbols into **Exported / Preserved Roots** ($E$) and **Internalized / Module-Private Symbols** ($I = \text{Defs} \setminus E$):

1. **Internalization (`internalize_symbols` in `partitioning.rs:529-615`, `thinLTOInternalizeAndPromoteInIndex` in `PassWrapper.cpp:1378`, `llvm/lib/Transforms/IPO/Internalize.cpp`):**
   - Converts `Linkage::External` to `Linkage::Internal` whenever a mono-item is referenced only within a single CGU (`MonoItemPlacement::SingleCgu(home_cgu)` at `partitioning.rs:571-612`) and `can_be_internalized == true`.
   - **Soundness Side Condition in `rustc` (`partitioning.rs:599-607, 784-967`):** `can_be_internalized` must be forced to `false` (and the symbol added to `GUIDPreservedSymbols` in `PassWrapper.cpp:1296-1300`) not only for public exported APIs (`tcx.is_reachable_non_generic`), `#[no_mangle]`, and `#[used]`, but also for four compiler-implicit cross-unit roots:
     - (i) Entrypoint functions (`tcx.is_entrypoint(def_id)`, line 869), referenced by the synthesized C `main` stub;
     - (ii) Naked functions (`CodegenFnAttrFlags::NAKED`, lines 601–606), whose raw assembly references are opaque to LLVM LTO;
     - (iii) Weak lang items (`#[panic_handler]`, `oom`, lines 925–931), forward-referenced by `libcore` and resolved by the system linker; and
     - (iv) Standard-library internal symbols and externally implementable items (`RUSTC_STD_INTERNAL_SYMBOL | EXTERNALLY_IMPLEMENTABLE_ITEM`, lines 933–964, such as `__rg_alloc`, `__rdl_alloc`, `__rust_alloc`), which are wired up by a compiler-injected allocator shim object file at final link time.
2. **Interprocedural Constant Propagation (`IPSCCP` in `llvm/lib/Transforms/IPO/SCCP.cpp` and `computeDeadSymbolsWithConstProp` in `PassWrapper.cpp:1312`):**
   - Propagates constant argument values across call sites and replaces parameter uses with constants inside the callee body.
   - **Soundness Side Condition:** In-place body specialization is sound **only** if `f` has local linkage (`Linkage::Internal`, guaranteeing that all callers are inside the current module and pass `arg = c₀`, proved in `wpo_internalize_ipsccp_sound`). If `f` remains externally callable (`f ∈ E`), `IPSCCP` must either leave `f`'s signature/body general or emit a specialized internal clone `f.constprop.0` while preserving `f` for external callers (`canary_open_world_ipsccp_unsound`).
3. **Dead-Argument Elimination (`DAE` in `llvm/lib/Transforms/IPO/DeadArgumentElimination.cpp`):**
   - Strips unused parameters or unused return values from a function's calling convention.
   - **Soundness Side Condition:** Sound if and only if `F.hasLocalLinkage() && !F.hasAddressTaken()`. If `F`'s address is taken (stored in a function pointer or vtable) or `F` is externally visible, changing its ABI signature mismatches caller and callee register/stack layouts.
4. **Global Dead-Code Elimination (`GlobalDCE` in `llvm/lib/Transforms/IPO/GlobalDCE.cpp` and CompCert `Unusedglob.v`):**
   - Deletes unreachable functions and global variables with `InternalLinkage` or `AvailableExternallyLinkage`.
   - **Soundness Side Condition:** Sound whenever the initial live root set contains all externally visible symbols (`E`), all address-taken targets reachable from `E`, and all linker-synthesized roots (`llvm.used`, `llvm.compiler.used`). Note that in `PassWrapper.cpp:1310-1315`, `rustc` explicitly passes `ImportEnabled = false` to `computeDeadSymbolsWithConstProp` because `rustc`'s in-process ThinLTO sees only the current crate's CGUs and `rlib` bitcode—not external C objects or dynamic libraries—so aggressive cross-module dead-static stripping previously deleted live statics (`rust-lang/rust#60184`).
5. **Devirtualization (`WholeProgramDevirtPass` in `llvm/lib/Transforms/IPO/WholeProgramDevirt.cpp`):**
   - Replaces an indirect vtable call with a direct call (or conditional branch tree) when all implementations of a virtual method across the LTO unit resolve to a single target (or small constant table).
   - **Soundness Side Condition:** Requires a **closed vtable world** for that trait/type identifier (`!type` metadata with hidden/internal LTO visibility). In Rust, because `dyn Trait` fat pointers can be constructed in separately compiled `dylib`s or passed across FFI unless the trait is module-private (`pub(crate)` or private), devirtualization of public traits is sound only within single-target intraproc/interproc value-flow analysis (`IPSCCP` / inlining) or full closed-binary LTO (`-Clto=fat` with no dynamic plugins).

#### 2.3 How ThinLTO's Summary-Based Importing Enters a Compositional Theorem

In `compiler/rustc_codegen_llvm/src/back/lto.rs:345-780` and `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:1213-1488`, ThinLTO avoids merging all CGUs into one monolithic module by splitting optimization into a **global summary phase** (`LLVMRustCreateThinLTOData`, `PassWrapper.cpp:1272-1381`) and **four parallel per-CGU transformations** (`lto.rs:735-770`):

| ThinLTO Stage (`lto.rs` / `PassWrapper.cpp`) | LLVM Operation Invoked | Effect on Module Interface $M_i$ | Proof Obligation in an `OpenModule` Theorem |
| :--- | :--- | :--- | :--- |
| **0. Index Merge** (`PassWrapper.cpp:1277-1380`) | `readModuleSummaryIndex`, `ComputeCrossModuleImport`, `thinLTOResolvePrevailingInIndex` | Computes per-CGU `ImportLists`, `ExportLists`, `ResolvedODR`, and `ExportedGUIDs` from summary call graphs | Pure static oracle computation; does not alter semantics by itself |
| **1. Rename** (`lto.rs:738`, `PassWrapper.cpp:1404-1412`) | `renameModuleForThinLTO(Mod, Data->Index, ClearDSOLocal)` | Promotes `Internal` symbols in `ExportLists[i]` to hidden globals renamed `<sym>.llvm.<guid>` | Extends $M_i$'s exported symbol namespace `exports` with `<sym>.llvm.<guid>` paired with its proven internal contract |
| **2. ResolveWeak** (`lto.rs:746`, `PassWrapper.cpp:1415-1422`) | `thinLTOFinalizeInModule(Mod, DefinedGlobals, /*PropagateAttrs=*/true)` | Keeps the single prevailing copy (`getFirstDefinitionForLinker`) as `WeakODR` and converts non-prevailing copies to `available_externally`; propagates summary attributes (`readonly`, `nounwind`) | Requires **Symbol Coherence (`WeakOdrCoherent`)** across all CGUs defining `GUID`, plus soundness of summary-inferred attributes |
| **3. Internalize** (`lto.rs:756`, `PassWrapper.cpp:1425-1432`) | `thinLTOInternalizeModule(Mod, DefinedGlobals)` | Marks definitions not in `ExportedGUIDs` $\cup$ `ExportLists[i]` as `InternalLinkage` | Discharged by closed-world non-membership in `GUIDPreservedSymbols` $\cup$ `ExportLists[i]` (`wpo_internalize_ipsccp_sound`) |
| **4. Import** (`lto.rs:766`, `PassWrapper.cpp:1434-1488`) | `FunctionImporter::importFunctions(Mod, ImportList)` | Lazily parses upstream bitcode (`getLazyBitcodeModule`), strips `wasm.custom_sections` and `llvm.ident` (`#38184`), and inserts imported bodies into $M_i$ with **`available_externally`** linkage | An `available_externally` definition is a **specification-carrying ghost copy**: inlining it into $M_i$ is sound because its body satisfies the exact contract exported by the defining CGU (`thinLto_summary_import_sound`), and dropping it before object emission leaves the external symbol resolved by the defining CGU at link time |

#### 2.4 How `rustc`'s Symbol Conventions Enter a Verification Theorem

In `compiler/rustc_symbol_mangling/src/lib.rs:1-350` and `compiler/rustc_monomorphize/src/partitioning.rs:215-256, 874-909`:
- **Non-generic items (`!is_generic(instance)`):** Mangled symbol names incorporate the defining crate's name, `DefPath` disambiguators, and 64-bit `StableCrateId` (`-Cmetadata`), guaranteeing globally disjoint symbol names across crates (`lib.rs:40-77`).
- **Generic items and `-Zshare-generics` (`is_generic(instance) || is_globally_shared_function`, `lib.rs:151-160, 280-305`):**
  - When a generic function is instantiated locally (`InstantiationMode::LocalCopy`), or when `share_generics` is disabled (`partitioning.rs:905-908`), the instantiation is given `Visibility::Hidden` and internalized into its CGU (`Linkage::Internal`).
  - When `-Zshare-generics` is enabled (`config.rs:1521`, default on debug/incremental builds and for `#[inline(never)]` generics in `rlib`s at `partitioning.rs:878-903`), `rustc` sets `InstantiationMode::GloballyShared { may_conflict: true }`. To prevent collisions when two downstream crates instantiate the same upstream generic `Vec::<u32>::push`, `symbol_name_provider` (`lib.rs:146-160`) queries `instance.upstream_monomorphization(tcx).unwrap_or(LOCAL_CRATE)` and hashes the **instantiating crate ID** into the symbol name, unless both crates reuse an already-exported upstream monomorphization.
  - Within a crate across multiple CGUs (or when `may_conflict: true` symbols are emitted with `LinkOnceODR` / `WeakODR` linkage), the system linker and ThinLTO (`getFirstDefinitionForLinker` at `PassWrapper.cpp:1248-1266`) assume that **identical mangled symbol names denote semantically equivalent functions**.
- **How this enters the theorem (`WeakOdrCoherent` in `CompositionalLinkingAndThinLtoWpoProbe.lean:212-235`):**
  A compositional crate/CGU theorem must include a **Symbol Coherence Premise**: for every symbol `sym` emitted with `WeakODR` / `LinkOnceODR` linkage (or imported via `upstream_monomorphization`), every compilation unit that defines `sym` must prove `SatisfiesContract body (contractOf sym)`. As proved in `canary_incoherent_weak_odr_unsound`, if two compilation units emit conflicting bodies under the same symbol `sym` (for instance, via unsound `#[no_mangle]` collisions or divergent target-feature/cfg specialization not reflected in the symbol hash), ThinLTO inlining and linker symbol resolution become mutually inconsistent.

---

### 3. Conditional Statements for Mixed Binaries: Precedents and Four Pitfalls

Basis: source + execution (`support/CompositionalLinkingAndThinLtoWpoProbe.lean:248-315`; `CertiRocq/VeriFFI@7e8cd8e7b631be066407f86c82ff60b6fc63ae0b`; `PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`).

When a binary links verified Rust modules $M_{\text{ver}}$ with unverified Rust or C modules $M_{\text{unver}}$, the top-level theorem takes a **conditional form**:
$$\mathsf{AssumedContracts}(M_{\text{unver}}, \Gamma_{\text{imp}}) \;\wedge\; \mathsf{OpenModuleRefines}(M_{\text{ver}}, \Gamma_{\text{imp}}, \Gamma_{\text{exp}}) \implies \mathsf{Satisfies}(M_{\text{ver}} \bowtie M_{\text{unver}}, \Gamma_{\text{exp}})$$
Four classic pitfalls can render this conditional statement vacuous or unsound:

1. **Pitfall 1 — Circular Rely-Guarantee Assumptions (`canary_circular_assumption_vacuity`, lines 253–256):**
   - If $M_{\text{ver}}$ exports `f` and imports `g`, while $M_{\text{unver}}$ defines `g` (which calls `f`), a naive unindexed implication $(\text{Spec}(g) \implies \text{Spec}(f)) \wedge (\text{Spec}(f) \implies \text{Spec}(g))$ is trivially satisfied when both $\text{Spec}(f)$ and $\text{Spec}(g)$ are `False`!
   - **Resolution (`conditional_mixed_binary_sound`, lines 261–284):** Index contracts by well-founded call-stack depth `d : Nat` (or execution step index $n$, as in Iris/CCR and CompCertO): proving $\forall d,\; (\forall k < d,\; Q(k)) \implies P(d)$ for the verified module and $\forall d,\; P(d) \implies Q(d)$ for the unverified step discharges $\forall d,\; P(d) \wedge Q(d)$ unconditionally by strong induction on $d$.
2. **Pitfall 2 — Reentrant Callbacks Observing Half-Updated Private Invariants (`canary_reentrant_callback_invariant_breach`, lines 292–310):**
   - Suppose a verified module maintains a private representation invariant `LibraryInv mem` (`mem % 2 = 0`). If a verified method `verifiedMethodWithCallback` mutates `mem` to an intermediate state `mem + 1` (violating `LibraryInv`), invokes an unverified callback `cb` before restoring `mem + 2`, and `cb` re-enters a safe public method `reentrantSafeReader` of the verified module, `reentrantSafeReader`'s entry assumption `LibraryInv` is falsified!
   - **Resolution:** Any call to an imported/unverified function or closure (`TerminatorKind::Call` to an external symbol or function pointer) must treat the library's own `AdtInv` / module invariant as a **precondition at the call site**, forcing the caller to restore `LibraryInv` before transferring control across the boundary.
3. **Pitfall 3 — Frame and Provenance Aliasing Across the Boundary:**
   - An unverified C function may return the right value in `rax`/`x0` while overwriting the caller's spilled locals on the stack or stashing a borrowed pointer `&mut T` in a C global and writing to it after the Rust borrow ends.
   - **Resolution:** Every imported `FnContract` must include a spatial frame clause (`PartitionedFrameLayout` separating public C-accessible stack objects from private compiler spills, plus Tree Borrows protector/footprint release on return).
4. **Pitfall 4 — Unwinding Across Non-Unwinding Boundaries (`extern "C"` vs. `extern "C-unwind"`):**
   - If an unverified callee unwinds across an `extern "C"` boundary (or a verified Rust `extern "C"` function unwinds into an unverified C caller), Itanium two-phase unwinding corrupts caller frames that lack `.eh_frame` / LSDA records.
   - **Resolution:** All `extern "C"` boundaries must enforce `UnwindAction::Terminate(Reason::Abi)` via a negative `ttype_index = -1` filter in `.gcc_except_table` so Phase 1 search halts and aborts deterministically at the boundary.

## Boundaries

1. **Dynamic Linker Interposition (`LD_PRELOAD` / ELF `SymbolVisibility::Interposable`, `known not to apply` without `-Bsymbolic` or hidden visibility):**
   - In `compiler/rustc_monomorphize/src/partitioning.rs:970-975`, when `tcx.sess.default_visibility() == SymbolVisibility::Interposable`, exported symbols have `Visibility::Default` and on ELF shared libraries (`cdylib`/`dylib`) can be interposed at load time by the dynamic linker (`ClearDSOLocalOnDeclarations` in `PassWrapper.cpp:1395-1402`). Compositional theorems that inline or rely on the crate-local body of an exported symbol assume non-interposable binding (`dso_local` / static linking / `-Bsymbolic`).
2. **Inline/Global Assembly Symbol References (`known not to apply` if `asm!` references private mangled symbols without `sym` operands):**
   - `MonoItem::GlobalAsm` and `TerminatorKind::InlineAsm` can reference linker symbols directly inside assembly strings. Unless referenced via explicit `sym <path>` operands (which `rustc_monomorphize` tracks in `usage_map`), `internalize_symbols` and `Unusedglob` cannot see the reference.

## Evidence

1. **Primary Upstream Compiler Sources Inspected:**
   - `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):
     - `compiler/rustc_symbol_mangling/src/lib.rs:1-350` (Rust linkage model, `symbol_name_provider`, `InstantiationMode::GloballyShared`, `RUSTC_STD_INTERNAL_SYMBOL`).
     - `compiler/rustc_monomorphize/src/partitioning.rs:179-277, 529-615, 757-975` (`internalize_symbols`, `mono_item_visibility`, naked-function and weak-lang-item internalization guards).
     - `compiler/rustc_codegen_llvm/src/back/lto.rs:345-495, 725-780` (`thin_lto`, `LLVMRustPrepareThinLTORename`, `LLVMRustPrepareThinLTOResolveWeak`, `LLVMRustPrepareThinLTOInternalize`, `LLVMRustPrepareThinLTOImport`).
     - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:1213-1584` (`LLVMRustThinLTOData`, `getFirstDefinitionForLinker`, `LLVMRustCreateThinLTOData`, `computeDeadSymbolsWithConstProp` with `ImportEnabled = false`, `FunctionImporter`).
   - `llvm/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`23.1.1`): `llvm/lib/Transforms/IPO/{FunctionImport,Internalize,DeadArgumentElimination,SCCP,GlobalDCE,WholeProgramDevirt}.cpp`.
   - `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (`3.18`): `common/Linking.v`, `driver/Compiler.v:212-481`, `backend/Unusedglob.v`.
2. **Preserved Support Artifacts in This Package:**
   - [`support/CompositionalLinkingAndThinLtoWpoProbe.lean`](support/CompositionalLinkingAndThinLtoWpoProbe.lean) (320 lines, `sha256: 92e26b9b3b20c3d74036db3318e954eef7eec5b9575e699a0b8a02eda3a963b0`): Standalone Lean `v4.34.1` mechanization proving 8 theorems (`horizontal_link_sound`, `wpo_internalize_ipsccp_sound`, `canary_open_world_ipsccp_unsound`, `thinLto_summary_import_sound`, `canary_incoherent_weak_odr_unsound`, `canary_circular_assumption_vacuity`, `conditional_mixed_binary_sound`, and `canary_reentrant_callback_invariant_breach`) with zero `sorryAx` and zero `Lean.ofReduceBool`.
   - [`support/compositional_and_wpo_matrix.json`](support/compositional_and_wpo_matrix.json) (98 lines, `sha256: 3ae04132f728a2ad43410e549cc91d791e38057f821c6e62c5a30f804fe380b1`): Structured comparison matrix of the 8 compositional frameworks and 6 WPO/ThinLTO mechanisms.

## Revalidation

Run the following command to revalidate all 8 mechanized Lean 4.34.1 theorems and verify the JSON matrix:

```bash
anneal-lean-run --mode file --concurrency 4 -- \
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/compositional-correctness-linking-and-whole-program-optimization/support/CompositionalLinkingAndThinLtoWpoProbe.lean

python3 -c 'import json; d = json.load(open("reports/compositional-correctness-linking-and-whole-program-optimization/support/compositional_and_wpo_matrix.json")); assert len(d["compositional_frameworks"]) == 8 and len(d["whole_program_optimizations"]) == 6; print("OK")'
```

Expected output: all eight `#print axioms` checks report only standard axioms (`[propext]`, `[propext, Quot.sound]`, or `does not depend on any axioms`), and the JSON check prints `OK` with exit code `0`.
