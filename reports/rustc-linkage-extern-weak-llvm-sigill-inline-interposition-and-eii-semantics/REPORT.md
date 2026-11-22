# `rustc` `#![feature(linkage)]` and `#![feature(extern_item_impls)]` (`#[eii]`): Same-CGU `define extern_weak` LLVM `SIGILL` Crash, Cross-Crate `Miri` Divergence, Contradictory `#[inline(always)]` Interposition Break, and `#[eii]` Foreign-Lookup Gap

## Summary

Across three pinned `rust-lang/rust` snapshots spanning six months (`1.98.0-nightly` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` with LLVM `22.1.6`, `1.102.0-nightly` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` with LLVM `23.1.5`, and `main` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), four distinct defects govern the interaction between `rustc`'s `#![feature(linkage)]`, LLVM's inliner and machine-code emitter, `Miri`'s foreign-symbol interpreter, and `#![feature(extern_item_impls)]` (`#[eii]`):

1. **Same-CGU `define extern_weak` triggers a hard `SIGILL` (`rc = -4`) crash inside `libLLVM` (`AsmPrinter`) while silently passing `--emit=llvm-ir` and `-Z verify-llvm-ir`.** When a single codegen unit (CGU) defines an exported function `#[unsafe(no_mangle)] pub extern "C" fn present_fn()` (or static `PRESENT_DATA`) and also references an `extern "C" { #[linkage = "extern_weak"] static present_fn: ...; }` import of the same symbol name, `check_and_apply_linkage` in `compiler/rustc_codegen_llvm/src/consts.rs` retrieves the already-predefined LLVM global via `declare_fn` / `declare_global` and unconditionally executes `llvm::set_linkage(actual_global, ExternalWeakLinkage)`. This mutates a defined symbol into illegal LLVM IR (`define extern_weak dso_local i32 @present_fn()` or `@PRESENT_DATA = extern_weak constant ...`) that `llvm-as` rejects on round-trip parsing, yet `llvm::Verifier` fails to check `!hasExternalWeakLinkage()` on definitions (`Verifier.cpp:569, 3034`), letting the invalid module reach `llvm::AsmPrinter::emitLinkage` (`AsmPrinter.cpp:755-758`), where `llvm_unreachable("Should never emit this")` traps with `SIGILL` (`rc = -4`).
2. **Cross-crate `#[linkage = "extern_weak"]` silently diverges between native ELF linking and `Miri`.** In `src/tools/miri/src/machine.rs` (`extern_static_pointer`), after checking Miri's hardcoded OS shim table `extern_statics_imports`, the `else if import_linkage == Some(Linkage::ExternalWeak)` branch short-circuits to a single shared null allocation (`extern_static_weak_import_default` in `3ef0c22cd`/`342d74463`; `missing_weak_symbol` in `14210df0e`) *before* searching exported Rust crate symbols via `lookup_exported_symbol`. Consequently, when a dependency crate exports `present_fn` returning `77`, native execution resolves `PRESENT=Some(77) MISSING=None SAME_SLOT=false`, whereas `Miri` resolves `PRESENT=None MISSING=None SAME_SLOT=true` (while still resolving built-in Linux weak shims such as `strlen` to `Some(5)`).
3. **`rustc` emits a contradictory `` `#[inline]` is ignored on externally exported functions `` warning on `#[inline(always)] #[linkage = "weak"]` while still emitting LLVM `alwaysinline`, breaking strong-over-weak interposition even at `-Z mir-opt-level=0 -C opt-level=0`.** `InlineParser::deferred_finalize_check` warns that `#[inline]` is ignored whenever an item carries an extern indicator (`#[no_mangle]`, `#[export_name]`, or `#[linkage]`), and MIR inlining honors that contract via `cross_crate_inlinable` returning `false`. However, `InlineParser::finalize` retains `AttributeKind::Inline(InlineAttr::Always, _)`, `rustc_codegen_llvm/src/attributes.rs` (`inline_attr`) lowers it unconditionally to LLVM `alwaysinline` without checking `codegen_fn_attrs.linkage`, and LLVM's `getAttributeBasedInliningDecision` (`InlineCost.cpp:3209-3239`) evaluates `Call.hasFnAttr(Attribute::AlwaysInline)` *before* checking `Callee->isInterposable()`. Same-CGU callers therefore inline the weak body (`10`) and ignore downstream strong overrides (`99`) across `-Z mir-opt-level=0 -C opt-level=0`, `-C opt-level=0`, and `-C opt-level=2` (`CALLERS=(99, 99, 10) DIRECT=(99, 99, 99)`), while `-Z inline-llvm=no` restores `CALLERS=(99, 99, 99)`.
4. **Native `#![feature(extern_item_impls)]` (`#[eii]`) resolves defaults and overrides via weak/strong alias shims with same-crate suppression, whereas `Miri` fails (`rc = 1`) on every `#[eii]` call.** Native builds execute default (`DEFAULT=15`), cross-crate explicit override (`OVERRIDE=905`), and same-crate explicit override (`SAME_CRATE_OVERRIDE=705`, with `codegen_attrs.rs:246-258` suppressing the weak default alias) and reject duplicate explicit implementations at compile time (`DuplicateEiiImpls`). `Miri` aborts with `unsupported operation: can't call foreign function _RNv...` on both default and overridden calls because `lookup_exported_symbol` (`src/tools/miri/src/shims/foreign_items.rs:139-151`) skips exported items lacking `attrs.symbol_name` or `RUSTC_STD_INTERNAL_SYMBOL` and never inspects `attrs.foreign_item_symbol_aliases`.

All four structural invariants and their sharp failure modes are mechanized in `support/LinkageInterpositionAndEiiSoundness.lean` (1,021 lines, verified under Lean `v4.34.1` with `-DwarningAsError=true -DElab.async=false -Ddebug.skipKernelTC=false`, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, zero `partial`, and zero `._unsafe_rec` across 382 kernel constants), and all four compiler/interpreter behaviors are packaged in the standalone reproduction harness `support/probe_linkage_extern_weak_and_eii.py`.

## Applicability

This report characterizes the joint behavior of the seven durable upstream subjects listed in `REPORT.json`, observed on `2026-11-22`:

| Role in Investigation | Subject | Exact Pinned Revision | How Examined |
| :--- | :--- | :--- | :--- |
| Live execution + primary source | `rust-lang/rust` (`rustc 1.98.0-nightly`, `LLVM 22.1.6`, `miri 0.1.0`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Direct `x86_64-unknown-linux-gnu` execution (`support/probe_linkage_extern_weak_and_eii.py`, recorded in `support/probe_results_live.json`) + full source inspection |
| Execution record + primary source | `rust-lang/rust` (`rustc 1.102.0-nightly`, `LLVM 23.1.5`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Recorded `x86_64-unknown-linux-gnu` execution of cases `c1`–`c4` + full source inspection |
| Forward source verification | `rust-lang/rust` (`main` snapshot, `2026-11-22`) | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | Direct source diff against `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` across all 8 audited compiler and Miri files |
| LLVM backend source (23.1.5) | `rust-lang/llvm-project` (submodule of `3ef0c22cd`) | `0a5579eb649d3634a9c30ac873300cc2944fa070` | Direct source inspection of `GlobalValue.h`, `Verifier.cpp`, `LLParser.cpp`, `AsmPrinter.cpp`, `AlwaysInliner.cpp`, `InlineCost.cpp` |
| LLVM backend source (22.1.6) | `rust-lang/llvm-project` (submodule of `14210df0e`) | `08c84e69a84d95936296dfcab0e38b34100725d5` | Direct source inspection of `AsmPrinter.cpp` + live `llvm-as` / `llvm-nm` / `libLLVM.so.22.1` execution |
| Verification-boundary consumer | `joshlf/anneal` (`main` snapshot) | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Direct source inspection of `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs` |
| Mechanization kernel | `leanprover/lean4` (`v4.34.1`) | `5045d0056413266e57c625dcd7c365b10e377c52` | Direct single-file kernel verification of `support/LinkageInterpositionAndEiiSoundness.lean` |

### Scope Conditions and Target Constraints

- **Target and ABI:** All empirical runs execute on `x86_64-unknown-linux-gnu` (ELF object format, GNU/LLD linker semantics, Rust 2024 edition). Findings that depend on ELF strong-over-weak symbol resolution (`c2`, `c3`, `c4`) apply directly to ELF targets; Mach-O (`-undefined dynamic_lookup` / `.weak_definition`) and COFF/PE (`/ALTERNATENAME` / weak externals) have distinct linker and `dso_local` code paths and are not empirically executed here (see **Boundaries**).
- **Feature gates and flags:** Findings require nightly `#![feature(linkage)]` (`c1`–`c3`) or `#![feature(extern_item_impls)]` (`c4`). Same-CGU collision (`c1`) requires the defining item and the `extern_weak` import consumer to be partitioned into the same LLVM module, guaranteed deterministically by `-C codegen-units=1` (and reachable by chance under default multi-CGU partitioning or ThinLTO/FatLTO module merging).
- **Version-shared vs. version-specific behaviors:** All four defects (`c1`–`c4`) hold identically across `14210df0e` (`1.98.0-nightly`), `3ef0c22cd` (`1.102.0-nightly`), and `342d74463` (`main`). Four internal implementation details changed between `14210df0e` and `3ef0c22cd` (and remained unchanged in `342d74463`):
  1. `#[eii]` default alias linkage changed from `Linkage::LinkOnceAny` (`14210df0e`, `codegen_attrs.rs:262`) to `Linkage::WeakAny` (`3ef0c22cd` and `342d74463`, `codegen_attrs.rs:262`).
  2. The `extern_weak` indirection global `@_rust_extern_with_linkage_<crate_id>_<sym>` gained `unnamed_addr` (`llvm::set_unnamed_address(pointer_global, llvm::UnnamedAddr::Global)`) and pointer-authentication signing support between `14210df0e` (`consts.rs:201-212`) and `3ef0c22cd` (`consts.rs:214-268`), plus `!guid` metadata in LLVM 23.
  3. Miri's shared weak-import null slot field was renamed from `missing_weak_symbol` (`14210df0e`, `machine.rs:579, 1437`) to `extern_static_weak_import_default` (`3ef0c22cd` and `342d74463`, `machine.rs:604, 1517`), while retaining the older ``.expect("`missing_weak_symbol` should have been initialized")`` message.
  4. `CodegenFnAttrFlags::NO_MANGLE` was retired and folded into `attrs.symbol_name = Some(name)` (`codegen_attrs.rs:97-111`), updating `foreign_items.rs`'s check from three disjuncts (`14210df0e:154-156`) to two (`3ef0c22cd:142-143`, `342d74463:142-143`).
- **Anneal boundary scope:** At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` models `TyKind::Foreign` and `TyKind::FnPtr` as `.unsupported` (`MirAst.lean:308-311`) and restricts `TerminatorKind.call` to direct `FnDef` calls (`MirAst.lean:780-784`), while `trusted/rustc-capture/src/driver.rs` only verifies clean analysis callbacks without yet serializing MIR or linkage attributes. The invariants in Finding 7 therefore serve as fail-closed design requirements for extending Anneal and verified-`rustc` codegen beyond closed-world direct `FnDef` calls.

## Findings

### 1. Attribute Pipeline, Linkage Metadata, and CGU Lowering Topology

Basis: source (`rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`)

Understanding all four failures requires tracing how `rustc` separates *symbol definition linkage*, *foreign import linkage*, *inline hints*, and *externally implementable item aliases* across four stages:

1. **Attribute parsing (`compiler/rustc_attr_parsing/`):**
   - `InlineParser` (`compiler/rustc_attr_parsing/src/attributes/inline.rs:129-158`) parses `#[inline]`, `#[inline(always)]`, `#[inline(never)]`, and `#[rustc_force_inline]`. Its `finalize` method always returns `Some(AttributeKind::Inline(a, s))`. Its `deferred_finalize_check` emits the lint `UNUSED_ATTRIBUTES` with diagnostic `InlineIgnoredForExported` whenever the item is a function/method/closure, does not have `InlineAttr::Never`, and has any parsed attribute satisfying `kind.is_extern_indicator()`.
   - `check_linkage` (`compiler/rustc_passes/src/check_attr.rs:1259-1282`) rejects only two malformed `#[linkage]` uses: `extern { #[linkage] static mut ... }` (`StaticMutLinkage`) and `#[linkage]` on `const fn` (`ConstFnLinkage`). It performs *no* conflict check between `#[linkage]` and `#[inline(always)]`, and *no* check against same-crate symbol-name collisions between a defined `#[no_mangle]` item and an `extern { #[linkage = "extern_weak"] static ... }` import.
2. **Codegen attribute synthesis (`compiler/rustc_codegen_ssa/src/codegen_attrs.rs`):**
   - `process_builtin_attrs` records `AttributeKind::Inline(inline, span)` into `codegen_fn_attrs.inline` (`lines 74-82`), `AttributeKind::NoMangle` / `ExportName` / `LinkName` into `codegen_fn_attrs.symbol_name` (`lines 73, 85-116`), and splits `AttributeKind::Linkage(linkage, span)` (`lines 196-211`) into two distinct fields:
     - `codegen_fn_attrs.import_linkage` when `tcx.is_foreign_item(did)` is true;
     - `codegen_fn_attrs.linkage` when `did` is a Rust definition.
   - `AttributeKind::RustcEiiForeignItem` sets `CodegenFnAttrFlags::EXTERNALLY_IMPLEMENTABLE_ITEM` (`lines 221-223`), and `apply_overrides` (`lines 445-476`) explicitly preserves *mangled* symbol names for foreign items carrying `EXTERNALLY_IMPLEMENTABLE_ITEM` (unlike ordinary foreign items, which receive an implicit `symbol_name = Some(tcx.item_name(did))` at `line 474`).
   - `AttributeKind::EiiImpl(i)` (`lines 224-278`) populates `codegen_fn_attrs.foreign_item_symbol_aliases.push((foreign_item, if i.is_default { Linkage::WeakAny } else { Linkage::External }, Visibility::Default))`—unless `i.is_default` is true and the local crate also contains a non-default impl for `foreign_item`, in which case it skips emitting the default alias (`lines 246-258`).
   - `CodegenFnAttrs::contains_extern_indicator` (`compiler/rustc_middle/src/middle/codegen_fn_attrs.rs:269-286`) returns `false` for `FOREIGN_ITEM`, and returns `true` for non-foreign items carrying any of `RUSTC_STD_INTERNAL_SYMBOL`, `EXTERNALLY_IMPLEMENTABLE_ITEM`, `OFFLOAD_KERNEL`, `symbol_name.is_some()`, or `linkage` other than `None | Some(Linkage::Internal)`.
3. **CGU two-phase emission (`compiler/rustc_codegen_llvm/src/base.rs:116-129`):**
   - Within `compile_codegen_unit`, LLVM codegen runs in two sequential loops over `cx.codegen_unit.items_in_deterministic_order(cx.tcx)`:
     - **Phase 1 (`predefine`):** Calls `mono_item.predefine(...)` for every monomorphized function and static in the CGU (`mono_item.rs:26-74`), creating the LLVM `Function` or `GlobalVariable`, setting its initial linkage via `llvm::set_linkage(..., base::linkage_to_llvm(linkage))` (`mono_item.rs:47, 88`), emitting `add_static_aliases` / `add_function_aliases` for `foreign_item_symbol_aliases`, and caching the `Instance -> Value` pointer in `self.instances`.
     - **Phase 2 (`define`):** Calls `mono_item.define(...)` (`rustc_codegen_ssa/src/mono_item.rs:30-52`) to populate basic blocks (`codegen_instance`) and static initializers (`codegen_static`). Crucially, **Phase 2 never restores or re-asserts LLVM linkage after Phase 1**, while body lowering in Phase 2 may call `get_static(foreign_def_id)` on foreign statics that were *not* part of `mono_items`.
4. **LLVM lowering and optimization (`rustc_codegen_llvm` + `rust-lang/llvm-project`):**
   - `rustc_codegen_llvm/src/base.rs:230-241` maps `rustc_attr_ir::Linkage` 1-to-1 onto LLVM `GlobalValue::LinkageTypes` (`External`, `AvailableExternally`, `LinkOnceAny`, `LinkOnceODR`, `WeakAny`, `WeakODR`, `Internal`, `ExternalWeak`).
   - `rustc_codegen_llvm/src/attributes.rs:51-91` (`inline_attr`) emits `alwaysinline` / `inlinehint` / `noinline` based exclusively on `codegen_fn_attrs.inline`, `optimize`, `target_features`, and `-Z inline-llvm`, without consulting `codegen_fn_attrs.linkage`.

---

### 2. Same-CGU `define extern_weak` LLVM `SIGILL` Compiler Crash (and Verifier Blind Spot)

Basis: source (`rustc_codegen_llvm/src/consts.rs`, `declare.rs`, `mono_item.rs`, `base.rs`; `llvm-project` `AsmPrinter.cpp`, `Verifier.cpp`, `LLParser.cpp`) + execution (`1.98.0-nightly` / `LLVM 22.1.6` live in `support/probe_results_live.json`; `1.102.0-nightly` / `LLVM 23.1.5` recorded) + derived

#### Root Cause in `rustc_codegen_llvm`

When a crate defines a `#[unsafe(no_mangle)]` function or static in the same CGU as a function body that reads an `extern "C" { #[linkage = "extern_weak"] static <same_name>: ...; }` declaration, the two-phase CGU loop executes the following sequence:

1. **Phase 1 (`predefine`):** `predefine_fn` (`compiler/rustc_codegen_llvm/src/mono_item.rs:58-74, 86-101`) calls `self.declare_fn("present_fn", fn_abi, Some(instance))`, which invokes `LLVMGetOrInsertFunction(cx.llmod, "present_fn", ...)` (`declare.rs:45`) and sets its linkage to `ExternalLinkage` (`mono_item.rs:88`) plus `dso_local` (`mono_item.rs:99`). For a data static `PRESENT_DATA`, `predefine_static` (`mono_item.rs:26-56`) similarly creates `@PRESENT_DATA` via `define_global` and sets `ExternalLinkage`.
2. **Phase 2 (`define` of `main`):** Lowering `main`'s read of `imp::present_fn` invokes `CodegenCx::get_static` -> `get_static_inner` (`consts.rs:367-407`). Because `imp::present_fn` is a foreign item (`self.tcx.is_foreign_item(def_id) == true`), it is not in `self.instances` and falls through to `check_and_apply_linkage` (`consts.rs:189-270` in `3ef0c22cd`/`342d74463`; `consts.rs:157-213` in `14210df0e`):
   ```rust
   // compiler/rustc_codegen_llvm/src/consts.rs:202-227 (3ef0c22cd / 342d74463)
   let actual_global = if matches!(attrs.import_linkage, Some(Linkage::ExternalWeak)) {
       let instance = Instance::mono(cx.tcx, def_id);
       if let ty::Adt(struct_def, args) = instance.ty(cx.tcx, cx.typing_env()).kind()
           && cx.tcx.is_lang_item(struct_def.did(), LangItem::Option)
           && let ty::FnPtr(sig, header) = args.type_at(0).kind()
       {
           ...
           cx.declare_fn(sym, &fn_abi, None)
       } else {
           cx.declare_global(sym, cx.type_i8())
       }
   } else {
       cx.declare_global(sym, cx.type_i8())
   };
   llvm::set_linkage(actual_global, base::linkage_to_llvm(linkage));
   ```
   Because `declare_fn` calls `LLVMGetOrInsertFunction` and `declare_global` calls `LLVMRustGetOrInsertGlobal` (`declare.rs:45, 97`), **both functions return the existing `llvm::Value` for the same-CGU definition `@present_fn` (or `@PRESENT_DATA`) rather than creating a fresh declaration.** Line 226 (`line 188` in `14210df0e`) then **unconditionally overwrites the existing definition's linkage with `ExternalWeakLinkage`** without checking `llvm::is_declaration(actual_global)` or whether `sym` is already defined in the current CGU!
3. **Indirection global creation (`consts.rs:256-269`):** `rustc` then creates an internal pointer slot `@_rust_extern_with_linkage_<stable_crate_id>_present_fn` initialized with `@present_fn`.
4. **Phase 2 (`define` of `present_fn` / `PRESENT_DATA`):** `codegen_instance` populates basic blocks inside `@present_fn` (and `codegen_static` attaches the constant initializer `c"*\00\00\00"` to `@PRESENT_DATA`), leaving the illegal linkage intact:
   - On `rustc 1.102.0-nightly` (`3ef0c22cd`, LLVM `23.1.5`):
     ```llvm
     @_rust_extern_with_linkage_12cf76b069526b25_present_fn = internal unnamed_addr global ptr @present_fn, !guid !1
       %_22 = icmp eq i64 ptrtoint (ptr @_rust_extern_with_linkage_12cf76b069526b25_present_fn to i64), 0
       %_7 = load ptr, ptr @_rust_extern_with_linkage_12cf76b069526b25_present_fn, align 8
     define extern_weak dso_local i32 @present_fn() unnamed_addr #3 !guid !29 {
     ```
   - On `rustc 1.98.0-nightly` (`14210df0e`, LLVM `22.1.6`, `support/probe_results_live.json`):
     ```llvm
     @_rust_extern_with_linkage_bfb4c4b058e63ff9_present_fn = internal global ptr @present_fn
       %_21 = icmp eq i64 ptrtoint (ptr @_rust_extern_with_linkage_bfb4c4b058e63ff9_present_fn to i64), 0
       %f = load ptr, ptr @_rust_extern_with_linkage_bfb4c4b058e63ff9_present_fn, align 8
     define extern_weak dso_local i32 @present_fn() unnamed_addr #3 {
     ```
   - And for same-CGU data statics (`14210df0e`, LLVM `22.1.6`, `support/probe_results_live.json`):
     ```llvm
     @PRESENT_DATA = extern_weak constant [4 x i8] c"*\00\00\00", align 4
     @_rust_extern_with_linkage_ff2dbc1ac127dc26_PRESENT_DATA = internal global ptr @PRESENT_DATA
     ```

#### Why `--emit=llvm-ir` and `-Z verify-llvm-ir` Both Fail to Catch It, While `llvm-as` Rejects It and `AsmPrinter` Traps with `SIGILL`

Inspecting `rust-lang/llvm-project` at `0a5579eb649d3634a9c30ac873300cc2944fa070` (LLVM `23.1.5`) and `08c84e69a84d95936296dfcab0e38b34100725d5` (LLVM `22.1.6`) exposes a three-way inconsistency inside LLVM itself:

1. **Textual IR parser (`LLParser.cpp:7084-7090`) explicitly forbids `define extern_weak`:**
   ```cpp
   switch ((GlobalValue::LinkageTypes)Linkage) {
   case GlobalValue::ExternalLinkage:
     break; // always ok.
   case GlobalValue::ExternalWeakLinkage:
     if (IsDefine)
       return error(LinkageLoc, "invalid linkage for function definition");
     break;
   ```
   Running sysroot `llvm-as` on the `.ll` emitted by `rustc --emit=llvm-ir` fails immediately (`rc = 1`):
   - Function case: `error: invalid linkage for function definition` at `define extern_weak dso_local i32 @present_fn()`.
   - Data static case: `error: expected top-level entity` at the initializer `c"*\00\00\00"` on `@PRESENT_DATA = extern_weak constant [4 x i8] c"*\00\00\00"`.
2. **In-memory IR verifier (`Verifier.cpp:568-570, 3034`) has a blind spot for `!isDeclaration()` + `ExternalWeakLinkage`:**
   ```cpp
   // llvm/lib/IR/Verifier.cpp:568-570
   void Verifier::visitGlobalValue(const GlobalValue &GV) {
     Check(!GV.isDeclaration() || GV.hasValidDeclarationLinkage(),
           "Global is external, but doesn't have external or weak linkage!", &GV);
   ...
   // llvm/lib/IR/Verifier.cpp:3034
   Check(!F.hasCommonLinkage(), "Functions may not have common linkage", &F);
   ```
   `visitGlobalValue` only validates linkage when `GV.isDeclaration()` is true; `visitFunction` checks `!F.hasCommonLinkage()`, and neither checks `!GV.hasExternalWeakLinkage()` when `!GV.isDeclaration()`. Empirically, compiling with `-Z verify-llvm-ir` (`support/probe_results_live.json`: `c1.fn_same_cgu.verify_llvm_ir_rc = -4`) does **not** report a verifier error—the corrupted module passes verification and proceeds to codegen.
3. **Machine code emission (`AsmPrinter.cpp:723-761, 1016-1041, 2052-2053` in LLVM 23.1.5; `686-722, 753, 979, 1963` in LLVM 22.1.6) hits `llvm_unreachable` -> `SIGILL`:**
   ```cpp
   void AsmPrinter::emitLinkage(const GlobalValue *GV, MCSymbol *GVSym) const {
     GlobalValue::LinkageTypes Linkage = GV->getLinkage();
     switch (Linkage) {
     ...
     case GlobalValue::ExternalWeakLinkage:
     case GlobalValue::AvailableExternallyLinkage:
     case GlobalValue::AppendingLinkage:
       llvm_unreachable("Should never emit this");
     }
     llvm_unreachable("Unknown linkage type!");
   }
   ```
   For functions, `AsmPrinter::emitFunctionBody()` calls `emitFunctionHeader()` (`AsmPrinter.cpp:2053`), which calls `emitLinkage(&F, CurrentFnSym)` (`AsmPrinter.cpp:1041`). For data statics, `AsmPrinter::emitGlobalVariable()` calls `emitLinkage(GV, GVSym)`. In release `libLLVM.so` shipped with nightly `rustc`, `llvm_unreachable` lowers to an illegal-instruction trap (`ud2` on `x86_64`), terminating `rustc` with **`SIGILL` (`rc = -4`)**:
   - LLVM `23.1.5` (`rustc 1.102.0-nightly`): `libLLVM.so.23.1-rust-1.102.0-nightly(_ZN4llvm10AsmPrinter16emitFunctionBodyEv+0x33)` -> `rc = -4`.
   - LLVM `22.1.6` (`rustc 1.98.0-nightly`, live): `libLLVM.so.22.1-rust-1.98.0-nightly(_ZN4llvm10AsmPrinter16emitFunctionBodyEv+0x33)` -> `rc = -4` (function case) and `libLLVM.so.22.1-rust-1.98.0-nightly(_ZN4llvm10AsmPrinter18emitGlobalVariableEPKNS_14GlobalVariableE+0x297)` -> `rc = -4` (static data case).
   - **Separate-crate control (`c1.separate_crate_control`):** Moving `pub extern "C" fn present_fn() -> i32 { 77 }` into an `rlib` dependency `prov` keeps `@present_fn` as a declaration in `app`'s CGU, compiles with `rc = 0`, and prints `PRESENT=Some(77)`.

---

### 3. Cross-Crate `extern_weak` Divergence Between Native ELF Linking and `Miri`

Basis: source (`src/tools/miri/src/machine.rs`, `src/tools/miri/src/shims/extern_static.rs`, `compiler/rustc_codegen_llvm/src/consts.rs`) + execution (`1.98.0-nightly` / `miri 0.1.0` live in `support/probe_results_live.json`; `1.102.0-nightly` recorded)

#### Root Cause in `Miri`

In `src/tools/miri/src/machine.rs:1463-1525` (`3ef0c22cd` and `342d74463`; identical logic at `lines 1390-1445` in `14210df0e`), `MiriMachine::extern_static_pointer` resolves foreign statics via a three-branch `if / else if / else`:

```rust
// src/tools/miri/src/machine.rs:1474-1524 (3ef0c22cd / 342d74463)
let ptr = match ecx.tcx.codegen_fn_attrs(def_id).import_linkage {
    None => ecx.machine.extern_statics.get(&link_name),
    Some(_) => ecx.machine.extern_statics_imports.get(&link_name),
};
if let Some(&ptr) = ptr {
    ...
    interp_ok(ptr)
} else if ecx.tcx.codegen_fn_attrs(def_id).import_linkage == Some(Linkage::ExternalWeak) {
    assert_eq!(
        extern_decl_layout.size,
        ecx.tcx.data_layout.pointer_size(),
        "non-pointer-sized weak static"
    );
    interp_ok(
        ecx.machine
            .extern_static_weak_import_default
            .expect("`missing_weak_symbol` should have been initialized"),
    )
} else {
    // Look for a Rust static with this symbol name in the crate graph.
    let Some(instance) = ecx.lookup_exported_static(link_name)? else {
        throw_unsup_format!("extern static `{link_name}` is not supported by Miri");
    };
    ...
}
```

Two distinct architectural consequences follow directly from this control flow:

1. **Silent value divergence on exported Rust crate symbols:** `ecx.machine.extern_statics_imports` is populated *solely* during `init_extern_statics` (`src/tools/miri/src/shims/extern_static.rs:52-99`) with a fixed target-specific list of OS/libc dynamic symbols (on `x86_64-unknown-linux-gnu`: `environ`, `copy_file_range`, `getrandom`, `gettid`, `statx`, `strlen`, optional `__futimens64`, `__cxa_thread_atexit_impl`, and `__dso_handle`). When a dependency Rust crate `prov` exports `#[unsafe(no_mangle)] pub extern "C" fn present_fn() -> i32 { 77 }`, `present_fn` is absent from `extern_statics_imports`. Miri immediately enters the `else if import_linkage == Some(Linkage::ExternalWeak)` branch and returns the zero-initialized null slot **without ever searching the crate graph via `lookup_exported_symbol`**. Even if the `else` branch were reached, `machine.rs:1522` calls `lookup_exported_static`, which rejects exported functions (`foreign_items.rs:246-249`) and returns the static's own allocation rather than synthesizing the extra pointer-indirection slot that `#[linkage = "extern_weak"]` uses.
2. **Slot-address identity divergence (`SAME_SLOT=true` vs. `SAME_SLOT=false`):** `init_extern_statics` (`extern_static.rs:101-105`) allocates a single `usize`-sized zeroed allocation `extern_static_weak_import_default` (named `missing_weak_symbol` in `14210df0e`) and reuses its exact pointer for every unresolved `extern_weak` static. In contrast, native `rustc_codegen_llvm` (`consts.rs:256-268`) emits a distinct internal mutable global `@_rust_extern_with_linkage_<stable_crate_id>_<sym>` per imported symbol (not marked `constant`, so distinct symbols retain distinct addresses even under `unnamed_addr`).

#### Empirical Comparison (`c2`)

Compiling a two-crate workspace (`prov` exporting `present_fn() -> i32 { 77 }` and `anchor()`, linked into `app` declaring `#[linkage = "extern_weak"]` statics `present_fn`, `missing_fn`, and built-in Linux symbol `strlen`):

| Execution Mode | Toolchain | Observed Output |
| :--- | :--- | :--- |
| Native binary (`cargo run`) | `rustc 1.98.0-nightly` (`14210df0e`) | `PRESENT=Some(77) MISSING=None SAME_SLOT=false BUILTIN_STRLEN=Some(5)` |
| `Miri` (`cargo miri run`) | `miri 0.1.0` (`14210df0e`) | `PRESENT=None MISSING=None SAME_SLOT=true BUILTIN_STRLEN=Some(5)` |
| Native binary | `rustc 1.102.0-nightly` (`3ef0c22cd`) | `PRESENT=Some(77) MISSING=None SAME_SLOT=false` |
| `Miri` | `miri` (`3ef0c22cd`) | `PRESENT=None MISSING=None SAME_SLOT=true` |

The `BUILTIN_STRLEN=Some(5)` control confirms both halves of `machine.rs:1474-1519`: Miri *does* resolve hardcoded OS weak shims in `extern_statics_imports` (`strlen`), while silently nulling out every Rust-crate-exported symbol and aliasing all their slot addresses together. Any test suite relying on `cargo miri test` to validate code that uses `extern_weak` feature probing against linked Rust or C libraries silently exercises only the fallback `None` path—without issuing a single warning or unsupported-operation error.

---

### 4. Contradictory `#[inline]`-Ignored Diagnostic vs. Broken `weak` Interposition

Basis: source (`rustc_attr_parsing/src/attributes/inline.rs`, `diagnostics.rs`, `rustc_mir_transform/src/inline.rs`, `cross_crate_inline.rs`, `rustc_codegen_llvm/src/attributes.rs`; `llvm-project` `GlobalValue.h`, `AlwaysInliner.cpp`, `InlineCost.cpp`) + execution (`1.98.0-nightly` / `LLVM 22.1.6` live in `support/probe_results_live.json`; `1.102.0-nightly` / `LLVM 23.1.5` recorded) + derived

#### Exact Four-Stage Causal Chain

Consider a library crate `weak_lib` defining three `#[linkage = "weak"] #[unsafe(no_mangle)] pub extern "C" fn` symbols returning `10`—`weak_plain` (no `#[inline]`), `weak_hint` (`#[inline]`), and `weak_always` (`#[inline(always)]`)—alongside same-CGU wrapper functions `call_plain`, `call_hint`, and `call_always`, linked into a binary `strong_bin` that provides strong `#[unsafe(no_mangle)]` overrides returning `99` for all three names:

1. **Misleading frontend lint (`rustc_attr_parsing`):**
   `InlineParser::deferred_finalize_check` (`compiler/rustc_attr_parsing/src/attributes/inline.rs:133-158`) checks whether any attribute on the function satisfies `kind.is_extern_indicator()` (`#[no_mangle]`, `#[export_name]`, or `#[linkage]`) and emits `UNUSED_ATTRIBUTES` (`diagnostics.rs:989-994`):
   ```text
   warning: `#[inline]` is ignored on externally exported functions
     = help: externally exported functions are functions with `#[no_mangle]`, `#[export_name]`, or `#[linkage]`
   ```
   Crucially, `InlineParser::finalize` (`inline.rs:129-131`) **still returns `Some(AttributeKind::Inline(a, s))`**, and `codegen_attrs.rs:74-82` copies `InlineAttr::Always` verbatim into `codegen_fn_attrs.inline`.
2. **MIR inliner respects extern indicators (`rustc_mir_transform`):**
   In `compiler/rustc_mir_transform/src/inline.rs:821-824`, `check_codegen_attributes` rejects non-generic callees for which `!tcx.cross_crate_inlinable(def_id)`. In `cross_crate_inline.rs:19-24`, `cross_crate_inlinable` immediately returns `false` whenever `codegen_fn_attrs.contains_extern_indicator()` is true (which includes `Linkage::WeakAny`, `#[no_mangle]`, and `#[export_name]`). Thus, MIR inlining *never* inlines `weak_plain`, `weak_hint`, or `weak_always`.
3. **LLVM codegen leaks `alwaysinline` onto interposable `weak` definitions (`rustc_codegen_llvm`):**
   In `compiler/rustc_codegen_llvm/src/attributes.rs:51-91` (`3ef0c22cd`; `lines 55-95` in `342d74463`; `lines 45-77` in `14210df0e`), `inline_attr` lowers `InlineAttr::Always` directly to `AttributeKind::AlwaysInline` and `InlineAttr::Hint` to `AttributeKind::InlineHint`, checking *only* `-Z inline-llvm`, `OptimizeAttr::DoNotOptimize`, and (for LLVM `< 23` only) `target_features`—**never** `codegen_fn_attrs.linkage` or `contains_extern_indicator()`:
   ```rust
   // compiler/rustc_codegen_llvm/src/attributes.rs:69-81 (3ef0c22cd)
   match inline {
       InlineAttr::Hint => Some(AttributeKind::InlineHint.create_attr(cx.llcx)),
       InlineAttr::Always
           if !codegen_fn_attrs.target_features.is_empty()
               && llvm_util::get_version() < (23, 0, 0) =>
       {
           Some(AttributeKind::InlineHint.create_attr(cx.llcx))
       }
       InlineAttr::Always | InlineAttr::Force { .. } => {
           Some(AttributeKind::AlwaysInline.create_attr(cx.llcx))
       }
       ...
   }
   ```
   The resulting LLVM IR for `weak_lib` at `-Z mir-opt-level=0 -C opt-level=0` (`support/probe_results_live.json`) confirms all three symbols have `weak` linkage in LLVM IR and `W` (weak) binding in ELF (`llvm-nm`), while carrying `alwaysinline` on `weak_always` and `inlinehint` on `weak_hint`:
   ```llvm
   define weak i32 @weak_always() unnamed_addr #1 { ... }
   define weak i32 @weak_hint() unnamed_addr #2 { ... }
   define weak i32 @weak_plain() unnamed_addr #3 { ... }
   attributes #1 = { alwaysinline nounwind nonlazybind uwtable ... }
   attributes #2 = { inlinehint nounwind nonlazybind uwtable ... }
   ```
4. **LLVM's `getAttributeBasedInliningDecision` checks `AlwaysInline` *before* `isInterposable()`:**
   In `llvm/include/llvm/IR/GlobalValue.h:431-438`, `isInterposableLinkage(WeakAnyLinkage)` returns `true`. However, in `llvm/lib/Analysis/InlineCost.cpp:3209-3239` (called by `AlwaysInlinerPass`, which runs at **all** optimization levels including `-C opt-level=0`, `AlwaysInliner.cpp:57-58, 108-118`):
   ```cpp
   // llvm/lib/Analysis/InlineCost.cpp:3209-3239 (LLVM 23.1.5, 0a5579eb649d)
   if (Call.hasFnAttr(Attribute::AlwaysInline)) {
     if (Call.getAttributes().hasFnAttr(Attribute::NoInline))
       return InlineResult::failure("noinline call site attribute");
     auto IsViable = isInlineViable(*Callee);
     if (IsViable.isSuccess())
       return InlineResult::success();
     return InlineResult::failure(IsViable.getFailureReason());
   }
   ...
   // Don't inline functions which can be interposed at link-time.
   if (Callee->isInterposable(/*CheckNoIPA=*/false))
     return InlineResult::failure("interposable");
   ```
   Because the `AlwaysInline` early return precedes `Callee->isInterposable()`, `weak_hint` (which lacks `AlwaysInline`) hits line 3238 and is **not** inlined (`%_0 = call i32 @weak_hint()`), preserving strong interposition (`99`), whereas `weak_always` takes the early return at line 3215 and is **inlined into `call_always` even at `-Z mir-opt-level=0 -C opt-level=0`**, baking in the weak body `10`!

#### Empirical Flag Matrix (`c3`)

| Flag Configuration | Warnings Emitted on `weak_lib` | `weak_lib` `call_always` IR | Runtime Output (`strong_bin`) |
| :--- | :--- | :--- | :--- |
| `-Z mir-opt-level=0 -C opt-level=0` (`14210df0e` & `3ef0c22cd`) | 2x `` `#[inline]` is ignored on externally exported functions `` | `weak_always` inlined (no `call @weak_always`) | `CALLERS=(99, 99, 10) DIRECT=(99, 99, 99)` |
| `-C opt-level=0` (`14210df0e` & `3ef0c22cd`) | 2x `` `#[inline]` is ignored on externally exported functions `` | `weak_always` inlined | `CALLERS=(99, 99, 10) DIRECT=(99, 99, 99)` |
| `-C opt-level=2` (`14210df0e` & `3ef0c22cd`) | 2x `` `#[inline]` is ignored on externally exported functions `` | `weak_always` inlined; `weak_plain`/`weak_hint` kept as `tail call` | `CALLERS=(99, 99, 10) DIRECT=(99, 99, 99)` |
| `-Z inline-llvm=no -C opt-level=0` (`14210df0e` control) | 2x `` `#[inline]` is ignored on externally exported functions `` | `inline_attr` emits `noinline` (`attributes.rs:57-60`) | `CALLERS=(99, 99, 99) DIRECT=(99, 99, 99)` |

The `-Z inline-llvm=no` control isolates the exact failure boundary: once LLVM `alwaysinline` is suppressed, ELF interposition succeeds for all three functions (`(99, 99, 99)`).

---

### 5. Externally Implementable Items (`#[eii]`): Alias Shims, Suppression, Validation, and `Miri` Foreign-Lookup Gap

Basis: source (`rustc_builtin_macros/src/eii.rs`, `rustc_passes/src/eii.rs`, `rustc_codegen_ssa/src/codegen_attrs.rs`, `rustc_codegen_llvm/src/mono_item.rs`, `src/tools/miri/src/shims/foreign_items.rs`) + execution (`1.98.0-nightly` live in `support/probe_results_live.json`; `1.102.0-nightly` recorded)

#### Macro Expansion, Validation, and Codegen Architecture

1. **Macro desugaring (`compiler/rustc_builtin_macros/src/eii.rs:145-185, 310-395`):**
   An EII declaration with a default body—such as `#[eii] pub fn compute_hook(x: i32) -> i32 { x + 10 }` in crate `hook_api`—expands into three items:
   - An anonymous `const _: () = { #[eii_impl(..., is_default = true)] pub fn compute_hook(x: i32) -> i32 { x + 10 } };` holding the default implementation;
   - A foreign declaration `#[rustc_eii_foreign_item] extern "Rust" { pub safe fn compute_hook(x: i32) -> i32; }` whose symbol name intentionally remains *mangled* (`codegen_attrs.rs:453-458`, e.g., `_RNvCs..._8hook_api12compute_hook`);
   - A builtin attribute macro `#[eii_declaration(compute_hook)] pub macro compute_hook() {}` used by downstream crates to attach explicit overrides (`#[hook_api::compute_hook] fn custom_impl(x: i32) -> i32 { x + 900 }`).
2. **Whole-graph uniqueness and existence validation (`compiler/rustc_passes/src/eii.rs:44-162`):**
   `check_externally_implementable_items` gathers `tcx.externally_implementable_items(cnum)` across all dependency crates plus `LOCAL_CRATE` and partitions implementations into `default_impls` and `explicit_impls`:
   - `explicit_impls.len() > 1` unconditionally emits `DuplicateEiiImpls` (`eii.rs:99-117`) in both `rlib` (`CheckDuplicates`) and final-artifact (`CheckExistence`) builds—reproduced live (`c4.duplicate_explicit_compile_error`, `rc = 1`: ``error: multiple implementations of `#[dup_hook]` ``).
   - `default_impls.len() > 1` emits a delayed bug (`eii.rs:119-122`).
   - In non-`rlib` final artifacts (`CheckingMode::CheckExistence`), `explicit_impls.is_empty() && default_impls.is_empty()` emits `EiiWithoutImpl` (`eii.rs:139-151`).
3. **Same-crate default-alias suppression (`compiler/rustc_codegen_ssa/src/codegen_attrs.rs:241-265`):**
   If a single crate defines *both* the default implementation and an explicit override, emitting both aliases into the same object file would collide within one LLVM module before ELF strong-over-weak resolution could occur. `codegen_attrs.rs:246-258` detects `i.is_default && impls.iter().any(|(_, imp)| !imp.is_default)` over `LOCAL_CRATE` and suppresses the default alias entirely. Verified live in `c4.same_crate_ir_defs`: the emitted LLVM IR contains only `define hidden i32 @_RNv..._4main14local_override` and the strong alias `define dso_local i32 @_RNv..._4main10local_hook`, producing `SAME_CRATE_OVERRIDE=705`.
4. **Function-alias forwarding shims vs. static LLVM aliases (`compiler/rustc_codegen_llvm/src/mono_item.rs:104-231`):**
   For statics, `add_static_aliases` (`lines 133-163`) emits true LLVM `GlobalAlias` entries (`llvm::add_alias`) to preserve address identity. For functions (because LLVM cannot attach target-architecture attributes to aliases on macOS), `add_function_aliases` (`lines 166-231`) synthesizes a forwarding wrapper function under the foreign item's mangled symbol name that directly calls the implementing function (`aliasee`) and forwards `sret` indirect return slots if present. In `1.98.0-nightly` (`14210df0e`), the default forwarding shim carries `Linkage::LinkOnceAny` (`define linkonce i32 @_RNv..._8hook_api12compute_hook`); in `1.102.0-nightly` (`3ef0c22cd`) and `main` (`342d74463`), it carries `Linkage::WeakAny` (`define weak`). Explicit overrides always carry `Linkage::External` (`define dso_local`).

#### Root Cause of `Miri`'s `#[eii]` Failure (`rc = 1`)

When `hook_api::invoke(5)` calls the `#[rustc_eii_foreign_item]` foreign function `compute_hook(x)`, `Miri` enters foreign-item dispatch and calls `lookup_exported_symbol(link_name)` (`src/tools/miri/src/shims/foreign_items.rs:117-216` in `3ef0c22cd`/`342d74463`; `lines 126-225` in `14210df0e`):

```rust
// src/tools/miri/src/shims/foreign_items.rs:139-151 (3ef0c22cd / 342d74463)
helpers::iter_exported_symbols(tcx, |cnum, def_id, _used| {
    let attrs = tcx.codegen_fn_attrs(def_id);
    // Skip over items without an explicitly defined symbol name.
    if !(attrs.symbol_name.is_some()
        || attrs.flags.contains(CodegenFnAttrFlags::RUSTC_STD_INTERNAL_SYMBOL))
    {
        return interp_ok(());
    }

    let instance = Instance::mono(tcx, def_id);
    let symbol_name = tcx.symbol_name(instance).name;
    let is_weak = attrs.linkage == Some(Linkage::WeakAny);
    if symbol_name == link_name.as_str() { ... }
```

This fails for `#[eii]` at **three independent choke points**:

1. **Filter rejection (`foreign_items.rs:142-146`):** Neither the default EII implementation nor an explicit `#[hook_api::compute_hook]` implementation sets `attrs.symbol_name` (`#[no_mangle]` / `#[export_name]`) or `RUSTC_STD_INTERNAL_SYMBOL` (`14210df0e:154-156` also checks `NO_MANGLE`, which is likewise unset). Miri immediately discards every EII implementation.
2. **Missing alias lookup (`foreign_items.rs:148-151`):** Even if the filter accepted `CodegenFnAttrFlags::EXTERNALLY_IMPLEMENTABLE_ITEM`, line 149 compares `link_name` (the mangled symbol name of the *foreign declaration* `_RNv..._8hook_api12compute_hook`) against `tcx.symbol_name(Instance::mono(tcx, def_id)).name` (the mangled name of the *implementing function*, e.g. `_RNv..._12app_override11custom_impl` or `_RNvNv..._8hook_api1__12compute_hook`), never iterating `attrs.foreign_item_symbol_aliases`.
3. **Weak-linkage classification (`foreign_items.rs:150`):** Line 150 checks `attrs.linkage == Some(Linkage::WeakAny)` on the item itself rather than the per-alias `Linkage` tuple element inside `attrs.foreign_item_symbol_aliases`, which would misclassify default EII aliases as strong even after resolving alias names (and under `14210df0e`, default aliases used `Linkage::LinkOnceAny`, which `== Some(Linkage::WeakAny)` does not match).

#### Empirical Results (`c4`)

| Case | Native (`--release` & debug, `14210df0e` & `3ef0c22cd`) | `Miri` (`14210df0e` & `3ef0c22cd`) |
| :--- | :--- | :--- |
| `app_default` (uses default impl `x + 10`) | `rc = 0`, `DEFAULT=15` | `rc = 1`, `error: unsupported operation: can't call foreign function _RNv..._8hook_api12compute_hook on OS linux` |
| `app_override` (explicit override `x + 900`) | `rc = 0`, `OVERRIDE=905` | `rc = 1`, `error: unsupported operation: can't call foreign function _RNv..._8hook_api12compute_hook on OS linux` |
| `app_same_crate` (default `x + 10` + same-crate override `x + 700`) | `rc = 0`, `SAME_CRATE_OVERRIDE=705` (weak default alias suppressed in IR) | not separately executed (same foreign-lookup path) |
| `dup_eii.rs` (two explicit overrides) | Compile error `rc = 1`: ``error: multiple implementations of `#[dup_hook]` `` | rejected before Miri execution |

---

### 6. Cross-Version Delta Matrix Across `rustc 1.98.0-nightly`, `1.102.0-nightly`, and `main`

Basis: source (`14210df0e`, `3ef0c22cd`, `342d74463`; LLVM `08c84e69a84d`, `0a5579eb649d`) + execution (`14210df0e` live; `3ef0c22cd` recorded)

| Mechanism / Defect | `1.98.0-nightly` (`14210df0e`, LLVM `22.1.6`) | `1.102.0-nightly` (`3ef0c22cd`, LLVM `23.1.5`) | `main` (`342d74463`, `2026-11-22`) |
| :--- | :--- | :--- | :--- |
| `c1`: Same-CGU `define extern_weak` `SIGILL` | **Present** (`consts.rs:188`, `LLVMSetLinkage(g1, ...)` -> `AsmPrinter` `SIGILL`, `rc = -4`; live verified for both fn and static) | **Present** (`consts.rs:226`, `LLVMSetLinkage(actual_global, ...)` -> `AsmPrinter::emitFunctionBody` `SIGILL`, `rc = -4`) | **Present** (`consts.rs:226` identical logic; signature refactor `&'ll Value -> Value<'ll>` only) |
| `c1`: Indirection global `@_rust_extern_with_linkage_*` | `internal global ptr @sym` (no `unnamed_addr`, no PAC signing) | `internal unnamed_addr global ptr @sym, !guid !1` (+ PAC signing support `consts.rs:214-248, 266`) | Identical to `3ef0c22cd` |
| `c2`: Miri `extern_weak` short-circuit | **Present** (`machine.rs:1422-1439`, field `missing_weak_symbol`; live verified `PRESENT=None SAME_SLOT=true`) | **Present** (`machine.rs:1502-1519`, renamed `extern_static_weak_import_default`; `PRESENT=None SAME_SLOT=true`) | **Present** (`machine.rs` byte-for-byte identical to `3ef0c22cd`) |
| `c3`: `#[inline(always)]` + `weak` contradiction | **Present** (`attributes.rs:45-77`, live verified `CALLERS=(99, 99, 10)` across all 3 opt configs; `-Z inline-llvm=no` -> `(99, 99, 99)`) | **Present** (`attributes.rs:51-91`, `CALLERS=(99, 99, 10)` across all 3 opt configs; `target_features` guard skipped for LLVM `>= 23`) | **Present** (`attributes.rs:55-95` identical logic; signature refactor `&'ll Attribute -> Attribute<'ll>` only) |
| `c4`: `#[eii]` default alias linkage | `Linkage::LinkOnceAny` (`codegen_attrs.rs:262`, IR `define linkonce`) | `Linkage::WeakAny` (`codegen_attrs.rs:262`) | `Linkage::WeakAny` (`codegen_attrs.rs:262`, identical) |
| `c4`: Miri `#[eii]` foreign-lookup failure | **Present** (`foreign_items.rs:154-156` checks `symbol_name`, `NO_MANGLE`, or `RUSTC_STD_INTERNAL_SYMBOL`; live verified `rc = 1`) | **Present** (`foreign_items.rs:142-143` checks `symbol_name` or `RUSTC_STD_INTERNAL_SYMBOL`; `rc = 1`) | **Present** (`foreign_items.rs` byte-for-byte identical to `3ef0c22cd`) |

---

### 7. Anneal Trusted Boundary Analysis and Verified-Compiler Architectural Invariants

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean`, `trusted/rustc-capture/src/driver.rs`) + derived

#### Current Fail-Closed Posture of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes that Anneal's current MIR trusted boundary fails closed on every construct implicated in `c1`–`c4`, but does **not** yet model symbol linkage or interposition metadata:

- `Trusted.MirAst.MirTy` (`trusted/lean/Trusted/MirAst.lean:308-322`) maps `TyKind::Foreign`, `TyKind::FnDef`, and `TyKind::FnPtr` to `.unsupported`, forcing `Trusted.MirSemantics` to abort with `FaultKind.unsupported` whenever `extern_weak` function-pointer statics (`Option<unsafe extern "C" fn(...)>`) or foreign types appear.
- `Trusted.MirAst.TerminatorKind` (`trusted/lean/Trusted/MirAst.lean:780-792`) supports only direct `FnDef` calls (`.call callee args dst target unwind`), mapping indirect calls (needed to invoke loaded `extern_weak` function pointers) to `.unsupported`.
- `Trusted.MirAst.Program` (`trusted/lean/Trusted/MirAst.lean:947-953`) carries `bodies : List Body`, `entryDefId`, `pointerWidthBits`, `mirProfileVersion`, and `scope : VerificationScope`, with **no** `Linkage` / `import_linkage` / `foreign_item_symbol_aliases` / `isInterposable` fields on `Body` or `Program`. As `MirAst.lean:943-946` explicitly documents, when `scope = .crate`, completeness and non-interposition of `bodies` is currently an **unchecked external producer obligation**.
- `trusted/rustc-capture/src/driver.rs` (`lines 32-145`) currently implements only a clean-analysis callback check (`AnalysisCallbacks::after_analysis`) and does not yet extract MIR bodies or `tcx.codegen_fn_attrs(def_id)`.

#### Four Mandatory Invariants for Verified `rustc` Codegen and Anneal Capture

Any verified Rust compiler backend or future `anneal-rustc-capture` extractor that admits `#[linkage]`, `#[eii]`, or open-world linking **must** enforce four invariants at the MIR-capture and IR-lowering boundaries:

1. **Declaration-Only `ExternalWeak` Guard (eliminates `c1`):** Lowering an `import_linkage = Some(Linkage::ExternalWeak)` reference must check whether `sym` is already defined in the current compilation unit (`!is_declaration(gv)` or membership in CGU `MonoItem` definitions). If defined in the same CGU, the indirection slot `@_rust_extern_with_linkage_*` must point to the existing definition *without* mutating the definition's linkage. Independently, the IR well-formedness checker must enforce `hasBody = true -> isValidFnDefinitionLinkage linkage = true` (rejecting `externalWeak`, `common`, and `appending` on definitions), closing `llvm::Verifier`'s blind spot.
2. **Interposability-First Inlining Guard (eliminates `c3`):** Both MIR and backend inliners—including forced/always-inline passes—must evaluate `isInterposableLinkage(callee.linkage)` *before* honoring `InlineAttr::Always` / `Attribute::AlwaysInline`. Under `Theorem 1` (`inlining_sound_under_link_override_iff_non_interposable`), inlining a `weakAny`, `linkOnceAny`, `common`, or `externalWeak` body is unsound whenever link-time strong overrides are admissible. In addition, `anneal-rustc-capture` must fail closed (or treat calls as opaque external calls rather than binding the local `Body`) whenever `tcx.codegen_fn_attrs(did).linkage` is interposable (`WeakAny`, `LinkOnceAny`, `Common`, `ExternalWeak`) or `did` carries a weak EII alias.
3. **Unified Linker/Interpreter Symbol-Resolution Algebra (eliminates `c2` and `c4`):** An interpreter or reference semantics (such as `Miri` or `lean-miri`) modeling cross-crate linking must resolve both `extern_weak` imports and `#[eii]` foreign calls through the same commutative, associative strong-over-weak symbol table as ELF linking:
   - For `extern_weak`, search exported crate symbols (both functions and statics, resolving strong over weak) *before* falling back to null, and allocate distinct per-symbol indirection slots if address identity is observable (or explicitly document non-unique slot semantics matching `unnamed_addr` merging).
   - For `#[eii]`, index every exported item's `attrs.foreign_item_symbol_aliases` by the aliased `foreign_item`'s mangled symbol name together with the per-alias `Linkage` (`WeakAny` vs. `External`), rather than filtering solely by `attrs.symbol_name` / `RUSTC_STD_INTERNAL_SYMBOL`.
4. **Same-Crate EII Default-Alias Suppression + Global Uniqueness Gate (soundness condition for `c4`):** Whole-crate-graph verification must require at most one explicit EII implementation (`DuplicateEiiImpls`) and at most one default implementation, plus same-crate suppression of weak default aliases whenever the same CGU/crate also defines an explicit implementation. Only under this precondition does `resolveSym` guarantee deterministic unique resolution across arbitrary crate/object link orders (`Theorem 3`).

---

### 8. Mechanized Lean `v4.34.1` Soundness and Sharpness Formalization

Basis: source + execution (`leanprover/lean4` `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`, `support/LinkageInterpositionAndEiiSoundness.lean`)

`support/LinkageInterpositionAndEiiSoundness.lean` (1,021 lines, namespace `LinkageInterpositionAndEiiSoundness`) mechanizes the LLVM linkage well-formedness model, the interposability inlining guard, the commutative-monoid strong-over-weak linker algebra, `#[eii]` lowering and suppression, and constructive sharpness counterexamples for all four empirical defects.

#### Kernel Verification Summary

- **Toolchain & flags:** `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/LinkageInterpositionAndEiiSoundness.lean` -> **exit code `0`**, zero warnings, zero errors.
- **Axiom & TCB hygiene audit:** Across all **382 kernel constants** in `LinkageInterpositionAndEiiSoundness.*`:
  - `0` `sorry` / `sorryAx`
  - `0` `Classical.choice`
  - `0` `Lean.ofReduceBool` / `Lean.trustCompiler` (`0` `bv_decide`, `0` `native_decide`)
  - `0` `omega`
  - `0` `partial def` / `unsafe` constants
  - `0` `._unsafe_rec` compiler helpers (all recursive definitions are marked `noncomputable def`, and no `deriving` clauses are placed on recursive inductives).

#### Core Theorems and Axiom Dependencies

| Theorem (`LinkageInterpositionAndEiiSoundness.*`) | Line | Formal Statement Summary | Verified Kernel Axioms |
| :--- | ---: | :--- | :--- |
| `applyExternWeakGuarded_preserves_wf` | 125 | `wfLlvmFn f → wfLlvmFn (applyExternWeakGuarded f)` — guarding `LLVMSetLinkage` by `!f.hasBody` preserves LLVM IR well-formedness. | `[propext]` |
| `inlining_sound_under_link_override_iff_non_interposable` | 171 | `(∀ ov, AdmissibleOverride d.linkage d.localVal ov → evalInlinedCall d = evalDirectCall d ov) ↔ isInterposableLinkage d.linkage = false` — exact necessary and sufficient condition for link-override-safe call-site inlining. | **(none — 0 axioms)** |
| `guardedInlineDecision_sound` | 254 | `guardedInlineDecision d alwaysInline = true → AdmissibleOverride ... → evalInlinedCall d = evalDirectCall d ov` — interposability-first inlining guard is sound even when `alwaysInline = true`. | `[propext]` |
| `linker_resolve_commutes_and_extern_weak_binds_strong_when_present` | 461 | `(∀ s xs ys, resolveSym s (xs ++ ys) = resolveSym s (ys ++ xs)) ∧ (resolveSym s xs = .resolved .strong v → AllWeakOrOther s ws → resolveSym s (ws ++ xs) = .resolved .strong v ∧ resolveSym s (xs ++ ws) = .resolved .strong v ∧ elfExternWeakEval s (ws ++ xs) = .bound v)` — link-order invariance plus strong-over-weak dominance for `extern_weak`. | `[propext, Quot.sound]` |
| `eii_resolution_deterministic_iff_at_most_one_explicit` | 830 | `countDefault s crates ≤ 1 → 1 ≤ countExplicit s crates + countDefault s crates → ((∃ st v, resolveSym s (lowerAllCrates crates) = .resolved st v) ↔ countExplicit s crates ≤ 1)` — exact determinism boundary for `#[eii]` lowering + ELF linking. | `[propext]` |
| `ce1_same_cgu_set_linkage_produces_ill_formed_define_extern_weak` | 899 | Witness `f` (`external`, `hasBody = true`, `bodyVal = 77`): `wfLlvmFn f`, `isEmittableByAsmPrinter f.linkage = true`, yet `applyExternWeakUnchecked f` violates `wfLlvmFn`, fails `isEmittableByAsmPrinter`, and still satisfies `llvmVerifierAcceptsFn`. | `[propext]` |
| `ce2_miri_short_circuit_diverges_from_elf_linker_on_present_symbol` | 925 | Witness (`present_fn = 77`, `missing_fn` absent, built-in `strlen = 5`): native ELF returns `.bound 77` / `.null` with distinct slots (`1001 ≠ 1002`), while Miri short-circuits both to `.null` at the identical shared slot `0`. | `[propext]` |
| `ce3_alwaysinline_on_weak_breaks_strong_interposition` | 957 | Witness (`weakAny`, local `10`, admissible strong override `some 99`): `llvmInlineDecision d true = true` bakes in `10 ≠ 99`, whereas `llvmInlineDecision d false = false` and `guardedInlineDecision d true = false` preserve `99`. | `[propext]` |
| `ce4_miri_eii_filter_misses_aliased_impl` | 975 | Witness (`hook_api` default `15`, `app_override` explicit `905`, both `hasExplicitSymName = false`): native resolves `.resolved .strong 905` (and `.resolved .weak 15` without override), while Miri's `miriLookupEiiSymbol` returns `none`. | `[propext]` |
| `eii_same_crate_suppresses_default_alias` | 996 | Witness single crate containing both default (`15`) and explicit (`705`): `lowerCrateEii` suppresses the weak default alias and emits only `[{ sym := 7, strength := .strong, val := 705 }]`. | `[propext]` |

## Boundaries

To prevent over-generalization, the following negative-space boundaries apply:

- **Non-ELF targets (`not examined`):** All empirical executions (`c1`–`c4`) ran on `x86_64-unknown-linux-gnu` (ELF). Mach-O (`.weak_definition`, `.weak_reference`, two-level namespaces, macOS `add_function_aliases` target-architecture constraints noted in `mono_item.rs:108-115`) and Windows COFF/PE (`dllimport`, `__imp_` stubs in `consts.rs:421-450`, weak externals) were not empirically executed.
- **Alternative `rustc` codegen backends (`not examined`):** Only `rustc_codegen_llvm` was audited and executed. `rustc_codegen_cranelift` and `rustc_codegen_gcc` have independent linkage and `extern_weak` lowering paths not examined here.
- **LTO / ThinLTO and multi-CGU `c1` triggering (`not examined`):** Case `c1` was triggered deterministically via `-C codegen-units=1`. Whether ThinLTO or FatLTO cross-module importing can merge a defining function and an `extern_weak` consumer into one LLVM module and reproduce the same `SIGILL` crash when compiled from separate CGUs or crates was not tested.
- **Dynamic shared objects (`cdylib` / `dylib`) and ELF `LD_PRELOAD` interposition (`not examined`):** Case `c3` tested static link-time strong-over-weak interposition between an `rlib` and a binary. Dynamic-linker (`RTLD_GLOBAL` / `LD_PRELOAD` / `-fsemantic-interposition`) interposition of `external` (`dso_preemptable`) symbols in shared libraries is a distinct mechanism not covered by the `AdmissibleOverride` predicate for `ExternalLinkage` (`ov = none` models static/DSO-local linking, matching `mono_item.rs:270-291` for executables and PIE).
- **Multiple weak definitions in native ELF vs. Miri (`known not to apply` as identical behavior):** In the Lean `LinkOutcome` algebra (`LinkageInterpositionAndEiiSoundness.lean:283-303`), combining two weak definitions produces `.ambiguousWeak` (matching `Miri`'s explicit `MultipleSymbolDefinitions` error in `foreign_items.rs:168-198` and reflecting link-order non-determinism). Native ELF static linkers (`ld` / `lld`) instead silently select the *first* weak definition encountered on the linker command line; therefore `mergeOutcome` models *order-independent* deterministic resolution rather than a specific ELF linker's first-wins tie-breaker.
- **Live execution of `1.102.0-nightly` (`3ef0c22cd`) and `main` (`342d74463`) on this host (`not examined` locally for `342d74463`; `1.102.0-nightly` recorded separately):** On `2026-11-22`, the live `support/probe_linkage_extern_weak_and_eii.py` run (`support/probe_results_live.json`) executed `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `LLVM 22.1.6` / `miri 0.1.0`. The `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` / `LLVM 23.1.5` outputs for `c1`–`c4` come from an independent execution on that pinned nightly toolchain, while `342d74463` (`main`) was verified by exact source inspection and diff against `3ef0c22cd` (zero semantic changes to any of the four defective code paths).
- **Non-executable `#[eii]` static items in `Miri` (`not examined`):** Case `c4` tested `#[eii]` functions (`add_function_aliases`). Static EII items (`add_static_aliases` via `llvm::add_alias`, `mono_item.rs:133-163`) were inspected in `rustc` source (`consts.rs:422-446`, `mono_item.rs:133-163`) but not executed under `Miri`.
- **Lean model abstraction boundary (`known not to apply` as full machine-code verification):** `support/LinkageInterpositionAndEiiSoundness.lean` is a standalone formal model of the linkage, inlining, symbol-resolution, and EII-lowering contracts; it does not import `joshlf/anneal`'s `Trusted.MirSemantics` (which does not yet represent linkage or foreign symbols) and does not verify `rustc`'s Rust source code or LLVM's C++ implementation directly.
- **`#[eii]` stability (`unsupported` on stable Rust):** `#![feature(extern_item_impls)]` is explicitly flagged `incomplete_features` (`rust-lang/rust#125418`) and `#![feature(linkage)]` is an unstable nightly-only feature; neither is supported on stable toolchains.

## Evidence

### Primary Upstream Source Citations (Pinned 40-Hex Commit SHAs)

1. **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`) and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`main`, `2026-11-22`):**
   - `compiler/rustc_attr_parsing/src/attributes/inline.rs:129-158`: `InlineParser::finalize` retains `AttributeKind::Inline`, while `deferred_finalize_check` emits `UNUSED_ATTRIBUTES` (`InlineIgnoredForExported`) when `kind.is_extern_indicator()` is true and `InlineAttr` is not `Never`.
   - `compiler/rustc_attr_parsing/src/diagnostics.rs:989-994`: defines `InlineIgnoredForExported` diagnostic text ``"`#[inline]` is ignored on externally exported functions"`` and help text naming `` `#[no_mangle]`, `#[export_name]`, or `#[linkage]` ``.
   - `compiler/rustc_passes/src/check_attr.rs:1259-1282`: `check_linkage` checks only `static mut` foreign linkage and `const fn` linkage.
   - `compiler/rustc_passes/src/eii.rs:44-162`: `check_externally_implementable_items` enforces `DuplicateEiiImpls` (`lines 99-117`), delayed bug on `default_impls.len() > 1` (`lines 119-122`), and `EiiWithoutImpl` in `CheckingMode::CheckExistence` (`lines 139-151`).
   - `compiler/rustc_builtin_macros/src/eii.rs:145-185, 310-395`: `#[eii]` expansion into default `const _: ()` item, `#[rustc_eii_foreign_item] extern "Rust"` declaration, and attribute macro.
   - `compiler/rustc_codegen_ssa/src/codegen_attrs.rs:74-82, 196-278, 445-476`: splits `import_linkage` vs. `linkage` (`lines 196-211`); suppresses same-crate EII default alias when a local non-default impl exists (`lines 246-258`); pushes `(foreign_item, Linkage::WeakAny | Linkage::External, Visibility::Default)` (`lines 260-265`); preserves mangled names for `EXTERNALLY_IMPLEMENTABLE_ITEM` foreign items (`lines 453-458`).
   - `compiler/rustc_middle/src/middle/codegen_fn_attrs.rs:269-286`: `CodegenFnAttrs::contains_extern_indicator`.
   - `compiler/rustc_mir_transform/src/inline.rs:803-852` and `compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-24`: MIR inliner skips non-generic callees where `cross_crate_inlinable` returns `false` due to `contains_extern_indicator()`.
   - `compiler/rustc_codegen_llvm/src/base.rs:116-129, 230-241`: two-phase CGU `predefine` then `define` loops and `linkage_to_llvm` mapping.
   - `compiler/rustc_codegen_llvm/src/declare.rs:36-52, 94-99, 165-196`: `declare_simple_fn` (`LLVMGetOrInsertFunction`) and `declare_global` (`LLVMRustGetOrInsertGlobal`) return existing definitions on name match.
   - `compiler/rustc_codegen_llvm/src/mono_item.rs:26-102, 133-231`: `predefine_static`, `predefine_fn`, `add_static_aliases`, `add_function_aliases`.
   - `compiler/rustc_codegen_llvm/src/consts.rs:189-270, 367-407`: `check_and_apply_linkage` unconditionally executes `llvm::set_linkage(actual_global, base::linkage_to_llvm(linkage))` (`line 226`) and emits `@_rust_extern_with_linkage_<stable_crate_id>_<sym>` (`lines 256-269`).
   - `compiler/rustc_codegen_llvm/src/attributes.rs:51-91` (`3ef0c22cd`; `55-95` in `342d74463`): `inline_attr` emits `AttributeKind::AlwaysInline` without checking `codegen_fn_attrs.linkage`.
   - `src/tools/miri/src/machine.rs:1463-1525` (byte-identical in `3ef0c22cd` and `342d74463`): `extern_static_pointer` short-circuits `import_linkage == Some(Linkage::ExternalWeak)` to `extern_static_weak_import_default` (`lines 1502-1519`) before `lookup_exported_static` (`line 1522`).
   - `src/tools/miri/src/shims/extern_static.rs:52-108`: populates `extern_statics_imports` with fixed OS shims and allocates the single shared zeroed slot (`lines 101-105`).
   - `src/tools/miri/src/shims/foreign_items.rs:117-216` (byte-identical in `3ef0c22cd` and `342d74463`): `lookup_exported_symbol` filters out exported items lacking `attrs.symbol_name` or `RUSTC_STD_INTERNAL_SYMBOL` (`lines 142-146`) and never reads `attrs.foreign_item_symbol_aliases`.

2. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`):**
   - `compiler/rustc_codegen_ssa/src/codegen_attrs.rs:192-265`: same `import_linkage` split and same-crate EII default suppression, using `Linkage::LinkOnceAny` for default EII aliases (`line 262`).
   - `compiler/rustc_codegen_llvm/src/consts.rs:157-213`: same unchecked `llvm::set_linkage(g1, base::linkage_to_llvm(linkage))` (`line 188`), omitting `unnamed_addr` on `_rust_extern_with_linkage_*`.
   - `compiler/rustc_codegen_llvm/src/attributes.rs:45-77`: same `inline_attr` emitting `AlwaysInline` without linkage guard.
   - `src/tools/miri/src/machine.rs:1390-1445`: same `ExternalWeak` short-circuit returning `missing_weak_symbol` (`line 1437`).
   - `src/tools/miri/src/shims/foreign_items.rs:126-225`: `lookup_exported_symbol` filters by `attrs.symbol_name.is_some() || NO_MANGLE || RUSTC_STD_INTERNAL_SYMBOL` (`lines 154-156`).

3. **`rust-lang/llvm-project` @ `0a5579eb649d3634a9c30ac873300cc2944fa070` (LLVM `23.1.5`) and `08c84e69a84d95936296dfcab0e38b34100725d5` (LLVM `22.1.6`):**
   - `llvm/include/llvm/IR/GlobalValue.h:431-468, 543-555`: `isInterposableLinkage` returns `true` for `WeakAnyLinkage`, `LinkOnceAnyLinkage`, `CommonLinkage`, `ExternalWeakLinkage`; `setLinkage` updates linkage unconditionally.
   - `llvm/lib/AsmParser/LLParser.cpp:7084-7090`: rejects `ExternalWeakLinkage` when `IsDefine` is true (`"invalid linkage for function definition"`).
   - `llvm/lib/IR/Verifier.cpp:568-570, 3024-3035`: checks `hasValidDeclarationLinkage()` only when `GV.isDeclaration()`, and `!F.hasCommonLinkage()` on functions—omitting `!hasExternalWeakLinkage()` on definitions.
   - `llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp:723-761, 1016-1041, 2052-2053` (LLVM `23.1.5`; `686-722, 753, 979, 1963` in LLVM `22.1.6`): `emitFunctionBody` -> `emitFunctionHeader` -> `emitLinkage` (and `emitGlobalVariable` -> `emitLinkage`) hits `llvm_unreachable("Should never emit this")` on `ExternalWeakLinkage`, `AvailableExternallyLinkage`, and `AppendingLinkage`.
   - `llvm/lib/Transforms/IPO/AlwaysInliner.cpp:56-75, 96-118` and `llvm/lib/Analysis/InlineCost.cpp:3209-3239`: `getAttributeBasedInliningDecision` returns `InlineResult::success()` on `Attribute::AlwaysInline` (`line 3215`) *before* evaluating `Callee->isInterposable(/*CheckNoIPA=*/false)` (`line 3238`).

4. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
   - `trusted/lean/Trusted/MirAst.lean:77-92, 308-322, 780-792, 943-953`: documents `noncomputable` discipline (preventing `._unsafe_rec`), fails closed on `TyKind::Foreign`/`FnPtr` and indirect calls, and documents `Program.bodies` completeness as an external producer obligation.
   - `trusted/rustc-capture/src/driver.rs:27-145`: records only clean `after_analysis` callbacks without extracting MIR or `codegen_fn_attrs`.

### Preserved Report-Owned Artifacts

- `support/probe_linkage_extern_weak_and_eii.py`: Standalone Python 3.10+ harness (stdlib only) constructing hermetic temporary crates to reproduce `c1` (fn + static same-CGU `SIGILL`, `--emit=llvm-ir`, `llvm-as` round-trip, `-Z verify-llvm-ir`, and separate-crate control), `c2` (native vs. Miri cross-crate `extern_weak` + `SAME_SLOT` + Linux built-in `strlen` control), `c3` (4-configuration flag sweep + LLVM IR + `llvm-nm` symbol table), and `c4` (`#[eii]` native debug/release default, cross-crate override, same-crate suppression, duplicate-explicit compile error, LLVM IR, and Miri execution).
- `support/probe_results_live.json`: Complete sanitized JSON output captured on `2026-11-22` running `support/probe_linkage_extern_weak_and_eii.py` against `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `LLVM 22.1.6` / `miri 0.1.0`.
- `support/LinkageInterpositionAndEiiSoundness.lean`: 1,021-line standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) mechanization containing all 22 theorems (`applyExternWeakGuarded_preserves_wf`, `inlining_sound_under_link_override_iff_non_interposable`, `guardedInlineDecision_sound`, `linker_resolve_commutes_and_extern_weak_binds_strong_when_present`, `eii_resolution_deterministic_iff_at_most_one_explicit`, `ce1`–`ce4`, `eii_same_crate_suppresses_default_alias`, and supporting monoid/counting lemmas) with `#print axioms` verification.

## Revalidation

To check whether any of the four behaviors have changed on a newer nightly `rustc`, `LLVM`, or `Miri` toolchain, or after editing `support/LinkageInterpositionAndEiiSoundness.lean`, run these narrow discriminating checks:

### 1. Re-run the All-in-One Empirical Probe (`~10 s`)

```bash
python3 support/probe_linkage_extern_weak_and_eii.py --output /tmp/linkage_probe_reval.json
```

Inspect the four discriminating predicates in `/tmp/linkage_probe_reval.json`:

- **`c1` fixed?** Check `cases.c1_same_cgu_define_extern_weak_sigill.fn_same_cgu.codegen_rc`: `-4` (`SIGILL`) confirms the crash persists; `0` (with no `define extern_weak` in `emitted_ir_lines` and `llvm_as_roundtrip.rc == 0`) indicates `consts.rs` now guards `LLVMSetLinkage` on existing definitions; a non-`-4` error on `verify_llvm_ir_rc` indicates `llvm::Verifier` closed its `ExternalWeakLinkage` definition blind spot. Also check `static_same_cgu.codegen_rc`.
- **`c2` fixed?** Compare `cases.c2_cross_crate_extern_weak_native_vs_miri.miri_stdout` against `native_stdout`: `PRESENT=None ... SAME_SLOT=true` confirms the Miri `extern_static_pointer` short-circuit persists; `PRESENT=Some(77)` indicates Miri now consults crate exports for `extern_weak`.
- **`c3` fixed?** Check `cases.c3_weak_linkage_inline_warning_contradiction.mir_opt0_o0.stdout`: `CALLERS=(99, 99, 10)` confirms `#[inline(always)]` still leaks `alwaysinline` past `isInterposable()`; `CALLERS=(99, 99, 99)` indicates either `rustc_codegen_llvm/src/attributes.rs` suppressed `alwaysinline` on interposable/exported functions or LLVM `InlineCost.cpp` moved `isInterposable()` ahead of `AlwaysInline`.
- **`c4` fixed in Miri?** Check `cases.c4_eii_default_vs_override_native_and_miri.miri_default.rc` and `miri_override.rc`: `rc == 1` with `can't call foreign function _RNv...` confirms Miri's `lookup_exported_symbol` still lacks `foreign_item_symbol_aliases` support; `rc == 0` with `DEFAULT=15` and `OVERRIDE=905` confirms Miri gained `#[eii]` resolution.

### 2. Targeted Upstream Source Diffs (`< 5 s` per file)

Instead of re-auditing the compiler, diff the five decisive functions against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`rust-lang/rust`) and `0a5579eb649d3634a9c30ac873300cc2944fa070` (`rust-lang/llvm-project`):

1. `compiler/rustc_codegen_llvm/src/consts.rs` (`check_and_apply_linkage`: check whether `llvm::is_declaration(actual_global)` gates `llvm::set_linkage`).
2. `compiler/rustc_codegen_llvm/src/attributes.rs` (`inline_attr`: check whether `codegen_fn_attrs.linkage` or `contains_extern_indicator()` suppresses `AlwaysInline`).
3. `src/tools/miri/src/machine.rs` (`extern_static_pointer`: check ordering of `Linkage::ExternalWeak` fallback vs. `lookup_exported_symbol`).
4. `src/tools/miri/src/shims/foreign_items.rs` (`lookup_exported_symbol`: check whether `attrs.foreign_item_symbol_aliases` is indexed).
5. `llvm/lib/IR/Verifier.cpp` (`visitGlobalValue` / `visitFunction`) and `llvm/lib/Analysis/InlineCost.cpp` (`getAttributeBasedInliningDecision`: relative order of `Attribute::AlwaysInline` and `Callee->isInterposable`).

### 3. Re-verify the Lean `v4.34.1` Formalization (`< 10 s`)

```bash
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
  -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/LinkageInterpositionAndEiiSoundness.lean
```

Confirm exit status `0` and verify that the printed `#print axioms` block contains only `propext` and `Quot.sound` (with `inlining_sound_under_link_override_iff_non_interposable` reporting zero axioms, and zero occurrences of `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler`).
