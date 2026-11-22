# Cross-Crate Linkage, Symbol Export Thresholds, `.rmeta` MIR Encoding, and `-Z share-generics` in `rustc`

## Summary

Three cross-crate compilation mechanisms in `rustc` govern what enters `.rlib`/`.rmeta` archives, which symbols cross shared-library and static-library ABI boundaries, and whether monomorphized generics are reused across crates or emitted as crate-private copies:

1. **Two-tier `SymbolExportLevel::{C, Rust}` filtering (`symbol_export.rs`, `exported_symbols.rs`, `linker.rs`, `link.rs`):** `crate_export_threshold` assigns `SymbolExportLevel::C` to `Executable`, `StaticLib`, `ProcMacro`, and `Cdylib`, and `SymbolExportLevel::Rust` to `Rlib`, `Dylib`, and `Sdylib`. Ordering `C <= Rust` (`is_below_threshold`), `crates_export_threshold` takes the join across all crate types requested in a single compiler invocation (`any == Rust -> Rust`) so CGU codegen (`is_reachable_non_generic`) retains every symbol needed by the most permissive output artifact. Separately, per-artifact linking (`linker::exported_symbols`) re-filters against `crates_export_threshold(&[crate_type])` and emits a GNU LD version script (`{ global: ...; local: *; };`) on ELF targets. Because `symbol_export_level` assigns `SymbolExportLevel::C` if and only if `contains_extern_indicator()` holds and neither `RUSTC_STD_INTERNAL_SYMBOL` nor `EXTERNALLY_IMPLEMENTABLE_ITEM` (nor `is_compiler_builtins`, nor an Emscripten static) applies, a `cdylib` exports strictly C-boundary symbols (`4` dynamic symbols in the probe: `CUSTOM_SEC_VAL`, `c_api_no_mangle`, `custom_c_export_sym`, `weak_c_hook`) even when co-compiled with `--crate-type=rlib`, whereas a `dylib` of the exact same crate exports `1,771` dynamic symbols (including Rust-mangled functions, exported generics, and `rust_metadata_upstream_*`). Meanwhile, `rlib` archives package both `lib.rmeta` and `lib.rmeta-link` (listing Rust `.rcgu.o` members), whereas `staticlib` archives bundle upstream dependencies (`329` archive members in the probe) and strip both `lib.rmeta` and `lib.rmeta-link`.
2. **Exact decoupling between `.rmeta` MIR availability (`should_encode_mir`) and cross-crate codegen inlining (`cross_crate_inlinable`):** `should_encode_mir` returns `(encode_const, encode_opt)` where `encode_opt` for `Fn`/`AssocFn`/`Closure` is `always_encode_mir || (should_codegen && reachable && (requires_monomorphization || cross_crate_inlinable))` (further excluding always-const comptime functions in `rust-lang/rust@bdf712ee8`). By contrast, `cross_crate_inlinable` never consults `-Z always-encode-mir`: under `-C incremental=...` it returns `false` for unmarked non-generic functions regardless of body size. Both downstream monomorphization (`collector::should_codegen_locally`, checking `is_reachable_non_generic`) and the MIR inliner (`inline.rs`, checking `!is_generic && !tcx.cross_crate_inlinable`) gate on `cross_crate_inlinable`, not `is_mir_available`. Empirically on `rustc 1.98.0-nightly (14210df0e)`, adding `-Z always-encode-mir` to an incremental `-O2` build grows `lib.rmeta` from `6,768 B` to `8,608 B` (`+1,840 B`, `+27.2%`), making upstream MIR available to verification consumers such as Miri and future cross-crate MIR capture in Anneal, while downstream `-O2` (both with default flags and with `-Z inline-mir=yes -Z inline-mir-threshold=1000`, without LTO) still emits an external `invoke` to `upstream::rust_unmarked_leaf`.
3. **`-Z share-generics` instantiation reuse, `#[inline(never)]` exemption, and v0 instantiating-crate disambiguation:** Monomorphization reuse across crates requires both `GloballyShared` instantiation mode (`mono.rs`) and export via `exported_generic_symbols_provider_local` (`symbol_export.rs`). Under `-Z share-generics=yes`, upstream exports non-inlinable generics instantiated in `upstream` with external linkage and v0 backreference suffix `EB2_`, so downstream emits `declare ...EB2_` instead of duplicating code. Under `-Z share-generics=no`, unmarked generics are internalized in `upstream` (`t` in `llvm-nm`) and locally duplicated in downstream as `define internal ...ECs<crate_hash>_2ds` (which LLVM `-O2` may inline and eliminate), whereas `#[inline(never)]` generics are explicitly exempted in both `symbol_export.rs` and `partitioning.rs` and therefore remain externally shared (`declare ...EB2_`) in both modes. Factoring the instantiating crate into v0 symbol names (`symbol_mangling/src/lib.rs`, `v0.rs`) plus internalization of unshared copies jointly guarantee zero duplicate global symbol collisions and complete link resolution.

All three mechanisms are corroborated by live source inspection across `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `rust-lang/rust@bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e`, executed cross-crate probes in `support/probe_rmeta_export_and_share_generics.py` (`support/probe_results.json`), and a standalone kernel-checked Lean `v4.34.1` mechanization (`support/RmetaExportAndShareGenericsSoundness.lean`, `1,008` lines, `26` theorems including `3` constructive counterexamples, zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`).

## Applicability

This report characterizes four directly examined, durable subjects and their interaction:

- **Executed and source-audited compiler (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):** `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, targeting `x86_64-unknown-linux-gnu` (ELF, GNU/LLD linker conventions, Rust 2024 edition, `-C symbol-mangling-version=v0`). Every empirical byte count, symbol table count, LLVM IR snippet, archive listing, and linked binary execution in this report was produced by executing this exact toolchain via `support/probe_rmeta_export_and_share_generics.py`.
- **Source-audited default-branch compiler (`rust-lang/rust@bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e`):** Direct source comparison across all 15 audited compiler files against `14210df0e` establishes which invariants remain identical across the 6-month interval (`2026-05-31` to `2026-11-21`) and isolates every material upstream evolution (detailed in Findings §3.4). No binary from `bdf712ee8` was executed locally.
- **Anneal verification boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Direct source audit of `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, and `trusted/audit/TrustedBoundary.lean`. At `c131b320e`, `anneal-rustc-capture` pins `1.98.0-nightly (f8a08b688 2026-05-30)` and reaches `Callbacks::after_analysis` without yet extracting MIR bodies (`driver.rs:25, 75-84`). The `.rmeta` MIR availability findings apply directly to the external producer obligation documented in `Trusted/MirAst.lean:933-936` when extending MIR capture across crate boundaries, and the Lean proof discipline aligns with `TrustedBoundary.lean:1117-1122, 1615-1617`.
- **Lean formalization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Standalone kernel-checked mechanization (`support/RmetaExportAndShareGenericsSoundness.lean`) encoding the exact decision procedures audited in `rust-lang/rust`. The mechanized theorems establish properties of this abstract decision model; correspondence between the model and `rustc`'s Rust source is established by line-by-line source audit and empirical probe execution, not by formal extraction from `rustc`.

### Scope Conditions and Cross-Revision Summary

| Mechanism | `rust-lang/rust@14210df0e` (`2026-05-31`, source + execution) | `rust-lang/rust@bdf712ee8` (`2026-11-21`, source only) | Shared vs. Divergent |
| :--- | :--- | :--- | :--- |
| `crate_export_threshold` / `crates_export_threshold` | `symbol_export.rs:25-47` | `symbol_export.rs:31-53` | **Shared:** Identical `CrateType -> SymbolExportLevel` map and join rule. |
| `symbol_export_level` | `symbol_export.rs:520-546` | `symbol_export.rs:634-660` | **Shared:** Identical `is_extern && !std_internal && !eii` predicate and Emscripten static downgrade. |
| `should_encode_mir` | `encoder.rs:1102-1132` (`&LocalDefIdSet`, includes `InlineConst`, no `Constness::Const { always: true }` filter) | `encoder.rs:1175-1206` (`Option<&LocalDefIdSet>`, `InlineConst` merged, filters out `Constness::Const { always: true }` from `opt`) | **Evolved:** Core `(encode_const, encode_opt)` decoupling and `always_encode_mir` override are shared; `bdf712ee8` adds comptime-only exclusion. |
| `cross_crate_inlinable` | `cross_crate_inline.rs:18-104` (unconditional `f16`/`f128` return `true`) | `cross_crate_inline.rs:18-117` (adds `Constness::Const { always: true } => false`, gates `f16`/`f128` on `!target_has_reliable_f16`/`f128`) | **Evolved:** Core precedence (`extern -> kind -> Always -> intrinsic -> inline attr -> incremental -> CostChecker`) and independence from `always_encode_mir` are shared. |
| MIR inliner cross-crate gate | `inline.rs:731, 834-837` | `inline.rs:728, 831-834` | **Shared:** Both reject `!is_generic && !tcx.cross_crate_inlinable(...)` even when `is_mir_available` is `true`. |
| `exported_generic_symbols` & `partitioning` | `symbol_export.rs:231-396`, `partitioning.rs:213-214, 837-871` | `symbol_export.rs:309-480` (adds `is_offload_instance` exemption), `partitioning.rs:213-214, 875-909` | **Evolved:** Both preserve `InlineAttr::Never` sharing under `!share_generics()` and `always_export_generics` gating; `bdf712ee8` also exempts offload instances. |
| `Options::share_generics` default | `config.rs:1463-1471` (explicit `OptLevel` match: `No/Less/Size/SizeMin => true`, `More/Aggressive => false`) | `config.rs:1599-1607` (`self.optimize.objective() != OptimizationObjective::Speed`) | **Refactored:** Same default trade-off (speed-optimized builds default to `false`). |
| `RmetaLink` (`lib.rmeta-link`) | `rmeta_link.rs:14-35` (`rust_object_files: Vec<String>`) | `rmeta_link.rs:22-47` (adds `native_lib_filenames: Vec<Option<String>>` and AIX/XCOFF support) | **Evolved:** `rlib` emits `lib.rmeta` + `lib.rmeta-link` and `staticlib` strips both in both revisions. |

## Findings

### 1. Crate-Type Export Thresholds, `SymbolExportLevel::{Rust, C}`, and Two-Tier Filtering

Basis: source + execution + derived (mechanized in Lean `v4.34.1`)

#### 1.1 The Two-Point Export-Level Semilattice

In `compiler/rustc_middle/src/middle/exported_symbols.rs:12-22` (identical in `14210df0e` and `bdf712ee8`), `rustc` defines a two-point export hierarchy:

```rust
pub enum SymbolExportLevel {
    C,
    Rust,
}

impl SymbolExportLevel {
    pub fn is_below_threshold(self, threshold: SymbolExportLevel) -> bool {
        threshold == SymbolExportLevel::Rust // export everything from Rust dylibs
          || self == SymbolExportLevel::C
    }
}
```

Ordered as `C <= Rust`, `is_below_threshold(lvl, thresh)` is the reflexive, antisymmetric, transitive lattice order. In `compiler/rustc_codegen_ssa/src/back/symbol_export.rs:25-47` (`14210df0e`; lines `31-53` in `bdf712ee8`), each `CrateType` maps to a threshold, and a session's crate-type slice maps to the lattice join:

```rust
fn threshold(tcx: TyCtxt<'_>) -> SymbolExportLevel {
    crates_export_threshold(tcx.crate_types())
}

fn crate_export_threshold(crate_type: CrateType) -> SymbolExportLevel {
    match crate_type {
        CrateType::Executable | CrateType::StaticLib | CrateType::ProcMacro | CrateType::Cdylib => {
            SymbolExportLevel::C
        }
        CrateType::Rlib | CrateType::Dylib | CrateType::Sdylib => SymbolExportLevel::Rust,
    }
}

pub fn crates_export_threshold(crate_types: &[CrateType]) -> SymbolExportLevel {
    if crate_types
        .iter()
        .any(|&crate_type| crate_export_threshold(crate_type) == SymbolExportLevel::Rust)
    {
        SymbolExportLevel::Rust
    } else {
        SymbolExportLevel::C
    }
}
```

#### 1.2 Assigning `SymbolExportLevel::C` vs. `SymbolExportLevel::Rust`

For every local reachable non-generic function or static that is not `cross_crate_inlinable` and does not `requires_inline` (`symbol_export.rs:49-137` in `14210df0e`; `55-179` in `bdf712ee8`), `symbol_export_level` (`symbol_export.rs:520-546` in `14210df0e`; `634-660` in `bdf712ee8`) assigns the symbol's export tier:

```rust
fn symbol_export_level(tcx: TyCtxt<'_>, sym_def_id: DefId) -> SymbolExportLevel {
    let codegen_fn_attrs = tcx.codegen_fn_attrs(sym_def_id);
    let is_extern = codegen_fn_attrs.contains_extern_indicator();
    let std_internal =
        codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::RUSTC_STD_INTERNAL_SYMBOL);
    let eii = codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::EXTERNALLY_IMPLEMENTABLE_ITEM);

    if is_extern && !std_internal && !eii {
        let target = &tcx.sess.target.llvm_target;
        if target.contains("emscripten") {
            if let DefKind::Static { .. } = tcx.def_kind(sym_def_id) {
                return SymbolExportLevel::Rust;
            }
        }
        SymbolExportLevel::C
    } else {
        SymbolExportLevel::Rust
    }
}
```

Three additional overrides shape the full classification:
- **Extern indicator definition (`compiler/rustc_middle/src/middle/codegen_fn_attrs.rs:249-266` in `14210df0e`; `269-286` in `bdf712ee8`):** `contains_extern_indicator()` returns `false` for `FOREIGN_ITEM`, and otherwise returns `true` iff any of `NO_MANGLE`, `RUSTC_STD_INTERNAL_SYMBOL`, `EXTERNALLY_IMPLEMENTABLE_ITEM`, `symbol_name.is_some()` (`#[export_name = "..."]`), or `linkage` other than `None | Some(Linkage::Internal)` (for example, `#[linkage = "weak"]`) is set.
- **Plumbing and `compiler_builtins` suppression:** Even though `RUSTC_STD_INTERNAL_SYMBOL` and `EXTERNALLY_IMPLEMENTABLE_ITEM` return `true` from `contains_extern_indicator()` (so they receive `GloballyShared` instantiation mode and escape internalization in `partitioning.rs:921-927`), `symbol_export_level` explicitly excludes `!std_internal && !eii` so internal allocator hooks (`__rg_alloc`, `__rdl_alloc`, etc.) never leak at `SymbolExportLevel::C`. Similarly, `reachable_non_generics_provider` (`symbol_export.rs:99-108`) forces every item in a `compiler_builtins` crate to `SymbolExportLevel::Rust`, and `linker::exported_symbols_for_non_proc_macro` (`linker.rs:1838` in `14210df0e`; `1719` in `bdf712ee8`) explicitly skips `!tcx.is_compiler_builtins(cnum)` from dynamic export lists.
- **Explicit linkage and custom sections (`partitioning.rs:749-751`, `mono.rs:237-245`):** In `mono_item_linkage_and_visibility`, any item carrying an explicit `#[linkage = "..."]` short-circuits immediately and returns `(explicit_linkage, Visibility::Default)`. Thus `#[linkage = "weak"] #[unsafe(no_mangle)] pub extern "C" fn weak_c_hook` receives ELF weak global binding (`W` in `llvm-nm`) and `SymbolExportLevel::C` visibility. Attributes such as `#[unsafe(link_section = ".my_custom_sec")]` direct section placement independently of export level; when combined with `#[unsafe(no_mangle)]`, `CUSTOM_SEC_VAL` is placed in `.my_custom_sec` and exported at `SymbolExportLevel::C`.

#### 1.3 Two-Tier Export Enforcement: Why `--crate-type=cdylib --crate-type=rlib` Does Not Leak Rust Symbols into `.dynsym`

A critical architectural separation exists between CGU internalization and per-artifact linker export filtering:

1. **CGU-retention tier (`symbol_export.rs:154-162` in `14210df0e`; `180-188` in `bdf712ee8`):** `is_reachable_non_generic_provider_local` checks `info.level.is_below_threshold(threshold(tcx))`, using the **session join** `crates_export_threshold(tcx.crate_types())`. In `partitioning.rs:876-880`, items returning `true` set `*can_be_internalized = false` and receive `default_visibility(...)`, preventing `internalize_symbols` (`partitioning.rs:597`) from demoting them to `Linkage::Internal`. When `--crate-type=cdylib` is built alone, `threshold = C`, so `upstream_instantiate_u32` (level `Rust`) returns `false` and can be internalized; when `--crate-type=cdylib --crate-type=rlib` is built in one invocation, `threshold = Rust`, so `upstream_instantiate_u32` is retained globally in `.rcgu.o` for the `rlib`.
2. **Per-artifact linker-export tier (`base.rs:909-912` in `14210df0e`; `1020-1023` in `bdf712ee8`; `linker.rs:1795-1856` in `14210df0e`; `1668-1733` in `bdf712ee8`; `link.rs:2482, 2508` in `14210df0e`; `2931, 2957` in `bdf712ee8`):** `CrateInfo::new` computes a separate `exported_symbols` map entry for each requested `crate_type` by calling `linker::exported_symbols(tcx, c)`. Inside `exported_symbols_for_non_proc_macro`, `rustc` recomputes the **single-artifact threshold** `symbol_export::crates_export_threshold(&[crate_type])`, filters symbols with `info.level.is_below_threshold(export_threshold) && !tcx.is_compiler_builtins(cnum)`, and appends `rust_metadata_<crate>_<stable_crate_id>` (`exported_symbols.rs:86-92`) **only** for `Dylib | ProcMacro` (and `!is_like_wasm` in `bdf712ee8:1695-1696`), plus allocator shim symbols **only** when `export_threshold == SymbolExportLevel::Rust`. On ELF targets, `GnuLinker::export_symbols` (`linker.rs:877-890` in `14210df0e`; `869-882` in `bdf712ee8`) writes a GNU LD version script:

```ld
{
  global:
    CUSTOM_SEC_VAL;
    c_api_no_mangle;
    custom_c_export_sym;
    weak_c_hook;

  local:
    *;
};
```

That version script forces every non-listed symbol (including `upstream_instantiate_u32` retained in `.rcgu.o` for the co-built `rlib`) to local scope in the `cdylib` `.so`.

#### 1.4 Archive Metadata Packaging: `.rlib` (`lib.rmeta` + `lib.rmeta-link`) vs. `staticlib`

In `compiler/rustc_codegen_ssa/src/back/link.rs:300-355, 500-553` (`14210df0e`; `540-595, 749-802` in `bdf712ee8`) and `compiler/rustc_codegen_ssa/src/back/rmeta_link.rs`:
- **`link_rlib` with `RlibFlavor::Normal`:** Emits two synthetic metadata archive members alongside the crate's `.rcgu.o` object files:
  1. `lib.rmeta` (`METADATA_FILENAME`), wrapping compressed crate metadata in section `.rmeta` inside a target-format dummy object file (placed first on ELF for fast metadata lookup, `MetadataPosition::First`, `link.rs:339-351`).
  2. `lib.rmeta-link` (`rmeta_link::FILENAME`), wrapping serialized `RmetaLink` in section `.rmeta-link` (`link.rs:323-331, 348-350`), recording `rust_object_files: Vec<String>` (and in `bdf712ee8:29`, `native_lib_filenames: Vec<Option<String>>`) so downstream linkers and LTO can distinguish Rust CGU object files from bundled native static libraries without parsing object contents.
- **`link_staticlib`:** Calls `link_rlib` with `RlibFlavor::StaticlibBase` (which omits both `lib.rmeta` and `lib.rmeta-link`), then iterates every upstream `.rlib` dependency via `each_linked_rlib` and merges their object members into the single `.a` archive while filtering out `fname == METADATA_FILENAME || fname == rmeta_link::FILENAME` (`link.rs:534`).

#### 1.5 Empirical 4-Crate-Type + Combined-Join + Weak-Override Matrix (`rustc 1.98.0-nightly`, `14210df0e`)

Executed via `support/probe_rmeta_export_and_share_generics.py` (`support/probe_results.json`) at `-C opt-level=2 -C symbol-mangling-version=v0` on `upstream.rs`:

| Crate Type | Output Size (B) | Archive Members / Dynamic Symbols | `lib.rmeta` (B) | `lib.rmeta-link` | `c_api_no_mangle` / `custom_c_export_sym` / `CUSTOM_SEC_VAL` | `weak_c_hook` (`llvm-nm`) | `upstream_instantiate_u32` | `.my_custom_sec` | `rust_metadata_*` |
| :--- | ---: | :--- | ---: | :--- | :--- | :--- | :--- | :--- | :--- |
| `rlib` | `15,008` | `3` archive members (`lib.rmeta`, `lib.rmeta-link`, `1` `.rcgu.o`) | `6,960` | `true` (`640 B`, `.rmeta-link` sec verified) | `true` / `true` / `true` | `W weak_c_hook` | `true` (`T`, global) | `true` (in `.rcgu.o`) | N/A (in `lib.rmeta`) |
| `dylib` | `5,443,368` | `1,771` defined dynamic symbols (`-D`) | N/A | N/A | `true` / `true` / `true` | `0000000000076af0 W weak_c_hook` | `true` (`T` in `.dynsym`) | `true` | `true` (`N rust_metadata_upstream_1e512f4d352cfed9`) |
| `cdylib` | `4,324,488` | **`4` defined dynamic symbols (`-D`)** | N/A | N/A | `true` / `true` / `true` | `0000000000011930 W weak_c_hook` | **`false`** | `true` | **`false`** |
| `staticlib` | `22,048,330` | `329` archive members (bundles `std` & deps) | `null` (omitted) | `false` (omitted) | `true` / `true` / `true` | `W weak_c_hook` | **`false`** (absent; internalized/eliminated) | `true` (in `.rcgu.o`) | N/A |
| `cdylib` + `rlib` (combined) | `cdylib`: `4` dyn syms; `rlib`: `lib.rmeta` + `lib.rmeta-link` | `cdylib` strictly `4` C syms; `rlib` keeps `T upstream_instantiate_u32` | `true` (in `rlib`) | `true` (in `rlib`) | `true` / `true` / `true` | `0000000000011920 W weak_c_hook` | `cdylib`: **`false`**; `rlib`: **`true`** | `true` | `cdylib`: **`false`** |

Exact `llvm-nm -D --defined-only` output for the standalone `cdylib`:

```text
0000000000003ed8 R CUSTOM_SEC_VAL
0000000000011910 T c_api_no_mangle
0000000000011920 T custom_c_export_sym
0000000000011930 W weak_c_hook
```

Weak-symbol override verification (`weak_c_hook_strong_override_test`): linking a Rust executable that defines a strong `#[unsafe(no_mangle)] pub extern "C" fn weak_c_hook(x: u32) -> u32 { x.wrapping_add(999) }` against `libupstream.rlib` links cleanly with zero duplicate-symbol errors and prints `1004:6:0x1122334455667788` (confirming the strong definition overrides `W weak_c_hook`, while `c_api_no_mangle(5) == 6` and `CUSTOM_SEC_VAL == 0x1122334455667788` resolve to `upstream`).

---

### 2. `.rmeta` `should_encode_mir` vs. `cross_crate_inlinable` Decoupling (`-Z always-encode-mir`)

Basis: source + execution + derived (mechanized in Lean `v4.34.1`)

#### 2.1 The `(encode_const, encode_opt)` Encoding Matrix in `encoder.rs`

In `compiler/rustc_metadata/src/rmeta/encoder.rs:1102-1132` (`14210df0e`), `should_encode_mir` returns a pair `(encode_const_mir, encode_optimized_mir)` classifying every local definition:

```rust
fn should_encode_mir(
    tcx: TyCtxt<'_>,
    reachable_set: &LocalDefIdSet,
    def_id: LocalDefId,
) -> (bool, bool) {
    match tcx.def_kind(def_id) {
        DefKind::Ctor(_, _) => (true, false),
        DefKind::AnonConst { .. }
        | DefKind::InlineConst
        | DefKind::AssocConst { .. }
        | DefKind::Const { .. } => (true, false),
        DefKind::Closure if tcx.is_coroutine(def_id.to_def_id()) => (false, true),
        DefKind::SyntheticCoroutineBody => (false, true),
        DefKind::AssocFn | DefKind::Fn | DefKind::Closure => {
            let opt = tcx.sess.opts.unstable_opts.always_encode_mir
                || (tcx.sess.opts.output_types.should_codegen()
                    && reachable_set.contains(&def_id)
                    && (tcx.generics_of(def_id).requires_monomorphization(tcx)
                        || tcx.cross_crate_inlinable(def_id)));
            let is_const_fn = tcx.is_const_fn(def_id.to_def_id());
            (is_const_fn, opt)
        }
        _ => (false, false),
    }
}
```

In `rust-lang/rust@bdf712ee8` (`encoder.rs:1175-1206`), the signature tightens `reachable_set` to `Option<&LocalDefIdSet>` with `assert_eq!(reachable_set.is_some(), tcx.sess.opts.output_types.should_codegen())`, collapses `InlineConst` into `AnonConst`, and masks `opt` with `!matches!(tcx.constness(def_id), hir::Constness::Const { always: true })` because always-const comptime functions have no runtime optimized MIR.

| `DefKind` | `encode_const` (`mir_for_ctfe`) | `encode_opt` (`optimized_mir`) | Primary Rationale |
| :--- | :--- | :--- | :--- |
| `DefKind::Ctor(_, _)` | `true` | `false` | `instance_mir` uses `mir_for_ctfe` rather than `optimized_mir` for tuple-struct/variant constructors (`collector.rs:1082` exempts `DefKind::Ctor(..)` from `NoOptimizedMir`). |
| `AnonConst`, `AssocConst`, `Const` (`InlineConst` in `14210df0e`) | `true` | `false` | Constants are evaluated via CTFE even when unreachable from runtime codegen. |
| `Closure` with `is_coroutine` / `SyntheticCoroutineBody` | `false` | `true` | Downstream crates require coroutine `optimized_mir` unconditionally to compute coroutine generator layout. |
| `Fn`, `AssocFn`, non-coroutine `Closure` | `tcx.is_const_fn(def_id)` | `always_encode_mir \|\| (should_codegen && reachable && (requires_mono \|\| cross_crate_inlinable))` (masked by `!always_const` in `bdf712ee8`) | Runtime MIR is omitted by default for non-generic, non-inlinable functions to reduce `.rmeta` size and compile time; `-Z always-encode-mir` overrides `encode_opt` to `true` for consumers such as Miri. |
| All other `DefKind`s | `false` | `false` | No MIR body exists. |

#### 2.2 Decision Precedence in `cross_crate_inlinable` (`cross_crate_inline.rs`)

In `compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-104` (`14210df0e`; lines `18-117` in `bdf712ee8`), `cross_crate_inlinable(tcx, def_id)` evaluates in strict top-to-bottom priority order—and **never inspects `always_encode_mir`**:

1. **Extern indicator guard (`L22-24`):** `if codegen_fn_attrs.contains_extern_indicator() { return false; }` — `#[no_mangle]`, `#[export_name]`, and non-internal `#[linkage]` functions are globally shared and never cross-crate inlinable.
2. **`DefKind` filter (`L27-31`):** `Ctor(..) | Closure | SyntheticCoroutineBody => return true`; `Fn | AssocFn => continue`; all others `=> return false`.
3. **Unconditional threshold override (`L34-36`):** `if cross_crate_inline_threshold == InliningThreshold::Always { return true; }`. Crucially, this precedes `InlineAttr::Never` (step 6) and `incremental.is_some()` (step 9), causing even `#[inline(never)]` non-extern functions to become `cross_crate_inlinable == true` (instantiated as CGU-local `define internal fastcc` copies in downstream, while LLVM still honors the `noinline` attribute on the local copy).
4. **Intrinsic fallback bodies (`L38-44`):** `RustcIntrinsic => return true`.
5. **Comptime-only guard (`bdf712ee8` only, `L46-50`):** `hir::Constness::Const { always: true } => return false`.
6. **Source `#[inline]` attributes (`L48-52` in `14210df0e`; `L54-58` in `bdf712ee8`):** `InlineAttr::Never => return false`; `Hint | Always | Force { .. } => return true`. Note that explicit `#[inline]` returns `true` *before* both `incremental.is_some()` and `InliningThreshold::Never`.
7. **`-Z hint-mostly-unused` (`L57-59` in `14210df0e`; `L63-65` in `bdf712ee8`):** Returns `true` after `#[inline(never)]`.
8. **`f16`/`f128` signature workaround (`L61-69` in `14210df0e`; gated on `!target_has_reliable_f16`/`f128` in `bdf712ee8:67-80`):** Returns `true`.
9. **Incremental compilation guard (`L73-75` in `14210df0e`; `L85-87` in `bdf712ee8`):** `if tcx.sess.opts.incremental.is_some() { return false; }` — completely disables automatic cross-crate inlining inference for unmarked functions under `-C incremental=...`.
10. **Opt-level / MIR-inliner guard (`L80-84` in `14210df0e`; `L92-97` in `bdf712ee8`):** Returns `false` if `OptLevel::No` and neither `inline::Inline` nor `ForceInline` will run.
11. **MIR availability & `CostChecker` (`L86-104` in `14210df0e`; `L99-117` in `bdf712ee8`):** Rejects `InliningThreshold::Never`, otherwise requires `calls == 0 && resumes == 0 && landing_pads == 0 && statements <= threshold` (ignoring `StorageLive`/`StorageDead`/`Nop` and `RustcIntrinsic` calls).

#### 2.3 Why `-Z always-encode-mir` Does Not Flip Downstream Inlining (Both LLVM Codegen and MIR Inliner)

Two independent downstream gates enforce the two-bit separation between `mirEncodedInRmeta` and `crossCrateInlinable`:

1. **Monomorphization collector (`compiler/rustc_monomorphize/src/collector.rs:1047-1091` in `14210df0e`; `1083-1127` in `bdf712ee8`):**
   ```rust
   if tcx.is_reachable_non_generic(def_id) || instance.upstream_monomorphization(tcx).is_some() {
       // We can link to the item in question, no instance needed in this crate.
       return false;
   }
   ```
   For an external `def_id`, `is_reachable_non_generic_provider_extern` (`symbol_export.rs:164-166`) checks `tcx.reachable_non_generics(def_id.krate).contains_key(&def_id)`, which upstream populated iff `!tcx.cross_crate_inlinable(def_id)` (`symbol_export.rs:96`). Therefore, when `cross_crate_inlinable` is `false`, `should_codegen_locally` returns `false` *before* checking `tcx.is_mir_available(def_id)`. Downstream emits an external `call`/`invoke` declaration and never passes the upstream body to LLVM's intra-module inliner (without LTO).
2. **MIR inliner (`compiler/rustc_mir_transform/src/inline.rs:731, 832-837` in `14210df0e`; `728, 829-834` in `bdf712ee8`):**
   ```rust
   // Reachability pass defines which functions are eligible for inlining. Generally inlining
   // other functions is incorrect because they could reference symbols that aren't exported.
   let is_generic = callsite.callee.args.non_erasable_generics().next().is_some();
   if !is_generic && !tcx.cross_crate_inlinable(callsite.callee.def_id()) {
       return Err("not exported");
   }
   ```
   This check is a **link-soundness requirement**, not merely an optimization heuristic: upstream's reachability pass only exports private callees transitively referenced by functions that are generic or `cross_crate_inlinable`. If the MIR inliner inlined a non-`cross_crate_inlinable` function merely because `-Z always-encode-mir` placed its MIR in `lib.rmeta`, the inlined body in downstream could emit a call to a crate-private upstream helper that was internalized in `upstream`, causing an undefined-symbol link failure.

#### 2.4 Empirical 6-Mode `.rmeta` Matrix (`rustc 1.98.0-nightly`, `14210df0e`)

Executed via `support/probe_rmeta_export_and_share_generics.py` (`support/probe_results.json`), compiling `upstream` (`--crate-type=rlib -C opt-level=2`) and downstream `ds_mir` (`--emit=llvm-ir -C opt-level=2`, no LTO):

| Upstream Mode (+ Downstream Flags) | `lib.rmeta` Size (B) | Delta vs. `incremental_default` | `ds_call_unmarked` External Call? | `ds_call_marked_inline` External Call? | `ds_call_marked_noinline` Emission in `ds_mir.ll` |
| :--- | ---: | ---: | :--- | :--- | :--- |
| `default_non_incr` | `6,960` | `+192 B` | `false` (inlined: `mul %x, 5; add %_2, 7`) | `false` (inlined: `mul %x, 11; add %_2, 13`) | `declare @_RNv...rust_marked_noinline` (external call) |
| `threshold_never` (`-Z cross-crate-inline-threshold=never`) | `6,784` | `+16 B` | `true` (`invoke @_RNv...rust_unmarked_leaf`) | `false` (explicit `#[inline]` precedes threshold) | `declare @_RNv...rust_marked_noinline` (external call) |
| `incremental_default` (`-C incremental=<tmp>`) | `6,768` | `0 B` | `true` (`invoke @_RNv...rust_unmarked_leaf`) | `false` (explicit `#[inline]` precedes incremental) | `declare @_RNv...rust_marked_noinline` (external call) |
| `incremental_always_encode_mir` (`-C incremental=<tmp> -Z always-encode-mir`) | **`8,608`** | **`+1,840 B` (`+27.2%`)** | **`true`** (`invoke @_RNv...rust_unmarked_leaf`) | `false` (inlined) | `declare @_RNv...rust_marked_noinline` (external call) |
| `incremental_always_encode_mir` + downstream `-Z inline-mir=yes -Z inline-mir-threshold=1000` | **`8,608`** | **`+1,840 B`** | **`true`** (`invoke @_RNv...rust_unmarked_leaf`) | `false` (inlined) | `declare @_RNv...rust_marked_noinline` (external call) |
| `incremental_threshold_always` (`-C incremental=<tmp> -Z cross-crate-inline-threshold=always`) | `8,168` | `+1,400 B` | `false` (inlined: `mul %x, 5; add %_2, 7`) | `false` (inlined) | **`define internal fastcc @_RNv...rust_marked_noinline`** (local copy, still called due to LLVM `noinline`) |

Notice two sharp empirical confirmations in this table:
1. Comparing rows 3, 4, and 5 proves directly that `-Z always-encode-mir` enlarges `lib.rmeta` by `+1,840 B` (`6,768 B -> 8,608 B`) by encoding all upstream MIR bodies, yet `ds_call_unmarked` emits byte-for-byte identical external `invoke` IR even when downstream enables `-Z inline-mir=yes -Z inline-mir-threshold=1000`.
2. Row 6 empirically validates the precedence bug/quirk visible at `cross_crate_inline.rs:34` vs. `49`: `-Z cross-crate-inline-threshold=always` returns `true` *before* checking `InlineAttr::Never`, removing `rust_marked_noinline` from `reachable_non_generics` and forcing downstream to emit a CGU-private `define internal fastcc` copy of `rust_marked_noinline` instead of declaring the upstream symbol!

#### 2.5 Implications for Anneal's Trusted Boundary (`joshlf/anneal@c131b320e`)

Basis: source + derived

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
- `trusted/lean/Trusted/MirAst.lean:933-942` defines `Program { bodies : List Body, entryDefId : DefId, pointerWidthBits : Nat, mirProfileVersion : Nat, scope : VerificationScope }` and explicitly documents that *"completeness of `bodies` (ensuring every executable body and reachable callee in the crate is included) is an external producer obligation, not checked by `Trusted.MirSemantics` alone."*
- `trusted/rustc-capture/src/driver.rs:25, 75-84` pins `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"` and currently runs `AnalysisCallbacks::after_analysis` with `Compilation::Continue` without yet extracting MIR bodies (`"No compiler data or verification obligation is extracted here."`).

When Anneal extends `trusted/rustc-capture` to extract cross-crate dependency MIR bodies via `tcx.optimized_mir(callee_def_id)` / `tcx.is_mir_available(callee_def_id)` (the same interface Miri relies on), upstream `.rlib` dependencies built under Cargo's default incremental dev profile (`-C incremental=...`) or `-Z cross-crate-inline-threshold=never` will omit `optimized_mir` from `lib.rmeta` for unmarked non-generic `pub fn` items unless compiled with `-Z always-encode-mir`. Because Theorem 2a/2b and Part B of the probe prove that `-Z always-encode-mir` flips `mirEncodedInRmeta = true` **without** perturbing `cross_crate_inlinable`, `reachable_non_generics`, downstream LLVM codegen, or MIR inlining decisions, enabling `-Z always-encode-mir` on dependency builds provides complete cross-crate MIR capture for Anneal/Miri with zero perturbation to non-LTO codegen semantics (at the cost of `.rmeta` size growth, `+27.2%` on the small probe crate).

---

### 3. `-Z share-generics` Instantiation Reuse, `#[inline(never)]` Exemption, and v0 Crate Disambiguation

Basis: source + execution + derived (mechanized in Lean `v4.34.1`)

#### 3.1 Four-File Decision Pipeline (`mono.rs` -> `partitioning.rs` -> `symbol_export.rs` -> `collector.rs`)

Cross-crate reuse of a monomorphized generic `Instance` is controlled by four tightly coupled compiler passes:

1. **Default policy (`compiler/rustc_session/src/config.rs:1463-1471` in `14210df0e`; `1599-1607` in `bdf712ee8`):**
   - When `-Z share-generics` is unset, `share_generics()` returns `true` for `-O0`, `-O1`, `-Os`, `-Oz` (`OptLevel::No | Less | Size | SizeMin`) and `false` for `-O2`, `-O3` (`OptLevel::More | Aggressive`; refactored to `self.optimize.objective() != OptimizationObjective::Speed` in `bdf712ee8`).
2. **Instantiation mode selection (`compiler/rustc_middle/src/mono.rs:192-235` in both `14210df0e` and `bdf712ee8`):**
   - If `!tcx.cross_crate_inlinable(def_id) && !instance.def.requires_inline(tcx)` (`L192`): returns `InstantiationMode::GloballyShared { may_conflict: false }`. Notably, for a non-leaf generic (one making calls or exceeding `CostChecker`'s threshold), `cross_crate_inlinable` is `false`, so it receives `GloballyShared` even at `-O2`!
   - If `#[inline(never)]` on a generic function (`L223-227`): returns `InstantiationMode::GloballyShared { may_conflict: true }`.
   - Fallthrough (`L231-234`): `OptLevel::No => GloballyShared { may_conflict: true }`, whereas any optimized level (`-O1..-Oz`) returns `LocalCopy` (which creates a CGU-private `Linkage::Internal` copy, `partitioning.rs:274-279`, and therefore can **never** be exported for cross-crate sharing!). This explains a non-obvious interaction discovered empirically below: a tiny 1-line unmarked generic (`generic_tiny_leaf { x + y }`) passes `CostChecker` (`cross_crate_inlinable == true`), falls through to `LocalCopy` at `-O2`, and is therefore NOT shared at `-O2` even with `-Z share-generics=yes`, whereas at `-O0` it gets `GloballyShared` and IS shared!
3. **CGU visibility and internalization (`compiler/rustc_monomorphize/src/partitioning.rs:213-214, 597, 837-871` in `14210df0e`; `213-214, 610, 875-909` in `bdf712ee8`):**
   ```rust
   let can_export_generics = cx.tcx.local_crate_exports_generics();
   let always_export_generics = can_export_generics && cx.tcx.sess.opts.share_generics();
   ```
   Inside `mono_item_visibility`, for both upstream-defined and locally-defined generic instances:
   ```rust
   if always_export_generics
       || (can_export_generics && tcx.codegen_fn_attrs(def_id).inline == InlineAttr::Never)
   {
       // ... (and reachable if local)
       *can_be_internalized = false;
       default_visibility(tcx, def_id, true)
   } else {
       Visibility::Hidden
   }
   ```
   Items left as `can_be_internalized = true` and not referenced by another CGU in the same crate are rewritten to `data.linkage = Linkage::Internal` by `internalize_symbols` (`partitioning.rs:597`).
4. **Upstream export & downstream reuse (`symbol_export.rs:231-312, 398-453` in `14210df0e`; `309-405, 504-559` in `bdf712ee8`; `collector.rs:1070-1073`):**
   - `exported_generic_symbols_provider_local` skips any item with `data.linkage != Linkage::External` (`L290`), skips hidden items when `dynamic_linking && !only_cdylib` (`L296`), and then enforces:
     ```rust
     if !tcx.sess.opts.share_generics() {
         if tcx.codegen_fn_attrs(mono_item.def_id()).inline == InlineAttr::Never {
             // explicitly allow sharing inline(never) across crates even without share-generics
         } else {
             continue;
         }
     }
     ```
     (In `bdf712ee8:395-404`, offload instances `is_offload_instance(mono_item)` receive the same exemption alongside `InlineAttr::Never`.)
   - Every exported generic is recorded at `SymbolExportLevel::Rust` (`symbol_export.rs:327`).
   - Downstream runs `upstream_monomorphizations_provider` (`symbol_export.rs:398-453`), collecting all upstream crates' `exported_generic_symbols` and breaking multi-crate ties deterministically by selecting the upstream crate with the **smallest `stable_crate_id`** (`L441`: `if tcx.stable_crate_id(other_cnum) > tcx.stable_crate_id(cnum) { e.insert(cnum); }`).
   - Downstream `collector::should_codegen_locally` (`collector.rs:1070`) checks `instance.upstream_monomorphization(tcx).is_some()` and returns `false`, suppressing local monomorphization and emitting an external `declare`.

#### 3.2 v0 Instantiating-Crate Mangling and Collision Freedom (`symbol_mangling/src/lib.rs`, `v0.rs`)

In `compiler/rustc_symbol_mangling/src/lib.rs:126-143, 259-261` (`14210df0e`; `146-163, 290-292` in `bdf712ee8`) and `compiler/rustc_symbol_mangling/src/v0.rs:81-83` (`14210df0e`; `87-89` in `bdf712ee8`):

```rust
let avoid_cross_crate_conflicts = is_generic(instance) || is_globally_shared_function;
let instantiating_crate = avoid_cross_crate_conflicts.then(compute_instantiating_crate);
```

where `compute_instantiating_crate` evaluates `instance.upstream_monomorphization(tcx).unwrap_or(LOCAL_CRATE)`, and `v0::mangle` appends the instantiating crate's root path right after the generic argument list `E`:

```rust
if let Some(instantiating_crate) = instantiating_crate {
    p.print_def_path(instantiating_crate.as_def_id(), &[]).unwrap();
}
```

In v0 syntax:
- When `upstream` instantiates `upstream::generic_shared::<u32>`, the instantiating crate equals the defining crate (`upstream`), which was already emitted earlier in the symbol (`Cs2BnozHpfEvZ_8upstream` at byte index `2`), so v0 compresses the suffix into the backreference **`EB2_`**:
  `_RINvCs2BnozHpfEvZ_8upstream14generic_sharedmEB2_` (`m` = `u32`).
- When downstream `ds` instantiates `upstream::generic_shared::<u32>` or `<u64>` locally, the instantiating crate is `ds`, so v0 appends **`ECs4SvsyqRUztB_2ds`**:
  `_RINvCs2BnozHpfEvZ_8upstream14generic_sharedmECs4SvsyqRUztB_2ds` (`m` = `u32`),
  `_RINvCs2BnozHpfEvZ_8upstream14generic_sharedyECs4SvsyqRUztB_2ds` (`y` = `u64`).

Consequently, two sibling crates `ds1` and `ds2` that independently instantiate `upstream::generic_shared::<u64>` (even with external linkage under `share-generics=yes` or `#[inline(never)]`) always produce disjoint symbol names (`...ECs<hash1>_3ds1` vs. `...ECs<hash2>_3ds2`), while unshared copies under `share-generics=no` additionally receive `define internal` linkage.

#### 3.3 Empirical `-Z share-generics={yes, no}` Matrix Across `-O0` and `-O2` (`rustc 1.98.0-nightly`, `14210df0e`)

Executed via `support/probe_rmeta_export_and_share_generics.py` (`support/probe_results.json`):

| Build Config | Upstream `.rlib` Symbols (`llvm-nm`) | `generic_shared::<u32>` in `ds.ll` | `generic_noinline::<u32>` in `ds.ll` | `generic_shared::<u64>` in `ds.ll` | `generic_noinline::<u64>` in `ds.ll` | `generic_tiny_leaf::<u32>` in `ds.ll` | Link & Exec Output |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`-O0`, `share-generics=yes`** | `T` `generic_shared::<u32>` (`EB2_`), `T` `generic_noinline::<u32>` (`EB2_`), `T` `generic_tiny_leaf::<u32>` (`EB2_`) | **`declare ...EB2_`** (`1` ext decl) | **`declare ...EB2_`** (`1` ext decl) | `define ...ECs..._2ds` (`1` ext def) | `define ...ECs..._2ds` (`1` ext def) | **`declare ...EB2_`** (`1` ext decl) | PASS (`10075270606862590662:5324056682298506799`) |
| **`-O0`, `share-generics=no`** | `t` `generic_shared::<u32>`, **`T`** `generic_noinline::<u32>`, `t` `generic_tiny_leaf::<u32>` | **`define internal ...ECs..._2ds`** (`1` int def) | **`declare ...EB2_`** (`1` ext decl) | `define internal ...ECs..._2ds` (`1` int def) | `define ...ECs..._2ds` (`1` ext def) | `define internal ...ECs..._2ds` (`1` int def) | PASS (`10075270606862590662:5324056682298506799`) |
| **`-O2`, `share-generics=yes`** | `T` `generic_shared::<u32>` (`EB2_`), `T` `generic_noinline::<u32>` (`EB2_`) *(no `generic_tiny_leaf`)* | **`declare ...EB2_`** (`1` ext decl) | **`declare ...EB2_`** (`1` ext decl) | `define ...ECs..._2ds` (`1` ext def) | `define ...ECs..._2ds` (`1` ext def) | Inlined & eliminated (`LocalCopy`) | PASS (`10075270606862590662:5324056682298506799`) |
| **`-O2`, `share-generics=no`** | **`T`** `generic_noinline::<u32>` (`EB2_`) *(others internalized & inlined away)* | Internalized (`define internal`) & inlined away by LLVM `-O2` | **`declare ...EB2_`** (`1` ext decl) | Internalized & inlined away by LLVM `-O2` | `define ...ECs..._2ds` (`1` ext def) | Inlined & eliminated (`LocalCopy`) | PASS (`10075270606862590662:5324056682298506799`) |

This 4-way matrix demonstrates every prediction of the source audit simultaneously:
1. Unmarked `generic_shared::<u32>` flips from `declare ...EB2_` (`share-generics=yes`) to `define internal ...ECs4SvsyqRUztB_2ds` (`share-generics=no`, visible directly at `-O0` and then eliminated after intra-CGU inlining at `-O2`).
2. `#[inline(never)] generic_noinline::<u32>` remains `declare ...EB2_` in **all 4 rows**, and `generic_noinline::<u64>` remains an external `define ...ECs4SvsyqRUztB_2ds` (not `internal`) in **all 4 rows**.
3. `generic_tiny_leaf::<u32>` demonstrates the `mono.rs:192, 231-234` interaction: shared via `declare ...EB2_` under `-O0 -Z share-generics=yes`, duplicated as `define internal` under `-O0 -Z share-generics=no`, and compiled as `LocalCopy` (never exported by `upstream`) under `-O2` even when `-Z share-generics=yes` is explicitly requested.
4. All 4 configurations link into native binaries without symbol conflicts and produce identical runtime output `10075270606862590662:5324056682298506799`.

#### 3.4 Upstream Evolution Between `14210df0e` (`2026-05-31`) and `bdf712ee8` (`2026-11-21`)

Basis: source

Diffing all 15 audited files between `14210df0e` and `bdf712ee8` confirms that every architectural invariant above is preserved across the 6-month window, with five concrete upstream refinements:
1. **Comptime-only functions (`encoder.rs:1197-1198`, `cross_crate_inline.rs:46-50` in `bdf712ee8`):** Functions with `hir::Constness::Const { always: true }` now force `cross_crate_inlinable = false` and mask `should_encode_mir.1` (`encode_opt`) to `false` even when `-Z always-encode-mir` is set, because comptime-only functions never have runtime optimized MIR.
2. **Reliable `f16`/`f128` gating (`cross_crate_inline.rs:67-80` in `bdf712ee8`):** The always-inline workaround for `f16`/`f128` signatures now fires only when the target lacks `target_has_reliable_f16` / `target_has_reliable_f128`.
3. **Offload generic sharing (`symbol_export.rs:395-404` in `bdf712ee8`):** `exported_generic_symbols_provider_local` exempts `is_offload_instance(mono_item)` alongside `InlineAttr::Never` when `!share_generics()`.
4. **Static visibility plumbing guard (`partitioning.rs:789-797` in `bdf712ee8`):** `static_visibility` mirrors `mono_item_visibility` by preventing internalization of unreachable statics marked `RUSTC_STD_INTERNAL_SYMBOL | EXTERNALLY_IMPLEMENTABLE_ITEM`.
5. **Extended `RmetaLink` & `OptimizationObjective` (`rmeta_link.rs:25-47`, `config.rs:1599-1607`, `linker.rs:1695-1704` in `bdf712ee8`):** `RmetaLink` adds `native_lib_filenames: Vec<Option<String>>` and AIX/XCOFF decoding; `Options::share_generics` uses `self.optimize.objective() != OptimizationObjective::Speed`; and `linker::exported_symbols` skips `rust_metadata_*` on Wasm targets where metadata resides in a custom section.

---

### 4. Kernel-Checked Lean `v4.34.1` Soundness Formalization

Basis: derived (mechanized in Lean `v4.34.1`, `support/RmetaExportAndShareGenericsSoundness.lean`)

`support/RmetaExportAndShareGenericsSoundness.lean` (`1,008` lines, standalone `namespace RmetaExportShareGenerics`, zero external imports) formalizes all three compiler subsystems and proves `26` theorems under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with **zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `._unsafe_rec`, and zero `axiom`**. Every audited theorem depends on either no axioms (`[]`) or `[propext]` alone.

| Theorem Name | Formal Claim Established | Axiom Footprint (`#print axioms`) |
| :--- | :--- | :--- |
| `cratesExportThreshold_monotone` | Subset inclusion of crate-type lists (`∀ ct ∈ xs, ct ∈ ys`) implies `exportLe (cratesExportThreshold xs) (cratesExportThreshold ys) = true`. | `[propext]` |
| `cratesExportThreshold_append` | Join homomorphism: `cratesExportThreshold (xs ++ ys) = exportJoin (cratesExportThreshold xs) (cratesExportThreshold ys)`. | `[propext]` |
| `cdylib_exports_only_c_level_symbols` | Every symbol in `dynamicExportsForArtifact .cdylib syms` satisfies `symbolExportLevel = .c`, `containsExternIndicator = true`, and `isForeignItem = isStdInternal = isEii = isCompilerBuiltins = false`. | `[propext]` |
| `cgu_retains_every_artifact_export` | Link-closure completeness: for every `ct ∈ sessionTypes`, every symbol required by `dynamicExportsForArtifact ct syms` is retained by CGU codegen (`cguRetained sessionTypes s = true`). | `[propext]` |
| `combined_cdylib_rlib_preserves_both_contracts` | Co-compiling `[.cdylib, .rlib]` raises the CGU join to `.rust` (retaining all `rlib` exports) while keeping `dynamicExportsForArtifact .cdylib` strictly at `SymbolExportLevel.c`. | `[propext]` |
| `alwaysEncodeMir_preserves_crossCrateInlinable` | Toggling `opts.alwaysEncodeMir` leaves `crossCrateInlinable` strictly invariant for all `opts` and `item`. | `[propext]` |
| `alwaysEncodeMir_preserves_codegen_and_mir_inlining` | For every non-generic item with `crossCrateInlinable = false`, toggling `alwaysEncodeMir` preserves `inReachableNonGenerics`, `downstreamCodegensLocallyNonGeneric`, and `downstreamMirInlinerEligible = false`. | `[propext]` |
| `alwaysEncodeMir_guarantees_verification_mir_available` | For every non-comptime `fnItem`/`assocFn`/`closure`, `alwaysEncodeMir = true` guarantees `verificationConsumerMirAvailable = true` regardless of `incremental` or `inlineThreshold`. | `[propext]` |
| `crossCrateInlinable_implies_mirEncoded_when_reachable_codegen` | When `shouldCodegen = true`, `reachable = true`, `isComptimeAlwaysConst = false`, `crossCrateInlinable = true` implies `mirEncodedInRmeta = true` (ruling out the `(false, true)` `NoOptimizedMir` gap). | `[propext]` |
| `mir_inliner_gate_prevents_unexported_helper_reference` | `downstreamMirInlinerEligible = true` implies `privateHelperExported = true`, formalizing why `inline.rs` must gate on `crossCrateInlinable` rather than `mirEncodedInRmeta`. | `[propext]` |
| `inline_never_generic_always_shared_regardless_of_shareGenerics` | An upstream-instantiated `#[inline(never)]` generic always emits `externalDef` in `upstream` and `externalDecl` targeting `upId` in downstream for both `shareGenerics = true` and `false`. | `[propext]` |
| `unmarked_noninlinable_generic_flips_on_shareGenerics` | An unmarked non-inlinable upstream generic flips downstream from `externalDecl` (`upId`) under `shareGenerics = true` to `internalDef` (`dsId`) under `shareGenerics = false`. | `[propext]` |
| `shareGenerics_link_safe_and_collision_free` | Across an upstream crate `upId` and two distinct sibling downstream crates `ds1Id ≠ ds2Id`, for all `(shareGenerics, optIsNo, instantiatedUpstream, inst)`, the linked object set satisfies both `NoDuplicateGlobalSymbols` and `AllExternalDeclsResolved`. | `[propext]` |
| `ce1_exporting_rust_level_symbols_in_cdylib_leaks_unstable_abi` | **Constructive counterexample 1:** A `cdylib` exporter using threshold `.rust` leaks `upstream_instantiate_u32` (mangled Rust ABI) and `__rust_alloc` (`isStdInternal = true`), whereas `dynamicExportsForArtifact .cdylib` exports strictly the 4 C symbols. | `[]` (no axioms) |
| `ce2_assuming_always_encode_mir_enables_cross_crate_inlining_fails_under_incremental` | **Constructive counterexample 2:** Under incremental + `alwaysEncodeMir = true`, `unmarkedLeafItem` has `mirEncodedInRmeta = true` yet `crossCrateInlinable = false`, `downstreamCodegensLocallyNonGeneric = false`, and `downstreamMirInlinerEligible = false` (while `#[inline]` sibling has `crossCrateInlinable = true`). | `[propext]` |
| `ce3_emitting_external_linkage_for_unshared_downstream_generic_causes_duplicate_symbol_link_error` | **Constructive counterexample 3:** Omitting both internalization and instantiating-crate v0 disambiguation on unshared downstream generics produces a concrete witness violating `NoDuplicateGlobalSymbols` at indices `0 ≠ 1`. | `[]` (no axioms) |

## Boundaries

The following scope limits, negative-space classifications, and non-conclusions apply strictly:

- **Not examined — Non-ELF targets (Mach-O, PE/COFF/MSVC, Wasm, AIX/XCOFF, Emscripten):** All live probes executed on `x86_64-unknown-linux-gnu` (ELF with GNU LD version scripts). Although `linker.rs` (Darwin `-exported_symbols_list`, Windows `.def`, Wasm `--export`), `symbol_export.rs` (Windows x86 stdcall/fastcall/vectorcall decoration and Emscripten static downgrade), and `rmeta_link.rs` (AIX XCOFF in `bdf712ee8`) were inspected in source, none of those non-ELF backends were executed.
- **Not examined — `Sdylib`, `ProcMacro`, and LTO (`-C lto=thin|fat`):** Live probes exercised `rlib`, `dylib`, `cdylib`, `staticlib`, and combined `cdylib + rlib` without LTO. Under ThinLTO or FatLTO, downstream LLVM bitcode linking can inline non-`cross_crate_inlinable` upstream functions via embedded LLVM bitcode independently of `.rmeta` MIR encoding; the non-inlining result for `-Z always-encode-mir` applies specifically to non-LTO compilation (and the MIR inliner).
- **Not examined — Multi-CGU intra-crate internalization (`-C codegen-units > 1`) and legacy symbol mangling (`-C symbol-mangling-version=legacy`):** All probes used `-C symbol-mangling-version=v0` and single-CGU small test crates. With multiple CGUs inside a single crate, `internalize_symbols` (`partitioning.rs:560-601`) retains `Linkage::External` + `Visibility::Hidden` for symbols referenced across sibling CGUs inside the same crate (which still stay excluded from `exported_generic_symbols` on `dynamic_linking && !only_cdylib` targets due to the `data.visibility == Visibility::Hidden` check at `symbol_export.rs:296`).
- **Not examined — Execution of `rust-lang/rust@bdf712ee8`:** Findings specific to `bdf712ee8` (such as `Constness::Const { always: true }` masking in `should_encode_mir` and `is_offload_instance` in `exported_generic_symbols`) are established by `source` inspection only; no `bdf712ee8` binary was executed on this host.
- **Known not to apply — Assuming `-Z always-encode-mir` causes cross-crate inlining or replaces LTO:** Falsified by `cross_crate_inline.rs`, `collector.rs:1070`, `inline.rs:835`, Part B of `probe_results.json`, and `ce2_assuming_always_encode_mir_enables_cross_crate_inlining_fails_under_incremental`.
- **Known not to apply — Assuming `-Z share-generics=yes` shares all generic functions at `-O2`:** Falsified by `mono.rs:192, 231-234` and Part C (`O2_share_generics_yes`) of `probe_results.json`: small leaf generics whose `cross_crate_inlinable == true` (such as `generic_tiny_leaf`) get `InstantiationMode::LocalCopy` at `-O2` and are never exported by `upstream` even under `-Z share-generics=yes`.
- **Known not to apply — Assuming `#[inline(never)]` blocks `-Z cross-crate-inline-threshold=always`:** Falsified by `cross_crate_inline.rs:34` vs. `49` and `incremental_threshold_always` in `probe_results.json`: `InliningThreshold::Always` returns `true` *before* inspecting `InlineAttr::Never`, causing downstream to codegen a CGU-local `define internal fastcc` copy of `rust_marked_noinline` (LLVM still respects the `noinline` attribute on that local copy, so the call itself is not inlined, but cross-crate symbol sharing is broken).
- **Known not to apply — Treating the standalone Lean formalization as a formally extracted proof of `rustc` or an Anneal `Trusted.MirSemantics` refinement:** `support/RmetaExportAndShareGenericsSoundness.lean` is a standalone decision-model formalization (`IMPORTS: []` of `joshlf/anneal`). Its fidelity to `rustc` rests on the audited source anchors in `support/source_anchors.json` and the live empirical probe in `support/probe_results.json`, not on mechanized refinement from `rustc`'s Rust source or `Trusted.MirSemantics`.
- **Unsupported — Cross-crate MIR extraction in `joshlf/anneal@c131b320e`:** At `c131b320e`, `trusted/rustc-capture/src/driver.rs:79` explicitly records that no MIR or verification obligation is extracted yet; `anneal-rustc-capture` only verifies compiler session identity and clean `after_analysis` reachability.
- **Unknown — Exact `.rmeta` byte overhead of `-Z always-encode-mir` on large workspace crates:** The `+27.2%` (`+1,840 B`) growth measured in Part B reflects the small 11-item probe crate (`upstream.rs`) and does not establish an ecosystem-wide overhead percentage for large libraries such as `core`, `alloc`, `std`, or `zerocopy`.

## Evidence

All evidence in this report was gathered on `2026-11-22`. Source facts and empirical outputs are preserved directly in four package-owned files under `support/`:

1. **`support/source_anchors.json` (`33` source entries, `26,500 B`):** Mechanically extracted verbatim line anchors across all audited files in `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (15 files), `rust-lang/rust@bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e` (15 files), and `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (3 files).
2. **`support/probe_rmeta_export_and_share_generics.py`:** Self-contained Python 3 standard-library probe compiling `upstream.rs`, `ds_mir.rs`, `ds_share.rs`, `main_share.rs`, and `weak_override.rs` with live `rustc`, `llvm-ar`, `llvm-nm`, and `llvm-readobj` inside an ephemeral `tempfile.TemporaryDirectory()`.
3. **`support/probe_results.json` (`20,843 B`):** Complete, path-scrubbed JSON output captured on `2026-11-22` from executing `support/probe_rmeta_export_and_share_generics.py` against `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / LLVM `22.1.6` on `x86_64-unknown-linux-gnu`.
4. **`support/RmetaExportAndShareGenericsSoundness.lean` (`1,008` LOC):** Standalone Lean `v4.34.1` formalization kernel-checked with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (exit code `0`, `0` warnings, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`).

### Primary Git Source Anchors

| Repository & Pinned 40-Hex Revision | File Path | Key Symbols & Verified Line Ranges |
| :--- | :--- | :--- |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_codegen_ssa/src/back/symbol_export.rs` | `threshold` (`L25-27`), `crate_export_threshold` (`L29-36`), `crates_export_threshold` (`L38-47`), `reachable_non_generics_provider` (`L49-152`, `cross_crate_inlinable` filter `L96`), `is_reachable_non_generic_provider_local` (`L154-162`), `exported_generic_symbols_provider_local` (`L231-396`, `InlineAttr::Never` exemption `L302-311`), `upstream_monomorphizations_provider` (`L398-453`, tie-break `L441`), `symbol_export_level` (`L520-546`), `symbol_name_for_instance_in_crate` (`L549-608`). |
| `rust-lang/rust@bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e` | `compiler/rustc_codegen_ssa/src/back/symbol_export.rs` | `threshold` (`L31-33`), `crate_export_threshold` (`L35-42`), `crates_export_threshold` (`L44-53`), `is_reachable_non_generic_provider_local` (`L180-188`), `exported_generic_symbols_provider_local` (`L309-480`, `is_offload_instance` + `InlineAttr::Never` `L395-404`), `upstream_monomorphizations_provider` (`L504-559`), `symbol_export_level` (`L634-660`), `symbol_name_for_instance_in_crate` (`L663-722`). |
| `rust-lang/rust@14210df0e` & `@bdf712ee8` | `compiler/rustc_middle/src/middle/exported_symbols.rs` | `SymbolExportLevel` (`L12-15`), `is_below_threshold` (`L18-21`), `SymbolExportInfo` (`L38-46`), `metadata_symbol_name` (`L86-92`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_middle/src/middle/codegen_fn_attrs.rs` | `contains_extern_indicator` (`14210df0e:L249-266`; `bdf712ee8:L269-286`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_metadata/src/rmeta/encoder.rs` | `should_encode_mir` (`14210df0e:L1102-1132`; `bdf712ee8:L1175-1206`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_mir_transform/src/cross_crate_inline.rs` | `cross_crate_inlinable` (`14210df0e:L18-104`; `bdf712ee8:L18-117`), `CostChecker` (`14210df0e:L115-189`; `bdf712ee8:L128-202`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_mir_transform/src/inline.rs` | `is_mir_available` check (`14210df0e:L731`; `bdf712ee8:L728`), `!is_generic && !tcx.cross_crate_inlinable` gate (`14210df0e:L834-837`; `bdf712ee8:L831-834`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_monomorphize/src/collector.rs` | `should_codegen_locally` (`14210df0e:L1047-1091`; `bdf712ee8:L1083-1127`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_monomorphize/src/partitioning.rs` | `can_export_generics`/`always_export_generics` (`L213-214`), `internalize_symbols` (`14210df0e:L597`; `bdf712ee8:L610`), `mono_item_linkage_and_visibility` (`14210df0e:L742-760`; `bdf712ee8:L757-775`), `mono_item_visibility` (`14210df0e:L777-931`; `bdf712ee8:L803-969`), `default_visibility` (`14210df0e:L933-957`; `bdf712ee8:L971-995`). |
| `rust-lang/rust@14210df0e` & `@bdf712ee8` | `compiler/rustc_middle/src/mono.rs` | `MonoItem::instantiation_mode` (`L132-235`), `MonoItem::explicit_linkage` (`L237-245`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_symbol_mangling/src/lib.rs`, `src/v0.rs` | `symbol_name_provider` (`14210df0e:L126-143`; `bdf712ee8:L146-163`), `avoid_cross_crate_conflicts` (`14210df0e:L259-261`; `bdf712ee8:L290-292`), `v0::mangle` `instantiating_crate` suffix (`14210df0e:L81-83`; `bdf712ee8:L87-89`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_codegen_ssa/src/back/{link.rs,linker.rs,rmeta_link.rs}`, `src/base.rs` | `link_rlib` (`14210df0e:L300-355`; `bdf712ee8:L540-595`), `link_staticlib` (`14210df0e:L500-553`; `bdf712ee8:L749-802`), `CrateInfo::new` (`14210df0e:L906-912`; `bdf712ee8:L1017-1023`), `linker::exported_symbols` (`14210df0e:L1795-1856`; `bdf712ee8:L1668-1733`), `GnuLinker::export_symbols` (`14210df0e:L797-890`; `bdf712ee8:L789-882`), `RmetaLink` (`14210df0e:L14-35`; `bdf712ee8:L22-47`). |
| `rust-lang/rust@14210df0e` / `@bdf712ee8` | `compiler/rustc_session/src/config.rs` | `Options::share_generics` (`14210df0e:L1463-1471`; `bdf712ee8:L1599-1607`). |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, `trusted/audit/TrustedBoundary.lean` | `COMPILER_VERSION` (`driver.rs:25`), `after_analysis` (`driver.rs:75-84`), `Program` & external producer completeness obligation (`MirAst.lean:933-942`), `ensureReplayableConstant` (`TrustedBoundary.lean:1117-1122`), `forbiddenVendorCompilerRefs` (`TrustedBoundary.lean:1615-1617`). |

### Verbatim Lean Kernel Axiom Audit Output

Running Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) on `support/RmetaExportAndShareGenericsSoundness.lean` exited with code `0` and emitted:

```text
'RmetaExportShareGenerics.cratesExportThreshold_monotone' depends on axioms: [propext]
'RmetaExportShareGenerics.cratesExportThreshold_append' depends on axioms: [propext]
'RmetaExportShareGenerics.cdylib_exports_only_c_level_symbols' depends on axioms: [propext]
'RmetaExportShareGenerics.cgu_retains_every_artifact_export' depends on axioms: [propext]
'RmetaExportShareGenerics.combined_cdylib_rlib_preserves_both_contracts' depends on axioms: [propext]
'RmetaExportShareGenerics.alwaysEncodeMir_preserves_crossCrateInlinable' depends on axioms: [propext]
'RmetaExportShareGenerics.alwaysEncodeMir_preserves_codegen_and_mir_inlining' depends on axioms: [propext]
'RmetaExportShareGenerics.alwaysEncodeMir_guarantees_verification_mir_available' depends on axioms: [propext]
'RmetaExportShareGenerics.crossCrateInlinable_implies_mirEncoded_when_reachable_codegen' depends on axioms: [propext]
'RmetaExportShareGenerics.mir_inliner_gate_prevents_unexported_helper_reference' depends on axioms: [propext]
'RmetaExportShareGenerics.inline_never_generic_always_shared_regardless_of_shareGenerics' depends on axioms: [propext]
'RmetaExportShareGenerics.unmarked_noninlinable_generic_flips_on_shareGenerics' depends on axioms: [propext]
'RmetaExportShareGenerics.shareGenerics_link_safe_and_collision_free' depends on axioms: [propext]
'RmetaExportShareGenerics.ce1_exporting_rust_level_symbols_in_cdylib_leaks_unstable_abi' does not depend on any axioms
'RmetaExportShareGenerics.ce2_assuming_always_encode_mir_enables_cross_crate_inlining_fails_under_incremental' depends on axioms: [propext]
'RmetaExportShareGenerics.ce3_emitting_external_linkage_for_unshared_downstream_generic_causes_duplicate_symbol_link_error' does not depend on any axioms
```

## Revalidation

Each claim in this report can be revalidated cheaply and independently against any newer `rustc` nightly or Lean release:

1. **Rerun the live cross-crate probe (~8 seconds on Linux x86_64):**
   ```bash
   python3 support/probe_rmeta_export_and_share_generics.py --out /tmp/probe_reval.json
   ```
   Discriminating invariants to check in `/tmp/probe_reval.json`:
   - `part_a_crate_types_and_symbol_export.cdylib.defined_dyn_symbol_count == 4` and `combined_cdylib_and_rlib.cdylib_defined_dyn_symbol_count == 4` (while `combined_cdylib_and_rlib.rlib_has_upstream_instantiate_u32_global == true`).
   - `part_a_crate_types_and_symbol_export.staticlib.lib_rmeta_bytes is None` and `has_lib_rmeta_link == false`, whereas `rlib.has_lib_rmeta_link == true`.
   - `part_b_rmeta_should_encode_mir.incremental_always_encode_mir.lib_rmeta_bytes > incremental_default.lib_rmeta_bytes` while `ds_call_unmarked_calls_external == true` in both `incremental_always_encode_mir` and `incremental_always_encode_mir_plus_ds_inline_mir`.
   - `part_c_share_generics.O0_share_generics_yes.generic_shared_u32.declared_external == 1` (`EB2_`), `O0_share_generics_no.generic_shared_u32.defined_internal == 1` (`ECs..._2ds`), while `generic_noinline_u32.declared_external == 1` (`EB2_`) across all four `(O0/O2) x (yes/no)` cells, and `all_modes_runtime_identical == true`.
2. **Re-verify the Lean `v4.34.1` kernel formalization (~6 seconds):**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/RmetaExportAndShareGenericsSoundness.lean
   ```
   Confirm exit code `0` and confirm every `#print axioms` line contains at most `[propext]` (no `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, or `Lean.ofReduceNat`).
3. **Diff the minimal upstream source surface when evaluating a newer `rust-lang/rust` commit:**
   Check the exact 7 decision functions anchored in `support/source_anchors.json`:
   - `crate_export_threshold`, `crates_export_threshold`, `symbol_export_level`, and `exported_generic_symbols_provider_local` in `compiler/rustc_codegen_ssa/src/back/symbol_export.rs`;
   - `should_encode_mir` in `compiler/rustc_metadata/src/rmeta/encoder.rs`;
   - `cross_crate_inlinable` in `compiler/rustc_mir_transform/src/cross_crate_inline.rs`;
   - `inline.rs` (`!is_generic && !tcx.cross_crate_inlinable`), `collector::should_codegen_locally`, `partitioning::mono_item_visibility`, and `linker::exported_symbols_for_non_proc_macro`.
   A passing probe alone establishes behavior only for the host ELF target (`x86_64-unknown-linux-gnu`) and the tested flags; revalidating non-ELF targets (Mach-O, PE/COFF, Wasm) or LTO modes requires extending the probe to invoke those targets or `-C lto` explicitly.
