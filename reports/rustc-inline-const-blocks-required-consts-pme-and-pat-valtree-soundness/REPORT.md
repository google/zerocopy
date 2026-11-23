# `rustc` Inline `const { ... }` Blocks, `required_consts` Post-Monomorphization Errors, Promotion Lifetime Rules, and `TyKind::Pat` Valtree & `Unlistable` Soundness

## Summary

`rustc` lowers inline `const { ... }` blocks, tracks their compile-time evaluation obligations via `Body::required_consts`, decides reference promotion to `'static` vs. local stack temporaries during MIR construction (`promote_consts`), and represents pattern-constrained scalar types (`TyKind::Pat`) across CTFE valtrees, niche layout compression, LLVM `range` metadata, Miri validity checks, and pattern exhaustiveness analysis (`ConstructorSet::Unlistable`). Primary-source inspection of `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and HEAD `0259d5e9a81c6af08e40f8c204f2c0c41dca1647`), `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), combined with live `rustc 1.98.0-nightly` / `miri 0.1.0` differential probes (`support/probe_inline_const_required_consts_and_pat_valtree.py`) and a standalone kernel-checked Lean `v4.34.1` formalization (`support/InlineConstRequiredConstsAndPatValtreeSoundness.lean`, `1,256` lines, `34` major theorems, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`), establishes seven core results:

1. **Pre-DCE `required_consts` collection vs. conditional MIR removal (`required_consts.rs`, `rustc_mir_transform/src/lib.rs`, `collector.rs`).** `hir::ExprKind::ConstBlock` lowers in THIR to `ExprKind::ConstBlock { did, args }` (`thir/cx/expr.rs` L841–852 / HEAD L985–999) and in MIR to `Const::Unevaluated(UnevaluatedConst::new(def_id, args), ty)` (`as_constant.rs` L93–98), for which `Const::is_required_const()` returns `true` (`rustc_middle/src/mir/consts.rs` L271–279). Inside `mir_promoted`, `RequiredConstsVisitor::compute_required_consts` (`required_consts.rs` L1–24) traverses `traversal::reverse_postorder(&body)` **before** `PromoteTemps` and **before** `SimplifyConstCondition` / runtime DCE (`rustc_mir_transform/src/lib.rs` L465 / HEAD L479). Consequently, `if false { const { 1u32 / 0 } }` **retains** the failing inline `const` in `body.required_consts`, whereas statements syntactically following an unconditional `return` (`return 7; const { 1u32 / 0 }`) are pruned earlier by `SimplifyCfg::Initial` and compile with `rc = 0` in every mode. `Basis: source + execution`
2. **Five-mechanism PME timing asymmetry across `--emit=metadata`, `--crate-type=lib` (`-O0` vs. `-O2` vs. `-Zmir-opt-level=0`), and `--crate-type=bin`.** Compile-time `E0080` diagnostics do not depend solely on `collector.rs` (`1347–1353` / HEAD `1382–1388`):
   - *Metadata-only (`--emit=metadata`):* Skips `codegen_crate` (`passes.rs` L1309 / HEAD L1341), sets `should_encode_mir` opt-encoding to `false` for ordinary functions (`encoder.rs` L1120–1124), and `KnownPanicsLint` skips `DefKind::InlineConst` bodies (`known_panics_lint.rs` L37–45). **Both** dead (`if false`) and reachable (`mono_live_pub`) failing inline `const` blocks exit `0` under `--emit=metadata` (`cargo check`).
   - *Lazy library root deferral (`cross_crate_inlinable` + `symbol_export`):* In `--crate-type=lib -C opt-level=2`, small leaf `pub fn` items (`mono_dead_pub`) are marked `cross_crate_inlinable = true` (`cross_crate_inline.rs` L96–104), omitted from `reachable_non_generics` (`symbol_export.rs` L96 / HEAD L114), and skipped by `MonoItemCollectionStrategy::Lazy` (`collector.rs` L1659–1661) — passing cleanly (`rc = 0`) unless forced by `#[inline(never)]` (`mono_dead_noinline`, `rc = 1`) or compiled as `--crate-type=bin` (`mono_dead_bin`, `rc = 1`). Similarly, calling `gen_dead_const::<u8>()` from an unannotated small `pub fn trigger()` passes at `--crate-type=lib -C opt-level=2` (because MIR `Inline` removes the call so `trigger` becomes `cross_crate_inlinable`) while failing with `E0080` at `-O0`, `-O2 -Zmir-opt-level=0`, or with `#[inline(never)]`.
   - *Reachable `KnownPanicsLint` and promoted-fragment extraction:* Live `mono_live_const() { const { 1u32 / 0 } }` fails even at `lib_opt2` because `KnownPanicsLint::run_lint` visits reachable `START_BLOCK` constants during `optimized_mir` (triggered by `cross_crate_inlinable`) and emits `E0080` before `.discard_err()` (`known_panics_lint.rs` L248, L269). Remarkably, `let r = &const { 1u32 / 0 };` inside `if false` **also** fails with `E0080` across `-O0`, `-O2`, and `-O2 -Zmir-opt-level=0`: `promote_consts` (`promote_consts.rs` L703) lifts `&const { ... }` out of `if false` without evaluating it, producing a standalone unguarded `promoted[0]` fragment whose `body.source.def_id()` is the enclosing `Fn`, causing `KnownPanicsLint` inside `promoted_mir` (`encoder.rs` L1869, L2312; `lib.rs` L836–838) to trigger `E0080` unconditionally (contrasting with `let r = &(1u32 / 0);`, which `promote_consts` rejects as `Unpromotable` at L494–499 and compiles `rc = 0`).
   - *Uninstantiated generic `GVN` evaluation at `-C opt-level=2`:* While `KnownPanicsLint` skips generic items via `if c.has_param()` (`known_panics_lint.rs` L254) and `gen_live_param<T>() { const { 1usize / (size_of::<T>() * 0) } }` returns `rc = 0` everywhere (`TooGeneric`), uninstantiated `pub fn gen_live_nonparam<T>() -> u32 { const { 1u32 / 0 } }` passes `emit_metadata`, `lib_opt0`, and `lib_opt2 -Zmir-opt-level=0` (`rc = 0`) yet **fails with `E0080` at `lib_opt2`** because `GVN::eval_to_const` (`gvn.rs` L605 / HEAD L600) calls `eval_mir_constant` without a `has_param()` filter! `Basis: source + execution + derived`
3. **`&const { ... }` promotion vs. `InteriorMutable` and `NeedsDrop` stack temporaries (`promote_consts.rs`).** `Validator::validate_local` (`L237–283`) rejects `qualifs::NeedsDrop` while allowing `[HasDrop; 0]` (`NeedsDrop == false`); `validate_ref` (`L393–423`) rejects `BorrowKind::Shared` on `qualifs::HasMutInterior` (`Cell`) and restricts `BorrowKind::Mut` strictly to zero-length arrays (`ty::Array(_, len)` with `len == 0`). Live MIR and LLVM IR (`Suite B`) confirm `&const { 10 + 20 }`, `&[]`, `&const { [] : [HasDrop; 0] }`, `&mut []`, and `&mut const { [] }` promote (`const <fn>::promoted[0]`, lowering in LLVM `-O2` to `@alloc_...` or `inttoptr (i64 4 to ptr)` with `@promoted_empty_drop_array = unnamed_addr alias ... @promoted_const_block_empty_drop_array`), whereas `&const { Cell::new(5) }` and `&const { HasDrop(7) }` materialize on the caller's stack frame (`alloca`, `CELL=6`, `DROP_VAL=7 DROPS=1`) and trigger `E0515` if returned as `&'static`. `Basis: normative + source + execution`
4. **`TyKind::Pat` valtree base-type erasure (`valtrees.rs`).** `const_to_valtree_inner` (`valtrees.rs` L105–112 / HEAD L121–128) strips `ty::Pat(base, ..)` to `*base` when constructing `ValTree` leaves, and `valtree_to_const_value` (`L298–301` / HEAD `L317–320`) strips `ty::Pat(ty, _)` back to `ty`; `valtree_into_mplace` (`L389–465` / HEAD `L408–474`) currently has no `ty::Pat` arm because `ty::Pat` is rejected as a non-structural type in constant patterns and rejected (`E0741`) in `adt_const_params` const generics (`Suite C`). Soundness of valtree erasure therefore depends critically on CTFE validating the `Pat` range invariant **before** constructing the base valtree. `Basis: source + execution + derived`
5. **Pattern-type niche compression, LLVM `range` metadata, and Miri vs. native `-O2` UB divergence (`layout.rs`, `validity.rs`, `rustc_codegen_llvm`).** `pattern_type!(u32 is 1..=10)` (`Small`), `pattern_type!(u8 is 1..=2)` (`OneTwo`), and wrapping signed union `pattern_type!(i8 is -128..=-1 | 1..=127)` (`NonZeroI8`) yield `size_of::<Option<Small>>() == 4`, `size_of::<Option<Option<OneTwo>>>() == 1`, and `size_of::<Option<NonZeroI8>>() == 1`. At `-C opt-level=2`, LLVM emits `noundef range(i32 0, 11)` on `unwrap_opt_small` (collapsing to `ret i32 %0`) and `noundef range(i32 1, 11)` on `Small` (folding `raw >= 1 && raw <= 10` to `ret i1 true` and `raw == 0 || raw == 11` to `ret i1 false`). Native `-O2` execution of `transmute::<u32, Small>(0)` and `(11)` completes silently (`rc = 0`), whereas CTFE (`E0080`) and both Miri Stacked Borrows and `-Zmiri-tree-borrows` trap immediately with `encountered 0/11, but expected something in the range 1..=10`. `Basis: source + execution`
6. **`ConstructorSet::Unlistable` conservative exhaustiveness (`rustc_pattern_analysis/src/rustc.rs`).** `ty::Pat(_, _)` returns `ConstructorSet::Unlistable` (`rustc.rs` L423 / HEAD L425), whose `all_empty()` returns `false` (`constructor.rs` L1190–1215). Therefore `match x {}` on uninhabited `pattern_type!(u32 is 1..=0)` fails exhaustiveness with `error[E0004]: non-exhaustive patterns: type (u32) is 1..=0 is non-empty` *before* `layout_of` evaluates, whereas forcing layout via `core::mem::size_of::<EmptyPat>()` fails with `error: pattern type ranges cannot wrap: 1..=0`. Only wildcard-bearing matches (`match x { _ => 42 }`) compile (`rc = 0`). `Basis: source + execution`
7. **Mechanized Lean `v4.34.1` soundness proof & Anneal fail-closed boundary (`c131b320e`).** `support/InlineConstRequiredConstsAndPatValtreeSoundness.lean` (`1,256` lines, `34` theorems verified via `support/check_lean.py` into `support/lean_check_receipt.json`) formally establishes: (1) pre-DCE `required_consts` collection, `--emit=metadata` skipping, lazy CGU `cross_crate_inlinable` deferral vs. `#[inline(never)]`, promoted-fragment `KnownPanicsLint` surfacing out of `if false`, and `GVN` `-O2` generic traps; (2) `'static` promotion soundness (`materializeBorrow_sound`, `promoted_expectedDrops_zero`, and two sharpness counterexamples for `.rodata` mutation and skipped `Drop`); (3) valtree base-type injectivity (`patToBaseValTree_injective`, `valtree_roundtrip_iff_valid`), zero-niche `Option<Pat>` and nested `Option<Option<OneTwo>>` round-trip bijections (`decode_encode_optionZeroNiche_roundtrip`, `decode_encode_opt2OneTwo_roundtrip`), LLVM `range` soundness vs. transmute UB, and `Unlistable` conservative completeness; and (4) Anneal's fail-closed `Trusted.MirAst` boundary (`anneal_lowering_fail_closed_sound`), which rejects `TyKind::Pat`, `Const::Unevaluated`, and promoted slice/pointer constants via `FaultKind.unsupported` (`Trusted/MirAst.lean` L312–321, L504–518). `Basis: source + execution (Lean kernel) + derived`

> **Scope note.** `support/InlineConstRequiredConstsAndPatValtreeSoundness.lean` is a standalone clean-room `Init`-only operational model characterizing the invariants above; it does not verify the Rust compiler sources directly or import `joshlf/anneal`'s internal Lean modules, and abstracts unwind edges, arbitrary multi-hop cross-crate call graphs beyond 1-hop callee deferral, Stacked/Tree Borrows tag trees, and multi-field `pattern_types` aggregates. See **Boundaries**.

---

## Applicability

**Examined subjects and mutual relationships.** All five metadata subjects in `REPORT.json` jointly define the findings:

- **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (`rustc 1.98.0-nightly 2026-05-31`, `x86_64-unknown-linux-gnu`, `LLVM version: 22.1.6`, `miri 0.1.0`): serves as the primary live execution target across all `3` probe suites in `support/probe_inline_const_required_consts_and_pat_valtree.py` (producing `support/probe_output/probe_results.json`) and bundled compiler source inspection.
- **`rust-lang/rust` at `0259d5e9a81c6af08e40f8c204f2c0c41dca1647`** (`HEAD` snapshot on `2026-11-23`): audited directly across all primary compiler files (`thir/cx/expr.rs`, `thir/constant.rs`, `as_constant.rs`, `required_consts.rs`, `rustc_mir_transform/src/lib.rs`, `promote_consts.rs`, `cross_crate_inline.rs`, `known_panics_lint.rs`, `gvn.rs`, `collector.rs`, `symbol_export.rs`, `valtrees.rs`, `rustc_pattern_analysis/src/rustc.rs`, `layout.rs`, `validity.rs`) to verify continuity and record line-number and field-name evolution (notably the rename of `hir::ConstContext::Const { inline: false }` at `14210df0e` `promote_consts.rs:662` to `allow_const_fn_promotion` at `0259d5e9a` `promote_consts.rs:669–674`).
- **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`**: supplies normative Rust language rules governing inline `const { ... }` block evaluation timing, static promotion, interior mutability, and temporary lifetime extension (`src/const_eval.md`, `src/expressions/block-expr.md`, `src/destructors.md`).
- **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`**: audited at `trusted/lean/Trusted/MirAst.lean`, `trusted/audit/TrustedBoundary.lean`, and `trusted/rustc-capture/src/driver.rs` to establish which MIR/type features are admitted into verified Lean obligations versus rejected fail-closed.
- **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`** (`v4.34.1`, `x86_64-unknown-linux-gnu`, Release): kernel-verifies `support/InlineConstRequiredConstsAndPatValtreeSoundness.lean` under strict flags (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`).

**Configurations and feature gates.** All Rust and Miri probes use `--edition=2021` on `x86_64-unknown-linux-gnu` (`usize`/`u32` pointer width `64`, little-endian). Suite A compares `--emit=metadata` (`cargo check` equivalent), `--crate-type=lib -Copt-level=0`, `--crate-type=lib -Copt-level=2`, `--crate-type=lib -Copt-level=2 -Zmir-opt-level=0`, and `--crate-type=bin`. Suite B compares `-Copt-level=0`, `-Copt-level=2`, `-Zdump-mir=...`, and `cargo miri run` under default Stacked Borrows and `MIRIFLAGS=-Zmiri-tree-borrows`. Suite C requires unstable compiler-internal feature gates `#![feature(pattern_types, pattern_type_macro)]` (plus `adt_const_params` in the const-generic rejection test) and evaluates CTFE, native `-Copt-level=2` binaries, LLVM IR (`-Copt-level=0` and `-Copt-level=2`), and Miri SB/TB execution.

**Generalization.** Inline `const` lowering, `RequiredConstsVisitor`, `promote_consts`, `valtrees`, `rustc_pattern_analysis`, and `layout_of` pattern-range niche selection are target-independent within `rustc_mir_build`, `rustc_mir_transform`, `rustc_const_eval`, `rustc_ty_utils`, and `rustc_pattern_analysis`. However, cross-crate inlining thresholds (`InliningThreshold`), CGU monomorphization root visibility (`--crate-type=lib` vs. `bin` vs. `#[inline(never)]`), and LLVM `!range` attribute emission depend on crate type, optimization flags, incremental compilation settings, and LLVM backend lowering.

---

## Findings

### 1. Inline `const { ... }` Lowering and `required_consts` Collection Before DCE

`Basis: normative + source + execution`

Normatively, an inline `const { ... }` block (`rust-lang/reference@c9cc32825b`, `src/expressions/block-expr.md`, `src/const_eval.md`) executes as a standalone constant context at compile time—evaluated at most once per monomorphization, without capturing runtime locals—while sharing generic parameters in scope from the enclosing item (`rustc` stabilized inline `const` blocks in Rust 1.79.0).

In the `rustc` compiler pipeline:

1. **THIR construction (`compiler/rustc_mir_build/src/thir/cx/expr.rs`):** `hir::ExprKind::ConstBlock(anon_const)` is lowered at `14210df0e` L841–852 (`0259d5e9a` L985–999) into `thir::ExprKind::ConstBlock { did, args }` using `InlineConstArgs`, forwarding enclosing type and const generic parameters directly to the `DefKind::InlineConst` child item (`ConstBlock` does *not* duplicate generic declarations in `generics_of`; it inherits parent generics via `InlineConstArgs`).
2. **MIR constant operand creation (`compiler/rustc_mir_build/src/builder/expr/as_constant.rs` L93–98):** `thir::ExprKind::ConstBlock { did, args }` builds `mir::Const::Unevaluated(UnevaluatedConst::new(did, args), ty)` wrapped in an `Operand::Constant`. Note that unlike simple literal expressions lowered via `thir/constant.rs` (L1–116) into `Const::Val`, an inline `const { ... }` block **always** begins MIR life as `Const::Unevaluated` so generic parameters remain uninstantiated until monomorphization and any evaluation failure carries a concrete `did` span.
3. **`is_required_const` classification (`compiler/rustc_middle/src/mir/consts.rs` L271–279):** `Const::is_required_const(&self) -> bool` returns `true` for **every** `Const::Unevaluated(..)` and every non-`Value` `Const::Ty(..)`.
4. **Pre-DCE reverse-postorder collection in `mir_promoted` (`compiler/rustc_mir_transform/src/required_consts.rs` L1–24; `rustc_mir_transform/src/lib.rs` `14210df0e` L465 / `0259d5e9a` L479):** Inside `mir_promoted(tcx, def)`—right after `SimplifyCfg::Initial` (`mir_built`) and **immediately before** `PromoteTemps`—the compiler executes:

   ```rust
   // Collect `required_consts` *before* promotion, so if there are any consts being promoted
   // we still add them to the list in the outer MIR body.
   RequiredConstsVisitor::compute_required_consts(&mut body);
   ```

   `RequiredConstsVisitor::compute_required_consts` (`required_consts.rs` L9–24) walks `traversal::reverse_postorder(&body)` and appends every `ConstOperand` whose `const_.is_required_const()` holds into `body.required_consts`:

   ```rust
   pub(super) fn compute_required_consts(body: &mut Body<'tcx>) {
       let mut visitor = RequiredConstsVisitor { required_consts: Vec::new() };
       for (bb, bb_data) in traversal::reverse_postorder(&body) {
           visitor.visit_basic_block_data(bb, bb_data);
       }
       body.set_required_consts(visitor.required_consts);
   }
   ```

   Two critical structural properties follow directly from placing this visitor right after `SimplifyCfg::Initial`:
   - **Pre-DCE syntactic survival (`if false { const { 1 / 0 } }`):** In `mir_built`, `if false` compiles to a `SwitchInt(const false)` terminator with *both* successor blocks present; `SimplifyConstCondition` (`simplify_branches.rs`), `GVN`, and runtime DCE only run much later inside `run_optimization_passes` (`rustc_mir_transform/src/lib.rs` L675–773). Consequently, `traversal::reverse_postorder(&body)` visits the dead `then` block and records `const { 1u32 / 0 }` in `body.required_consts` (`requiredConsts_captures_deadBranchPreDce` in Lean). Furthermore, when MIR inlining inlines a callee into a caller, `inline.rs` (`14210df0e` L1027–1032) explicitly propagates `callee_body.required_consts()` into `caller_body.required_consts`.
   - **Pre-`mir_promoted` unconditional CFG pruning (`return 7; const { 1 / 0 }`):** By contrast, statements placed strictly sequentially *after* an unconditional `return` or diverging expression already have no CFG incoming edge in `mir_built` after `SimplifyCfg::Initial`. Because `reverse_postorder` traverses only blocks reachable from `START_BLOCK`, `after_return()` (`pub fn after_return() -> u32 { return 7; #[allow(unreachable_code)] { const { 1u32 / 0 } } }`) records zero entries in `body.required_consts` and compiles cleanly (`rc = 0`) across **all** profiles (`requiredConsts_excludes_prunedAfterReturn`, `postReturn_unreachable_never_produces_collector_err`).

---

### 2. Two-Stage Post-Monomorphization Error (PME) Timing Matrix: Metadata Checks, Lazy Root Deferral, Promoted Extraction, & `GVN`

`Basis: source + execution + derived`

Evaluating `body.required_consts` during monomorphization collection (`collector::items_of_instance`, `compiler/rustc_monomorphize/src/collector.rs` `14210df0e` L1347–1353 / `0259d5e9a` L1382–1388) explains the baseline PME rule (`--emit=metadata` skips monomorphization; full codegen evaluates it). However, live execution in Suite A (`support/probe_inline_const_required_consts_and_pat_valtree.py`) exposes **three critical additional interactions** across `KnownPanicsLint`, `cross_crate_inlinable`, `promoted_mir` metadata encoding, and `GVN` that determine whether `E0080` fires:

| Probe Case | `--emit=metadata` (`cargo check`) | `--crate-type=lib` `-Copt-level=0` | `--crate-type=lib` `-Copt-level=2` | `--crate-type=lib` `-Copt-level=2 -Zmir-opt-level=0` | `--crate-type=bin` (`-O0` / `-O2`) | Governing Mechanism |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| `mono_dead_pub` (`if false { const { 1u32 / 0 } }`) | `rc=0` | `rc=1` (`E0080`) | **`rc=0`** | **`rc=0`** | — | `lib -O2`: `cross_crate_inlinable = true` defers root (`symbol_export.rs:96`), while `KnownPanicsLint` `SwitchInt(false)` skips dead branch! |
| `mono_dead_noinline` (`#[inline(never)]`) | `rc=0` | `rc=1` (`E0080`) | `rc=1` (`E0080`) | `rc=1` (`E0080`) | — | `InlineAttr::Never` forces `cross_crate_inlinable = false` (`cross_crate_inline.rs:49`), retaining local mono root. |
| `mono_dead_bin` (`fn mono_dead_const` called by `main`) | `rc=0` | — | — | — | `rc=1` / `rc=1` | Binary entry `main` is always a local mono root (`collector.rs:1660`); `collector.rs:1347` evaluates `required_consts`. |
| `mono_live_pub` (`const { 1u32 / 0 }`) | **`rc=0`** | `rc=1` (`E0080`) | **`rc=1`** (`E0080`) | **`rc=1`** (`E0080`) | — | `--emit=metadata` skips `optimized_mir` + `codegen`; at `lib -O2`, `KnownPanicsLint` (`optimized_mir`) emits `E0080` in `START_BLOCK` before `.discard_err()`. |
| `after_return_unreachable` (`return 7; const { 1 / 0 }`) | `rc=0` | `rc=0` | `rc=0` | `rc=0` | — | Pruned by `SimplifyCfg::Initial` before `RequiredConstsVisitor`. |
| `generic_uninstantiated_dead` (`if false { 1/(size_of::<T>()*0) }`) | `rc=0` | `rc=0` | `rc=0` | `rc=0` | — | Generic function never enters `is_root`; `has_param()` + `if false` + `TooGeneric` suppress all passes. |
| `generic_uninstantiated_live_param` (`1/(size_of::<T>()*0)`) | `rc=0` | `rc=0` | `rc=0` | `rc=0` | — | `KnownPanicsLint` skips `c.has_param()`; `GVN` hits `Err(TooGeneric)` cleanly (`discard_err`). |
| `generic_uninstantiated_live_nonparam` (`<T>() { const { 1u32 / 0 } }`) | `rc=0` | `rc=0` | **`rc=1` (`E0080`)** | `rc=0` | — | `GVN::eval_to_const` (`gvn.rs:605`) calls `eval_mir_constant` **without** `has_param()`, emitting `E0080` at `-O2` even without instantiation! |
| `generic_instantiated_dead` (`trigger() { gen_dead_const::<u8>() }`) | `rc=0` | `rc=1` (`E0080`) | **`rc=0`** | **`rc=1` (`E0080`)** | — | With MIR opts (`lib -O2`), `Inline` eliminates call so `trigger` has `calls == 0` -> `cross_crate_inlinable = true` -> deferred (`rc=0`); `-Zmir-opt-level=0` leaves call (`calls == 1`), retaining local root -> `E0080`! |
| `generic_instantiated_dead_noinline` (`#[inline(never)] pub fn trigger`) | `rc=0` | `rc=1` (`E0080`) | `rc=1` (`E0080`) | `rc=1` (`E0080`) | — | `#[inline(never)]` forces `trigger` as local root across all codegen modes. |
| `promoted_dead_rvalue` (`if false { let r = &(1u32 / 0); *r }`) | `rc=0` | `rc=0` | `rc=0` | `rc=0` | — | `promote_consts.rs:494-499` rejects `Div` by zero (`Unpromotable`); runtime `Div` is not a `required_const`, and `KnownPanicsLint` skips `if false`. |
| `promoted_dead_inline_const` (`if false { let r = &const { 1u32 / 0 }; *r }`) | `rc=0` | `rc=1` (`E0080`) | **`rc=1` (`E0080`)** | **`rc=1` (`E0080`)** | — | `promote_consts` extracts `&const { ... }` into unguarded `promoted[0]`; `encoder.rs:1869,2312` runs `promoted_mir` -> `KnownPanicsLint` -> `E0080`! |

Query-stack tracing via `-Ztreat-err-as-bug=1` (`rustc 1.98.0-nightly`) directly confirms the exact compiler mechanisms explaining every non-obvious cell in that table:

1. **Why `--emit=metadata` (`cargo check`) skips even live monomorphic `const { 1 / 0 }`:**
   - `rustc_interface/src/passes.rs` (`14210df0e` L1309 / `0259d5e9a` L1341) gates `codegen_crate` (and thus `collect_and_partition_mono_items`) on `tcx.sess.opts.output_types.should_codegen()`.
   - In `rustc_metadata/src/rmeta/encoder.rs` (`14210df0e` L1120–1124, L2293), `should_encode_mir` sets `encode_opt = false` for non-`const fn` functions when `!should_codegen()`, so neither `optimized_mir` nor `promoted_mir` is demanded on the enclosing function.
   - Although `should_encode_mir` sets `(encode_const = true, false)` for `DefKind::InlineConst` (L1112), triggering `mir_for_ctfe` -> `mir_drops_elaborated_and_const_checked` -> `KnownPanicsLint`, `KnownPanicsLint::run_lint` (`known_panics_lint.rs` `14210df0e` L37–45 / `0259d5e9a` L39–43) checks `let is_fn_like = def_kind.is_fn_like(); let is_assoc_const = matches!(def_kind, DefKind::AssocConst { .. }); if !is_fn_like && !is_assoc_const { return; }`, deliberately skipping `DefKind::InlineConst` (`emitMetadata_always_skips_pme`).
2. **Why `-C opt-level=2` library builds defer unannotated dead leaf `pub fn`s (`mono_dead_pub`, `generic_instantiated_dead`):**
   - `symbol_export.rs` (`14210df0e` L96 / `0259d5e9a` L114) executes `if tcx.cross_crate_inlinable(def_id) { None } else { Some(def_id) }` inside `reachable_non_generics_provider`.
   - `cross_crate_inlinable` (`cross_crate_inline.rs` `14210df0e` L80–104 / `0259d5e9a` L95–116) returns `false` at `-O0` (when the inliner does not run), but at `-C opt-level=2` inspects `tcx.optimized_mir(def_id)` with `CostChecker` (`calls == 0 && resumes == 0 && landing_pads == 0 && statements <= threshold`).
   - Because `mono_dead_const` contains no function calls, `cross_crate_inlinable` evaluates to `true`, excluding it from `reachable_non_generics` and hence from `RootCollector::is_root` (`collector.rs` L1659–1661). Meanwhile, inspecting `optimized_mir` ran `KnownPanicsLint`, whose `SwitchInt` visitor (`known_panics_lint.rs` L758–767) folded `if false` and only visited the `else` (`0`) arm! Adding `#[inline(never)]` (`cross_crate_inline.rs` L49) or linking as a binary (`main` entry root) forces local monomorphization and surfaces `E0080`.
   - In `generic_instantiated_dead`, `trigger()` calls `gen_dead_const::<u8>()`: with MIR optimizations (`lib_opt2`), `inline::Inline` inlines `gen_dead_const::<u8>` into `trigger()`, leaving `calls == 0`, so `cross_crate_inlinable(trigger)` flips to `true` and defers both `trigger` and its inlined `required_consts` (`inline.rs` L1027–1032) to downstream callers! Disabling MIR optimizations (`-Zmir-opt-level=0`) leaves the call intact (`calls == 1`), keeping `trigger` as a local root so `collector.rs` triggers `E0080` (`instantiatedGeneric_leafCaller_inlining_deferral_matrix`).
3. **Why `if false { let r = &const { 1u32 / 0 }; *r }` (`promoted_dead_inline_const`) breaks `if false` hiding even at `lib_opt2`:**
   - In `promote_consts.rs` (`14210df0e` L703), `should_evaluate_for_promotion_checks` skips evaluating `DefKind::InlineConst` to avoid borrow-checker query cycles (`#138499`/`#150464`), so `Validator` promotes `&const { 1u32 / 0 }` into an extracted `promoted[0]` body.
   - Unlike `mono_dead_pub`, the extracted `promoted[0]` MIR body strips the surrounding `if false` branch so `const { 1u32 / 0 }` sits unconditionally in `START_BLOCK`—and retains `body.source.def_id()` pointing to the enclosing `DefKind::Fn`!
   - During metadata encoding (`encoder.rs` L1869, L2312), whenever `should_codegen()` and `cross_crate_inlinable` hold, `rustc` runs `tcx.promoted_mir(def_id)` -> `run_analysis_to_runtime_passes` (`rustc_mir_transform/src/lib.rs` L836–838) -> `KnownPanicsLint::run_lint`, firing `E0080` directly at frame #16 (`promotedMirMetadataErrors`, `promotedInlineConst_surfaces_in_libOpt2_despite_ifFalse`).
   - By contrast, `let r = &(1u32 / 0);` (`promoted_dead_rvalue`) uses runtime binary division, which `validate_rvalue` (`promote_consts.rs` L484–518) explicitly rejects (`rhs_val.to_uint(sz) == 0` returns `Err(Unpromotable)`), keeping `1u32 / 0` unpromoted inside the dead `if false` block with `rc = 0`.
4. **Why uninstantiated `pub fn gen_live_nonparam<T>() -> u32 { const { 1u32 / 0 } }` errors only at `-C opt-level=2` (`GVN`):**
   - `should_encode_mir` (`encoder.rs` L1123) demands `optimized_mir` for generic functions whenever `should_codegen()` is true. At `-O0` (`lib_opt0`) and `-O2 -Zmir-opt-level=0`, only `KnownPanicsLint` runs, skipping the operand because `c.has_param()` is `true` (`known_panics_lint.rs` L254). At `-O2` with MIR optimizations enabled, `GVN::eval_to_const` (`gvn.rs` `14210df0e` L605 / `0259d5e9a` L600) calls `self.ecx.eval_mir_constant(value, DUMMY_SP, None).discard_err()?` *without* a `has_param()` check; because `1u32 / 0` does not read `T`, CTFE executes the division by zero and emits hard error `E0080` inside `report_eval_error` before `.discard_err()` runs (`gvn_nonparam_generic_divergence`).

---

### 3. `&const { ... }` Promotion Eligibility vs. `InteriorMutable` and `NeedsDrop` Stack Lifetime (`promote_consts.rs`)

`Basis: normative + source + execution`

Promotion hoists anonymous compiler-generated temporaries backing shared references (`&expr`)—and strictly zero-length mutable slices (`&mut []`)—from per-invocation stack frames into `'static` read-only constant allocations (`promoted[k]`). In `compiler/rustc_mir_transform/src/promote_consts.rs`:

- **`Validator::validate_local` (`14210df0e` L237–283 / `0259d5e9a` L242–288):** Rejects any local temporary whose qualified MIR state satisfies `qualifs::NeedsDrop`. Because an empty array `[HasDrop; 0]` of a `Drop` element type has zero elements to drop (`needs_drop == false`), `[HasDrop; 0]` satisfies `!NeedsDrop`, whereas non-empty `HasDrop(1)` satisfies `NeedsDrop` even inside an inline `const { HasDrop(1) }` block (`emptyDropArray_zero_expected_drops`).
- **`Validator::validate_ref` (`14210df0e` L393–423 / `0259d5e9a` L402–432):**
  - For `BorrowKind::Shared`: accepts promotion only if `!qualifs::HasMutInterior` holds on the borrowed place (rejecting any non-`Freeze` `UnsafeCell` / `Cell<u32>` inside `&const { Cell::new(5) }`). Note that in an inline `const { Cell::new(5) }` block, the outer expression *by value* (`let c = const { Cell::new(5) };`) is allowed in CTFE (`CtfeValidationMode::Const { allow_immutable_unsafe_cell: true }`), producing a fresh local stack temporary each time control passes through the block, while taking `&const { Cell::new(5) }` borrows that **stack** temporary rather than promoting to `.rodata`.
  - For `BorrowKind::Mut { .. }`: rejects promotion unconditionally **except** when the dereferenced place type is `ty::Array(_, len)` resolving to length `0` (`len == 0`). Hence `&mut []` and `&mut const { [] }` of type `&'static mut [HasDrop; 0]` both promote, while `&mut const { 5u32 }` is refused and receives local temporary lifetime!
- **`Validator::validate_call` (`14210df0e` L635–683 / `0259d5e9a` L641–689):** Only calls marked `#[rustc_promotable]` are promotable inside inline `const { ... }` blocks; arbitrary `const fn` call promotion (for legacy compatibility in `const` / `static` items) explicitly excludes inline consts (`Const { inline: false }` at `14210df0e` L662, renamed `Const { allow_const_fn_promotion: true, .. }` in `0259d5e9a` L669–674).

Live empirical execution in Suite B (`support/probe_inline_const_required_consts_and_pat_valtree.py`, compiled with `rustc 1.98.0-nightly`, MIR dumped at `runtime-post-cleanup`, LLVM IR at `-O0` and `-O2`, and verified under native `-O0`/`-O2`, Miri Stacked Borrows, and Miri `-Zmiri-tree-borrows`) reproduces every branch:

| Case / Helper Function | Promoted in MIR (`runtime-post-cleanup`)? | LLVM `-O2` Representation | Return `&'static` Result (`lib`) | Runtime / Miri Semantics (`SB` & `TB`) |
| :--- | :---: | :--- | :---: | :--- |
| `&const { 10 + 20 }` (`promoted_const_block`) | **Yes**: `_3 = const promoted_const_block::promoted[0];` | `ret ptr @alloc_0e3505805f4905816c1bd644811a7869` | Allowed (`rc=0`) | `PROM=30` |
| `&[]` on `[HasDrop; 0]` (`promoted_empty_drop_array`) | **Yes**: `_3 = const promoted_empty_drop_array::promoted[0];` | `@promoted_empty_drop_array = unnamed_addr alias ptr (), ptr @promoted_const_block_empty_drop_array` | Allowed (`rc=0`) | `EMPTY=0`, 0 drops |
| `&const { [] }` on `[HasDrop; 0]` (`promoted_const_block_empty_drop_array`) | **Yes**: `_3 = const promoted_const_block_empty_drop_array::promoted[0];` | `ret ptr inttoptr (i64 4 to ptr)` | Allowed (`rc=0`) | `EMPTY_C=0`, 0 drops |
| `&mut []` / `&mut const { [] }` on `&'static mut [HasDrop; 0]` | **Yes** (`0`-length array exception) | Zero-sized dangling aligned static ptr | Allowed (`rc=0`) | Zero writable bytes in `.rodata` (`mut_borrow_promotion_iff_zero_len_array`) |
| `&const { Cell::new(5) }` (`non_promoted_cell_const_block`) | **No**: `_3 = const ...::{constant#0}; _2 = &_3;` | `-O0`: `%_2 = alloca [4 x i8], align 4; store i32 5, ptr %_2` | **`E0515`** | `CELL=6` (fresh local stack temporary mutated safely) |
| `&const { HasDrop(7) }` (`non_promoted_drop_const_block`) | **No**: stack temporary `_8` dropped at block exit | `-O2`: `atomicrmw add ptr ...DROPS, i64 1 monotonic` | **`E0515`** (also for `&HasDrop(1)`) | `DROP_VAL=7 DROPS=1` (drop glue runs on scope exit) |
| `&mut const { 5u32 }` | **No** (non-ZST `BorrowKind::Mut`) | Stack temporary `alloca` | **`E0515`** | Non-zero mutable ref stays local |

Notice two striking empirical confirmations from LLVM IR:
- At `-C opt-level=2`, LLVM emits `@promoted_empty_drop_array = unnamed_addr alias ptr (), ptr @promoted_const_block_empty_drop_array` targeting `ret ptr inttoptr (i64 4 to ptr)`, directly establishing that `&[]` and `&const { [] }` at `[HasDrop; 0]` are codegen-identical ZST aligned non-null static pointers.
- Promoting either `&const { Cell::new(5) }` or `&const { HasDrop(7) }` would violate soundness: Lean theorems `ce_promote_interiorMut_breaks_rodata_soundness` and `ce_promote_needsDrop_loses_destructor` prove that bypassing `!HasMutInterior` permits mutation of read-only interned `.rodata` (`UB`), while bypassing `!NeedsDrop` reduces observed destructors from `1` to `0`, and `materializeBorrow_sound` proves that the compiler's conjunction holds universally across arbitrary nested arrays `[T; N]`.

---

### 4. `TyKind::Pat` (`pattern_types`) Valtree Base-Type Stripping & Non-Structural Rejection (`valtrees.rs`)

`Basis: source + execution + derived`

In `compiler/rustc_const_eval/src/const_eval/valtrees.rs`:

1. **`const_to_valtree_inner` (`14210df0e` L105–112 / `0259d5e9a` L121–128):** When lowering an evaluated typed `MPlaceTy` into a structural `ValTree`, the `ty::Pat(base, ..)` arm replaces the place's pattern-constrained layout with its underlying base layout without recording any pattern predicate inside the `ValTree`:

   ```rust
   ty::Pat(base, ..) => {
       let mut place = place.clone();
       place.layout = ecx.layout_of(*base).unwrap();
       ensure_sufficient_stack(|| const_to_valtree_inner(ecx, &place, num_nodes))
   }
   ```

2. **`valtree_to_const_value` (`14210df0e` L298–301 / `0259d5e9a` L317–320):** When re-converting a `ValTree` back into a `mir::ConstValue`, the `ty::Pat(ty, _)` arm strips the outer `ty::Pat` back to `ty` via `ty::Value { valtree: cv.valtree, ty }` and recurses on the underlying base scalar type:

   ```rust
   ty::Pat(ty, _) => {
       let cv = ty::Value { valtree: cv.valtree, ty };
       valtree_to_const_value(tcx, typing_env, cv)
   }
   ```

3. **`valtree_into_mplace` (`14210df0e` L389–465 / `0259d5e9a` L408–474):** Does **not** contain a `ty::Pat` match arm at all.

Because valtrees are **erased structural trees over base scalar bits** (`patToBaseValTree`), forgetting `ty::Pat` when converting valid pattern inhabitants to valtrees is **injective** (`patToBaseValTree_injective`: distinct valid inhabitants of `pattern_type!(u32 is 1..=10)` never collide under erasure). Crucially, however, `reconstructPatFromBaseValTree` is **partial** on raw base valtrees: `ValTree.leaf 0` and `ValTree.leaf 11` are valid `u32` valtrees yet invalid for `Small = pattern_type!(u32 is 1..=10)` (`base_valtree_zero_invalid_for_smallU32`, `base_valtree_eleven_invalid_for_smallU32`). Therefore:

- Any caller of `const_to_valtree` on `ty::Pat` **must** already have enforced `ty::Pat` validity during CTFE (`const_validate_mplace`) *before* erasure (`valtree_roundtrip_iff_valid`).
- Currently (`rustc 1.98.0-nightly` Suite C), both direct typeck/HIR pathways that inspect structural valtrees for equality reject `ty::Pat`:
  - `match x { C1 => 1, _ => 0 }` on `pub type Small = pattern_type!(u32 is 1..=10)` fails with `error: constant of non-structural type (u32) is 1..=10 in a pattern` (missing `StructuralPartialEq`).
  - `#![feature(adt_const_params)]` `pub struct K<const X: Small>;` fails with `error[E0741]: (u32) is 1..=10 can't be used as a const parameter type` (blocking `ty::Pat` from entering `valtree_into_mplace`).

---

### 5. `TyKind::Pat` Niche Layout, LLVM `!range` Optimization, CTFE `E0080`, and Miri vs. Native Divergence

`Basis: source + execution + derived`

In `compiler/rustc_ty_utils/src/layout.rs` (`14210df0e` L215–380 / `0259d5e9a` L243–408), `rustc` lowers `TyKind::Pat(base, pat)` over scalar integer bases by intersecting pattern range constraints directly into `Scalar::Initialized { valid_range, .. }` (`WrappingRange`) and exposing unused bit patterns via `largest_niche`:

- For `Small = pattern_type!(u32 is 1..=10)`, `valid_range = [1, 10]` (4 bytes), freeing `{0, 11..=u32::MAX}` so `Option<Small>` uses niche tag `0` and compacts cleanly to **`size_of::<Option<Small>>() == 4`** (`Suite C`: `SZ=4 OPT_SZ=4`, `OK=5`, `NONE=0`).
- For `OneTwo = pattern_type!(u8 is 1..=2)`, `valid_range = [1, 2]` leaves `254` niche values (`0` and `3..=255`), so **both** single and doubly nested options stay **`1` byte**: `size_of::<Option<OneTwo>>() == 1` (`OPT_OT=1`) and `size_of::<Option<Option<OneTwo>>>() == 1` (`OPT2_OT=1`, mechanized cleanly by `decode_encode_opt2OneTwo_roundtrip` and `encodeOpt2OneTwo_fits_u8`).
- For signed disjunction `NonZeroI8 = pattern_type!(i8 is -128..=-1 | 1..=127)`, two's-complement bit layout turns `-128..=-1 | 1..=127` into the contiguous unsigned wrapping bit range `[1, 255]` mod `256` (`valid_range = 1..=255`), leaving bit pattern `0` free as the niche (`OPT_NZI8=1`; mechanized by `option_small_and_nzi8_sound`). Note that `const_validate_mplace` formats errors on `i8` pattern types via the underlying signed bounds: `transmute::<i8, NonZeroI8>(0)` fails CTFE with `error[E0080]: constructing invalid value of type (i8) is (i8::MIN..=-1 | 1..): encountered 0, but expected something greater or equal to 1` (`ctfe_const_bad_or_zero`).
- Conversely, an inverted single scalar range `EmptyPat = pattern_type!(u32 is 1..=0)` cannot wrap inside a single-range `Pat` and aborts `layout_of` with `error: pattern type ranges cannot wrap: 1..=0` (`layout_empty_pat_size_of_wrap_error`).

**Backend LLVM `range` metadata vs. UB divergence (`rustc_codegen_llvm/src/{abi.rs:478, builder.rs:701}`, `validity.rs` `14210df0e` L1501–1548 / `0259d5e9a` L1499–1546):**

- Comparing Suite C LLVM IR at `-Copt-level=0` vs. `-Copt-level=2`:
  - At `-O0`, `unwrap_opt_small` explicitly branches on `%2 = icmp eq i32 %1, 0` (the niche discriminant for `None`), while `range_check_after_small` and `impossible_check_after_small` materialize full integer range comparisons.
  - At `-O2`, LLVM receives ABI/load `range` attributes (`noundef range(i32 0, 11)` on `Option<Small>`, `noundef range(i32 1, 11)` on `Small`, where LLVM `range(lo, hi)` is half-open `[lo, hi)`!) and collapses all three functions into single-instruction returns:
    - `define dso_local noundef range(i32 0, 11) i32 @unwrap_opt_small(i32 noundef returned range(i32 0, 11) %0)` -> `ret i32 %0` (`llvm_range_metadata_sound_for_valid_small`)
    - `define dso_local noundef zeroext i1 @range_check_after_small(i32 noundef range(i32 1, 11) %v)` -> `ret i1 true`
    - `define dso_local noundef zeroext i1 @impossible_check_after_small(i32 noundef range(i32 1, 11) %v)` -> `ret i1 false`
- Executing `let bad: Small = unsafe { core::mem::transmute(0u32) }` (and `11u32`) reveals the exact **CTFE/Miri vs. native `-O2` split**:
  - **CTFE:** Rejects `0u32`, `11u32`, and `0i8` with hard compile error `E0080: constructing invalid value of type ...`.
  - **Miri (both default Stacked Borrows and `-Zmiri-tree-borrows`):** Traps immediately at the `transmute` assignment (`rc = 1`: `error: Undefined Behavior: constructing invalid value of type (u32) is 1..=10: encountered 0, but expected something in the range 1..=10` / `encountered 11`).
  - **Native `-O2` (`./bin_o2 zero` and `./bin_o2 eleven`):** Exits silently with **`rc = 0`** and prints `IN_RANGE=true IMPOSSIBLE=false` (computed on `ok = 5`), while passing an invalid `0` or `11` violates LLVM's `noundef range(i32 1, 11)` poison/UB contract (`ce_transmute_zero_eleven_ub_and_llvm_divergence`).

---

### 6. `ConstructorSet::Unlistable` Pattern Exhaustiveness (`rustc_pattern_analysis/src/rustc.rs`)

`Basis: source + execution`

In `compiler/rustc_pattern_analysis/src/rustc.rs` (`14210df0e` L423 / `0259d5e9a` L425), `RustcPatCtxt::ctors_for_ty` maps `ty::Pat(_, _)` directly to **`ConstructorSet::Unlistable`**, rather than computing `ConstructorSet::Integers { range, .. }` from the pattern bounds. In `compiler/rustc_pattern_analysis/src/constructor.rs` (`14210df0e` L1190–1215), `all_empty()` returns `false` on `ConstructorSet::Unlistable`.

This causes two observable front-end behaviors confirmed in Suite C:

1. **Exhaustiveness rejects empty match on uninhabited `pattern_type!(u32 is 1..=0)` *before* layout checks wrap errors:** `pub type EmptyPat = pattern_type!(u32 is 1..=0); pub fn m(x: EmptyPat) -> u32 { match x {} }` fails in HAIR pattern checking with **`error[E0004]: non-exhaustive patterns: type (u32) is 1..=0 is non-empty`**, never emitting `pattern type ranges cannot wrap: 1..=0` (`emptyPat_triggers_e0004_before_layout_error`). Only when layout is explicitly demanded (e.g., `core::mem::size_of::<EmptyPat>()`) does `rustc_ty_utils::layout` emit `pattern type ranges cannot wrap: 1..=0`.
2. **Only wildcard / catch-all matches pass `match` on `ty::Pat` (`unlistable_rejects_empty_match_and_literal_only_matches`, `unlistable_accepts_wildcard_and_covers_all`):** `match x { _ => 42 }` compiles with `rc = 0`, whereas matches without a catch-all arm fail `E0004` conservatively (sound over-approximation relative to finite constructor analysis `finite_exhaustive_iff_all_covered`).

---

### 7. Lean `v4.34.1` Mechanization and Anneal `Trusted.MirAst` Fail-Closed Boundary (`joshlf/anneal@c131b320e`)

`Basis: source + execution (Lean kernel) + derived`

#### Lean `v4.34.1` Formalization Map (`support/InlineConstRequiredConstsAndPatValtreeSoundness.lean`)

Verified standalone against `Init` only under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`support/check_lean.py`, receipt `support/lean_check_receipt.json`: `1,256` lines, `700` namespace constants, `0` bare/partial/unsafe definitions, `0` `deriving`, `0` `._unsafe_rec` constants across `env.constants.map₁ ++ env.constants.map₂`, `0` `sorry`/`omega`/`bv_decide`/`native_decide`/`Classical.choice`/`axiom`/`opaque`, wall clock `6.23s`, max RSS `520,532 KiB`):

| Domain | Key Formal Definitions | Key Kernel-Checked Theorems & Axiom Footprints |
| :--- | :--- | :--- |
| **Part 1: Pre-DCE `required_consts` & PME timing** | `BlockStage`, `InlineConstSite`, `BuildProfile`, `computeRequiredConsts`, `crossCrateInlinable`, `isLocalMonoRoot`, `knownPanicsErrors`, `promotedMirMetadataErrors`, `gvnGenericErrors`, `reportCratePmeErrors` | `requiredConsts_captures_deadBranchPreDce`, `requiredConsts_excludes_prunedAfterReturn`, `emitMetadata_always_skips_pme`, `postReturn_unreachable_never_produces_collector_err`, `monoRoot_deadConst_triggers_pme_at_codegen`, `uninstantiated_paramGeneric_zero_errors`, `promotedInlineConst_surfaces_in_libOpt2_despite_ifFalse`, `gvn_nonparam_generic_divergence` (`[propext]`); `instantiatedGeneric_leafCaller_inlining_deferral_matrix` (`[propext, Quot.sound]`) |
| **Part 2: Promotion eligibility vs. `Cell` / `Drop`** | `PromType` (`needsDrop`, `hasMutInterior`, `isZeroLenArray`), `isPromotableBorrow`, `checkReturnStaticRef`, `materializeBorrow`, `soundMemoryModel` | `promoted_expectedDrops_zero`, `ce_promote_interiorMut_breaks_rodata_soundness`, `ce_promote_needsDrop_loses_destructor` (`[propext]`); `emptyDropArray_zero_expected_drops`, `zero_len_array_promotable_both_shared_and_mut`, `cell_and_drop_non_zero_fail_e0515`, `materializeBorrow_sound` (`[propext, Quot.sound]`) |
| **Part 3: `TyKind::Pat` valtrees, niches, `!range`, `Unlistable`** | `PatScalarSpec`, `PatVal`, `mkPatValOpt` (constructive dependent option builder), `reconstructPatFromBaseValTree`, `encodeOptionZeroNiche`/`decodeOptionZeroNiche`, `encodeOpt2OneTwo`/`decodeOpt2OneTwo`, `ConstructorSet`, `patternAnalysisExhaustive` | `patToBaseValTree_injective`, `valtree_roundtrip_iff_valid`, `base_valtree_zero_invalid_for_smallU32`, `base_valtree_eleven_invalid_for_smallU32`, `ce_transmute_zero_eleven_ub_and_llvm_divergence` (**0 axioms**: `does not depend on any axioms`); `encodeOptionZeroNiche_lt_modulus`, `encodeOptionZeroNiche_injective`, `decode_encode_optionZeroNiche_roundtrip`, `encodeOpt2OneTwo_fits_u8`, `decode_encode_opt2OneTwo_roundtrip`, `option_small_and_nzi8_sound`, `unlistable_rejects_empty_match_and_literal_only_matches`, `unlistable_accepts_wildcard_and_covers_all`, `emptyPat_triggers_e0004_before_layout_error`, `finite_exhaustive_iff_all_covered` (`[propext]`); `llvm_range_metadata_sound_for_valid_small` (`[propext, Quot.sound]`) |
| **Part 4: Cross-feature Anneal admission boundary** | `RustMirFeature`, `lowerFeatureToAnneal`, `featureSemanticsPreserved` | `anneal_lowering_fail_closed_sound`, `anneal_blocks_pat_valtree_and_unevaluated_const` (`[propext]`) |

#### Consequences for `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Inspection of `trusted/lean/Trusted/MirAst.lean` (`MirTy` L312–321, `ConstLit` L504–518), `trusted/rustc-capture/src/driver.rs` (L1–152), and `trusted/audit/TrustedBoundary.lean` confirms Anneal's MIR ingestion architecture **currently fails closed** across all three problem areas:

1. **Inline `const { ... }` / `Const::Unevaluated` & PME coverage:** Anneal's `MirAst.ConstLit` models only `ConstLit.scalar` and `ConstLit.zeroSized`. Unreduced `Const::Unevaluated`, `Const::Ty`, and `promoted[k]` indirect allocations reject cleanly to `.unsupported` (`FaultKind.unsupported`), so verification never silently passes code containing unmonomorphized generic `const` blocks—while running Anneal verification requires monomorphic/concrete MIR extraction (`rustc_driver`), escaping the `--emit=metadata` blind spot only for the captured concrete MIR bodies.
2. **Promoted `&const { ... }` pointers and `&'static [T; 0]`:** Because `Trusted.MirAst` does not yet admit promoted `GlobalAlloc::Memory` pointer constants or slice metadata in `ConstLit`, both `&const { 10 + 20 }` and `&const { [] : [HasDrop; 0] }` fail closed to `.unsupported` unless eliminated earlier by MIR constant folding into plain scalars (`erasedScalarAfterOpt`). Any future extension admitting promoted `'static` constants must preserve the `!HasMutInterior` and `!NeedsDrop || ZeroLengthArray` invariants (`materializeBorrow_sound`).
3. **`TyKind::Pat` (`pattern_types`):** `MirTy` admits fixed scalar/reference/aggregate/array types and rejects `TyKind::Pat` as unsupported (`anneal_blocks_pat_valtree_and_unevaluated_const`). If future Anneal extensions ingest `TyKind::Pat` MIR or valtrees, soundness requires importing `PatScalarSpec.inRange` validity assumptions into both value invariants (matching LLVM `range` assumptions) and valtree reconstruction (`valtree_roundtrip_iff_valid`), rather than trusting valtree erasure (`ty::Pat -> base`) alone.

---

## Boundaries

1. **Multi-hop transitive inlining chains and `-C lto=fat` across external crates (`not examined`).**
   - *Evidence status:* Suite A tests single-crate binaries and 1-hop `trigger -> gen_dead_const<u8>` call chains (`--crate-type=lib` / `--crate-type=bin`); multi-crate `extern crate` downstream instantiation of `cross_crate_inlinable` library functions (where a downstream crate monomorphizes a `pub fn` deferred by `-C opt-level=2`) and fat LTO were not executed.
2. **Unstable `generic_const_exprs` / `min_generic_const_args` interactions with inline `const` and `Const::Ty` (`not examined` / `unknown`).**
   - *Evidence status:* Probes and source review focused on stable inline `const { ... }` (`DefKind::InlineConst`, `Const::Unevaluated`) and `#![feature(pattern_types, pattern_type_macro)]`. Experimental `Const::Ty` / `min_generic_const_args` valtree normalization paths referenced in `FIXME(mgca)` comments (`promote_consts.rs` L691, `collector.rs` L1568) were not executed.
3. **Non-scalar `TyKind::Pat` variants (`pattern_type!` on enums, structs, or char/float once generalized) (`unsupported`).**
   - *Evidence status:* `rustc_ty_utils/src/layout.rs` and `rustc_const_eval/src/const_eval/valtrees.rs` only lower scalar integer range patterns (`Scalar::Initialized { valid_range, .. }`); pattern types over aggregates or non-scalar uninhabited types are rejected or unimplemented in the examined compiler revisions.
4. **Clean-room abstraction scope in `InlineConstRequiredConstsAndPatValtreeSoundness.lean` (`known not to apply` beyond modeled transitions).**
   - *Evidence status:* The Lean formalization mechanizes pre-DCE `required_consts` collection, single-hop root/caller deferral, promotion eligibility qualifiers (`HasMutInterior`, `NeedsDrop`, `[T; 0]`), scalar two's-complement bit-pattern `Pat` valtree erasure, single/nested `Option` niche bijections, LLVM `range` invariant soundness, `Unlistable` wildcard rules, and fail-closed Anneal lowering. It does **not** verify `rustc`'s Rust source code directly, does not prove preservation of unwind/drop-order edges under exceptions, and does not model Stacked/Tree Borrows pointer retagging trees.
5. **Exact `[Cell<u32>; 0]` zero-length `HasMutInterior` behavior in `promote_consts.rs` (`not examined` by live probe).**
   - *Evidence status:* Live Suite B probes tested `&[]` and `&const { [] }` for `[HasDrop; 0]` (testing `NeedsDrop` exception and `&mut []` `validate_ref` carve-out) and `&const { Cell::new(5) }` (size 4). Whether `&[Cell::new(0); 0]` is treated equivalently by `qualifs::HasMutInterior` at `promote_consts.rs:413` was not empirically compiled in Suite B.

---

## Evidence

### Preserved Package Artifacts

| Artifact | Purpose & Measured Metrics | Verification |
| :--- | :--- | :--- |
| `support/probe_inline_const_required_consts_and_pat_valtree.py` | Standalone Python 3 harness running Suite A (`12` PME timing cases × `3–4` profiles = `47` `rustc` invocations), Suite B (`positive_and_miri` at `-O0`/`-O2`/MIR dumps/LLVM IR/Miri SB & TB + `6` lifetime matrix tests), and Suite C (`native -O2` × `3` inputs, LLVM IR `-O0`/`-O2`, Miri SB & TB × `3` inputs = `6` runs, plus `9` compile-time CTFE/layout/exhaustiveness cases). | Executed live on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` + `miri 0.1.0`; output captured in `support/probe_output/probe_results.json` (`68,469` bytes). |
| `support/probe_output/probe_results.json` | Machine-readable captured exit codes, redacted diagnostics, MIR excerpts (`runtime-post-cleanup`, `runtime-optimized`), and LLVM IR (`-O0`, `-O2`). | `100%` of expected Suite B and Suite C LLVM IR blocks verified non-empty; sanitized against environment strings. |
| `support/InlineConstRequiredConstsAndPatValtreeSoundness.lean` | Standalone `Init`-only Lean `v4.34.1` mechanization (`1,256` lines, every definition `noncomputable def`, `0` `deriving`, `0` imports). | Kernel type-checked via `support/check_lean.py` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. |
| `support/check_lean.py` | Standalone hygiene, kernel compiler, `env.constants.map₁ ++ env.constants.map₂` walk, and 34-theorem `#print axioms` auditor running inside `tempfile.TemporaryDirectory`. | Outputs `support/lean_check_receipt.json` and exits `0` (`all_checks_passed: true`). |
| `support/lean_check_receipt.json` | Cryptographic and kernel audit receipt (`sha256: 69a87b9d2897aaf99e93b8db43a561781936f29d3fe1fe743cd23288a7840abd`, `line_count: 1256`, `namespace_constants: 700`, `is_unsafe: 0`, `is_partial: 0`, `unsafe_rec_helpers: 0`, `user_axioms: 0`, `forbidden_axioms_present: false`, `wall_clock_sec: 6.2316`, `max_rss_kib: 520532`). | Directly generated by executing `python3 support/check_lean.py`. |

### Primary Source Locations Audited (`rust-lang/rust`, `rust-lang/reference`, `joshlf/anneal`)

Observed on `2026-11-23`:

| Repository / Commit | File & Symbol / Line Range | Verified Role |
| :--- | :--- | :--- |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_mir_build/src/thir/cx/expr.rs` (L841–852 / L985–999) | Lowers `hir::ExprKind::ConstBlock` using `InlineConstArgs` to `thir::ExprKind::ConstBlock { did, args }`. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_mir_build/src/builder/expr/as_constant.rs` (L93–98); `compiler/rustc_mir_build/src/thir/constant.rs` (L1–116) | Lowers `ConstBlock` to `mir::Const::Unevaluated`; pure literals lower via `thir/constant.rs`. |
| `rust-lang/rust` (`14210df0e`) | `compiler/rustc_middle/src/mir/consts.rs` (L271–279) | `Const::is_required_const()` returns `true` for `Const::Unevaluated` and non-`Value` `Const::Ty`. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_mir_transform/src/required_consts.rs` (L1–24); `rustc_mir_transform/src/lib.rs` (L465 / L479) | `RequiredConstsVisitor::compute_required_consts` collects `required_consts` in reverse postorder *before* `PromoteTemps` and *before* `SimplifyConstCondition` / DCE. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_mir_transform/src/known_panics_lint.rs` (L29–45, L254, L269, L758–767 / L31–43, L253, L268, L757) | Skips `DefKind::InlineConst` and `c.has_param()`, skips `if false` dead targets via `SwitchInt`, yet runs on `promoted_mir` (with parent `DefKind::Fn`!) and emits `E0080` before `.discard_err()`. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_mir_transform/src/cross_crate_inline.rs` (L18–104 / L18–116); `compiler/rustc_codegen_ssa/src/back/symbol_export.rs` (L49–97 / L55, L114) | Marks call-free small non-`#[inline(never)]` functions `cross_crate_inlinable` at `-O2`, removing them from `reachable_non_generics` and local collector roots. |
| `rust-lang/rust` (`14210df0e`) | `compiler/rustc_metadata/src/rmeta/encoder.rs` (L1102–1132, L1812–1870, L2292–2314); `compiler/rustc_interface/src/passes.rs` (L1309 / `0259d5e9a` L1341) | Gates codegen and `optimized_mir` on `should_codegen()`; evaluates `promoted_mir` during metadata encoding when `should_codegen()` and `cross_crate_inlinable` hold. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_mir_transform/src/gvn.rs` (L605 / L600); `inline.rs` (`14210df0e` L1027–1032) | `GVN::eval_to_const` calls `eval_mir_constant` without `has_param()`; `inline.rs` copies `callee_body.required_consts` when inlining. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_monomorphize/src/collector.rs` (L1047–1091, L1347–1353 / L1382–1388, L1653–1671); `compiler/rustc_passes/src/reachable.rs` (L44–48, L458–523) | Root selection (`Lazy` vs `Eager`) and `items_of_instance` evaluation of `body.required_consts()`. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_mir_transform/src/promote_consts.rs` (L237–283 / L242–288, L393–423 / L402–432, L484–518, L635–705 / L641–689) | Promotion guards: `!NeedsDrop` (exempting `[T; 0]`), `!HasMutInterior`, `&mut` only for zero-length arrays, `validate_rvalue` rejecting div-by-zero, `InlineConst` eval cycle guard (`L703`). |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_const_eval/src/const_eval/valtrees.rs` (L105–112, L298–301, L389–465 / L121–128, L317–320, L408–474) | `ty::Pat` stripped to base type in `const_to_valtree_inner` and `valtree_to_const_value`; omitted in `valtree_into_mplace`. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_ty_utils/src/layout.rs` (L215–380 / L243–408); `compiler/rustc_const_eval/src/interpret/validity.rs` (L1501–1548 / L1499–1546); `rustc_codegen_llvm/src/{abi.rs:478, builder.rs:701}` | `ty::Pat` `valid_range`, niche calculation, wrapping error, CTFE/Miri scalar range enforcement, and LLVM `range` metadata emission. |
| `rust-lang/rust` (`14210df0e` / `0259d5e9a`) | `compiler/rustc_pattern_analysis/src/rustc.rs` (L423 / L425); `constructor.rs` (`14210df0e` L1190–1215) | Maps `ty::Pat(_, _)` to `ConstructorSet::Unlistable` (`all_empty() == false`). |
| `rust-lang/reference` (`c9cc32825b`) | `src/const_eval.md`, `src/expressions/block-expr.md`, `src/destructors.md` | Normative semantics for inline const blocks, promotion, interior mutability, and temporary lifetime extension. |
| `joshlf/anneal` (`c131b320e`) | `trusted/lean/Trusted/MirAst.lean` (`MirTy` L312–321, `ConstLit` L504–518); `trusted/rustc-capture/src/driver.rs` (L1–152); `trusted/audit/TrustedBoundary.lean` | Confirms `TyKind::Pat`, `Const::Unevaluated`, `Const::Ty`, and promoted non-scalar allocations fail closed (`FaultKind.unsupported`). |

---

## Revalidation

To revalidate the empirical behavior, compiler source stability, and Lean formalization on a newer toolchain or target:

1. **Rerun the live `rustc` + Miri differential harness** inside the report directory (requires nightly `rustc` + `miri` component installed on `PATH`):

   ```bash
   python3 support/probe_inline_const_required_consts_and_pat_valtree.py
   ```

   Inspect the output summary in `support/probe_output/probe_results.json` to confirm:
   - `mono_live_pub` still passes `--emit=metadata` (`rc=0`) while failing codegen modes;
   - `mono_dead_pub` and `generic_instantiated_dead` defer under `--crate-type=lib -Copt-level=2` unless annotated `#[inline(never)]`;
   - `promoted_dead_inline_const` fails `E0080` across `-O0` and `-O2` while `promoted_dead_rvalue` stays `rc=0`;
   - `gen_live_nonparam` behavior in `GVN` at `-O2` (monitoring whether future `rustc` adds a `has_param()` filter matching `known_panics_lint.rs`);
   - `PROM=30 EMPTY=0 EMPTY_C=0 CELL=6 DROP_VAL=7 DROPS=1` holds across native `-O0`, native `-O2`, Miri Stacked Borrows, and Miri `-Zmiri-tree-borrows`, alongside LLVM alias/niche IR patterns (`inttoptr (i64 4 to ptr)`, `range(i32 0, 11)`, `range(i32 1, 11)`);
   - CTFE (`E0080`), Miri (`SB` & `TB` UB), and `match x {}` on `pattern_type!(u32 is 1..=0)` (`E0004` before layout wrap error) remain unchanged.

2. **Re-verify the standalone Lean `v4.34.1` formalization and regenerate its audit receipt:**

   ```bash
   python3 support/check_lean.py
   ```

   Confirm `all_checks_passed: true`, `line_count >= 900`, zero banned tokens, zero `._unsafe_rec` / `isUnsafe` / `isPartial` / user axioms, and zero forbidden axioms across all `34` major theorems.

3. **Diff the narrow upstream decision points in `rust-lang/rust` before generalizing:** Inspect changes specifically in `required_consts.rs`, `promote_consts.rs` (`validate_local`, `validate_ref`, `validate_call`, `should_evaluate_for_promotion_checks`), `cross_crate_inline.rs`, `known_panics_lint.rs` (`KnownPanicsLint::run_lint`, `eval_constant`), `gvn.rs` (`eval_to_const`), `valtrees.rs` (`const_to_valtree_inner`, `valtree_to_const_value`, `valtree_into_mplace`), and `rustc_pattern_analysis/src/rustc.rs` (`ConstructorSet::Unlistable`).
