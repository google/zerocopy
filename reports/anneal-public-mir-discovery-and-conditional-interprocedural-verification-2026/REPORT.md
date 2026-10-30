<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Public MIR Discovery, Conditional Specifications, and Dual-Mode Interprocedural Verification in Anneal (2026)

## Summary

Moving Anneal from single-function unconditional verification (`pre := fun _ =>
True`) to crate-level verification of Rust libraries and binaries with private
helpers, conditional calling preconditions, and post-monomorphization
compile-time checks requires solving three coupled problems across
`trusted/rustc-capture`, `trusted/lean/`, and `theory/`:

1. **Public MIR Function Discovery in `rustc` (`58cf8f9c35`):**
   Textual MIR (`--emit=mir`, `-Z unpretty=mir`) and HIR (`-Z unpretty=hir`)
   outputs omit item visibility because `write_mir_sig` unconditionally prints
   `"fn "` and HIR stores visibilities out-of-band in
   `ResolverOutputs.visibilities`. An empirical 7-category `rustc_driver` probe
   ([`vis_probe/driver.rs`](vis_probe/driver.rs)) shows that no single `TyCtxt`
   query defines a crate's external entry surface: `tcx.local_visibility` has
   false positives on `pub fn` items inside private modules or private inherent
   `impl` blocks; `tcx.collect_and_partition_mono_items(())` omits
   uninstantiated generic `pub fn` items; `tcx.reachable_set(())` marks private
   helpers called by generic or `#[inline]` public functions as reachable in
   libraries and is nearly empty in binaries; and
   `tcx.effective_visibilities(())` has both an upstream `FIXME` false positive
   at `Level::ReachableThroughImplTrait` (marking all `OpaqueTy` hidden types in
   the crate as public even when their parent function is private) and a false
   negative on `<DynPrivStruct as PubTrait>` methods exposed via `&'static dyn
   PubTrait` coercion. Combining `tcx.mir_keys(())` with a 5-rule predicate
   `is_external_entry_fn(tcx, def_id)` resolves all seven categories and stamps
   an immutable `isPublic : Bool` field onto each `Trusted.CapturedFn` in
   `Mir.crate`.

2. **Three-Level Calling-Condition Taxonomy and Conditional `SpecOn`:**
   In Anneal's `Partial` refinement order (`p ≤ q` iff `∀ hq : q.defined, ∃ hp :
   p.defined, p.val hp ≤ q.val hq`), unconditional `MirLang.Spec post` sets
   `defined := True` at every query `q`. Consequently, any function `b` that can
   fail (`¬ (b q).defined`) on an input outside its precondition cannot refine
   `MirLang.Spec post` for *any* `post` (`not_le_spec_of_not_defined`,
   `addBody_not_le_spec` in
   [`ConditionalCrateVerification.lean`](ConditionalCrateVerification.lean)).
   Calling conditions partition cleanly into three orthogonal levels:
   - **Level 1 (ABI, type, memory, and aliasing validity):** Enforced in
     `MirMachine.initState` (`initMirState`), where queries outside
     `initMirState` satisfy `defined = True` and `val = False` and vacuously
     refine any specification (`behaviorOf_outside_initState_vacuous`).
   - **Level 2 (Safety and no-failure preconditions `pre`):** Placed in
     `.defined` via `MirLang.SpecOn pre post` and `MirLang.WellFormedOn pre`.
     Generalizing `FunctionalTranslation` with `funcSem_le_specOn` and
     `π_func_specOn_le` requires zero changes to `π_func` or `evalSym_sound`
     because `.fail` maps under `π_func` to `{ defined := False }` (the top
     element `⊤` of `Partial`).
   - **Level 3 (Functional domain assumptions `req` on safe functions):** Placed
     as an implicational guard `req q → post q out` inside `.val` of
     `MirLang.SpecOn pre`, preserving `spec ≤ MirLang.WellFormedOn pre`
     (`specOn_functional_req_le_wellFormedOn`).

3. **Call-Stack `Terminator.call`, Transitive `CompileAdmitted`, and Dual-Mode
   Interprocedural Symbolic Evaluation:**
   Replacing the skeleton's hardcoded two-callee `Terminator.callPure2` with a
   call-stack `Terminator.call dst callee args target` over `CrateEnv` and
   `MirState.frames : List CallFrame` in
   [`InterproceduralConditionalMir.lean`](InterproceduralConditionalMir.lean)
   eliminates both `PureCallee2` and `CalleeSummaryVerified` from `trusted/`
   while preserving `TotalStep`, `InhabitedDemonic`, and
   `mirMachine_non_vacuity_at_every_depth`. Pairing runtime call-stack semantics
   with transitive `CompileAdmitted` over `requiredConsts` and `mentionedItems`
   catches post-monomorphization CTFE failures even inside dead runtime branches
   (`if false { const_bounded_add::<2000>(x) }`,
   `deadBranchBadCaller_not_compileAdmitted`). In `theory/`, a unified
   spine-preserving evaluator `evalSymState` (`Option (Bool × SymVal)`) proved
   sound via a frame-stack continuation invariant `ReturnCont`
   (`evalSymState_sound`) supports both **Mode A** (zero-annotation symbolic
   call inlining via `TransPlan.callInline`) and **Mode B** (modular verified
   callee summaries via `TransPlan.callSummary`), reducing guarded and
   conditional callers by Lean kernel `rfl` to identical symbolic terms
   (`evalSymState_doubleGuarded_modeA_eq_modeB`).

## Applicability

The findings in this report apply to the combination of three pinned subjects:

- **Anneal verification framework (`joshlf/anneal` at
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):** Specifically the behavioral
  refinement algebra (`trusted/lean/Trusted/Refinement.lean`), small-step MIR
  operational semantics (`trusted/lean/Trusted/MirSemantics.lean`), `.olean`
  boundary auditor (`trusted/audit/TrustedBoundary.lean`), `rustc` MIR capture
  driver (`trusted/rustc-capture/`), and pure functional translation layer
  (`theory/Anneal/FunctionalTranslation.lean`).
- **Rust compiler (`rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67`):** Specifically the query
  implementations in `rustc_middle` (`hir::ModuleItems`, `hir::map`,
  `middle::privacy`, `mir::pretty`, `mir::syntax`), `rustc_mir_transform`
  (`mir_keys`), `rustc_resolve` (`effective_visibilities`), `rustc_privacy`
  (`EmbargoVisitor`, `ReachEverythingInTheInterfaceVisitor`), `rustc_passes`
  (`reachable_set`), and `rustc_monomorphize` (`collector`).
- **Lean 4 theorem prover (`leanprover/lean4` at
  `5045d0056413266e57c625dcd7c365b10e377c52`, release `v4.34.1`):** All
  mechanized definitions, positive and negative controls, and kernel `rfl`
  symbolic-evaluation proofs in
  [`ConditionalCrateVerification.lean`](ConditionalCrateVerification.lean) and
  [`InterproceduralConditionalMir.lean`](InterproceduralConditionalMir.lean)
  were checked under `lean -DElab.async=false -Ddebug.skipKernelTC=false` with
  zero `sorryAx`, zero `Lean.ofReduceBool`, and zero `Classical.choice`.

The `rustc` visibility findings depend on internal `rustc_private` query
behavior at commit `58cf8f9c35b355199727627d07ae34a4e2846d67` (in particular,
the `krate.opaques()` loop in `compiler/rustc_privacy/src/lib.rs`) and must be
revalidated via [`vis_probe/driver.rs`](vis_probe/driver.rs) when advancing the
pinned Rust toolchain.

## Findings

### 1. Public MIR Function Discovery in `rustc` and `trusted/rustc-capture`

#### 1.1 Textual MIR and HIR Dumps Strip Item Visibility

`Basis: source + execution`

Running `rustc --emit=mir`, `rustc -Z unpretty=mir`, or `rustc -Z unpretty=hir`
cannot distinguish public entry points from private functions:

1. **Textual MIR (`--emit=mir` and `-Z unpretty=mir`):**
   [`write_mir_pretty`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs#L326-L329)
   iterates over `tcx.mir_keys(())` and formats each signature with
   [`write_mir_sig`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs#L679-L722),
   which unconditionally emits `"fn "` followed by `tcx.def_path_str(def_id)`.
   In our probe crate ([`vis_probe/src/lib.rs`](vis_probe/src/lib.rs)),
   `pub fn cat1_top_pub`, `fn cat1_top_priv`, `pub(crate) fn
   cat1_top_pub_crate`, and `#[no_mangle] fn cat6_ffi_no_mangle` all emit
   identical `fn <name>(_1: u32) -> u32 {` headers with no visibility modifier
   or attribute.
2. **Textual HIR (`-Z unpretty=hir`):**
   `rustc` does not store visibility on `rustc_hir::Item` or
   `rustc_hir::ImplItem`; instead, `rustc_resolve` records syntactic
   visibilities out-of-band in `ResolverOutputs.visibilities` (queried via
   [`tcx.local_visibility(def_id)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/map.rs#L1265-L1324)).
   Consequently, `-Z unpretty=hir` prints both `pub fn` and `pub use` without
   `pub`.

Discovering a crate's external entry surface therefore requires querying
`TyCtxt` inside an in-process `rustc_driver::Callbacks::after_analysis` pass.

#### 1.2 Candidate MIR Body Enumeration: `mir_keys` vs. `hir_body_owners`

`Basis: source + execution`

In
[`compiler/rustc_mir_transform/src/lib.rs#L325-L358`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L325-L358),
`tcx.mir_keys(())` constructs the authoritative `FxIndexSet<LocalDefId>` of
definitions that own MIR bodies by starting from `tcx.hir_body_owners()`
([`compiler/rustc_middle/src/hir/mod.rs#L106-L108`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/mod.rs#L106-L108))
and making three adjustments:

1. It removes `DefKind::GlobalAsm` fake bodies.
2. It inserts `tcx.coroutine_by_move_body_def_id(body_owner)`
   (`DefKind::SyntheticCoroutineBody`) for coroutine-closures.
3. It inserts synthetic tuple-struct and tuple-enum variant constructors
   (`DefKind::Ctor(CtorOf::Struct | CtorOf::Variant, CtorKind::Fn)`), which have
   callable `optimized_mir` bodies (`PubStruct(x)`) despite having no HIR
   `BodyId` (`in_bo = false, in_mk = true` in
   [`vis_probe/driver_lib.txt`](vis_probe/driver_lib.txt#L17)).

Required trait methods without a default body (`PubTrait::cat4_trait_req`) have
no `BodyId` and are absent from both `hir_body_owners()` and `mir_keys(())`,
whereas default trait methods (`PubTrait::cat4_trait_default`) appear in both.
Following
[`write_mir_sig`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs#L679-L685),
a `LocalDefId` in `tcx.mir_keys(())` is a callable runtime function when its
`DefKind` is `Fn`, `AssocFn`, `Ctor(_, CtorKind::Fn)`, `SyntheticCoroutineBody`,
or `Closure`.

#### 1.3 Empirical Evaluation of `TyCtxt` Visibility and Reachability Queries Across 7 Categories

`Basis: source + execution`

We evaluated five `TyCtxt` mechanisms in
[`vis_probe/driver.rs`](vis_probe/driver.rs) against a 7-category test crate
([`vis_probe/src/lib.rs`](vis_probe/src/lib.rs)) under both `--crate-type=lib`
([`vis_probe/driver_lib.txt`](vis_probe/driver_lib.txt)) and `--crate-type=bin`
([`vis_probe/driver_bin.txt`](vis_probe/driver_bin.txt)):

- **`nom_vis` (`tcx.local_visibility(def_id)`):** Defined in
  [`compiler/rustc_middle/src/hir/map.rs#L1265-L1324`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/map.rs#L1265-L1324).
  Purely syntactic (`Visibility::Public` vs. `Visibility::Restricted(ModId)`);
  panics with `bug!("visibility of unexpected DefKind: Closure")` on closures,
  `Impl`, and `OpaqueTy`.
- **`Direct`, `Reexp`, `Reach`, `ReachIT`
  (`tcx.effective_visibilities(())`):** Defined in
  [`compiler/rustc_middle/src/middle/privacy.rs#L20-L289`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/middle/privacy.rs#L20-L289)
  and computed by `EffectiveVisibilitiesVisitor` in
  [`compiler/rustc_resolve/src/effective_visibilities.rs#L27-L202`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_resolve/src/effective_visibilities.rs#L27-L202)
  and `EmbargoVisitor` / `ReachEverythingInTheInterfaceVisitor` in
  [`compiler/rustc_privacy/src/lib.rs#L510-L828`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs#L510-L828)
  and
  [`#L1809-L1855`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs#L1809-L1855).
  Tracks four monotonic levels:
  $\text{Direct} \le \text{Reexported} \le \text{Reachable} \le \text{ReachableThroughImplTrait}$.
- **`reach` (`tcx.reachable_set(())`):** Defined in
  [`compiler/rustc_passes/src/reachable.rs#L459-L524`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs#L459-L524).
  Computes cross-crate symbol/MIR linkage reachability.
- **`extern` (`tcx.codegen_fn_attrs(def_id).contains_extern_indicator()`):**
  Checks `#[no_mangle]`, `#[export_name]`, and `#[rustc_std_internal_symbol]`.
- **`mono` (`tcx.collect_and_partition_mono_items(())`):** Defined in
  [`compiler/rustc_monomorphize/src/collector.rs#L1483-L1957`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1483-L1957).

| Cat | Function (`def_path_str`) | `DefKind` | `nom_vis` | `Direct` | `Reexp` | `Reach` | `ReachIT` | `reach (lib)` | `reach (bin)` | `extern` | `mono (lib)` | `mono (bin)` | **External Entry?** |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **1** | `cat1_top_pub` | `Fn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **1** | `cat1_top_priv` | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `true` | `true` | **No** (`mono` false positive: called by `main`) |
| **1** | `cat1_top_pub_crate` | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **2** | `priv_mod::cat2_priv_mod_unexported` | `Fn` | `Pub` | `Restr` | `Restr` | `Restr` | `Restr` | `false` | `false` | `false` | `false` | `false` | **No** (`nom_vis` false positive) |
| **2** | `priv_mod::cat2_priv_mod_reexported` | `Fn` | `Pub` | `Restr` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** (`Direct` false negative) |
| **3** | `PubStruct::cat3_pub_struct_inh_pub` | `AssocFn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **3** | `PubStruct::cat3_pub_struct_inh_pub_crate` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **3** | `PubStruct::cat3_pub_struct_inh_priv` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **3** | `PrivStruct::cat3_priv_struct_inh_pub` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Restr` | `false` | `false` | `false` | `false` | `false` | **No** (`nom_vis` false positive) |
| **3** | `PrivStruct::cat3_priv_struct_inh_priv` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **3** | `priv_mod_type::PubInPrivMod::cat3_pub_in_priv_mod_inh_pub` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** (leaked via `pub fn` return type; `Reexp` false negative) |
| **3** | `priv_mod_type::PubInPrivMod::cat3_pub_in_priv_mod_inh_priv` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **4a** | `<PubStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **4a** | `PubTrait::cat4_trait_default` | `AssocFn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **4b** | `<RpitPrivStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** (returned via `pub fn -> impl PubTrait`) |
| **4b** | `RpitPrivStruct::cat4_rpit_priv_struct_inh_pub` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `true` | `false` | **No** (`ReachIT` false positive: caller only sees `impl PubTrait`) |
| **4b** | `<PrivFnRpitStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes (conservative)** / `ReachIT` `opaques()` `FIXME` |
| **4c** | `<DynPrivStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Restr` | `true` | `false` | `false` | `true` | `false` | **Yes** (callable via `&'static dyn PubTrait`; `ReachIT` false negative!) |
| **4d** | `<UnexportedPrivStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Restr` | `true` | `false` | `false` | `true` | `false` | **Yes (conservative)** (implements exported trait `PubTrait`) |
| **4e** | `<PubStruct as PrivTrait>::cat4_priv_trait_req` | `AssocFn` | `Restr` | `Restr` | `Restr` | `Restr` | `Restr` | `true` | `false` | `false` | `true` | `false` | **No** (`reach (lib)` false positive!) |
| **4e** | `PrivTrait::cat4_priv_trait_default` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `true` | `false` | `false` | `false` | `false` | **No** (`reach (lib)` false positive!) |
| **5** | `cat5_generic_pub_uninstantiated<T>` | `Fn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `false` | `false` | **Yes** (`mono` false negative!) |
| **5** | `cat5_generic_pub_instantiated<T>` | `Fn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **5** | `cat5_generic_priv_uninstantiated<T>` | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **5** | `cat5_priv_helper_called_by_generic` | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `true` | `true` | `false` | `true` | `false` | **No** (`reach` false positive!) |
| **6** | `cat6_ffi_no_mangle` (`#[no_mangle]`) | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `true` | `true` | `true` | `true` | `true` | **Yes** (`EffectiveVisibilities` false negative) |
| **6** | `cat6_ffi_export_name` (`#[export_name]`) | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `true` | `true` | `true` | `true` | `true` | **Yes** (`EffectiveVisibilities` false negative) |
| **6** | `main` (in `--crate-type=bin`) | `Fn` | `Pub`/`Restr` | `Pub`/`-` | `Pub`/`-` | `Pub`/`-` | `Pub`/`-` | `true` | `false` | `false` | `true` | `true` | **Yes** (`tcx.entry_fn(()) == Some((def_id, _))`) |
| **7** | `cat7_make_adder_pub::{closure#0}` | `Closure` | `-` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `false` | `false` | **Yes** (returned via `pub fn -> impl Fn`) |
| **7** | `cat7_make_adder_priv::{closure#0}` | `Closure` | `-` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `false` | `false` | **No** (`ReachIT` false positive due to `opaques()` `FIXME`!) |
| **7** | `cat7_internal_closure_only::{closure#0}` | `Closure` | `-` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `true` | `false` | **No** |

Four subtle compiler behaviors explain the off-diagonal entries in the table:

1. **`Level::Reachable` vs. `Level::Reexported`:**
   `priv_mod_type::PubInPrivMod::cat3_pub_in_priv_mod_inh_pub` is `Restricted`
   at `Level::Direct` and `Level::Reexported` because `PubInPrivMod` is never
   re-exported by a `pub use`, but becomes `Public` at `Level::Reachable`
   because `pub fn cat3_leak_pub_in_priv_mod() -> priv_mod_type::PubInPrivMod`
   exposes the struct in a public return signature, allowing external callers to
   write `cat3_leak_pub_in_priv_mod(1).cat3_pub_in_priv_mod_inh_pub()`.
2. **`rustc_privacy` `opaques()` `FIXME` false positive at
   `Level::ReachableThroughImplTrait`:**
   In
   [`compiler/rustc_privacy/src/lib.rs#L1841-L1846`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs#L1841-L1846),
   `ReachEverythingInTheInterfaceVisitor` iterates over `for opaque in
   krate.opaques()` and marks the hidden type of *every* `OpaqueTy` (`impl
   Trait`) in the crate as `Public` at `Level::ReachableThroughImplTrait`—with a
   comment `FIXME: Actually compute visibility of opaque types instead of
   pessimistically considering all of them pub`. As a result, a private function
   `fn cat7_make_adder_priv(x: usize) -> impl Fn(usize) -> usize` marks its
   returned closure `cat7_make_adder_priv::{closure#0}` as `Public` at
   `Level::ReachableThroughImplTrait`, and `RpitPrivStruct` has its inherent
   method `cat4_rpit_priv_struct_inh_pub` marked `Public` at
   `Level::ReachableThroughImplTrait` even though callers receiving `impl
   PubTrait` can only invoke `PubTrait` methods, never inherent methods on the
   hidden type.
3. **`dyn Trait` vtable coercion false negative in `EffectiveVisibilities`:**
   Because `rustc_privacy` inspects item signatures rather than function bodies,
   when a private struct `DynPrivStruct` implements `PubTrait` and is coerced to
   `&'static dyn PubTrait` inside `pub fn cat4_return_dyn()`,
   `<DynPrivStruct as PubTrait>::cat4_trait_req` remains `Restricted` across all
   four `EffectiveVisibility` levels even though external callers can invoke it
   through the returned vtable.
4. **Why `tcx.reachable_set(())` cannot be used for entry-point discovery:**
   In
   [`compiler/rustc_passes/src/reachable.rs#L206-L209`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs#L206-L209)
   and
   [`#L411-L431`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs#L411-L431),
   `ReachableContext` walks the HIR bodies of all generic, `#[inline]`, and
   `const` reachable functions and adds every private helper they call
   (`cat5_priv_helper_called_by_generic`) plus every trait `impl` method in the
   crate (`<PubStruct as PrivTrait>::cat4_priv_trait_req`) to
   `reachable_symbols`. Treating `reachable_set` as the public entry surface
   would force private helpers called by generic or inline public functions to
   satisfy unrestricted public preconditions.

#### 1.4 Exact 5-Rule External-Entry Discovery Predicate (`is_external_entry_fn`)

`Basis: source + execution + derived`

Combining `tcx.mir_keys(())` with the following 5-rule predicate over `TyCtxt`
classifies every row of the 7-category probe matrix without false negatives on
`dyn Trait`, FFI symbols, or `fn main`, and without false positives on private
helpers, inherent methods on RPIT hidden types, or closures inside private RPIT
functions:

```rust
pub fn is_external_entry_fn(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let eff_vis = tcx.effective_visibilities(());

    // Rule 1: Direct, re-exported, or signature-reachable public items.
    if eff_vis.is_reachable(def_id) {
        return true;
    }

    // Rule 2: Executable entry point (`fn main` or `#[start]`).
    if tcx.entry_fn(()).and_then(|(id, _)| id.as_local()) == Some(def_id) {
        return true;
    }

    // Rule 3: FFI / custom symbol export (`#[no_mangle]`, `#[export_name]`, EII).
    let kind = tcx.def_kind(def_id);
    if kind.has_codegen_attrs() {
        let attrs = tcx.codegen_fn_attrs(def_id);
        if attrs.contains_extern_indicator()
            || !attrs.foreign_item_symbol_aliases.is_empty()
        {
            return true;
        }
    }

    // Rule 4: Associated functions in `impl Trait for Type` where `Trait` is
    // foreign or publicly reachable (covers RPIT `impl Trait` and `dyn Trait`).
    if kind == DefKind::AssocFn {
        let parent_id = tcx.local_parent(def_id);
        if matches!(tcx.def_kind(parent_id), DefKind::Impl { of_trait: true }) {
            let trait_def_id = tcx.impl_trait_id(parent_id.to_def_id());
            let trait_is_public = !trait_def_id.is_local()
                || eff_vis.is_reachable(trait_def_id.expect_local());
            if trait_is_public {
                return true;
            }
        }
    }

    // Rule 5: Closures (or synthetic coroutine bodies) that escape an external
    // entry item via `impl Trait` (filtering out `rustc_privacy`'s `opaques()`
    // false positive on private functions returning `impl Trait`).
    if tcx.is_closure_like(def_id.to_def_id()) {
        let root_owner = tcx.typeck_root_def_id_local(def_id);
        if is_external_entry_fn(tcx, root_owner)
            && eff_vis.is_public_at_level(def_id, Level::ReachableThroughImplTrait)
        {
            return true;
        }
    }

    false
}
```

#### 1.5 Public-Surface Completeness in `Trusted.CrateTheorem`

`Basis: source + derived`

In `trusted/lean/Trusted/MirSemantics.lean` and
`trusted/lean/Trusted/Refinement.lean`, `Trusted.Crate` must retain *both*
public entry points and private helpers in a single `functions : List
CapturedFn` table so that `Terminator.call` and `mentionedItems` inside public
functions resolve against private helper bodies. Adding `isPublic : Bool :=
true` to `Trusted.CapturedFn` (populated by `trusted/rustc-capture` via
`is_external_entry_fn` for every callable item in `tcx.mir_keys(())`) preserves
public-surface completeness without modifying
`trusted/audit/TrustedBoundary.lean`:

1. `checkModuleImports` verifies that `.anneal/Mir.lean` imports only
   `foundation ++ trusted`.
2. `checkMirCrate` verifies that `Mir.crate : Trusted.Crate` is defined in
   module `Mir`.
3. `checkVerifyCrate` verifies that `Proof.verify_crate` has the exact type
   `Trusted.CrateTheorem Mir.crate`.

Because `is_external_entry_fn` is computed from `TyCtxt` queries rather than
user attributes, and `Proof.lean` cannot mutate or shadow `Mir.crate`, user code
cannot omit a public function or downgrade `isPublic` from `true` to `false`.

---

### 2. Conditional Crate Verification and the Three-Level Calling-Condition Taxonomy

#### 2.1 Impossibility of Unconditional `MirLang.Spec` for Conditional Functions

`Basis: source + execution`

In Anneal's behavioral lattice
([`ConditionalCrateVerification.lean`](ConditionalCrateVerification.lean#L81-L160)),
refinement `p ≤ q` on `Partial α` is defined as:

```lean
def Partial.le (p q : Partial α) : Prop :=
  ∀ hq : q.defined, ∃ hp : p.defined, p.val hp ≤ q.val hq
```

Because `Language.Spec L post` is an abbreviation for `L.SpecOn (fun _ => True)
post`, `(L.Spec post q).defined` is `True` at *every* query `q : L.Query`.
Consequently, whenever a program's behavior `b` has `¬ (b q).defined` at even a
single valid initial state `q` (for example, when an arithmetic helper overflows
and transitions to `.failed .contractViolation`), `b` cannot refine `L.Spec
post` for *any* postcondition `post`—even when `post` is guarded by an
implication `pre q → ...`:

```lean
theorem not_le_spec_of_not_defined {L : Language} {b : L.Behavior}
    {q : L.Query} (hundef : ¬ (b q).defined)
    (post : L.Query → L.Out → Prop) :
    ¬ (b ≤ L.Spec post) :=
  fun hle => hundef (hle q True.intro).1
```

In
[`ConditionalCrateVerification.lean`](ConditionalCrateVerification.lean#L3116-L3155),
`addBody_not_wellFormed` and `addBody_not_le_spec` instantiate this theorem on
`addBody` (`fn add(x: usize, y: usize) -> usize { x + y }`) at the valid initial
state `addOverflowInit` (`_1 = usizeMax, _2 = 1`, step budget `2`), proving
`¬ (MirSem addBody ≤ MirLang.Spec post)` for every `post`. Any function with a
non-trivial safety or no-failure precondition `pre` must therefore state its
contract using `MirLang.SpecOn pre post` (`defined := pre q`) and
`MirLang.WellFormedOn pre`.

#### 2.2 Three-Level Taxonomy of Calling Conditions

`Basis: derived + execution`

Mapping calling conditions onto the machine initial-state predicate
`M.initState` and the two fields of `Partial` (`defined` and `val`) yields three
orthogonal levels mechanized in
[`ConditionalCrateVerification.lean`](ConditionalCrateVerification.lean#L141-L283)
and [`#L673-L685`](ConditionalCrateVerification.lean#L673-L685):

| Level | Calling Condition Class | Representation in Anneal | Semantic Effect When Violated |
| :--- | :--- | :--- | :--- |
| **Level 1: ABI / Type / Memory / Aliasing Validity** | Well-typed arguments in `_1.._n`, uninitialized scratch locals, `block = 0`, `stmtIdx = 0`, `frames = []`, valid entry heap | `MirMachine.initState` (`initMirState`) | `(MirSem body q).defined = True` and `(MirSem body q).val = False`; vacuously refines any spec (`behaviorOf_outside_initState_vacuous`), mirrored by `AeneasRes.inapplicable` in `FuncLang` |
| **Level 2: Safety / No-Failure Precondition (`pre`)** | Checked-arithmetic bounds (`x + y <= usizeMax`), raw-pointer validity, slice bounds, `unsafe fn` contracts | `fn.pre : ExecQuery MirState → Prop` in `MirLang.WellFormedOn fn.pre` and `MirLang.SpecOn fn.pre post` (`.defined := fn.pre q`) | `(SpecOn fn.pre post q).defined = False` (`⊤` in `Partial`), imposing no obligation on `MirSem body q` outside `fn.pre` |
| **Level 3: Functional Precondition (`req`)** | Logical domain assumptions on an already-safe function (e.g., input slice is sorted for `binary_search`) | Implicational guard inside `.val`: `MirLang.SpecOn fn.pre (fun q out => req q → post q out)` | `.defined = fn.pre q` still holds (execution is still proved safe), while `post q out` is only promised when `req q` holds |

Two structural lemmas govern how these levels compose:

1. **Implicational vs. Existential State Preconditions
   ([`preAdd_iff_exists_on_init`](ConditionalCrateVerification.lean#L2528-L2548)):**
   Writing `FuncPreAdd init` implicationally (`∀ x0 y0, init.locals 1 = some
   (.usize x0) → init.locals 2 = some (.usize y0) → x0 + y0 ≤ usizeMax`) is
   equivalent to the existential form `PreAddExists` on every valid entry state
   satisfying `initMirState addBody q.init`, but automatically holds on
   ill-typed states outside `initMirState` where `translate body init =
   .inapplicable`.
2. **Single-Proof Discharge of `WellFormedOn`
   ([`specOn_le_wellFormedOn`](ConditionalCrateVerification.lean#L250-L253),
   [`specOn_functional_req_le_wellFormedOn`](ConditionalCrateVerification.lean#L280-L283),
   [`Compiler.Verified.with_wellFormedOn`](ConditionalCrateVerification.lean#L318-L326)):**
   Because `L.SpecOn pre post ≤ L.WellFormedOn pre` holds for any `post`
   (including `fun q out => req q → post q out`), a single proof of
   `C.Verified prog (L.SpecOn pre ...)` discharges both the functional
   specification and `L.WellFormedOn pre` in `VerificationResultOn`.

#### 2.3 Conditional `FunctionalTranslation` (`funcSem_le_specOn` and `π_func_specOn_le`)

`Basis: derived + execution`

Generalizing `FunctionalTranslation` to conditional specifications requires
replacing the unconditional bridge lemmas `funcSem_le_spec` and `π_func_spec_le`
with
[`funcSem_le_specOn`](ConditionalCrateVerification.lean#L1078-L1085) and
[`π_func_specOn_le`](ConditionalCrateVerification.lean#L1096-L1102):

```lean
theorem funcSem_le_specOn {p : MirState → AeneasRes MirVal}
    {Pre : MirState → Prop} {Post : MirState → MirVal → Prop}
    (h : ∀ init, Pre init → p init ≠ .fail ∧ ∀ v, p init = .ok v → Post init v) :
    FuncLang.sem p ≤ FuncLang.SpecOn Pre Post

theorem π_func_specOn_le (Pre : MirState → Prop) (Post : MirState → MirVal → Prop) :
    π_func (FuncLang.SpecOn Pre Post) ≤
      MirLang.SpecOn (fun q => Pre q.init) (fun q out =>
        ∀ v, out.outcome = .terminated (.normal v) → Post q.init v)
```

Crucially, `π_func`, `monotone_π_func`, and `evalSym_sound` (`MirSem body ≤
π_func (FuncLang.sem (evalSym plan body))`) require **zero changes**. When an
input violates `Pre init` and causes `evalSym plan body init = .fail`, `π_func`
maps `.fail` to `{ defined := False }` (`Partial.ub`, the top element `⊤` of the
refinement preorder), so `MirSem body q ≤ π_func (FuncLang.sem ...) q` holds
trivially on failing inputs while enforcing safety and functional correctness on
all inputs where `Pre init` holds and `evalSym` returns `.ok v`.

#### 2.4 Mode 1 (`.failed .contractViolation`) vs. Mode 2 (`.terminated .unwind`) Overflow Semantics

`Basis: normative + execution`

Section 7 of
[`ConditionalCrateVerification.lean`](ConditionalCrateVerification.lean#L3197-L3516)
compares Anneal's Mode 1 panic-free semantics (`MirLang`, where
`assertNotOverflow` transitions to `.failed .contractViolation`) against Mode 2
unwinding semantics (`MirLangUnwind`, where `assertNotOverflow` transitions to
`.terminated .unwind`) on the same `addBody` AST:

| Dimension | Mode 1: `.failed .contractViolation` (`MirLang`) | Mode 2: `.terminated .unwind` (`MirLangUnwind`) |
| :--- | :--- | :--- |
| **`outcome.isSafe` on arithmetic overflow** | `False` | `True` (stack unwinding is defined behavior in safe Rust) |
| **Unconditional `WellFormed` for `addBody`** | **False** ([`addBody_not_wellFormed`](ConditionalCrateVerification.lean#L3116-L3131)) | **True** ([`addBody_satisfies_wellFormedUnwind`](ConditionalCrateVerification.lean#L3513-L3515)) |
| **Specification level for `addBody` no-overflow** | Level 2 (`MirLang.SpecOn PreAdd PostAdd`, [`addBody_satisfies_ensuresOn`](ConditionalCrateVerification.lean#L2659-L2665)) | Level 3 (`MirLangUnwind.Spec` with `x0 + y0 ≤ usizeMax → out.outcome ≠ .terminated .unwind` in `.val`, [`addBody_satisfies_ensuresUnwind`](ConditionalCrateVerification.lean#L3308-L3510)) |
| **Where Level 2 (`SpecOn`) remains mandatory** | Checked arithmetic, `assert!`, division/remainder by zero, bounds checks, and `unsafe fn` preconditions | `unsafe fn` preconditions (raw-pointer dereference, aliasing, `get_unchecked`) where violation is true UB (`.failed .ub`) |

---

### 3. Call-Stack `Terminator.call`, Transitive `CompileAdmitted`, and Dual-Mode Interprocedural Verification

#### 3.1 Eliminating `PureCallee2` and `CalleeSummaryVerified` from `trusted/` via Call-Stack `Terminator.call`

`Basis: normative + source + execution`

In Round 1 ([`ConditionalCrateVerification.lean`](ConditionalCrateVerification.lean#L829-L946)),
interprocedural calls were modeled by extending `evalPureCallee2` to return
`Option (Bool × MirVal)` and requiring `CalleeSummaryVerified` in
`CrateTheorem`. While sound, that interim design kept a hardcoded `PureCallee2`
enumeration and summary-adequacy predicate inside the TCB.

Applying `model-refinement` in Round 2
([`InterproceduralConditionalMir.lean`](InterproceduralConditionalMir.lean#L643-L1035)),
we replace `Terminator.callPure2` with a general crate-resolved
`Terminator.call dst callee args target` matching the normative semantics of
`TerminatorKind::Call` and `TerminatorKind::Return` in
[`compiler/rustc_middle/src/mir/syntax.rs#L696-L784`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L696-L784):

1. **Call-Stack State (`CallFrame` and `MirState`):**
   `MirState` ([`InterproceduralConditionalMir.lean`](InterproceduralConditionalMir.lean#L737-L758))
   records the active `curBody : MirBody` and a stack of suspended caller
   continuations `frames : List CallFrame`, where each `CallFrame` stores
   `callerBody`, `dst : LocalIdx`, `returnTarget : BasicBlockIdx`, and
   `callerLocals : Nat → Option MirVal`.
2. **Operational Call and Return Transitions (`evalMirTerminator`):**
   - On `Terminator.call dst callee args target`
     ([`#L964-L983`](InterproceduralConditionalMir.lean#L964-L983)), the machine
     evaluates `args` left-to-right via `evalOperandList`, looks up `callee` in
     `env : CrateEnv`, validates argument arity and types via
     `argsHaveTysBool argVals calleeBody.argTys`, pushes a `CallFrame` onto
     `s.frames`, and steps to `calleeBody` at `block := 0, stmtIdx := 0` with
     `locals := buildCalleeLocals argVals`.
   - On `Terminator.return_`
     ([`#L940-L958`](InterproceduralConditionalMir.lean#L940-L958)), reading
     `s.locals 0 = some retVal` either terminates with `.terminated (.normal
     retVal)` when `s.frames = []` or pops `frame :: restFrames`, restoring
     `frame.callerBody` at `frame.returnTarget.index` with `frame.dst.index`
     updated to `some retVal`.
3. **Preservation of Layer 1B Machine Health Theorems:**
   Because `evalMirStep env s` is a total deterministic function that never
   emits `StepResult.choice`, the call-stack `MirMachine` satisfies:
   - [`mirMachine_totalStep`](InterproceduralConditionalMir.lean#L1138-L1140)
     (`TotalStep MirMachine`),
   - [`mirMachine_inhabitedDemonic`](InterproceduralConditionalMir.lean#L1143-L1146)
     (`InhabitedDemonic MirMachine`), and
   - [`mirMachine_non_vacuity_at_every_depth`](InterproceduralConditionalMir.lean#L1151-L1161)
     (every valid initial state has a non-`.stuck` execution prefix at every
     step budget `n : Nat` across arbitrary call depth).

Because `MirMachine` executes the callee's actual `MirBody` on the call stack,
`trusted/` needs neither `PureCallee2` nor `CalleeSummaryVerified`.

#### 3.2 Transitive `CompileAdmitted` Across `requiredConsts` and `mentionedItems`

`Basis: source + execution`

In
[`compiler/rustc_monomorphize/src/collector.rs#L1364-L1389`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1364-L1389),
`collect_items_of_instance` evaluates every constant in `body.required_consts()`
and visits every item in `body.mentioned_items()` (including items inside dead
runtime branches `if false { ... }`) in `CollectionMode::MentionedItems`, which
recursively evaluates the target item's `required_consts()`.

In
[`InterproceduralConditionalMir.lean`](InterproceduralConditionalMir.lean#L1355-L1403),
each `MirBody` carries `requiredConsts : List ConstMirBody` and `mentionedItems
: List String`, and transitive compile-time admissibility is defined alongside
its executable boolean checker:

```lean
def CompileAdmitted (env : CrateEnv) : Nat → MirBody → Prop
  | 0, _ => False
  | fuel + 1, body =>
    AllHold (body.requiredConsts.map CtfeAdmitted) ∧
    AllHold (body.mentionedItems.map (fun calleeName =>
      match lookupFn env calleeName with
      | some calleeBody => CompileAdmitted env fuel calleeBody
      | none => False))
```

By [`compileAdmitted_of_checkCompileAdmitted`](InterproceduralConditionalMir.lean#L1385-L1403),
`checkCompileAdmitted env ctfeFuel fuel body = true` implies
`CompileAdmitted env fuel body`, discharging compile-time admissibility on
concrete crates by kernel `rfl`. Section 7.4
([`#L3881-L4117`](InterproceduralConditionalMir.lean#L3881-L4117)) mechanizes
both positive and negative controls over `const_bounded_add<N>(x)` (containing
`const { assert!(N <= 1000) }` in `requiredConsts`):

- **Positive control (`caller_good_500`):** Calls `const_bounded_add::<500>(x)`.
  Proved both compile-admitted by `rfl`
  ([`callerGood500_compileAdmitted`](InterproceduralConditionalMir.lean#L3992-L3994))
  and runtime-safe via Mode A call inlining
  ([`callerGood500_runtime_verified`](InterproceduralConditionalMir.lean#L4038-L4067)).
- **Dead-branch negative control (`dead_branch_bad_caller`):** Executes `if
  false { const_bounded_add::<2000>(x) } else { x }`. At runtime, it is verified
  safe
  ([`deadBranchBadCaller_runtime_verified`](InterproceduralConditionalMir.lean#L4077-L4106))
  because `switchInt (const false)` always jumps to the live `else` branch. At
  compile time, however, `"const_bounded_add_2000" ∈ mentionedItems` causes
  `CompileAdmitted` to be refuted at **every** fuel depth `fuel : Nat`
  ([`deadBranchBadCaller_not_compileAdmitted`](InterproceduralConditionalMir.lean#L4013-L4017)),
  and its `Behavior.when`-gated behavior collapses to `Partial.bot`
  ([`deadBranchBadCaller_when_compileAdmitted_refines_any`](InterproceduralConditionalMir.lean#L4112-L4117)).

#### 3.3 Unified Spine-Preserving `evalSymState` and Dual-Mode Interprocedural Verification

`Basis: derived + execution`

In
[`InterproceduralConditionalMir.lean`](InterproceduralConditionalMir.lean#L1643-L1930),
`evalSymState env summaries plan body sym` returns `Option (Bool × SymVal)`
(`some (failed, retSv)`). Two combinators preserve outer `some` and `SymVal`
constructors across branches and calls so Lean's kernel reduces interprocedural
symbolic execution by `rfl`:

1. **Right-matching `orBool`
   ([`#L1643-L1656`](InterproceduralConditionalMir.lean#L1643-L1656)):**
   `def orBool (ov1 ov2 : Bool) : Bool := match ov2 with | false => ov1 | true
   => true`. Because `Terminator.return_` produces `failed = false`, matching on
   `ov2` first reduces `orBool (decide (usizeMax < x + x)) false` definitionally
   to `decide (usizeMax < x + x)` by `rfl` even when `x : Nat` is a free
   symbolic variable.
2. **Constructor-lifting `mergeBranchSymVal`
   ([`#L1660-L1683`](InterproceduralConditionalMir.lean#L1660-L1683)):**
   Lifts the shared `SymVal` constructor (`.usize`, `.bool`, `.unit`) outside
   `match cond with` across `Terminator.switchInt`.

To prove soundness across arbitrary call-stack depth in a single structural
induction without step-count arithmetic,
[`InterproceduralConditionalMir.lean`](InterproceduralConditionalMir.lean#L1936-L3035)
defines prefix safety `SafeFrom` and a frame-stack continuation invariant
`ReturnCont`:

```lean
def ReturnCont (env : CrateEnv) (frames : List CallFrame) (retVal : MirVal)
    (finalVal : MirVal) : Prop :=
  match frames with
  | [] => retVal = finalVal
  | frame :: restFrames =>
    ∀ (mem : MemState),
      SafeFrom env
        { curBody := frame.callerBody
          locals := updateLocal frame.callerLocals frame.dst.index (some retVal)
          mem := mem
          block := frame.returnTarget.index
          stmtIdx := 0
          frames := restFrames }
        finalVal
```

The master soundness theorem
[`evalSymState_sound`](InterproceduralConditionalMir.lean#L2515-L3004) handles
two interprocedural call plan constructors in `TransPlan`:

| Dimension | Mode A: Symbolic Call Inlining (`TransPlan.callInline`) | Mode B: Modular Callee Summaries (`TransPlan.callSummary`) |
| :--- | :--- | :--- |
| **User annotation burden on private helpers** | **Zero:** private helper `add` (`isPublic = false`) needs no `Pre`, `Post`, or summary ([`prove_guarded_crate_modeA`](InterproceduralConditionalMir.lean#L3462-L3480)) | Requires a conditional spec `MirLang.SpecOn Pre Post` ([`addBody_verified_specOn`](InterproceduralConditionalMir.lean#L3516-L3550)) and `CalleeSummary` ([`addSummary_sound`](InterproceduralConditionalMir.lean#L3565-L3586)) |
| **Kernel `rfl` reduction on `double_guarded(x)`** | [`evalSymState_doubleGuarded_modeA_rfl`](InterproceduralConditionalMir.lean#L3368-L3378) | [`evalSymState_doubleGuarded_modeB_rfl`](InterproceduralConditionalMir.lean#L3615-L3625) (definitionally equal to Mode A by `rfl` in [`evalSymState_doubleGuarded_modeA_eq_modeB`](InterproceduralConditionalMir.lean#L3631-L3635)) |
| **Summary soundness bridge** | Not needed (`summaries = []`) | [`summaryEntrySound_of_evalSymState`](InterproceduralConditionalMir.lean#L3038-L3069) proves `SummaryEntrySound` from `evalSymState` in 20 lines; [`bogusUnconditionalAddSummary_not_sound`](InterproceduralConditionalMir.lean#L3828-L3875) rejects an unconditional summary for `add` |
| **Top-level crate theorem** | [`PublicAdmittedCrateTheorem`](InterproceduralConditionalMir.lean#L3219-L3225) (checks `c.publicFns` while resolving calls against full `c.toEnv`) | [`ModularAdmittedCrateTheorem`](InterproceduralConditionalMir.lean#L3230-L3235) (verifies all `c.fns` against their respective `f.pre` and `f.specs`, [`prove_modular_crate_modeB`](InterproceduralConditionalMir.lean#L3780-L3815)) |

Because both Mode A and Mode B execute against the same call-stack `MirMachine`
in `trusted/` and the same `evalSymState` evaluator in `theory/`, Anneal can
default to Mode A (`callFuel > 0`) for unannotated private helpers and switch to
Mode B whenever a helper carries an explicit contract or is recursive, with zero
summary machinery in the TCB.

## Boundaries

1. **Trait implementations of exported/foreign traits on completely unexposed
   private types (Category 4d) — conservative over-approximation:**
   Rule 4 of `is_external_entry_fn` marks `<UnexportedPrivStruct as
   PubTrait>::cat4_trait_req` as an external entry point whenever `PubTrait` is
   foreign or `Level::Reachable`, even if `UnexportedPrivStruct` is never
   returned via `impl PubTrait`, coerced to `dyn PubTrait`, or passed to a
   generic function. Excluding such dead trait `impl`s would require whole-crate
   MIR scanning for `PointerCoercion::Unsize` and generic instantiations;
   treating every implementation of a public or foreign trait as a public
   contract obligation is sound and conservative.
2. **Closures escaping via function-pointer or `dyn Fn` coercion — not covered
   by `Level::ReachableThroughImplTrait` alone:**
   Rule 5 of `is_external_entry_fn` identifies closures that escape via RPIT
   (`impl Fn(...)`) using `Level::ReachableThroughImplTrait` gated by
   `is_external_entry_fn(tcx, root_owner)`. If a closure inside a public
   function escapes instead by coercion to a bare `fn(...)` pointer or `&dyn
   Fn(...)` trait object without an `OpaqueTy` in the return signature, its
   `FnOnce::call_once` / `Fn::call` body is reached via vtable or indirect
   function-pointer call rather than `Level::ReachableThroughImplTrait`.
   Indirect and dynamic-dispatch calls (`TerminatorKind::Call` where `func` is a
   non-constant `Operand` or a `Virtual` instance) are **not examined** in
   `InterproceduralConditionalMir.lean`, which resolves static callee names in
   `CrateEnv`.
3. **Fuel-bounded recursion and mutual recursion in `CompileAdmitted` and Mode A
   inlining:**
   Both `CompileAdmitted env fuel body` and Mode A `computePlan` use explicit
   `Nat` fuel bounds. For non-recursive call graphs (DAGs), finite fuel is
   exact; for recursive or mutually recursive functions, Mode A symbolic
   inlining cannot unroll unboundedly and must yield to Mode B modular
   summaries (`callFuel = 0`) paired with an inductive termination or rank
   argument.

## Evidence

### Preserved Package Artifacts

- **[`ConditionalCrateVerification.lean`](ConditionalCrateVerification.lean)**
  (`3,517` lines, SHA-256
  `7ca6ddc28189eb03fa389526114e11705f2cbf755888498ce905e990d09af2f4`):
  Standalone Lean `v4.34.1` mechanization of the 3-level calling-condition
  taxonomy (`initMirState`, `MirLang.SpecOn`, `MirLang.WellFormedOn`),
  impossibility of unconditional `MirLang.Spec` (`not_le_spec_of_not_defined`,
  `addBody_not_le_spec`), conditional `FunctionalTranslation` bridges
  (`funcSem_le_specOn`, `π_func_specOn_le`), spine-preserving `evalPureCallee2`,
  `CalleeSummaryVerified`, multi-function crates (`prove_guarded_crate`,
  `prove_mixed_crate`), and Mode 2 unwinding semantics (`MirLangUnwind`,
  `addBody_satisfies_ensuresUnwind`, `addBody_satisfies_wellFormedUnwind`).
- **[`InterproceduralConditionalMir.lean`](InterproceduralConditionalMir.lean)**
  (`4,149` lines, SHA-256
  `b09d995045d58b9f91f30838364bb82adffa995e84b7a2641ff5f1d68c2d8374`):
  Standalone Lean `v4.34.1` mechanization of call-stack `Terminator.call` and
  `Terminator.return_` over `CrateEnv` and `MirState.frames : List CallFrame`,
  Layer 1B structural health theorems (`mirMachine_totalStep`,
  `mirMachine_inhabitedDemonic`, `mirMachine_non_vacuity_at_every_depth`),
  transitive `CompileAdmitted` and executable `checkCompileAdmitted` over
  `requiredConsts` and `mentionedItems`
  (`compileAdmitted_of_checkCompileAdmitted`), dead-branch PME negative control
  (`deadBranchBadCaller_not_compileAdmitted`,
  `deadBranchBadCaller_runtime_verified`), and unified dual-mode symbolic
  evaluation (`evalSymState_sound`, `ReturnCont`, Mode A
  `prove_guarded_crate_modeA`, Mode B `prove_modular_crate_modeB`, and
  `evalSymState_doubleGuarded_modeA_eq_modeB`).
- **[`vis_probe/src/lib.rs`](vis_probe/src/lib.rs)** (`261` lines, SHA-256
  `87769081314d234bc7d4034833a11ab87eb0d7b9d36502cc205c6189a33ddbb0`):
  7-category Rust visibility test fixture covering top-level items, private and
  re-exported modules, inherent methods on public/private/leaked structs, trait
  implementations (direct, RPIT `impl Trait`, `&'static dyn Trait`, unexported
  private structs, private traits), generic functions and private helpers called
  by generics, FFI roots (`#[no_mangle]`, `#[export_name]`, `main`), and
  closures.
- **[`vis_probe/driver.rs`](vis_probe/driver.rs)** (`183` lines, SHA-256
  `3df79cd45b7506cf9f2c2d01995687805b74026d2a21716b1d81278d8279789e`):
  In-process `rustc_driver` probe inspecting `tcx.mir_keys(())`,
  `tcx.hir_body_owners()`, `tcx.local_visibility`,
  `tcx.effective_visibilities(())` at all four `Level`s,
  `tcx.reachable_set(())`, `tcx.codegen_fn_attrs`, `tcx.entry_fn(())`, and
  `tcx.collect_and_partition_mono_items(())`.
- **[`vis_probe/driver_lib.txt`](vis_probe/driver_lib.txt)** (`71` lines,
  SHA-256
  `6e0931ebef4b4ea6899b608c4ea2a63dfa305d46f074ad63ae0e06cd5e43a136`) and
  **[`vis_probe/driver_bin.txt`](vis_probe/driver_bin.txt)** (`71` lines,
  SHA-256
  `d5fc8856f5d2c123623adf75484f8c3d97615f2c3ce17592c33cc34dfe2aacbf`):
  Recorded outputs of `vis_probe/driver.rs` on `vis_probe/src/lib.rs` with
  `--crate-type=lib` and `--crate-type=bin`.

### Primary Upstream Sources

- **`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`:**
  - [`compiler/rustc_mir_transform/src/lib.rs#L325-L358`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L325-L358):
    `mir_keys` query implementation.
  - [`compiler/rustc_middle/src/hir/mod.rs#L37-L115`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/mod.rs#L37-L115)
    and
    [`compiler/rustc_middle/src/hir/map.rs#L1265-L1324`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/map.rs#L1265-L1324):
    `ModuleItems`, `hir_body_owners`, and `local_visibility`.
  - [`compiler/rustc_middle/src/middle/privacy.rs#L20-L289`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/middle/privacy.rs#L20-L289),
    [`compiler/rustc_resolve/src/effective_visibilities.rs#L27-L202`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_resolve/src/effective_visibilities.rs#L27-L202),
    and
    [`compiler/rustc_privacy/src/lib.rs#L510-L828`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs#L510-L828),
    [`#L1809-L1855`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs#L1809-L1855):
    `EffectiveVisibilities`, `Level`, `EmbargoVisitor`, and the
    `krate.opaques()` `FIXME` at `#L1841-L1846`.
  - [`compiler/rustc_passes/src/reachable.rs#L177-L209`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs#L177-L209)
    and
    [`#L411-L524`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs#L411-L524):
    `reachable_set` implementation.
  - [`compiler/rustc_monomorphize/src/collector.rs#L1364-L1389`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1364-L1389)
    and
    [`#L1751-L1778`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1751-L1778):
    `collect_items_of_instance` (`required_consts`, `mentioned_items`) and
    `RootCollector::is_root`.
  - [`compiler/rustc_middle/src/mir/pretty.rs#L326-L329`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs#L326-L329),
    [`#L679-L722`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs#L679-L722),
    and
    [`compiler/rustc_middle/src/mir/syntax.rs#L696-L784`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L696-L784):
    `write_mir_pretty`, `write_mir_sig`, `TerminatorKind::Call`, and
    `TerminatorKind::Return`.

## Revalidation

1. **Revalidating the Lean `v4.34.1` Mechanizations:**
   Run the Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel
   with asynchronous elaboration and kernel type-checking skip disabled on both
   preserved files from the package directory:

   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false ConditionalCrateVerification.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false InterproceduralConditionalMir.lean
   ```

   Both commands must exit with status `0`, zero warnings, and `#print axioms`
   outputs depending only on subsets of `{propext, Quot.sound}` (with zero
   `sorryAx`, zero `Lean.ofReduceBool`, and zero `Classical.choice`).

2. **Revalidating the `rustc_driver` Visibility Probe on a Newer Rust
   Toolchain:**
   Compile [`vis_probe/driver.rs`](vis_probe/driver.rs) against the target
   toolchain's `rustc_private` sysroot and execute it on
   [`vis_probe/src/lib.rs`](vis_probe/src/lib.rs) in both library and binary
   modes:

   ```console
   SYSROOT=$(rustc --print sysroot)
   rustc --edition=2021 vis_probe/driver.rs \
     --sysroot "$SYSROOT" \
     -L "$SYSROOT/lib" \
     -o /tmp/vis_probe_driver
   LD_LIBRARY_PATH="$SYSROOT/lib" /tmp/vis_probe_driver \
     --edition=2021 --crate-type=lib vis_probe/src/lib.rs > /tmp/driver_lib.txt
   LD_LIBRARY_PATH="$SYSROOT/lib" /tmp/vis_probe_driver \
     --edition=2021 --crate-type=bin vis_probe/src/lib.rs > /tmp/driver_bin.txt
   diff -u vis_probe/driver_lib.txt /tmp/driver_lib.txt
   diff -u vis_probe/driver_bin.txt /tmp/driver_bin.txt
   ```

   Also inspect `compiler/rustc_privacy/src/lib.rs` around `krate.opaques()` to
   check whether the upstream `FIXME` on `Level::ReachableThroughImplTrait` or
   trait-impl visibility propagation in `EmbargoVisitor` has changed.
