# `rustc` `PromoteTemps` Infallibility (RFC 3027), Zero-Sized `&'static mut` Promotion vs. `UnsafeCell` Rejection, and `CheckConstItemMutation` Destructor Asymmetry

## Summary

Constant promotion in `rustc` (`PromoteTemps`, running during `mir_promoted` immediately after `RequiredConstsVisitor`) extracts immutable—and strictly zero-sized mutable array—borrows of compile-time-evaluable temporary subtrees into promoted `'static` allocations (`promoted[i]`), while runtime-mir linting (`CheckConstItemMutation`, running earlier during `mir_built`) warns when a `const` item temporary (`LocalInfo::ConstRef`) is mutated without an observable destructor. Across four pinned compiler revisions (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` `1.98.0-nightly`, `940498dad7cb35a753a7cce104ab510b414e84de`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` `1.102.0-nightly`, and `ce66487ebbd7541212d22d01c39a808057d69f1f`), live differential compilation and Miri execution (30 empirical test cases, 21 saved MIR dumps), and a pure kernel-checked Lean `v4.34.1` mechanization (`1,351` lines, `367` Lean theorem declarations across `39` top-level `theorem` keywords, `0` warnings, `0` `Classical.choice`, `0` `_unsafe_rec`), this investigation establishes three primary findings:

1. **RFC 3027 Infallible Implicit Promotion with Place-Borrow vs. Value-Copy Indexing Split and Dead-Branch Panics Kept in Parent MIR**: `PromoteTemps` (`compiler/rustc_mir_transform/src/promote_consts.rs`) splits promotion into `Collector` (`TempState::{Undefined, Defined, Unpromotable, PromotedOut}` enforcing single-assignment temporary trees) and `Validator` (requiring `NeedsDrop == false`, infallible integer `Div`/`Rem` guards rejecting `1 / 0` and `INT_MIN / -1` even under `#![allow(unconditional_panic)]` / `#![allow(arithmetic_overflow)]`, `#[rustc_promotable]` for calls outside `const`/`static` `promotion_safe_blocks`, and `HasMutInterior == false` for shared references). When a checked arithmetic temporary has multiple uses (value + overflow flag, `AddWithOverflow`), `Promoter` keeps the original checked computation (`keep_original = true`) in the parent MIR while hoisting the wrapping constant into `promoted[0]`. Crucially, indexing inside a value-copy temporary (`&({ [10u32, 20u32][2] })`) is validated by `Validator::validate_place` (`idx < len`) and rejected (`E0515`), whereas an out-of-bounds place-borrow (`&([10u32, 20u32][2])`) validates only the base `[10u32, 20u32]` (`promoted_count_after = 1`) and leaves `assert(Lt(copy _3, const 2_usize))` plus `&(*_5)[_3]` in the parent function, preserving runtime panic semantics (`ce_copy_index_oob_rejected_vs_place_index_base_promoted`). Similarly, plain `const fn` calls in `&cf()` fail implicit promotion (`E0515`), whereas `&const { cf() }` lowers via an inline `AnonConst` (`f::{constant#0}`) evaluated through `RequiredConstsVisitor` + post-monomorphization evaluation (PME), which rejects dead-branch panics like `&const { 1u32 / 0u32 }` under `--emit=obj` (`E0080`) while skipping PME under `--emit=metadata` (`rc = 0`).

2. **Zero-Sized `&'static mut [T; 0]` Promotion into Read-Only Static Memory Is Sound Under Miri Stacked Borrows and Tree Borrows, Whereas `&UnsafeCell<()>` Is Still Rejected**: `Collector::visit_local` (`promote_consts.rs:131-136`) explicitly allows `MutatingUseContext::Borrow` on temporaries, and `Validator::validate_ref` (`promote_consts.rs:400-430`) permits `BorrowKind::Mut { kind: Default | TwoPhaseBorrow }` **exclusively** for syntactically zero-length arrays `ty::Array(_, 0)`—rejecting `&mut ()` despite `size_of::<()>() == 0`. Both `&mut []` (`[u32; 0]`, unsized to `&'static mut [u32]`) and `let b: &'static mut [u32; 0] = &mut []` promote into read-only static allocations (`promoted[i]`) and execute cleanly (`rc = 0`) under both Miri Stacked Borrows (`sb_reborrow` early-returns at `size == Size::ZERO` before allocation mutability checks) and Miri Tree Borrows (`tb_reborrow` constructs an empty `DedupRangeMap` performing `0` write checks), even with two simultaneous `StrongProtector`-guarded mutable parameters (`a.split_at_mut(0)`). Any nonzero write through that promoted pointer (`*a.as_mut_ptr() = 1`) triggers immediate out-of-bounds UB in both Miri SB and TB (`rc = 1`). Meanwhile, `HasMutInterior` enforces **value-based** structural inspection (`qualifs.rs:84-137`): `&Option::<UnsafeCell<()>>::None` promotes (`HasMutInterior == false`), while `&UnsafeCell::new(())` and `&Some(UC)` fail promotion (`E0515`) even at size `0`—preventing unsynchronized interior writes into read-only static memory (`zst_mut_borrow_promoted_rodata_sound` with zero axioms).

3. **`CheckConstItemMutation` Exhibits an Intra-Pass Destructor Asymmetry Between Direct Writes (`visit_statement`) and `&mut self` Method Calls (`visit_rvalue`)**: `CheckConstItemMutation` (`compiler/rustc_mir_transform/src/check_const_item_mutation.rs`) flags mutations against `LocalInfo::ConstRef` temporaries created from `const` items. Commit `940498dad7cb35a753a7cce104ab510b414e84de` replaced `adt.has_dtor` in `is_const_item_without_destructor` (`check_const_item_mutation.rs:63-74`) with `ty.needs_drop`, suppressing false positives on wrapper types with nested `Drop` fields (`Outer { inner: Inner }`: `1.98.0-nightly` emitted 2 warnings; `1.102.0-nightly` suppresses direct `O.inner.val = 42` while retaining `&mut self` warnings). However, across **both** `1.98.0-nightly` and `ce66487` `HEAD`, `visit_statement` calls `is_const_item_without_destructor` while `visit_rvalue` (`check_const_item_mutation.rs:134` in `1.98.0`, `:144` in `1.102.0`/HEAD) calls `is_const_item` **without** checking destructors. Consequently, on `const C_DIRECT: DropLogger`, direct assignment `C_DIRECT.val = 10` emits `0` warnings whereas `C_DIRECT.set(15)` (`&mut self` method call) emits a false-positive `taking a mutable reference to a const item` warning—even though MIR lowers both by copying `const C_DIRECT` into a local and dropping it at statement end, empirically accumulating `OBSERVED_DROPS=75` (`10 + 15 + 50`). Meanwhile, dereferenced raw pointers (`*c_ptr.ptr = 7`) skip linting via `PlaceElem::Deref` (`should_lint_const_item_usage`), and explicit `{ let r = &mut C; r.val = 50; }` warns once and still observes `EXPLICIT_DROPS=50`.

| Focus Area | Upstream Mechanism | Empirical Verification (`1.98.0` + Miri + `1.102.0` Parity) | Lean `v4.34.1` Theorem | Anneal / Trusted Boundary Effect |
| --- | --- | --- | --- | --- |
| RFC 3027 infallible promotion | `Collector` + `Validator` (`NeedsDrop=false`, total ops, `#[rustc_promotable]`, `keep_original`) | `div_by_zero`, `rem_by_zero`, `i32::MIN / -1`, `copy_oob` -> `E0515`; `place_oob` & dead `200u8 + 200u8` -> `rc=0` (`promoted=1`) | `validator_implies_ctfe_infallible`, `promoteTemps_infallible_preserves_semantics_iff` | Promoted bodies loaded by Anneal `rustc-capture` (`promoted_mir`) are CTFE-total & drop-free |
| Inline `const { ... }` vs. implicit promotion | `AnonConst` + `RequiredConstsVisitor` (`mir_promoted` before `PromoteTemps`) + PME | `&cf()` -> `E0515`; `&const { cf() }` -> `rc=0`; dead `&const { 1/0 }` -> `E0080` (`--emit=obj`) / `rc=0` (`--emit=metadata`) | `validateLeaf` (`constFnCall` `inlineConst` branch) + `ctfeEvalLeaf_ok_of_validate` | `const { ... }` shifts infallibility failure from promotion rejection to PME (`mir_drops_elaborated`) |
| `&'static mut []` ZST promotion | `MutatingUseContext::Borrow` + `validate_ref` `ty::Array(_, 0)` | `&mut []` (`[u32; 0]` / `[u32]`) & `split_at_mut(0)` -> `rc=0` SB & TB; `&mut ()` -> `E0515`; write -> Miri `rc=1` | `zst_mut_borrow_promoted_rodata_sound` (`[]` axioms), `dual_protected_zst_mut_borrows_rodata_sound` | Justifies zero-sized `.unit` / empty-slice `&mut` pointing to `AllocMutability::Immutable` rodata |
| `&UnsafeCell<()>` at size `0` | Value-based `HasMutInterior` (`!adt.is_unsafe_cell()`, `!IS_CLEARED_ON_MOVE`) | `&None::<UnsafeCell<()>>` -> `rc=0`; `&UnsafeCell::new(())` & `&Some(...)` -> `E0515` | `qualifHasMutInterior_optionNone_unsafeCellZst_false`, `validateRef_mut_syntactic_conservatism_and_unsafecell_zst_witness` | Guarantees promoted shared allocations remain `.readOnly` even for zero-sized `UnsafeCell` |
| `CheckConstItemMutation` asymmetry | `visit_statement` (`needs_drop` / `has_dtor`) vs. `visit_rvalue` (`is_const_item`) | `C_DIRECT.val = 10` (0 warn), `C_DIRECT.set(15)` (`&mut` warn), `OBSERVED_DROPS=75`; `Outer` 2->1 warn delta | `constMutation_unobservable_iff_no_needsDrop`, `checkConstItemMutation_visitRvalue_false_positive_witness`, `lintRepaired_exact_soundness_and_completeness` | `CheckConstItemMutation` runs only in `mir_built` (`LocalInfo` cleared post-analysis); diagnostic-only |

### Key Takeaways

- **Implicit Promotion Does Not Inspect Borrow Projections Beyond `!Deref`**: A place-borrow of a promotable base (`&([10u32, 20u32][2])`) splits at the base array: `[10u32, 20u32]` moves into `promoted[0]`, while the index bounds check (`assert(Lt(copy _3, const 2_usize))`) stays live in parent MIR; value-copy indexing (`&({ [10u32, 20u32][2] })`) validates `idx < len` and refuses promotion.
- **0-Byte Mutable Promotion Relies on Byte-Empty Miri Contracts, Not Mutability**: `&'static mut [u32; 0]` points to read-only promoted static memory; Stacked Borrows (`size == Size::ZERO`) and Tree Borrows (empty `DedupRangeMap`) permit unlimited aliased `StrongProtector` mutable reborrows iff `0` bytes are read or written.
- **Promotability of `&mut ()` vs. `&mut []` and `&UnsafeCell<()>` vs. `&Option::<UnsafeCell<()>>::None` Are Orthogonally Gated**: Syntactic `validate_ref` whitelists `ty::Array(_, 0)` (excluding `&mut ()`), while value-based `HasMutInterior` whitelists uninhabited/inactive enum variants (allowing `None`, rejecting `UnsafeCell<()>`).
- **Pre-`940498dad7cb` vs. Post-`940498dad7cb` `CheckConstItemMutation` Closed Nested-Field Drop Bugs Only in `visit_statement`**: Direct field mutations to `Outer { inner: Inner }` stopped warning in `1.102.0-nightly`, but `&mut self` method calls on *every* `Drop` `const` item still trigger `CONST_ITEM_MUTATION` on `HEAD` (`ce66487`) due to the asymmetric `visit_rvalue` call.
- **`anneal-rustc-capture` Post-Cleanup Isolation**: `PromoteTemps` populates `body.promoted`, `RequiredConstsVisitor` populates `body.required_consts`, and `run_analysis_to_runtime_passes` clears `LocalInfo` before optimized `promoted_mir` capture (`Trusted.MirSemantics.deinitMovedPlace = true`), cleanly isolating Anneal from pre-borrowck `LocalInfo::ConstRef` diagnostics.

*Basis:* Upstream `rust-lang/rust` revisions (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `940498dad7cb35a753a7cce104ab510b414e84de`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `ce66487ebbd7541212d22d01c39a808057d69f1f`), `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`; empirical results in `support/probe_results.json`; mechanized proofs in `support/PromoteTempsInfallibleZstMutAndConstMutationSoundness.lean` (`support/lean_check_receipt.json`).

---

## Applicability

This report establishes primary-source, empirical, and mechanized ground truth for the pinned subjects enumerated in `REPORT.json` as of `2026-11-22`:

| Subject | Repository | Pinned Commit / Version | Role in Study |
| --- | --- | --- | --- |
| `rustc` `1.98.0-nightly` + `Miri 0.1.0` | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) | Local live compiler & Miri execution baseline (`PromoteTemps`, pre-`940498dad7cb` `CheckConstItemMutation`, SB, TB) |
| `needs_drop` lint fix | `rust-lang/rust` | `940498dad7cb35a753a7cce104ab510b414e84de` (`2026-08-24`) | Commit fixing `is_const_item_without_destructor` (`adt.has_dtor` -> `ty.needs_drop`) |
| `rustc` `1.102.0-nightly` | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`) | Target nightly baseline for cross-version MIR/lint parity and primary source line mapping |
| Upstream `HEAD` snapshot | `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` (`2026-11-22`) | Latest `rust-lang/rust` check confirming 0-line source diff from `3ef0c22cd` in `promote_consts.rs` and `check_const_item_mutation.rs` |
| The Rust Reference | `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`2026-11-17`) | Normative reference rules for temporary scopes, lifetime extension, constant promotion, and constant items |
| The Rust RFC Book | `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (`2026-11-14`) | RFC 3027 (`text/3027-infallible-promotion.md`) & RFC 1414 (`text/1414-rvalue_static_promotion.md`) design contracts |
| Anneal Verified MIR | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) | Downstream consumer (`Trusted.MirAst`, `Trusted.MirSemantics`, `TrustedBoundary`, `anneal-rustc-capture`) |
| Lean 4 Kernel | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Proof assistant & kernel (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) |

### Target Environments and Downstream Consumers

- **Rust Compiler Verification and Anneal Integration**: Applicable to pre-borrowck MIR passes (`mir_built` and `mir_promoted`) and post-cleanup promoted body decoding (`promoted_mir`), specifically informing `joshlf/anneal`'s `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/audit/TrustedBoundary.lean`.
- **Host / Architecture**: All live `rustc` and Miri probes executed on `x86_64-unknown-linux-gnu` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`), cross-checked against recorded `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` baseline results (`support/baseline_1_102_3ef0c22cd.json`). All 8 shared baseline cases show `true` parity in `support/probe_results.json`.
- **Complementary Corpus Coverage (`unsupported` / Complementation)**: Post-cleanup `promoted_mir` constant decoding and allocation layout semantics are analyzed in the existing companion corpus report `rustc-postcleanup-mir-unevaluated-consts-promoted-bodies-and-alloc-decoding`; the present report specifically isolates pre-borrowck `PromoteTemps` qualification/extraction, Miri SB/TB zero-sized `'static mut` admissibility, and `CheckConstItemMutation` lint asymmetry.

### Negative-Space Declarations

- **`not examined`**: Downstream LLVM IR / Cranelift codegen lowering of promoted allocations beyond `--emit=obj` vs. `--emit=metadata` exit/diagnostic behavior, macro-generated `const` patterns spanning multiple crates, CTFE heap interning flags (`intern.rs`), and experimental feature gates (`#![feature(generic_const_exprs)]`, `#![feature(const_eval_select)]`) were `not examined`.
- **`unknown`**: It is `unknown` whether an unmerged upstream PR after `ce66487ebbd7541212d22d01c39a808057d69f1f` (`2026-11-22`) modifies `visit_rvalue` in `check_const_item_mutation.rs` to call `is_const_item_without_destructor`, or whether Rust's next edition changes `CONST_ITEM_MUTATION` lint severity.
- **`known not to apply`**: The ZST `'static mut` Miri soundness guarantee (`sb_reborrow` / `tb_reborrow` on read-only static memory) is `known not to apply` to any nonzero-sized type (`size > 0`) or any nonzero byte read/write (e.g., `*a.as_mut_ptr() = 1` produces immediate UB even though `a: &'static mut [u32]` was legally promoted). Likewise, `PromoteTemps` infallibility guarantees are `known not to apply` to explicit `const { ... }` / `static` items where `ConstQualifs` and `RequiredConstsVisitor` permit fallible operations whose panic only surfaces at CTFE (`E0080`).
- **`unsupported`**: `Trusted.MirAst` / `anneal-rustc-capture` does not extract pre-borrowck `LocalInfo::ConstRef` metadata (because `run_analysis_to_runtime_passes` clears `local_info` before runtime MIR capture) and does not natively run Miri borrow trackers; hence, proving promoted ZST `&mut` safety for Anneal relies on connecting `Allocation::mutability = .readOnly` (immutable static memory) with the Miri zero-byte reborrow theorem established here.

*Basis:* `REPORT.json`, `support/pin_receipt.json`, `support/probe_results.json`, `support/baseline_1_102_3ef0c22cd.json`, and primary source diffs across `14210df0e2`, `940498dad7cb`, `3ef0c22cdb`, and `ce66487ebb`.

---

## Findings

### Pipeline Placement and Pass Ordering (`mir_built` -> `mir_const_qualif` -> `mir_promoted`)

By primary-source inspection of `compiler/rustc_mir_transform/src/lib.rs` (anchored at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`: `364-696, 840-855`), `CheckConstItemMutation` and `PromoteTemps` operate in strictly separated compiler queries:

1. **`mir_built` (`lib.rs:395-433`)**: Runs `CheckConstItemMutation` at `lib.rs:423` immediately before `simplify::SimplifyCfg::Initial` (`lib.rs:427`). At this stage, AST-lowering (`compiler/rustc_mir_build/src/builder/expr/as_temp.rs`) has tagged temporaries materialized from `const` items with `LocalInfo::ConstRef { def_id }`, so `CheckConstItemMutation` sees pre-inlining uses before CFG simplification or constant propagation eliminates or merges them.
2. **`mir_const_qualif` (`lib.rs:364-392`)**: Computes body-level `ConstQualifs` (`has_mut_interior`, `needs_drop`, `custom_eq`, `precise_live_drops`) over `mir_built` bodies for `const`/`static`/`const fn` evaluation gating (`check_consts/qualifs.rs`).
3. **`mir_promoted` (`lib.rs:436-498`)**: Clones `mir_built` and executes two ordered passes before borrow checking (`mir_borrowck`):
   - First, `RequiredConstsVisitor::compute_required_consts` (`lib.rs:477`, implemented in `compiler/rustc_mir_transform/src/required_consts.rs:1-24`) walks `traversal::reverse_postorder(&body)`—visiting **all reachable basic blocks in the MIR CFG, including statically dead `if false { ... }` branches**—and records every encountered `Const::Unevaluated` (such as inline `const { ... }` `AnonConst`s) into `body.required_consts`.
   - Second, `PromoteTemps` (`lib.rs:484`, implemented in `compiler/rustc_mir_transform/src/promote_consts.rs`) runs `Collector` + `Validator` + `Promoter` (`promote_candidates`) to populate `body.promoted` (`IndexVec<Promoted, Body<'tcx>>`) with extracted promoted constant bodies and rewrites parent uses to `Rvalue::Use(Operand::Constant(Const::Unevaluated(... promoted: Some(p))))`. Note that promoted bodies themselves recursively inherit `required_consts` from statements moved into `promoted[p]` (`promote_consts.rs:851, 971-973`).
4. **`mir_drops_elaborated_and_const_checked` (`lib.rs:546-604`), `run_analysis_to_runtime_passes` (`lib.rs:608-696`), and `promoted_mir` (`lib.rs:840-855`)**: Evaluates `required_consts`, runs drop elaboration, and strips analysis-only metadata (`local_info` is cleared at `lib.rs:693-695`). Downstream Anneal extraction (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/rustc-capture/src/driver.rs:1-152`) consumes post-cleanup `optimized_mir` / `promoted_mir`, meaning Anneal observes already-promoted `promoted[i]` bodies rather than `LocalInfo::ConstRef`.

*Cross-version note (`14210df0e` vs. `3ef0c22cd` vs. `ce66487eb`)*: Diff inspection confirms **0 source line differences** in both `promote_consts.rs` and `check_const_item_mutation.rs` between `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`) and `ce66487ebbd7541212d22d01c39a808057d69f1f` (`HEAD`). Between `14210df0e27` (`1.98.0-nightly`) and `3ef0c22cdb`, `promote_consts.rs` underwent cleanups (`PassPolicy::Required`, `ProjectionElem::PhantomDeref`, `!tcx.is_foreign_item(did)` static guard, `allow_const_fn_promotion` field naming, and `AnonConstKind::NonTypeSystemInline`), while `TempState`, `Collector`, `Validator` infallibility predicates, `ty::Array(_, 0)` mutable promotion, and `Promoter` semantics remained identical.

---

### RFC 3027 Infallible Implicit Promotion (`PromoteTemps`): Collector, Qualifs, and Validator

Per The Rust Reference `r[destructors.scope.const-promotion]` (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/destructors.md:379-383`) and RFC 3027 (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/3027-infallible-promotion.md:1-210`), implicit promotion (`let r: &'static T = &expr;`) must **never introduce a compile-time evaluation failure on code that would execute cleanly—or avoid executing inside a dead branch—without promotion**. In contrast, explicitly extending `static`/`const` initializers (subject to `promotion_safe_blocks`) and inline `const { ... }` blocks opt into compile-time evaluation errors (`E0080`).

#### `TempState` Lattice and Single-Assignment Tree Discipline (`Collector`)

`promote_consts.rs:73-156` models candidate temporaries using a four-state lattice (`TempState`):

```text
Undefined --(store / callDest)--> Defined { loc, uses: 0, valid: false }
Defined   --(mutBorrow / sharedBorrow / nonMutRead)--> Defined { loc, uses: uses + 1, valid }
Defined   --(store / callDest / otherMutUse)-------> Unpromotable   (absorbing sink)
PromotedOut --(any active use)----------------------> Unpromotable
(Drop / StorageLive / StorageDead / arg / userVar) -> state invariant (no-op)
```

- **Local eligibility (`promote_consts.rs:106-110`)**: `Collector::visit_local` skips all locals except compiler temporaries (`!is_arg && !is_user_var`, covering `_0` return slot and compiler temporaries).
- **Drop and storage immunity (`promote_consts.rs:115-145`)**: `Drop` and non-uses (`StorageLive`, `StorageDead`, annotations) preserve `TempState`.
- **Single-assignment invariant**: A temporary initialized more than once transitions to `Unpromotable` and remains absorbed there regardless of subsequent statements.
- **Mutable borrow admission in `Collector` (`promote_consts.rs:130-141`)**: Crucially, `MutatingUseContext::Borrow` increments `uses` on a `Defined` temporary rather than marking it `Unpromotable`. Deferring mutability rejection from `Collector` to `Validator::validate_ref` enables `&mut []` ZST promotion without duplicating control-flow analysis.

In Lean (`support/PromoteTempsInfallibleZstMutAndConstMutationSoundness.lean:75-252`), `collectorVisitLocal` and `collectorRunEvents` mechanize this transition relation, establishing:
- `collector_ignores_non_temps`: `LocalKind.arg` and `LocalKind.userVar` remain invariant across arbitrary event lists.
- `collector_drop_and_storage_noop`: `dropUse` and `storageMarker` are identity transitions.
- `collector_unpromotable_absorbing`: `.unpromotable` is an absorbing sink (`collectorRunEvents k .unpromotable evs = .unpromotable`).
- `collector_double_init_unpromotable`: any two `store`/`callDest` initializations force `.unpromotable`.
- `collector_mutBorrow_increments_uses` and `collector_defined_after_single_init`: preserving `.defined` across any suffix event list implies no re-assignment or non-borrow mutation occurs (`activeReadsOrBorrowsOnly evs = true`).

#### Value-Based vs. Type-Based `ConstQualifs` (`HasMutInterior`, `NeedsDrop`)

`promote_consts.rs` queries value-based `ConstQualifs` from `compiler/rustc_const_eval/src/check_consts/qualifs.rs` (`lines 84-162, 227-287`) rather than relying solely on coarse outer type traits:

| Qualifier | `IS_CLEARED_ON_MOVE` | `ALLOW_PROMOTED` | `is_structural_in_adt_value` | Fallback on Union / Non-Structural ADT / Operand (`qualifs.rs:227-287`) |
| --- | --- | --- | --- | --- |
| `HasMutInterior` (`qualifs.rs:84-137`) | `false` | `false` (`!ALLOW_PROMOTED`: once tainted, stays tainted even when promoted sub-parts appear) | `!adt.is_unsafe_cell()` | Type-based `in_any_value_of_ty` (marks `UnsafeCell<T>` and unions containing cells interior-mutable) |
| `NeedsDrop` (`qualifs.rs:144-162`) | `true` (cleared when value moved out, e.g. variant overwrite or partial move) | `true` (promoted parts don't drop) | `!adt.has_dtor(tcx)` | Type-based `ty.needs_drop(tcx, typing_env)` |

This structural distinction explains a subtle empirical boundary verified in `support/probe_results.json`:

1. **`&UnsafeCell::new(())` (`unsafecell_zst_not_promoted`)**: Fails with `rc = 1`, `error[E0515]`, `promoted_count_after = 0`. Even though `size_of::<UnsafeCell<()>>() == 0`, `UnsafeCell` is non-structural in `HasMutInterior` (`!adt.is_unsafe_cell()` is `false`), setting `HasMutInterior = true` and failing `Validator::validate_ref` for shared borrows.
2. **`&Option::<UnsafeCell<()>>::None` (`none_unsafecell_zst_promoted`)**: **Compiles and promotes (`rc = 0`, `promoted_count_after = 1`)!** `Option` is not `UnsafeCell`, so `in_rvalue` traverses `AggregateKind::Adt` field-by-field (`0` fields in `None`), leaving `HasMutInterior = false`.
3. **`&Some(UC)` (`const UC: UnsafeCell<()>` in `some_unsafecell_zst_not_promoted`)**: **Rejected (`rc = 1`, `E0515`, `promoted_count_after = 0`)** because the `Some` payload temporary carries `HasMutInterior = true` into the aggregate field.

Mechanized in Lean (`qualifHasMutInterior_optionNone_unsafeCellZst_false`, `qualifHasMutInterior_unsafeCellZst_true`, `qualifHasMutInterior_optionSome_unsafeCellZst_true`, and `validateRef_mut_syntactic_conservatism_and_unsafecell_zst_witness`).

#### Arithmetic, Indexing (`validate_place` vs. Outer Borrow Projection), and `keep_original = true`

`Validator::validate_candidate` (`promote_consts.rs:197-216`), `validate_local` (`240-286`), `validate_place` (`288-364`), and `validate_rvalue` (`432-600`) enforce total compile-time evaluation and side-effect preservation:

1. **Division and Remainder Guards (`promote_consts.rs:510-540`)**: `BinOp::Div` and `BinOp::Rem` require compile-time proof of non-zero divisor (`!= 0`), and for signed division/remainder additionally forbid signed `MIN / -1` overflow (`lhs == MIN && rhs == -1`). Live probes confirm:
   - `div_by_zero_not_promoted` (`#![allow(unconditional_panic)] &(1u32 / 0u32)`): `rc = 1`, `E0515`, `promoted_count_after = 0` (`#[allow(unconditional_panic)]` does **not** override `PromoteTemps`!).
   - `rem_by_zero_not_promoted` (`#![allow(unconditional_panic)] &(1u32 % 0u32)`): `rc = 1`, `E0515`, `promoted_count_after = 0`.
   - `signed_min_div_neg1_not_promoted` (`#![allow(arithmetic_overflow)] &(i32::MIN / -1i32)`): `rc = 1`, `E0515`, `promoted_count_after = 0` (Lean witness `ce_signed_min_div_neg1_breaks_ctfe` establishes the matching 1-byte `i8Min / -1` bound).
   - `signed_nonmin_div_neg1_promoted` (`&((-5i32) / -1i32)`): `rc = 0`, `promoted_count_after = 1`.

2. **Checked Arithmetic `keep_original = true` (`promote_consts.rs:779-781` and `rfc3027.md:106-114`)**: `CheckedAdd` / `AddWithOverflow` produces a tuple `(val, overflow_flag)` assigned to a temporary read twice (`uses > 1` or live `Assert` checking `.1` in the parent body). `Validator::validate_rvalue` admits `AddWithOverflow`, and `Promoter` sets **`keep_original = true`** (`uses > 1`), leaving the checked operation and panic `assert!` intact in the active branch of the parent body while promoting the wrapping result into `promoted[0]`. Verbatim excerpt from `support/mir_dumps/overflow_add_in_dead_branch_promoted/overflow_add_in_dead_branch_promoted.f.1-1-007.PromoteTemps.after.mir`:

```mir
    bb1: {
        StorageLive(_2);
        StorageLive(_3);
        _5 = AddWithOverflow(const 200_u8, const 200_u8);
        assert(!move (_5.1: bool), "attempt to compute `{} + {}`, which would overflow", const 200_u8, const 200_u8) -> [success: bb2, unwind: bb5];
    }

    bb2: {
        _6 = const f::promoted[0];
        _3 = &(*_6);
        _2 = &(*_3);
```

   Thus `if false { Some(&(200_u8 + 200_u8)) } else { None }` (`overflow_add_in_dead_branch_promoted`) compiles cleanly (`rc = 0`, `promoted_count_after = 1`): if `bb1` were reached at runtime under overflow checks, the parent `assert!` panics immediately, whereas CTFE evaluates `promoted[0]` cleanly (`144_u8`) without false panic on the dead branch (`ce_addWithOverflow_dead_branch_keepOriginal_sound`).

3. **Place-Borrow vs. Value-Copy Array Indexing (`promote_consts.rs:197-216` vs. `288-364`)**:
   `Validator::validate_candidate` validates the *base local* of a borrowed place (`&place`, checking `!place.projection.contains(Deref)`) rather than asserting bounds on trailing projections of the promoted root borrow itself, whereas `Validator::validate_place` inside rvalue operands (`Rvalue::Use(Copy/Move(place[idx]))`) *does* require statically provable `idx < len` (and rejects union field projections). Empirical differential probes isolate this split cleanly:
   - **Value-copy OOB indexing (`value_index_oob_not_promoted`: `&({ [10u32, 20u32][2] })`)**: Parent MIR contains `_2 = copy _3[_4]; _1 = &_2;`, forcing `validate_place` on `[10u32, 20u32][2]`, failing `idx < len` -> **`rc = 1`, `E0515`, `promoted_count_after = 0`**. Likewise `value_arith_index_oob_not_promoted` (`&(1u32 + [10u32, 20u32][2])`) -> **`rc = 1`, `E0515`, `promoted_count_after = 0`**. (By contrast, in-bounds `value_index_inbounds_promoted` `&({ [10u32, 20u32][1] })` -> **`rc = 0`, `promoted_count_after = 1`**.)
   - **Place-borrow OOB indexing (`place_index_oob_base_promoted`: `&([10u32, 20u32][2])`)**: **`rc = 0`, `promoted_count_after = 1`!** Verbatim `support/mir_dumps/place_index_oob_base_promoted/place_index_oob_base_promoted.f.1-1-007.PromoteTemps.after.mir` demonstrates how `rustc` preserves soundness:

```mir
    bb0: {
        StorageLive(_1);
        StorageLive(_2);
        _2 = [const 10_u32, const 20_u32];
        StorageLive(_3);
        _3 = const 2_usize;
        FakeRead(ForIndex, _2);
        _4 = Lt(copy _3, const 2_usize);
        assert(move _4, "index out of bounds: the length is {} but the index is {}", const 2_usize, copy _3) -> [success: bb1, unwind: bb2];
    }

    bb1: {
        _5 = const f::promoted[0];
        _1 = &(*_5)[_3];
        _0 = &(*_1);
```

   The array literal `[10_u32, 20_u32]` is promoted into `f::promoted[0]` (which is infallible!), while the runtime bounds `assert(Lt(copy _3, const 2_usize))` and the indexed projection `_1 = &(*_5)[_3]` remain in the parent body. Therefore `rustc` preserves runtime panic semantics without ever exposing CTFE or post-cleanup execution to an unchecked OOB read (`ce_copy_index_oob_rejected_vs_place_index_base_promoted`).

#### `#[rustc_promotable]` Calls, `promotion_safe_blocks` in `const`/`static`, and Inline `const { ... }` PME

`Validator::validate_call` (`promote_consts.rs:642-693`) gates `TerminatorKind::Call` promotion along two distinct paths controlled by body kind and `promotion_safe_blocks` (`promote_consts.rs:605-640`):

1. **Ordinary `fn` Bodies**: Only functions marked `#[rustc_promotable]` with infallible MIR semantics are implicitly promotable inside `fn` (`promotable_std_const_fn_promoted`: `&core::mem::size_of::<u64>()` -> `rc = 0`, `promoted_count_after = 1`). Plain user-defined `const fn cf() -> u32 { 42 }` lacks `#[rustc_promotable]`, so `pub fn f() -> &'static u32 { &cf() }` (`plain_const_fn_not_promoted`) fails with **`rc = 1`, `E0515`, `promoted_count_after = 0`**.
2. **`const` Items and `static` Initializers (`promotion_safe_blocks`)**: Inside `static` items (`explicit_promote_all`) and `const` items with `allow_const_fn_promotion = true`, `Validator::is_promotion_safe_block` computes the control-flow blocks dominated-and-reached from `START_BLOCK` *without* crossing conditional runtime-branching edges (`SwitchInt`, `Drop`, `Assert`). Arbitrary `const fn` calls are promotable inside `promotion_safe_blocks` (`const_item_safe_block_const_fn_promoted`: `pub const C_SAFE: &'static u32 = core::convert::identity(&cf());` -> `rc = 0`, `promoted_count_after = 1`), and panics inside live safe blocks trigger CTFE errors (`const_item_safe_block_panic_e0080`: `pub const C_LIVE_PANIC: &'static u32 = core::convert::identity(&cf_panic());` -> `E0080`, `promoted_count_after = 1`).
   - **Lifetime-extension masking pitfall discovered empirically**: Top-level extending positions inside a `const` item (`pub const C_DEAD_EXT: Option<&'static u32> = if false { Some(&cf_panic()) } else { None };`, `const_item_dead_branch_ext_unpromoted_ok`) compile cleanly with **`rc = 0`, `promoted_count_after = 0`** because syntactic `'static` lifetime extension (`r[destructors.scope.lifetime-extension]`) grants `&cf_panic()` a `'static` borrow *without* promoting it! Wrapping `&cf_panic()` in non-extending `core::convert::identity(&cf_panic())` (`const_item_dead_branch_nonext_rejected`: `C_DEAD`) disables syntactic extension and isolates `promotion_safe_blocks`: `if false` is excluded from `promotion_safe_blocks`, so `PromoteTemps` declines promotion (`promoted_count_after = 0`) and borrowck emits `E0716: temporary value dropped while borrowed` (`rc = 1`).
3. **Inline `const { ... }` Blocks (`inline_const_block_allows_plain_const_fn` vs. PME)**:
   - `const { cf() }` lowers into a separate `AnonConst` MIR body `f::{constant#0}` (visible in `support/mir_dumps/inline_const_block_allows_plain_const_fn/inline_const_block_allows_plain_const_fn.f-{constant#0}.1-1-007.PromoteTemps.after.mir`). In parent `f`'s MIR, `_2 = const f::{constant#0}; _1 = &_2;` is simply reading an `Operand::Constant`—**not** a `Call` terminator—so `f` promotes `_2` cleanly into `f::promoted[0]` (`inline_const_block_allows_plain_const_fn`: `rc = 0`, `promoted_count_after = 1`), verbatim:

```mir
    bb0: {
        StorageLive(_1);
        _3 = const f::promoted[0];
        _1 = &(*_3);
        _0 = &(*_1);
        StorageDead(_1);
        return;
    }
```

   - **Post-Monomorphization Error (PME) across Dead Branches**: Because `RequiredConstsVisitor` (`required_consts.rs:1-24`, running at `lib.rs:477`) walks `reverse_postorder(&body)`, even an inline `const { 1u32 / 0u32 }` placed inside a dead `if false { Some(&const { 1u32 / 0u32 }) } else { None }` branch is recorded in `required_consts` (both `f` and `f::promoted[0]`). Under `--emit=obj` (`inline_const_pme_dead_branch_obj_rejected`), PME evaluates `f::{constant#0}` and fails with **`rc = 1`, `error[E0080]: attempt to divide 1_u32 by zero`, `promoted_count_after = 1`**. Under `--emit=metadata` (`inline_const_pme_dead_branch_metadata_skipped`), monomorphization/codegen does not trigger PME and `PromoteTemps` is not dumped (**`rc = 0`, `promoted_count_after = 0`**). Inside `const_eval` / `check` itself, `should_evaluate_for_promotion_checks` (`promote_consts.rs:697-718`) guards against `AnonConstKind::NonTypeSystemInline` cycles.

#### Mechanized Infallibility & Drop-Trace Equivalence (`Lean v4.34.1`)

Part 2 of `support/PromoteTempsInfallibleZstMutAndConstMutationSoundness.lean` (`lines 254-954`) formalizes candidate expressions (`CandExpr`), value-based `Qualif` (`qualifHasMutInterior`, `qualifNeedsDrop`), `validatePromotionCandidate`, `ctfeEvalPromoted`, and pre/post-promotion runtime execution (`evalParentBeforePromote` vs. `evalParentAfterPromote` with explicit drop traces `RuntimeOutcome.drops`):

- **`validator_implies_ctfe_infallible`**: Every validated candidate (`validatePromotionCandidate = true`) with satisfied call contracts (`callContractSatisfied = true`, i.e., `#[rustc_promotable]` or safe non-panicking `const fn` in safe blocks) evaluates to `.ok v` at CTFE (`0` CTFE panics).
- **`promoteTemps_runtime_and_drop_trace_preserved`**: Under validated promotion, post-promotion execution (`promoted[0]` precomputed + `keep_original` checked arithmetic / place-index assertions kept in the active branch) produces the exact same `RuntimeOutcome` and `DropTrace` as pre-promotion execution across all `overflowChecks × branchCond ∈ Bool × Bool`.
- **`promoteTemps_infallible_preserves_semantics_iff`**: Assuming `validateCandExpr`, `callContractSatisfied`, and `validateRef` hold, CTFE-totality combined with full runtime & destructor equivalence holds **if and only if** `qualifNeedsDrop e = false`.
- **Six explicit counterexample / discriminator theorems**:
  1. `ce_div_zero_dead_branch_breaks_ctfe`: `if false { &(1 / 0) }` returns `.returned 0 []` pre-promotion vs. `.runtimePanic []` if promoted -> rejected by `validatePromotionCandidate`.
  2. `ce_signed_min_div_neg1_breaks_ctfe`: `i8::MIN / -1` rejected vs. `(-5) / -1` accepted (`.ok 5`).
  3. `ce_copy_index_oob_rejected_vs_place_index_base_promoted`: `copyArrayIndex` OOB rejected vs. `placeArrayIndexBase` accepted with runtime `.runtimePanic []` kept in the active branch.
  4. `ce_needsDrop_promotion_drops_side_effect`: promoting `NeedsDrop` silently drops `[1]` from `DropTrace` -> rejected by `!qualifNeedsDrop`.
  5. `ce_addWithOverflow_dead_branch_keepOriginal_sound`: `200_u8 + 200_u8` promotes `.ok 144` (`uses = 2`, `keep_original = true`) while keeping `.runtimePanic []` in the active overflow-checked branch.
  6. `ce_non_zst_move_deinit_preserved`: aligns `promote_consts.rs` single-use temporary trees (`usedTwice = false`) with `joshlf/anneal`'s `Trusted.MirSemantics` (`deinitMovedPlace = true`, lines `949-976`), proving double-moves fault cleanly (`uninitMoveFault`) for non-ZST locals while ZST (`unit`) preserves `.unit` validity.

---

### Zero-Sized `'static mut` Promotion vs. `&UnsafeCell<()>` Rejection and Miri Soundness

#### `validate_ref` Array-0 Whitelist vs. Syntactic `&mut ()` Rejection

In `promote_consts.rs:400-430`, `Validator::validate_ref` branches sharply on reference mutability:

- **Shared borrow (`Mutability::Not`)**: Rejected iff `HasMutInterior == true` (value-based, allowing `&Option::<UnsafeCell<()>>::None` while rejecting `&UnsafeCell::new(())`).
- **Mutable borrow (`Mutability::Mut`, `BorrowKind::Mut { kind: Default | TwoPhaseBorrow }`)**: Allowed **only if** the borrowed place's peeled tail type matches syntactically `ty::Array(_, len)` with constant `len == 0`! All other `BorrowKind::Mut` (and shared fake/raw borrows) are rejected.

Empirical results verify this syntactic narrowness:
- **`zst_mut_and_rvalue_promotion`** (`let a: &'static mut [u32] = &mut []; let b: &'static mut [u32; 0] = &mut [];`): Compiles (`compile_rc = 0`, `promoted_count_after = 3`) and unsizes `[u32; 0]` to `&mut [u32]` (`PointerCoercion(Unsize, Implicit)`). Verbatim `support/mir_dumps/zst_mut_and_rvalue_promotion/zst_mut_and_rvalue_promotion.probe_three_promoteds.1-1-007.PromoteTemps.after.mir`:

```mir
    bb0: {
        StorageLive(_1);
        StorageLive(_2);
        StorageLive(_3);
        _20 = const probe_three_promoteds::promoted[2];
        _3 = &mut (*_20);
        _2 = &mut (*_3);
        _1 = move _2 as &mut [u32] (PointerCoercion(Unsize, Implicit));
...
        _19 = const probe_three_promoteds::promoted[1];
        _6 = &mut (*_19);
        _5 = &mut (*_6);
```

- **`mut_unit_zst_not_promoted` (`let r: &'static mut () = &mut ();`)**: Rejected with **`rc = 1`, `error[E0515]`, `promoted_count_after = 0`**! Even though `size_of::<()>() == 0` and `&mut ()` is every bit as byte-empty as `&mut [u32; 0]`, `validate_ref` syntactically checks `ty::Array(_, 0)` rather than layout `is_zst()`.
- **`mut_non_zst_not_promoted` (`let r: &'static mut [u32; 1] = &mut [0];`)**: Rejected (`rc = 1`, `E0515`, `promoted_count_after = 0`).
- **Double `UnsafeCell<()>` test (`unsafecell_zst_const_temp_not_promoted`)**: `let r: &'static UnsafeCell<()> = &{ const U: UnsafeCell<()> = UnsafeCell::new(()); U };` also fails (`rc = 1`, `E0515`) because reading an `UnsafeCell<()>` constant temporary marks `HasMutInterior = true` (`qualifs.rs:84-137`).

#### Why Miri Stacked Borrows (`sb_reborrow`) and Tree Borrows (`tb_reborrow`) Admit Read-Only Promoted `&'static mut [u32]` (`rc = 0`)

Promoted allocations reside in read-only static memory (`AllocMutability::Immutable` in `rustc`, mapped to `AllocMut.readOnly` in Miri). Naively, creating `&'static mut T` pointing to read-only memory (`Unique` reborrow or write protector) appears to risk aliasing or write-to-rodata Undefined Behavior (`WriteToReadOnly`). Auditing Miri's two borrow trackers explains why 0-byte mutable borrows—even **two simultaneous `StrongProtector`-guarded mutable parameters derived from `a.split_at_mut(0)`** (`dual_protected_zst_mut`)—are strictly sound:

1. **Stacked Borrows (`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs:667-752`)**: In `sb_reborrow`, **before calling `get_alloc_extra_mut`** or pushing `Permission::Unique` (`lines 735-751`), Miri checks `size == Size::ZERO` (`lines 667-696`) and **returns immediately** with the newly minted pointer tag, updating zero byte stacks and never inspecting `alloc_mutability` (`Mutability::Mut` vs. `Mutability::Not`).
2. **Tree Borrows (`src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:274-434`)**: When creating a child tag (`new_child`, `lines 423-431`) with `StrongProtector` (`FnEntry`, `lines 300-318`), `tb_reborrow` initializes the touched offset range `inside_perms` as a `DedupRangeMap` (`lines 345-363`). For a zero-sized reborrow (`size == Size::ZERO`), that `DedupRangeMap` covers `0` bytes; the loop `inside_perms.iter_all()` (`lines 368-420`) executes **zero iterations**, never hitting the `WriteToReadOnly` mutability guard (`lines 374-378`).
3. **Empirically verified Miri SB & TB split**:
   - `zst_mut_and_rvalue_promotion` (returning promoted `&'static mut [u32]`, checking non-null, splitting `a.split_at_mut(0)` into `(x, y)` passed into `#[inline(never)] fn dual_protected_zst_mut(x: &mut [u32], y: &mut [u32]) -> bool`):
     * Native execution: **`native_rc = 0`**, `native_stdout = "PROMOTED_OK=true NZ=true C=[11, 40]"`.
     * Miri Stacked Borrows (default): **`miri_sb_rc = 0`**, `miri_stdout = "PROMOTED_OK=true NZ=true C=[11, 40]"`.
     * Miri Tree Borrows (`-Zmiri-tree-borrows`): **`miri_tb_rc = 0`**, `miri_tb_stdout = "PROMOTED_OK=true NZ=true C=[11, 40]"`.
   - `miri_zst_mut_oob_write_rejected` (`let a: &'static mut [u32] = &mut []; unsafe { *a.as_mut_ptr() = 1; }`):
     * Miri SB (`miri_sb_rc = 1`) and Miri TB (`miri_tb_rc = 1`) **both reject with Undefined Behavior** (out-of-bounds 4-byte access at offset `0` of 0-byte allocation).

Mechanized in Lean (`lines 955-1109` via zero-axiom / `propext`-minimal proofs):
- **`zst_mut_borrow_promoted_rodata_sound`** (**`[]` axioms**): For any `alloc` with `alloc.mutability = .readOnly` and `offset ≤ alloc.size`, `sbRetag alloc offset 0 true protect` and `tbRetag alloc offset 0 true tyIsFreeze protect immediateWrite` both return `.ok`, preserve `.readOnly`, and mint valid fresh tags (and keep `sbStacks` unchanged).
- **`dual_protected_zst_mut_borrows_rodata_sound`** (**`[]` axioms**): Two consecutive `StrongProtector` (`protect = true`) `&mut` reborrows at offset `0` succeed in both SB and TB with distinct tags `t1 ≠ t2`.
- **`nonzst_mut_borrow_rodata_ub_counterexample`**: Any nonzero (`size = n + 1`) mutable reborrow on `.readOnly` memory triggers `.error .writeToReadOnly` in both SB and TB.
- **`zst_mut_promoted_write_oob_ub`**: Writing 4 bytes at offset `0` on a 0-byte allocation fails with `.error .outOfBounds`.

---

### `CheckConstItemMutation`: `LocalInfo::ConstRef` Destructor Asymmetry and `940498dad7cb` Evolution

Evaluating a `const` item (`const C: T = ...`) in expression position materializes a **fresh temporary local** tagged `LocalInfo::ConstRef { def_id }` (`as_temp.rs`, cleared only after analysis passes at `lib.rs:693-695`). Mutating that temporary **never** alters subsequent evaluations of `C`, so `rustc` provides the warn-by-default `CONST_ITEM_MUTATION` lint (`check_const_item_mutation.rs`) to catch likely user confusion—EXCEPT when `T` has a destructor (`Drop`), because mutating the temporary *does* change what `Drop::drop` observes when the temporary goes out of scope!

#### `visit_statement` (`is_const_item_without_destructor`) vs. `visit_rvalue` (`is_const_item`) Asymmetry

Comparing `check_const_item_mutation.rs` in `14210df0e` (`1.98.0-nightly`) and `3ef0c22cd` (`1.102.0-nightly` / `HEAD` `ce66487`) exposes a striking **intra-pass asymmetry**:

| Visitor Method | MIR Hook | Check Function (`1.98.0-nightly` / `1.102.0-nightly`) | Effect on `C_DIRECT : DropLogger` (`has_dtor = true`) | Effect on `O : Outer { inner: Inner }` (`has_dtor = false`, `needs_drop = true`) |
| --- | --- | --- | --- | --- |
| `visit_statement` | `StatementKind::Assign(place, _)` (`line 104` / `113`) | `is_const_item_without_destructor` (`line 59` / `63-74`) | **No warning** (`C_DIRECT.val = 10;`, `C_DIRECT.val = 50;`) | `1.98.0`: **False positive** (`adt.has_dtor == false`); `1.102.0` (`940498dad7cb`): **Suppressed** (`ty.needs_drop == true`) |
| `visit_rvalue` | `Rvalue::Ref(..., BorrowKind::Mut, place)` / `RawPtr` (`line 134` / `144`) | `is_const_item` (**omits destructor check!**) | **False positive!** (`C_DIRECT.set(15);` emits `taking a mutable reference to a const item`) | **False positive on both `1.98.0` and `1.102.0`!** (`O.set_inner(1);` emits `taking a mutable reference to a const item`) |
| `should_lint_const_item_usage` | Filtered inside both (`line 91`) | Rejects `PlaceElem::Deref` (`place.projection.contains(&PlaceElem::Deref)`) | **No warning** on raw deref `*c_ptr.ptr = 7` | **No warning** on raw deref |

Empirical inspection of `check_const_item_mutation_asymmetry.rs` and its verbatim `mir_built` dump (`support/mir_dumps/check_const_item_mutation_asymmetry/check_const_item_mutation_asymmetry.demo_const_mutation_paths.1-1-000.built.after.mir`) confirms that direct field mutation (`_2`), `&mut self` method call (`_5` -> `DropLogger::set(move _4, const 15_u32)` -> `drop(_5)`), and direct mutation `_6` follow the **exact same MIR lifecycle**: copy `const C_DIRECT` to a `ConstRef` temporary, mutate it, and run `drop`!

```mir
    bb0: {
        StorageLive(_2);
        _2 = const C_DIRECT;
        (_2.0: u32) = const 10_u32;
        drop(_2) -> [return: bb1, unwind: bb6];
    }

    bb1: {
        StorageDead(_2);
        StorageLive(_3);
        StorageLive(_4);
        StorageLive(_5);
        _5 = const C_DIRECT;
        _4 = &mut _5;
        _3 = DropLogger::set(move _4, const 15_u32) -> [return: bb2, unwind: bb5];
    }

    bb2: {
        StorageDead(_4);
        drop(_5) -> [return: bb3, unwind: bb6];
    }

    bb3: {
        ...
        _6 = const C_DIRECT;
        (_6.0: u32) = const 50_u32;
        drop(_6) -> [return: bb4, unwind: bb6];
    }
```

At runtime (`probe_results.json`):
- `check_const_item_mutation_asymmetry`: compiles and exits `0` printing **`OBSERVED_DROPS=75`** (`10 + 15 + 50`), while emitting **2** warnings:
  * Line 35 (`C_DIRECT.set(15);`): `taking a mutable reference to a const item` (**false positive!**)
  * Line 37 (`C_NODROP.val = 99;`): `attempting to modify a const item` (**true positive!**)
  * Lines 34 & 36 (`C_DIRECT.val = 10`, `50`) & Line 40 (`*c_ptr.ptr = 7`): `0` warnings!
- Separate probe `check_const_item_mutation_explicit_mut_ref` (`{ let r = &mut C; r.val = 50; }`): emits 1 `&mut` warning at line 9 and outputs **`EXPLICIT_DROPS=50`**—demonstrating that even an explicit short-lived `&mut C` triggers `drop` on the mutated `ConstRef` temporary and updates observable drop state!

#### Cross-Version Evolution (`1.98.0` `adt.has_dtor` vs. `940498dad7cb` / `1.102.0` `ty.needs_drop`)

In `14210df0e` (`1.98.0-nightly`), `is_const_item_without_destructor` (`check_const_item_mutation.rs:59`) had a `FIXME` checking `adt.has_dtor(self.tcx)` only on the outer ADT, missing indirect `Drop` glue in fields. Running `check_const_item_mutation_nested_drop.rs` (`struct Outer { inner: Inner }` where `Inner: Drop`, `Outer` has no `Drop` impl) on `1.98.0-nightly`:
- Runtime output: **`NESTED_DROPS=43`** (`42` from `O.inner.val = 42` + `1` from `O.set_inner(1)`!).
- `1.98.0-nightly` diagnostics: **2 false positives** (Line 28 `O.inner.val = 42` `attempting to modify a const item` + Line 29 `O.set_inner(1)` `taking a mutable reference to a const item`).
- Upstream commit **`940498dad7cb35a753a7cce104ab510b414e84de`** (`2026-08-24`) replaced `line 59` with `!ty.has_param() && ty.needs_drop(self.tcx, typing_env)` (`check_const_item_mutation.rs:63-74`), eliminating the Line 28 false positive on `O.inner.val = 42` in `1.102.0-nightly`, while leaving `visit_rvalue`'s bare `is_const_item` call untouched so Line 29 (`O.set_inner(1)`) still warns on both `1.102.0-nightly` and `HEAD` (`ce66487ebb`).

#### Observational Equivalence Criterion & Repaired Lint Soundness/Completeness (`Lean v4.34.1`)

Part 4 of `support/PromoteTempsInfallibleZstMutAndConstMutationSoundness.lean` (`lines 1110-1290`) models `execConstRefUsage` (mutating the temporary vs. `derefPtrEscapeWrite` vs. `nop`, appending final temporary state iff `tyNeedsDrop ty = true`), together with `lintRustc198`, `lintRustc1102`, and `lintRepaired` (applying `!tyNeedsDrop ty` uniformly to both `visit_statement` and `visit_rvalue`):

- **`constMutation_unobservable_iff_no_needsDrop`**: Across **all three** non-deref mutation forms (`directFieldWrite`, `mutBorrowMethodCall`, `mutBorrowBlockWrite`), mutating a `ConstRef` temporary is observationally indistinguishable from `.nop` across all initial values and logs **if and only if** `tyNeedsDrop ty = false`.
- **`checkConstItemMutation_visitRvalue_false_positive_witness`** & **`observed_drops_sum_eq_75`**: Reproduces `C_DIRECT` (`OBSERVED_DROPS = 75`) and proves `lintRustc1102` returns `none` for `directFieldWrite` yet `some .mutBorrow` for `mutBorrowMethodCall`, even though both alter the observable drop trace.
- **`checkConstItemMutation_nestedDrop_198_vs_1102_witness`**: Captures `Outer { inner: Inner }` (`hasDtor = false`, `tyNeedsDrop = true`), witnessing `lintRustc198` flagging `.directFieldWrite 42`, `lintRustc1102` clearing it, and `lintRustc1102` still flagging `.mutBorrowMethodCall 42`.
- **`lintRepaired_exact_soundness_and_completeness`**: Proves that applying `tyNeedsDrop` uniformly in both visitors yields an **exact** soundness-and-completeness correspondence: `(lintRepaired ty op).isSome = true` iff the mutation is observationally unobservable.

*Basis:* `promote_consts.rs`, `qualifs.rs`, `required_consts.rs`, `lib.rs`, `check_const_item_mutation.rs` (`14210df0`, `940498dad`, `3ef0c22cd`, `ce66487eb`); Miri `sb_reborrow` (`stacked_borrows/mod.rs:667-752`) and `tb_reborrow` (`tree_borrows/mod.rs:274-434`); `support/probe_results.json`; `support/mir_dumps/*`; and `support/PromoteTempsInfallibleZstMutAndConstMutationSoundness.lean`.

---

## Boundaries

### Methodological & Verification Scope Boundaries

1. **Lean Model Abstractions vs. Full Compiler IR (`not examined` / `unsupported`)**:
   - The Lean formalization in `support/PromoteTempsInfallibleZstMutAndConstMutationSoundness.lean` models single-candidate expression trees (`CandExpr`), byte-range allocation mutability (`AllocState` with `size`, `AllocMut`, `sbStacks`, `tbNodes`), and statement-local `LocalInfo::ConstRef` drop logs. It does **not** verify full multi-basic-block MIR SSA/alias reconstruction (`not examined`), trait-object vtable promotion rules, or Miri tree/stack garbage collection (`remove_unreachable_tags`).
   - All checked-division and ZST theorems use pure structural recursion and total functions (`0` `partial`, `0` `_unsafe_rec`, `0` `omega`/`bv_decide`/`native_decide`, `0` `Classical.choice`; only core Lean axioms `propext` and `Quot.sound` appear in theorem dependencies, with `zst_mut_borrow_promoted_rodata_sound`, `dual_protected_zst_mut_borrows_rodata_sound`, and `observed_drops_sum_eq_75` depending on **zero** axioms).
2. **`rustc` Generic Type Parameter Boundary (`check_const_item_mutation.rs:63-74`)**:
   - In `940498dad7cb` / `1.102.0-nightly`, `is_const_item_without_destructor` checks `if ty.has_param() { return false; }`. For generic `const` expressions inside generic functions before monomorphization where `T` might later specialize to a `Drop` type, `rustc` conservatively suppresses `visit_statement` lints (`ty.has_param()` -> suppress) while still warning in `visit_rvalue` (`is_const_item`). Our Lean `tyNeedsDrop` model operates on concrete instantiated types (`hasParam = false` witnesses concrete structs; explicit `hasParam = true` defaults conservative in `qualifNeedsDrop` and `tyNeedsDrop`).
3. **Host Tooling Parity and `1.102.0` vs. `1.98.0` Delta (`unknown` / `known not to apply`)**:
   - Because live execution on this host uses `rustc 1.98.0-nightly` (`14210df0e2`) and `miri 0.1.0`, the nested-drop `visit_statement` warning in `check_const_item_mutation_nested_drop` (`O.inner.val = 42` warned on `1.98.0`, suppressed post-`940498dad7cb`) reflects the pinned `1.98.0` binary coupled with diff-verified upstream commit `940498dad7cb35a753a7cce104ab510b414e84de` present in `3ef0c22cdb` and `ce66487ebb`. All 8 baseline parity cases in `support/baseline_1_102_3ef0c22cd.json` match identically (`baseline_parity: all true`).
   - Promoted `&mut [u32; 0]` soundness is `known not to apply` if `T` is non-zero-sized or if unsafe raw pointer casts write non-zero bytes at offset `0`. Similarly, `PromoteTemps` runtime-vs-CTFE equivalence is `known not to apply` to explicit `const { ... }` items evaluated across dead branches (`E0080` PME).
   - Downstream `upstream` evolution of `check_const_item_mutation.rs` beyond `ce66487ebbd7541212d22d01c39a808057d69f1f` (`2026-11-22`)—specifically whether `visit_rvalue` is later harmonized with `is_const_item_without_destructor`—is **`unknown`** at the `observed_at` cutoff.

### Impact on `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

| Anneal Boundary Component | Relevant Upstream Invariant | Boundary Status |
| --- | --- | --- |
| `trusted/rustc-capture/src/driver.rs` | Captures post-cleanup `optimized_mir` + `promoted_mir` after `PromoteTemps` and `run_analysis_to_runtime_passes` | `LocalInfo::ConstRef` already cleared (`lib.rs:693-695`); `promoted_mir` contains only promoted bodies admitted by `Validator` |
| `trusted/lean/Trusted/MirAst.lean` | `Allocation.mutability`, `ConstLit`, `Rvalue.ref`, `Terminator.call` | Promoted `&[T]` and `&mut [T; 0]` both map cleanly onto `.readOnly` / `Allocation.mutability` = immutable static allocs |
| `trusted/lean/Trusted/MirSemantics.lean` | `evalOperandToSlot` (`deinitMovedPlace = true`), `.unit` vs. non-ZST slot uninit (`949-976`) | Aligns with `PromoteTemps` single-move / zero-drop invariant (`ce_non_zst_move_deinit_preserved`); ZST `&mut` writes are empty |
| `trusted/audit/TrustedBoundary.lean` | Axiom-clean kernel audit boundary (`[propext, Quot.sound]`, zero `Classical.choice` / `sorryAx`) | Matches the exact purity discipline proven in `support/PromoteTempsInfallibleZstMutAndConstMutationSoundness.lean` (`support/PromoteTempsAudit.lean`) |

*Basis:* Upstream `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` files (`driver.rs`, `MirAst.lean`, `MirSemantics.lean`, `TrustedBoundary.lean`), `check_const_item_mutation.rs` (`940498dad7cb` diff), `support/lean_check_receipt.json`, and `support/baseline_1_102_3ef0c22cd.json`.

---

## Evidence

### Normative and Documentation Sources (`normative`, `documentation`)

| Evidence Artifact / Reference | Role | Verified Scope |
| --- | --- | --- |
| `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/destructors.md` (`r[destructors.scope.const-promotion]`, `:379-383`) & `src/items/constant-items.md` | `normative` | Normative specification of temporary scopes, lifetime extension in `const`/`static`, and constant promotion |
| `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/3027-infallible-promotion.md` (`:106-114`) & `text/1414-rvalue_static_promotion.md` | `documentation` | RFC 3027 infallible implicit promotion contract (`Div`/`Rem`, `#[rustc_promotable]`, `CheckedAdd` split) and RFC 1414 rvalue static promotion |

### Primary Compiler, Miri, and Anneal Source Code (`source`)

All 26 upstream source files across all 8 pinned commits were verified live as HTTP `200` via `support/verify_pins.py` (`support/pin_receipt.json`, `passed: true`, `generated_on: 2026-11-22`):

| Repository & Commit | Inspected Files | Role | Key Verified Findings / Line Ranges |
| --- | --- | --- | --- |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `promote_consts.rs`, `check_const_item_mutation.rs`, `required_consts.rs`, `lib.rs`, `qualifs.rs`, `stacked_borrows/mod.rs`, `tree_borrows/mod.rs` | `source` | `check_const_item_mutation.rs:59` (`adt.has_dtor`), `:91` (`PlaceElem::Deref`), `:104` (`visit_statement`), `:134` (`visit_rvalue`); SB `667-752`; TB `274-434` |
| `rust-lang/rust@940498dad7cb35a753a7cce104ab510b414e84de` | `compiler/rustc_mir_transform/src/check_const_item_mutation.rs` | `source` | Replaced `adt.has_dtor` with `ty.has_param()` + `ty.needs_drop`; left `visit_rvalue` unguarded |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `promote_consts.rs`, `check_const_item_mutation.rs`, `required_consts.rs`, `lib.rs`, `qualifs.rs`, `as_temp.rs`, SB/TB `mod.rs` | `source` | `promote_consts.rs` `1-1100` (`TempState`, `Collector`, `Validator`, `Promoter`); `check_const_item_mutation.rs:63-74, 91, 113, 144`; `lib.rs:364-696` |
| `rust-lang/rust@ce66487ebbd7541212d22d01c39a808057d69f1f` | `promote_consts.rs`, `check_const_item_mutation.rs` | `source` | `0`-line diff vs. `3ef0c22cdb86`; both behaviors active at `HEAD` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `driver.rs`, `MirAst.lean`, `MirSemantics.lean`, `TrustedBoundary.lean` | `source` | `promoted_mir` extraction; `Allocation.mutability`; `evalOperandToSlot` `deinitMovedPlace = true` (`949-976`) |

### Empirical Compiler, MIR Dump, and Miri Execution Ledger (`execution`)

All 30 probes executed cleanly via `support/probe_promote_temps_and_const_item_mutation.py` (`support/probe_results.json`, `generated_on: 2026-11-22`) on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)`, matching all 8 baseline cases in `support/baseline_1_102_3ef0c22cd.json` (`1.102.0-nightly`, `3ef0c22cd`):

| Case Identifier | Category | `rc` / Runtime / Miri Result | Promoted Count | Saved Artifact / Diagnostic |
| --- | --- | --- | --- | --- |
| `zst_mut_and_rvalue_promotion` | ZST `&mut` + arith promotion | compile `0`, native `0`, SB `0`, TB `0`, stdout `PROMOTED_OK=true NZ=true C=[11, 40]` | `3` | `support/mir_dumps/zst_mut_and_rvalue_promotion/*` (`4` dumps) |
| `miri_zst_mut_oob_write_rejected` | 4-byte write via `&'static mut [u32]` | SB `1` (UB), TB `1` (UB) | — | Miri `Undefined Behavior` abort (`support/specimens/miri_zst_mut_oob_write_rejected.rs`) |
| `mut_non_zst_not_promoted` | `&'static mut [u32; 1]` | `1` (`E0515`) | `0` | Rejected by `validate_ref` (`len != 0`) |
| `mut_unit_zst_not_promoted` | `&'static mut ()` | `1` (`E0515`) | `0` | Syntactic rejection (`()` is not `ty::Array(_, 0)`) |
| `unsafecell_u32_not_promoted` | `&UnsafeCell<u32>` | `1` (`E0515`) | `0` | `HasMutInterior == true` (`baseline_parity = true`) |
| `unsafecell_zst_not_promoted` | `&UnsafeCell<()>` | `1` (`E0515`) | `0` | `HasMutInterior == true` at size `0` (`baseline_parity = true`) |
| `unsafecell_zst_const_temp_not_promoted` | `const U: UnsafeCell<()>` temp borrow | `1` (`E0515`) | `0` | `HasMutInterior` non-structural on `Const::Unevaluated` read |
| `none_unsafecell_zst_promoted` | `&Option::<UnsafeCell<()>>::None` | `0` | `1` | Value-based `HasMutInterior == false` |
| `some_unsafecell_zst_not_promoted` | `&Some(UC)` (`const UC: UnsafeCell<()>`) | `1` (`E0515`) | `0` | Field operand taints `Some` aggregate |
| `div_by_zero_not_promoted` | `&(1u32 / 0u32)` (`#[allow(unconditional_panic)]`) | `1` (`E0515`) | `0` | `Div 0` rejected even under `-A unconditional_panic` |
| `rem_by_zero_not_promoted` | `&(1u32 % 0u32)` (`#[allow(unconditional_panic)]`) | `1` (`E0515`) | `0` | `Rem 0` rejected |
| `signed_min_div_neg1_not_promoted` | `&(i32::MIN / -1i32)` (`#[allow(arithmetic_overflow)]`) | `1` (`E0515`) | `0` | Signed min overflow division guard |
| `signed_nonmin_div_neg1_promoted` | `&((-5i32) / -1i32)` | `0` | `1` | Safe signed division promoted |
| `overflow_add_in_dead_branch_promoted` | `if false { Some(&(200u8 + 200u8)) } else { None }` | `0` | `1` | `keep_original = true`: `bb1` keeps `AddWithOverflow` (`2` dumps) |
| `place_index_oob_base_promoted` | `&([10u32, 20u32][2])` | `0` | `1` | Base `[10, 20]` promoted; parent `bb0` keeps `assert(Lt)` (`2` dumps) |
| `value_index_oob_not_promoted` | `&({ [10u32, 20u32][2] })` | `1` (`E0515`) | `0` | `validate_place` `idx < len` fails (`2` dumps) |
| `value_arith_index_oob_not_promoted` | `&(1u32 + [10u32, 20u32][2])` | `1` (`E0515`) | `0` | `validate_place` rejects rvalue operand indexing |
| `value_index_inbounds_promoted` | `&({ [10u32, 20u32][1] })` | `0` | `1` | In-bounds `validate_place` succeeds |
| `plain_const_fn_not_promoted` | `&cf()` (plain `const fn`) | `1` (`E0515`) | `0` | Lacks `#[rustc_promotable]` |
| `promotable_std_const_fn_promoted` | `&core::mem::size_of::<u64>()` | `0` | `1` | `#[rustc_promotable]` admitted |
| `const_item_safe_block_const_fn_promoted` | `C_SAFE = identity(&cf())` | `0` | `1` | `promotion_safe_blocks` admits plain `const fn` |
| `const_item_dead_branch_nonext_rejected` | `C_DEAD = if false { Some(identity(&cf_panic())) }` | `1` (`E0716`) | `0` | Excluded from `promotion_safe_blocks` -> unpromoted `E0716` |
| `const_item_dead_branch_ext_unpromoted_ok` | `C_DEAD_EXT = if false { Some(&cf_panic()) }` | `0` | `0` | Syntactic `'static` lifetime extension bypasses promotion |
| `const_item_safe_block_panic_e0080` | `C_LIVE_PANIC = identity(&cf_panic())` | `1` (`E0080`) | `1` | Promoted in safe block -> CTFE panic `E0080` |
| `inline_const_block_allows_plain_const_fn` | `&const { cf() }` | `0` | `1` | `f::{constant#0}` `AnonConst` promoted (`6` MIR dumps) |
| `inline_const_pme_dead_branch_obj_rejected` | `if false { Some(&const { 1u32 / 0u32 }) }` (`--emit=obj`) | `1` (`E0080`) | `1` | `RequiredConstsVisitor` triggers PME (`4` MIR dumps) |
| `inline_const_pme_dead_branch_metadata_skipped` | Same under `--emit=metadata` | `0` | `0` | Codegen/PME skipped under metadata-only emit |
| `check_const_item_mutation_asymmetry` | `C_DIRECT` direct + `.set(15)` + `C_NODROP` + raw ptr | compile `0`, run `0`, `OBSERVED_DROPS=75` | — | `2` warnings (L35 `&mut`, L37 `modify`), `0` on L34/L36/L40 (`1` MIR dump) |
| `check_const_item_mutation_explicit_mut_ref` | `{ let r = &mut C; r.val = 50; }` | compile `0`, run `0`, `EXPLICIT_DROPS=50` | — | `1` warning (L9 `taking a mutable reference to a const item`) |
| `check_const_item_mutation_nested_drop` | `Outer { inner: Inner }` direct + `.set_inner(1)` | compile `0`, run `0`, `NESTED_DROPS=43` | — | `1.98.0`: `2` warn (L28 + L29); `1.102.0` (`940498dad7cb`): L28 suppressed, L29 stays |

### Mechanized Lean `v4.34.1` Verification & Kernel Audit (`derived`)

Compiled and audited via `support/check_lean.py` (`support/lean_check_receipt.json`, `generated_on: 2026-11-22`) under `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) with strict kernel flags (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`):

- **Module**: `support/PromoteTempsInfallibleZstMutAndConstMutationSoundness.lean` (`1,351` lines, `57,609` bytes, SHA-256 `e0a3f80b28c0c6253cc3fdd44eea696113166840593fdc9483926e937fd22cd4`).
- **Build Result**: `exit_code = 0`, `errors = 0`, `warnings = 0`, `olean_bytes = 2847120`, `wall_seconds = 5.066`, `peak_rss_kb = 566112`.
- **Forbidden Token Counts (Static Scan)**: `sorry: 0`, `admit: 0`, `omega: 0`, `bv_decide: 0`, `native_decide: 0`, `partial: 0`, `unsafe: 0`, `axiom: 0`, `opaque: 0`, `implemented_by: 0`, `extern: 0`, `Classical: 0`, `_unsafe_rec: 0`.
- **Kernel Environment Audit (`support/PromoteTempsAudit.lean`)**: `exit_code = 0`, `violations = 0`, `constants = 951`, `theorems = 367` (`226` without any axioms), `definitions = 467`, `inductive_types = 20`, `constructors = 76`, `recursors = 21`, `axioms_used = ["propext", "Quot.sound"]` (`wall_seconds = 3.256`, `peak_rss_kb = 1604320`).

| Lean Theorem (`PromoteTempsSoundness.*`) | Axioms Reported (`#print axioms`) | Proved Claim |
| --- | --- | --- |
| `collector_ignores_non_temps` | `[propext]` | `arg` and `userVar` locals remain unchanged under `Collector::visit_local` |
| `collector_drop_and_storage_noop` | `[propext]` | `Drop` and `StorageLive`/`StorageDead` preserve `TempState` |
| `collector_unpromotable_absorbing` | `[propext]` | `.unpromotable` is an absorbing sink of `Collector` |
| `collector_double_init_unpromotable` | `[propext]` | Multiple `store`/`callDest` writes force `.unpromotable` |
| `collector_mutBorrow_increments_uses` | `[propext]` | `MutatingUseContext::Borrow` increments `uses` on `.defined` temps |
| `collector_defined_after_single_init` | `[propext]` | Surviving `.defined` precludes subsequent writes or `otherMutUse` |
| `qualifHasMutInterior_optionNone_unsafeCellZst_false` | `[]` (zero axioms!) | `&None::<UnsafeCell<()>>` has `HasMutInterior = false` |
| `qualifHasMutInterior_unsafeCellZst_true` | `[]` (zero axioms!) | `&UnsafeCell<()>` has `HasMutInterior = true` despite `sizeOf = 0` |
| `validator_implies_ctfe_infallible` | `[propext]` | Every validated candidate + call contract evaluates to `.ok v` at CTFE |
| `promoteTemps_runtime_and_drop_trace_preserved` | `[propext, Quot.sound]` | Validated promotion preserves runtime outcomes & `DropTrace` across all branches & overflow modes |
| `promoteTemps_infallible_preserves_semantics_iff` | `[propext, Quot.sound]` | CTFE totality + runtime/drop preservation hold iff `qualifNeedsDrop = false` |
| `ce_div_zero_dead_branch_breaks_ctfe` | `[propext]` | `if false { &(1 / 0) }` panics at CTFE -> rejected by `Validator` |
| `ce_signed_min_div_neg1_breaks_ctfe` | `[propext]` | `i8::MIN / -1` rejected vs. `(-5) / -1` accepted |
| `ce_copy_index_oob_rejected_vs_place_index_base_promoted` | `[propext]` | Value-copy OOB indexing rejected; place-borrow base promoted with runtime panic retained |
| `ce_needsDrop_promotion_drops_side_effect` | `[propext]` | Promoting `NeedsDrop` value drops `[1]` from `DropTrace` -> rejected |
| `ce_addWithOverflow_dead_branch_keepOriginal_sound` | `[propext]` | Checked addition (`uses = 2`, `keep_original = true`) promotes `.ok 144` & retains panic in active branch |
| `ce_non_zst_move_deinit_preserved` | `[propext]` | `deinitMovedPlace = true` faults on non-ZST double move while permitting ZST reuse |
| `zst_mut_borrow_promoted_rodata_sound` | `[]` (zero axioms!) | 0-byte `&'static mut` reborrow on `.readOnly` memory succeeds in SB and TB (`sbStacks` preserved) |
| `dual_protected_zst_mut_borrows_rodata_sound` | `[]` (zero axioms!) | Dual `StrongProtector` (`split_at_mut(0)`) mutable reborrows succeed simultaneously on `.readOnly` static alloc |
| `nonzst_mut_borrow_rodata_ub_counterexample` | `[propext]` | Any nonzero mutable reborrow on `.readOnly` triggers `.writeToReadOnly` UB in SB and TB |
| `zst_mut_promoted_write_oob_ub` | `[propext]` | Any nonzero byte write through 0-byte promoted `&'static mut` triggers `.outOfBounds` UB |
| `validateRef_mut_syntactic_conservatism_and_unsafecell_zst_witness` | `[propext]` | Syntactic `&mut [T; 0]` admission vs. `&mut ()` rejection and `&UnsafeCell<()>` vs. `&None::<UnsafeCell<()>>` split |
| `constMutation_unobservable_iff_no_needsDrop` | `[propext]` | Non-deref mutation of `ConstRef` is unobservable iff `tyNeedsDrop = false` |
| `checkConstItemMutation_visitRvalue_false_positive_witness` | `[propext]` | Reproduces `C_DIRECT.set(15)` false positive despite nonzero `Drop` observation |
| `observed_drops_sum_eq_75` | `[]` (zero axioms!) | Exact trace `[10, 15, 50]` and `sumList = 75` matching `OBSERVED_DROPS=75` |
| `checkConstItemMutation_nestedDrop_198_vs_1102_witness` | `[propext]` | Reproduces `1.98.0` -> `1.102.0` `Outer.inner.val = 42` fix vs. persistent `Outer.set_inner` `&mut` false positive |
| `lintRepaired_exact_soundness_and_completeness` | `[propext]` | Symmetric `!tyNeedsDrop` lint warns iff the mutation is observationally unobservable |

---

## Revalidation

To reproduce every verification gate independently from the package or corpus root, execute the following self-contained commands without modifying repository files:

### 1. Re-verify Upstream Commit Pins and Primary Source Availability

```bash
python3 support/verify_pins.py --gh gh
```

Expected exit code `0`, confirming all 8 pinned 40-hex commit SHAs (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `940498dad7cb35a753a7cce104ab510b414e84de`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `ce66487ebbd7541212d22d01c39a808057d69f1f`, `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `5045d0056413266e57c625dcd7c365b10e377c52`) and all 26 upstream source URLs resolve cleanly (`passed: true` in `support/pin_receipt.json`).

### 2. Re-run Live `rustc` / Miri Probes and Baseline Parity Checks

```bash
python3 support/probe_promote_temps_and_const_item_mutation.py
```

Expected exit code `0` (`ALL_PROBES_PASSED`), executing all 30 promotion, Miri SB/TB, and `CheckConstItemMutation` cases against `support/specimens/*.rs` and `support/baseline_1_102_3ef0c22cd.json`, regenerating `support/probe_results.json` and the 21 MIR dumps under `support/mir_dumps/`.

### 3. Re-compile and Kernel-Audit the Lean `v4.34.1` Mechanization

```bash
python3 support/check_lean.py --lean lean
```

(Or pass `--wrap "<cgroup-runner> --mode file --"` when running under bounded memory/CPU governance with `lean` `v4.34.1`.) Expected exit code `0`, `passed: true`, `errors: 0`, `warnings: 0`, `violations: 0`, `Classical`: `0`, `_unsafe_rec`: `0`, `axioms_used`: `["propext", "Quot.sound"]`.

### 4. Re-validate Corpus Format, Catalog Index, and Hygiene Invariants

From the enclosing corpus root:

```bash
python3 tools/reference.py catalog && python3 tools/reference.py check
```

Expected output: `wrote CATALOG.json (1 reports)` and `reference check passed` with exit code `0`.

### Revalidation Triggers

Re-run all four checks and diff `promote_consts.rs`, `qualifs.rs`, `check_const_item_mutation.rs`, `required_consts.rs`, Miri `stacked_borrows/mod.rs` / `tree_borrows/mod.rs`, and `joshlf/anneal` `trusted/` whenever any of the following upstream changes land:
1. Any upstream change to `Validator::validate_ref` (especially expanding `&mut ()` or relaxing `ty::Array(_, 0)`).
2. Any change harmonizing `CheckConstItemMutation::visit_rvalue` with `is_const_item_without_destructor` after `ce66487ebbd7541212d22d01c39a808057d69f1f`.
3. Any change to Miri `sb_reborrow` / `tb_reborrow` 0-byte reborrow semantics (`size == Size::ZERO`) or `ConstQualifs` (`HasMutInterior`, `NeedsDrop`).
4. Any `joshlf/anneal` toolchain upgrade advancing the pinned `rustc` / `lean4` compiler versions or extending `Trusted.MirAst` with pre-borrowck `LocalInfo` fields or raw-allocation mutability rules.

*Basis:* `support/verify_pins.py`, `support/probe_promote_temps_and_const_item_mutation.py`, `support/check_lean.py`, and corpus schema tooling (`tools/reference.py`).
