# `rustc` Match Lowering: Fake Borrows, Guard Backtracking, Or-Pattern Drop Schedules, Uninhabited Scrutinees, and Slice/Range MIR Semantics

## Summary

`rustc` lowers `match` expressions (`compiler/rustc_mir_build/src/builder/matches/`) into MIR decision trees whose runtime soundness depends on a non-local contract between pattern exhaustiveness (`rustc_pattern_analysis`), guard borrow checking (`FakeBorrowCollector` + `rustc_borrowck`), post-borrowck erasure (`CleanupPostBorrowck`), and interpreter/codegen place evaluation (`rustc_const_eval`). A verifier or compiler consumer that inspects only `Runtime(PostCleanup)` MIR—after `BorrowKind::Fake(_)` assignments, `StatementKind::FakeRead`, and `TerminatorKind::FalseEdge` have been erased—cannot treat `TerminatorKind::Unreachable` at decision-tree fallback leaves as unconditionally dead without relying on pre-erasure borrowck soundness.

Five concrete invariants govern this pipeline:

1. **Two-point `FakeBorrowKind` lattice (`Shallow < Deep`) and `FakeReadCause::ForMatchGuard` (`util.rs`, `mod.rs`, `places_conflict.rs`, `conflict_errors.rs`):** When an arm has a match guard, `collect_fake_borrows` records `FakeBorrowKind::Shallow` on switched places and on strict dereference prefixes of switched and bound places, while reserving `FakeBorrowKind::Deep` exclusively for `TestableCase::Deref` (non-`Box` smart-pointer `deref!(...)` patterns lowered via `<P as Deref>::deref(&place)`). Because `place_components_conflict` returns `false` for `BorrowKind::Fake(FakeBorrowKind::Shallow)` whenever `borrow_place` is a strict prefix of `access_place` (`places_conflict.rs:288-293`), `Shallow` borrows block overwriting a switched enum discriminant or redirecting a reference/box pointer prefix while **permitting** guard mutations to unswitched locals (`match u { _ if { u = true; false } => false, x => x }` evaluates to `true`), unswitched `Box<T>` interiors without a deref pattern (`*b = true`), and unswitched variant-payload projections (`((p.0 as Some).0) = 42`). Conversely, a custom `DerefPure` smart pointer `s: SmartBool` tests an ephemeral deref temporary `(*temp)` invisible to `FakeBorrowCollector` (`util.rs:172-186, 199-205`); `s` therefore **must** carry `FakeBorrowKind::Deep` (printed in built MIR as `&fake _1` without `shallow`) so `s.0 = true` is rejected (`E0510`) before falling into `TerminatorKind::Unreachable`. Diagnostic codes split between **`E0506`** (when a real `BorrowKind::Shared` `ref_for_guard` binding loan conflicts first) and **`E0510`** (when only `&fake` + `FakeRead(ForMatchGuard)` conflicts, including behind `&T` where `PlaceExt::ignore_borrow` suppresses `BorrowKind::Shared` conflicts).
2. **Post-borrowck erasure and verified-MIR TCB coupling (`cleanup_post_borrowck.rs`, `joshlf/anneal` `Trusted.MirAst` / `Trusted.MirSemantics`):** `CleanupPostBorrowck` replaces every `Rvalue::Ref(_, BorrowKind::Fake(_), _)` assignment and `StatementKind::FakeRead(..)` with `StatementKind::Nop` and rewrites `TerminatorKind::FalseEdge` to `TerminatorKind::Goto`. In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst.StatementKind` maps `FakeRead` and `PlaceMention` fail-closed to `.unsupported` (`MirAst.lean:654-656`), while `Trusted.MirSemantics` evaluates `TerminatorKind.unreachable` to `.fault .undefined` (`MirSemantics.lean:1551-1552`). Consequently, proving absence of `.undefined` faults at decision-tree fallback blocks in `PostCleanup` MIR relies directly on `FakeBorrowCollector` + `mir_borrowck` having prevented prior match guards from invalidating ancestor branch tests.
3. **Or-pattern guard re-evaluation, non-`Copy` preservation, and leftmost-sub-branch LIFO drop order (`mod.rs`, `scope.rs`):** Or-patterns (`P_0 | P_1 if guard`) expand into separate `MatchTreeSubBranch` leaves that each bind `ref_for_guard = &source` (`ByRef::No`), evaluate a distinct lowered copy of `guard`, branch on `false` to `sub_branch.otherwise_block` (leaving non-`Copy` scrutinee fields unmoved), and move/copy `for_arm_body` bindings only along `guard_true_block`. Thus `(Some(x), _) | (_, Some(x)) if log_and_eq(x, 2)` on `(Some(1), Some(2))` executes the guard **twice** (`["guard:1", "guard:2"]`). However, `arm_block` is shared across all sub-branches of an arm: `Builder::bind_pattern` iterates `branch.sub_branches.into_iter().rev().with_position()`, passing `ScheduleDrops::No` to every sub-branch except the final iteration (`sub_branches[0]`, the leftmost sub-pattern), where `clear_match_arm_and_guard_scopes` resets `arm_scope.drops` and schedules LIFO drops for `sub_branches[0]`'s bindings. On `Ok((a, b)) | Err((b, a))`, `arm_block` statically drops `b` then `a` in **both** cases—dropping `(second, first)` on `Ok((first, second))` and `(first, second)` on `Err((first, second))` identically under native execution, Miri Stacked Borrows, and Miri Tree Borrows.
4. **Uninhabited (`Void`) `PlaceMention` vs `&Void` validity UB, and cross-crate single-variant `#[non_exhaustive]` dispatch (`rustc.rs`, `usefulness.rs`, `match_pair.rs`, `place.rs`):** `is_toplevel_exception` (`usefulness.rs:947-960`) allows zero-arm `match *p {}` on `*const Void` (`PlaceMention((*_1))` + `FakeRead(ForMatchedPlace)` + `Unreachable`). Adding a wildcard arm `match *p { _ => 99 }` lowers in `PostCleanup` MIR to `PlaceMention((*_1))` followed directly by `_0 = const 99_i32` with zero `discriminant`, `SwitchInt`, or `Unreachable`. Because Miri's `StatementKind::PlaceMention` calls `eval_place` -> `deref_pointer` (`place.rs:468-538`), which runs alignment/null/dereferenceability checks **only** when `ptr_ty.is_ref() || ptr_ty.is_box()` and skips them when `ptr_ty.is_raw_ptr()`, `match *p { _ => 99 }` executes cleanly in Miri (`rc = 0`, `RES=99`) on **both** `core::ptr::null::<Void>()` and aligned dangling `*const Void`. By contrast, `&*p` materializes a reference of type `&Void` and triggers immediate Miri value-validity Undefined Behavior (`constructing invalid value of type &Void: encountered a reference pointing to uninhabited type Void`). Across crate boundaries, a single-variant `#[non_exhaustive]` enum (`#[non_exhaustive] pub enum SingleNonExh { Only }`) rejects wildcard-free matches (`E0004`) and—via `adt_def.variants().len() > 1 || adt_def.is_variant_list_non_exhaustive()` (`match_pair.rs:399`)—forces `TestableCase::Variant` (`_2 = discriminant(_1); switchInt(move _2)`), whereas a closed single-variant enum (`pub enum SingleExh { Only }`) lowers as `Irrefutable` with zero `discriminant` or `SwitchInt`.
5. **Slice/range `PostCleanup` MIR primitives and constructive `Lean v4.34.1` proofs (`match_pair.rs`, `test.rs`, `as_place.rs`, `support/MatchLoweringFakeBorrowAndGuardSoundness.lean`):** Legacy `Rvalue::Len` is absent from modern `PostCleanup` MIR: dynamic slice length tests emit `Rvalue::UnaryOp(UnOp::PtrMetadata, ptr_or_ref)` paired with `BinOp::Eq` (exact slice pattern) or `BinOp::Ge` (variadic `..` slice pattern), suffix/subslice bindings emit `ProjectionElem::ConstantIndex { offset, min_length, from_end: true }` (`[-1 of 2]`) and `PlaceElem::Subslice { from, to, from_end: true }` (`[1:-1]`), fixed-size arrays `[T; N]` elide `PtrMetadata` and emit static `from_end: false` projections, and range patterns lower to chained `BinOp::{Le, Lt}` comparisons. The companion `Lean v4.34.1` module `support/MatchLoweringFakeBorrowAndGuardSoundness.lean` kernel-checks three main soundness theorems (`fakeBorrow_prevents_unreachable_fallthrough`, `orPattern_guard_backtracking_exact`, `nonExhaustive_requires_discriminant_dispatch`), three companion characterization theorems, and three constructive counterexamples (`ce1`–`ce3`) depending at most on `propext`.

## Applicability

### Covered Subjects and Their Relationships

The findings in this report apply to the concrete upstream revisions recorded in `REPORT.json`, related as follows:

| Subject | Repository & Full Revision | Version / Role in This Report |
| :--- | :--- | :--- |
| Primary compiler & interpreter subject | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` on `x86_64-unknown-linux-gnu`: primary source audited and executed live across all four empirical probes (`support/probe_match_lowering_fake_borrows.py`). |
| Newer upstream compiler revision | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`: full primary-source comparison across all 17 match-lowering, pattern-analysis, borrowck, post-borrowck cleanup, and interpreter files to establish cross-revision stability and exact line-number mappings. |
| Anneal MIR semantic anchor | `rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd` | Upstream `rustc` revision whose `rustc_middle::mir::syntax` and `rustc_const_eval::interpret::discriminant` definitions anchor `joshlf/anneal`'s `Trusted.MirAst` and `Trusted.MirSemantics`. |
| Anneal capture driver pin | `rust-lang/rust` @ `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | `1.98.0-nightly (f8a08b688 2026-05-30)` compiler library version checked by `joshlf/anneal`'s `trusted/rustc-capture/src/driver.rs:25`. |
| Downstream verified-MIR consumer | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` and `trusted/audit/TrustedBoundary.lean`: audited to establish which match-lowered MIR constructs are modeled vs rejected fail-closed as `.unsupported`. |
| Mechanization kernel | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `Lean v4.34.1` kernel (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) used to verify `support/MatchLoweringFakeBorrowAndGuardSoundness.lean`. |

### Cross-Revision Continuity (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` vs `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`)

Direct comparison of all 16 compiler source files between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`) establishes that **every semantic rule characterized in this report is identical across both revisions**, with only minor line-number shifts and syntactic cleanups:

- In `compiler/rustc_mir_build/src/builder/matches/mod.rs`, `if pos == Position::Last { ScheduleDrops::Yes } else { ScheduleDrops::No }` (`14210df0:556`) was refactored syntactically to `if pos.is_last() { ScheduleDrops::Yes } else { ScheduleDrops::No }` (`3ef0c22c:537`) with identical control flow.
- In `compiler/rustc_mir_build/src/builder/matches/match_pair.rs`, helper extraction shifted `PatKind::Variant` (`adt_def.variants().len() > 1 || adt_def.is_variant_list_non_exhaustive()`) from line `278` (`14210df0`) to line `399` (`3ef0c22c`), and `PatKind::DerefPattern` (`DerefPatBorrowMode::Box` vs `DerefPatBorrowMode::Borrow(mutability)`) from lines `311-334` (`14210df0`) to lines `432-455` (`3ef0c22c`).
- In `compiler/rustc_borrowck/src/places_conflict.rs`, `place_components_conflict`'s `BorrowKind::Fake(FakeBorrowKind::Shallow)` short-circuit moved from lines `276-281` (`14210df0`) to lines `288-293` (`3ef0c22c`) with unchanged logic.

Throughout **Findings** and **Evidence**, exact line coordinates are given for both revisions whenever they differ.

### Configuration, Dialect, and Feature Scope

- **MIR Dialect Sensitivity:** Fake borrows (`Rvalue::Ref(_, BorrowKind::Fake(FakeBorrowKind::{Shallow, Deep}), _)`) and `StatementKind::FakeRead(FakeReadCause::{ForMatchedPlace, ForMatchGuard, ForGuardBinding}, _)` exist **only** in pre-cleanup MIR (`-Zdump-mir=built` through `mir_borrowck`). `CleanupPostBorrowck` (`-Zdump-mir=CleanupPostBorrowck` and all later `Runtime(PostCleanup)` passes, including `optimized_mir`) erases them to `Nop`. By contrast, `StatementKind::PlaceMention` and `TerminatorKind::Unreachable` survive `CleanupPostBorrowck` into `Runtime(PostCleanup)` MIR (unless a later optimization pass eliminates `PlaceMention`).
- **Unstable Feature Gates:** Exercising `FakeBorrowKind::Deep` via `deref!(true)` requires `#![feature(deref_patterns)]` (plus `#![feature(deref_pure_trait)]` and `unsafe impl core::ops::DerefPure` when testing a user-defined smart pointer rather than `Box<T>`, `Rc<T>`, or `Arc<T>`). All other findings (regular switched borrows, deref-prefix borrows, unswitched guard mutations, or-pattern guard backtracking and drop order, uninhabited `enum Void {}`, cross-crate `#[non_exhaustive]`, and slice/range patterns) apply to stable Rust (`--edition=2021` and `--edition=2024`).
- **Miri Aliasing Models:** Dynamic UB/non-UB claims for or-pattern guards, drop schedules, unswitched guard mutations, and `*const Void` vs `&Void` were executed under both Miri's default Stacked Borrows model and Tree Borrows (`-Zmiri-tree-borrows`) on `x86_64-unknown-linux-gnu`.

## Findings

### Finding 1: The `FakeBorrowKind::{Shallow, Deep}` Lattice, Dereference-Prefix Protection, and `FakeReadCause::ForMatchGuard` Borrowck Barrier

`Basis: source + execution + derived`

#### 1.1 `FakeBorrowCollector` Collection Rules (`util.rs`)

When lowering a `match` arm that carries a pattern guard (`if guard_expr`), `Builder::bind_and_guard_matched_candidate` (`compiler/rustc_mir_build/src/builder/matches/mod.rs:2387-2495` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`; `2416-2521` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) invokes `collect_fake_borrows` (`compiler/rustc_mir_build/src/builder/matches/util.rs:71-101` at `3ef0c22c`; `69-99` at `14210df0`). `FakeBorrowCollector` (`util.rs:103-231` at `3ef0c22c`; `101-227` at `14210df0`) maintains `fake_borrows: FxIndexMap<Place<'tcx>, FakeBorrowKind>` ordered by the two-element lattice $\mathsf{Shallow} \sqsubset \mathsf{Deep}$:

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1
// compiler/rustc_mir_build/src/builder/matches/util.rs:117-153
fn fake_borrow(&mut self, place: Place<'tcx>, kind: FakeBorrowKind) {
    if self.fake_borrows.get(&place) == Some(&FakeBorrowKind::Deep) {
        return;
    }
    self.fake_borrows.insert(place, kind);
    // Also fake borrow prefixes of deref patterns.
    self.fake_borrow_deref_prefixes(place, kind);
}

fn fake_borrow_deref_prefixes(&mut self, place: Place<'tcx>, kind: FakeBorrowKind) {
    for (place_ref, elem) in place.iter_projections().rev() {
        if let ProjectionElem::Deref = elem {
            // Insert a shallow borrow after a deref. For other projections the borrow of
            // `place_ref` will conflict with any mutation of `place.local`.
            self.fake_borrows
                .entry(place_ref.to_place(self.cx.tcx))
                .and_modify(|k| *k = std::cmp::max(*k, kind))
                .or_insert(kind);
        }
    }
}
```

Note that `FakeBorrowKind` derives `Ord` in declaration order `Shallow, Deep`, so `std::cmp::max(*k, kind)` computes the lattice join $\mathsf{join}(k_1, k_2)$. `FakeBorrowCollector` populates this map via two visitors over each candidate's pre-binding/test summary:

1. **Tested places (`visit_match_pair`, `util.rs:163-196` at `3ef0c22c`; `161-193` at `14210df0`):**
   - If `match_pair.testable_case` is `Some(TestableCase::Deref { .. })`:
     - If `match_pair.place` is `Some(place)` and `place.local` is **not** in `temps` (the map of ephemeral `Deref` temporaries allocated by match lowering), `self.fake_borrow(place, FakeBorrowKind::Deep)` is called, and `FakeBorrowCollector` **returns without recursing** into `match_pair.subpairs` (`util.rs:172-186` at `3ef0c22c`). Those `subpairs` project through `(*temp)` and cannot be borrowed across the entire match because `temp` is initialized lazily inside the `TestKind::Deref` block.
   - For **every other** `Some(_)` `TestableCase` (`Variant`, `Constant`, `Range`, `Slice`, `Never`) on a non-`temps` `Some(place)`:
     - `self.fake_borrow(place, FakeBorrowKind::Shallow)` is called, followed by recursion into `match_pair.subpairs` (`util.rs:187-195` at `3ef0c22c`).
   - If `match_pair.testable_case` is `None` (irrefutable structural Decomposition: tuples, structs, closed single-variant enums, wildcards, and `Box<T>` deref patterns under `DerefPatBorrowMode::Box`), **no fake borrow is inserted for `match_pair.place` itself**; the visitor simply recurses into `match_pair.subpairs`.
2. **Pattern bindings (`visit_binding`, `util.rs:198-230` at `3ef0c22c`; `195-227` at `14210df0`):**
   - If `source.local` is not in `temps`, `self.fake_borrow_deref_prefixes(*source, FakeBorrowKind::Shallow)` is called **without** calling `self.fake_borrow(*source, ...)`. Direct mutation of an unprojected local `u` bound by `x` (`source = _1`, zero `ProjectionElem::Deref` elements) therefore inserts **zero** fake borrows, whereas binding `y` inside `&y` (`source = (*_1)`) inserts `&fake shallow _1` so the guard cannot reassign `x = &other` between the guard's shared borrow of `(*_1)` and `arm_block`'s lazy copy/move of `(*_1)` (`mod.rs:2511-2515` at `3ef0c22c`).

#### 1.2 Why `Box<T>` Uses Paired `Shallow` Borrows While Custom `DerefPure` Requires `Deep`

A critical subtlety separates built-in `Box<T>` dereference patterns from general `DerefPure` smart-pointer dereference patterns (`compiler/rustc_mir_build/src/builder/matches/match_pair.rs:432-455` at `3ef0c22c`; `311-334` at `14210df0`):

- **`DerefPatBorrowMode::Box` (`Box<bool>`):** `MatchPairTree::for_pattern` lowers `PatKind::Deref` and `PatKind::DerefPattern { borrow: DerefPatBorrowMode::Box }` identically: it projects `place = tcx.mk_place_deref(place)` (`(*_1)`), recurses on `subpattern` with `(*_1)`, and classifies the deref node itself as `testable_case: None` (irrefutable). When `subpattern` tests `true` (`TestableCase::Constant` on `(*_1)`), `visit_match_pair` calls `fake_borrow((*_1), Shallow)`, which inserts **`&fake shallow (*_1)`** and—via `fake_borrow_deref_prefixes`—**`&fake shallow _1`**. Together, these two shallow borrows prevent both `*b = true` (conflicts with `&fake shallow (*_1)`) and `b = Box::new(true)` (conflicts with `&fake shallow _1`).
- **`DerefPatBorrowMode::Borrow(mutability)` (`SmartBool` with `unsafe impl DerefPure`):** User-defined and library `DerefPure` types (`Rc`, `Arc`, or custom `struct SmartBool(pub bool)`) cannot be projected via built-in MIR `ProjectionElem::Deref`. Instead, `match_pair.rs:440-455` allocates a fresh local `temp` (`temps.insert(temp)`), builds `subpairs` rooted at `(*temp)`, and marks `match_pair.place` (`_1: SmartBool`) with `TestableCase::Deref { temp, mutability }`. At runtime, `Builder::perform_test` (`test.rs:311-382` at `3ef0c22c`; `309-380` at `14210df0`) emits `temp = <SmartBool as Deref>::deref(&_1)` and switches on `(*temp)`. If `_1` received only `FakeBorrowKind::Shallow`, `place_components_conflict` (`compiler/rustc_borrowck/src/places_conflict.rs:288-293` at `3ef0c22c`; `276-281` at `14210df0`) would evaluate a write to `s.0` (`_1.0`) against `borrow_place = _1` as follows:

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1
// compiler/rustc_borrowck/src/places_conflict.rs:288-297
if borrow_kind == BorrowKind::Fake(FakeBorrowKind::Shallow)
    && borrow_place.projection.len() < access_place.projection.len()
{
    // Mutable access to a subplace of a shallowly borrowed place is allowed, e.g.
    // `(_1 as Some).0 = ...` when `_1` is shallowly borrowed.
    return false;
}
```

Because `borrow_place` (`_1`, length `0`) is a strict prefix of `access_place` (`_1.0`, length `1`), `Shallow` would return `false` (`NoConflict`), allowing a guard on arm `deref!(false) if { s.0 = true; false }` to mutate `s.0` from `false` to `true`, fail the guard, re-run `<SmartBool as Deref>::deref(&_1)` in the next test block (now yielding `true`, which arm 1 already ruled out!), and fall directly into `otherwise_block`'s `TerminatorKind::Unreachable` (`mod.rs:1648` at `3ef0c22c`). Emitting `FakeBorrowKind::Deep` (`&fake _1`) bypasses the `Shallow` prefix exception in `places_conflict.rs:288`, rejecting `s.0 = true` with `error[E0510]: cannot assign s.0 in match guard`.

#### 1.3 Temporal Span of `&fake` Loans and Why `E0506` Splits from `E0510`

In `bind_and_guard_matched_candidate` (`mod.rs:2419-2470` at `3ef0c22c`; `2448-2496` at `14210df0`), MIR statements for a guarded sub-branch are emitted in a strict order:

1. `bind_matched_candidate_for_guard` (`mod.rs:2419` -> `2634-2697` at `3ef0c22c`) creates a `ref_for_guard` temporary for each pattern binding via `BorrowKind::Shared` (`_ref = &source`, `ByRef::No`)—even for `move` bindings—so that a failing guard never moves out of the scrutinee.
2. Each `(place, kind)` in `fake_borrows` is assigned `_fb_temp = &fake [shallow] place` (`Rvalue::Ref(erased_region, BorrowKind::Fake(kind), place)`, `mod.rs:2432-2439` at `3ef0c22c`).
3. The guard expression `guard` is lowered into a boolean `cond` (`mod.rs:2455` at `3ef0c22c`).
4. Immediately **after** `guard` evaluation—before branching on `cond`—`rustc` emits `StatementKind::FakeRead(FakeReadCause::ForMatchGuard, _fb_temp)` for every fake-borrow temporary (`mod.rs:2465-2469` at `3ef0c22c`) and `StatementKind::FakeRead(FakeReadCause::ForGuardBinding, _ref)` for every `ref_for_guard` temporary (`mod.rs:2505-2509` at `3ef0c22c`).

In NLL (`rustc_borrowck`), those post-guard `FakeRead` uses force every `&fake` loan and every `ref_for_guard` loan to remain live across the entire guard CFG. When a guard attempts an illegal write, `MirBorrowckCtxt::report_illegal_mutation_of_borrowed` (`compiler/rustc_borrowck/src/diagnostics/conflict_errors.rs:4016-4058` at `3ef0c22c`) dispatches on `loan.kind`:

- If the first conflicting loan in `BorrowSet` order is `BorrowKind::Shared` (from `ref_for_guard` emitted in Step 1 before `&fake` in Step 2, e.g., `Some(_v) if { x = None; false }`), `rustc` emits **`error[E0506]: cannot assign to x because it is borrowed`**.
- If no `BorrowKind::Shared` loan conflicts—either because the pattern used a wildcard payload `Some(_)` (no `ref_for_guard` created) or because the binding dereferenced an immutable `&T` (`&y` on `x: &i32` or `&[a, ..]` on `x: &[i32]`, where `PlaceExt::ignore_borrow` at `places_conflict.rs:230-232` ignores borrows behind `&T` since `&T` already guarantees immutability of `*x`, leaving `x` itself protected solely by `&fake shallow _1`)—the conflicting loan has `loan.kind == BorrowKind::Fake(_)`. `classify_immutable_section` (`conflict_errors.rs:4297-4322` at `3ef0c22c`) inspects the `FakeReadCause::ForMatchGuard` user of the fake-borrow temporary, labels the section `"match guard"`, and emits **`error[E0510]: cannot assign ... in match guard`**.

#### 1.4 Empirical 9-Case `FakeBorrow` & Post-Cleanup Erasure Matrix (`rustc 1.98.0-nightly`)

Running `support/probe_match_lowering_fake_borrows.py` (`probe_1_fake_borrow_matrix`) against `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) with `-Zdump-mir=built,CleanupPostBorrowck` confirms every cell of this classification:

| Probe Case | Scrutinee & Pattern + Guard | `rc` | Diagnostic | `&fake` Borrows in `built` MIR | `FakeRead`s in `built` MIR | Surviving `&fake` / `FakeRead` After `CleanupPostBorrowck` |
| :--- | :--- | :---: | :--- | :--- | :--- | :---: |
| `mutate_switched_enum_with_binding_in_guard` | `x: Option<i32>`, `Some(_v) if { x = None; false }` | `1` | `E0506` | `["&fake shallow _1"]` | `ForGuardBinding(_5)`, `ForMatchGuard(_2)`, `ForMatchedPlace(_1)` | `[]` / `[]` |
| `mutate_switched_enum_wildcard_payload_in_guard` | `x: Option<i32>`, `Some(_) if { x = None; false }` | `1` | `E0510` | `["&fake shallow _1"]` | `ForMatchGuard(_2)`, `ForMatchedPlace(_1)` | `[]` / `[]` |
| `mutate_deref_prefix_bound_in_guard` | `x: &i32`, `&y if { x = &other; y == 1 }` | `1` | `E0510` | `["&fake shallow _1"]` | `ForGuardBinding(_5)`, `ForMatchGuard(_3)`, `ForMatchedPlace((*_1))` | `[]` / `[]` |
| `mutate_slice_ref_prefix_in_guard` | `x: &[i32]`, `[a, ..] if { x = &other; *a == 1 }` | `1` | `E0510` | `["&fake shallow (*_1)", "&fake shallow _1"]` | `ForMatchGuard(_3)`, `ForMatchGuard(_4)`, `ForMatchedPlace((*_10), _1)` | `[]` / `[]` |
| `mutate_box_deref_pat_in_guard_shallow_pair` | `b: Box<bool>`, `deref!(false) if { *b = true; false }` | `1` | `E0510` | `["&fake shallow (*_1)", "&fake shallow _1"]` | `ForMatchGuard(_2)`, `ForMatchGuard(_3)`, `ForMatchedPlace(_1)` | `[]` / `[]` |
| `mutate_custom_deref_pure_in_guard_deep_borrow` | `s: SmartBool`, `deref!(false) if { s.0 = true; false }` | `1` | `E0510` | `["&fake _1"]` (`Deep`) | `ForMatchGuard(_4)`, `ForMatchedPlace(_1)` | `[]` / `[]` |
| `mutate_unswitched_local_in_guard_allowed` | `u: bool`, `_ if { u = true; false } => false, x => x` | `0` | none | `[]` | `ForMatchedPlace(_1)` | `[]` / `[]` |
| `mutate_unswitched_box_inner_without_deref_pat_allowed` | `b: Box<bool>`, `_ if { *b = true; false } => false, v => *v` | `0` | none | `[]` | `ForMatchedPlace(_1)` | `[]` / `[]` |
| `mutate_unswitched_payload_projection_allowed` | `p: (Option<i32>, bool)`, `(Some(_), false) if { if let Some(r) = &mut p.0 { *r = 42; } false }` | `0` | none | `["&fake shallow (_1.0)", "&fake shallow (_1.1)"]` | `ForMatchGuard(_2)`, `ForMatchGuard(_3)`, `ForMatchedPlace(_1)` | `[]` / `[]` |

Executing the two subtle allowed cases in `probe_2_or_pattern_guards_and_drop_order` confirms that `match u { _ if { u = true; false } => false, x => x }` evaluates to `UNSWITCHED_MUT_GUARD=true`, and mutating `((_1.0 as Some).0) = 42` while `_1.0` holds `&fake shallow (_1.0: Option<i32>)` evaluates to `UNSWITCHED_PAYLOAD_MUT_GUARD=42` with zero Miri violations under both Stacked Borrows and Tree Borrows.

---

### Finding 2: Post-Borrowck Erasure (`CleanupPostBorrowck`) and Verified-Compiler TCB Obligations on `TerminatorKind::Unreachable`

`Basis: source + execution + derived`

#### 2.1 `CleanupPostBorrowck` Erasure Rules (`cleanup_post_borrowck.rs`)

Immediately after `mir_borrowck` completes, `CleanupPostBorrowck::run_pass` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:24-75` at `3ef0c22c`; `24-77` at `14210df0`) strips every match-guard borrowck artifact from the MIR body:

1. `StatementKind::Assign((_, Rvalue::Ref(_, BorrowKind::Fake(_), _)))` is overwritten with `StatementKind::Nop` (`cleanup_post_borrowck.rs:34, 41` at `3ef0c22c`).
2. `StatementKind::FakeRead(..)` is overwritten with `StatementKind::Nop` (`cleanup_post_borrowck.rs:35, 41` at `3ef0c22c`).
3. `TerminatorKind::FalseEdge { real_target, .. }`—inserted on guard branches (`mod.rs:2470-2475` at `3ef0c22c`) so NLL dataflow treats `otherwise_block` as reachable without waiting for guard value analysis—is replaced by `TerminatorKind::Goto { target: real_target }` (`cleanup_post_borrowck.rs:66-69` at `3ef0c22c`).

 Crucially, `CleanupPostBorrowck` **retains** every `TerminatorKind::Unreachable` block generated by `Builder::build_match_tree` (`mod.rs:1648, 2051, 2403` at `3ef0c22c`; `1688, 2093, 2432` at `14210df0`) at decision-tree fallback edges that `rustc_pattern_analysis` proved statically unreachable under immutable-scrutinee assumptions.

#### 2.2 Trust-Boundary Seam in `joshlf/anneal` (`Trusted.MirAst` and `Trusted.MirSemantics`)

Inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` reveals how this erasure boundary interacts with a verified MIR consumer:

- **`StatementKind` (`trusted/lean/Trusted/MirAst.lean:650-663`, `MirSemantics.lean:1370-1428`):** `MirAst.StatementKind` admits only `.assign`, `.storageLive`, `.storageDead`, and `.nop`. Both `StatementKind::FakeRead` and `StatementKind::PlaceMention` map fail-closed to `StatementKind.unsupported` (`MirAst.lean:654-656`), which steps to `.fault .unsupported` (`MirSemantics.lean:1427`). Thus `Anneal` **cannot** consume raw `built` MIR directly (every `match` emits `FakeRead(ForMatchedPlace)` in `built` MIR); it consumes post-borrowck / optimized `Runtime(PostCleanup)` MIR after `CleanupPostBorrowck` has erased `FakeRead` and `&fake` borrows (and after `PlaceMention` is either eliminated or rejected fail-closed if retained).
- **`TerminatorKind.unreachable` (`trusted/lean/Trusted/MirAst.lean:776, 789`, `MirSemantics.lean:1551-1552`):** `MirAst.TerminatorKind.unreachable` is modeled first-class and evaluates to `.fault .undefined` (Undefined Behavior).
- **Soundness Implication (`derived`):** When `Anneal` verifies a Rust function containing a `match` with guards by symbolically executing its `Runtime(PostCleanup)` MIR, symbolic execution sees concrete `Rvalue::Discriminant` + `SwitchInt` tests and concrete guard mutations, **without** seeing the erased `&fake` borrows. For pure first-order functions modeled completely inside `Trusted.MirSemantics`, symbolic execution re-verifies branch reachability directly on MIR state. However, whenever a guard invokes an abstractly specified helper (`#[spec]`) whose specification leaves unmentioned frame state unconstrained—or in any translation-validation architecture assuming `rustc`'s generated fallback `Unreachable` blocks are unreachable—freedom from `.fault .undefined` at `TerminatorKind.unreachable` depends on `mir_borrowck` + `FakeBorrowCollector` having rejected mutations to ancestor-tested places. Counterexample `ce1` in Section 6 demonstrates constructively that weakening `FakeBorrowKind::Deep` to `Shallow` on `TestableCase::Deref` drives a borrowck-clean, statically exhaustive match directly into `TerminatorKind::Unreachable`.

---

### Finding 3: Or-Pattern Sub-Branch Lowering, Guard Re-Evaluation, Non-`Copy` Preservation, and Final-Sub-Branch LIFO Drop Scheduling

`Basis: source + execution + derived`

#### 3.1 Split-Sub-Branch Guard Lowering and Two-Step Binding (`mod.rs`)

When an arm contains a top-level or nested or-pattern (`P_0 | P_1 if guard => body`), `Builder::build_match_tree` (`mod.rs:1620-1690` at `3ef0c22c`) expands the candidate tree into a `Vec<MatchTreeSubBranch<'tcx>>` stored on `MatchTreeBranch::sub_branches`. Each leaf `MatchTreeSubBranch` corresponds to one disjunctive alternative and owns its own entry block, its own `bindings: Vec<Binding<'tcx>>`, and its own `otherwise_block` pointing to the next decision-tree alternative!

Inside `bind_and_guard_matched_candidate` (`mod.rs:2387-2529` at `3ef0c22c`; `2416-2555` at `14210df0`), each `MatchTreeSubBranch` with a guard is lowered **independently**:

1. **Non-destructive guard binding (`bind_matched_candidate_for_guard`, `mod.rs:2634-2697` at `3ef0c22c`):** Every pattern variable `x` bound in the sub-branch creates a guard-local shared reference `_ref_for_guard = &source` (`ByRef::No`, `ScheduleDrops::Yes` only on temporary guard storage, never on the scrutinee place `source`). Even when `x` is a by-value `move` binding of a non-`Copy` type (`DropToken`), the guard receives `&DropToken` by shared reference (`user_binding_mode` vs guard dereference projection).
2. **Per-sub-branch guard cloning:** `guard` is lowered fresh from THIR inside `bind_and_guard_matched_candidate` (`let guard = self.thir[guard].clone()`, `mod.rs:2450` at `3ef0c22c`) for **each** `MatchTreeSubBranch`.
3. **Short-circuit backtracking on `false` (`mod.rs:2470-2476, 2523-2527` at `3ef0c22c`):** A `SwitchInt` on `cond` branches on `true` to `FalseEdge { real_target: guard_true_block, imaginary_target: otherwise_post_guard_block }` and on `false` to `otherwise_post_guard_block`, which exits `guard_scope` (dropping only temporaries created inside the guard, leaving the scrutinee intact!) and jumps to `sub_branch.otherwise_block`—entering the **next** or-pattern alternative (or the next match arm) with any guard side effects preserved in program state.
4. **Lazy by-value binding on `true` (`bind_matched_candidate_for_arm_body`, `mod.rs:2511-2515, 2699-2735` at `3ef0c22c`):** Only inside `guard_true_block` does `rustc` move or copy `source` into the arm-body local `var_local` (`storage_live_binding` + `schedule_drop_for_binding` gated by `schedule_drops`), before jumping to the single shared `arm_block`!

#### 3.2 Reverse Sub-Branch Iteration and Single Static `arm_block` Drop Schedule (`mod.rs:534-546`, `scope.rs:1760-1774`)

Although an or-pattern arm has $k \ge 2$ entry paths (`sub_branches[0..k]`), `rustc` lowers the arm body `expr` **once** inside a single shared `arm_block`. Because MIR drop elaboration schedules unwinding and scope-exit drops from a single static `region::Scope` tree (`arm_scope`), `arm_block` can have **only one static drop order** over the arm's `VarBinding` locals (`var_local_a`, `var_local_b`), even when different sub-branches bind those variables in opposite syntactic orders (such as `Ok((a, b)) | Err((b, a))`).

`Builder::bind_pattern` (`compiler/rustc_mir_build/src/builder/matches/mod.rs:498-550` at `3ef0c22c`; `517-569` at `14210df0`) establishes this static drop schedule as follows:

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1
// compiler/rustc_mir_build/src/builder/matches/mod.rs:534-546
for (pos, sub_branch) in branch.sub_branches.into_iter().rev().with_position() {
    let schedule_drops =
        if pos.is_last() { ScheduleDrops::Yes } else { ScheduleDrops::No };
    self.bind_and_guard_matched_candidate(
        sub_branch,
        &mut arm_match_scope,
        guard,
        has_guard_borrows,
        schedule_drops,
        storages_alive,
    );
}
```

Combined with `bind_and_guard_matched_candidate` (`mod.rs:2457-2459` at `3ef0c22c`) and `Builder::clear_match_arm_and_guard_scopes` (`compiler/rustc_mir_build/src/builder/scope.rs:1760-1774` at `3ef0c22c`; `1791-1805` at `14210df0`):

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1
// compiler/rustc_mir_build/src/builder/matches/mod.rs:2457-2459
if matches!(schedule_drops, ScheduleDrops::No) {
    self.clear_match_arm_and_guard_scopes(arm_match_scope.region_scope);
}
```

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1
// compiler/rustc_mir_build/src/builder/scope.rs:1760-1773
pub(crate) fn clear_match_arm_and_guard_scopes(&mut self, region_scope: region::Scope) {
    let scopes = &mut self.scopes;
    for scope in scopes.scopes.iter_mut().rev() {
        if scope.region_scope == region_scope {
            scope.drops.clear();
            break;
        }
        scope.drops.clear();
    }
}
```

Tracing `branch.sub_branches = [sub_0, sub_1]` (`Ok((a, b)) | Err((b, a))`):

1. `.into_iter().rev().with_position()` visits `sub_1` (`Err((b, a))`) **first** with `pos = First` (`!pos.is_last()`, so `schedule_drops = ScheduleDrops::No`). During `sub_1`'s guard lowering, `clear_match_arm_and_guard_scopes` clears any accumulated drops in `guard_scope` and `arm_scope`, and `bind_matched_candidate_for_arm_body` skips `schedule_drop_for_binding` because `schedule_drops == ScheduleDrops::No` (`mod.rs:2721`).
2. Next, the loop visits `sub_0` (`Ok((a, b))`) **last** with `pos = Last` (`pos.is_last() == true`, so `schedule_drops = ScheduleDrops::Yes`). `bind_matched_candidate_for_arm_body` iterates `sub_0.bindings` in declaration order `[a, b]`, pushing `a` then `b` onto `arm_scope.drops`.
3. Because `scope.drops` is unwound in **LIFO (reverse) order** on scope exit, `arm_block` exit drops **`b` first, then `a`** regardless of which sub-branch jumped to `arm_block`!
   - When `Ok((DropToken("first", 1), DropToken("second", 2)))` matches `sub_0`, `a = first:1` and `b = second:2`; dropping `[b, a]` drops **`second:2` then `first:1`**.
   - When `Err((DropToken("first", 1), DropToken("second", 2)))` matches `sub_1`, `b = first:1` and `a = second:2`; dropping `[b, a]` drops **`first:1` then `second:2`**.

#### 3.3 Empirical Verification Across Native `x86_64`, Miri Stacked Borrows, and Miri Tree Borrows

`probe_2_or_pattern_guards_and_drop_order` compiles and runs the complete five-scenario harness natively and inside Miri (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) under both Stacked Borrows and `-Zmiri-tree-borrows`, producing bit-for-bit identical output across all three engines (`native_equals_miri_stacked_and_tree: true`, `rc = 0`):

| Scenario | Input | Observed Runtime Trace (`native` = `Miri SB` = `Miri TB`) | Verified Semantic Property |
| :--- | :--- | :--- | :--- |
| Or-pattern guard re-evaluation | `(Some(1), Some(2))` on `(Some(x), _) \| (_, Some(x)) if log_and_eq(x, 2) => x * 10` | `OR_GUARD_RES=20 LOG=["guard:1", "guard:2"]` | Guard executes twice (`x = 1` fails, backtracks to second sub-branch, `x = 2` succeeds). |
| Leftmost sub-branch drop schedule (`sub_0`) | `Ok((DropToken("first", 1), DropToken("second", 2)))` on `Ok((a, b)) \| Err((b, a))` | `DROP_BRANCH0=["arm:a=first:b=second", "drop:second:2", "drop:first:1"]` | Drops `b` (`second:2`) then `a` (`first:1`) in LIFO order of `Ok((a, b))`. |
| Secondary sub-branch drop schedule (`sub_1`) | `Err((DropToken("first", 1), DropToken("second", 2)))` on `Ok((a, b)) \| Err((b, a))` | `DROP_BRANCH1=["arm:a=second:b=first", "drop:first:1", "drop:second:2"]` | Still drops `b` (`first:1`) then `a` (`second:2`) using `sub_0`'s static LIFO schedule. |
| Non-`Copy` survival across failing guard | `(DropToken("left", 1), DropToken("right", 2))` on `(a, b) if fail_log(&a, &b) => ..., (x, y) => ...` | `GUARD_FAIL_NONCOPY=["guard_fail:a=left:b=right", "fallback_arm:x=left:y=right", "drop:right:2", "drop:left:1"]` | `ByRef::No` guard borrow leaves non-`Copy` fields unmoved for fallback arm `(x, y)`. |
| Allowed unswitched guard mutations | `u = false` (`u = true` in guard) & `(Some(1), false)` (`*r = 42` in guard) | `UNSWITCHED_MUT_GUARD=true`, `UNSWITCHED_PAYLOAD_MUT_GUARD=42` | Both compile (`rc = 0`) and pass Miri Stacked Borrows and Tree Borrows with zero UB. |

---

### Finding 4: Uninhabited (`Void` / `!`) Scrutinees, Raw-Pointer `PlaceMention` Semantics vs `&Void` Validity UB, and Cross-Crate Single-Variant `#[non_exhaustive]` Dispatch

`Basis: source + execution + derived`

#### 4.1 Top-Level Uninhabited Exception vs Wildcard Lowering (`rustc_pattern_analysis`, `matches/mod.rs`)

On stable Rust (without `#![feature(exhaustive_patterns)]`), `rustc_pattern_analysis` treats uninhabited types (`!`, `enum Void {}`) asymmetrically depending on whether the uninhabited place is at the **top level** of the `match` scrutinee (`compiler/rustc_pattern_analysis/src/usefulness.rs:947-965` at `3ef0c22c`; `953-971` at `14210df0` and `rustc.rs:395-415`):

1. **Zero-arm match (`match v {}` on `v: Void`, `match *r {}` on `r: &Void`, `match *p {}` on `p: *const Void`):** `is_toplevel_exception` (`usefulness.rs:947`) holds when the column at the root scrutinee is uninhabited (`cx.is_uninhabited(ty)`)—provided that for a raw pointer dereference `*p` in safe code it would be rejected by typeck/unsafeck, whereas inside `unsafe { match *p {} }` `is_toplevel_exception` allows `Constructor::Never` to be omitted without an arm! `Builder::match_expr` (`mod.rs:334-390` at `3ef0c22c`) lowers the scrutinee via `lower_scrutinee` (emitting `PlaceMention(scrutinee)`), emits `FakeRead(ForMatchedPlace(None), scrutinee)` in `built` MIR, and terminates the empty candidate tree with `TerminatorKind::Unreachable` (`mod.rs:2403` at `3ef0c22c`).
2. **Wildcard match on raw pointer (`unsafe { match *p { _ => 99 } }` on `p: *const Void`):** The single wildcard arm `_` is `Irrefutable` (`testable_case: None`, zero bindings). `Builder::match_expr` emits `PlaceMention((*_1))` (`mod.rs:383` at `3ef0c22c`), `FakeRead(ForMatchedPlace(None), (*_1))` (erased by `CleanupPostBorrowck`), and jumps unconditionally to `arm_block` (`_0 = const 99_i32; return`) with **zero `Rvalue::Discriminant`, zero `SwitchInt`, and zero `TerminatorKind::Unreachable`**.

#### 4.2 Why `match *p { _ => 99 }` Passes Miri on Null and Valid `*const Void` While `&*p` Is Immediate UB

In `rustc_const_eval` (shared by CTFE and Miri), `StatementKind::PlaceMention(place)` executes (`compiler/rustc_const_eval/src/interpret/step.rs:120-123` at `3ef0c22c`):

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1
// compiler/rustc_const_eval/src/interpret/step.rs:120-122
StatementKind::PlaceMention(place) => {
    let _ = self.eval_place(**place)?;
}
```

For `place = (*_1)` where `_1: *const Void`, `eval_place` calls `InterpCx::deref_pointer` (`compiler/rustc_const_eval/src/interpret/place.rs:468-538` at `3ef0c22c`; `466-536` at `14210df0`):

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1
// compiler/rustc_const_eval/src/interpret/place.rs:490-523
let ptr_ty = op.layout.ty;
let mplace = if ptr_ty.is_ref() || ptr_ty.is_box_global(*self.tcx) {
    // Check alignment, non-nullness, and dereferenceability for references and boxes.
    ...
} else {
    assert!(ptr_ty.is_raw_ptr());
    // For raw pointers, deref_pointer performs NO null, alignment, or inbounds check!
    MPlaceTy::from_aligned_ptr_maybe_unaligned(ptr, pointee_layout, meta)
};
```

Because `PlaceMention` discards `mplace` without reading memory or validating a `Void` value—and because `deref_pointer` explicitly skips null/alignment/dereferenceability checks when `ptr_ty.is_raw_ptr()`—**both** `core::ptr::null::<Void>()` and `core::ptr::NonNull::<Void>::dangling().as_ptr()` execute `unsafe { match *p { _ => 99 } }` cleanly in Miri (`rc = 0`, `RES=99`)!

By contrast, evaluating `let r: &Void = unsafe { &*p }; match *r {}` executes `Rvalue::Ref` to construct a value of type `&Void` **before** reaching the match. Miri's value-validity invariant checks pointee inhabitedness when constructing a safe reference `&T`, aborting immediately (`rc = 1`):

```text
error: Undefined Behavior: constructing invalid value of type &Void: encountered a reference pointing to uninhabited type Void
```

#### 4.3 Cross-Crate Single-Variant `#[non_exhaustive]` vs Exhaustive Enum Lowering (`match_pair.rs:396-406`)

Consider two single-variant `pub enum` definitions in an upstream crate `up_defs`:

```rust
pub enum SingleExh { Only }

#[non_exhaustive]
pub enum SingleNonExh { Only }
```

In a downstream crate:

1. **Exhaustiveness (`rustc_pattern_analysis`):** Matching `SingleNonExh` with only `SingleNonExh::Only => 1` fails with **`error[E0004]: non-exhaustive patterns: `_` not covered`**, because `split_column_ctors` (`compiler/rustc_pattern_analysis/src/rustc.rs:371-407, 861-885` at `3ef0c22c`) injects `Constructor::NonExhaustive` whenever `adt_def.is_variant_list_non_exhaustive() && !defining_crate`.
2. **MIR Lowering (`compiler/rustc_mir_build/src/builder/matches/match_pair.rs:396-406` at `3ef0c22c`; `275-285` at `14210df0`):**

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1
// compiler/rustc_mir_build/src/builder/matches/match_pair.rs:396-405
PatKind::Variant { adt_def, args: _, variant_index, ref subpatterns } => {
    let refutable =
        adt_def.variants().len() > 1 || adt_def.is_variant_list_non_exhaustive();
    let testable_case =
        refutable.then_some(TestableCase::Variant { adt_def, variant_index });
    ...
}
```

- For **`SingleExh`** (`variants().len() == 1`, `is_variant_list_non_exhaustive() == false`), `refutable` is `false` (`testable_case = None`). `PostCleanup` MIR emits **zero `discriminant(_1)` reads and zero `SwitchInt` terminators**, jumping directly to `arm_block`!
- For **`SingleNonExh`** (`variants().len() == 1`, `is_variant_list_non_exhaustive() == true`), `refutable` is **`true`** (`TestableCase::Variant` -> `TestKind::Switch`). Even though `SingleNonExh` currently has ABI `Variants::Single { index: 0 }` (a zero-sized type whose `Rvalue::Discriminant(_1)` evaluates to constant `0`), `PostCleanup` MIR emits an explicit `_2 = discriminant(_1); switchInt(move _2) -> [0: bb_only, otherwise: bb_wild]`. If `SingleNonExh` were lowered with `refutable == false`, linking or ABI-evolving an open-world variant discriminant (`runtimeDiscr != 0`) or compiling uniform polymorphic MIR before monomorphization would silently misdispatch unknown variants into `SingleNonExh::Only` instead of `_` (formalized in Theorem 3 and Counterexample `ce3`).

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirSemantics.enumAdmitted` (`MirSemantics.lean:507-516`) requires `!ety.discriminants.isEmpty`, rejecting zero-variant `Void` enums fail-closed while admitting single-variant enums (`ety.discriminants.length == 1`, `tagRepr = .zeroSized`) and evaluating `Rvalue.discriminant` on them (`MirSemantics.lean:1285-1300`) to `ety.discriminants[0]` without reading tag bytes, matching `rustc_const_eval`'s `read_discriminant` on `Variants::Single`.

#### 4.4 Empirical 7+3 Uninhabited & `#[non_exhaustive]` Matrix (`probe_3_uninhabited_and_non_exhaustive`)

| Case | Construct | `rc` | Error / Miri Status | `discriminant` in `PostCleanup` | `SwitchInt` in `PostCleanup` | `Unreachable` in `PostCleanup` | `PlaceMention` in `PostCleanup` |
| :--- | :--- | :---: | :--- | :---: | :---: | :---: | :---: |
| `match_exh_single_no_wild` | `match x { SingleExh::Only => 1 }` | `0` | compiles | `false` | `false` | `false` | `true` |
| `match_non_exh_single_no_wild` | `match x { SingleNonExh::Only => 1 }` | `1` | `error[E0004]` | `false` | `false` | `true` (error stub) | `false` |
| `match_non_exh_single_with_wild` | `match x { SingleNonExh::Only => 1, _ => 2 }` | `0` | compiles | **`true`** | **`true`** | `false` | `true` |
| `match_void_by_val_empty` | `fn(v: Void) { match v {} }` | `0` | compiles | `false` | `false` | **`true`** | `true` |
| `match_void_ref_empty` | `fn(r: &Void) { match *r {} }` | `0` | compiles | `false` | `false` | **`true`** | `true` |
| `match_void_raw_ptr_empty` | `unsafe { match *p {} }` (`*const Void`) | `0` | compiles | `false` | `false` | **`true`** | `true` |
| `match_void_raw_ptr_wildcard` | `unsafe { match *p { _ => 99 } }` (`*const Void`) | `0` | compiles | `false` | `false` | **`false`** | `true` |
| Miri `raw_wildcard_null` | `p = ptr::null::<Void>()`, `match *p { _ => 99 }` | `0` | **`RES=99` (no UB)** | `false` | `false` | `false` | `true` |
| Miri `raw_wildcard_valid` | `p = (&1u8) as *const u8 as *const Void`, `match *p { _ => 99 }` | `0` | **`RES=99` (no UB)** | `false` | `false` | `false` | `true` |
| Miri `ref_empty_from_valid` | `let r: &Void = &*p; match *r {}` | `1` | **UB: invalid `&Void`** | `false` | `false` | `true` | `true` |

---

### Finding 5: Dynamic Slice, Fixed-Array, and Range Pattern Lowering in `PostCleanup` MIR

`Basis: source + execution + derived`

#### 5.1 Elimination of Legacy `Rvalue::Len` in Favor of `UnOp::PtrMetadata` (`as_place.rs`, `match_pair.rs`, `test.rs`)

Across `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, legacy `Rvalue::Len` no longer exists in `rustc_middle::mir::Rvalue` (`MirAst.lean:566-580`). Slice and array patterns (`PatKind::Slice { prefix, slice, suffix }`, `match_pair.rs:360-386` at `3ef0c22c`; `242-268` at `14210df0`) lower through two distinct code paths depending on whether the scrutinee type is `[T]` (unsized slice) or `[T; N]` (fixed-length array):

1. **Unsized slice (`&[i32]`):**
   - **Length test (`TestableCase::Slice { len, op }` -> `TestKind::Len`):**
     - Exact pattern `[a, b]` (`slice: None`): `len = prefix.len() + suffix.len()`, `op = SliceLenOp::Equal` -> `Builder::len_of_slice_or_array` (`compiler/rustc_mir_build/src/builder/expr/as_place.rs:669-724` at `3ef0c22c`; `668-723` at `14210df0`) extracts fat-pointer metadata via `_len = PtrMetadata(copy _slice_ref)` (`Rvalue::UnaryOp(UnOp::PtrMetadata, ptr_or_ref)`, `as_place.rs:716` at `3ef0c22c`), compares `_cmp = Eq(move _len, const 2_usize)`, and branches via `SwitchInt`.
     - Variadic pattern `[first, mid @ .., last]` (`slice: Some(_)`): `len = prefix.len() + suffix.len()`, `op = SliceLenOp::GreaterOrEqual` -> emits `_len = PtrMetadata(copy _slice_ref)` + `_cmp = Ge(move _len, const 2_usize)` + `SwitchInt`. When `len == 0` (`[..]` or `[rest @ ..]`), `match_pair.rs:379` elides the length test (`testable_case = None`).
   - **Element and subslice projections (`adjust_slice_pat_subpattern_place`, `match_pair.rs:17-67` at `3ef0c22c`):**
     - Prefix elements emit `ProjectionElem::ConstantIndex { offset: i, min_length, from_end: false }` (printed as `(*_1)[0 of 2]`).
     - Suffix elements behind `..` emit `ProjectionElem::ConstantIndex { offset: k, min_length, from_end: true }` (printed as `(*_1)[-1 of 2]`, where `offset: 1` with `from_end: true` indexes `len - 1`).
     - Binding the middle subslice `mid @ ..` emits `PlaceElem::Subslice { from: prefix.len() as u64, to: suffix.len() as u64, from_end: true }` (printed as `(*_1)[1:-1]`).
2. **Fixed-size array (`[i32; 4]`):**
   - `match_pair.rs:373-376` sees `ty::Array(_, length)` whose constant length is already statically checked by typeck, so **`testable_case` is `None`** (`0` `PtrMetadata` operations, `0` length `SwitchInt`s).
   - `adjust_slice_pat_subpattern_place` folds `from_end` indices statically against the known array length $N = 4$: `[first, mid @ .., last]` emits `from_end: false` projections `_1[0 of 4]`, `_1[1..3]` (`Subslice { from: 1, to: 3, from_end: false }`), and `_1[3 of 4]` (`ConstantIndex { offset: 3, min_length: 4, from_end: false }`).
3. **Range patterns (`PatKind::Range` -> `TestKind::Range`, `test.rs:238-309` at `3ef0c22c`; `236-307` at `14210df0`):**
   - Half-open and inclusive integer ranges lower to sequential basic blocks testing lower bound (`BinOp::Le(const lo, copy place)`) and upper bound (`BinOp::Le(copy place, const hi)` for `..=hi` or `BinOp::Lt(copy place, const hi)` for `..hi`), branching via boolean `SwitchInt` at each bound.

#### 5.2 Empirical Slice/Array/Range Verification (`probe_4_slice_and_range_mir`) and `joshlf/anneal` Support Matrix

`probe_4_slice_and_range_mir` inspects `PostCleanup` MIR for both `classify_slice_and_ranges(xs: &[u32], tag: i32)` (`slice_and_range_fn`) and `classify_fixed_array(arr: &[u32; 4])` (`fixed_array_fn`):

| MIR Property (`PostCleanup`) | `classify_slice_and_ranges` (`&[u32]`) | `classify_fixed_array` (`&[u32; 4]`) | `joshlf/anneal@c131b32` `Trusted.MirAst` Status |
| :--- | :---: | :---: | :--- |
| Legacy `Len(...)` rvalue | `false` | `false` | Removed upstream; absent from `MirAst.Rvalue` (`MirAst.lean:620-628`). |
| `PtrMetadata(...)` unary op | **`true`** | `false` | **Admitted**: `UnOp.ptrMetadata` (`MirAst.lean:446`). |
| Length / range `BinOp`s (`Eq`, `Ge`, `Le`, `Lt`) | **`["Eq(", "Ge(", "Le(", "Lt("]`** | `[]` | **Admitted**: `BinOp.{eq, ge, le, lt}` (`MirAst.lean:400-409`). |
| Prefix `ConstantIndex` (`from_end: false`) | **`true`** (`[0 of 2]`) | **`true`** (`[3 of 4]`) | **Fail-closed**: `ProjectionElem.unsupported` (`MirAst.lean:469-475`). |
| Suffix `ConstantIndex` (`from_end: true`) | **`true`** (`[-1 of 2]`) | `false` | **Fail-closed**: `ProjectionElem.unsupported` (`MirAst.lean:469-475`). |
| Dynamic `Subslice` (`from_end: true`, `[1:-1]`) | **`true`** | `false` | **Fail-closed**: `ProjectionElem.unsupported` (`MirAst.lean:469-475`). |
| Static `Subslice` (`from_end: false`, `[1..3]`) | `false` | **`true`** | **Fail-closed**: `ProjectionElem.unsupported` (`MirAst.lean:469-475`). |

Thus scalar range patterns (`0..=10`, `11..20`) lower purely into constructs already modeled in `joshlf/anneal` (`BinOp.{le, lt}` + `TerminatorKind.switchInt`), whereas slice and array element/subslice patterns hit `ProjectionElem.unsupported` until `ConstantIndex` and `Subslice` place projections are added to `Trusted.MirAst.ProjectionElem`.

---

### Finding 6: Kernel-Checked `Lean v4.34.1` Mechanization and Constructive Counterexamples

`Basis: derived + execution`

The self-contained `Lean v4.34.1` module `support/MatchLoweringFakeBorrowAndGuardSoundness.lean` (`2,616` lines, zero external imports beyond core `Init`) mechanizes operational models of all three soundness pillars and checks nine `#print axioms` targets under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with zero unfinished obligations, zero `Classical.choice`, zero reflection axioms (`ofReduceBool`/`ofReduceNat`), and zero auxiliary unsafe recursion declarations.

#### 6.1 Mechanized Model Correspondence

| Rust / MIR Concept | Upstream `rust-lang/rust` Location | Lean 4 Definition in `MatchLoweringFakeBorrowAndGuardSoundness.lean` |
| :--- | :--- | :--- |
| `ProjectionElem::{Deref, Field, Downcast+Field}` & `Place` | `rustc_middle/src/mir/syntax.rs` | `ProjElem` (`.deref`, `.field`, `.downcastField`), `Place`, `evalPlace`, `writePlace` |
| Runtime values (`Box<T>`, `DerefPure` smart ptr, `&T`, ADT, tuple) | `rustc_const_eval/src/interpret/` | `Val` (`.scalar`, `.boolVal`, `.tuple`, `.enumAdt`, `.boxVal`, `.smartPtr`, `.refLocal`) |
| `FakeBorrowKind::{Shallow, Deep}` lattice | `rustc_middle/src/mir/syntax.rs` | `FakeBorrowKind` (`.shallow`, `.deep`), `FakeBorrowKind.le`, `FakeBorrowKind.join` |
| `place_components_conflict` (`Shallow` vs `Deep` + deref tail) | `rustc_borrowck/src/places_conflict.rs:131-297` | `hasDerefInTail`, `projComponentsConflict`, `borrowConflictsWithWrite` |
| `FakeBorrowCollector::{fake_borrow, visit_match_pair, visit_binding}` | `rustc_mir_build/src/builder/matches/util.rs:103-231` | `collectDerefPrefixPlaces`, `recordFakeBorrow`, `recordBindingFakeBorrows`, `collectTreeFakeBorrows` |
| Post-cleanup decision-tree execution with side-effecting guards | `rustc_mir_build/src/builder/matches/mod.rs` | `DecTree`, `GuardWrite`, `applyGuardWrites`, `evalDecTree`, `DecTreeOutcome` |
| Or-pattern source backtracking vs split `MatchTreeSubBranch` CFG | `matches/mod.rs:2387-2529` | `OrSubPat`, `evalSourceOrArm`, `lowerOrArmToSubBranches`, `execLoweredSubBranchChain` |
| Reverse sub-branch drop scheduling (`clear_match_arm_and_guard_scopes`) | `matches/mod.rs:534-546`, `scope.rs:1760-1773` | `scheduleLifoDropsForSubBranch`, `runSubBranchDropLoop`, `rustcLoweredArmDropOrder` |
| `#[non_exhaustive]` single-variant refutability & `Void` `PlaceMention` | `matches/match_pair.rs:399`, `interpret/place.rs:490-523` | `isVariantPatternRefutable`, `lowerSingleVariantEnumMatch`, `evalMatchRawPtrVoidWildcard`, `evalRefVoidEmptyMatch` |

#### 6.2 Verified Theorems and Constructive Counterexamples

| Theorem / Counterexample Identifier | Statement Summary | Kernel `#print axioms` Footprint |
| :--- | :--- | :--- |
| `fakeBorrow_prevents_unreachable_fallthrough` (**Theorem 1**) | For any decision tree `dt` that is statically exhaustive (`treeExhaustiveUnderFacts [] dt`) and whose guard writes satisfy `allTreeGuardsBorrowckOk borrowedPointees (collectTreeFakeBorrows [] dt) dt = true`, post-erasure execution `evalDecTree dt st₀` **never** produces `.reachedUnreachableUB`—even when failing guards mutate unswitched locals or unborrowed variant payloads. | `[propext]` |
| `orPattern_guard_backtracking_exact` (**Theorem 2**) | For every list of or-pattern alternatives `subpats` and every stateful side-effecting guard `guardFn`, executing the split sub-branch chain `lowerOrArmToSubBranches subpats guardFn armId` yields the **exact** same `OrMatchResult` (matched arm or `otherwise` exit, bound values, mutated store, and guard execution log) as source-level backtracking `evalSourceOrArm`. | `[]` (zero axioms) |
| `rustcLoweredArmDropOrder_matches_primary_lifo` (**Theorem 2b**) | For any non-empty sub-branch list `firstSub :: otherSubs`, `rustc`'s reverse sub-branch loop with `clear_match_arm_and_guard_scopes` schedules `firstSub.bindingVars.reverse`—the exact LIFO drop order of the leftmost sub-pattern. | `[propext]` |
| `okErrSwappedBindings_value_drop_asymmetry` (**Corollary 2c**) | On `Ok((a, b)) \| Err((b, a))`, `staticDropVars = [b, a]`, dropping runtime values `[2, 1]` on `Ok((1, 2))` and `[1, 2]` on `Err((1, 2))`, matching `DROP_BRANCH0` and `DROP_BRANCH1` from `probe_2`. | `[propext]` |
| `nonExhaustive_requires_discriminant_dispatch` (**Theorem 3**) | For any `#[non_exhaustive]` enum (`isNonExhaustive = true`), even with `declaredVariantCount = 1`, `lowerSingleVariantEnumMatch` emits `.switchDiscriminant 0` and agrees with `evalOpenWorldEnumSpec` on **all** open-world runtime discriminants `runtimeDiscr : Nat`; for an exhaustive 1-variant enum (`⟨1, false⟩`), it emits `.irrefutableDirectGoto` while agreeing on the unique closed-world inhabitant `0`. | `[propext]` |
| `voidRawPtrWildcard_safe_vs_refVoid_ub` (**Corollary 3b**) | `evalMatchRawPtrVoidWildcard addr 99 = .okReturn 99` for both `.nullAddr` and `.validAlignedAddr`, whereas `evalMatchRawPtrVoidEmpty` reaches `.ubEnteredUnreachable` and `evalRefVoidEmptyMatch` faults `.ubConstructingInvalidRefToUninhabited`. | `[]` (zero axioms) |
| `ce1_shallow_only_fake_borrow_on_deref_pat_reaches_unreachable_ub` (**Counterexample 1**) | Replacing `FakeBorrowKind::Deep` with `Shallow` on `TestableCase::Deref` (`buggyShallowDerefTreeCollector`) causes borrowck to accept `s.0 = true` inside arm 2's guard on an exhaustive `SmartBool` decision tree and step `SmartBool(false)` directly to `.reachedUnreachableUB`, whereas `collectTreeFakeBorrows` rejects the guard (`false`, corresponding to `E0510`). | `[propext]` |
| `ce2_omitting_deref_prefix_fake_borrow_corrupts_arm_binding` (**Counterexample 2**) | Omitting `fake_borrow_deref_prefixes` (`&fake shallow x`) on binding `&y` allows a guard write `x = &2` (`buggyAllows = true`), causing the guard to test `some (.scalar 1)` while `arm_block` copies `some (.scalar 2)` into `y`, whereas `recordBindingFakeBorrows` rejects the write (`soundAllows = false`, `E0510`). | `[propext]` |
| `ce3_omitting_discriminant_check_on_non_exhaustive_single_variant_misdispatches_future_variant` (**Counterexample 3**) | Testing only `declaredVariantCount > 1` without `\|\| isNonExhaustive` on a 1-variant `#[non_exhaustive]` enum elides `SwitchInt` and misdispatches open-world discriminant `1` to `onlyArmVal = 1` instead of `wildArmVal = 2`. | `[propext]` |

## Boundaries

To prevent over-generalization by downstream verification and compiler tools, the following negative space and disproved stronger hypotheses apply:

- **Unstable `#![feature(exhaustive_patterns)]` and `#![feature(never_patterns)]` (`not examined`):** All uninhabited-type experiments in `probe_3_uninhabited_and_non_exhaustive` run without `exhaustive_patterns` or `never_patterns`. Enabling `exhaustive_patterns` allows omitting uninhabited variants inside **nested** positions (such as `let Ok(x) = res` on `Result<u32, Void>`), which changes `rustc_pattern_analysis`'s nested constructor splitting (`usefulness.rs:955`) and emits `SwitchInt` + `Unreachable` on nested variant tags; enabling `never_patterns` introduces explicit `!` arms that forbid fallthrough even without bindings.
- **Unstable `#![feature(deref_patterns)]` and `unsafe impl DerefPure` Violations (`known not to apply`):** Soundness of `FakeBorrowKind::Deep` on `TestableCase::Deref` relies on `<P as Deref>::deref(&p)` being deterministic when `p` and its owned fields are not mutated (`core::ops::DerefPure`'s `unsafe` trait contract). If unsound `unsafe` code implements `DerefPure` for a type whose `deref` reads an external `AtomicBool` or `thread_local!` mutated by a match guard without touching `p`, `FakeBorrowKind::Deep` on `p` does **not** prevent `<P as Deref>::deref(&p)` from returning a different reference on the second call and reaching `TerminatorKind::Unreachable`. That unsoundness belongs to the invalid `unsafe impl DerefPure`, not to `FakeBorrowCollector`.
- **Interior Mutability (`Cell<T>`, `RefCell<T>`, `UnsafeCell<T>`) Inside Scrutinees (`not examined` in the Lean mechanization; constrained in `rustc`):** `MatchLoweringFakeBorrowAndGuardSoundness.lean` models value-level store updates (`writePlace`) rather than shared-reference `UnsafeCell` writes. In Rust, an enum's own discriminant tag is never wrapped in `UnsafeCell` without raw-pointer `unsafe` writes; if an `UnsafeCell<Option<i32>>` wraps an enum, safe code cannot pattern-match through `UnsafeCell` directly, and matching on `*cell.get()` inside `unsafe` while mutating `cell` in a guard violates aliasing/validity invariants if a `ref_for_guard` live reference exists, or falls under `unsafe` raw-pointer preconditions.
- **Polonius (`-Zpolonius`) Loan Liveness (`not examined`):** All borrowck probes ran under `rustc`'s default NLL borrow checker (`mir_borrowck`). Interaction between `-Zpolonius=next` and `FakeReadCause::ForMatchGuard` was not separately executed.
- **Zero-Variant Enums, `PlaceMention`, `ConstantIndex`, and `Subslice` in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`unsupported`):** `Trusted.MirSemantics.enumAdmitted` (`MirSemantics.lean:507-516`) rejects zero-variant enums (`ety.discriminants = []`), `Trusted.MirAst.StatementKind` (`MirAst.lean:654-656`) maps `StatementKind::PlaceMention` and `StatementKind::FakeRead` to `.unsupported`, and `Trusted.MirAst.ProjectionElem` (`MirAst.lean:469-475`) maps `ConstantIndex`, `Subslice`, and `Downcast` to `.unsupported`. Any captured MIR body retaining those nodes fails closed rather than mis-executing.
- **Attractive Stronger Claims Disproved by Evidence (`known not to apply`):**
  1. *"A match guard freezes the entire scrutinee local against mutation."* **False:** Unswitched locals (`u = true`), unswitched `Box<T>` interiors without `deref!` (`*b = true`), and unswitched variant-payload fields (`((p.0 as Some).0) = 42`) emit either zero `&fake` borrows or `&fake shallow` on a prefix, and all compile and execute cleanly under Miri.
  2. *"Mutating a matched scrutinee inside a guard always reports `E0510`."* **False:** Whenever the arm binds a subplace (`Some(_v)`), `ref_for_guard` creates a real `BorrowKind::Shared` loan before `&fake shallow`, causing `mir_borrowck` to report `E0506` rather than `E0510`.
  3. *"In an or-pattern `P_0 | P_1`, bindings drop in the declaration order of whichever sub-pattern matched at runtime."* **False:** `arm_block` has a single static LIFO drop schedule fixed by `P_0` (`sub_branches[0]`), reversing value drop order when `P_1` permutes variable names (`Ok((a, b)) | Err((b, a))`).
  4. *"Matching `*p` where `p: *const Void` dereferences `p` and causes UB if `p` is null."* **False:** With a wildcard arm (`match *p { _ => 99 }`), `PostCleanup` MIR emits only `PlaceMention((*_1))`, which skips null/alignment/dereferenceability checks on raw pointers and passes Miri with `rc = 0`.

## Evidence

### 1. Primary Upstream Source Audited (`rust-lang/rust`)

All files below were audited directly at both `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`):

| Component | Repository Path | Narrow Line Ranges (`3ef0c22c` / `14210df0`) | Key Symbols Audited |
| :--- | :--- | :--- | :--- |
| Fake-borrow collector | `compiler/rustc_mir_build/src/builder/matches/util.rs` | `71-231` / `69-227` | `collect_fake_borrows`, `FakeBorrowCollector`, `fake_borrow`, `fake_borrow_deref_prefixes`, `visit_match_pair`, `visit_binding` |
| Match tree, guards & drops | `compiler/rustc_mir_build/src/builder/matches/mod.rs` | `84, 334-390, 498-550, 1637-1650, 2045-2055, 2387-2529, 2634-2735` / `77, 351-408, 517-569, 1677-1690, 2087-2097, 2416-2555, 2660-2761` | `ScheduleDrops`, `Builder::match_expr`, `lower_scrutinee`, `bind_pattern`, `build_match_tree`, `bind_and_guard_matched_candidate`, `bind_matched_candidate_for_guard`, `bind_matched_candidate_for_arm_body` |
| Pattern-to-test lowering | `compiler/rustc_mir_build/src/builder/matches/match_pair.rs` | `17-67, 270-281, 360-406, 432-455` / `17-67, 135-146, 242-285, 311-334` | `adjust_slice_pat_subpattern_place`, `MatchPairTree::for_pattern` (`PatKind::{Range, Slice, Variant, Deref, DerefPattern}`) |
| Runtime test emission | `compiler/rustc_mir_build/src/builder/matches/test.rs` | `38-60, 66-125, 238-382` / `36-58, 64-123, 236-380` | `Builder::test`, `perform_test` (`TestKind::{Switch, SwitchInt, Range, Len, Deref}`) |
| Slice metadata & indexing | `compiler/rustc_mir_build/src/builder/expr/as_place.rs` | `669-724` / `668-723` | `Builder::len_of_slice_or_array` (`Rvalue::UnaryOp(UnOp::PtrMetadata, ...)`) |
| Or-pattern drop clearing | `compiler/rustc_mir_build/src/builder/scope.rs` | `1760-1774` / `1791-1805` | `Builder::clear_match_arm_and_guard_scopes` |
| Borrow conflict semantics | `compiler/rustc_borrowck/src/places_conflict.rs` | `131-297` / `131-285` | `place_components_conflict`, `PlaceExt::ignore_borrow`, `FakeBorrowKind::{Shallow, Deep}` |
| `E0506` vs `E0510` emission | `compiler/rustc_borrowck/src/diagnostics/conflict_errors.rs` | `4016-4058, 4297-4322` (`3ef0c22c`) | `report_illegal_mutation_of_borrowed`, `classify_immutable_section` (`FakeReadCause::ForMatchGuard`) |
| Post-borrowck erasure | `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs` | `24-75` / `24-77` | `CleanupPostBorrowck::run_pass` (`BorrowKind::Fake`, `FakeRead`, `FalseEdge`) |
| Exhaustiveness & `Void` | `compiler/rustc_pattern_analysis/src/rustc.rs` & `usefulness.rs` | `rustc.rs:157-172, 360-415, 861-885`; `usefulness.rs:947-965, 1698-1740` (`3ef0c22c`) | `RevealedTy::is_uninhabited`, `split_column_ctors`, `Constructor::NonExhaustive`, `is_toplevel_exception`, `compute_exhaustiveness_and_usefulness` |
| `PlaceMention` & raw deref | `compiler/rustc_const_eval/src/interpret/step.rs` & `place.rs` | `step.rs:120-123`; `place.rs:468-538` / `466-536` | `StatementKind::PlaceMention`, `InterpCx::deref_pointer` (`ptr_ty.is_raw_ptr()`) |

### 2. Downstream Verified-Compiler Source Audited (`joshlf/anneal`)

Audited at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (referencing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` and `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

- `trusted/lean/Trusted/MirAst.lean`: `EnumTy` (`228-275`), `BinOp` (`400-409`), `UnOp.ptrMetadata` (`445-446`), `ProjectionElem` (`466-475`), `Rvalue.discriminant` (`600-628`), `StatementKind` (`650-663`), `TerminatorKind.unreachable` (`776-790`).
- `trusted/lean/Trusted/MirSemantics.lean`: `enumAdmitted` (`507-516`), `Rvalue.discriminant` evaluation on `Variants::Single` / `.zeroSized` (`1269-1308`), `evalStatement` (`1370-1428`), `TerminatorKind.unreachable` -> `.fault .undefined` (`1551-1552`).
- `trusted/rustc-capture/src/driver.rs`: pinned compiler version check (`25, 45-47`) and `after_analysis` gate (`75-84`).

### 3. Preserved Support Artifacts (Acquired and Verified `2026-11-22`)

1. **`support/probe_match_lowering_fake_borrows.py`:** Standalone Python 3 probe compiling and running real Rust specimens with `rustc` (`-Zdump-mir=built,CleanupPostBorrowck`) and building a hermetic `-Zalways-encode-mir` sysroot (`core`, `compiler_builtins`, `alloc`) from bundled rustup toolchain sources to execute `miri` directly across Stacked Borrows, Tree Borrows (`-Zmiri-tree-borrows`), and uninhabited `Void` pointer tests without network access.
2. **`support/probe_match_lowering_fake_borrows_results.json`:** Machine-readable output captured on `x86_64-unknown-linux-gnu` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` (`LLVM 22.1.6`), scrubbed of host-specific filesystem paths.
3. **`support/MatchLoweringFakeBorrowAndGuardSoundness.lean`:** Standalone `Lean v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) formalization proving Theorems 1–3, Corollaries 2b/2c/3b, and Counterexamples `ce1`–`ce3`, verified with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

## Revalidation

To determine cheaply and reliably whether all findings still hold on a newer `rustc` / `Miri` nightly or an updated `joshlf/anneal` revision, run the following three narrow checks from this report package's directory:

### 1. Re-Execute the Empirical `rustc` + `Miri` Probe (~15–25 seconds)

Requires a rustup nightly toolchain with `rustc`, `miri`, and `rust-src` components installed:

```bash
python3 support/probe_match_lowering_fake_borrows.py --output /tmp/revalidated_match_probe.json
```

`probe_match_lowering_fake_borrows.py` runs `verify_invariants(payload)` over all four probes and exits non-zero immediately if:
- Any of the 9 `FakeBorrow` borrowck/MIR cases changes its exit code, `E0506`/`E0510` split, `&fake` / `&fake shallow` emission in `built` MIR, or complete erasure after `CleanupPostBorrowck`;
- Native execution, Miri Stacked Borrows, or Miri Tree Borrows diverge on or-pattern guard re-evaluation (`["guard:1", "guard:2"]`), `Ok((a, b)) | Err((b, a))` drop ordering (`DROP_BRANCH0` vs `DROP_BRANCH1`), non-`Copy` guard-failure survival, or unswitched guard mutations;
- Cross-crate `SingleNonExh` stops requiring `_` (`E0004`) or stops emitting `discriminant` + `SwitchInt`, or Miri changes behavior on null/valid `*const Void` `PlaceMention` vs `&Void` construction;
- Slice/array/range `PostCleanup` MIR reintroduces `Len` or alters `PtrMetadata`, `ConstantIndex`, `Subslice`, or `BinOp` lowering.

### 2. Re-Check the `Lean v4.34.1` Mechanization (~8 seconds)

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/MatchLoweringFakeBorrowAndGuardSoundness.lean
```

Confirm exit status `0` and verify that the nine `#print axioms` lines printed on stdout list only `[propext]` or `does not depend on any axioms` (zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`).

### 3. Narrow Upstream Diff Regions When Evaluating a New `rust-lang/rust` or `joshlf/anneal` Commit

Before repeating manual source inspection on a new revision `<NEW_SHA>`, diff only the governing implementation files:

```bash
# In a rust-lang/rust checkout:
git diff 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1..<NEW_SHA> -- \
  compiler/rustc_mir_build/src/builder/matches/{util.rs,mod.rs,match_pair.rs,test.rs} \
  compiler/rustc_mir_build/src/builder/scope.rs \
  compiler/rustc_mir_build/src/builder/expr/as_place.rs \
  compiler/rustc_borrowck/src/places_conflict.rs \
  compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs \
  compiler/rustc_pattern_analysis/src/{rustc.rs,usefulness.rs} \
  compiler/rustc_const_eval/src/interpret/{step.rs,place.rs}

# In a joshlf/anneal checkout:
git diff c131b320eeeb26ef692e5afd5ec8db49ee518613..<NEW_ANNEAL_SHA> -- \
  trusted/lean/Trusted/{MirAst.lean,MirSemantics.lean} \
  trusted/rustc-capture/src/driver.rs
```

If `ProjectionElem.ConstantIndex`, `ProjectionElem.Subslice`, `StatementKind.PlaceMention`, or zero-variant `EnumTy` admission is added to `joshlf/anneal`, update the fail-closed `.unsupported` rows in **Finding 4**, **Finding 5**, and **Boundaries** accordingly.
