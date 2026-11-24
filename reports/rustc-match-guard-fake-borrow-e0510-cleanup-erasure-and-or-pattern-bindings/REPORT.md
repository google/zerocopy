# Match-Guard Fake Borrows, E0510/E0506/E0594 Diagnostics, CleanupPostBorrowck Erasure, and Or-Pattern Guard Bindings in rustc and Lean 4

## Summary

Basis: source + execution + derived (Lean 4 kernel mechanization)

When lowering a `match` expression with arm guards into MIR, `rustc` decouples pattern discrimination from arm entry so that a guard executes between discriminant switching and pattern-binding moves without allowing user code in the guard to falsify the match automaton's structural or exhaustiveness invariants. Across both `rustc 1.98.0-nightly` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and upstream `rust-lang/rust@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`, the compiler enforces this separation through five coordinated MIR and NLL mechanisms, all verified in live `rustc` executions (`support/probe_match_guard_fake_borrow.py`, results in `support/probe_results.json`) and mechanized without axioms beyond `[Quot.sound, propext]` in Lean `v4.34.1` (`support/MatchGuardFakeBorrowAndOrPatternSoundness.lean`):

1. **Shallow vs. Deep Fake Borrows (`FakeBorrowCollector`):** Whenever any candidate has a guard, `collect_fake_borrows` traverses every tested sub-pattern and bound place with a dereference prefix (`compiler/rustc_mir_build/src/builder/matches/util.rs:71-230`). Every switched place receives `BorrowKind::Fake(FakeBorrowKind::Shallow)`, while every `TestableCase::Deref` scrutinee receives `BorrowKind::Fake(FakeBorrowKind::Deep)`. For bound places with at least one `ProjectionElem::Deref` prefix, `fake_borrow_deref_prefixes` inserts a shallow fake borrow on each prefix immediately before each `Deref`, keeping pointer chains stable without blocking irrefutable whole-local mutation (`match u { _ if { u = true; false } => {}, _x => {} }` compiles cleanly).
2. **Exact Four-Way Diagnostic Partition (`E0510` vs. `E0506` vs. `E0502` vs. `E0594`) and `Box` vs. `Vec` `deref!` Split:** In `rustc_borrowck/src/places_conflict.rs:288-296`, a `FakeBorrowKind::Shallow` loan does **not** conflict with any mutable access strictly deeper than `borrow_place` (`borrow_place.projection.len() < access_place.projection.len()` returns `false`). Thus, matching `(Some(_), false)` lets a guard mutably borrow `(x.0 as Some).0`, whereas matching `Some(_)` and assigning `x = None` rejects with **`E0510`** (`cannot assign x in match guard`), matching `Some(_y)` and assigning `x = None` rejects with **`E0506`** (`cannot assign to x because it is borrowed`, because `bind_matched_candidate_for_guard` issues the user `&` borrow *before* `&fake shallow _1`), writing through a pattern binding inside a guard (`*v = ...` for `ref mut v` or `v = ...` for `mut v`) rejects with **`E0594`** (`cannot assign to ..., as it is immutable for the pattern guard` via `LocalDecl::is_ref_for_guard()`), and mutating a `Vec<u32>` inside a `#![feature(deref_patterns)]` guard rejects slice-indexing mutable borrows with **`E0502`** (while `Box<bool>` `deref!` lowers via built-in `PlaceElem::Deref` with `&fake shallow (*_1)` and `&fake shallow _1`, rejecting `*b = true` with **`E0510`**).
3. **`CleanupPostBorrowck` Erasure to `Nop` and `Goto`:** Because fake borrows may point into inactive enum variants (`util.rs:59-70`) and would cause UB if evaluated at runtime, `CleanupPostBorrowck::run_pass` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:27-89`) rewrites every `StatementKind::FakeRead`, `StatementKind::AscribeUserType`, `StatementKind::Assign((_, Rvalue::Ref(_, BorrowKind::Fake(_), _)))`, `StatementKind::BackwardIncompatibleDropHint`, and post-analysis `Coverage` statement to `Nop` (`statement.make_nop(true)`), and replaces every `TerminatorKind::FalseEdge { real_target, .. }` and `FalseUnwind { real_target, .. }` with an unconditional jump to `real_target`.
4. **Dual Bindings (`RefWithinGuard` vs. `OutsideGuard`), `Cell` Interior Mutability, and Or-Pattern Reverse Lowering:** For every candidate with a guard, `declare_binding` allocates both `for_arm_body` (with the pattern's declared mutability) and `ref_for_guard` (`Mutability::Not`, immutable `&T`, tagged `BindingForm::RefForGuard(for_arm_body)`). Guards see `*ref_for_guard` (blocking `E0594` writes while admitting `Cell::set` interior mutability, including observable mutations across guard fallthrough); only after `FakeRead(ForMatchGuard)` and `FakeRead(ForGuardBinding)` pass does `bind_matched_candidate_for_arm_body` move/copy `ByRef::No` values out of the scrutinee into `for_arm_body`. Or-patterns duplicate the lowered guard on each expanded sub-branch (`MatchPairKind::Or`), evaluate left-to-right with short-circuiting, and iterate sub-branches in reverse when scheduling drops (`branch.sub_branches.into_iter().rev().with_position()`) so arm drop order matches the first subpattern.
5. **Verification TCB Consequences (`anneal`) and Mechanized Soundness:** Any sound MIR interpreter or verifier (including `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`'s `Trusted.MirSemantics`, which conservatively enforces `deinitMovedPlace = true` on `move` operands) MUST either execute post-`CleanupPostBorrowck` MIR (after fake-borrow/false-edge erasure) or explicitly treat `&fake` / `FakeRead` / `FalseEdge` identically to `cleanupStmt` / `cleanupTerm`. In `support/MatchGuardFakeBorrowAndOrPatternSoundness.lean` (`2,832` lines, `953` constants, `346` theorems, `506` defs, `0` `_unsafe_rec`, `0` `Classical.choice`/`sorry`/`omega`/`bv_decide`/`native_decide`), all four core theorems (`discriminant_stability_of_fake_borrow_shallow`, `ref_within_guard_immutability_and_move_once`, `cleanup_post_borrowck_observational_erasure_equiv`, `or_pattern_per_branch_short_circuit_and_move_once`) and four diagnostic partition theorems are kernel-checked in Lean `v4.34.1`.

## Applicability

### Scope and Covered Subjects

This report characterizes four directly inspected technical subjects and one theorem-proving toolchain recorded in `REPORT.json`:

- **`rustc 1.98.0-nightly` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, built `2026-05-31`, `x86_64-unknown-linux-gnu`):** Used for all live compiler executions, diagnostic captures, compiled binary runs, and `--edition=2024 -Zdump-mir=...` MIR pass dumps in `support/probe_match_guard_fake_borrow.py`, and audited verbatim in compiler source files.
- **Upstream `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`):** Audited verbatim across `compiler/rustc_mir_build/src/builder/matches/util.rs`, `compiler/rustc_mir_build/src/builder/matches/mod.rs`, `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`, `compiler/rustc_borrowck/src/places_conflict.rs`, `compiler/rustc_borrowck/src/diagnostics/conflict_errors.rs`, `compiler/rustc_borrowck/src/diagnostics/mutability_errors.rs`, `compiler/rustc_borrowck/src/diagnostics/borrowck_errors.rs`, and `compiler/rustc_middle/src/mir/syntax.rs`.
- **Anneal (`joshlf/anneal` at `main@c131b320eeeb26ef692e5afd5ec8db49ee518613` and `unstable@7133a9f5c779f624f513ee1e29fd9742214ce3e1`):** Audited for MIR verification boundary design in `trusted/lean/Trusted.lean`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean` (`evalOperandToSlot` and `deinitMovedPlace = true`), and `trusted/audit/TrustedBoundary.lean` (`ensureReplayableConstant`, `validateRepoConstant`, and `allowedTermSyntaxKinds`). No source changes to `joshlf/anneal` were applied; this report guides downstream MIR-capture and semantic integration work.
- **Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):** Used to kernel-check and MetaM-audit every definition and theorem in `support/MatchGuardFakeBorrowAndOrPatternSoundness.lean` starting from `prelude` + `Init.*` only.

### Shared Behavior vs. Revision Differences Between `rustc 1.98.0-nightly` and `rust-lang/rust` HEAD

Basis: source (line-by-line diff of `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`)

The core match-guard fake-borrow algorithm, `FakeBorrowKind` conflict rule, `E0510`/`E0506`/`E0502`/`E0594` diagnostic selection, `RefWithinGuard` dual-binding design, or-pattern reverse sub-branch drop ordering, and `CleanupPostBorrowck` erasure semantics are **shared verbatim** across both Rust revisions, with three API-level refactorings distinguishing `HEAD` from `1.98.0-nightly`:

| Compiler Component | `rustc 1.98.0-nightly` (`14210df0e...`) | `rust-lang/rust` HEAD (`f7da9a423...`) | Behavioral Impact on Match Guards |
| :--- | :--- | :--- | :--- |
| `FakeBorrowCollector::visit_match_pair` (`util.rs`) | Dispatches on `match_pair.testable_case` (`TestableCase::Or` vs. `TestableCase::Deref`) with `Option<Place>` check `if let Some(place) = match_pair.place` (`util.rs:161-193`) | Dispatches on `match_pair.kind` (`MatchPairKind::Or { ref or_subpats }` vs. `MatchPairKind::Testable { place, ref testable_case, ref subpairs }`) with non-optional `place` (`util.rs:163-196`) | None for fake-borrow emission: `Deref` emits `Deep`, switched places emit `Shallow`, or-patterns recurse into `or_subpats`. |
| `CleanupPostBorrowck` (`cleanup_post_borrowck.rs`) | Erases `CoverageKind::BlockMarker \| SpanMarker` (`lines 35-39`), rewrites `FalseEdge`/`FalseUnwind` to `TerminatorKind::Goto { target: real_target }` (`line 71`), overrides `fn is_required(&self) -> bool { true }` (`lines 88-90`) | Erases `Coverage(ref kind) if kind.is_removed_after_analysis()` (`line 39`), uses `TerminatorKind::goto(real_target)` (`line 69`), overrides `fn policy(&self, _) -> PassPolicy { PassPolicy::Required }` (`lines 86-89`) | Identical MIR erasure for `&fake`, `FakeRead`, `AscribeUserType`, `BackwardIncompatibleDropHint`, and `FalseEdge`. |
| Guard Condition Helper (`matches/mod.rs`) | Calls `this.then_else_break(block, guard, None, this.source_info(arm.span), DeclareLetBindings::No)` inside `in_if_then_scope` (`lines 2471-2477`) | Calls `this.lower_if_condition(block, guard, LowerIfCondArgs { temp_scope_override: None, variable_source_info: this.source_info(arm.span), declare_let_bindings: DeclareLetBindings::No })` (`lines 2451-2460`) | Identical `RefWithinGuard` initialization, fake-borrow emission order, and post-guard `FakeRead` placement. |
| `mutability_errors.rs` / `borrowck_errors.rs` | Uses `impl<'infcx, 'tcx> MirBorrowckCtxt<'_, 'infcx, 'tcx>` (`self.infcx.dcx()`) and lacks `PhantomDeref` arms in `mutability_errors.rs` | Uses `impl<'diag, 'tcx>` (`self.root_cx.dcx()` in `borrowck_errors.rs:7-9`) and adds `ProjectionElem::PhantomDeref` arms at `mutability_errors.rs:185-192` | `is_ref_for_guard()` `E0594` and `cannot_mutate_in_immutable_section` `E0510` logic are unchanged. |

### Relation to Existing Corpus Reports and Toolchain Conditions

This package complements the existing corpus package `match-guards-shallow-and-deep-fake-borrows-exhaustiveness-and-or-pattern-splitting`. Whereas that prior package formalizes a standalone pattern-match decision-tree toy (`Toy.MatchGuard`) with `Classical.choice` and no compiler execution or real MIR inspection, the present package establishes direct `rustc` primary-source behavior, concrete `rustc 1.98.0-nightly` compilation and `-Zdump-mir` execution receipts, `E0510` vs. `E0506` vs. `E0502` vs. `E0594` diagnostic routing, `CleanupPostBorrowck` erasure equivalence, `Cell` interior-mutability guard preservation, and a constructive (`0`-`Classical.choice`, `0`-`_unsafe_rec`) Lean `v4.34.1` formalization. Live `deref!` probes require `#![feature(deref_patterns)]` (unstable nightly feature gated under `--edition=2024`); all other probes use stable 2024-edition Rust syntax compiled with `rustc 1.98.0-nightly`.

## Findings

### 1. MIR Match-Guard Lowering Architecture (`rustc_mir_build`)

Basis: source (`rust-lang/rust@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) + execution (`probe_results.json`)

When `rustc` lowers a `match` expression (`lower_match_tree` in `compiler/rustc_mir_build/src/builder/matches/mod.rs`), it builds a backtracking decision tree over `Candidate`s rather than duplicating pattern tests blindly, while still ensuring NLL borrow checking sees conservative control flow and stability constraints:

1. **False-Edge Wiring Before Binding and After Guard Failure (`mod.rs:1593-1628`, `util.rs:17-33`):** For each leaf candidate in reverse order, `lower_match_tree` inserts a `TerminatorKind::FalseEdge { real_target, imaginary_target }` via `Builder::false_edges` before entering `pre_binding_block` (`mod.rs:1605-1610`), and if `has_guard` is true, inserts a second `FalseEdge` from the guard's `otherwise_block` to `next_candidate_start_block` (`mod.rs:1612-1623`). Whenever `imaginary_target == real_target`, `false_edges` emits `TerminatorKind::Goto` directly (`util.rs:24-32`). On exhaustive matches, `otherwise_block` receives `FakeRead(ForMatchedPlace(None), scrutinee_place)` before `TerminatorKind::Unreachable` (`mod.rs:1646-1654`) so even empty matches on uninhabited types (`match v {}` where `v: Void`) reject uninitialized scrutinees during NLL/move analysis.
2. **Whole-Match Fake-Borrow Collection (`util.rs:71-101`):** `collect_fake_borrows` returns early if `candidates.iter().all(|c| !c.has_guard)` (`line 77`). Otherwise it visits every `Candidate` (`visit_candidate`), descending into `FlatPat` alternatives of `MatchPairKind::Or` (`util.rs:152-169`) and classifying each testable sub-pair and binding:
   - **Deref patterns (`TestableCase::Deref`, `util.rs:171-185`):** Because deref-pattern sub-pairs index into a deref temporary rather than the scrutinee itself, a shallow borrow on `place` would allow a later guard to mutate `*b` (e.g., `box_deref_pattern`), invalidate earlier arms, and reach `Unreachable`. Therefore `rustc` records `self.fake_borrow(place, FakeBorrowKind::Deep)` (`line 185`).
   - **Switched places (`util.rs:186-193`):** Every other tested place receives `self.fake_borrow(place, FakeBorrowKind::Shallow)` (`line 188`), and recursion continues into `subpairs`.
   - **Bound places (`visit_binding`, `util.rs:198-230`):** If `source.local` is a deref temporary distinct from `scrutinee_base`, `visit_binding` returns early (`lines 199-205`). Otherwise it calls `self.fake_borrow_deref_prefixes(*source, FakeBorrowKind::Shallow)` (`line 229`), which iterates `place.as_ref().iter_projections().rev()` (`lines 127-139`) and inserts shallow fake borrows on every prefix immediately preceding a `ProjectionElem::Deref`. Lattice ordering ensures `Deep >= Shallow` (`line 118, 133`) so `Deep` overrides `Shallow` if both apply to the same place.
   - **Temporary Local Metadata (`util.rs:91-98`):** Each fake borrow allocates an immutable reference local `&'erased T` whose `local_info` is `ClearCrossCrate::Set(Box::new(LocalInfo::FakeBorrow))`.
3. **Exact Guard Statement Emission Order (`mod.rs:2428-2525`):** Inside `bind_and_guard_matched_candidate`, for every candidate arm that has a guard (`if let Some((arm, match_scope)) = arm_match_scope && let Some(guard) = arm.guard`):
   1. `self.bind_matched_candidate_for_guard(block, sub_branch.bindings.iter())` (`line 2428`) emits `StorageLive(ref_for_guard)` and assigns `ref_for_guard = &binding.source` (`BorrowKind::Shared` for `ByRef::No`, `mod.rs:2674-2679`; or allocates `value_for_arm = &raw/shared/mut` first and assigns `ref_for_guard = &value_for_arm` for `ByRef::Yes`, `mod.rs:2680-2703`).
   2. `for &(place, temp, kind) in fake_borrows` (`lines 2441-2444`) emits `temp = &fake [shallow] place` **after** step (1)'s shared/mut binding borrows!
   3. `lower_if_condition` / `then_else_break` (`line 2451` / `line 2471`) lowers the guard expression in `GuardFrame`, terminating in `(guard_true_block, guard_false_block)`.
   4. On `guard_true_block`, `rustc` emits `FakeRead(FakeReadCause::ForMatchGuard, fake_temp)` for every fake borrow (`lines 2475-2478`), then `FakeRead(FakeReadCause::ForGuardBinding, ref_for_guard)` for every `ByRef::No` binding (`lines 2508-2518`), and finally calls `bind_matched_candidate_for_arm_body(guard_true_block, schedule_drops, by_value_bindings)` (`lines 2520-2524`) to copy or **move** `binding.source` into `for_arm_body` on entry to the arm body.
   5. On `guard_false_block`, `StorageDead(ref_for_guard)` runs and control jumps to `sub_branch.otherwise_block` (`line 2480`), leaving `ByRef::No` scrutinee places completely unmoved for subsequent sub-branches or arms.

```text
Basis: source (util.rs:117-230, matches/mod.rs:2428-2525, 2665-2704) + execution (probe_guard_probe MIR)

  [switchInt(discriminant(_1))]
         |
         +--> bb2: falseEdge -> [real: bb5, imaginary: bb1]
                       |
                       v
  [Guard Setup & Execution (bb5)]
    1. StorageLive(_5);  _5 = &((_1 as Some).0)       // RefWithinGuard (Shared) [mod.rs:2428]
    2. _2 = &fake shallow _1                          // FakeBorrow(Shallow/Deep) [mod.rs:2441]
    3. Guard body evaluates *_5 (cannot assign to _5, *_5, or _1; Cell interior mut OK)
         |
         +--- guard == false ---> bb8/bb9: StorageDead(_5); falseEdge(otherwise) -> next candidate / arm
         |
         v guard == true (bb7)
    4. FakeRead(ForMatchGuard, _2)                    // Anchors fake borrow [mod.rs:2477]
    5. FakeRead(ForGuardBinding, _5)                  // Anchors shared binding [mod.rs:2517]
    6. StorageLive(_4);  _4 = copy/move ((_1 as Some).0) // By-value move ONLY HERE [mod.rs:2520]
    7. Arm body executes with _4 (`OutsideGuard`)
```

---

### 2. Shallow vs. Deep Conflict Algebra and Four-Way Diagnostic Partition (`E0510` / `E0506` / `E0502` / `E0594`)

Basis: source (`places_conflict.rs`, `conflict_errors.rs`, `borrowck_errors.rs`, `mutability_errors.rs`) + execution (`probe_results.json`)

The borrow checker's overlap test `borrow_conflicts_with_place` (`compiler/rustc_borrowck/src/places_conflict.rs:288-296`) ends its projection loop with one asymmetric shallow-borrow guard:

```rust
// compiler/rustc_borrowck/src/places_conflict.rs:288-296
    if borrow_kind == BorrowKind::Fake(FakeBorrowKind::Shallow)
        && borrow_place.projection.len() < access_place.projection.len()
    {
        debug!("borrow_conflicts_with_place: shallow borrow");
        false
    } else {
        debug!("borrow_conflicts_with_place: full borrow, CONFLICT");
        true
    }
```

When NLL detects an illegal write or conflicting mutable borrow while a guard borrow is active, diagnostic selection partitions cleanly across **four distinct error codes** governed by the loan kind, access kind (direct assignment vs. `&mut` borrow), loan order, and `LocalDecl::is_ref_for_guard()`:

| Case | Borrowed / Protected Entity | Guard Action Attempted | Primary NLL Source Rule | Live `rustc 1.98.0-nightly` Output |
| :--- | :--- | :--- | :--- | :--- |
| Wildcard pattern (`Some(_)`) | `_2 = &fake shallow _1` on `x` | `x = None;` (direct write to prefix/equal place) | `report_illegal_mutation_of_borrowed`: `if let BorrowKind::Fake(_) = loan.kind` + `ForMatchGuard => "match guard"` (`conflict_errors.rs:4007-4016, 4299`; `borrowck_errors.rs:369-380`) | `error[E0510]: cannot assign x in match guard` |
| Tested tuple/enum sub-pattern (`(Some(_), false)`) | `_2 = &fake shallow (_1.0)` | `if let Some(ref mut y) = x.0 { *y += 1; }` (mutable borrow of `(x.0 as Some).0`) | `borrow_place.projection.len() == 1 < access_place.projection.len() == 3` (`places_conflict.rs:288-292`) => **disjoint** | Compiles cleanly (`compile_returncode = 0`) |
| Tested sub-pattern field assignment (`(Some(_), false)`) | `_2 = &fake shallow (_1.0)` | `x.0 = None;` (direct write to shallow-borrowed place `x.0`) | Equal length `1 == 1` => conflicts; `BorrowKind::Fake(_)` (`conflict_errors.rs:4007`) | `error[E0510]: cannot assign x.0 in match guard` |
| Deep pattern literal inside option (`(Some(0), false)`) | `&fake shallow _1`, `&fake shallow (_1.0)`, `&fake shallow ((_1.0 as Some).0)` | `if let Some(ref mut y) = x.0 { *y += 1; }` (mutable borrow of `x.0.0`) | Conflict with `Fake(Shallow)` on `x.0.0` via `(Mut, Fake(Shallow))` arm (`conflict_errors.rs:1935-1945`) | `error[E0510]: cannot mutably borrow x.0.0 in match guard` |
| Guard binding (`Some(_y)`) | `_5 = &((_1 as Some).0)` (`Shared`) **and** `_2 = &fake shallow _1` | `x = None;` (direct write to `x`) | `bind_matched_candidate_for_guard` runs *before* `fake_borrows` (`mod.rs:2428-2444`); earliest overlapping loan is `Shared`, falling past `if let BorrowKind::Fake(_)` to `cannot_assign_to_borrowed` (`conflict_errors.rs:4033`) | `error[E0506]: cannot assign to x because it is borrowed` |
| `Box<bool>` deref pattern (`deref!(true)`) | `_2 = &fake shallow (*_1)` and `_3 = &fake shallow _1` | `*b = true;` | **Important:** `Box` deref lowers as built-in `PlaceElem::Deref` (`else` branch at `util.rs:188`), NOT `TestableCase::Deref`; conflict hits `Fake(Shallow)` on `*_1` (`conflict_errors.rs:4007`) | `error[E0510]: cannot assign *b in match guard` |
| `Vec<u32>` deref pattern (`deref!([1, ..])`) — elem mut | `_3 = &fake _1` (`FakeBorrowKind::Deep`, `TestableCase::Deref` at `util.rs:171, 185`) | `v[0] = 9;` (`&mut v` via `IndexMut`) | `(Mut { Default }, Shared \| Fake(Deep))` at `conflict_errors.rs:1847-1860` (`report_borrow_conflict`) | `error[E0502]: cannot borrow v as mutable because it is also borrowed as immutable` |
| `Vec<u32>` deref pattern (`deref!([1, ..])`) — direct assign | `_3 = &fake _1` (`FakeBorrowKind::Deep`) | `v = Vec::new();` (direct overwrite of `v`) | `if let BorrowKind::Fake(_) = loan.kind` at `conflict_errors.rs:4007` matches BOTH `Shallow` and `Deep`! | `error[E0510]: cannot assign v in match guard` |
| Mutating pattern-bound variable (`Some(ref mut v)` or `Some(mut v)`) | `ref_for_guard` local (`is_ref_for_guard() == true`, `mod.rs:2848-2850`) | `*v = Box::new(99);` or `v = Box::new(99);` | `PlaceRef { local, projection: [ProjectionElem::Deref] } if self.body.local_decls[local].is_ref_for_guard()` (`mutability_errors.rs:128-133, 557-564`) | `error[E0594]: cannot assign to *v / v, as it is immutable for the pattern guard` (`variables bound in patterns are immutable until the end of the pattern guard`) |
| Binding behind pointer deref (`match *x { y if ... => ... }`) | `fake_borrow_deref_prefixes` (`util.rs:127-138, 229`) adds `&fake shallow x` | `x = &2;` | Conflicting write to shallow-borrowed prefix `x` (`conflict_errors.rs:4007`) | `error[E0510]: cannot assign x in match guard` |
| Irrefutable local binding (`let mut u = false; match u { _ if ... => {}, _x => {} }`) | Neither switched nor behind `Deref`; `fake_borrows` is empty (`util.rs:224-229`) | `u = true;` | No fake borrow or shared guard borrow overlaps `u` | Compiles cleanly (`compile_returncode = 0`) |

**Empirical Nuance — `Box` Built-In Deref vs. Trait `Deref` in `#![feature(deref_patterns)]`:** A subtle distinction uncovered by the live `rustc 1.98.0-nightly` MIR dumps (`probe_results.json`) is that matching a `Box<bool>` with `deref!(true)` lowers in `rustc` via built-in `PlaceElem::Deref` (`switchInt(copy (*_1))`), hitting the `else` branch of `visit_match_pair` (`util.rs:188`) and emitting **two shallow fake borrows**: `_2 = &fake shallow (*_1); _3 = &fake shallow _1;` (producing `E0510` on `*b = true`). Only types lowered via a trait deref call such as `Vec<u32>` (`<Vec<u32> as Deref>::deref(move _8)`) take the `TestableCase::Deref` branch (`util.rs:171, 185`), emitting `_3 = &fake _1;` (`FakeBorrowKind::Deep`), which produces `E0502` on `v[0] = 9` and `E0510` on `v = Vec::new()`. Either mechanism prevents guard mutation from invalidating deref sub-pattern assumptions.

---

### 3. `CleanupPostBorrowck` Erasure Pass and Observed MIR Transitions

Basis: source (`cleanup_post_borrowck.rs:1-90`) + execution (`probe_results.json` `-Zdump-mir`)

`CleanupPostBorrowck` runs once immediately after NLL borrow checking (`MirPhase::Analysis` -> `MirPhase::Analysis(PostCleanup)`) as a `Required` pass (`policy() -> PassPolicy::Required` in `HEAD`; `is_required() -> true` in `1.98.0-nightly`). Its exact rewrite rules (`cleanup_post_borrowck.rs:32-84`) are:

1. Replace with `StatementKind::Nop` (`statement.make_nop(true)`):
   - `StatementKind::AscribeUserType(..)`
   - `StatementKind::Assign((_, Rvalue::Ref(_, BorrowKind::Fake(_), _)))` (both `Shallow` and `Deep`)
   - `StatementKind::FakeRead(..)` (`ForMatchGuard`, `ForGuardBinding`, `ForMatchedPlace`, etc.)
   - `StatementKind::BackwardIncompatibleDropHint { .. }`
   - `StatementKind::Coverage(kind)` where `kind.is_removed_after_analysis()` (`HEAD`) / `BlockMarker | SpanMarker` (`1.98`)
2. Lower borrowck-tracked pointer coercions (`PointerCoercion::ArrayToPointer | MutToConstPointer`) to `CastKind::PtrToPtr` (`lines 42-57`).
3. Replace `TerminatorKind::FalseEdge { real_target, .. }` and `FalseUnwind { real_target, .. }` with unconditional `Goto { target: real_target }`, setting `invalidate_cfg = true` and calling `body.basic_blocks.invalidate_cfg_cache()` (`lines 65-77`).
4. Clear `body.user_type_annotations.raw` and `decl.user_ty` across all locals (`lines 79-83`).

Notice what `CleanupPostBorrowck` **retains**: the administrative fake-borrow local declaration (`let mut _2: &Option<u32>;`) and the generated `Nop` instructions remain in the MIR until later CFG/local-simplification passes (`SimplifyCfg-post-analysis`, `RemoveZsts`, `SimplifyLocals`). Live `rustc 1.98.0-nightly` dumps verify every transition verbatim:

#### Probe 1: `guard_probe` (`match x { Some(v) if v > 5 => v, _ => 0 }`) — `CleanupPostBorrowck.before.mir` vs. `CleanupPostBorrowck.after.mir`

```rust
// BEFORE CleanupPostBorrowck (probe.guard_probe.2-1-002.CleanupPostBorrowck.before.mir):
    bb2: {
        falseEdge -> [real: bb3, imaginary: bb1];
    }
    bb3: {
        StorageLive(_5);
        _5 = &((_1 as Some).0: u32);
        _2 = &fake shallow _1;
        ...
        switchInt(move _6) -> [0: bb5, otherwise: bb4];
    }
    bb4: {
        ...
        FakeRead(ForMatchGuard, _2);
        FakeRead(ForGuardBinding, _5);
        StorageLive(_4);
        _4 = copy ((_1 as Some).0: u32);
        _0 = copy _4;
        ...
    }
    bb5: {
        ...
        StorageDead(_5);
        falseEdge -> [real: bb1, imaginary: bb1];
    }

// AFTER CleanupPostBorrowck (probe.guard_probe.2-1-002.CleanupPostBorrowck.after.mir):
    bb2: {
        goto -> bb3;
    }
    bb3: {
        StorageLive(_5);
        _5 = &((_1 as Some).0: u32);
        nop;
        ...
        switchInt(move _6) -> [0: bb5, otherwise: bb4];
    }
    bb4: {
        ...
        nop;
        nop;
        StorageLive(_4);
        _4 = copy ((_1 as Some).0: u32);
        _0 = copy _4;
        ...
    }
    bb5: {
        ...
        StorageDead(_5);
        goto -> bb1;
    }
```

(In `runtime-optimized.after.mir`, `SimplifyLocals` and `SimplifyCfg` further compact `_5`, eliminate `nop`, and collapse dead jumps cleanly down to `bb0..bb5`.)

#### Probe 2: `deref_guard_probe` (`Box<bool>`) vs. `vec_deref_guard_probe` (`Vec<u32>`) — Shallow Prefixes vs. Deep Fake Borrow

- **`Box<bool>` (`deref_guard_probe.1-1-000.built.after.mir` -> `CleanupPostBorrowck.after.mir`):**
  `bb8` initializes `_2 = &fake shallow (*_1); _3 = &fake shallow _1;`, and `bb11` anchors `FakeRead(ForMatchGuard, _2); FakeRead(ForMatchGuard, _3);`. `CleanupPostBorrowck` rewrites both fake assignments and both fake reads to `nop;`, and turns `bb1` / `bb2` `falseEdge` terminators into `goto -> bb6;` / `goto -> bb7;`. Note that `bb4` in `built` (`bb3` after cleanup) re-reads `(*_1)` cleanly only because `&fake shallow (*_1)` and `&fake shallow _1` prevented `*b` mutation during the guard.
- **`Vec<u32>` (`vec_deref_guard_probe.1-1-000.built.after.mir` -> `CleanupPostBorrowck.after.mir`):**
  `bb0` calls `_2 = <Vec<u32> as Deref>::deref(move _8)`, `bb10` emits `_3 = &fake _1;` (`Deep`, printed without `shallow`), and `bb13` anchors `FakeRead(ForMatchGuard, _3);`. `CleanupPostBorrowck` rewrites `_3 = &fake _1;` and `FakeRead(ForMatchGuard, _3);` to `nop;` and `falseEdge` to `goto`.
- **Uninhabited `match v {}` (`uninhabited_probe`):**
  `bb0` emits `PlaceMention(_1); FakeRead(ForMatchedPlace(None), _1); unreachable;` before `CleanupPostBorrowck`, which turns `FakeRead(ForMatchedPlace(None), _1);` into `nop;` while `PlaceMention(_1);` remains until `RemovePlaceMention` (`3-1-002`).

---

### 4. `RefWithinGuard`, Interior Mutability (`Cell`), and Or-Pattern Guard Bindings

Basis: source (`matches/mod.rs:498-549, 2428-2867`, `mutability_errors.rs:128-133, 557-564`) + execution (`probe_results.json`)

#### Dual-Local Lowering (`RefWithinGuard` vs. `OutsideGuard`)

When a pattern arm carries a guard, `declare_binding` (`compiler/rustc_mir_build/src/builder/matches/mod.rs:2840-2861`) allocates **two** distinct locals for every pattern variable (`LocalsForNode::ForGuard { ref_for_guard, for_arm_body }`):

- `for_arm_body`: declared with the user's pattern mutability (`mode.1`), representing the actual arm-body binding `OutsideGuard`.
- `ref_for_guard`: declared with **`mutability: Mutability::Not`**, type `&'erased T`, and metadata `BindingForm::RefForGuard(for_arm_body)`.

During `bind_matched_candidate_for_guard` (`mod.rs:2643-2706`):
- **By-value bindings (`ByRef::No`):** `rustc` does **not** move or copy the matched value yet. It emits `StorageLive(ref_for_guard)` and `ref_for_guard = &(binding.source)` (`BorrowKind::Shared`). Every mention of `v` inside the guard denotes `(*ref_for_guard)` (`RefWithinGuard`).
- **By-reference bindings (`ByRef::Yes(pinnedness, mutbl)`):** `rustc` eagerly initializes `value_for_arm` (`OutsideGuard`) with `&` or `&mut` pointing at `binding.source` (plus pinning if pinned), and then takes a shared reference `ref_for_guard = &value_for_arm` (`BorrowKind::Shared`). Consequently, even for `Some(ref mut v) if ...`, `v` has type `&mut Box<u32>` accessed through `(*ref_for_guard): & &mut Box<u32>`, so writing `*v = Box::new(99)` inside the guard still attempts a write through `*ref_for_guard` (`PlaceRef { local, projection: [ProjectionElem::Deref] }` where `is_ref_for_guard() == true`).

Borrow checking enforces two distinct diagnostic rules on `ref_for_guard`:
1. Any direct mutation through or to `*ref_for_guard` triggers `E0594` in `mutability_errors.rs:128-133, 557-564` with the note `"variables bound in patterns are immutable until the end of the pattern guard"` — confirmed identically for both `Some(ref mut v)` and `Some(mut v)` in `probe_results.json`.
2. `FakeRead(ForGuardBinding, ref_for_guard)` (`mod.rs:2514-2518`) extends the `BorrowKind::Shared` loan of `ref_for_guard` across the entire guard until guard-true confirmation, blocking `x = None` with `E0506` rather than moving prematurely. Only on the true branch, **after** both `FakeRead(ForMatchGuard)` and `FakeRead(ForGuardBinding)`, does `bind_matched_candidate_for_arm_body` execute `_4 = move/copy ((_1 as Some).0)` (`mod.rs:2520-2524, 2734-2736`).

#### Interior Mutability (`Cell`) Across Guard Evaluation and Fallthrough

Because `ref_for_guard` takes `BorrowKind::Shared` (never exclusive `&mut`) and `FakeBorrow(Shallow)` permits mutation through shared aliases (`UnsafeCell` / `Cell<T>`) that do not write directly to the shallow-borrowed place or its prefixes, mutating a `Cell` inside a match guard is accepted in three distinct situations — all empirically verified on `rustc 1.98.0-nightly`:

- Mutating the `Cell` after `cell.take()` while an active `Some(v)` guard holds `v` (`CELL_GUARD_VAL=17`).
- Mutating a `Cell` bound via `ref cell` inside a guard (`INTERIOR_REF_VAL=17`), then reading the mutated value in the selected arm body (`=> cell.get()`).
- Mutating an outer `MatchedCellField { tag: true, c: Cell<u32> }` field (`s.c.set(17); false`) inside a **failing** guard and observing `s.c.get() == 17` after control falls through to the subsequent arm (`INTERIOR_MUT_ACROSS_FALLTHROUGH=17`). Notice why discriminant safety still holds: `&fake shallow _1` freezes structural tags/discriminants and non-interior-mutable payload places referenced by subsequent decision-tree tests, while interior mutability inside `UnsafeCell` cannot overwrite the outer enum tag through `&Cell<T>`.

#### Or-Pattern Guard Lowering, Reverse Sub-Branch Order, and Shared Guard Viewing

An arm such as `PairStr::Left(s) | PairStr::Right(s) if check_once(&s, &mut once_ctr) => s` demonstrates why `bind_matched_candidate_for_guard` and `bind_matched_candidate_for_arm_body` are separated (`matches/mod.rs:498-549, 2428-2525`):

1. **Per-Sub-Branch Guard Duplication:** In the live `-Zdump-mir=or_guard_probe` dump (`probe_results.json`), `bb9` lowers arm sub-branch `Two::A(s)` (`_6 = &((_1 as A).0)`, `_3 = &fake shallow _1`, `*gate += 1; s.len() > 2`), while `bb7` independently lowers sub-branch `Two::B(s)` (`_6 = &((_1 as B).0)`, `_3 = &fake shallow _1`, `*gate += 1; s.len() > 2`).
2. **Left-to-Right Short-Circuiting and Re-Evaluation:** For `(Some(x), _) | (_, Some(x))`, empirical execution measures:
   - First sub-branch guard succeeds (`(Some(10), Some(20))` with `x > 5`): `SHORT_CHECKS=1 SHORT_VAL=10`.
   - First sub-branch guard fails and second succeeds (`(Some(1), Some(2))` with `x > 1`): `OR_SUBBRANCH_CHECKS=2 PICKED=2`.
   - Both sub-branch guards fail (`(Some(1), Some(1))` with `x > 5`): `MISS_CHECKS=2 MISS_VAL=99`.
3. **Move-Once Soundness After Shared Guard Inspection:** For `PairStr::Right(String::from("hi"))` matching `PairStr::Left(s) | PairStr::Right(s) if check_once(&s, &mut once_ctr) => s`, live execution confirms `OR_CHECKS_ONCE=1 OR_MOVE_OUT=hi RES=ok`. Inspection of `or_guard_probe.1-1-000.built.after.mir` shows `_6: &String` (`ForGuardBinding`) is passed to `String::len` inside the guard blocks (`bb12`, `bb17`), whereas `_5 = move ((_1 as B).0)` (`bb14`) and `_5 = move ((_1 as A).0)` (`bb19`) occur **only** on the guard-true edge right before jumping to shared arm block `bb11` (`_0 = move _5`).
4. **Reverse Sub-Branch Lowering for Drop Order (`#142163`):** Because each guard sub-branch schedules and then clears its own arm/guard drop scopes via `clear_match_arm_and_guard_scopes` except on the last iteration (`ScheduleDrops::Yes` when `pos.is_last()`, `mod.rs:534-545, 2463-2468`), `bind_pattern` iterates `branch.sub_branches.into_iter().rev().with_position()` (`mod.rs:534`) so the retained arm-body drop schedule reflects the binding order of the *first* source sub-pattern rather than the last.

---

### 5. Integration Boundaries for Verified `rustc` and Anneal MIR Semantics

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted.lean`, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `trusted/audit/TrustedBoundary.lean`) + derived

1. **Mandatory MIR Phase Boundary (Post-`CleanupPostBorrowck`):** In `rust-lang/rust`, pre-`CleanupPostBorrowck` MIR (`built`, `analysis`) legitimately constructs `&fake shallow` / `&fake` borrows pointing into uninitialized or inactive enum variants (`util.rs:59-70`) and retains `FalseEdge` terminators linking mutually exclusive control paths for NLL soundness. Consuming `built` or `analysis` MIR in an operational interpreter would falsely trigger undefined behavior or miss unreachable invariants. Downstream capture pipelines for `Anneal` (`Trusted.MirAst`) MUST consume MIR at or after `MirPhase::Analysis(PostCleanup)` (`CleanupPostBorrowck.after`), or explicitly replicate `cleanupStmt` / `cleanupTerm`.
2. **Alignment with `deinitMovedPlace = true` (`Trusted.MirSemantics.lean:949-972`):** Anneal's `evalOperandToSlot` models `Operand.move` conservatively by resetting non-ZST moved local slots to `liveUninitSlot ty` (`.live none`), matching `Miri.Interpreter.OperandMachine.evalOperand` with `deinitMovedPlace = true`. That transition matches `rustc`'s delayed placement of `ByRef::No` moves inside `bind_matched_candidate_for_arm_body`: because `bind_matched_candidate_for_guard` reads only via shared `&T` (`ref_for_guard`), failing a match guard never triggers `liveUninitSlot`, while taking the guard-true branch moves out once (`bb14` / `bb19` in `or_guard_probe`) after which dynamic drop flags (visible as `_14`/`_15` in `or_guard_probe.3-3-000.runtime-optimized.after.mir`) track deinitialization.
3. **Fail-Closed Representation Discipline (`Trusted.MirAst.lean:620-628` & `TrustedBoundary.lean:1117-1152`):** Currently `Trusted.MirAst.Rvalue` deliberately lowers unsupported aggregate/reference constructs fail-closed to `.unsupported`, and `TrustedBoundary.ensureReplayableConstant` enforces zero `unsafe`/`partial`/`quotInfo`/`_unsafe_rec`/missing-body declarations before `Kernel.Environment.replay`. Any future expansion of `Trusted.MirAst` to support guard references, indirect `Cell` heaps, or match-tree borrows must preserve fail-closed behavior on any residual unmodeled `FakeRead` / `FakeBorrow` / `FalseEdge` instructions.

---

### 6. Kernel-Checked Lean `v4.34.1` Soundness Mechanization (`Anneal.MatchGuardSoundness`)

Basis: source + execution (`support/MatchGuardFakeBorrowAndOrPatternSoundness.lean`)

The formalization in `support/MatchGuardFakeBorrowAndOrPatternSoundness.lean` (`2,832` lines; `953` constants in `Anneal.MatchGuardSoundness.*`: `346` theorems, `506` `noncomputable def`s, `0` plain recursive `def`s, `0` `partial`, `0` `._unsafe_rec`, `0` `deriving`, `0` `sorry`, `0` `Classical.choice`/`omega`/`bv_decide`/`native_decide`, kernel axioms exclusively `[Quot.sound, propext]`) establishes exact syntactic, borrow-checking, and operational theorems mirroring `rustc`:

#### Part I: Place Conflict Algebra and Store Semantics (`lines 68-1445`)

- **Shallow vs. Deep Conflict Predicates (`lines 359-395`):**
  ```lean
  noncomputable def shallowConflicts (borrowPlace accessPlace : Place) : Bool :=
    Place.isPrefix accessPlace borrowPlace

  noncomputable def deepConflicts (borrowPlace accessPlace : Place) : Bool :=
    Place.overlap borrowPlace accessPlace
  ```
  - `shallowConflict_implies_deepConflict` (`L366`): every shallow conflict is also a deep conflict.
  - `shallowConflict_proj_len_le` (`L378`): any conflicting access has `a.proj.length <= b.proj.length`, formalizing `places_conflict.rs:288`.
  - `strictProjection_not_shallowConflict` (`L385`): witnesses mutating `(x.0 as Some).0` (`[field 0, downcast 1, field 0]`) while holding `&fake shallow x.0` (`[field 0]`) yields `false`.
  - `derefPrefixes_isPrefix` (`L452`): every element returned by `Place.derefPrefixes` (`util.rs:127-138`) is a prefix of the bound place.
- **Memory Model with `deinitMovedPlace = true` (`lines 458-1445`):**
  `MirStore` tracks `locals : List LocalSlot` (`dead | live (optVal : Option Val)`), `boxHeap : List (Option Val)`, and `cellHeap : List (Option Val)`. Key store lemmas:
  - `writeProjInVal_preserves_discriminant` (`L650`): mutating any non-empty projection inside `Val` preserves `v.discriminant`.
  - `writeProjInVal_strictDescendant_preserves_prefix_discr` (`L884`): mutating a strict descendant projection `qs` inside `v` (`ps.length < qs.length`) preserves the discriminant at prefix `ps`.
  - `writeProjInVal_disjoint_preserves_read` (`L1130`): mutating a non-overlapping projection preserves `readProjFromVal`.
  - `writeCell_preserves_readPlace_noDeref` (`L1222`): `Cell::set` writes (`cellHeap`) leave every non-deref `readPlace` invariant.
  - `writePlace_noShallowConflict_preserves_readDiscr` (`L1371`): any non-deref write `st.writePlace q newV = some st'` with `shallowConflicts p q = false` preserves `readDiscr p`.

#### Part II: Borrowck Diagnostic Partition and Permissions (`lines 1446-1712`)

`checkStmtBorrowck` (`L1560`) and `checkStmtsBorrowck` (`L1617`) model earliest-issued NLL loan conflict checks (`E0510` for direct writes/mut-borrows conflicting with `Fake`, `E0506` for direct writes conflicting with `Shared`/`Mut`, `E0502` for mut-borrows conflicting with `Shared`/`FakeDeep`, and `E0594` for writes or `&mut` through a `RefWithinGuard` deref place `isRefGuard dst.localId && projHasDeref dst.proj`):

- `e0510_on_fakeShallow_wildcard` (`L1627`): `Some(_)` wildcard match + `x = None` = `.error .E0510`.
- `e0506_on_shared_guard_binding_before_fake` (`L1640`): `Some(_y)` guard binding (`_5 = &x.Some.0` issued before `_2 = &fake shallow x`) + `x = None` = `.error .E0506`.
- `e0502_vs_e0510_on_fakeDeep_deref_pattern` (`L1657`): `FakeBorrow(Deep)` on `Vec` returns `.error .E0502` on mutable element borrow vs. `.error .E0510` on direct overwrite `v = ...`.
- `e0594_on_ref_within_guard_write` (`L1675`): writing `*_5 = 99` or taking `&mut *_5` when `isRefGuard 5 = true` = `.error .E0594`.
- `cellWrite_admitted_under_fakeShallow_and_shared` (`L1685`): `Rvalue.cellWrite` succeeds with both `&fake shallow s` and `&s` active (`∃ loans', ... = .ok loans'`).
- `strictProjection_mutBorrow_admitted_under_fakeShallow` (`L1701`): mutably borrowing `(x.0 as Some).0` succeeds under `&fake shallow x.0`.

#### Part III: Main Soundness Theorems 1–3 (`lines 1713-2607`)

1. **Theorem 1 — Discriminant Stability (`lines 2303-2327`):**
   ```lean
   theorem discriminant_stability_of_fake_borrow_shallow
       (frozen : List Place) (stmts : List StatementKind) (st st' : MirStore)
       (hAll : ∀ s, s ∈ stmts → guardStmtPreservesShallow frozen s)
       (hRun : runStmts st stmts = .ok st') :
       ∀ p, p ∈ frozen → projHasDeref p.proj = false → st'.readDiscr p = st.readDiscr p
   ```
   Across any arbitrary-length sequence of guard statements admitted under `FakeBorrow(Shallow)` (including payload writes to disjoint fields/sub-variants and `Cell` interior mutations), every tested place `p ∈ frozen` has **identical discriminant** before and after guard execution.

2. **Theorem 2 — Guard Binding Immutability & Move-Once Safety (`lines 2552-2607`):**
   ```lean
   theorem ref_within_guard_immutability_and_move_once
       (bound : List Place) (stmts : List StatementKind) (st st' : MirStore)
       (hAll : ∀ s, s ∈ stmts → guardStmtPreservesBound bound s)
       (hRun : runStmts st stmts = .ok st') :
       (∀ src, src ∈ bound → projHasDeref src.proj = false → st'.readPlace src = st.readPlace src) ∧
       (∀ (loc : LocalId) (v : Val) (st'' : MirStore),
         v.isZstUnit = false →
         st'.movePlace (Place.local loc) = some (v, st'') →
         st''.movePlace (Place.local loc) = none)
   ```
   Across any guard sequence respecting `RefWithinGuard`/`ForGuardBinding` loans, every non-deref bound place `src` keeps its exact pre-guard value (`readPlace src` is invariant), so guard failure leaves `src` live for subsequent arms, while guard entry's first non-unit `movePlace` transitions the local to `.live none`, causing any second move to yield `none`.

3. **Theorem 3 — `CleanupPostBorrowck` Observational Erasure Equivalence (`lines 1974-1985`):**
   ```lean
   theorem cleanup_post_borrowck_observational_erasure_equiv
       (body : MirBody) (fuel : Nat) (es : ExecState) :
       runMir true (cleanupBody body) fuel es = runMir false body fuel es
   ```
   Supported by lockstep lemmas `stepStmt_cleanup_equiv` (`L1933`), `stepTerm_cleanup_equiv` (`L1945`), `stepMir_cleanup_equiv` (`L1951`), and idempotence lemmas `cleanupStmt_idempotent` / `cleanupTerm_idempotent` / `cleanupBlock_idempotent` / `cleanupBody_idempotent` (`L1738-1774`), post-`CleanupPostBorrowck` execution (which rejects any residual `&fake`, `FakeRead`, `AscribeUserType`, or `FalseEdge` with `.fault .unsupported`) produces bit-for-bit identical outcomes (`Except FaultKind (Option Val × MirStore)`) to pre-cleanup MIR across all bodies, initial states, and fuel bounds.

#### Part IV: Or-Pattern Guard Equational Equivalence and Concrete Witnesses (`lines 2609-2832`)

4. **Theorem 4 — Or-Pattern Per-Branch Short-Circuit & Move-Once Equivalence (`lines 2676-2718`):**
   ```lean
   theorem or_pattern_per_branch_short_circuit_and_move_once :
       (∀ (arm : OrArm) (bs : List OrSubBranch) (idx calls : Nat) (st : MirStore),
         evalOrBranchesLowered arm idx calls st bs = evalOrBranchesSource arm idx calls st bs) ∧
       (∀ (arm : OrArm) (b0 : OrSubBranch) (rest : List OrSubBranch) (st stG : MirStore) (v0 : Val),
         b0.matchesPattern st = some v0 →
         b0.guardEval v0 st = (true, stG) →
         let tr := evalOrBranchesLowered arm 0 0 st (b0 :: rest)
         tr.guardCalls = 1 ∧ tr.selectedBranch = some 0 ∧
         tr.result = (arm.armBody v0 stG).1 ∧ tr.finalStore = (arm.armBody v0 stG).2) ∧
       (∀ (arm : OrArm) (b0 b1 : OrSubBranch) (rest : List OrSubBranch)
         (st stG0 stG1 : MirStore) (v0 v1 : Val),
         b0.matchesPattern st = some v0 →
         b0.guardEval v0 st = (false, stG0) →
         b1.matchesPattern stG0 = some v1 →
         b1.guardEval v1 stG0 = (true, stG1) →
         let tr := evalOrBranchesLowered arm 0 0 st (b0 :: b1 :: rest)
         tr.guardCalls = 2 ∧ tr.selectedBranch = some 1 ∧
         tr.result = (arm.armBody v1 stG1).1 ∧ tr.finalStore = (arm.armBody v1 stG1).2)
   ```
- **Concrete Kernel-Checked Witnesses Matching Live Probes:**
  - `witness_guard_probe_cleanup_equiv` (`L2759`): models `guard_probe` (6 basic blocks, `FalseEdge`, `&fake shallow _1`, `ForMatchGuard`, `ForGuardBinding`), proving `Some(42)` with guard `true` returns `42`, guard `false` returns `0`, `None` returns `0`, and `runMir true (cleanupBody ...) = runMir false ...`.
  - `witness_or_pattern_short_circuit_and_fallthrough` (`L2793`): proves `(Some(10), Some(20))` hits `(guardCalls=1, selectedBranch=some 0)`, `(Some(1), Some(20))` hits `(guardCalls=2, selectedBranch=some 1)`, and `(Some(1), Some(1))` hits `(guardCalls=2, selectedBranch=none)`.
  - `witness_cell_interior_mut_across_fallthrough` (`L2807`): proves `MatchedCellField { tag: true, c: Cell::new(5) }` satisfies `guardStmtPreservesShallow`, mutates `cellHeap[0] := 17`, preserves `tag = true` (`readDiscr = some 1`), and observes `17` across fallthrough.

---

## Boundaries

The negative space of this investigation separates four explicit boundary classes:

1. **`not examined` — Unaudited Runtime & Compiler Subsystems:**
   - **Full NLL Region/Liveness Fixpoint (`rustc_borrowck::region_inference`):** The Lean borrow-checking model (`checkStmtBorrowck`) models sequential statement-order loan conflict detection and diagnostic prioritization (`places_conflict.rs`, `conflict_errors.rs`, `mutability_errors.rs`), not Polonius/NLL CFG dataflow liveness or drop-liveness region inference.
   - **Two-Phase Borrows Beyond Guard Conflicts:** While `(Shared | Fake(Deep), Mut { Default | TwoPhaseBorrow })` is inspected in `conflict_errors.rs:1822-1860`, general two-phase reservation/activation semantics in match guards (such as method-receiver two-phase calls interleaved with pattern deref temps) were not separately probed.
   - **`RefCell` Dynamic Panics, Async/Coroutine `FalseUnwind`/Yield Interactions, and `unsafe` Raw Pointers:** `probe_match_guard_fake_borrow.py` verified `Cell` interior mutability, `Box`/`Vec` `deref!` patterns, `Option`/`struct`/tuple matches, and or-patterns; runtime `RefCell` borrow-flag panics inside guards, coroutine matches holding fake borrows across `Yield`, and `unsafe` raw-pointer writes bypassing alias tracking were not empirically executed (`unsafe` raw-pointer mutation can corrupt matched discriminants outside safe Rust's borrowck guarantees).
   - **Other `rustc` Channels/Versions (`stable`, older nightlies, `1.102+`):** Live execution covered `rustc 1.98.0-nightly (14210df0e 2026-05-31)` on `x86_64-unknown-linux-gnu`; primary-source inspection additionally covered upstream `rust-lang/rust@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`. Behavior on unreleased or older compiler commits is inferred only where AST/MIR logic aligns and is not directly verified outside those two revisions.

2. **`known not to apply` — Invalid Extrapolations Refuted by Evidence:**
   - **Wrong generalization: "Every guard borrow mutation produces `E0510`."** Known not to apply: pattern bindings under `&` (`Some(_y)`) emit `E0506`, writes to `RefWithinGuard` bindings emit `E0594`, mutable element borrows under `FakeBorrowKind::Deep` (e.g., `Vec` `deref!`) emit `E0502`, and strict sub-projections of shallow-borrowed places (e.g., mutating `x.0.0` under `(Some(_), false)`) plus `Cell::set` interior mutations compile with **zero errors**.
   - **Wrong generalization: "Every `deref!` pattern emits `FakeBorrowKind::Deep`."** Known not to apply: `Box<bool>` `deref!(true)` lowers via built-in `PlaceElem::Deref` (`util.rs:188`) using `&fake shallow (*_1)` and `&fake shallow _1` (`E0510` on `*b = true`), whereas `Vec<u32>` `deref!([1, ..])` invokes `<Vec as Deref>::deref` (`TestableCase::Deref`, `util.rs:185`) and emits `&fake _1` (`Deep`, giving `E0502` on `v[0] = 9`).
   - **Wrong generalization: "Pre-`CleanupPostBorrowck` MIR can be executed directly by a concrete interpreter."** Known not to apply: as documented verbatim in `util.rs:59-70`, `&fake` references may target inactive enum variants (`Some(Some(_))` when the outer or inner variant is inactive) and cannot be materialized safely at runtime; only post-`CleanupPostBorrowck` MIR replaces `&fake`, `FakeRead`, and `FalseEdge` safely.
   - **Wrong generalization: "A match guard runs once per arm regardless of `|` alternatives."** Known not to apply: `rustc` lowers guarded or-patterns by duplicating guard evaluation per matching sub-branch (`OR_SUBBRANCH_CHECKS=2`, `SHORT_CHECKS=1`, `MISS_CHECKS=2`).
   - **Safe `PartialEq` / `Deref` Misbehavior Under Custom Impls:** Known not to apply without `StructuralPartialEq` / `DerefPure` idempotence guarantees: user-defined non-idempotent `Deref` or interior-mutable `Deref` traits (outside built-in `Box`/slices) are outside safe constant/deref-pattern soundness assumptions (`#![feature(deref_patterns)]` remains unstable).

3. **`unsupported` — Formal Model Boundaries in Lean `v4.34.1`:**
   - **`Val.boxPtr` and `.deref` Targets in `writePlace_noShallowConflict_preserves_readDiscr`:** Theorem 1 and Theorem 2 require `projHasDeref p.proj = false` on protected places (and `MirStore.writePlace` supports one-hop `&mut` writes only to locals with `target.proj = []`); deep mutable pointer chains through `boxPtr` (`Box`) or nested `&mut` projections are modeled only at concrete witnesses (`FakeBorrowKind.fakeDeep` in Part II).
   - **Fuel-Bounded Execution:** `cleanup_post_borrowck_observational_erasure_equiv` quantifies universally over every finite step budget `fuel : Nat` via `runMir`, proving lockstep equivalence at all finite horizons (`stepMir_cleanup_equiv`), rather than coinductively over infinite traces (`Diverges` in `Anneal`'s `Trusted.MirSemantics.lean:1665` is not duplicated here).
   - **Exact Compiler AST FFI:** `MirBody` / `MirStore` is a faithful clean-slate Lean `v4.34.1` formalization rather than an automated extractor from `rustc_middle::mir::Body`.

4. **`unknown` — Remaining Open Design Questions:**
   - Whether future stabilization of `#![feature(deref_patterns)]` will unify built-in `Box` derefs and trait `DerefPure` receivers under a single `TestableCase::Deref` `FakeBorrowKind::Deep` rule or retain distinct `Box` shallow-prefix lowering.

---

## Evidence

### 1. Upstream Primary-Source Coordinates

| Repository & Commit | Path & Lines | Role | Key Verified Artifact / Rule |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` `@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_mir_build/src/builder/matches/util.rs:17-33, 36-239` | source + documentation | `false_edges`, `collect_fake_borrows`, `FakeBorrowCollector` (`Deep` at `L185`, `Shallow` at `L188`, `fake_borrow_deref_prefixes` at `L127-138, 229`), `ref_pat_borrow_kind` (`L234-239`) |
| `rust-lang/rust` `@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_mir_build/src/builder/matches/mod.rs:498-550, 1593-1655, 1833-1925, 2418-2538, 2643-2745, 2796-2867` | source | Reverse `bind_pattern` loop (`#142163`, `L532-546`), `ForMatchedPlace(None)` (`L1646-1654`), `expand_and_match_or_candidates` (`L1833-1925`), `bind_and_guard_matched_candidate` (`ForMatchGuard` + `ForGuardBinding`, `L2428-2525`), `bind_matched_candidate_for_guard` (`L2643-2706`), `declare_binding` (`RefForGuard`, `L2840-2861`) |
| `rust-lang/rust` `@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:1-90` | source + documentation | `CleanupPostBorrowck::run_pass` (`Nop` erasure `L32-41`, `PtrToPtr` `L42-57`, `TerminatorKind::goto` `L65-72`, `PassPolicy::Required` `L86-89`) |
| `rust-lang/rust` `@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_borrowck/src/places_conflict.rs:248-296` | source | `borrow_conflicts_with_place` shallow prefix check (`borrow_place.projection.len() < access_place.projection.len() => false`, `L288-296`) |
| `rust-lang/rust` `@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_borrowck/src/diagnostics/conflict_errors.rs:1820-1865, 1935-1945, 1997-2039, 3997-4045, 4278-4303` | source | `E0502` (`Shared \| FakeDeep`), `E0510` (`(Mut, FakeShallow)` and `report_illegal_mutation_of_borrowed` `if let BorrowKind::Fake(_)`), `ForMatchGuard => Some("match guard")`, fallback `E0506` (`cannot_assign_to_borrowed`) |
| `rust-lang/rust` `@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_borrowck/src/diagnostics/borrowck_errors.rs:361-380`, `mutability_errors.rs:128-133, 557-564` | source | `cannot_mutate_in_immutable_section` (`E0510`), `is_ref_for_guard()` (`E0594`) |
| `rust-lang/rust` `@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_middle/src/mir/syntax.rs:248-295, 509-564` | documentation + source | `FakeBorrowKind` (`Shallow`, `Deep`) and `FakeReadCause` (`ForMatchGuard`, `ForMatchedPlace`, `ForGuardBinding`) |
| `rust-lang/rust` `@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Matched source files (`util.rs:161-193`, `cleanup_post_borrowck.rs:19-91`, `matches/mod.rs:2468-2543`, `conflict_errors.rs`, `mutability_errors.rs`, `borrowck_errors.rs`) | source | Verified `1.98.0-nightly` code matches `HEAD` modulo `MatchPairKind`, `CoverageKind::is_removed_after_analysis()`, `TerminatorKind::goto`, `then_else_break` -> `lower_if_condition`, and `PhantomDeref` arms |
| `joshlf/anneal` `main@c131b320eeeb26ef692e5afd5ec8db49ee518613` & `unstable@7133a9f5c779f624f513ee1e29fd9742214ce3e1` | `trusted/lean/Trusted.lean:1-19`, `Trusted/MirAst.lean:550-650`, `Trusted/MirSemantics.lean:949-976, 1665-1750`, `trusted/audit/TrustedBoundary.lean:442-535, 1050-1225` | source | `evalOperandToSlot` (`deinitMovedPlace = true`), fail-closed `.unsupported` `Rvalue` handling, `ensureReplayableConstant` |

### 2. Live `rustc 1.98.0-nightly` Execution Receipts (`support/probe_results.json`, `88,812` bytes)

Executed `2026-11-24` via `python3 support/probe_match_guard_fake_borrow.py` under `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), all sources compiled in isolated `tempfile.TemporaryDirectory()` workspaces with `--edition=2024`:

- **Group A (`a_fake_borrow_e0510_vs_e0506_and_mir_cleanup` — 15 probes):**
  - `wildcard_scrutinee_mutation_rejected_e0510`: `compile_rc=1`, `error[E0510]: cannot assign x in match guard`.
  - `binding_scrutinee_mutation_rejected_e0506`: `compile_rc=1`, `error[E0506]: cannot assign to x because it is borrowed`.
  - `shallow_fake_borrow_allows_disjoint_payload_mutation`: `compile_rc=0` (clean compile).
  - `shallow_fake_borrow_rejects_field_tag_overwrite_e0510`: `compile_rc=1`, `error[E0510]: cannot assign x.0 in match guard`.
  - `tested_subpattern_payload_shallow_fake_borrow_rejects_payload_mut_e0510`: `compile_rc=1`, `error[E0510]: cannot mutably borrow x.0.0 in match guard`.
  - `box_deref_pattern_shallow_fake_borrow_rejects_pointee_mut_e0510`: `compile_rc=1`, `error[E0510]: cannot assign *b in match guard`.
  - `vec_deref_pattern_deep_fake_borrow_rejects_elem_mut_e0502`: `compile_rc=1`, `error[E0502]: cannot borrow v as mutable because it is also borrowed as immutable`.
  - `vec_deref_pattern_deep_fake_borrow_rejects_scrutinee_assign_e0510`: `compile_rc=1`, `error[E0510]: cannot assign v in match guard`.
  - `binding_behind_deref_prefix_shallow_fake_borrow_e0510`: `compile_rc=1`, `error[E0510]: cannot assign x in match guard`.
  - `irrefutable_local_binding_without_deref_allows_mutation`: `compile_rc=0` (clean compile).
  - `mir_built_vs_cleanup_post_borrowck` (`-Zdump-mir=guard_probe`): `compile_rc=0`, captured `built.after`, `CleanupPostBorrowck.before`, `CleanupPostBorrowck.after`, `runtime-optimized.after`.
  - `mir_box_deref_pattern_built_vs_cleanup` (`-Zdump-mir=deref_guard_probe`): `compile_rc=0`, captured `built.after`, `CleanupPostBorrowck.before/after`, `runtime-optimized.after`.
  - `mir_vec_deref_pattern_deep_fake_borrow_built_vs_cleanup` (`-Zdump-mir=vec_deref_guard_probe`): `compile_rc=0`, captured `built.after`, `CleanupPostBorrowck.before/after`, `runtime-optimized.after`.
  - `mir_uninhabited_exhaustive_fake_read_for_matched_place` (`-Zdump-mir=uninhabited_probe`): `compile_rc=0`, captured `built.after`, `CleanupPostBorrowck.before/after`, `runtime-optimized.after`.
  - `mir_or_pattern_guard_built_vs_cleanup` (`-Zdump-mir=or_guard_probe`): `compile_rc=0`, captured `built.after`, `CleanupPostBorrowck.before/after`, `runtime-optimized.after`.
- **Group B (`b_cell_interior_mutability_ref_within_guard_and_or_patterns` — 5 probes):**
  - `mut_scrutinee_write_to_ref_mut_binding_in_guard_rejected_e0594`: `compile_rc=1`, `error[E0594]: cannot assign to *v, as it is immutable for the pattern guard`.
  - `mut_by_val_binding_write_in_guard_rejected_e0594`: `compile_rc=1`, `error[E0594]: cannot assign to v, as it is immutable for the pattern guard`.
  - `cell_interior_mut_and_mut_arm_body_ok`: `compile_rc=0`, `run_rc=0`, stdout: `CELL_GUARD_VAL=17 INTERIOR_REF_VAL=17 MUT_BODY_OK=99`.
  - `cell_interior_mut_fallthrough_observed`: `compile_rc=0`, `run_rc=0`, stdout: `INTERIOR_MUT_ACROSS_FALLTHROUGH=17`.
  - `or_pattern_guard_per_subbranch_and_move_after_ref_within_guard`: `compile_rc=0`, `run_rc=0`, stdout: `OR_CHECKS_ONCE=1 OR_MOVE_OUT=hi OR_SUBBRANCH_CHECKS=2 PICKED=2 SHORT_CHECKS=1 SHORT_VAL=10 MISS_CHECKS=2 MISS_VAL=99 RES=ok`.

### 3. Lean `v4.34.1` Kernel Verification and MetaM Purity Receipts (`support/MatchGuardFakeBorrowAndOrPatternSoundness.lean`)

- **Source Metrics:** `2,832` lines (`113,432` bytes), `prelude` + `Init.*` imports only, zero `noncomputable section`, zero `deriving`, zero `partial`, zero `._unsafe_rec`, zero `Classical.choice`, zero `sorry`, zero `omega`, zero `bv_decide`, zero `native_decide`.
- **Standalone Kernel Check:** Compiled cleanly (`exit 0`) with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`leanprover/lean4:v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`).
- **MetaM Constant & Axiom Enumeration:** Every constant under `Anneal.MatchGuardSoundness.*` inspected via `Lean.collectAxioms` and `ConstantInfo` inspection reported:
  `AUDIT_SUMMARY total=953 theorems=346 defs=506 unsafeRecs=0 unsafeConsts=0 bannedAxioms=0 allAxioms=[Quot.sound, propext]`.

### 4. Support Artifacts Bundled in Package

- `support/probe_match_guard_fake_borrow.py` (`506` lines) — self-contained live `rustc` empirical harness using isolated temporary directories and path sanitization.
- `support/probe_results.json` (`88,812` bytes) — full recorded outputs, compiler errors, execution stdout, and MIR dumps across all 20 probes.
- `support/MatchGuardFakeBorrowAndOrPatternSoundness.lean` (`2,832` lines) — self-contained Lean `v4.34.1` mechanization of Parts I–IV.

---

## Revalidation

1. **Rerun Live `rustc` Diagnostic, Binary, and MIR-Dump Probes (Expected: `compile_rc`/`run_rc` match all 20 entries in `support/probe_results.json`):**
   ```bash
   rustc -Vv
   python3 support/probe_match_guard_fake_borrow.py
   ```
   Verify that `compile_returncode`, first diagnostic lines (`E0510`/`E0506`/`E0502`/`E0594`), `Box` vs. `Vec` `deref!` MIR fake borrows (`&fake shallow (*_1)` vs. `&fake _1`), and stdout tokens (`CELL_GUARD_VAL=17`, `INTERIOR_MUT_ACROSS_FALLTHROUGH=17`, `OR_CHECKS_ONCE=1`, `OR_SUBBRANCH_CHECKS=2`, `SHORT_CHECKS=1`, `MISS_CHECKS=2`) remain invariant, noting any compiler commit drift relative to `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

2. **Re-Verify Lean `v4.34.1` Kernel Proofs and Zero-Axiom Purity:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MatchGuardFakeBorrowAndOrPatternSoundness.lean
   ```
   To re-audit every declaration in `Anneal.MatchGuardSoundness.*` programmatically with Lean MetaM outside the package directory:
   ```bash
   mkdir -p /tmp/reval_lean
   lean -R support -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     -o /tmp/reval_lean/MatchGuardFakeBorrowAndOrPatternSoundness.olean \
     support/MatchGuardFakeBorrowAndOrPatternSoundness.lean
   ```
   Then run an audit script importing `MatchGuardFakeBorrowAndOrPatternSoundness` (`LEAN_PATH=/tmp/reval_lean`) checking `Lean.collectAxioms` (`⊆ [Quot.sound, propext]`), `ConstantInfo` safety (`0` unsafe/partial/opaque/axiom), and `0` `_unsafe_rec` names, and remove `/tmp/reval_lean` afterward.

3. **Check Upstream `rust-lang/rust` Regions for Behavioral Drift:**
   Diff the following pinned paths against newer `rust-lang/rust` commits:
   - `compiler/rustc_mir_build/src/builder/matches/util.rs` (`FakeBorrowCollector`, `collect_fake_borrows`)
   - `compiler/rustc_mir_build/src/builder/matches/mod.rs` (`bind_pattern`, `bind_and_guard_matched_candidate`, `bind_matched_candidate_for_guard`, `declare_binding`)
   - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs` (`CleanupPostBorrowck::run_pass`)
   - `compiler/rustc_borrowck/src/places_conflict.rs` (`borrow_conflicts_with_place` shallow prefix check)
   - `compiler/rustc_borrowck/src/diagnostics/conflict_errors.rs` & `mutability_errors.rs` (`report_illegal_mutation_of_borrowed`, `classify_immutable_section`, `is_ref_for_guard`)

4. **Validate Corpus Catalog and Package Schema (`reference-corpus/1`):**
   ```bash
   python3 tools/reference.py catalog
   python3 tools/reference.py check
   ```
