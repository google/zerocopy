<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Three-Stage MIR Verification Pipeline: Place Initialization, Post-Monomorphization Completeness, Assert Semantics, and TCB Refinement Architecture

## Summary

Anneal verifies Rust crates across a three-stage pipeline (`docs/architecture.md:102-146`
at `d79b0c070cf4115b523fe6ee62c1e72504de2254`):

1. **Stage 1 (`trusted/rustc-capture`)** intercepts `rustc`'s
   `mir_drops_elaborated_and_const_checked` query (`Runtime(PostCleanup)` MIR)
   and emits a pure Lean 4 crate AST (`Mir.lean`), specification stubs
   (`Spec.lean`), and top-level theorem target (`Theorem.lean`).
2. **Stage 2 (`trusted/lean/Trusted/`)** defines the Trusted Computing Base
   (TCB) MIR syntax (`MirAst.lean`), small-step operational semantics and
   post-monomorphization checks (`MirSemantics.lean`), step-indexed trace
   refinement (`StepResult.lean`), and abstract `Language`/`Tool` verification
   interfaces (`Refinement.lean`), audited at the `.olean` kernel level by
   `trusted/audit/TrustedBoundary.lean` and `trusted/audit/src/lib.rs`.
3. **Stage 3 (`theory/Anneal/`)** proves verified semantic lemmas, Stage 3 IR
   simplifications, and `decide`-driven bounded symbolic execution in
   `theory/Anneal/MirLemmas.lean` outside the TCB.

Cross-checking the Stage 1 extractor (`trusted/rustc-capture/src/`), Stage 2
semantics (`trusted/lean/Trusted/`), `.olean` boundary auditor
(`trusted/audit/`), and Stage 3 proof engine (`theory/Anneal/`) against `rustc`
(`1.96.0-nightly` and `1.98.0-nightly`) and Lean 4 (`v4.28.0` and `v4.34.1`)
establishes five load-bearing soundness and architectural results:

- **F-01 (Partial Moves and Path-Sensitive `.uninit`):** Translating projected
  moves (`Operand::Move(_1.0)`) to a non-destructive `Rvalue.field0` read
  (`trusted/rustc-capture/src/extract.rs:472-485`,
  `trusted/lean/Trusted/MirSemantics.lean:589-597`) is unsound when
  `StorageDead(_1)` is absent or deferred on non-`Copy` types, allowing a moved
  field or whole aggregate to be read a second time. Conversely, resetting the
  entire root local `_1` to `none` breaks valid Rust programs that subsequently
  move or read sibling fields (`_1.1`). Representing places compositionally as
  `(LocalId, List PlaceElem)` with a leaf `MirVal.uninit` constructor written back
  at the moved projection path—gated by recursive `isFullyInitFuel` checks on
  (a) terminal whole-value reads (`proj = []`), (b) intermediate `.deref` hops,
  and (c) terminal reference creation (`Rvalue.ref`)—restores exact
  field-granularity initialization soundness.
- **F-02 (`StatementKind::PlaceMention` Erasure and `-Z mir-preserve-ub`):**
  Under default compiler flags, `rustc`'s `RemovePlaceMention` pass
  (`3-1-002.RemovePlaceMention`) erases `PlaceMention((*_1))` before
  `3-2-000.runtime-post-cleanup` (`mir_drops_elaborated_and_const_checked`),
  causing `unsafe { let _ = *dangling_ptr; }` and `let _ = partially_moved;` to
  vanish before Stage 1 capture (`extract.rs:529-549`). Passing
  `-Z mir-preserve-ub` retains `StatementKind::PlaceMention` in
  `Runtime(PostCleanup)` MIR, and evaluating `Stmt.placeMention p` via
  `evalPlaceRead` (including `isFullyInitFuel`) rejects invalid dereferences and
  uninitialized places.
- **F-03 (Post-Monomorphization Error Completeness via Two-Stage `ConstsTotal`
  and `MonoAdmitted`):** Syntactically dead generic branches such as
  `if false { let _ = Fail::<T>::C; }` are never reached by dynamic execution of
  `basic_blocks` (and are erased from `basic_blocks` in `Runtime(Optimized)` by
  `SimplifyConstCondition` + `SimplifyLocals`), yet `rustc` records
  `Fail::<T>::C` in `Body::required_consts` (and `Body::mentioned_items` for
  functions, drops, and closures in `optimized_mir`) and rejects
  `dead_branch_pme::<u8>()` during monomorphization with `error[E0080]`.
  Single-quantifier PME predicates either lock out valid compile-time guards
  (`const { assert!(size_of::<T>() == 8); }`, as in
  `theory/Anneal/MirLemmas.lean:3726-3730`) if they require `ConstSucceeds` over
  all `ValidTySizes`, or fail open vacuously if `evalTyByteSize ... = some sz`
  is placed on the left-hand side of an implication on `.unsupported` or
  oversized types. A two-stage predicate—`ConstsTotal` requiring positive type
  sizing (`∃ sz`) and `ConstSucceeds ∨ ConstUnwinds` over all `ValidTySizes`
  (`≤ maxTypeSize`), paired with `MonoAdmitted` requiring `ConstSucceeds` and
  valid mentioned-type layouts at the active `s.tySizes` in `initMirState`—is
  both sound and non-vacuous.
- **F-04 (Compiler-Inserted `TerminatorKind::Assert` vs. `core::panicking::panic`
  and Multi-Config `CONFIGS`):** `rustc` lowers checked integer arithmetic
  (`+`, `-`, `*`), division/remainder (`/`, `%`), and bounds checks to
  `TerminatorKind::Assert`, whereas user `assert!(...)` and
  `const { assert!(...) }` lower to `SwitchInt` + `TerminatorKind::Call` to
  `core::panicking::panic`. Because `PrefixOutcome.isSafe`
  (`trusted/lean/Trusted/StepResult.lean:59-63`) treats `.terminated .unwind` as
  safe and `EnsuresRetLibInv` (`MirSemantics.lean:1011-1015`) only constrains
  normal returns, stepping `Terminator.assert` failure to `.unwind` makes
  `bad_overflow(x: u8)` (`let y = x + 1; if y == 0 { unsafe { unreachable_unchecked() } }`)
  verify as safe under `-C overflow-checks=on` (`x = 255` unwinds) while
  executing `unreachable` Undefined Behavior (`.failed`) in `--release`
  (`-C overflow-checks=off`, where `255 + 1` wraps to `0`). `Terminator.assert`
  failure must therefore step to `.failed`, `CONFIGS`
  (`trusted/rustc-capture/src/main.rs:325-328`) must hold `-C overflow-checks=on`
  and `-Z mir-preserve-ub` invariant across `-C debug-assertions=on/off`, and
  emitted `BodyId`/`AdtId`/`SpanId` indices must be assigned by deterministic
  reachability order rather than raw `LocalDefId::local_def_index` (which shifts
  when `#[cfg(debug_assertions)]` items are present).
- **F-05 (Flat `BodyId` Tables, `.olean` Boundary Constraints, Frame-Relative
  `returnRefsOk`, and In-Place Stage 3 `lowerBody`):** Embedding `MirBody` by
  value inside `Terminator.call1` (`trusted/lean/Trusted/MirAst.lean:193-235`)
  forces a `mutual inductive` block whose structural recursion cannot be
  elaborated in `SourceRole.trusted` without `.olean`-forbidden `._unsafe_rec`
  or `WellFounded.fix` (`trusted/audit/TrustedBoundary.lean:208-239, 644-665`),
  compelling Stage 3 (`theory/Anneal/MirLemmas.lean:305-308, 3549-3560`) to use
  manual `@Terminator.casesOn` and fuel-bounded `beqMirBodyFuel 8`. Replacing
  inline `MirBody` trees with a flat `BodyId`-indexed `BodyDecl` table,
  replacing five dummy `opaque Target*` declarations
  (`MirSemantics.lean:1045-1108`) with `Obligation.assumed`, making
  `returnRefsOk` frame-relative (`s.frameId == 0` vs. `targetFrameId < s.frameId`),
  and canonicalizing PC coordinates in `MirReturn` enables in-place
  `BlockId`-preserving Stage 3 `lowerBody : MirBody → MirBody` simulation.

## Applicability

These findings apply to:

- **`joshlf/anneal` (`simplify-trusted` branch at commit
  `572f1e80580daa4b052ce5646bb675484d9bb957` and `main` branch architecture
  documentation at commit `d79b0c070cf4115b523fe6ee62c1e72504de2254`):**
  - Stage 1 extractor and emitter: `trusted/rustc-capture/src/{main.rs, hook.rs, extract.rs, items.rs, ir.rs, lean.rs, spec.rs}`.
  - Stage 2 TCB definitions: `trusted/lean/Trusted/{Refinement.lean, StepResult.lean, MirAst.lean, MirSemantics.lean}` and `trusted/lean/foundation-lock.json`.
  - `.olean` and workspace boundary auditor: `trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/{lib.rs, main.rs}`, and `trusted/cargo-anneal/src/lib.rs`.
  - Stage 3 proof library: `theory/Anneal/{Refinement.lean, StepResult.lean, MirLemmas.lean}`.
- **Rust compiler (`rust-lang/rust`):**
  - `rustc 1.96.0-nightly` (`+nightly-2026-03-19`, commit `fd0c901b00ee1e08a250039cdb90258603497e20`, LLVM 22.1.0).
  - `rustc 1.98.0-nightly` (`+nightly-2026-05-31`, commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, LLVM 22.1.6).
- **Lean 4 theorem prover (`leanprover/lean4`):**
  - `v4.28.0` (commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`, pinned in `joshlf/anneal/lean-toolchain`).
  - `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### F-01: Partial Moves Out of Composite Places (`Operand::Move(_1.0)`) and Path-Sensitive `MirVal.uninit`

`Basis: source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. In `trusted/rustc-capture/src/extract.rs:456-487`, `BodyCx::rvalue`
     translates `mir::Rvalue::Use(mir::Operand::Move(p), _)` when
     `!p.projection.is_empty()` and `p.projection == [ProjectionElem::Field(0, _)]`
     on a local struct to `ir::Rvalue::Field0(local_index(l))` (lines 472–485),
     identical to `Operand::Copy(_l.0)` (lines 458–471). In
     `trusted/lean/Trusted/MirSemantics.lean:589-597`, `evalMirStmt` evaluates
     `.assign dst (.field0 src)` as a non-destructive read that leaves
     `s.locals src.index` unchanged, whereas bare-local `evalOperand` on
     `.move src` (`MirSemantics.lean:501-506`) sets
     `updateLocal locals src.index none`.
  2. When a non-`Copy` aggregate field is moved (`let a = p.0;`), `rustc` emits
     `_2 = move (_1.0: NonCopy)` in `Runtime(PostCleanup)` MIR without emitting
     `StorageDead(_1)` until `_1` exits scope. Under the non-destructive
     `Rvalue.field0` semantics, a subsequent read or move of `_1.0` or of the
     whole struct `_1` succeeds (`nonDestructiveField0_allows_double_move`).
  3. Conversely, if `Operand::Move(p)` resets the entire root local `p.local` to
     `none`, moving `p.0` destroys sibling fields and causes valid Rust code
     `let a = p.0; let b = p.1;` (`partial_move_sibling`) to fail closed on
     `_3 = move (_1.1: NonCopy)` (`naiveRootReset_breaks_sibling_move`).
  4. Representing places compositionally as `Place = (LocalId, List PlaceElem)`
     (`PlaceElem := .deref | .field (idx : Nat)`), adding a leaf constructor
     `MirVal.uninit`, writing `MirVal.uninit` back to path `p` on
     `Operand.move p` via `updateProj`, and gating three operations with
     recursive `isFullyInitFuel` checks is both sound and complete for nested
     aggregates:
     - **Gate (a) — Terminal read (`proj = []` in `evalProjFuel`):** Rejects
       reading, moving, or place-mentioning `.uninit` or any `.adt`/`.tuple`
       containing `.uninit` at any nested leaf, while allowing `.field idx`
       steps to project initialized sibling fields out of partially moved
       aggregates (`pathSensitive_allows_sibling_field_move`,
       `pathSensitive_rejects_removed_field`,
       `pathSensitive_rejects_whole_aggregate_read`).
     - **Gate (b) — Intermediate dereference (`.deref :: rest` in
       `evalProjFuel` and `resolveRefTargetFuel`):** Evaluates `evalProjFuel` on
       the dereferenced target path `target.proj` (enforcing `isFullyInitFuel`
       on the referent value) before projecting `rest`, rather than
       concatenating `target.proj ++ rest`. Without Gate (b), if `r = &_1` is
       created while `_1` is fully initialized and `_1.0` is later moved,
       projecting `(*r).1` via path concatenation unsoundly reads sibling field
       `1` through an invalidated whole-struct reference
       (`pathSensitive_rejects_deref_projection_through_partially_moved_struct`).
     - **Gate (c) — Terminal reference creation (`proj = []` in
       `resolveRefTargetFuel` for `Rvalue.ref`):** Enforces `isFullyInitFuel` on
       the target value at `p` so borrowing `&_1` of a partially moved struct
       fails closed while borrowing an initialized sibling field `&(_1.1)`
       succeeds (`pathSensitive_rejects_whole_aggregate_ref_but_allows_sibling_ref`).
- **Evidence:**
  - `joshlf/anneal` (`572f1e80580daa4b052ce5646bb675484d9bb957`):
    `trusted/rustc-capture/src/extract.rs:437-516` (`BodyCx::operand`,
    `BodyCx::rvalue`), `trusted/lean/Trusted/MirAst.lean:64-131` (`Operand`,
    `Rvalue`), and `trusted/lean/Trusted/MirSemantics.lean:501-508, 589-605`
    (`evalOperand`, `evalMirStmt`).
  - Empirical `rustc` MIR capture in
    [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs)
    (lines 27–34, `partial_move_sibling`) and
    [support/mir_subtleties_output.json](support/mir_subtleties_output.json)
    (lines 18–26 and 199–207): across both `rustc 1.96.0-nightly` and
    `rustc 1.98.0-nightly`, `3-2-000.runtime-post-cleanup.after.mir` emits
    `_2 = move (_1.0: NonCopy);` followed by `_3 = move (_1.1: NonCopy);` with
    no `StorageDead(_1)`.
  - Mechanized Lean 4 proofs in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 35–286 (`nonDestructiveField0_allows_double_move`,
    `naiveRootReset_breaks_sibling_move`,
    `pathSensitive_allows_sibling_field_move`,
    `pathSensitive_rejects_removed_field`,
    `pathSensitive_rejects_whole_aggregate_read`,
    `pathSensitive_rejects_whole_aggregate_ref_but_allows_sibling_ref`,
    `pathSensitive_rejects_deref_projection_through_partially_moved_struct`).

---

### F-02: `StatementKind::PlaceMention` Erasure in `Runtime(PostCleanup)` and Retention via `-Z mir-preserve-ub`

`Basis: source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. In `trusted/rustc-capture/src/extract.rs:529-549`, `BodyCx::stmt` rejects
     `mir::StatementKind::PlaceMention`, assuming that runtime cleanup passes
     have removed it alongside `FakeRead` and `AscribeUserType`.
  2. In `rustc` (`1.96.0-nightly` and `1.98.0-nightly`), place-mention bindings
     such as `unsafe { let _ = *p; }` (`place_mention_raw_ptr`) lower to
     `PlaceMention((*_1));` in `1-1-000.built.after.mir`. Under default flags,
     pass `3-1-002.RemovePlaceMention` erases `PlaceMention((*_1));` before
     `3-2-000.runtime-post-cleanup.after.mir`
     (`mir_drops_elaborated_and_const_checked`), leaving only `_0 = const (); return;`.
     Consequently, dereferencing a null or dangling pointer or mentioning a
     partially moved aggregate in `let _ = ...;` is erased before Stage 1
     inspects the `Runtime(PostCleanup)` body.
  3. Passing `-Z mir-preserve-ub` to `rustc` disables `RemovePlaceMention`,
     preserving `PlaceMention((*_1));` in both
     `3-2-000.runtime-post-cleanup.after.mir` and
     `3-3-000.runtime-optimized.after.mir`.
  4. Translating `mir::StatementKind::PlaceMention(place)` to
     `Stmt.placeMention place` and evaluating it via `evalPlaceRead` (which
     traverses projections, resolves intermediate dereferences, and enforces
     `isFullyInitFuel`) steps valid initialized places to `s.nextStmt s.locals`
     and steps dangling dereferences or uninitialized/partially moved places to
     `.failed` (`placeMention_rejects_dangling_and_partially_moved`).
- **Evidence:**
  - `joshlf/anneal` (`572f1e80580daa4b052ce5646bb675484d9bb957`):
    `trusted/rustc-capture/src/extract.rs:529-549` (`BodyCx::stmt`).
  - Empirical `rustc` MIR pass dumps in
    [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs)
    (lines 36–44, `place_mention_raw_ptr`) and
    [support/mir_subtleties_output.json](support/mir_subtleties_output.json)
    (lines 27–55 and 208–236).
  - Mechanized Lean 4 proof in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 288–317 (`placeMention_rejects_dangling_and_partially_moved`).

---

### F-03: Post-Monomorphization Error (PME) Completeness Across `required_consts`, `mentioned_items`, and Two-Stage `ConstsTotal` / `MonoAdmitted`

`Basis: source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. In `rustc` (`1.96.0-nightly` and `1.98.0-nightly`), a constant referenced
     inside a syntactically dead branch (`if false { let _ = Fail::<T>::C; }` in
     `dead_branch_pme<T>`) is recorded in `Body::required_consts` during
     `1-1-008.PromoteTemps`. At `3-2-000.runtime-post-cleanup.after.mir`
     (`mir_drops_elaborated_and_const_checked`), `bb1` (`_3 = const Fail::<T>::C;`)
     is still present behind `_2 = const false; switchInt(move _2)`, while
     `Body::mentioned_items` is still `None` (`MentionedItems` runs in
     `optimized_mir` prior to `3-2-013.SimplifyConstCondition-after-inst-simplify`
     and `3-2-014.SimplifyLocals-before-const-prop`, which erase `bb1` from
     `3-3-000.runtime-optimized.after.mir`). When `dead_branch_pme::<u8>()` is
     monomorphized (`--emit=obj`), `rustc` evaluates `required_consts` and
     rejects the crate with `error[E0080]` (`evaluation of Fail::<u8>::C failed`).
     Conversely, code after an unconditional `return` (`return 0; let _ = Fail::<T>::C;`)
     is stripped by `1-1-006.SimplifyCfg-initial` before `PromoteTemps` and does
     not trigger `E0080`.
  2. Because dynamic execution of `dead_branch_pme` takes the `false` branch of
     `switchInt` and never reaches `bb1`, checking constants only when reached
     along dynamic execution traces misses PMEs in dead branches. Moreover, in
     `trusted/lean/Trusted/MirSemantics.lean:243` (`tySizeStep`), `.param idx => some (tySizes idx)`
     places no upper bound on `tySizes idx`, whereas `rustc` rejects any
     monomorphized type exceeding `isize::MAX` (`c.layout.maxTypeSize = 9223372036854775807`
     on 64-bit targets).
  3. Collapsing PME checking into a single quantifier exhibits two dual soundness/completeness hazards:
     - **Single-quantifier lockout (`SingleQuantifierStrictConstsTotal_locks_out_pme_guard`):**
       Requiring every reachable constant in `requiredConsts` / `mentionedItems`
       to evaluate to `ConstSucceeds` over *all* `ValidTySizes` makes
       `ConstsTotal` false whenever a generic function uses a compile-time PME
       guard (`const { assert!(core::mem::size_of::<T>() == 8); }`, as tested in
       `inlineConstPmeCrate` at `theory/Anneal/MirLemmas.lean:3726-3730`),
       because at `tySizes 0 = 1` the guard panics (`ConstUnwinds`). That empties
       `initMirState` and falsifies `NonVacuousOn`.
     - **Vacuous implication precondition (`ImplicationLHSConstsTotal_vacuous_on_unsupported_ty`):**
       Placing `mapOpt (evalTyByteSize c tySizes) typeArgs = some argSizes` on
       the left-hand side of an implication `→` makes `ConstsTotal` vacuously
       true whenever `typeArgs` contains `MirTy.unsupported` or a type whose size
       exceeds `maxTypeSize`, failing open even if the constant body triggers
       CTFE Undefined Behavior (`.failed`). Similarly, calling
       `instantiateBody c cid []` instead of `instantiateBody c cid typeArgs`
       fails the arity guard `body.typeParamCount == typeArgs.length` on generic
       constants.
  4. A **two-stage** PME predicate resolves both hazards (`twoStagePme_sound_and_nonvacuous`):
     - **Stage 1 (`ConstsTotal c b` across all `ValidTySizes c b.typeParamCount tySizes`):**
       Requires that no reachable body is `none` (`¬ ReachableBody c b none`) and
       that for every reachable required or mentioned constant `(cid, typeArgs)`,
       there *positively exist* (`∃ argSizes constBody`) evaluated byte sizes
       `mapOpt (evalTyByteSize c tySizes) typeArgs = some argSizes` and
       instantiated body `instantiateBody c cid typeArgs = some constBody` such
       that `ConstSucceeds c tySizes constBody ∨ ConstUnwinds c tySizes constBody`.
       This guarantees that no monomorphization ever triggers CTFE UB (`.failed`)
       or encounters an unmodeled type/body.
     - **Stage 2 (`MonoAdmitted c s.tySizes b` in `initMirState` at active `s.tySizes`):**
       Requires that every reachable `MentionedItem.tyLayout ty` has a valid
       layout (`∃ sz, evalTyByteSize c s.tySizes ty = some sz`) and every
       reachable required or mentioned constant satisfies
       `ConstSucceeds c s.tySizes constBody`. Including `MonoAdmitted` in
       `initMirState` gives runtime verification the exact hypothesis that
       compile-time `const { assert!(...) }` guards succeeded (e.g.,
       `s.tySizes 0 = 8`), while `NonVacuousOn` guarantees at least one admitted
       monomorphization exists.
- **Evidence:**
  - `joshlf/anneal` (`572f1e80580daa4b052ce5646bb675484d9bb957`):
    `trusted/rustc-capture/src/hook.rs:86-109`,
    `trusted/rustc-capture/src/extract.rs:196-203, 271-323`,
    `trusted/lean/Trusted/MirSemantics.lean:238-259, 895-983`, and
    `theory/Anneal/MirLemmas.lean:3721-3769` (`inlineConstPmeCrate`).
  - Empirical `rustc` MIR dumps and monomorphization probe in
    [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs)
    (lines 46–66, `Fail<T>::C`, `dead_branch_pme`) and
    [support/mir_subtleties_output.json](support/mir_subtleties_output.json)
    (lines 6–17 and 187–198).
  - Mechanized Lean 4 proofs in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 319–463 (`SingleQuantifierStrictConstsTotal_locks_out_pme_guard`,
    `ImplicationLHSConstsTotal_vacuous_on_unsupported_ty`,
    `twoStagePme_sound_and_nonvacuous`).

---

### F-04: Compiler-Inserted `TerminatorKind::Assert` vs. `core::panicking::panic` (`assert!`) and Multi-Config `CONFIGS` Equivalence

`Basis: source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. Across `rustc 1.96.0-nightly` and `rustc 1.98.0-nightly`, user-level
     `assert!(x > 0)` (`explicit_assert`) and `const { assert!(...) }`
     (`Fail<T>::C`) lower to `TerminatorKind::SwitchInt` branching on failure to
     `TerminatorKind::Call` invoking `core::panicking::panic` (`Known::Panic` in
     `trusted/rustc-capture/src/extract.rs:120-131, 677-679`), under all four
     `(debug-assertions=yes/no) × (overflow-checks=yes/no)` combinations. By
     contrast, `TerminatorKind::Assert` (`extract.rs:567-568`) is emitted for
     compiler-inserted safety/overflow checks: checked arithmetic
     (`AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow` when
     `-C overflow-checks=yes`), division/remainder by zero (`Div`, `Rem`), and
     bounds checks.
  2. In `trusted/lean/Trusted/StepResult.lean:59-63`, `PrefixOutcome.isSafe`
     defines `.terminated .unwind` as safe (`True`), and `EnsuresRetLibInv`
     (`trusted/lean/Trusted/MirSemantics.lean:1011-1015`) only constrains normal
     returns (`.terminated tr (.normal r)`). If `Terminator.assert` failure steps
     to `.terminated .unwind` (treating compiler-inserted `Assert` like user
     `panic!`), then on:
     ```rust
     pub fn bad_overflow(x: u8) -> u8 {
         let y = x + 1;
         if y == 0 {
             unsafe { core::hint::unreachable_unchecked() }
         }
         y
     }
     ```
     under `-C overflow-checks=yes` (debug mode), input `x = 255` sets the
     overflow flag in `AddWithOverflow(255, 1) = (0, true)` and steps via
     `Terminator.assert` to `.terminated .unwind` (`isSafe = True`), while all
     `x < 255` produce `y = x + 1 ≠ 0` and return normally. Thus `bad_overflow`
     verifies as sound (`naiveAssertUnwind_unsound_on_bad_overflow.1`)! Yet in
     `--release` (`-C overflow-checks=no`), `rustc` lowers `x + 1` to wrapping
     `BinOp::Add`, so `x = 255` wraps to `y = 0`, enters `if y == 0`, and
     executes `unreachable_unchecked()` (`.failed` — immediate Undefined
     Behavior, `naiveAssertUnwind_unsound_on_bad_overflow.2`).
  3. Stepping `Terminator.assert` failure to `.failed` (while keeping
     `Callee.panic` stepping to `.terminated .unwind`) rejects `bad_overflow` at
     `x = 255` in both debug and release modes and guarantees that any input
     proven free of `.failed` under `-C overflow-checks=yes` never overflows and
     therefore has identical semantics under `-C overflow-checks=no`
     (`fixedAssertFailed_sound_across_profiles`).
  4. In `trusted/rustc-capture/src/main.rs:325-328, 550-559`, `CONFIGS` runs
     `("debug", &["-Cdebug-assertions=on", "-Coverflow-checks=on"])` and
     `("release", &["-Cdebug-assertions=off", "-Coverflow-checks=off"])` and
     requires byte-for-byte identical `Mir.lean` output. Because `+`, `-`, and
     `*` lower to `AddWithOverflow` + `Assert` when `overflow-checks=on` and to
     `Add` without `Assert` when `overflow-checks=off`, varying `overflow-checks`
     in `CONFIGS` rejects every Rust function containing integer arithmetic!
     Holding `-C overflow-checks=on` and `-Z mir-preserve-ub` invariant across
     both `-C debug-assertions=on` and `-C debug-assertions=off` passes verifies
     both profiles when paired with `Terminator.assert` failure stepping to
     `.failed`.
  5. In `trusted/rustc-capture/src/hook.rs:86, 108` and `items.rs:193, 576`,
     items and bodies are indexed by raw `LocalDefId::local_def_index` (`DefIdx`).
     When a crate contains a `#[cfg(debug_assertions)]` item (`debug_only_helper`
     in `mir_subtleties_specimen.rs:68-71`), `rustc` includes it under
     `-C debug-assertions=yes` and omits it under `-C debug-assertions=no`,
     shifting `LocalDefId` indices of subsequent items. Assigning `BodyId`,
     `AdtId`, and `SpanId` sequentially by deterministic reachability order from
     root functions (keying the capture map by `DefPathHash`) makes emitted IDs
     invariant to unreferenced `#[cfg(debug_assertions)]` items.
- **Evidence:**
  - `joshlf/anneal` (`572f1e80580daa4b052ce5646bb675484d9bb957`):
    `trusted/rustc-capture/src/main.rs:325-328, 550-559`,
    `trusted/rustc-capture/src/hook.rs:86-109`,
    `trusted/rustc-capture/src/extract.rs:120-131, 567-568, 677-679`,
    `trusted/lean/Trusted/StepResult.lean:59-63`, and
    `trusted/lean/Trusted/MirSemantics.lean:1011-1015`.
  - Empirical `rustc` profile matrix in
    [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs)
    (lines 68–99) and
    [support/mir_subtleties_output.json](support/mir_subtleties_output.json)
    (lines 56–176 and 237–357).
  - Mechanized Lean 4 proofs in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 465–547 (`naiveAssertUnwind_unsound_on_bad_overflow`,
    `fixedAssertFailed_sound_across_profiles`).

---

### F-05: Lean 4 TCB AST Structure, `.olean` Boundary Auditing (`TrustedBoundary.lean`), Frame-Relative `returnRefsOk`, and In-Place Stage 3 Lowering (`lowerBody`)

`Basis: documentation + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. **Eliminating `mutual inductive` `MirBody` via Flat `BodyId` Tables:**
     In `trusted/lean/Trusted/MirAst.lean:193-235`, `Terminator`, `BasicBlock`,
     and `MirBody` form a `mutual inductive ... structure` block because
     `Terminator.call1` embeds `(callee : MirBody)` by value (line 214) and
     `MirBody.requiredConsts` embeds `List (MirBody × List MirTy)` (line 234).
     In `trusted/audit/TrustedBoundary.lean:208-239, 314-321, 644-665`,
     `SourceRole.trusted` modules (`trusted/lean/`) are restricted to
     `allowedTrustedSyntaxKinds` (forbidding `byTactic`, `partial`, `unsafe`,
     and `termination_by`/`decreasing_by`) and Phase 2 `.olean` auditing rejects
     any constant with `isUnsafe` (`._unsafe_rec`) or `isPartial`, as well as
     any reference to `WellFounded.fix`. Because Lean 4's structural recursion
     elaborator cannot reduce nested/mutual recursion over `MirBody` without
     `WellFounded.fix` or `._unsafe_rec`, Stage 3 (`theory/Anneal/MirLemmas.lean`)
     cannot derive `BEq MirBody` or use standard `match` in total recursive
     functions over `MirBody`, forcing manual `@Terminator.casesOn` recursors
     (`MirLemmas.lean:305-308`) and a fuel-bounded equality `beqMirBodyFuel 8`
     (`MirLemmas.lean:3549-3560`) that silently returns `false` on call chains
     deeper than 8. Replacing inline `MirBody` trees with a flat `BodyId`-indexed
     table `Crate.bodies : List BodyDecl` (where `BodyDecl` orthogonally pairs
     `payload : BodyPayload` with `contract : Option FnContract`) makes
     `Terminator` and `MirBody` non-recursive (`flatBody_decidableEq_refl`).
  2. **Replacing 5 Dummy `opaque Target*` Declarations with `Obligation.assumed`:**
     In `trusted/lean/Trusted/MirSemantics.lean:1045-1108`, five declarations
     (`TargetArtifact`, `rustc`, `opaque TargetSem`, `TargetLang`, `rustcCodec`)
     exist solely to construct an unprovable `Obligation.compiles` for
     `TCBItem.rustcLowering` (`MirSemantics.lean:1134-1135`). Defining
     `def Obligation.assumed {Id : Type} (id : Id) : Obligation Id := ⟨id, False⟩`
     in `Trusted/Refinement.lean` expresses unprovable, waiver-gated obligations
     (`rustcLowering`, `assumedContract`, `unverifiedFn`) in 2 lines with zero
     `opaque` symbols.
  3. **`foundation-lock.json` and `TrustedBoundary.lean` Syntax Allowlist
     Constraints:**
     `trusted/lean/foundation-lock.json` locks only the 38 `Init.*` modules
     transitively imported by `Init.NotationExtra` and `Init.Core` (including
     `Init.Data.String.Bootstrap` rather than `Init.Data.String.Basic`, and
     `Init.Data.Int.Basic` without `Init.Data.Int.Order`). In addition,
     `TrustedBoundary.allowedNotationSyntaxKinds`
     (`TrustedBoundary.lean:274-280`) permits only `+`, `-`, `*`, `/`, `%`, `<`,
     `≤`, `>`, `≥`, `=`, `≠`, `==`, `!=`, `&&`, `||`, `!`, `++`, `::`, `∧`, `∨`,
     `¬`, `↔`, and `∈`, rejecting unary negation (`` `«term-_» ``),
     exponentiation (`` `«term_^_» ``), and `∉` (`` `«term_∉_» ``) in
     `SourceRole.trusted` and `SourceRole.spec` files (requiring `Nat.pow`,
     `Int.negOfNat`, and `¬ (... ∈ ...)`).
  4. **Frame-Relative `returnRefsOk` (`Bool`):**
     In `trusted/lean/Trusted/MirSemantics.lean:307-326`, `MirVal.returnRefsOk`
     checks whether references inside a return value outlive the returning stack
     frame. Returning `Bool` (rather than `Prop`) allows `evalMirTerminator` to
     branch via `if ... then` without `Decidable` instances or tactics inside
     `SourceRole.trusted`. Furthermore, the survival check must be
     frame-relative (`returnRefsOk_frame_relative_correctness`): at the root
     frame (`s.frameId == 0`), a returned reference must target frame `0` at a
     caller-owned slot (`localCount ≤ targetLocalIdx`), whereas at an inline
     callee frame (`s.frameId > 0`), any reference targeting a strictly older
     caller frame (`targetFrameId < s.frameId`) survives callee exit even when
     `targetLocalIdx < calleeBody.localCount`.
  5. **In-Place Stage 3 Lowering (`lowerBody : MirBody → MirBody`) and
     PC-Canonicalized `MirReturn`:**
     In `docs/architecture.md:133-146` (`d79b0c070cf4115b523fe6ee62c1e72504de2254`),
     Stage 3 (`theory/`) simplifies Stage 2 MIR before symbolic evaluation.
     Stripping `Stmt.storageLive` or `Stmt.storageDead` during Stage 3 lowering
     is unsound because `evalMirStmt` (`MirSemantics.lean:633-638`) increments
     `s.localGens` via `bumpGen` to invalidate dangling references to dead stack
     locals. Even for pure no-op stripping (`Stmt.nop`), root
     `Terminator.return_` in `MirSemantics.lean:744` returns
     `.terminated (.normal ⟨retVal, s⟩)` carrying the full `MirState` `s`
     (including `s.block` and `s.stmtIdx`). Stripping `Stmt.nop` changes
     `s.stmtIdx` at `return_` (`rawReturn_distinguishes_nop_stripping`),
     falsifying `ExecNormal c (lowerBody b) s P → ExecNormal c b s P` for
     general postconditions `P : MirReturn → Prop` unless root
     `Terminator.return_` canonicalizes PC coordinates (`block := 0, stmtIdx := 0`
     or `pc := .terminated .normal`) in `MirReturn.state` and `lowerBody` updates
     blocks in place (`lowerBody_preserves_block_count`,
     `canonicalReturn_preserves_lowerBlock`).
- **Evidence:**
  - `joshlf/anneal` (`572f1e80580daa4b052ce5646bb675484d9bb957`):
    `trusted/lean/Trusted/MirAst.lean:193-282`,
    `trusted/lean/Trusted/MirSemantics.lean:307-326, 633-638, 740-750, 1045-1150`,
    `trusted/lean/foundation-lock.json:1-800`,
    `trusted/audit/TrustedBoundary.lean:208-321, 644-665`, and
    `theory/Anneal/MirLemmas.lean:305-308, 3549-3560`.
  - `joshlf/anneal` (`d79b0c070cf4115b523fe6ee62c1e72504de2254`):
    `docs/architecture.md:102-146`.
  - Mechanized Lean 4 proofs in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 549–695 (`returnRefsOk_frame_relative_correctness`,
    `flatBody_decidableEq_refl`, `lowerBody_preserves_block_count`,
    `rawReturn_distinguishes_nop_stripping`,
    `canonicalReturn_preserves_lowerBlock`).

## Boundaries

- **Raw pointer provenance, byte-level representation, and Tree/Stacked Borrows (`not examined`):**
  Both the current `MirSemantics.lean` and the path-sensitive `Place` +
  `MirVal.uninit` model represent references symbolically as paths
  `(FrameId, LocalId, List PlaceElem)` with per-local generation counters
  (`localGens`) rather than a byte-addressed memory model with pointer
  provenance or aliasing trees. Reinterpreting casts, union field aliasing, and
  sub-scalar byte slices remain outside the modeled fragment.
- **Unwinding cleanup pads (`TerminatorKind::Resume`, `UnwindAction::Cleanup`) (`not examined`):**
  Stage 1 (`trusted/rustc-capture/src/extract.rs:584-592`) and Stage 2
  (`trusted/lean/Trusted/MirSemantics.lean`) model unwinding as a direct
  transition to `.terminated .unwind` without executing landing-pad drop glue
  blocks along the unwind path.
- **Full `rustc_private` query-hook behaviour on `Runtime(Optimized)` (`not examined`):**
  Stage 1 (`trusted/rustc-capture/src/hook.rs:86-109`) captures MIR from
  `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`). Extending
  the query hook to cross-check `optimized_mir` (`Runtime(Optimized)`) directly
  inside `rustc-capture` was probed via `rustc` MIR dumps but not integrated into
  `hook.rs`.

## Evidence

| Artifact / Source | Type | Role | Description |
| :--- | :--- | :--- | :--- |
| `joshlf/anneal` @ `572f1e80580daa4b052ce5646bb675484d9bb957` | Git commit | `source` | Primary Anneal repository checkout (`trusted/rustc-capture`, `trusted/lean`, `trusted/audit`, `trusted/cargo-anneal`, `theory/Anneal`). |
| `joshlf/anneal` @ `d79b0c070cf4115b523fe6ee62c1e72504de2254` | Git commit | `documentation` | Architecture specification (`docs/architecture.md:102-146`) defining the three-stage MIR pipeline. |
| [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs) | Rust source | `execution` | `#![no_std]` specimen exercising partial moves, `PlaceMention`, dead-branch PME constants, checked arithmetic `Assert` vs. `assert!` panic, and `#[cfg(debug_assertions)]` item shifts. |
| [support/probe_rustc_mir_subtleties.py](support/probe_rustc_mir_subtleties.py) | Python script | `execution` | Reproducible probe driver executing `rustc +nightly-2026-03-19` and `rustc +nightly-2026-05-31` across MIR phases and flag matrices. |
| [support/mir_subtleties_output.json](support/mir_subtleties_output.json) | JSON capture | `execution` | Golden output captured from `probe_rustc_mir_subtleties.py` across `rustc 1.96.0-nightly` (`fd0c901b00ee1e08a250039cdb90258603497e20`) and `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). |
| [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean) | Lean 4 source | `execution + derived` | Zero-`sorry`, zero-axiom mechanized proofs of Findings F-01 through F-05, verified under `leanprover/lean4:v4.28.0` and `leanprover/lean4:v4.34.1`. |

## Revalidation

To reproduce the `rustc` MIR phase and flag-matrix probe across
`nightly-2026-03-19` and `nightly-2026-05-31`:

```console
python3 support/probe_rustc_mir_subtleties.py
```

To recheck the mechanized Lean 4 proofs in `support/RefinementSoundnessProbes.lean`
under both `leanprover/lean4:v4.28.0` and `leanprover/lean4:v4.34.1`:

```console
elan run leanprover/lean4:v4.28.0 lean support/RefinementSoundnessProbes.lean
elan run leanprover/lean4:v4.34.1 lean support/RefinementSoundnessProbes.lean
```
