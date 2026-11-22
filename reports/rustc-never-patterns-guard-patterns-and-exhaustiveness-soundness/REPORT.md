# `rustc` Never Type Stabilization, Never Patterns, Guard Patterns, Postfix Match, and Pattern Exhaustiveness Soundness

## Summary

This report establishes primary-source, empirical (`rustc` + `Miri`), and kernel-checked (`Lean v4.34.1`) ground truth for how `rustc` checks pattern exhaustiveness and lowers uninhabited matches, bodiless never patterns (`#![feature(never_patterns)]`), sub-pattern guards (`#![feature(guard_patterns)]`), and postfix matches (`#![feature(postfix_match)]`) after the stabilization of the never type (`!` in Rust `1.100.0`), together with the exact operational and verification consequences for `Miri` and Anneal's `Trusted.MirAst` / `Trusted.MirSemantics` boundary.

Seven load-bearing invariants and discrepancies hold across the examined `rust-lang/rust` revisions (`1.98.0-nightly` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1.102.0-nightly` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `HEAD` at `01afe534803b93889b85f6028117251cfbd431da`):

1. **Stabilization split (`never_type` vs. pattern features):** `never_type` (tracking issue `#35121`) transitioned from `unstable` in `1.98.0-nightly` (`rustc_feature/src/unstable.rs:666`) to `accepted` since `"1.100.0"` in `1.102.0-nightly` and `HEAD` (`rustc_feature/src/accepted.rs:339`), where `#![feature(never_type)]` emits `#[warn(stable_features)]`. Stabilizing `!` does **not** stabilize `exhaustive_patterns` (`unstable`, `#51085`), `never_patterns` (`incomplete`, `#118155`), `guard_patterns` (`incomplete`, `#129967`), or `postfix_match` (`unstable`, `#121618`). Only `min_exhaustive_patterns` (`accepted` since `"1.82.0"`, `accepted.rs:320`) governs stable empty-arm omission.
2. **Module-scoped inhabitedness, privacy, and `PlaceValidity` govern empty-arm omission:** In `compiler/rustc_pattern_analysis/src/usefulness.rs:947-960`, `PlaceInfo::split_column_ctors` computes:
   ```rust
   let is_toplevel_exception =
       self.is_scrutinee && matches!(ctors_for_ty, ConstructorSet::NoConstructors);
   let can_omit_empty_arms = self.validity.is_known_valid()
       || is_toplevel_exception
       || cx.is_exhaustive_patterns_feature_on();
   ```
   `MatchVisitor::is_known_valid_scrutinee` (`check_match.rs:290-365`) marks any dereference (`*p` or `*r`) or union field access as `PlaceValidity::MaybeInvalid`, and `PlaceValidity::specialize` (`usefulness.rs:901-917`) resets validity to `MaybeInvalid` whenever descending through `Constructor::Ref`, `Constructor::DerefPattern(_)`, or `Constructor::UnionField`. Consequently:
   - By-value `Result<u32, !>` (`ValidOnly`) permits omitting `Err(_)`.
   - Shared reference `&Result<u32, !>` crosses `Constructor::Ref` -> `MaybeInvalid` and `is_scrutinee = false`, so omitting `Err` is rejected with `E0004` (`&Err(!)` not covered) unless `#![feature(exhaustive_patterns)]` is enabled or an explicit `&Err(!),` / `&Err(_) => ...` arm is written.
   - Top-level `match *p {}` on `p: *const !` succeeds **only** because of `is_toplevel_exception` (`NoConstructors` on the top-level scrutinee), whereas `match *p {}` on `p: *const HasNever` (`pub struct HasNever(pub u32, pub !);`) is **rejected with `E0004`** because `ctors_for_ty` returns `ConstructorSet::Struct { empty: true }` rather than `NoConstructors`.
   - Private uninhabited struct fields (`PrivateUninhabitedField(true)` in `rustc.rs:248-256` -> `Constructor::PrivateUninhabited` in `usefulness.rs:933-936`) and foreign `#[non_exhaustive]` empty enums (`Constructor::NonExhaustive` in `rustc.rs:372-374`) prevent callers outside the defining module or crate from observing uninhabitedness.
3. **Bodiless `!` (`never_patterns`) AST-to-MIR pipeline and `RemoveZsts` pass interaction:** `rustc_ast_lowering/src/expr.rs:793-843` rejects arm bodies (`NeverPatternWithBody`) and arm guards (`NeverPatternWithGuard`) on never patterns while synthesizing a placeholder `loop {}` HIR body (which leaves dead locals `let mut _2: !; let mut _3: ();` in `-O0` MIR). `rustc_hir_typeck/src/pat.rs:587, 767` accepts `PatKind::Never` at any expected type and defers uninhabitedness validation to `check_never_pattern` (`check_match.rs:908-918`, rejecting `Some(!)` on `Option<u32>` with `NonEmptyNeverPattern`). During MIR building, `TestKind::Never` (`builder/matches/test.rs:317-329`) emits `FakeRead(ForMatchedPlace(None), place)` followed by `TerminatorKind::Unreachable`—enforcing initialization (`E0381`) and union-field unsafety (`E0133`), while carrying an explicit `// FIXME(never_patterns): Also assert validity of the data at place`. Post-borrowck, `CleanupPostBorrowck` (`cleanup_post_borrowck.rs:28-64`) erases `FakeRead`, `RemovePlaceMention` (`remove_place_mention.rs:13`) erases `PlaceMention` unless `-Zmir-preserve-ub` is active, and **`RemoveZsts` (`remove_zsts.rs:13, 124, 143-148`) erases indirect ZST `PlaceMention((*_1))` at `-Zmir-opt-level >= 1` even when `-Zmir-preserve-ub` is set**.
4. **Three-way operational split in `Miri` (null `*const !`, rogue tagged enums, and product types):**
   - On `p: *const ! = core::ptr::null()`: wildcard `match *p { _ => 99 }` lowers to `PlaceMention((*_1)); _0 = const 99_u32; return;` and **succeeds with `99` (`rc=0`)** because `InterpCx::deref_pointer` (`place.rs:468-536`) skips null, alignment, dereferenceability, and pointee-inhabitedness checks for sized raw pointers. By contrast, **both** `match *p {}` and `match *p { ! }` lower to `bb0: { PlaceMention((*_1)); unreachable; }` (at `-O0 -Zmir-preserve-ub`, or `bb0: { unreachable; }` after `RemovePlaceMention`) and **fault immediately in `Miri` with `Undefined Behavior: entering unreachable code`** (`step.rs:704`).
   - On an aligned buffer holding tag byte `1` interpreted as `#[repr(C, u8)] enum Tagged { Ok(u32) = 0, Err(!) = 1 }`: creating `&Tagged` succeeds (shallow reference validity sees `Tagged` as inhabited), and a top-level wildcard `match r { _ => 888 }` succeeds (`888`), whereas inspecting the discriminant via `Tagged::Err(_)`, `Tagged::Err(!)`, or omitted `Err` (`exhaustive_patterns`) faults immediately in `Miri` with **`Undefined Behavior: read discriminant of an uninhabited enum variant`** (`discriminant.rs:214-216`), **before** reaching any `unreachable` arm body.
   - On `#[repr(C)] struct HasNever(u32, !)` (a product type with no discriminant): behind `*const HasNever` pointing to `42u32`, `match *p { HasNever(n, _) => n }` **succeeds with `42` (`rc=0`)**, whereas `match *p { HasNever(_, !), }` **faults with `entering unreachable code` (`rc=1`)**; behind `&HasNever`, reference creation itself faults immediately in `Miri` (`validity.rs:700-707`: `encountered a reference pointing to uninhabited type HasNever`), exposing an explicit conservatism gap between `Miri`'s operational reference validity and `rustc_pattern_analysis`'s rule that `"references are always considered inhabited"` (`check_match.rs:1350`).
5. **Live `#![feature(guard_patterns)]` soundness and miscompilation defect (still unfixed in `HEAD`):** While traditional arm guards (`arm.guard.is_some()` -> `MatchArm { has_guard: true }` in `check_match.rs:512` -> `useful &= row.is_under_guard` in `usefulness.rs:1720`) are strictly opaque to exhaustiveness (`E0004` when `Some(_)` is uncovered), **`#![feature(guard_patterns)]` (`#129967`) is doubly broken identically in `1.98.0-nightly`, `1.102.0-nightly`, and `HEAD` (`01afe5348`)**:
   - `compiler/rustc_pattern_analysis/src/rustc.rs:471-472` lowers `PatKind::Guard { subpattern: subpat, .. } => return self.lower_pat(subpat)` without setting `is_under_guard` or emitting an opaque constructor, falsely declaring `Some(n if n > 0)` exhaustive over all `Some(_)` and emitting a false `#[warn(unreachable_patterns)]` on a following `Some(_)` arm.
   - `compiler/rustc_mir_build/src/builder/matches/match_pair.rs:457-460` still lowers `PatKind::Guard { .. }` to an empty `InterPatKind::Irrefutable { subpats: vec![], binding: None }` stub (`// FIXME(guard_patterns)`), silently discarding **both** the guard condition and all sub-pattern bindings. Empirically, `classify_subpat_guard(Some(-5))` returns **`"pos"`**, and omitting the fallback arm produces **zero `E0004`** and instead fails borrowck with `E0381: used binding 'n' isn't initialized`.
6. **`#![feature(postfix_match)]` temporary drop-scope equivalence:** `rustc_ast_lowering/src/expr.rs:351-358` lowers `MatchKind::Postfix` directly to `hir::ExprKind::Match(scrutinee, arms, hir::MatchSource::Postfix)`, and `rustc_hir_analysis/src/check/region.rs:657-661` ignores the `MatchSource` field when constructing drop and temporary scopes (`hir::ExprKind::Match(_, arms, _)`). Across both Edition 2021 and Edition 2024, postfix `expr.match { ... }` and prefix `match expr { ... }` produce the exact same execution trace `RES=15 LOG=["make", "arm_body", "drop_inner", "after_match"]` (scrutinee temporary dropped after arm body completes, before code following the `match` statement).
7. **Anneal trusted-boundary alignment and kernel-checked Lean `v4.34.1` formalization:** In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Trusted/MirAst.lean` models `MirTy.never` (`L296, 316`) and `TerminatorKind.unreachable` (`L776, 789`, evaluated to `.fault .undefined` in `Trusted/MirSemantics.lean:1551-1552`) while failing closed on `FakeRead` and `PlaceMention` (`L654-662`), and `BodyVerified` (`MirSemantics.lean:1730-1758`) conjoins unconditional `BodyStaticAdmitted` to close vacuity when `MirTy.never` parameters render `ValidEntryArgs` empty (`canaryNeverParamBody`, `L2513-2600`). The standalone Lean `v4.34.1` mechanization (`support/NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean`, `2,570` lines, `86` top-level `theorem` declarations, `914` kernel constants, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`/`unsafe`, **`0` `._unsafe_rec` helpers**, axioms strictly within `{propext, Quot.sound}`) proves `exhaustiveMatrix_every_valid_value_matched_or_never_read`, `guardPattern_must_stay_opaque_for_exhaustiveness`, `threeWay_null_raw_never_split`, `postfixMatch_temp_drop_order_eq_prefix`, `anneal_never_param_vacuity_requires_static_admission`, and six constructive sharpness counterexamples (`ce1`–`ce6`).

---

## Applicability

### Subject Relationships

The six durable subjects recorded in `REPORT.json` form a cross-checked primary-source, execution, specification, and mechanization matrix:

| Subject | Repository & Immutable Revision | Role in This Report |
| :--- | :--- | :--- |
| **`rustc 1.98.0-nightly` + `Miri`** | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`, LLVM `22.1.6`) | Primary live execution toolchain for all `16` compiler/MIR cases, `1` cross-crate `#[non_exhaustive]` case, and `13` `Miri` operational cases (`support/probe_never_patterns_postfix_match_and_exhaustiveness.json`), plus feature-gate source audit pre-`never_type` stabilization. |
| **`rustc 1.102.0-nightly` + `Miri`** | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`, LLVM `23.1.5`) | Post-`never_type` stabilization (`1.100.0`) source tree cross-checked against `1.98.0-nightly` and `HEAD`, and toolchain of the retained `7`-case compiler/MIR + `3`-case null-`*const !` `Miri` execution receipt cross-checked in §Findings and §Evidence. |
| **`rust-lang/rust` `HEAD`** | `rust-lang/rust` @ `01afe534803b93889b85f6028117251cfbd431da` (`2026-11-22`) | Latest upstream compiler source audited line-by-line across `rustc_feature`, `rustc_ast_lowering`, `rustc_hir_typeck`, `rustc_hir_analysis`, `rustc_pattern_analysis`, `rustc_mir_build`, `rustc_mir_transform`, and `rustc_const_eval`. |
| **Rust Reference** | `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`2026-11-17`) | Normative and descriptive specification baseline for `!` (`types/never.md`), UB and value validity (`behavior-considered-undefined.md`), `match` and guards (`expressions/match-expr.md`), patterns (`patterns.md`), and drop/temporary scopes (`destructors.md`). |
| **Anneal Trusted Boundary** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) | Downstream verified-MIR consumer whose `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `trusted/rustc-capture/src/driver.rs`, and `trusted/audit/TrustedBoundary.lean` define the MIR admission and Lean purity constraints evaluated here. |
| **Lean 4 `v4.34.1`** | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`2026-09-24`) | Kernel type-checker and environment inspector executing `support/check_lean.py` on `support/NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean` (`support/lean_check_receipt.json`). |

### Version Delta Matrix Across Examined `rust-lang/rust` Revisions

Direct programmatic comparison of the audited files across `14210df0e` (`1.98.0-nightly`), `3ef0c22cd` (`1.102.0-nightly`), and `01afe5348` (`HEAD`) separates shared invariants from version-specific changes:

| Subsystem / Behavior | `1.98.0-nightly` (`14210df0e`) | `1.102.0-nightly` (`3ef0c22cd`) | `HEAD` (`01afe5348`) | Status Across Revisions |
| :--- | :--- | :--- | :--- | :--- |
| `#![feature(never_type)]` (`#35121`) | `unstable` (`unstable.rs:666`); required for `!` in value/type positions (`Result<u32, !>`, `*const !`) | `accepted` since `"1.100.0"` (`accepted.rs:339`); attribute emits `#[warn(stable_features)]` | `accepted` since `"1.100.0"` (`accepted.rs:339`); attribute emits `#[warn(stable_features)]` | **Differs** (stabilized in `1.100.0`) |
| `min_exhaustive_patterns` (`#119612`) | `accepted` since `"1.82.0"` (`accepted.rs:320`) | `accepted` since `"1.82.0"` (`accepted.rs:320`) | `accepted` since `"1.82.0"` (`accepted.rs:320`) | **Shared** |
| `exhaustive_patterns` (`#51085`), `never_patterns` (`#118155`), `guard_patterns` (`#129967`), `postfix_match` (`#121618`) | All unstable (`never_patterns` and `guard_patterns` `incomplete`) | All unstable (identical gates) | All unstable (identical gates) | **Shared** |
| `rustc_pattern_analysis/src/usefulness.rs` (`PlaceValidity`, `split_column_ctors`, `is_toplevel_exception`, `can_omit_empty_arms`, `is_under_guard`) | Exact algorithm audited | Identical (`0` semantic diff vs. `HEAD`) | Identical (`0` semantic diff vs. `3ef0c22cd`) | **Shared** |
| `rustc_pattern_analysis/src/rustc.rs` | `PatKind::Guard => lower_pat(subpat)` (`L472`), `PrivateUninhabitedField` (`L255`) | Same; no `ty::View` arm | Adds 2 lines (`L436-437`: `ty::View(..) => unimplemented!()`); `PatKind::Guard` defect unchanged | **Shared** (additive `ty::View` stub only) |
| `rustc_mir_build/src/thir/pattern/check_match.rs` | `is_known_valid_scrutinee`, `check_never_pattern`, `"references are always considered inhabited"` | Same | Minor diagnostic metadata addition (`non_exhaustive_attr` span on `UNREACHABLE_PATTERNS` lint, `L986, 1043`); exhaustiveness/never-pattern logic unchanged | **Shared** (lint span metadata only) |
| `rustc_mir_build/src/builder/matches/{mod.rs, test.rs, match_pair.rs}` | `PatKind::Guard => Irrefutable { subpats: vec![], binding: None }`, `TestKind::Never => FakeRead + Unreachable` | Identical (`0` diff vs. `HEAD`) | Identical (`0` diff vs. `3ef0c22cd`) | **Shared** |
| `np_04` `NeverPatternWithBody` help wording | `help: remove this expression` (span on `0`) | `help: remove the match arm body, leaving only the pattern` (span on `=> 0`) | Same AST-lowering error (`NeverPatternWithBody`) | **Differs** (diagnostic help text only; error condition identical) |

### Invocation Profiles, Editions, and Scope Qualifications

- **Target and host:** All live `rustc`, native binary, and `Miri` executions ran on `x86_64-unknown-linux-gnu` (`pointerWidthBits = 64`). MIR dumps in `support/probe_never_patterns_postfix_match_and_exhaustiveness.json` record four distinct compilation profiles on `1.98.0-nightly`:
  1. Default `--emit=mir` (optimized MIR, `-Zmir-opt-level` default);
  2. Pass-by-pass `-Zdump-mir=all` (`built.after`, `CleanupPostBorrowck.after`, `RemovePlaceMention.after`);
  3. `--emit=mir -Zmir-opt-level=0 -Zmir-preserve-ub` (matching Miri's MIR ingestion profile);
  4. `--emit=mir -Zmir-opt-level=1 -Zmir-preserve-ub` (exposing `RemoveZsts` erasure of indirect ZST `PlaceMention`).
- **Editions:** Postfix and prefix `match` temporary-drop probes ran under both `--edition=2021` and `--edition=2024`; all other compiler/Miri probes ran under `--edition=2021` (with `np_06` also tested under `--edition=2024`).
- **Exact observation vs. broader applicability:** Findings on `rustc_pattern_analysis` and `rustc_mir_build` are established directly by primary-source inspection across all three `rust-lang/rust` revisions (`14210df0e`, `3ef0c22cd`, `01afe5348`) and by live execution on `1.98.0-nightly` cross-checked against the retained `1.102.0-nightly` receipt. Because `usefulness.rs` and `builder/matches/{mod.rs, test.rs, match_pair.rs}` are byte-identical between `3ef0c22cd` and `01afe5348`, the semantic findings generalize from `1.102.0-nightly` to `HEAD` (`01afe5348`) by source identity; however, no `01afe5348` binary was executed directly (see §Boundaries). Claims about Anneal's MIR semantics apply specifically to `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`mirProfileVersion = 1`, `pointerWidthBits = 64`), and claims about the Lean mechanization apply to the standalone model in `support/NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean` kernel-checked by `Lean v4.34.1`.

---

## Findings

### 1. Feature-Gate Timeline: Stabilized Never Type vs. Experimental Pattern Features

Basis: normative specification (`rust-lang/reference`) + source (`rust-lang/rust` `14210df0e`, `3ef0c22cd`, `01afe5348`) + execution (`1.98.0-nightly` and `1.102.0-nightly`).

In `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/types/never.md:4-59`), `!` is defined as the empty type with size `0`, alignment `1`, and universal coercion (`r[type.never.intro]`, `r[type.never.coercion]`, `r[type.never.layout]`), with `core::convert::Infallible` documented as a type alias for `!` (`L59`) and `Result<u32, !>` / `type Err = !;` shown in standard examples (`L25-43`).

In the compiler feature tables, however, `!` type syntax and the four pattern-matching/control-flow extensions evolve on independent tracks:

| Feature Gate | Tracking Issue | `1.98.0-nightly` (`14210df0e`) | `1.102.0-nightly` (`3ef0c22cd`) & `HEAD` (`01afe5348`) | Semantic Scope |
| :--- | :---: | :--- | :--- | :--- |
| `min_exhaustive_patterns` | `#119612` | `accepted`, `"1.82.0"` (`accepted.rs:320`) | `accepted`, `"1.82.0"` (`accepted.rs:320`) | Enables omitting uninhabited arms **only** when `PlaceValidity::ValidOnly` or `is_toplevel_exception` holds. |
| `never_type` | `#35121` | `unstable`, `"1.13.0"` (`unstable.rs:666`; comment: *"Does not imply `exhaustive_patterns` (below) any more."*) | `accepted`, `"1.100.0"` (`accepted.rs:339`) | Permits `!` as a general type (struct fields, enum payloads, type aliases, raw pointers, references); does **not** relax exhaustiveness behind references or raw pointers. |
| `exhaustive_patterns` | `#51085` | `unstable`, `"1.13.0"` (`unstable.rs:517`) | `unstable`, `"1.13.0"` (`unstable.rs:517`) | Forces `can_omit_empty_arms = true` even on `PlaceValidity::MaybeInvalid` places (e.g., omitting `Err` on `&Result<u32, !>` or `match *p {}` on `*const HasNever`). |
| `never_patterns` | `#118155` | `incomplete`, `"1.76.0"` (`unstable.rs:682`) | `incomplete`, `"1.76.0"` (`unstable.rs:682`) | Introduces bodiless, guardless `!` patterns (e.g., `Err(!),` or `&Err(!),`) representing an explicit uninhabited-place match arm. |
| `guard_patterns` | `#129967` | `incomplete`, `"1.85.0"` (`unstable.rs:591`) | `incomplete`, `"1.85.0"` (`unstable.rs:591`) | Syntax for sub-pattern guards (`Some(n if n > 0)`), currently broken in both exhaustiveness analysis and MIR building (§6). |
| `postfix_match` | `#121618` | `unstable`, `"1.79.0"` (`unstable.rs:702`) | `unstable`, `"1.79.0"` (`unstable.rs:702`) | Permits `scrutinee.match { ... }` syntax lowering to `hir::MatchSource::Postfix` (§7). |

Empirical differential evidence confirms the exact transition boundary:
- On `rustc 1.98.0-nightly` (`np_01_never_pattern_in_result_ok_and_err_never`), `#![feature(never_patterns, never_type)]` emits only `#[warn(incomplete_features)]` for `never_patterns` and executes to `UNWRAP=42`.
- On `rustc 1.102.0-nightly` (`3ef0c22cd`), the identical source emits **two** warnings: `#[warn(incomplete_features)]` for `never_patterns` **and** `warning: the feature 'never_type' has been stable since 1.100.0 and no longer requires an attribute to enable` (`#[warn(stable_features)]`), executing to the identical `UNWRAP=42`.
- On `rustc 1.98.0-nightly` (`np_01b_by_value_omit_err_min_exhaustive`), matching a by-value `Result<u32, core::convert::Infallible>` with only `Ok(v) => v` compiles with **zero** feature flags and **zero** warnings under `min_exhaustive_patterns` (`MIN_EXHAUSTIVE=42`).

---

### 2. Pattern-Analysis Inhabitedness, Module Privacy, and Cross-Crate Non-Exhaustiveness

Basis: source (`rust-lang/rust` `rustc_pattern_analysis/src/{rustc.rs, constructor.rs, usefulness.rs}`) + execution (`np_07d`, `foreign_non_exhaustive_empty_enum`) + derived (Lean `ce5`, `ce6`).

`rustc_pattern_analysis` does **not** equate pattern-exhaustiveness emptiness with global type-theoretic uninhabitedness. Instead, constructor visibility and uninhabitedness are strictly scoped to the match site's module and crate boundaries so that private fields and future `#[non_exhaustive]` variants cannot leak breaking API commitments.

#### Module-Scoped Inhabitedness (`RustcPatCtxt::is_uninhabited`)

In `compiler/rustc_pattern_analysis/src/rustc.rs:157-164` (identical in `3ef0c22cd` and `01afe5348`):

```rust
pub fn is_uninhabited(&self, ty: Ty<'tcx>) -> bool {
    !ty.inhabited_predicate(self.tcx).apply_revealing_opaque(
        self.tcx,
        self.typing_env,
        self.module,
        &self.reveal_opaque_ty,
    )
}
```

Evaluating `inhabited_predicate(self.tcx)` relative to `self.module` means that a struct `pub struct PrivEmpty { _priv: !, pub x: u8 }` is uninhabited **inside** its defining module (`inDefiningMod = true`) where `_priv` is accessible, yet treated as **inhabited** from outside (`inDefiningMod = false`) where `_priv` is inaccessible.

#### Private Uninhabited Fields (`PrivateUninhabitedField` -> `Constructor::PrivateUninhabited`)

When decomposing a struct constructor's field columns, `RustcPatCtxt::ctor_sub_tys` (`rustc.rs:230-256`) computes a per-field skip flag:

```rust
let is_visible = field.vis.is_accessible_from(self.module, self.tcx);
let is_uninhabited = self.is_uninhabited(ty.ty);
let skip = is_uninhabited && !is_visible;
(ty, PrivateUninhabitedField(skip))
```

When `PlaceInfo::split_column_ctors` (`usefulness.rs:924-936`) visits a column marked `self.is_private_uninhabited`:

```rust
if self.is_private_uninhabited {
    // Skip this column: private uninhabited fields must not be decomposed or witnessed.
    return Ok((smallvec![Constructor::PrivateUninhabited], vec![]));
}
```

Because `Constructor::PrivateUninhabited` has arity `0` and specializes every pattern (which typecheck already constrained to an implicit wildcard/rest pattern outside the defining module) to `[]`, the matrix checker drops that column instead of concluding the parent struct is empty.

Live execution (`np_07d_private_uninhabited_field_inside_vs_outside`) confirms this boundary:
- Inside `mod inner` (defining `pub struct PrivEmpty { _priv: !, pub x: u8 }`), `fn inside_ok(r: Result<u8, PrivEmpty>) -> u8 { match r { Ok(v) => v } }` compiles cleanly (`rc=0`).
- Outside `mod inner`, `fn outside_err(r: Result<u8, inner::PrivEmpty>) -> u8 { match r { Ok(v) => v } }` fails with **`error[E0004]: non-exhaustive patterns: 'Err(_)' not covered`** (`rc=1`), proving that private uninhabited fields cannot discharge match exhaustiveness across a module privacy boundary.

#### Foreign `#[non_exhaustive]` Empty Enums (`Constructor::NonExhaustive`)

In `compiler/rustc_pattern_analysis/src/rustc.rs:365-395`, `ctors_for_ty` inspects `ty::Adt(adt, args)` when `adt.is_enum()`:
- It computes `is_declared_nonexhaustive = self.is_foreign_non_exhaustive_enum(adt)` (true iff `adt` has `#[non_exhaustive]` and is defined in a **foreign** crate).
- Only when `adt.variants().is_empty() && !is_declared_nonexhaustive` does `ctors_for_ty` return `ConstructorSet::NoConstructors`.
- When `is_declared_nonexhaustive` is true, `ctors_for_ty` returns `ConstructorSet::Variants { variants, non_exhaustive: true }`, whose `split()` implementation (`constructor.rs:1126-1128`) always appends `Constructor::NonExhaustive` to the required constructor set (uncoverable except by a wildcard `_`).

Live cross-crate execution (`cross_crate_cases.foreign_non_exhaustive_empty_enum`) verifies this exact split:
- Crate `dep` defines `#[non_exhaustive] pub enum ForeignEmpty {}` and `pub fn same_crate_empty(x: ForeignEmpty) -> ! { match x {} }`: compiles cleanly (`dep_rc = 0`).
- Crate `client` depends on `--extern dep=...` and writes `pub fn foreign_crate_empty(x: dep::ForeignEmpty) -> ! { match x {} }`: rejected (`client_rc = 1`) with **`error[E0004]: non-exhaustive patterns: type 'ForeignEmpty' is non-empty`** and note `the matched value is of type 'ForeignEmpty', which is marked as non-exhaustive`.

---

### 3. `PlaceValidity`, Dereference Boundaries, and the `can_omit_empty_arms` Predicate

Basis: source (`rust-lang/rust` `check_match.rs:290-365`, `usefulness.rs:842-985`, `constructor.rs:1079-1215`) + execution (`np_01b`, `np_02`, `np_02b`, `np_02c`, `np_05`, `np_05b`) + derived (Lean `ce2`, `ce3`).

Why does `rustc` allow omitting `Err` on by-value `Result<u32, !>` and allow `match *p {}` on `*const !`, yet reject omitting `Err` on `&Result<u32, !>` and reject `match *p {}` on `*const HasNever` (`struct HasNever(u32, !)`)? The entire design reduces to three tightly coupled functions in `rustc_mir_build` and `rustc_pattern_analysis`.

#### Step A: Initial Scrutinee Validity (`is_known_valid_scrutinee`)

In `compiler/rustc_mir_build/src/thir/pattern/check_match.rs:290-365`, `MatchVisitor::is_known_valid_scrutinee` recursively inspects the THIR scrutinee expression to decide whether the top-level match column starts as `PlaceValidity::ValidOnly` or `PlaceValidity::MaybeInvalid`:
- Local variables, value expressions (function returns, temporaries), and field projections of structs/tuples/enums inherit validity from their base expression (`ValidOnly` when the base is valid).
- **Dereference expressions (`ExprKind::Deref`) — covering both `*raw_ptr` and `*shared_ref` / `*mut_ref` — return `false` (`PlaceValidity::MaybeInvalid`)**, because dereferencing a raw pointer (or a reference in `unsafe` code that has not yet been read) does not statically guarantee that the pointee bytes satisfy Rust's type-validity invariant at the moment the place expression is formed.
- **Union field projections (`ExprKind::Field` on a `ty::Adt` union)** also return `false` (`PlaceValidity::MaybeInvalid`), because reading an inactive union field may yield invalid bytes for the field's type.

#### Step B: Validity Loss Across Projections (`PlaceValidity::specialize`)

In `compiler/rustc_pattern_analysis/src/usefulness.rs:842-917`, `PlaceValidity` has two states (`ValidOnly` and `MaybeInvalid`) and transitions on constructor specialization:

```rust
pub enum PlaceValidity {
    ValidOnly,
    MaybeInvalid,
}

impl PlaceValidity {
    fn specialize(self, ctor: &Constructor<Cx>) -> Self {
        match ctor {
            Constructor::Ref | Constructor::DerefPattern(_) | Constructor::UnionField => {
                PlaceValidity::MaybeInvalid
            }
            _ => self,
        }
    }
}
```

When matching `r: &Result<u32, !>`:
1. Column 0 begins as `(ty = &Result<u32, !>, validity = ValidOnly, is_scrutinee = true)` (because `r` itself is a by-value local reference).
2. Specializing on `Constructor::Ref` yields the inner column `(ty = Result<u32, !>, validity = MaybeInvalid, is_scrutinee = false)`.
3. Crucially, **both** `validity` flips from `ValidOnly` to `MaybeInvalid` **and** `is_scrutinee` flips from `true` to `false`.

#### Step C: Exact `can_omit_empty_arms` Decision Rule (`split_column_ctors`)

In `compiler/rustc_pattern_analysis/src/usefulness.rs:947-985`, `PlaceInfo::split_column_ctors` computes whether uninhabited constructors may be omitted from the required constructor split:

```rust
let is_toplevel_exception =
    self.is_scrutinee && matches!(ctors_for_ty, ConstructorSet::NoConstructors);
let is_empty_match_exception = self.is_scrutinee
    && cx.is_empty_match() // (when checking empty match diagnostics)
    && (is_toplevel_exception || cx.is_exhaustive_patterns_feature_on());
let can_omit_empty_arms = self.validity.is_known_valid()
    || is_toplevel_exception
    || cx.is_exhaustive_patterns_feature_on();
```

Notice the sharp syntactic distinction between `ConstructorSet::NoConstructors` (returned for `!` and local non-`#[non_exhaustive]` zero-variant enums) and `ConstructorSet::Struct { empty: true }` (returned for structs/tuples containing an uninhabited field such as `struct HasNever(u32, !)`): `is_toplevel_exception` matches **only** `NoConstructors` (`constructor.rs:1079-1215`)!

The complete 6-cell truth table verified by live `rustc` execution is:

| Case & Scrutinee | Column `ty` at Empty Check | `validity` | `is_scrutinee` | `ctors_for_ty` | `can_omit_empty_arms` | Observed `rustc` Result |
| :--- | :--- | :---: | :---: | :--- | :---: | :--- |
| `np_01b`: by-value `Result<u32, Infallible>`, arm `Ok(v)` | `Infallible` (`!`) | `ValidOnly` | `false` | `NoConstructors` | **`true`** | **Accepted** (`rc=0`, `MIN_EXHAUSTIVE=42`) |
| `np_02b`: `r: &Result<u32, !>`, arm `Ok(v)` only (`never_patterns`) | `!` (under `Ref` -> `Err`) | `MaybeInvalid` | `false` | `NoConstructors` | **`false`** | **Rejected `E0004`**: `` `&Err(!)` not covered ``; note: `` `!` is uninhabited but is not being matched by value, so a wildcard `_` is required ``; help suggests `&Err(!),` |
| `np_02`: `r: &Result<u32, !>`, arms `Ok(v) => *v, Err(!),` | `!` covered by `PatKind::Never` -> `Wildcard` | `MaybeInvalid` | `false` | `NoConstructors` | `false`, **covered by `!`** | **Accepted** (`rc=0`) |
| `np_02c`: `r: &Result<u32, !>`, arm `Ok(v)` only (`#![feature(exhaustive_patterns)]`) | `!` | `MaybeInvalid` | `false` | `NoConstructors` | **`true`** (feature) | **Accepted** (`rc=0`), emits identical optimized MIR to `np_02` |
| `np_05`: `p: *const !`, `unsafe { match *p {} }` | `!` | `MaybeInvalid` | **`true`** | **`NoConstructors`** | **`true`** (`is_toplevel_exception`) | **Accepted** (`rc=0`), emits `unreachable` |
| `np_05b`: `p: *const HasNever`, `unsafe { match *p {} }` | `HasNever(u32, !)` | `MaybeInvalid` | **`true`** | **`Struct { empty: true }`** | **`false`** | **Rejected `E0004`**: `` type `HasNever` is non-empty `` |

This explains the architectural motivation behind bodiless `!` patterns (`#118155`, `compiler/rustc_feature/src/unstable.rs:682`): on `r: &Result<u32, !>` (or `p: *const HasNever`), the language refuses to *silently* omit the uninhabited arm because `r`/`p` might in `unsafe` code point to uninitialized or invalid bytes; requiring an explicit `Err(!),` (or `HasNever(_, !),`) forces the programmer to write the pattern that lowers to a place read / `unreachable` assertion at the match site rather than leaving an uninspected validity assumption implicit.

---

### 4. Bodiless Never Patterns (`#![feature(never_patterns)]`): AST-to-MIR Pipeline and Pass Lifecycle

Basis: source (`rust-lang/rust` `rustc_ast_lowering/src/expr.rs`, `rustc_hir_typeck/src/pat.rs`, `check_match.rs`, `builder/matches/{mod.rs, match_pair.rs, test.rs}`, `rustc_mir_transform/src/{lib.rs, cleanup_post_borrowck.rs, remove_place_mention.rs, remove_zsts.rs}`) + execution (`np_02`, `np_03`, `np_04`, `np_04b`, `np_05`, `np_07f`).

Tracing a bodiless never-pattern arm (`Err(!),` or `match *p { ! }`) across every compiler stage explains every diagnostic, MIR local, and pass interaction observed empirically.

#### Stage 1: AST-to-HIR Lowering (`rustc_ast_lowering/src/expr.rs:793-843`)

When lowering an AST match arm, `rustc_ast_lowering` computes `let is_never_pattern = pat.is_never_pattern();` (recursively true if any sub-pattern of a product/variant/ref is a never pattern, or **both** sides of an or-pattern are never patterns):
- If `is_never_pattern` is true and the arm supplies a body (`Err(!) => 0`), `expr.rs:822` emits **`NeverPatternWithBody`** (`np_04`: `error: a never pattern is always unreachable`).
- If `is_never_pattern` is true and the arm supplies a guard (`Err(!) if true,`), `expr.rs:824` emits **`NeverPatternWithGuard`** (`np_04b`: `error: a guard on a never pattern will never be run`).
- Conversely, if the arm omits a body and `!is_never_pattern`, `expr.rs:815` rejects it as a missing arm body.
- Crucially, for a valid bodiless never-pattern arm (`body.is_none() && is_never_pattern`), HIR still requires every `hir::Arm` to hold a `body: &hir::Expr`. `rustc_ast_lowering` therefore **synthesizes a fake diverging `loop {}` HIR expression** for the arm body.

**Empirical MIR artifact explained:** This synthesized fake `loop {}` directly explains why in `np_02` (`np_02.ref_to_err_never.built.after.mir`) basic blocks `bb9..bb13` contain an unreachable `falseUnwind` loop over `let mut _4: !; let mut _5: ();`, and why in `np_05` (`explicit_never_pat_raw_never`), **both** `rustc 1.98.0-nightly` and `rustc 1.102.0-nightly` retain the two dead locals `let mut _2: !; let mut _3: ();` in the default `--emit=mir` dump (whereas `empty_match_raw_never`, which has no arm at all, has only `let mut _0: ();` after optimization!).

#### Stage 2: Type Checking and Never-Pattern Validation (`rustc_hir_typeck` + `check_match`)

1. In `compiler/rustc_hir_typeck/src/pat.rs:587, 767`:
   - `PatKind::Never => expected` accepts any expected type during HIR type checking without rejecting inhabited types yet.
   - `PatKind::Never => AdjustMode::peel_all()` peels auto-deref match ergonomics references (allowing `Err(!)` inside `match r` for `r: &Result<u32, !>` to match `&Err(!)` seamlessly).
2. In `compiler/rustc_mir_build/src/thir/pattern/check_match.rs:908-918`, `check_never_pattern` validates that the resolved THIR pattern type is actually uninhabited in the current module:
   ```rust
   fn check_never_pattern<'tcx>(cx: &RustcPatCtxt<'_, 'tcx>, pat: &Pat<'tcx>) -> Result<(), ErrorGuaranteed> {
       if !cx.is_uninhabited(pat.ty) {
           return Err(cx.tcx.dcx().emit_err(NonEmptyNeverPattern { span: pat.span, ty: pat.ty }));
       }
       Ok(())
   }
   ```
   Live execution (`np_03_never_pattern_on_inhabited_type_rejected`) confirms that `Some(!),` on `Option<u32>` fails with `error: mismatched types ... a never pattern must be used on an uninhabited type ... the matched value is of type 'u32'` (note also a minor doc-comment typo on `check_match.rs:907` in upstream source).
3. In `compiler/rustc_pattern_analysis/src/rustc.rs:696-703`, `lower_pat` lowers `PatKind::Never` to `Constructor::Wildcard` for matrix exhaustiveness analysis—so `!` covers the uninhabited column in `check_match` while retaining distinct lowering semantics during MIR construction.

#### Stage 3: MIR Construction (`builder/matches/{mod.rs, match_pair.rs, test.rs}`)

During MIR building:
1. `Builder::lower_scrutinee` (`builder/matches/mod.rs:374-386`) evaluates the scrutinee place and emits `StatementKind::PlaceMention(scrutinee)`.
2. `match_pair.rs:462-466` lowers `PatKind::Never` as **`InterPatKind::Refutable`** with `TestableCase::Never` (never as an irrefutable wildcard!).
3. `test.rs:59, 317-329` lowers `TestKind::Never` by emitting a `FakeRead` of the uninhabited place followed immediately by `TerminatorKind::Unreachable`:
   ```rust
   TestKind::Never => {
       // FIXME(never_patterns): Also assert validity of the data at `place`.
       // We emit a fake read so that borrowck/liveness/union-safety treat `!` as reading the place.
       self.cfg.push_fake_read(block, source_info, FakeReadCause::ForMatchedPlace(None), place);
       self.cfg.terminate(block, source_info, TerminatorKind::Unreachable);
   }
   ```
4. Similarly, when a `match` is exhaustive with no remaining candidates (such as `match *p {}`), `builder/matches/mod.rs:1637-1649` pushes `FakeRead(ForMatchedPlace(None), scrutinee)` into `otherwise_block` and terminates it with `TerminatorKind::Unreachable`.

**Two compile-time soundness invariants enforced by `FakeRead` (verified live in `np_07f_never_pattern_uninit_and_union_read`):**
- Matching an uninitialized `let x: !; match x { ! }` triggers borrowck **`E0381: used binding 'x' isn't initialized`** (because `FakeRead(ForMatchedPlace(None), _1)` demands initialization), alongside `#[warn(unreachable_code)]` and `#[warn(unreachable_patterns)]`.
- Matching a union field `let U { a: ! } = u;` outside `unsafe` triggers **`E0133: access to union field is unsafe and requires unsafe block`** (matching upstream `tests/ui/rfcs/rfc-0000-never_patterns/never-pattern-is-a-read.rs:1-14`).

**Critical open compiler `FIXME` (`test.rs:319`):** Notice that `TestKind::Never` currently emits **only** `FakeRead` (which is erased post-borrowck) and `TerminatorKind::Unreachable`; it does **not** emit a separate runtime `PlaceMention` or validity-asserting read on sub-places. For `match *p { ! }` or `match *p { HasNever(_, !), }`, control immediately enters `TerminatorKind::Unreachable`, so UB is still triggered unconditionally when control reaches the `!` pattern—**provided** the branch reaching `!` is taken. On `ref_to_err_never(_1: &Result<u32, !>)`, the `Err(!)` branch is preceded by `_2 = discriminant((*_1))`, which itself traps on an uninhabited enum variant in Miri (§5).

#### Stage 4: MIR Pass Lifecycle (`built` -> `CleanupPostBorrowck` -> `RemovePlaceMention` -> `RemoveZsts`)

Live `-Zdump-mir=all` and `-Zmir-preserve-ub` captures (`np_02` and `np_05` in `support/probe_never_patterns_postfix_match_and_exhaustiveness.json`) trace the exact statement survival across `rustc_mir_transform/src/lib.rs:642-736`:

| MIR Pass / Stage | Source Location & Gate | `np_05` `wildcard_match_raw_never` (`match *p { _ => 99 }`) | `np_05` `explicit_never_pat_raw_never` (`match *p { ! }`) | `np_02` `ref_to_err_never` (`&Result<u32, !>`) |
| :--- | :--- | :--- | :--- | :--- |
| **`built` (after)** | `builder/matches/` | `bb0: PlaceMention((*_1)); _0 = const 99_u32; goto -> bb2;` + `bb1: FakeRead((*_1)); unreachable;` | `bb0: PlaceMention((*_1)); FakeRead((*_1)); unreachable;` + dead fake `loop {}` in `bb4..bb10` | `bb0: PlaceMention(_1); _2 = discriminant((*_1)); switchInt -> [0: bb2, 1: bb4, otherwise: bb1]; bb4: FakeRead((((*_1) as Err).0: !)); unreachable;` |
| **`CleanupPostBorrowck` (after)** | `cleanup_post_borrowck.rs:28-64` (unconditional, `Analysis(PostCleanup)`) | `bb0: PlaceMention((*_1)); _0 = const 99_u32; return;` (`FakeRead` -> erased) | `bb0: PlaceMention((*_1)); nop; unreachable;` (`FakeRead` -> `nop`; dead `loop {}` CFG pruned, dead locals `_2, _3` kept) | `bb0: PlaceMention(_1); _2 = discriminant((*_1)); ... bb3: nop; unreachable;` |
| **`RemovePlaceMention` (after)** | `remove_place_mention.rs:13`: `!mir_preserve_ub` (`Runtime(PostCleanup)`) | `bb0: _0 = const 99_u32; return;` (`PlaceMention` erased) | `bb0: unreachable;` (`PlaceMention` erased) | `bb0: _2 = discriminant((*_1)); switchInt -> [0: bb2, 1: bb1, otherwise: bb1]; bb1: unreachable;` |
| **`-Zmir-opt-level=0 -Zmir-preserve-ub`** (Miri profile) | `RemovePlaceMention` skipped; `RemoveZsts` disabled (`opt_level < 1`) | **`PlaceMention((*_1))` SURVIVES** (`preserve_ub_opt0_has_place_mention = true`) | **`PlaceMention((*_1))` SURVIVES** (`bb0: PlaceMention((*_1)); unreachable;`) | **`PlaceMention(_1)` SURVIVES** (`bb0: PlaceMention(_1); _2 = discriminant((*_1)); ...`) |
| **`-Zmir-opt-level=1 -Zmir-preserve-ub`** | `remove_zsts.rs:13`: `mir_opt_level() >= 1`; `L124`: erases ZST `PlaceMention`! | **`PlaceMention((*_1))` ERASED!** (`preserve_ub_opt1_has_place_mention = false`) | **`PlaceMention((*_1))` ERASED!** (`bb0: unreachable;`, dead locals `_2, _3` also eliminated) | **`PlaceMention(_1)` SURVIVES** (because `_1: &Result<u32, !>` is non-ZST, 8 bytes!) |

**Subtle compiler pass interaction discovered:** `RemoveZsts` (`compiler/rustc_mir_transform/src/remove_zsts.rs:13, 124, 143-148`) runs whenever `ctx.mir_opt_level() >= 1` and treats `StatementKind::PlaceMention(ref place)` identically to ZST assignments when `place` has zero size (`!`), erasing `PlaceMention((*_1))` **even under `-Zmir-preserve-ub`** (whereas `PlaceMention(_1)` on the 8-byte reference `_1` in `np_02` survives at `-Zmir-opt-level=1 -Zmir-preserve-ub`). Because `Miri` disables MIR optimizations (`-Zmir-opt-level=0`) and sets `-Zmir-preserve-ub`, `Miri` always executes the preserved `PlaceMention((*_1))` statement.

---

### 5. Three-Way Operational Semantics in `Miri`: Null Raw Pointers, Rogue Enum Tags, and Product Types

Basis: normative specification (`rust-lang/reference` `behavior-considered-undefined.md:19, 58-59, 83-159`) + source (`rust-lang/rust` `rustc_const_eval/src/interpret/{step.rs, place.rs, discriminant.rs, validity.rs}`) + execution (`13` live `Miri` cases on `1.98.0-nightly`, cross-checked against `3` null-`*const !` cases on `1.102.0-nightly`) + derived (Lean `threeWay_null_raw_never_split`, `ce2`, `ce3`).

Executing all 13 `Miri` cases (`support/probe_never_patterns_postfix_match_and_exhaustiveness.json`, `miri_comparison`) exposes four sharp operational boundaries in `rustc_const_eval`:

#### Complete 13-Case Live `Miri` Matrix

| # | Case ID | Scrutinee Construction | Match Expression | `Miri` (`1.98.0-nightly`) Outcome | `1.102.0-nightly` Cross-Check | Determining Interpreter Source |
| :-: | :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | `wildcard_match_star_null` | `p: *const ! = null()` | `match *p { _ => 99 }` | **`rc=0`**, `WILDCARD_NULL_OK=99` | **`rc=0`**, `WILDCARD_NULL_OK=99` (exact match) | `step.rs:119` (`PlaceMention`) -> `place.rs:517-534` (`deref_pointer` sized raw ptr skips null/align/valid) |
| 2 | `empty_match_star_null` | `p: *const ! = null()` | `match *p {}` | **`rc=1`**, `UB: entering unreachable code` | **`rc=1`**, `UB: entering unreachable code` (exact match) | `step.rs:704` (`TerminatorKind::Unreachable => throw_ub!(Unreachable)`) |
| 3 | `explicit_bang_match_star_null` | `p: *const ! = null()` | `match *p { ! }` | **`rc=1`**, `UB: entering unreachable code` | **`rc=1`**, `UB: entering unreachable code` (exact match) | `test.rs:328` (`TestKind::Never`) -> `step.rs:704` (`Unreachable`) |
| 4 | `rogue_tagged_raw_ptr_err_wildcard` | Aligned `[u8; 8]` with tag `1` as `p: *const Tagged` (`#[repr(C, u8)] enum Tagged { Ok(u32) = 0, Err(!) = 1 }`) | `match *p { Tagged::Ok(v) => v, Tagged::Err(_) => 777 }` | **`rc=1`**, `UB: read discriminant of an uninhabited enum variant` | N/A (extended case) | `discriminant.rs:214-216` (`is_variant_uninhabited(index)`) |
| 5 | `rogue_tagged_raw_ptr_err_bang` | Same `p: *const Tagged` (tag `1`) | `match *p { Tagged::Ok(v) => v, Tagged::Err(!), }` | **`rc=1`**, `UB: read discriminant of an uninhabited enum variant` | N/A (extended case) | `discriminant.rs:214-216` (faults at `discriminant((*_1))` **before** `!` arm) |
| 6 | `rogue_tagged_raw_ptr_omit_err_exhaustive_patterns` | Same `p: *const Tagged` (tag `1`, `#![feature(exhaustive_patterns)]`) | `match *p { Tagged::Ok(v) => v }` | **`rc=1`**, `UB: read discriminant of an uninhabited enum variant` | N/A (extended case) | `discriminant.rs:214-216` |
| 7 | `rogue_tagged_shared_ref_err_wildcard` | Aligned tag `1` -> `r: &Tagged` (`&*p`) | `match r { Tagged::Ok(v) => *v, Tagged::Err(_) => 777 }` | **`rc=1`**, `UB: read discriminant of an uninhabited enum variant` | N/A (extended case) | `&Tagged` creation succeeds (shallow validity); faults on `Rvalue::Discriminant` (`discriminant.rs:214-216`) |
| 8 | `rogue_tagged_shared_ref_err_bang` | Same `r: &Tagged` (tag `1`) | `match r { Tagged::Ok(v) => *v, Tagged::Err(!), }` | **`rc=1`**, `UB: read discriminant of an uninhabited enum variant` | N/A (extended case) | Same: faults at `discriminant((*_1))` |
| 9 | `rogue_tagged_shared_ref_top_wildcard` | Same `r: &Tagged` (tag `1`) | `match r { _ => 888 }` | **`rc=0`**, `ROGUE_TOP_WILDCARD_OK=888` | N/A (extended case) | No `Rvalue::Discriminant` emitted; shallow `&Tagged` validity does not read pointee bytes |
| 10 | `rogue_hasnever_raw_ptr_wildcard` | `x = 42u32`, `p = (&x as *const u32).cast::<HasNever>()` (`#[repr(C)] struct HasNever(u32, !)`) | `match *p { HasNever(n, _) => n }` | **`rc=0`**, `HASNEVER_RAW_WILD_OK=42` | N/A (extended case) | Product type has no discriminant; `_` does not read `!` field; `n` reads valid `42u32` |
| 11 | `rogue_hasnever_raw_ptr_bang` | Same `p: *const HasNever` pointing to `42u32` | `match *p { HasNever(_, !), }` | **`rc=1`**, `UB: entering unreachable code` | N/A (extended case) | `TestKind::Never` emits `TerminatorKind::Unreachable` on `!` sub-pattern |
| 12 | `rogue_hasnever_shared_ref_wildcard` | `r: &HasNever = unsafe { &*(&x as *const u32).cast::<HasNever>() }` | `match r { HasNever(n, _) => *n }` | **`rc=1`**, `UB: constructing invalid value of type &HasNever: encountered a reference pointing to uninhabited type HasNever` | N/A (extended case) | `validity.rs:700-707` (`!place.layout.ty.is_opsem_inhabited`) faults at `&*...` creation before `match` |
| 13 | `rogue_hasnever_shared_ref_bang` | Same `r: &HasNever` creation | `match r { HasNever(_, !), }` | **`rc=1`**, same `constructing invalid value of type &HasNever` | N/A (extended case) | `validity.rs:700-707` faults at `&*...` creation before `match` |

#### Exact Operational Mechanisms Behind the Split

1. **Why `match *p { _ => 99 }` on `null()` succeeds in `Miri` (`place.rs:468-536`):**
   `StatementKind::PlaceMention(place)` executes `self.eval_place(place)` (`step.rs:119-125`), which invokes `InterpCx::deref_pointer` (`place.rs:468-536`). Inside `deref_pointer`:
   - When `ptr_ty.is_ref() || ptr_ty.is_box()`, Miri enforces non-null, dereferenceability (`check_ptr_access`), and alignment (`check_ptr_align`).
   - In the `else { assert!(ptr_ty.is_raw_ptr()); ... }` branch (`L517-534`), Miri checks **only** `ty::Dynamic` vtable validity when `mplace.layout.is_unsized()`. For a sized raw pointer (`*const !`), `deref_pointer` only reads the initialized pointer value (`0usize`) and returns a dangling `MPlaceTy` without throwing UB. Because the wildcard arm `_ => 99` never loads from that `MPlaceTy`, execution completes cleanly and prints `WILDCARD_NULL_OK=99`.
   - This aligns with the Rust Reference (`behavior-considered-undefined.md:88, 110`): forming a place from a misaligned or dangling raw pointer is not itself UB until loaded from or stored to, and zero-sized places are never dangling.
2. **Why `match *p {}` and `match *p { ! }` both fault identically (`step.rs:704`):**
   Both empty-match lowering (`builder/matches/mod.rs:1648`) and `TestKind::Never` (`builder/matches/test.rs:328`) emit `TerminatorKind::Unreachable` immediately after `PlaceMention((*_1))`. In `Miri`, `PlaceMention((*_1))` succeeds on `null()`, and the very next step hits `TerminatorKind::Unreachable => throw_ub!(Unreachable)` (`step.rs:704`).
3. **Discriminant trap vs. product-type separation (`discriminant.rs:214-216` vs. `HasNever`):**
   - For an enum like `Tagged { Ok(u32) = 0, Err(!) = 1 }`, any match arm that inspects the variant tag emits `Rvalue::Discriminant((*_1))`. `InterpCx::read_discriminant` (`compiler/rustc_const_eval/src/interpret/discriminant.rs:214-216`) checks:
     ```rust
     if op.layout().is_variant_uninhabited(index) {
         throw_ub!(UninhabitedEnumVariantRead(Some(index)))
     }
     ```
     Hence even `Tagged::Err(_) => 777` (a wildcard on the payload!) triggers UB at the discriminant read (cases 4 and 7), whereas a top-level wildcard `match r { _ => 888 }` emits no `Rvalue::Discriminant` and succeeds (`ROGUE_TOP_WILDCARD_OK=888`, case 9) because Miri's reference validity check (`validity.rs:700-707`) is shallow on inhabited pointees (`Tagged.is_opsem_inhabited == true`).
   - By contrast, a product type `#[repr(C)] struct HasNever(u32, !)` has **no enum discriminant**. Behind a raw pointer `*const HasNever`, `match *p { HasNever(n, _) => n }` never reads field `.1: !` and returns `42` (case 10), whereas `match *p { HasNever(_, !), }` lowers the `!` sub-pattern to `TerminatorKind::Unreachable` and traps immediately (case 11). This proves why `rustc` MUST forbid omitting empty arms on `PlaceValidity::MaybeInvalid` product types (`np_05b`): if `match *p {}` were silently accepted as exhaustive on `*const HasNever`, a program that deliberately avoids touching field `.1` would turn a well-defined partial read into unconditional `unreachable` UB!
4. **Conservatism gap between `rustc_pattern_analysis` and `Miri` on `&HasNever`:**
   `check_match.rs:1350` documents `err.note("references are always considered inhabited")` in exhaustiveness analysis (reflecting ongoing UCG debate noted in `behavior-considered-undefined.md:152`: *"Note that the last point (about pointing to a valid value) remains a subject of some debate"*). Meanwhile, `Miri`'s operational validity checker (`validity.rs:700-707`) **already rejects** `&HasNever` at reference creation via `!place.layout.ty.is_opsem_inhabited` (cases 12 and 13). Preserving this explicit disagreement rather than collapsing it is essential for any verified Rust compiler or abstract machine: `rustc_pattern_analysis` is strictly more conservative than Miri on `&Uninhabited`.

---

### 6. Traditional Arm Guards vs. Live `#![feature(guard_patterns)]` Soundness and Miscompilation Defect

Basis: normative specification (`rust-lang/reference` `expressions/match-expr.md:133-247`) + source (`rust-lang/rust` `check_match.rs:512, 591-594`, `usefulness.rs:757, 1720`, `rustc.rs:471-472`, `match_pair.rs:457-460`) + execution (`np_07a`, `np_07b`, `np_07c`) + derived (Lean `guardPattern_must_stay_opaque_for_exhaustiveness`, `ce1`).

#### Soundness Baseline: Traditional Match Arm Guards

In the Rust Reference (`expressions/match-expr.md:133-183`), an arm guard (`Pattern if GuardCond => Body`) runs after the pattern matches and, on `false`, continues testing subsequent patterns (including remaining `|` alternatives in the same arm, `L146`). Because arbitrary runtime predicates cannot in general be decided statically, a sound exhaustiveness checker must treat guarded arms as contributing **zero** coverage to exhaustiveness.

`rustc` enforces this cleanly for traditional arm guards:
1. `check_match.rs:512` records `has_guard: arm.guard.is_some()` on each `MatchArm`.
2. `usefulness.rs:757` suppresses witness elimination for guarded rows (`if row.useful && !row.is_under_guard { ... }`), and `usefulness.rs:1720` propagates `useful &= row.is_under_guard` when testing whether an arm makes later rows redundant.
3. `check_match.rs:591-594` re-checks exhaustiveness with `has_guard: false` only for diagnostic diagnostics so it can emit the explanatory note `match arms with guards don't count towards exhaustivity`.

Live execution (`np_07a_arm_guard_opaque_to_exhaustiveness`) verifies that:
```rust
pub fn bad_arm_guard(x: Option<i32>) -> i32 {
    match x {
        Some(n) if n > 0 => n,
        None => 0,
    }
}
```
is rejected with **`error[E0004]: non-exhaustive patterns: 'Some(_)' not covered`** and `note: match arms with guards don't count towards exhaustivity`.

#### Live `#![feature(guard_patterns)]` Twin Defect (Present Across `1.98.0-nightly`, `1.102.0-nightly`, and `HEAD`)

By contrast, sub-pattern guards gated behind `#![feature(guard_patterns)]` (`#129967`, `incomplete`) — such as `Some(n if n > 0) => ...` or `(Some(n if n > 0), true) | ...` — suffer from **two compounding defects** that remain identically unfixed in `1.98.0-nightly` (`14210df0e`), `1.102.0-nightly` (`3ef0c22cd`), and `HEAD` (`01afe5348`):

1. **Exhaustiveness opacity bug (`compiler/rustc_pattern_analysis/src/rustc.rs:471-472`):**
   ```rust
   PatKind::AscribeUserType { subpattern: subpat, .. }
   | PatKind::Guard { subpattern: subpat, .. } => return self.lower_pat(subpat),
   ```
   `lower_pat` strips `PatKind::Guard` and lowers its `subpattern` directly **without** marking the enclosing `MatrixRow` as `is_under_guard = true` and without introducing an opaque refutable constructor (such as `Constructor::Opaque` or guard-tagged wildcard). Consequently, `rustc_pattern_analysis` treats `Some(n if n > 0)` as covering **all** `Some(_)` values!
2. **MIR builder placeholder stub (`compiler/rustc_mir_build/src/builder/matches/match_pair.rs:457-460`):**
   ```rust
   PatKind::Guard { .. } => {
       // FIXME(guard_patterns)
       InterPatKind::Irrefutable { subpats: vec![], binding: None }
   }
   ```
   During MIR construction, `PatKind::Guard` is lowered to an **empty irrefutable pattern with no sub-patterns and no binding**, silently erasing both the runtime guard condition (`n > 0`) and every binding declared inside `subpattern` (`n`)!

#### Empirical Reproduction Receipts (`np_07b` and `np_07c`)

Live execution on `rustc 1.98.0-nightly` (`support/probe_never_patterns_postfix_match_and_exhaustiveness.json`) directly confirms both halves of the defect:

1. **Silent runtime miscompilation + false `unreachable_patterns` lint (`np_07b_guard_patterns_live_defect_and_int_ranges`):**
   ```rust
   #![feature(guard_patterns)]
   fn classify_subpat_guard(x: Option<i32>) -> &'static str {
       match x {
           Some(n if n > 0) => "pos",
           Some(_) => "nonpos",
           None => "none",
       }
   }
   ```
   - `rustc` exits `0`, emitting a **false** `warning: unreachable pattern` on line 6 (`Some(_) => "nonpos"`) with note `matches all the relevant values` on `Some(n if n > 0)` (caused by `rustc.rs:472`).
   - Running the compiled binary prints **`GUARD_POS=pos GUARD_NEG=pos GUARD_NONE=none RANGE_0=hit RANGE_255=hit`** — i.e., `classify_subpat_guard(Some(-5))` **silently returns `"pos"`** because `match_pair.rs:459` discarded `n > 0`!
   - Meanwhile, the same probe confirms exhaustive integer range patterns (`0u8..=127 | 128..=255 => "hit"`, normative in `patterns.md:641-642`) compile and match cleanly (`RANGE_0=hit RANGE_255=hit`).
2. **Missing `E0004` + spurious borrowck `E0381` when the guarded binding is used (`np_07c_guard_patterns_omits_e0004_and_drops_binding`):**
   ```rust
   #![feature(guard_patterns)]
   pub fn only_subpat_guard(x: Option<i32>) -> i32 {
       match x {
           Some(n if n > 0) => n,
           None => 0,
       }
   }
   ```
   - `rustc` emits **zero `E0004`** (exhaustiveness falsely passes via `rustc.rs:472`!).
   - Instead, borrowck rejects the arm body with **`error[E0381]: used binding 'n' isn't initialized`** because `match_pair.rs:459` dropped the binding (`binding: None`)!

**Implication for verified compilers and Anneal:** Until both `rustc.rs:472` (guard-opacity tracking in `rustc_pattern_analysis`) and `match_pair.rs:457-460` (actual MIR test/binding/short-circuit lowering) are implemented upstream, `#![feature(guard_patterns)]` is **unsound for both exhaustiveness checking and runtime semantics** and must be rejected fail-closed by any verification frontend. Note also that the cross-checked `1.102.0-nightly` receipt (`np_07_guard_patterns_or_exhaustive_int_ranges`, which exercised `(Some(n if n > 0), true) | ...` with a non-discriminating `"hit"` arm) exited `0` with `A=hit B=hit C=hit` purely because all inputs hit the same string literal—masking the exact same `rustc.rs:472` + `match_pair.rs:457-460` defect confirmed by source diff on `3ef0c22cd` and `01afe5348`.

---

### 7. Postfix Match (`#![feature(postfix_match)]`) Lowering and Temporary Drop-Scope Equivalence

Basis: normative specification (`rust-lang/reference` `destructors.md:55-118, 261-350`) + source (`rust-lang/rust` `rustc_ast_lowering/src/expr.rs:351-358`, `rustc_hir_analysis/src/check/region.rs:657-661`) + execution (`np_06`, `np_06b`, `np_06c` on `1.98.0-nightly` and `np_06` on `1.102.0-nightly`) + derived (Lean `postfixMatch_temp_drop_order_eq_prefix`).

#### Compiler Desugaring and Region-Scope Invariance

1. In `compiler/rustc_ast_lowering/src/expr.rs:351-358`:
   ```rust
   ast::ExprKind::Match(ref scrutinee, ref arms, match_kind) => {
       let match_source = match match_kind {
           ast::MatchKind::Prefix => hir::MatchSource::Normal,
           ast::MatchKind::Postfix => hir::MatchSource::Postfix,
       };
       ...
       hir::ExprKind::Match(scrutinee, arms, match_source)
   }
   ```
   Postfix `expr.match { ... }` differs from prefix `match expr { ... }` **solely** in the diagnostic `hir::MatchSource` tag (`Postfix` vs. `Normal`).
2. In `compiler/rustc_hir_analysis/src/check/region.rs:657-661`, drop-scope and temporary-scope construction matches on `hir::ExprKind::Match(_, arms, _)` with a wildcard `_` for `MatchSource`:
   - The scrutinee expression is evaluated in the enclosing temporary scope (per `destructors.md:282`: *"The scrutinee of a `match` expression is not a temporary scope, so temporaries in the scrutinee can be dropped after the `match` expression"*, i.e., at the end of the enclosing statement / `let` initializer unless extended).
   - Each arm has its own arm drop scope whose parent is the `match` expression scope (`destructors.md:83-84, 107-111`).

#### Empirical Drop-Order Verification Across Editions 2021 and 2024

All four live executions of the instrumented `Drop` harness (`let res = make(&log, 10).match { x => { log.borrow_mut().push("arm_body"); x.0 + 5 } }; log.borrow_mut().push("after_match");` and its prefix `match` counterpart) produce bit-for-bit identical output:

| Case | Syntax | Edition | Toolchain | Exit Code | Observed Stdout |
| :--- | :--- | :---: | :--- | :-: | :--- |
| `np_06_postfix_match_chaining_and_temp_drop_order` | `make(&log, 10).match { ... }` | `2024` | `1.98.0-nightly` (`14210df0e`) | `0` | `RES=15 LOG=["make", "arm_body", "drop_inner", "after_match"]` |
| `np_06b_postfix_match_edition_2021` | `make(&log, 10).match { ... }` | `2021` | `1.98.0-nightly` (`14210df0e`) | `0` | `RES=15 LOG=["make", "arm_body", "drop_inner", "after_match"]` |
| `np_06c_prefix_match_edition_2024_comparison` | `match make(&log, 10) { ... }` | `2024` | `1.98.0-nightly` (`14210df0e`) | `0` | `RES=15 LOG=["make", "arm_body", "drop_inner", "after_match"]` |
| `np_06` (retained cross-check) | `make(&log, 10).match { ... }` | `2024` | `1.102.0-nightly` (`3ef0c22cd`) | `0` | `RES=15 LOG=["make", "arm_body", "drop_inner", "after_match"]` |

In every case:
1. `"make"` constructs the temporary `Tracked(10)` scrutinee;
2. `"arm_body"` runs while `x` (moved from the scrutinee into the arm binding) is live inside the arm scope;
3. `"drop_inner"` runs as `x` leaves the arm scope (`destructors.scope.bindings.match-arm`, `destructors.md:164-165`), **before** execution proceeds past the `let res = ...;` statement;
4. `"after_match"` runs strictly after `"drop_inner"`.

Thus `postfix_match` introduces **zero** new drop-order or temporary-lifetime divergence relative to prefix `match` in either Edition 2021 or Edition 2024.

---

### 8. Integration with Anneal `Trusted.MirAst`, `Trusted.MirSemantics`, and `TrustedBoundary`

Basis: source (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/rustc-capture/src/driver.rs`, `trusted/audit/TrustedBoundary.lean`) + derived (Lean `anneal_never_param_vacuity_requires_static_admission`).

Examining `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` directly connects the upstream `rustc` findings in §§1–7 to Anneal's trusted computing base:

1. **Pinned Compiler Version (`trusted/rustc-capture/src/driver.rs:25`):**
   `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"` sits immediately prior to the `1.100.0` `never_type` stabilization (`accepted.rs:339`) and shares the exact `rustc_pattern_analysis` / `rustc_mir_build` / `rustc_mir_transform` architecture audited on `1.98.0-nightly (14210df0e 2026-05-31)` and `HEAD (01afe5348)`.
2. **MIR Representation & Fail-Closed Boundaries (`trusted/lean/Trusted/MirAst.lean`):**
   - `MirTy.never` (`L296, 316`) models `TyKind::Never` (`!`) natively as an uninhabited type (no `Val` constructor has `Val.ty? = some .never`).
   - `TerminatorKind.unreachable` (`L776, 789`) models `rustc`'s `TerminatorKind::Unreachable` directly, and `Trusted/MirSemantics.lean:1551-1552` evaluates it to immediate UB:
     ```lean
     | .unreachable =>
       .fault .undefined
     ```
   - `StatementKind.unsupported` (`MirAst.lean:636-662`) explicitly lists `FakeRead`, `PlaceMention`, `SetDiscriminant`, `AscribeUserType`, `Coverage`, `Intrinsic`, and `Nop` as failing closed to `.unsupported` (`FaultKind.unsupported`).
   - **Seam consequence with MIR passes (§4):**
     - `FakeRead` emitted by `TestKind::Never` (`test.rs:326`) and empty-match `otherwise_block` (`builder/matches/mod.rs:1644`) is already unconditionally erased by `CleanupPostBorrowck` (`Analysis(PostCleanup)`), so it never reaches `Runtime(PostCleanup)` MIR.
     - `PlaceMention` emitted by `lower_scrutinee` (`builder/matches/mod.rs:375`) is erased by `RemovePlaceMention` in default `Runtime(PostCleanup)` MIR (`!mir_preserve_ub`), **but survives if MIR is captured with `-Zmir-preserve-ub` at `-Zmir-opt-level=0`** (and even at `-Zmir-opt-level=1` for non-ZST places like `_1: &Result<u32, !>` in `np_02`). Therefore, if Anneal ever ingests `-Zmir-preserve-ub` MIR (to faithfully capture Miri's place-mention UB on dangling/misaligned references), `Trusted.MirAst` must explicitly distinguish `StatementKind.placeMention` with raw-pointer vs. reference/box `deref_pointer` semantics (`place.rs:468-536`) rather than collapsing `PlaceMention` to `.unsupported` or to a no-op!
3. **Closing `MirTy.never` Vacuous Verification (`Trusted/MirSemantics.lean:1715-1758, 2513-2600`):**
   Because `MirTy.never` has no inhabitant in `Val`, a function `fn(x: !) -> ()` has an **empty** `ValidEntryArgs body args` set (`L1715-1716`). A naive specification `∀ args, ValidEntryArgs body args → WellFormed ...` would be **vacuously true** even for a malformed body carrying out-of-bounds `StorageLive(9)`, unsupported local types, or wrong `pointerWidthBits`. `Trusted/MirSemantics.lean` closes this exact soundness hole by conjoining unconditional `BodyStaticAdmitted p body = true` (`L1730-1737`) into `BodyVerified` (`L1751-1758`):
   ```lean
   noncomputable def BodyVerified (p : Program) (defId : DefId) (body : Body)
       (safetyPre : List Val → Prop) : Prop :=
     getElem? p.bodies defId = some body ∧
     BodyStaticAdmitted p body = true ∧
     ∀ args : List Val,
       ValidEntryArgs body args →
       (body.isUnsafe = true → safetyPre args) →
       WellFormed (entryProgForBody p defId) { args := args }
   ```
   `MirSemantics.lean:2513-2600` exercises this directly via `canaryNeverParamBody (badStorage : Bool)` (an empty-block `TerminatorKind.unreachable` body taking `.never`), asserting that `canaryNeverParamBody true` (with `.storageLive 9`) **refutes** `BodyVerified`, while `canaryNeverParamBody false` **satisfies** `BodyVerified`.
4. **TrustedBoundary Pass-1/Pass-2 Lean Purity Compatibility (`trusted/audit/TrustedBoundary.lean:475, 1119, 1763-1774, 2143-2167`):**
   `TrustedBoundary.lean` forbids `sorryAx`, `Lean.ofReduceBool`/`Lean.ofReduceNat` (`native_decide`), `Lean.trustCompiler`, `unsafe`, and `isPartial` (`*._unsafe_rec` compiler helpers), while explicitly admitting `Parser.Command.noncomputable` (`L475`). Notably, Lean `v4.34.1`'s equation compiler emits an `isPartial` `<fn>._unsafe_rec` bytecode helper for **every** recursive `def` written with equation-compiler syntax (even simple structural recursion on `Nat` or `List`), whereas defining recursive specifications via kernel recursors (`Ty.rec`, `Pat.rec`, `ValStack.rec`, `Nat.rec`, `List.rec`) under `noncomputable def` and higher-order `List.foldr` eliminates **100%** of `._unsafe_rec` and `isPartial` constants while preserving kernel `rfl` definitional reduction and adding zero axioms (verified directly in §9).

---

### 9. Kernel-Checked Lean `v4.34.1` Mechanization and Constructive Sharpness Counterexamples

Basis: execution (Lean `v4.34.1` kernel check & `env.constants.toList` audit in `support/lean_check_receipt.json`) + source (`support/NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean`) + derived (mechanized proofs).

The standalone formalization `support/NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean` (`2,570` lines, `122,894` bytes, `sha256=efabb0ba0568dfd7ecc8052e616265012218c7fc349f28a68d9b6a64c554297b`, `0` imports beyond `Init`) mechanizes the entire semantic chain of §§1–8 across eight structured parts:

#### Architecture & Zero-`_unsafe_rec` Kernel Design

- **Part 1 (`Ty`, `FieldVis`, `ValidVal`, `visiblyUninhabited`, `isNoConstructors`):** Models `!`, `()`, `bool`, local vs. foreign `#[non_exhaustive]` empty enums (`.emptyEnum Bool`), `Option<T>`, `Result<T, E>`, two-field structs with per-field visibility (`.pair FieldVis Ty FieldVis Ty`), `&T`, `*const T`, and `union { a: T1, b: T2 }`. Proves `visiblyUninhabited_false_implies_no_validVal` and visibility monotonicity (`visiblyUninhabited_mono`).
- **Part 2 (`PlaceValidity`, `ScrutineeKind`, `RawPlace`, `PlaceRespectsValidity`, `readResultDiscr`):** Models `ValidOnly` vs. `MaybeInvalid`, validity reset across `Ref`/`Deref`/`UnionField`, valid vs. rogue operational places (`nullRawDeref`, `uninitLocal`, `rogueErrTag`, `roguePair`, `rogueRef`), and Miri's `UninhabitedEnumVariantRead` trap (`readResultDiscr`).
- **Part 3 (`Pat`, `Arm`, `checkPatWellFormed`, `armWellFormed`, `GuardLoweringMode`, `armCountsAsGuarded`):** Models wildcards, `!` (`Pat.never`), constructors, references, or-patterns, and sub-pattern guards (`Pat.subGuard`), enforcing `check_never_pattern` (`visiblyUninhabited`), bodiless/guardless never-pattern arms, and contrasting `GuardLoweringMode.soundOpaque` against `GuardLoweringMode.rustcBuggyUnguarded` (`rustc.rs:472`).
- **Part 4 (`evalPat`, `evalPatRustcStub`, `evalArmsLoop`, `evalMatchPlace`):** Models operational pattern evaluation (including `PlaceMention` wildcard success, `!` -> `.ubNeverRead` -> `.ubUnreachable`, rogue enum discriminant -> `.ubInvalidDiscrRead`, and live `rustc`'s `match_pair.rs:457-460` stub `evalPatRustcStub`). Proves `evalPat_validVal_never_faults` and `neverPattern_cannot_match_validVal`.
- **Part 5 (`PlaceCol`, `canOmitEmptyArms`, `lowerPatForAnalysis`, `expandOrColumn`, `specializeCol`, `specializeRows`, `requiredCtors`, `checkMatrixFuel`, `checkMatchExhaustive`):** Mirrors `rustc_pattern_analysis`'s exact `can_omit_empty_arms` / `is_toplevel_exception` / `PrivateUninhabited` / `NonExhaustive` matrix specialization algorithm.
- **Part 6 (`ValStack`, `loweredMatchesVal`, `rowMatchesStack`, `matrixWf`, `checkMatrixFuel_sound_valid`, `exhaustiveMatrix_every_valid_value_matched_or_never_read`):** Full inductive soundness proof that any match accepted by `checkMatchExhaustive` under `GuardLoweringMode.soundOpaque` reaches a concrete `.matchedArm k` on every valid value under every guard oracle and cannot be reached on any `ValidOnly` visibly uninhabited place.
- **Part 7 (Guard Opacity, Three-Way Place Split, Postfix Match, Anneal Bridge):** Proves `guardPattern_must_stay_opaque_for_exhaustiveness`, `threeWay_null_raw_never_split`, `postfixMatch_temp_drop_order_eq_prefix`, and `anneal_never_param_vacuity_requires_static_admission`.
- **Part 8 (Constructive Sharpness Counterexamples `ce1`–`ce6`):** Proves via constructive witnesses that relaxing any of the six soundness hypotheses breaks exhaustiveness, operational safety, or privacy boundaries.

Every recursive function over `Ty`, `Pat`, `ValStack`, `Nat`, and `List` is defined directly via kernel recursors (`Ty.rec`, `Pat.rec`, `ValStack.rec`, `Nat.rec`, `List.rec`) and `List.foldr` with `rfl` constructor equations, avoiding equation-compiler `._unsafe_rec` helpers completely.

#### Flagship Theorems and Constructive Sharpness Counterexamples

| Theorem (`NeverPatternsSoundness.*`) | Exact Mechanized Statement / Witness | Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| **`exhaustiveMatrix_every_valid_value_matched_or_never_read`** | For any `exhFeat`, `scrutVal`, well-formed `arms` accepted by `checkMatchExhaustive false exhFeat .soundOpaque t scrutVal arms = true`: (1) `∀ gOracle v : ValidVal t, ∃ k, evalMatchPlace false gOracle arms (.valid v) = .matchedArm k`, AND (2) `∀ p : RawPlace t, visiblyUninhabited false t = true → PlaceRespectsValidity .validOnly p → False`. | `[propext, Quot.sound]` |
| **`guardPattern_must_stay_opaque_for_exhaustiveness`** | `checkMatchExhaustive inMod exhFeat .soundOpaque t scrutVal arms = checkMatchExhaustive inMod exhFeat .soundOpaque t scrutVal (arms.filter (fun a => !armCountsAsGuarded .soundOpaque a))` — guarded arms (both top-level arm guards and `Pat.subGuard`) contribute identically zero coverage. | `[propext]` |
| **`threeWay_null_raw_never_split`** | On `p : RawPlace .never := .nullRawDeref`: `[wildArm]` yields `.matchedArm 0`, `[]` yields `.ubUnreachable`, and `[neverArm]` yields `.ubUnreachable`. | `[propext]` |
| **`postfixMatch_temp_drop_order_eq_prefix`** | `evalMatchTempDropTrace (lowerMatchSource .postfixDotMatch) = evalMatchTempDropTrace (lowerMatchSource .prefixNormal) = [.makeScrutinee, .armBody, .dropInnerTemp, .afterMatch]`. | `none` (`0` axioms) |
| **`anneal_never_param_vacuity_requires_static_admission`** | On `badNeverBody` (`paramTy := .never, storageInBounds := false`): `miniBodyVerifiedNaive badNeverBody` holds vacuously, `¬ miniBodyVerifiedAnneal badNeverBody` rejects it, and `miniBodyVerifiedAnneal goodNeverBody` admits the well-formed `.never` body. | `none` (`0` axioms) |
| **`ce1_guard_pattern_treated_as_exhaustive_causes_missing_arm`** | On `Option<bool>` with `[Some(_ if g0), None]` and `g0 = false`, `Some(false)`: `.rustcBuggyUnguarded` falsely accepts (`true`), `.soundOpaque` rejects (`false`), proper `evalMatchPlace` hits `.missingArmTrap`, and `evalMatchPlaceRustcStub` miscompiles to `.matchedArm 0`. | `[propext]` |
| **`ce2_uninhabited_behind_raw_ptr_without_read_unsound_unreachable`** | On `HasNever = (pub bool, pub !)` behind `.maybeInvalid`: `[]` is rejected (`exhFeat = false`) and accepted (`exhFeat = true`), while `roguePair (valid true) nullRawDeref` evaluates `[(_, _)]` to `.matchedArm 0` vs. `[]` to `.ubUnreachable`; on `&Result<bool, !>`, `[&Ok(_)]` is rejected while `[&Ok(_), &Err(!)]` is accepted and traps `.rogueRef .rogueErrTag` with `.ubInvalidDiscrRead`. | `[propext]` |
| **`ce3_wildcard_star_null_never_succeeds_while_empty_match_faults`** | On `.never` + `.maybeInvalid`: `[]` is accepted via `is_toplevel_exception`, `[wildArm]` succeeds (`.matchedArm 0`), `[]` and `[neverArm]` fault (`.ubUnreachable`), and `evalMatchPlace [wildArm] ≠ evalMatchPlace []`. | `[propext]` |
| **`ce4_never_pattern_on_inhabited_variant_rejected`** | `Some(!)` on `Option<bool>` is rejected (`checkPatWellFormed = false`, `armWellFormed = false`), `Err(!) => body` is rejected (`armWellFormed = false`), and wrongly admitting `Some(!)` would fault `.ubUnreachable` on `Some(true)`. | `[propext]` |
| **`ce5_private_uninhabited_field_hidden_outside_module`** | `PrivEmpty = (priv !, pub bool)` in `Result<bool, PrivEmpty>`: `Ok(_)` alone is accepted inside (`inMod = true`) and rejected outside (`inMod = false`). | `[propext]` |
| **`ce6_foreign_non_exhaustive_empty_enum_blocks_empty_match`** | `#[non_exhaustive] enum ForeignEmpty {}`: `isNoConstructors` and empty `match x {}` hold inside (`inMod = true`) and fail outside (`inMod = false`). | `[propext]` |

#### Kernel Verification & Purity Receipt (`support/lean_check_receipt.json`)

Executed via `python3 support/check_lean.py` using Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with flags `["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]`:

| Metric / Invariant | Observed Value |
| :--- | :--- |
| Source LOC / bytes / SHA-256 | `2,570` lines / `122,894` bytes / `efabb0ba0568dfd7ecc8052e616265012218c7fc349f28a68d9b6a64c554297b` |
| Source declarations | `86` `theorem`, `49` `def`, `16` `inductive`, `4` `structure` |
| Kernel `env.constants.toList` (`NeverPatternsSoundness.*`) | `914` total constants (`309` `thmInfo`, `475` `defnInfo`), **`0` `isUnsafe`**, **`0` `isPartial`**, **`0` `._unsafe_rec` helpers**, **`0` `user_axioms`** |
| Banned source tokens (comments stripped) | `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `unsafe def`, `0` `deriving`, `0` `axiom `, `0` `opaque `, `0` `_unsafe_rec` |
| Transitive axiom footprint (all 11 major theorems) | Strictly subset of `{propext, Quot.sound}`; `forbidden_axioms_present: false` |
| Wall-clock time & Max RSS | `11.9247 s`, `700,392 KiB` (`all_checks_passed: true`) |

---

## Boundaries

The following negative-space boundaries separate established findings from untested, unresolved, non-applicable, or unsupported cases:

1. **Not examined:**
   - **Live execution of `rust-lang/rust` `HEAD` (`01afe534803b93889b85f6028117251cfbd431da`) or a fresh local `1.102.0-nightly` binary:** Live compiler and `Miri` execution in `support/probe_never_patterns_postfix_match_and_exhaustiveness.json` ran on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), cross-checked against the retained `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) receipt and full primary-source diffs against `3ef0c22cd` and `01afe5348`. Extended cases added beyond the original `7+3` matrix (`np_01b`, `np_02b`, `np_02c`, `np_04b`, `np_05b`, `np_06b`, `np_06c`, `np_07a`, `np_07b`, `np_07c`, `np_07d`, `np_07f`, `foreign_non_exhaustive_empty_enum`, and Miri cases 4–13) were executed live on `1.98.0-nightly` only; continuity to `3ef0c22cd` and `01afe5348` is derived from source-level identity of `usefulness.rs`, `builder/matches/`, `discriminant.rs`, `place.rs`, and `validity.rs`.
   - **LLVM codegen / backend lowering of `TerminatorKind::Unreachable` and `noundef` / `unreachable` IR attributes:** This report stops at MIR (`built` through default `--emit=mir` and `-Zmir-preserve-ub`) and `Miri` operational semantics; LLVM IR / machine-code exploitation of `unreachable` or `!` ABI lowering was not examined.
   - **Edition 2024 temporary-lifetime changes for non-`match` constructs (`if let`, tail expressions, `while let`):** Only `match` (prefix and postfix) temporary drop order was probed across Editions 2021 and 2024; `if let` and block tail-expression temporary shortening (`destructors.scope.temporary.edition2024`) were not examined here.
   - **Deref patterns (`#![feature(deref_patterns)]`), opaque types (`impl Trait` revealing `!`), and `const` / CTFE pattern matching:** `PlaceValidity::specialize` handles `Constructor::DerefPattern(_)` identically to `Constructor::Ref` in source (`usefulness.rs:905`), and `is_uninhabited` calls `apply_revealing_opaque` (`rustc.rs:158`), but neither `#![feature(deref_patterns)]` nor CTFE evaluation of never patterns was executed in this study.
   - **Non-64-bit targets and `unsafe` mutable reference aliasing (`&mut !` / Tree Borrows vs. Stacked Borrows):** All executions targeted `x86_64-unknown-linux-gnu` under Miri's default aliasing model without `-Zmiri-tree-borrows`.
2. **Unknown (unresolved upstream design questions):**
   - **Exact future runtime semantics of `TestKind::Never` (`test.rs:319`):** Upstream `compiler/rustc_mir_build/src/builder/matches/test.rs:319` explicitly carries `// FIXME(never_patterns): Also assert validity of the data at place`. Whether a future stabilization of `never_patterns` will emit an explicit runtime validity assertion / `PlaceMention` on sub-places in addition to `FakeRead` + `TerminatorKind::Unreachable` remains unresolved upstream.
   - **Normative reference validity on uninhabited pointees:** `rust-lang/reference` (`behavior-considered-undefined.md:152`) explicitly marks whether a reference must point to a valid value as *"a subject of some debate"*, leaving an active tension between `check_match.rs:1350` (*"references are always considered inhabited"*) and `Miri`'s `validity.rs:700-707` (`is_opsem_inhabited` immediate UB on `&HasNever`).
3. **Known not to apply:**
   - **Wildcard `PlaceMention(*p)` UB-freedom does NOT apply to `&!`, `Box<!>`, or unsized `*const dyn Trait`:** `place.rs:483-534` enforces non-null, dereferenceability, and alignment on references and `Box`es, and checks vtable validity on unsized `dyn Trait` raw pointers; `wildcard_match_star_null` (`rc=0`) applies specifically to **sized raw pointers** (`*const !`).
   - **`is_toplevel_exception` (`match *p {}`) does NOT apply to product types with uninhabited fields (`*const HasNever`):** Verified live in `np_05b` (`E0004`) and mechanized in `ce2`; `is_toplevel_exception` applies solely to `ConstructorSet::NoConstructors` (`!` and local non-`#[non_exhaustive]` zero-variant enums).
   - **`-Zmir-preserve-ub` does NOT preserve ZST `PlaceMention((*_1))` at `-Zmir-opt-level >= 1`:** Verified live in `np_05` (`preserve_ub_opt0_has_place_mention = true`, `preserve_ub_opt1_has_place_mention = false`) because `RemoveZsts` (`remove_zsts.rs:13, 124`) runs unconditionally at `mir_opt_level >= 1`.
   - **The Lean mechanization is NOT linked directly to `joshlf/anneal`'s `Trusted.MirSemantics`:** `support/NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean` is a standalone, self-contained `Init`-only model (`0` external imports). Its `MiniMirBody` / `miniBodyVerifiedAnneal` theorem models the exact vacuity structure of `Trusted/MirSemantics.lean:1715-1758, 2513-2600` rather than importing `Trusted.MirSemantics` directly.
4. **Unsupported:**
   - **`#![feature(guard_patterns)]` runtime guard evaluation and sub-pattern binding initialization:** Explicitly unimplemented (`// FIXME(guard_patterns)`) in `match_pair.rs:457-460` and unsoundly lowered in `rustc.rs:471-472` across all three examined `rust-lang/rust` revisions (`14210df0e`, `3ef0c22cd`, `01afe5348`).
   - **Anneal `Trusted.MirAst` support for `StatementKind::FakeRead` and `StatementKind::PlaceMention`:** Both fail closed to `StatementKind.unsupported` in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirAst.lean:636-662`).
   - **Lean `v4.34.1` code generation for explicit kernel recursors (`Ty.rec`, `Pat.rec`):** Lean's runtime code generator rejects raw `.rec` calls in computable `def`s (`code generator does not support recursor ... yet`), which is why zero-`_unsafe_rec` recursive specifications over custom inductives require `noncomputable def` (accepted by `TrustedBoundary.lean:475` with zero axiom cost).

---

## Evidence

### Primary-Source Citations

All upstream commit SHAs were resolved live on `2026-11-22` via authenticated GitHub API lookups, and all cited files were fetched and inspected directly.

| Repository & Commit | Path & Symbol / Line Range | Key Observed Fact |
| :--- | :--- | :--- |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`) | `compiler/rustc_feature/src/unstable.rs:666` | `(unstable, never_type, "1.13.0", Some(35121))` — *"Does not imply `exhaustive_patterns` (below) any more."* |
| `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`) & `01afe534803b93889b85f6028117251cfbd431da` (`HEAD`, `2026-11-22`) | `compiler/rustc_feature/src/accepted.rs:320, 339` | `min_exhaustive_patterns` accepted `"1.82.0"`; `never_type` accepted `"1.100.0"`. |
| `rust-lang/rust` @ `3ef0c22cd` & `01afe5348` | `compiler/rustc_feature/src/unstable.rs:517, 591, 682, 702` | `exhaustive_patterns` (`unstable`), `guard_patterns` (`incomplete`, `#129967`), `never_patterns` (`incomplete`, `#118155`), `postfix_match` (`unstable`, `#121618`). |
| `rust-lang/rust` @ `01afe5348` (and `3ef0c22cd`) | `compiler/rustc_pattern_analysis/src/rustc.rs:157-164, 230-256, 306-395, 437, 464-472, 696-703, 900` | `is_uninhabited` (`inhabited_predicate` at `self.module`), `ctor_sub_tys` (`PrivateUninhabitedField(skip)`), `ctors_for_ty` (`is_foreign_non_exhaustive_enum`), `PatKind::Guard => lower_pat(subpat)` defect (`L472`), `PatKind::Never => Wildcard` (`L696`), `ty::View(..)` stub (`L437`, HEAD only). |
| `rust-lang/rust` @ `01afe5348` (byte-identical to `3ef0c22cd`) | `compiler/rustc_pattern_analysis/src/usefulness.rs:757, 842-985, 1698-1720` | `PlaceValidity::{ValidOnly, MaybeInvalid}`, `specialize` (`Ref`/`DerefPattern`/`UnionField` -> `MaybeInvalid`), `split_column_ctors` (`PrivateUninhabited` skip, `is_toplevel_exception`, `can_omit_empty_arms`), `is_under_guard` opacity (`L757, 1720`). |
| `rust-lang/rust` @ `01afe5348` | `compiler/rustc_pattern_analysis/src/constructor.rs:760-763, 985, 1079-1215` | `ConstructorSet::{NoConstructors, Struct { empty }, Variants { non_exhaustive }}` and `Constructor::{NonExhaustive, PrivateUninhabited}`. |
| `rust-lang/rust` @ `01afe5348` (and `3ef0c22cd`) | `compiler/rustc_mir_build/src/thir/pattern/check_match.rs:290-365, 512, 591-594, 908-918, 986, 1043, 1350` | `is_known_valid_scrutinee` (`Deref`/`UnionField` -> `false`), `MatchArm.has_guard`, `check_never_pattern` (`NonEmptyNeverPattern`), `"references are always considered inhabited"` (`L1350`). |
| `rust-lang/rust` @ `01afe5348` (byte-identical to `3ef0c22cd`) | `compiler/rustc_mir_build/src/builder/matches/{mod.rs:374-386,1621-1649; match_pair.rs:457-466; test.rs:59,317-329}` | `lower_scrutinee` (`PlaceMention`), `otherwise_block` (`FakeRead` + `Unreachable`), `PatKind::Guard` empty `Irrefutable` stub (`match_pair.rs:457-460`), `PatKind::Never` -> `TestKind::Never` -> `FakeRead` + `Unreachable` + `FIXME(never_patterns)` (`test.rs:319`). |
| `rust-lang/rust` @ `01afe5348` | `compiler/rustc_ast_lowering/src/expr.rs:351-358, 793-843`; `compiler/rustc_hir_typeck/src/pat.rs:587, 767`; `compiler/rustc_hir_analysis/src/check/region.rs:657-661` | `MatchKind::Postfix => MatchSource::Postfix`, `NeverPatternWithBody`/`NeverPatternWithGuard` + fake `loop {}` body synthesis, `PatKind::Never` `AdjustMode::peel_all()`, `MatchSource`-agnostic drop/temp scopes in `region.rs:657`. |
| `rust-lang/rust` @ `01afe5348` | `compiler/rustc_mir_transform/src/{lib.rs:645,687,732; cleanup_post_borrowck.rs:28-64; remove_place_mention.rs:13; remove_zsts.rs:13,124,143-148}` | Exact pass schedule erasing `FakeRead`, `PlaceMention` (gated on `!mir_preserve_ub`), and ZST `PlaceMention` (`mir_opt_level >= 1`). |
| `rust-lang/rust` @ `01afe5348` | `compiler/rustc_const_eval/src/interpret/{step.rs:119,704; place.rs:468-536; discriminant.rs:70-77,214-216,256; validity.rs:700-707}` | Miri execution of `PlaceMention`, `Unreachable`, `deref_pointer` raw-ptr vs. ref/box split, `UninhabitedEnumVariantRead`, and `is_opsem_inhabited` on references. |
| `rust-lang/rust` @ `01afe5348` | `tests/ui/rfcs/rfc-0000-never_patterns/never-pattern-is-a-read.rs:1-14` | Upstream UI test confirming `let U { a: ! } = u;` triggers union-read unsafety (`E0133`). |
| `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`2026-11-17`) | `src/types/never.md:4-59`, `src/behavior-considered-undefined.md:19,58-59,83-159`, `src/expressions/match-expr.md:133-247`, `src/destructors.md:55-118,164-165,261-350`, `src/patterns.md:641-642` | Normative specification of `!`, invalid values, misaligned/dangling places, match guards, range-pattern irrefutability, and match drop/temporary scopes. |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) | `trusted/lean/Trusted/MirAst.lean:296,316,636-662,776,789`; `trusted/lean/Trusted/MirSemantics.lean:1551-1552,1715-1758,2513-2600`; `trusted/rustc-capture/src/driver.rs:25`; `trusted/audit/TrustedBoundary.lean:475,1119,1763-1774,2143-2167` | Anneal's pinned `1.98.0-nightly` driver, `MirTy.never`, `TerminatorKind.unreachable -> .fault .undefined`, fail-closed `FakeRead`/`PlaceMention`, `BodyStaticAdmitted` vacuity guard (`canaryNeverParamBody`), and `TrustedBoundary` noncomputable / zero-`isPartial` rules. |

### Preserved Support Artifacts

All evidence and verification scripts are preserved inside this report package under `support/`:

| Artifact Path | Size & Lines | SHA-256 Digest | Purpose & Verification Role |
| :--- | :--- | :--- | :--- |
| `support/probe_never_patterns_postfix_match_and_exhaustiveness.py` | `28,314` B / `969` L | `e2dc9a5e63687a38c4c4d678d1a5fd14584852e2525a682307ec46657c88c88c` | Self-contained Python 3 harness running all `16` compiler/MIR cases (including `-Zdump-mir=all`, `-Zmir-opt-level=0/1 -Zmir-preserve-ub`), `1` cross-crate `#[non_exhaustive]` case, and `13` `Miri` cases. |
| `support/probe_never_patterns_postfix_match_and_exhaustiveness.json` | `39,411` B / `249` L | `b2edecac93d51a78e92ad45751faefff0e8952a114012fdd7f24bf73ddb50858` | Live execution output recorded on `2026-11-22` against `rustc 1.98.0-nightly (14210df0e 2026-05-31)` + `Miri` (all paths normalized to `<tmp>`/`<home>`). |
| `support/NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean` | `122,894` B / `2,570` L | `efabb0ba0568dfd7ecc8052e616265012218c7fc349f28a68d9b6a64c554297b` | Standalone `Init`-only Lean `v4.34.1` mechanization (`86` theorems, `49` defs, `16` inductives, `4` structures, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, `0` `isPartial`, `0` `isUnsafe`). |
| `support/check_lean.py` | `10,712` B / `276` L | `5e4706083bfd9a05917beb4968657f8ff2188fac55152ef4e4b75f4a68e5e05c` | Reproducible Lean kernel + source-token + `env.constants.toList` + `#print axioms` auditor writing `support/lean_check_receipt.json`. |
| `support/lean_check_receipt.json` | `2,327` B / `51` L | `86e3a1bfdabc2582a6ad8fe6a4a354cb21d89c745c9c8ed15a2a411f1fe30f00` | Live kernel-check and purity audit receipt (`all_checks_passed: true`, `914` namespace constants, `0` `._unsafe_rec`, `11.9247 s`, `700,392 KiB`). |

### Complete Live Compiler & Cross-Crate Execution Summary (`1.98.0-nightly` vs. Retained `1.102.0-nightly`)

| Probe Case | `1.98.0-nightly` (`14210df0e`, live `2026-11-22`) | `1.102.0-nightly` (`3ef0c22cd`, retained `2026-11-11` toolchain) | Differential Note |
| :--- | :--- | :--- | :--- |
| `np_01_never_pattern_in_result_ok_and_err_never` | `rc=0`, `run_rc=0`, `UNWRAP=42`, 1 warning (`incomplete_features`) | `rc=0`, `run_rc=0`, `UNWRAP=42`, 2 warnings (`incomplete_features` + `stable_features` on `never_type` since `1.100.0`) | Exact stabilization delta |
| `np_01b_by_value_omit_err_min_exhaustive` | `rc=0`, `run_rc=0`, `MIN_EXHAUSTIVE=42`, 0 warnings (no `#![feature]`) | N/A (extended case) | `min_exhaustive_patterns` stable since `1.82.0` |
| `np_02_never_pattern_behind_shared_ref_requires_deref_read` | `rc=0`, default MIR: `discriminant((*_1)); switchInt -> [0: bb2, otherwise: bb1]; bb1: unreachable;`; `built` has `PlaceMention(_1)` + `FakeRead((((*_1) as Err).0: !))`; `-Zmir-preserve-ub` keeps `PlaceMention(_1)` at both `-O0` and `-O1` | `rc=0`, identical default MIR (`has_place_mention=false`, `has_fake_read=false`, `has_unreachable=true`), plus `stable_features` warning | Identical MIR |
| `np_02b_ref_result_omit_err_rejected` | `rc=1`, `E0004` (`&Err(!)` not covered; suggests `&Err(!),`) | N/A (extended case) | Proves `PlaceValidity::MaybeInvalid` across `Constructor::Ref` |
| `np_02c_ref_result_omit_err_exhaustive_patterns` | `rc=0`, identical default MIR to `np_02` | N/A (extended case) | `exhaustive_patterns` overrides `PlaceValidity::MaybeInvalid` |
| `np_03_never_pattern_on_inhabited_type_rejected` | `rc=1`, `a never pattern must be used on an uninhabited type` (`u32`) | `rc=1`, identical diagnostic | Identical |
| `np_04_never_pattern_with_arm_body_rejected` | `rc=1`, `a never pattern is always unreachable` (`help: remove this expression`) | `rc=1`, `a never pattern is always unreachable` (`help: remove the match arm body, leaving only the pattern`) | Help wording refined; error identical |
| `np_04b_never_pattern_with_guard_rejected` | `rc=1`, `a guard on a never pattern will never be run` | N/A (extended case) | `NeverPatternWithGuard` (`expr.rs:824`) |
| `np_05_raw_ptr_empty_match_vs_never_pattern_deref` | `rc=0`; default MIR: `empty_match_raw_never` & `explicit_never_pat_raw_never` (with dead `_2: !, _3: ()`) -> `bb0: unreachable;`, `wildcard_match_raw_never` -> `bb0: _0 = const 99_u32; return;`; `-Zmir-preserve-ub` keeps `PlaceMention((*_1))` at `-O0` (`true`) but `RemoveZsts` erases it at `-O1` (`false`) | `rc=0`, identical `empty_match_raw_never` & `explicit_never_pat_raw_never` MIR (including dead locals `_2: !, _3: ()`), plus `stable_features` warning | Identical MIR |
| `np_05b_hasnever_raw_ptr_empty_match_rejected` | `rc=1`, `E0004` (`type 'HasNever' is non-empty`) | N/A (extended case) | `Struct { empty: true }` excluded from `is_toplevel_exception` |
| `np_06` / `np_06b` / `np_06c` (`postfix_match` Ed. 2024, Ed. 2021, prefix Ed. 2024) | All 3: `rc=0`, `run_rc=0`, `RES=15 LOG=["make", "arm_body", "drop_inner", "after_match"]` | `np_06`: `rc=0`, `run_rc=0`, identical `RES=15 LOG=[...]` | Exact equivalence across syntax & editions |
| `np_07a_arm_guard_opaque_to_exhaustiveness` | `rc=1`, `E0004` (`Some(_)` not covered; `match arms with guards don't count towards exhaustivity`) | N/A (extended case) | Traditional arm guards sound |
| `np_07b_guard_patterns_live_defect_and_int_ranges` | `rc=0`, false `unreachable pattern` on `Some(_)`, **`GUARD_NEG=pos`** (`RANGE_0=hit RANGE_255=hit`) | Source-verified identical defect (`rustc.rs:472` + `match_pair.rs:459`) | Live soundness & miscompilation defect |
| `np_07c_guard_patterns_omits_e0004_and_drops_binding` | `rc=1`, **no `E0004`**, fails borrowck `E0381` (`used binding 'n' isn't initialized`) | Source-verified identical defect (`rustc.rs:472` + `match_pair.rs:459`) | Confirms dropped guard + dropped binding |
| `np_07d_private_uninhabited_field_inside_vs_outside` | Inside `mod inner`: `rc=0`; outside: `rc=1`, `E0004` (`Err(_)` not covered) | N/A (extended case) | Confirms `PrivateUninhabitedField` |
| `np_07f_never_pattern_uninit_and_union_read` | `rc=1`, `E0381` (uninit `x: !`) + `E0133` (unsafe union field `U { a: ! }`) | N/A (extended case) | Confirms `TestKind::Never` `FakeRead` |
| `foreign_non_exhaustive_empty_enum` (cross-crate) | `dep`: `rc=0`; `client`: `rc=1`, `E0004` (`type 'ForeignEmpty' is non-empty`, marked `non-exhaustive`) | N/A (extended case) | Confirms `Constructor::NonExhaustive` |

---

## Revalidation

Use the following narrow, cheap discriminating checks to determine whether any finding in this report has changed on a newer `rustc`, `Miri`, `joshlf/anneal`, or `Lean` release:

1. **Re-execute the `rustc` + `Miri` differential probe (`~10–25 s`):**
   ```bash
   python3 support/probe_never_patterns_postfix_match_and_exhaustiveness.py \
     --out /tmp/reval_never_patterns.json
   ```
   Inspect the output JSON for five discriminating sentinels:
   - **`never_type` / feature-gate shifts:** Whether `np_01` emits `#[warn(stable_features)]` for `never_type` (true on `1.100.0+`), or whether `never_patterns`, `guard_patterns`, or `postfix_match` lose their `incomplete_features` / feature-gate requirements.
   - **Fix of the `#![feature(guard_patterns)]` defect:** `np_07b` will stop warning `unreachable pattern` on `Some(_)` and will change from `GUARD_NEG=pos` to `GUARD_NEG=nonpos`, while `np_07c` will change from `error_codes: ["E0381"]` to `error_codes: ["E0004"]`.
   - **Resolution of `FIXME(never_patterns)` (`test.rs:319`) or `RemoveZsts` (`remove_zsts.rs:124`):** Check `np_02` and `np_05` MIR snapshots (`mir_built_after`, `mir_preserve_ub_opt0`, `mir_preserve_ub_opt1`) for new validity checks or survival of ZST `PlaceMention((*_1))` at `-Zmir-opt-level=1`.
   - **`Miri` reference-validity or raw-pointer-deref changes:** Check whether `wildcard_match_star_null` remains `rc=0` (`WILDCARD_NULL_OK=99`), whether `rogue_tagged_*` still faults with `UninhabitedEnumVariantRead`, and whether `rogue_hasnever_shared_ref_*` still faults at reference creation (`is_opsem_inhabited`).
   - **Postfix match temporary drop order:** Verify `np_06`, `np_06b`, and `np_06c` remain identical (`RES=15 LOG=["make", "arm_body", "drop_inner", "after_match"]`).

2. **Narrow upstream `rust-lang/rust` source diff (`<5 s`):**
   Diff the exact eight determining source paths from `01afe534803b93889b85f6028117251cfbd431da` to the new target commit:
   ```bash
   git diff 01afe534803b93889b85f6028117251cfbd431da..HEAD -- \
     compiler/rustc_feature/src/{accepted,unstable}.rs \
     compiler/rustc_pattern_analysis/src/{rustc,usefulness,constructor}.rs \
     compiler/rustc_mir_build/src/thir/pattern/check_match.rs \
     compiler/rustc_mir_build/src/builder/matches/{mod,match_pair,test}.rs \
     compiler/rustc_mir_transform/src/{cleanup_post_borrowck,remove_place_mention,remove_zsts}.rs \
     compiler/rustc_const_eval/src/interpret/{step,place,discriminant,validity}.rs
   ```
   A zero diff across these files guarantees that all compiler-architecture findings in §§1–7 remain unchanged.

3. **Re-verify the Anneal trusted boundary seam (`<5 s`):**
   Diff `joshlf/anneal` from `c131b320eeeb26ef692e5afd5ec8db49ee518613` over `trusted/lean/Trusted/MirAst.lean` (`StatementKind`, `MirTy.never`, `TerminatorKind.unreachable`), `trusted/lean/Trusted/MirSemantics.lean` (`BodyStaticAdmitted`, `BodyVerified`, `canaryNeverParamBody`), and `trusted/rustc-capture/src/driver.rs` (`COMPILER_VERSION`). If Anneal adopts `-Zmir-preserve-ub` or upgrades `COMPILER_VERSION` past `1.100.0`, re-check whether `StatementKind.placeMention` is modeled explicitly and whether `MirTy.never` capture handles stabilized `!` types.

4. **Re-verify the Lean `v4.34.1` mechanization and purity invariants (`~12 s`):**
   ```bash
   python3 support/check_lean.py
   ```
   Confirm `all_checks_passed: true`, `0` `sorry`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `is_unsafe`, `0` `is_partial`, `0` `unsafe_rec_helpers`, and `0` `user_axioms`.
