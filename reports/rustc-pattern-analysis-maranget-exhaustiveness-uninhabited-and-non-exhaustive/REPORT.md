# Maranget Pattern Analysis, Uninhabited Exhaustiveness, References, Guards, and Cross-Crate `#[non_exhaustive]` in `rustc`

## Summary

Basis: source + execution + derived (mechanized Lean 4 proofs).

`rustc` performs pattern exhaustiveness checking and redundant-arm (`unreachable_patterns`) analysis via a modified Maranget usefulness matrix algorithm implemented in `compiler/rustc_pattern_analysis` and driven on THIR patterns by `compiler/rustc_mir_build/src/thir/pattern/check_match.rs`, while missing `..` wildcards on foreign `#[non_exhaustive]` structs and struct-like variants are rejected earlier during HIR pattern type checking in `compiler/rustc_hir_typeck/src/pat.rs`. Four structural invariants govern correctness across edge cases:

1. **Uninhabited matching depends orthogonally on place validity (`PlaceValidity`), top-level scrutinee status (`is_scrutinee`), constructorless emptiness (`ConstructorSet::NoConstructors`), and `#![feature(exhaustive_patterns)]`:**
   - By-value matches on uninhabited types (`Void`, `!`, `Result<u32, Void>`, `Result<u32, !>`) start with `PlaceValidity::ValidOnly`, so empty constructors are omitted (`can_omit_empty_arms = true`) and dead arms are unreachable in MIR (`-Copt-level=1` `UnreachablePropagation` and `MatchBranchSimplification` collapse `unwrap_void_res` to `_2 = discriminant(_1); _4 = Eq(copy _2, const 0_isize); assume(move _4);`).
   - Dereferencing a reference (`match *r {}` or `match *r { Ok(x) => x }` for `r: &Result<u32, Void>`) sets `PlaceValidity::MaybeInvalid` (`is_known_valid_scrutinee` returns `false` on `ExprKind::Deref`). An empty match directly on `*r` where `r: &Void` (`is_scrutinee = true`, `ConstructorSet::NoConstructors`) succeeds solely through the special `is_toplevel_exception` rule (`usefulness.rs:953-966`), whereas matching `*r` on `&Result<u32, Void>` recurses into field `Err.0` (`is_scrutinee = false`, `validity = MaybeInvalid`) and **rejects with `E0004`** (`Err(_)` not covered) unless `#![feature(exhaustive_patterns)]` is enabled.
   - References themselves have `ConstructorSet::Ref` regardless of pointee uninhabitedness, and `PlaceValidity::specialize(Constructor::Ref)` resets sub-place validity to `MaybeInvalid` (`usefulness.rs:868-877`). Consequently `match r {}` on `r: &Void` **always fails with `E0004`** (`note: references are always considered inhabited`) even under `#![feature(exhaustive_patterns)]`.
2. **Privacy hides uninhabited fields (`Constructor::PrivateUninhabited`) without hiding `#[non_exhaustive]` struct `..` obligations (`E0638` vs `E0004`):**
   - Outside a struct's defining module, `RustcPatCtxt::ctor_sub_tys` marks an inaccessible uninhabited field with `PrivateUninhabitedField(true)` (`rustc.rs:251-255`), and `PlaceInfo::split_column_ctors` short-circuits that column to `Constructor::PrivateUninhabited` (`usefulness.rs:939-942`), preventing callers from proving `match p {}` exhaustive while allowing `match p { inner::Priv { tag: 0..=255, .. } => 1 }` once visible fields are covered.
   - Across crates, `#[non_exhaustive]` on an `enum` (even a single-variant enum or a foreign empty enum) sets `ConstructorSet::Variants { non_exhaustive: true, .. }`, injecting `Constructor::NonExhaustive` into `missing` so downstream matches without `_` fail with `E0004` (`_ not covered`), while upstream matches inside the defining crate check `is_foreign_non_exhaustive_enum` (`VariantListHasApplicableNonExhaustive`) as `false` and accept exhaustive variant matches without `_`. By contrast, `#[non_exhaustive]` on a `struct` (even with all `pub` fields) or on an `enum` struct-variant is enforced by HIR type checking via `error_foreign_non_exhaustive_spat` (`E0638`: `` `..` required with struct/variant marked as non-exhaustive ``), before THIR pattern analysis runs.
3. **Guards never establish exhaustivity and never shadow later arms, while overlapping integer ranges compose collectively (`unreachable_patterns`) and `usize::MAX`/`isize` remain open-ended:**
   - `MatrixRow::new` propagates `is_under_guard: arm.has_guard`; at a 0-column leaf, `compute_exhaustiveness_and_usefulness` updates `useful &= row.is_under_guard` (`usefulness.rs:1726`). Because guarded rows leave `useful = true` for subsequent rows and for the virtual exhaustiveness row, logically complementary guarded arms (`n if n >= 0` / `n if n < 0`, or `true if flag` / `false if !flag`) still fail with `E0004` (`match arms with guards don't count towards exhaustivity`).
   - `ConstructorSet::Integers` splits overlapping intervals via `IntRange::split` so arms `0..=10` and `5..=15` collectively mark a later arm `7` redundant (`unreachable_patterns`: `collectively making this unreachable`). Meanwhile `usize` and `isize` map `MAX`/`MIN` boundaries to `PosInfinity`/`NegInfinity` (`rustc.rs:176-186, 331-358`), causing `0..=usize::MAX` to fail `E0004` (`usize::MAX.. not covered`).
4. **Mechanized kernel verification (`Lean v4.34.1`)**:
   - The standalone formalization in `support/PatternAnalysisMarangetExhaustivenessSoundness.lean` (`6,340` lines, `978` local declarations, `299` kernel theorems, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `_unsafe_rec` constants) establishes bidirectional soundness and completeness of Maranget's specialization matrix under both `.validOnly` and `.maybeInvalid`, witness soundness, uninhabited constructor omission, `&Void` inhabitedness, cross-crate `#[non_exhaustive]` wildcard necessity, private uninhabited field hiding, guard over-approximation equivalence, and collective range shadowing.

## Applicability

This report characterizes pattern exhaustiveness, usefulness checking, HIR `#[non_exhaustive]` field enforcement, post-pattern MIR lowering, and mechanized proof correspondence across the following concrete pinned subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`)**:
   - Directly executed for all `support/probe_pattern_analysis_exhaustiveness.py` compilation tests, runtime outputs, and MIR dumps (`support/probe_results.json`), and directly audited across `compiler/rustc_pattern_analysis/src/{usefulness.rs, constructor.rs, rustc.rs, pat.rs}`, `compiler/rustc_mir_build/src/thir/pattern/check_match.rs`, and `compiler/rustc_hir_typeck/src/pat.rs`.
2. **`rust-lang/rust` at `49d734536222bf28bb6d07d885b3a81d145981da` and `main` at `960ba7cf7e8666ecb449402ca82b6e9e631bd227`**:
   - Primary-source comparison baselines. Direct diffs of `usefulness.rs` and `constructor.rs` establish that `usefulness.rs` at `49d734536` and `960ba7cf` share the exact blob SHA `1f19bfd73289` and preserve identical `PlaceInfo::split_column_ctors`, `MatrixRow::new`, `PlaceValidity`, and `compute_exhaustiveness_and_usefulness` semantics relative to `14210df0e` (blob `bf236b7737d9`, which differs only in `ensure_sufficient_stack` wrapping), while `constructor.rs` (`0f636f323e5f` vs `6f07e922ceef`) differs only in dropping `#![feature(never_type)]` from two doctests and switching one internal error in `is_covered_by` from `cx.bug` to `cx.delayed_bug`.
3. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`main`) and `da6917c5cc574a4e06543576b9508c5221467bd1` (`unstable`)**:
   - Inspected in `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/rustc-capture/src/driver.rs`, and `trusted/audit/TrustedBoundary.lean` to determine exact compatibility seams between `rustc` exhaustiveness/MIR lowering and Anneal's MIR semantics and kernel proof hygiene rules.
4. **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`Lean v4.34.1`, `x86_64-unknown-linux-gnu`)**:
   - Kernel-checked `support/PatternAnalysisMarangetExhaustivenessSoundness.lean` cleanly with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and audited all declarations with Lean MetaM.

**Scope of extension:** Findings for other Rust toolchains matching the same `rustc_pattern_analysis` matrix rules (`PlaceValidity`, `ConstructorSet`, `is_toplevel_exception`, `is_under_guard`) generalize only insofar as their `usefulness.rs`, `constructor.rs`, and `check_match.rs` implementations match those documented here; exact MIR pass formatting (`-Zdump-mir`) or diagnostic wording may vary across `rustc` releases. In addition, the formal theorems in `support/PatternAnalysisMarangetExhaustivenessSoundness.lean` are proved directly for an explicit deep embedding modeling core `rustc_pattern_analysis` types and operators, not extracted from or compiled against the Rust compiler crates themselves.

## Findings

### 1. Maranget Matrix Specialization, Place Validity, and Witness Unspecialization

Basis: source + derived.

In `compiler/rustc_pattern_analysis/src/usefulness.rs` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `compute_match_usefulness` (`1835–1890`) initializes a `Matrix` (`Matrix::new`, `1239–1255`) with a single root column whose `PlaceInfo` carries four fields (`892–902`):

- `ty: Cx::Ty`: revealed type of the place (`rustc.rs:135-146` unwraps opaque `impl Trait` types when revealed in the body).
- `private_uninhabited: bool`: `false` at the root scrutinee; set per subfield during specialization by `RustcPatCtxt::ctor_sub_tys` (`rustc.rs:230-281`).
- `validity: PlaceValidity`: initialized at root via `PlaceValidity::from_bool(tycx.known_valid_scrutinee())` (`rustc.rs:1076`, reading `is_known_valid_scrutinee` from `check_match.rs:293-368`).
- `is_scrutinee: bool`: `true` at the root match scrutinee (`Matrix::new`), reset to `false` on every specialized subplace (`PlaceInfo::specialize`, `usefulness.rs:914-919`).

Every match arm enters the matrix via `MatrixRow::new` (`1143–1153`):

```rust
fn new(arm: &MatchArm<'p, Cx>, arm_id: usize) -> Self {
    MatrixRow {
        pats: PatStack::from_pattern(arm.pat),
        parent_row: arm_id,
        is_under_guard: arm.has_guard,
        useful: false,
        intersects_at_least: DenseBitSet::new_empty(0),
        head_is_branch: true,
    }
}
```

At each recursive call to `compute_exhaustiveness_and_usefulness` (`1704–1798`):

1. **Base case (`matrix.head_place()` is `None`, i.e., zero columns remain, `1717–1736`):**
   - The algorithm iterates sequentially over the surviving specialized rows with a boolean accumulator `useful = true`:
     ```rust
     let mut useful = true; // Whether the next row is useful.
     for (i, row) in matrix.rows_mut().enumerate() {
         row.useful = useful;
         row.intersects_at_least.insert_range(0..i);
         // The next rows stays useful if this one is under a guard.
         useful &= row.is_under_guard;
     }
     return if useful && matrix.wildcard_row_is_relevant {
         Ok(WitnessMatrix::unit_witness())
     } else {
         Ok(WitnessMatrix::empty())
     };
     ```
   - An arm at this leaf is useful iff **no unguarded arm sits above it**. An unguarded row extinguishes `useful` (`true && false == false`), making all lower rows at that leaf redundant and returning `WitnessMatrix::empty()`. Any sequence consisting solely of guarded rows leaves `useful = true`, returning `WitnessMatrix::unit_witness()` (whenever `wildcard_row_is_relevant` holds).

2. **Recursive column split (`PlaceInfo::split_column_ctors`, `usefulness.rs:930–1006`):**
   - When columns remain, `split_column_ctors` inspects the head pattern constructors in column 0 in strict precedence order:
     1. If `self.private_uninhabited` is `true`, it skips the entire column immediately by returning `(smallvec![Constructor::PrivateUninhabited], vec![])` (`939–942`).
     2. If any head constructor is `Constructor::Or`, it returns `(smallvec![Constructor::Or], vec![])` (`944–947`), expanding or-patterns into separate rows via `MatrixRow::expand_or_pat` (`1168–1178`). Note that `expand_or_pat` preserves `self.is_under_guard` on every expanded row.
     3. Otherwise, it queries `ctors_for_ty(&self.ty)` (`rustc.rs:306-436`) and splits the `ConstructorSet` via `ConstructorSet::split(ctors)` (`constructor.rs:1046-1205`) into `SplitConstructorSet { present, missing, missing_empty }` (`constructor.rs:1035-1039`).
   - Crucially, `SplitConstructorSet` distinguishes non-empty missing constructors (`missing`) from zero-inhabitant missing constructors (`missing_empty`) and maintains seven explicit invariants documented in `constructor.rs:1018-1029`:
     - `present ∪ missing ∪ missing_empty` partitions all constructors of the type;
     - every `c ∈ present` is covered by some non-wildcard column head;
     - no `c ∈ missing ∪ missing_empty` is covered by any column head;
     - every column constructor equals the union of one or more members of `present`;
     - every constructor is **sharp** with respect to column heads (either fully included in or fully disjoint from each column constructor — eliminating partial intersections on overlapping integer ranges `0..=10` and `5..=15` or slice patterns).

3. **Specialization and witness reconstruction (`usefulness.rs:1745–1775`):**
   - For each `ctor` in `split_ctors`, `matrix.specialize_constructor(pcx, &ctor, ctor_is_relevant)` (`1283–1321`) builds a specialized sub-matrix whose column 0 is replaced by `PlaceInfo::specialize` (arity `a`), filtering rows where `ctor.is_covered_by(pcx.cx, row.head().ctor())?` holds and popping `ctor` via `pop_head_constructor` (`1182–1198`).
   - Returned sub-witness stacks `witnesses` from the specialized sub-matrix are lifted back via `witnesses.apply_constructor(pcx, &missing_ctors, &ctor)` (`1760`):
     - When `ctor == Constructor::Missing`, each witness stack `ws` is duplicated once per `m ∈ missing_ctors`, prepending `WitnessPat::wild_from_ctor(cx, m, ty)` (which recursively fills `m`'s subfields using `WitnessPat::wildcard`, turning uninhabited subfields into `Constructor::Never`, `pat.rs:261-285`).
     - When `ctor` is a concrete constructor of arity `a`, `unspecialize` pops the top `a` patterns from the stack and wraps them into `WitnessPat::new(ctor, fields, ty)`.
     - Regardless of `ctor`, `matrix.unspecialize(spec_matrix)` (`1325–1330`) propagates usefulness upward: `parent_row.useful |= child_row.useful`.

### 2. Uninhabited Types, `PlaceValidity`, `&Void` Inhabitedness, and Toplevel Deref Exception

Basis: source + execution + derived.

#### 2.1 How `PlaceValidity` and `is_toplevel_exception` interact

In `compiler/rustc_mir_build/src/thir/pattern/check_match.rs:293–368`, `is_known_valid_scrutinee` determines whether the root scrutinee expression can validly point to invalid memory before matching:

```rust
fn is_known_valid_scrutinee(&self, scrutinee: &Expr<'tcx>) -> bool {
    use ExprKind::*;
    match &scrutinee.kind {
        // Pointers can validly point to a place with invalid data. It is undecided whether
        // references can too, so we conservatively assume they can.
        Deref { .. } => false,
        Field { lhs, .. } => {
            let lhs = &self.thir()[*lhs];
            match lhs.ty.kind() {
                ty::Adt(def, _) if def.is_union() => false,
                _ => self.is_known_valid_scrutinee(lhs),
            }
        }
        ...
```

When descending into subpatterns in `PlaceValidity::specialize` (`usefulness.rs:868–878`), validity is preserved everywhere **except** `Constructor::Ref`, `Constructor::DerefPattern(_)`, and `Constructor::UnionField`, all of which reset `PlaceValidity` to `MaybeInvalid`. `split_column_ctors` (`usefulness.rs:953–990`) then computes three booleans controlling empty constructors:

```rust
let is_toplevel_exception =
    self.is_scrutinee && matches!(ctors_for_ty, ConstructorSet::NoConstructors);
let empty_arms_are_unreachable = self.validity.is_known_valid()
    && (is_toplevel_exception || cx.is_exhaustive_patterns_feature_on());
let can_omit_empty_arms = self.validity.is_known_valid()
    || is_toplevel_exception
    || cx.is_exhaustive_patterns_feature_on();
...
if !(split_set.missing.is_empty()
    && (split_set.missing_empty.is_empty() || empty_arms_are_unreachable))
{
    split_ctors.push(Constructor::Missing);
}
let mut missing_ctors = split_set.missing;
if !can_omit_empty_arms {
    missing_ctors.append(&mut split_set.missing_empty);
}
```

This three-boolean gating explains every single uninhabited case observed empirically in Group A of `support/probe_results.json`:

| Case (from `support/probe_results.json`) | Scrutinee / Type | Root `validity` | Subplace (`Err` / `*`) `is_scrutinee`, `validity` | `ctors_for_ty` / `missing_empty` | `can_omit_empty_arms` | Observed `rustc` Result |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `void_and_result_void_opt0` (`unwrap_void_res_implicit`) | `r: Result<u32, Void>` (by value) | `ValidOnly` | `true`, `ValidOnly` | `Variants([Visible(u32), Empty(Void)])`, `missing_empty = [Err]` | `true` (`is_known_valid()`) | Compiles (`0`); outputs `UNWRAP_VOID=(77,99)` |
| `never_type_and_result_never` | `n: !`, `r: Result<u32, !>` (by value) | `ValidOnly` | `true`, `ValidOnly` | `NoConstructors` (`!`), `Variants([Visible, Empty])` | `true` | Compiles (`0`); outputs `UNWRAP_NEVER=88` (with `unreachable_code` on `absurd(n)`) |
| `deref_result_void_default` | `match *r { Ok(x) => x }` on `r: &Result<u32, Void>` | `MaybeInvalid` (`Deref`) | `false`, `MaybeInvalid` | `missing_empty = [Err]` (`!is_toplevel_exception`) | `false` | **Rejects `E0004`**: ``pattern `Err(_)` not covered``, note: `` `Void` is uninhabited but is not being matched by value, so a wildcard `_` is required `` |
| `deref_result_void_exhaustive_patterns` | Same with `#![feature(exhaustive_patterns)]` | `MaybeInvalid` | `false`, `MaybeInvalid` | `missing_empty = [Err]` | `true` (`exhaustive_patterns`) | Compiles (`0`); outputs `DEREF_RES=55` |
| `ref_void_deref_empty_default` | `match *r {}` on `r: &Void` | `MaybeInvalid` (`Deref`) | `true`, `MaybeInvalid` | `NoConstructors`, `missing_empty = [Never]` (`constructor.rs:1200`) | `true` (`is_toplevel_exception = true`) | Compiles (`0`) |
| `ref_void_empty_default` | `match r {}` on `r: &Void` | `ValidOnly` | `Ref` ctor (`missing = [Ref]`) -> inner `false`, `MaybeInvalid` | `ConstructorSet::Ref` | `false` (on `Void` pointee under `Ref`) | **Rejects `E0004`**: ``type `&Void` is non-empty``, note: `references are always considered inhabited` |
| `ref_void_empty_exhaustive_patterns` | Same `match r {}` with `#![feature(exhaustive_patterns)]` | `ValidOnly` | `Ref` ctor -> inner `false`, `MaybeInvalid` | `ConstructorSet::Ref` | `true` on inner `Void` (`exh`), **`Ref` in `missing` non-empty**! | **Still rejects `E0004`**: ``type `&Void` is non-empty``, note: `references are always considered inhabited` |

Notice the subtle two-stage invariant for `match *r {}` vs `match r {}`:

1. When matching `*r` directly on `r: &Void`, `split_set.missing` is `[]` and `split_set.missing_empty` is `[Constructor::Never]` (`constructor.rs:1196-1201`), while `empty_arms_are_unreachable` is **`false`** (because `self.validity.is_known_valid()` is `false`), so `split_ctors` STILL receives `Constructor::Missing` (`usefulness.rs:977-981`)! That keeps an arm like `_ => ...` or `! => ...` on `*r` non-redundant until the `missing_ctors` check runs. Because `is_toplevel_exception` is `true`, `can_omit_empty_arms` is `true`, so `missing_ctors` remains `[]`, `apply_constructor` emits `[]` witnesses, and `match *r {}` compiles!
2. When matching `r: &Void` directly (`match r {}`) even with `#![feature(exhaustive_patterns)]`, `ctors_for_ty(&Void)` returns `ConstructorSet::Ref` (`rustc.rs:413`), and `ConstructorSet::Ref::split` (`constructor.rs:1090-1096`) puts `Constructor::Ref` unconditionally into **`missing`** (NOT `missing_empty`!). Specialization pushes `Constructor::Missing`, recurses on zero rows (`WitnessMatrix::unit_witness()`), and `wild_from_ctor(Ref, &Void)` inspects the inner `&Void` subplace with `PlaceValidity::MaybeInvalid`. Look closely: when `exhaustive_patterns` is **off**, `WitnessPat::wildcard` (`pat.rs:253-259`) queries `ctors_for_ty(Void).all_empty()` which is **`true`** (independently of `exhaustive_patterns` for `NoConstructors`), constructing `WitnessPat(Never, Void)`, while `rustc.rs:869` prints `Never` as `_` unless `#![feature(never_patterns)]` is enabled. Because the top-level match had empty arms (`arms.is_empty()`), `check_match.rs:1243-1249` formats `NonExhaustivePatternsTypeNotEmpty` (`type `&Void` is non-empty`) and `1312-1316` checks `ty::Ref(_, sub_ty, _)` to emit `= note: references are always considered inhabited`. Even with `#![feature(exhaustive_patterns)]`, `Constructor::Ref` is NEVER marked empty in `ConstructorSet::Ref` (`all_empty` at `constructor.rs:1212` returns `false`), so `match r {}` is unconditionally rejected with `E0004`! Adding `&_ => 12` (`ref_void_wildcard_default`) covers `Constructor::Ref`, specializing into `Void` with a `_` wildcard row that immediately discharges all values.

### 3. Private Uninhabited Fields (`Constructor::PrivateUninhabited`)

Basis: source + execution + derived.

Inside `RustcPatCtxt::ctor_sub_tys` (`compiler/rustc_pattern_analysis/src/rustc.rs:248–257`):

```rust
ty::Adt(adt, _) => {
    let variant = &adt.variant(RustcPatCtxt::variant_index_for_adt(&ctor, *adt));
    let tys = cx.variant_sub_tys(ty, variant).map(|(field, ty)| {
        let is_visible =
            adt.is_enum() || field.vis.is_accessible_from(cx.module, cx.tcx);
        let is_uninhabited = cx.is_uninhabited(*ty);
        let skip = is_uninhabited && !is_visible;
        (ty, PrivateUninhabitedField(skip))
    });
    cx.dropless_arena.alloc_from_iter(tys)
}
```

And in `RustcPatCtxt::ctors_for_ty` (`rustc.rs:410-412`):

```rust
ty::Adt(..) | ty::Tuple(..) => {
    ConstructorSet::Struct { empty: cx.is_uninhabited(ty.inner()) }
}
```

This creates a crucial privacy asymmetry (`inner::Priv { pub tag: u8, _v: Void }`):

- **Inside module `inner` (`cx.module` can access `_v`):** `ty.inhabited_predicate().apply_revealing_opaque(..., cx.module, ...)` sees `_v: Void`, so `cx.is_uninhabited(Priv)` returns **`true`**. `ConstructorSet::Struct { empty: true }` puts `Constructor::Struct` into `missing_empty`, which `can_omit_empty_arms` (`ValidOnly`) omits. Hence `match p {}` compiles cleanly (`private_uninhabited_inside_mod_empty_ok`).
- **Outside module `inner` (`outside(p: inner::Priv)`):**
  1. `field.vis.is_accessible_from(cx.module, cx.tcx)` is **`false`** for `_v`, and critically, **`ty.inhabited_predicate(...)` checks visibility from `cx.module`**, so `cx.is_uninhabited(Priv)` returns **`false`**! Therefore `match p {}` puts `Constructor::Struct` into `missing` (NOT `missing_empty`), failing with `E0004: non-exhaustive patterns: type Priv is non-empty` (`private_uninhabited_outside_mod_empty_e0004`).
  2. When the user covers all visible fields (`match p { inner::Priv { tag: 0..=255, .. } => 1 }`), specialization by `Constructor::Struct` invokes `ctor_sub_tys`, where `_v` has `is_visible = false` and `is_uninhabited = true`, setting `PrivateUninhabitedField(true)`.
  3. On the resulting specialized subcolumn for `_v`, `PlaceInfo::split_column_ctors` hits line `939`: `if self.private_uninhabited { return Ok((smallvec![Constructor::PrivateUninhabited], vec![])); }`. Notice `PrivateUninhabited` has `ctor_arity == 0` (`rustc.rs:298`) and `specialize_constructor` (`pat.rs:146-149`) returns `smallvec![]` when `matches!(other_ctor, PrivateUninhabited)`! Thus the compiler skips the hidden uninhabited column completely (both avoiding unsafely revealing private uninhabitedness in `match p {}` and avoiding falsely demanding a pattern for an inaccessible field when `..` is used), and `private_uninhabited_outside_mod_cover_pub_tag_ok` compiles with exit code `0`.

### 4. Cross-Crate `#[non_exhaustive]` (`E0004` vs `E0638`, `Constructor::NonExhaustive`)

Basis: source + execution + derived.

Pattern checking treats `#[non_exhaustive]` via **two completely distinct mechanisms** depending on whether the attribute annotates an `enum` (handled in `rustc_pattern_analysis` with `E0004`) or a `struct` / struct-like enum `variant` (handled earlier in `rustc_hir_typeck` with `E0638`):

1. **`#[non_exhaustive]` on `enum`s (`rustc_pattern_analysis` -> `E0004`):**
   - `RustcPatCtxt::is_foreign_non_exhaustive_enum` (`rustc.rs:167-172`) checks `def.variant_list_has_applicable_non_exhaustive()`. Inside the defining crate (`up.rs`), this predicate is `false`, so `internal_exhaustive_match` on `Status`, `SingleNonExh`, `Config`, and `AllPub` compiles with zero errors without `_` or `..` (`upstream_defining_crate_without_wildcard_ok`).
   - Outside the defining crate, `is_declared_nonexhaustive` is `true`. Note line `rustc.rs:373`:
     ```rust
     if def.variants().is_empty() && !is_declared_nonexhaustive {
         ConstructorSet::NoConstructors
     } else {
         ...
         ConstructorSet::Variants { variants, non_exhaustive: is_declared_nonexhaustive }
     }
     ```
     Even if an upstream `#[non_exhaustive]` enum has zero variants, it stays `ConstructorSet::Variants { non_exhaustive: true }` rather than `NoConstructors` (`all_empty()` returns `false` because of `!*non_exhaustive`, `constructor.rs:1218`).
   - During `ConstructorSet::split` (`constructor.rs:1128-1130`), `*non_exhaustive` unconditionally appends `Constructor::NonExhaustive` to `missing`.
   - Back in `PlaceInfo::split_column_ctors` (`usefulness.rs:997-1003`):
     ```rust
     } else if missing_ctors.iter().any(|c| c.is_non_exhaustive()) && !cx.exhaustive_witnesses()
     {
         missing_ctors = vec![Constructor::NonExhaustive];
     }
     ```
     Because listing some missing variants when a wildcard `_` is still required would mislead users, `rustc` collapses `missing_ctors` to `[Constructor::NonExhaustive]` (unless `exhaustive_witnesses` is requested for diagnostics like missing-variant lints). `WitnessPat` prints `Constructor::NonExhaustive` as `_` (`rustc.rs:869`), and `check_match.rs:1302-1303` attaches the note `` `Status` is marked as non-exhaustive, so a wildcard `_` is necessary to match exhaustively ``.
   - Live execution confirms this even for a **single-variant** `#[non_exhaustive]` enum (`downstream_single_variant_non_exhaustive_without_wildcard_e0004` rejects `match x { up::SingleNonExh::Only => 1 }` with `E0004`: ``pattern `_` not covered``), while adding `_ => 3` compiles and executes cleanly (`downstream_non_exhaustive_enum_with_wildcard_ok`, `STAT=(1,2)`).

2. **`#[non_exhaustive]` on `struct`s and enum variants (`rustc_hir_typeck` -> `E0638`):**
   - Struct pattern completeness (field visibility and `..` rest patterns) is checked in `compiler/rustc_hir_typeck/src/pat.rs:2221–2241` (`error_foreign_non_exhaustive_spat`), emitting **`E0638`**:
     ```rust
     struct_span_code_err!(
         self.dcx(),
         pat.span,
         E0638,
         "`..` required with {descr} marked as non-exhaustive",
     )
     ```
   - Critically, our live probes confirm `E0638` fires on **all three** foreign cases even when every field in the struct or variant is `pub`:
     - `downstream_non_exhaustive_struct_without_dotdot_e0638` (`up::Config { pub port: u16, extra: u8 }` -> `let up::Config { port } = c;`): emits **two** errors (`E0638` plus `error: pattern requires '..' due to inaccessible fields`).
     - `downstream_non_exhaustive_allpub_struct_without_dotdot_e0638` (`up::AllPub { pub port: u16 }` with zero private fields -> `let up::AllPub { port } = a;`): still emits `E0638` (`` `..` required with struct marked as non-exhaustive ``), isolating the `#[non_exhaustive]` gate from inaccessible-field checking!
     - `downstream_non_exhaustive_variant_without_dotdot_e0638` (`up::Ev::V { pub a: u8 }` with `#[non_exhaustive]` on the variant -> `up::Ev::V { a } => a,`): emits `E0638` (`` `..` required with variant marked as non-exhaustive ``).
   - Supplying `..` (`let up::Config { port, .. } = c;`) compiles cleanly and runs to `PORT=8080`.

### 5. Match Guards, Non-Exhaustiveness, and Guarded Shadowing

Basis: source + execution + derived.

Because match guards execute arbitrary runtime predicates (which are undecidable statically and may have side effects), `rustc_pattern_analysis` treats every guarded arm strictly as an **over-approximation for usefulness** and **completely ignored for exhaustivity coverage**:

- `MatrixRow::new` (`usefulness.rs:1147`) initializes `is_under_guard: arm.has_guard`, which `expand_or_pat` (`1173`) and `pop_head_constructor` (`1193`) propagate unchanged through specialization.
- At a 0-column leaf (`1721–1727`), `useful &= row.is_under_guard` ensures a guarded row marks itself `useful = true` (if no earlier unguarded row covered the leaf) while leaving `useful = true` for every subsequent row and for `WitnessMatrix::unit_witness()`.
- Crucially, `check_match.rs:576–584` also computes a diagnostic counter-check (`would_be_exhaustive_without_guards`) by clearing `has_guard = false` whenever `!witnesses.is_empty()` and any arm had a guard (`probe_results.json` confirms the emitted note `= note: match arms with guards don't count towards exhaustivity`).

Our live probes confirm both consequences:

- **`guarded_arms_non_exhaustive_e0004`**: `match x { n if n >= 0 => 1, n if n < 0 => -1 }` on `x: i32` rejects with `E0004` (`pattern i32::MIN..=i32::MAX not covered`) even though `{n >= 0, n < 0}` mathematically partitions `i32`.
- **`guarded_bool_non_exhaustive_e0004`**: `match b { true if flag => 1, false if !flag => 0 }` on `(bool, bool)` rejects with `E0004` (`patterns true and false not covered`), empirically confirming both boolean constructors survive into `non_exhaustiveness_witnesses`.
- **`guarded_does_not_shadow` inside `integer_ranges_and_unreachable_patterns_lint`**: `0..=10 if flag => 100` followed by `7 => 255` compiles cleanly with **zero** `unreachable_patterns` warning and evaluates at runtime to `GSHAD=(255,100)` for `flag=false` and `flag=true` respectively.

### 6. Integer Range Splitting, `usize::MAX`/`isize`, and `unreachable_patterns`

Basis: source + execution + derived.

#### 6.1 `IntRange::split` and open-ended `usize`/`isize` bounds

In `compiler/rustc_pattern_analysis/src/rustc.rs:331–359`:

- Fixed-width integers (`u8`, `i32`, etc.) generate exact finite intervals `IntRange::from_range(0, max, Included)` or `[min, max]`. For example, matching `u8` with `0..=127 => 1, 128..=255 => 2` splits `[0, 255]` into two `Presence::Seen` subranges (`[0, 127]` and `[128, 255]`), leaves `missing = []`, and compiles cleanly (`U8=(1,2)`).
- Ptr-sized integers **`isize` and `usize`** bypass `size.truncate(...)`:
  - `isize` maps to `IntRange { lo: MaybeInfiniteInt::NegInfinity, hi: MaybeInfiniteInt::PosInfinity }`.
  - `usize` maps to `IntRange { lo: MaybeInfiniteInt::new_finite_uint(0), hi: MaybeInfiniteInt::PosInfinity }`.
  When `hoist_pat_range_bdy` encounters values beyond the platform bound (`is_range_beyond_boundaries`, `rustc.rs:176-186`), `check_match.rs:1288-1299` emits the note: `` `usize::MAX` is not treated as exhaustive, so half-open ranges are necessary to match exhaustively ``. Live execution on `0..=usize::MAX => 1` (`usize_max_range_non_exhaustive_e0004`) reproduces `E0004`: ``pattern `usize::MAX..` not covered``.

#### 6.2 Collective `unreachable_patterns` across overlapping intervals

In `usefulness.rs:1724`, whenever specialization reaches a 0-column leaf with multiple active rows (`row 0`, `row 1`, ..., `row i`), `row.intersects_at_least.insert_range(0..i)` records every prior row reachable at that leaf. When an arm's `useful` remains `false` across all specialized branches:

1. `compute_match_usefulness` (`1862–1865`) returns `Usefulness::Redundant(explanation)`, where `explanation.covered_by` lists prior pattern nodes accumulated in `BranchPatUsefulness`.
2. `report_unreachable_pattern` (`check_match.rs:999–1018`) formats multiple covering ranges with up to `CAP_COVERED_BY_MANY = 4` spans and label `"collectively making this unreachable"`.

In `integer_ranges_and_unreachable_patterns_lint`:
```rust
match x {
    0..=10 => 100,
    5..=15 => 200,
    7 => 255,
    _ => 0,
}
```
Splitting `[0, 255]` yields sharp sub-intervals including `[0, 4]`, `[5, 6]`, `[7, 7]`, `[8, 10]`, `[11, 15]`, `[16, 255]`. Both `0..=10` and `5..=15` cover `[7, 7]`, so both cover row 2 (`7`) at the `[7, 7]` specialized leaf; `rustc` emits the exact multi-span `unreachable_patterns` warning labeling both `0..=10` and `5..=15` with `matches some of the same values` and `7` with `collectively making this unreachable` (while runtime evaluation prints `SHAD=(100,200,0,100)`).

### 7. MIR Lowering of Eliminated Uninhabited Arms and Anneal Verification Seams

Basis: execution + source.

Inspecting `-Zdump-mir=UnreachablePropagation|MatchBranchSimplification|built` on `unwrap_void_res` and `unwrap_void_res_implicit` (`Result<u32, Void>`, `probe_results.json`) reveals how MIR optimization lowers pattern-analysis guarantees:

- **`-Copt-level=0` (`built.after.mir`)**:
  - When the user writes the explicit `Err(v) => match v {}` arm (`unwrap_void_res`), `built` emits `switchInt(move _2) -> [0: bb2, 1: bb4, otherwise: bb1];`, with `bb2: falseEdge -> [real: bb6, imaginary: bb4];` and `bb4` reading `Void` followed by `PlaceMention(_4); FakeRead(ForMatchedPlace(None), _4); unreachable;`.
  - When the user omits the `Err` arm (`unwrap_void_res_implicit`), `built` omits variant `1` directly from the `switchInt`: `switchInt(move _2) -> [0: bb2, otherwise: bb1];` where `bb1` is `FakeRead(ForMatchedPlace(None), _1); unreachable;`.
- **`-Copt-level=1` (`UnreachablePropagation.after.mir` and `MatchBranchSimplification.after.mir`)**:
  - `UnreachablePropagation` eliminates the dead `switchInt` branch to `bb1: unreachable` and replaces the branch with an assumption; `MatchBranchSimplification` fuses the cleanup directly into `bb0`:
    ```mir
    bb0: {
        _2 = discriminant(_1);
        _4 = Eq(copy _2, const 0_isize);
        assume(move _4);
        StorageLive(_3);
        _3 = copy ((_1 as Ok).0: u32);
        _0 = copy _3;
        StorageDead(_3);
        return;
    }
    ```
  - **Architectural Seam with `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
    1. **Trusted capture MIR profile boundary (`trusted/lean/Trusted/MirAst.lean:634–784`):** In Anneal's MIR AST, `StatementKind::Intrinsic(Box<NonDivergingIntrinsic>)` (`Assume` in MIR dumps) maps to `StatementKind.unsupported` (`654–656`), `FakeRead` / `PlaceMention` likewise map to `StatementKind.unsupported`, and `TerminatorKind::FalseEdge` maps to `TerminatorKind.unsupported` (`782–784`). Meanwhile `TerminatorKind::Unreachable` is modeled explicitly in `MirSemantics.lean:1551–1552` as `.fault .undefined` (UB if reached dynamically).
    2. **Consequence for post-cleanup capture:** If a captured function passes through `UnreachablePropagation` / `MatchBranchSimplification` and retains `assume(move _4)` (`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume)`), Anneal's `MirAst` currently fails closed (`StatementKind.unsupported`) rather than interpreting the assumption—or else the upstream MIR capture pass must execute under a clean post-cleanup/pre-optimization profile (cf. `trusted/rustc-capture/src/driver.rs`) where dead `SwitchInt` `otherwise` targets remain explicit `.unreachable` terminators (`MirSemantics.lean:1551–1552`) discharged by variant/type invariants.

### 8. Mechanized Lean `v4.34.1` Soundness and Completeness Formalization

Basis: derived (kernel-checked Lean `v4.34.1` proof).

`support/PatternAnalysisMarangetExhaustivenessSoundness.lean` (`6,340` lines) formalizes Maranget's constructor-splitting algorithm in `namespace PatternAnalysisSoundness` under strict constructive kernel discipline: **every `def` is marked `noncomputable def`**, zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `deriving` on recursive inductives, and zero `_unsafe_rec` constants.

#### 8.1 Formal Data Model and Core Judgments

- **Types (`Ty`, `448–456`) and Weight Termination (`tyWeight`, `colsWeight`):** `unit`, `bool`, `u8`, `void`, `pair`, `struct2 pubField privField privFieldVisible`, `enum variants nonExh`, and `ref inner`. Structural positivity (`tyWeight_pos`) guarantees strict decrease under constructor specialization (`colsWeight_specialize_lt`), enabling structural induction on `fuel ≥ colsWeight cols + 1`.
- **Values (`Val`, `569–577`) and Dual Validity Semantics (`VisibleWellTyped` vs `TrueWellTyped` vs `ValidPlaceVal`):**
  - `Val.invalid` models possibly uninitialized/invalid place memory under `PlaceValidity.maybeInvalid` (`ValidPlaceVal`, `588–621, 1489–1520`).
  - `Val.hiddenCtor extraTag` models unknown upstream enum variants of a cross-crate `#[non_exhaustive]` enum (`enum variants true`).
  - `VisibleWellTyped .validOnly false (.ref .void) (.ref .invalid)` holds trivially (`visibleWellTyped_ref_void_inhabited`) because entering `.ref inner` resets inner validity to `.maybeInvalid`.
  - When a `struct2 a b false` has an invisible empty field (`bVis = false`, `tyIsEmpty b = true`), `ValidPlaceVal` resets the field slot's ambient validity to `.maybeInvalid` and privacy flag to `true`, faithfully matching `RustcPatCtxt::is_uninhabited` visibility semantics (`rustc.rs:157-164, 248-257`) while preserving strict physical `TrueWellTyped → VisibleWellTyped` (`trueWellTyped_implies_visible`).
- **Constructor Splitting & Algorithm (`marangetCheckAux`, `2025–2045`):**
  - `IntRange.splitList` partitions `[0, 255]` (`splitIntRanges_sound_and_complete`) into covering, bounded, and sharp seen/unseen sub-intervals.
  - `splitColumnCtors col heads` implements the exact `PrivateUninhabited` short-circuit, `Or` expansion flag, `NoConstructors` top-level deref exception (`is_toplevel_exception`), `can_omit_empty_arms`, `empty_arms_are_unreachable`, and `NonExhaustive` collapse.
  - `marangetCheckAux fuel cols rows` computes `(witnessStacks, usefulArmIds)` by calling `evalBaseRows` (`1721–1727` guard & usefulness semantics) at `cols = []` and recursing via `marangetBranches` + `applyCtorToWitnesses` on non-empty columns.

#### 8.2 Verified Theorem Inventory and `#print axioms` Receipt

Every theorem below compiled with exit code `0` under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` on `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). An explicit Lean MetaM scan over `env.constants` verified **`localDecls=978`**, **`thmCount=299`**, **`unsafeRecs=0`**, **`unsafeConsts=0`**, **`customAxioms=0`**, and **`badAxiomThms=0`**:

| Lean Theorem (`PatternAnalysisSoundness.*`) | Line | What It Proves | Axiom Dependencies (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `tyIsEmpty_sound` | `914` | `tyIsEmpty t = true → VisibleWellTyped .validOnly t v → False` | `[propext]` |
| `splitIntRanges_sound_and_complete` | `1248` | Exact bounds, full `[lo, hi]` coverage, seen/unseen soundness, and sharpness of `IntRange` splitting | `[propext, Quot.sound]` |
| `marangetCheckAux_iff` | `5515` | Multi-column biconditional soundness & completeness under `ColsWellFormed` and `ColsSoundCtx` | `[propext, Quot.sound]` |
| `marangetCheckAux_witness_sound` | `5782` | Unconditional witness soundness (even when `exhPatterns = true` or `isScrutinee` deref): every witness stack yields a matching `ValidPlaceVal` value vector unguardedly unmatched | `[propext, Quot.sound]` |
| `maranget_validOnly_sound_and_complete` | `5942` | **Theorem 1:** By-value (`validOnly`, `!exhPatterns`) `evalMaranget col arms = [] ↔ ∀ v, ValidPlaceVal .validOnly false col.ty v → armsUnguardedMatch arms v = true` | `[propext, Quot.sound]` |
| `maranget_maybeInvalid_sound_and_complete` | `5979` | **Theorem 2:** Non-scrutinee-exception `.maybeInvalid` (`!exhPatterns`) exact soundness & completeness | `[propext, Quot.sound]` |
| `witness_soundness` / `evalMaranget_witness_sound` | `6017` / `6027` | **Theorem 3:** Multi-column and single-column witness soundness producing a concrete `VisibleWellTyped` unmatched witness value | `[propext, Quot.sound]` |
| `uninhabited_void_closed_exhaustive` | `6072` | **Theorem 4:** Any empty type (`tyIsEmpty = true`) matched by value (`[]` arms) yields `evalMaranget = []` | `[propext, Quot.sound]` |
| `ref_void_always_inhabited` | `6084` | **Theorem 5:** `&Void` (`match r {}`) returns `[.ref .never]` for **both** `exh = false` and `exh = true`, witnessed by `Val.ref Val.invalid` | `[propext]` |
| `deref_void_toplevel_vs_nested` | `6100` | **Theorem 6:** `match *r {}` returns `[]`; `match *r { Ok(_) => ... }` returns `[.variant 1 .never]` when `exhPatterns = false` and `[]` when `exhPatterns = true` | `[propext]` |
| `non_exhaustive_hidden_ctor_unexhausted` | `6135` | **Theorem 7:** Downstream `#[non_exhaustive]` enum matching is exhaustive only if an unguarded arm flattens at its head to `.wild` | `[propext, Quot.sound]` |
| `private_uninhabited_vs_visible_struct` | `6166` | **Theorem 8:** Private empty field (`struct2 .u8 .void false`) rejects `[]` arms, requires `[0..=255]` (`PrivateUninhabited` skips field 2), while `struct2 .u8 .void true` accepts `[]` | `[propext]` |
| `evalMaranget_guard_overapprox_equiv` | `6215` | **Theorem 9a:** Exhaustiveness (`evalMaranget = []`) is invariant under filtering to unguarded arms | `[propext, Quot.sound]` |
| `complementary_guarded_bool_non_exhaustive` | `6231` | **Theorem 9b:** Complementary guarded `bool` arms return `[.bool true, .bool false] ≠ []` | `[propext]` |
| `arm_usefulness_guard_and_range_overlap` | `6249` | **Theorem 10:** Guarded `0..=10 if flag` leaves arm `7` useful (`true`), while overlapping unguarded ranges `[0..=10, 5..=15, 7]` and `[0..=10, 11..=20, 5..=15]` mark arm `2` redundant (`false`) | `[propext]` |
| `ce1` – `ce4` (Negative Controls) | `6265`–`6313` | Mechanized counterexamples matching `rustc` `E0004` rejections on `&Void`, guarded `bool`, open `#[non_exhaustive]` enums, and `&Result<u8, Void>` deref | `[propext]` |

### 9. Cross-Property Summary Matrix

| Phenomenon | Core `rustc` Trigger | Live Probe Outcome (`rustc 1.98.0-nightly`) | Mechanized Proof Anchor (`PatternAnalysisSoundness.*`) |
| :--- | :--- | :--- | :--- |
| `match r {}` on `Void`, `!`, `Result<u32, Void>` | `PlaceValidity::ValidOnly` + `all_empty` / `NoConstructors` | `compile_returncode = 0`, `UNWRAP_VOID=(77,99)` (`unwrap_void_res` & `_implicit`) | `uninhabited_void_closed_exhaustive` |
| `match *r {}` on `&Void` | `is_toplevel_exception = is_scrutinee && NoConstructors` | `compile_returncode = 0` (`ref_void_deref_empty_default`) | `deref_void_toplevel_vs_nested` |
| `match *r { Ok(x) => x }` on `&Result<u32, Void>` | `is_scrutinee = false`, `MaybeInvalid`, `!exhaustive_patterns` | **`E0004`** default (`Err(_)` not covered); `0` under `#![feature(exhaustive_patterns)]` | `deref_void_toplevel_vs_nested`, `ce4_deref_result_void_without_feature_non_exhaustive` |
| `match r {}` on `&Void` (any feature flag) | `ConstructorSet::Ref` non-empty + `Ref::specialize -> MaybeInvalid` | **`E0004`** even with `#![feature(exhaustive_patterns)]` (`references are always considered inhabited`) | `ref_void_always_inhabited`, `ce1_ref_void_is_non_exhaustive` |
| Private uninhabited struct field outside mod | `ctor_sub_tys` sets `PrivateUninhabitedField(true)` | **`E0004`** on `match p {}`; **`0`** on `{ tag: 0..=255, .. }` | `private_uninhabited_vs_visible_struct` |
| Cross-crate `#[non_exhaustive]` enum (incl. 1-variant) | `is_foreign_non_exhaustive_enum` -> `Constructor::NonExhaustive` | **`E0004`** (`_ not covered`) downstream; **`0`** upstream | `non_exhaustive_hidden_ctor_unexhausted`, `ce3_non_exhaustive_enum_all_visible_insufficient` |
| Cross-crate `#[non_exhaustive]` struct (incl. all-`pub`) & variant | `rustc_hir_typeck::pat::error_foreign_non_exhaustive_spat` | **`E0638`** (`` `..` required with struct/variant marked as non-exhaustive ``) | `rustc_hir_typeck/src/pat.rs:2221-2241` (HIR boundary) |
| Complementary guarded match arms | `MatrixRow::is_under_guard` leaves `useful = true` at base leaf | **`E0004`** on `i32` & `bool` complementary guards | `evalMaranget_guard_overapprox_equiv`, `complementary_guarded_bool_non_exhaustive` |
| `0..=usize::MAX` | `usize::MAX` hoisted to `PosInfinity` (`rustc.rs:176-186, 350`) | **`E0004`** (`usize::MAX.. not covered`) | Recorded in Boundaries (`usize`/`isize` infinite endpoints) |
| Overlapping ranges shadowing a singleton (`0..=10`, `5..=15`, `7`) | `IntRange::split` + `intersects_at_least` multi-arm coverage | `warn(unreachable_patterns)`: `collectively making this unreachable` (`SHAD=(100,200,0,100)`) | `arm_usefulness_guard_and_range_overlap` |

## Boundaries

Per `FORMAT.md` negative-space conventions:

- **`not examined` — Full crates.io `rustc_pattern_analysis` execution / performance scaling benchmarks:** While all algorithm source code and 18 focused compiler probes were executed live, compilation latency and memory usage of complex matrix splits (e.g., high-arity slice/tuple matrices hitting `complexity_limit`) across arbitrary crates.io packages were not benchmarked.
- **`unsupported` (by current Lean formalization relative to full `rustc_pattern_analysis`):** `PatternAnalysisMarangetExhaustivenessSoundness.lean` models finite unit, bool, `u8` (0..=255 closed interval splitting), zero-constructor `void`, 2-tuples, 2-field structs with field-2 visibility (`struct2`), multi-variant enums with cross-crate `nonExh`, and references (`&T`). It intentionally omits floating-point ranges (`F16Range`–`F128Range`), string literal patterns (`Str`), variable-length slices (`ConstructorSet::Slice`), raw/struct-union fields (`ConstructorSet::Union`), `Opaque` non-structural constants, unstable/doc-hidden variant witnesses (`Constructor::Hidden`), experimental deref smart-pointer patterns (`DerefPattern`), `rustc`'s `usize`/`isize` `MaybeInfiniteInt` open-bound policy (`0..=usize::MAX`), and `complexity_limit` diagnostics. Additionally, the Lean model uses `1`-column `MatchArm` lists externally (`evalMaranget`) while proving multi-column theorems internally via `marangetCheckAux_iff`, `marangetCheckAux_witness_sound`, and `witness_soundness`.
- **`known not to apply` — Direct compilation of Lean proofs against Rust compiler crates:** The Lean 4 theorems verify a faithful formal specification of Maranget's algorithm constructed from `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`; they do not execute `rustc`'s actual Rust binary code nor eliminate the TCB gap between Rust source and Lean formalization.
- **`known not to apply` — `#[non_exhaustive]` struct/variant `..` rule in `rustc_pattern_analysis`:** `E0638` on `struct` and struct-variant patterns is enforced in `rustc_hir_typeck/src/pat.rs:2221–2241` rather than in `rustc_pattern_analysis`, and therefore falls outside the THIR pattern-matrix algorithm.
- **`known not to apply` — Anneal MIR direct interpretation of `assume(...)` intrinsics:** Audited `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirAst.lean:634–662`) explicitly classifies `StatementKind::Intrinsic` (`assume`) and `TerminatorKind::FalseEdge` as `.unsupported` rather than validatable assumptions; post-`MatchBranchSimplification` MIR dumps emitting `assume(move _4)` cannot yet be consumed directly by `Anneal` without retaining explicit `.unreachable` terminators or adding semantics for `NonDivergingIntrinsic::Assume`.
- **`unknown` — Planned stabilization timeline of `#![feature(exhaustive_patterns)]` and `#![feature(never_patterns)]` diagnostics:** Source inspection establishes exact current nightly behavior (`14210df0e` through `960ba7cf`), not future Rust RFC/tracking-issue stabilization decisions (which may also expand `WitnessPat` emission of `!` patterns vs `_`).

## Evidence

### 1. Primary Upstream Source Anchors (`rust-lang/rust`)

Inspected directly at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and cross-checked against `49d734536222bf28bb6d07d885b3a81d145981da` and `960ba7cf7e8666ecb449402ca82b6e9e631bd227`:

- `compiler/rustc_pattern_analysis/src/usefulness.rs` (blob `bf236b7737d9` at `14210df0e`, `1,890` lines; `1f19bfd73289` at both `49d734536` and `960ba7cf`, `1,882` lines):
  - `PlaceValidity::{ValidOnly, MaybeInvalid}` and `PlaceValidity::specialize` (`848–878`).
  - `PlaceInfo` and `PlaceInfo::split_column_ctors` (`892–1006`): `PrivateUninhabited` skip (`939–942`), `Or` expansion (`944–947`), `is_toplevel_exception` (`953–954`), `empty_arms_are_unreachable` (`960–961`), `can_omit_empty_arms` (`964–966`), `split_ctors` pushing `Constructor::Missing` (`977–981`), `missing_ctors` appending `missing_empty` (`986–989`), and `NonExhaustive` collapse (`997–1003`).
  - `MatrixRow::new` (`1143–1153`), `expand_or_pat` (`1168–1178`), `pop_head_constructor` (`1182–1198`), `Matrix::new` (`1239–1255`), `Matrix::specialize_constructor` (`1283–1321`), `Matrix::unspecialize` (`1325–1330`).
  - `WitnessStack` (`1444–1462`), `compute_exhaustiveness_and_usefulness` (`1704–1798`, base leaf `useful &= row.is_under_guard` at `1726` and `intersects_at_least.insert_range(0..i)` at `1724`), and `compute_match_usefulness` (`1835–1890`).
- `compiler/rustc_pattern_analysis/src/constructor.rs` (blob `6f07e922ceef` at `14210df0e`, `1,228` lines; `0f636f323e5f` at `960ba7cf`, `1,226` lines):
  - Empty type/constructor semantics documentation (`81–140`).
  - `Constructor::{NonExhaustive, Hidden, Missing, PrivateUninhabited, Never, Wildcard}` (`721–740`).
  - `VariantVisibility::{Visible, Hidden, Empty}` (`969–979`), `ConstructorSet` (`987–1011`), `SplitConstructorSet` & 7 invariants (`1018–1039`), `ConstructorSet::split` (`1046–1205`, appending `NonExhaustive` at `1128–1130` and `Never` into `missing_empty` for `NoConstructors` at `1196–1201`), and `ConstructorSet::all_empty` (`1208–1226`).
- `compiler/rustc_pattern_analysis/src/rustc.rs` (blob `b5491de7905b` at `14210df0e`, `1,094` lines):
  - `is_uninhabited` (`157–164`), `is_foreign_non_exhaustive_enum` (`167–172`), `is_range_beyond_boundaries` (`176–186`).
  - `ctor_sub_tys` / `PrivateUninhabitedField` (`230–281`, specifically `!is_visible && is_uninhabited` at `251–255`), `ctor_arity` (`284–301`), `ctors_for_ty` (`306–436`, including `usize`/`isize` `PosInfinity`/`NegInfinity` at `331–358`, `Variants` vs `NoConstructors` at `371–407`, `Ref` at `413`).
  - `WitnessPat` stringification printing `Never`/`Wildcard`/`NonExhaustive` as `_` unless `never_patterns` is enabled (`868–895`).
  - `is_exhaustive_patterns_feature_on` (`905–907`).
- `compiler/rustc_pattern_analysis/src/pat.rs` (blob `51d0703f9c5c` at `14210df0e`, `314` lines):
  - `DeconstructedPat::specialize` (`140–150`, returning `smallvec![]` for `PrivateUninhabited`), `WitnessPat::wildcard` (`253–259`), `WitnessPat::wild_from_ctor` (`263–285`).
- `compiler/rustc_mir_build/src/thir/pattern/check_match.rs` (blob `afd8447b17ed` at `14210df0e`, `1,544` lines):
  - `is_known_valid_scrutinee` (`293–368`: `Deref { .. } => false`), `check_match` (`483–560`, passing `has_guard: arm.guard.is_some()` at `499`), `report_unreachable_pattern` (`947–1019`: `"collectively making this unreachable"` at `1007`, emitting `UNREACHABLE_PATTERNS` at `1018`), `report_arm_reachability` (`1169–1192`), and `report_non_exhaustive_match` (`1226–1346`: `E0004` at `1254–1259`, `usize::MAX`/`isize` note at `1288–1299`, `#[non_exhaustive]` note at `1302–1303`, uninhabited `MaybeInvalid` note at `1304–1308`, `"references are always considered inhabited"` note at `1312–1316`).
- `compiler/rustc_hir_typeck/src/pat.rs` (blob `b5ae3d06b3b3` at `14210df0e`, `3,362` lines):
  - `error_foreign_non_exhaustive_spat` (`2221–2241`: `E0638` ``"`..` required with {descr} marked as non-exhaustive"``).

### 2. Primary Upstream Source Anchors (`joshlf/anneal`)

Inspected directly at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- `trusted/lean/Trusted/MirAst.lean` (blob `0da11dc6dd5c`, `944` lines): `StatementKind::Intrinsic` / `FakeRead` / `PlaceMention` mapped to `.unsupported` (`634–662`), `TerminatorKind::FalseEdge` mapped to `.unsupported` (`764, 782–784`), and `TerminatorKind::Unreachable` (`776, 789`).
- `trusted/lean/Trusted/MirSemantics.lean` (blob `668c0955aef2`, `2,681` lines): `evalTerminator` (`1537–1569`, lowering `.unreachable` to `.fault .undefined` at `1551–1552` and `.switchInt` at `1553–1567`).
- `trusted/audit/TrustedBoundary.lean` (blob `a1d90a4a4cca`, `2,333` lines): kernel axiom/tactic policy rejecting `sorryAx`, `native_decide`, `bv_decide`, `Classical`-dependent/reflection shortcuts (`Lean.ofReduceBool`), and `*._unsafe_rec` recursive partial helpers (`23, 92–93, 532–533, 1616, 2164`).
- `trusted/rustc-capture/src/driver.rs` (blob `f82074bb58e1`, `152` lines).

### 3. Live `rustc` Execution Artifact (`support/probe_pattern_analysis_exhaustiveness.py` and `support/probe_results.json`)

Executed on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `LLVM version: 22.1.6`), inside an ephemeral `tempfile.TemporaryDirectory()`, preserving full compiler return codes, scrubbed diagnostics, runtime stdouts, and `-Copt-level={0,1}` MIR dumps across all three test groups (`270` lines, `27,414` bytes in `support/probe_results.json`):

- **Group A (`a_uninhabited_matching_and_mir`)**:
  - `void_and_result_void_opt0` & `void_and_result_void_opt1`: both exit `0`, printing `UNWRAP_VOID=(77,99)`. `a1_void_res.unwrap_void_res.3-2-018.MatchBranchSimplification.after.mir` documents `_2 = discriminant(_1); _4 = Eq(copy _2, const 0_isize); assume(move _4);` with dead `Err(Void)` blocks excised.
  - `deref_result_void_default` vs `deref_result_void_exhaustive_patterns`: `rustc` exit `1` (`E0004`: ``pattern `Err(_)` not covered``) vs exit `0` (`DEREF_RES=55`).
  - `never_type_and_result_never`: compiles cleanly (`0`, warning `unreachable_code` on `absurd(n)` call), prints `UNWRAP_NEVER=88`.
  - `ref_void_empty_default` vs `ref_void_empty_exhaustive_patterns` vs `ref_void_deref_empty_default` vs `ref_void_wildcard_default`: first two both fail `E0004` (`references are always considered inhabited`); deref `match *r {}` and `&_ => 12` both exit `0`.
  - `private_uninhabited_inside_mod_empty_ok` (`0`), `private_uninhabited_outside_mod_empty_e0004` (`1`, `E0004`: `type Priv is non-empty`), `private_uninhabited_outside_mod_cover_pub_tag_ok` (`0` on `{ tag: 0..=255, .. }`).
- **Group B (`b_cross_crate_non_exhaustive`)**:
  - `upstream_defining_crate_without_wildcard_ok` (`rlib`, exit `0`).
  - `downstream_non_exhaustive_enum_without_wildcard_e0004` & `downstream_single_variant_non_exhaustive_without_wildcard_e0004`: both fail `E0004` (``pattern `_` not covered``).
  - `downstream_non_exhaustive_enum_with_wildcard_ok`: exit `0`, outputs `STAT=(1,2)`.
  - `downstream_non_exhaustive_struct_without_dotdot_e0638`, `downstream_non_exhaustive_allpub_struct_without_dotdot_e0638`, `downstream_non_exhaustive_variant_without_dotdot_e0638`: all three fail `E0638` (`` `..` required with struct/variant marked as non-exhaustive ``).
  - `downstream_non_exhaustive_struct_with_dotdot_ok`: exit `0`, outputs `PORT=8080`.
- **Group C (`c_guards_ranges_and_unreachable_patterns`)**:
  - `guarded_arms_non_exhaustive_e0004` & `guarded_bool_non_exhaustive_e0004`: both fail `E0004` (`match arms with guards don't count towards exhaustivity`).
  - `usize_max_range_non_exhaustive_e0004`: fails `E0004` (``pattern `usize::MAX..` not covered``).
  - `integer_ranges_and_unreachable_patterns_lint`: exit `0`, emits `unreachable_patterns` warning (`collectively making this unreachable` on `7 => 255` from `0..=10` and `5..=15`) with zero warning on `guarded_does_not_shadow`, outputs `U8=(1,2) SHAD=(100,200,0,100) GSHAD=(255,100)`.

### 4. Kernel-Checked Lean 4 Proof Artifact (`support/PatternAnalysisMarangetExhaustivenessSoundness.lean`)

Verified directly with `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` using `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit code 0`):

- Size and constructiveness: `6,340` lines (`290,864` bytes), `978` local declarations, `299` kernel-checked theorems.
- Axiom & MetaM audit output: `LOCAL_META_AUDIT: localDecls=978 thmCount=299 unsafeRecs=0 unsafeConsts=0 customAxioms=0 badAxiomThms=0`. Every exported `#print axioms` statement (`20` theorems listed in lines `6315–6334`) depends exclusively on `[propext]` or `[propext, Quot.sound]`.

## Revalidation

All findings in this report can be revalidated cheaply from the preserved package files:

1. **Re-run the live `rustc` empirical probe suite** (inside a temporary directory; requires `python3` 3.10+ and any target `rustc` toolchain):
   ```sh
   python3 support/probe_pattern_analysis_exhaustiveness.py --output /tmp/reval_probe_results.json
   ```
   Compare the output JSON against `support/probe_results.json` to detect changes in `E0004` / `E0638` diagnostics, `#![feature(exhaustive_patterns)]`, `usize::MAX` handling, `unreachable_patterns` wording, or `UnreachablePropagation` / `MatchBranchSimplification` MIR output.

2. **Re-verify the Lean `v4.34.1` formalization and kernel axioms** (requires `Lean v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`):
   ```sh
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/PatternAnalysisMarangetExhaustivenessSoundness.lean
   ```
   A clean exit (`0`) with `#print axioms` output containing only `[propext]` and `[propext, Quot.sound]` revalidates all `299` theorems.

3. **Targeted primary-source diff check** on a newer `rust-lang/rust` commit `<new_sha>`:
   ```sh
   git diff 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65..<new_sha> -- \
     compiler/rustc_pattern_analysis/src/usefulness.rs \
     compiler/rustc_pattern_analysis/src/constructor.rs \
     compiler/rustc_pattern_analysis/src/rustc.rs \
     compiler/rustc_pattern_analysis/src/pat.rs \
     compiler/rustc_mir_build/src/thir/pattern/check_match.rs \
     compiler/rustc_hir_typeck/src/pat.rs
   ```
   Pay specific attention to changes in `PlaceInfo::split_column_ctors`, `PlaceValidity::specialize`, `ConstructorSet::split`, `ctor_sub_tys`, `MatrixRow::new`, and `report_non_exhaustive_match`.
