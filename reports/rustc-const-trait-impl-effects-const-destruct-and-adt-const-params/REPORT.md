# `rustc` Const Trait Effects (`const_trait_impl`, `[const]`), Generic Const Destructors (`const_destruct`), and Structural Const Generic Parameters (`adt_const_params` / `unsized_const_params`)

## Summary

Across `rustc` `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and upstream `HEAD` (`01afe534803b93889b85f6028117251cfbd431da`), compile-time trait dispatch (`#![feature(const_trait_impl)]`), compile-time generic destruction (`#![feature(const_destruct)]`), and type-level aggregate or unsized constant generic parameters (`#![feature(adt_const_params, unsized_const_params)]`) are governed by seven load-bearing architectural invariants that determine compiler soundness, solver parity, and verified MIR capture:

1. **Three-Point Surface/HIR Constness Lowered to Two-Point Middle-IR `HostEffectClause`**: Surface and HIR trait bounds carry a three-point effect-constness semilattice `Always <= Maybe <= Normal` (`ast::BoundConstness::{Always, Maybe, Never}` and `hir::BoundConstness::{Always, Maybe, Never}`): `T: const Trait` (`Always`, unconditionally const even in runtime functions), `T: [const] Trait` (`Maybe`, polymorphic over caller const context), and `T: Trait` (`Normal`/`Never`, runtime-only). In `rustc_type_ir/src/predicate.rs`, middle-IR `ty::BoundConstness` collapses to two variants (`Const`, `Maybe`) inside `HostEffectClause` (renamed from `HostEffectPredicate` between `1.98.0-nightly` and `1.102.0-nightly`), because `Normal` emits only a plain `TraitClause` and no host-effect clause. The partial order is enforced verbatim by `BoundConstness::satisfies(self, goal)`, where `(Const, Const | Maybe) => true`, `(Maybe, Maybe) => true`, and `(Maybe, Const) => false`.
2. **Parser and HIR Syntax Evolution Between `1.98.0-nightly` and `1.102.0-nightly`/`HEAD`**: In `1.98.0-nightly` (`compiler/rustc_parse/src/parser/item.rs:662,677-680`), `parse_item_impl` still accepted both prefix `const impl Trait for T` and legacy infix `impl const Trait for T` (verified live by probe `ct_10`). By `1.102.0-nightly` (`3ef0c22cd:694-721`) and `HEAD` (`01afe5348:695-721`), the post-`impl` `self.parse_constness` recovery was removed, making prefix `const impl` mandatory. By contrast, legacy `~const` bound syntax remains accepted as an alias for `[const]` in `parse_bound_constness` (`compiler/rustc_parse/src/parser/ty.rs:1379-1402`) across all three revisions (verified live by probe `ct_18`), and `hir::Constness` expanded from `{ Const, NotConst }` (`1.98.0-nightly`) to `{ Const { always: bool }, NotConst }` (`1.102.0-nightly` and `HEAD`) to reserve an experimental `comptime` (`always: true`) mode.
3. **Context-Monotone Effect Enforcement and Dual-Solver Agreement**: Both HIR type checking (`FnCtxt::enforce_context_effects`, `compiler/rustc_hir_typeck/src/callee.rs:1135-1206`) and MIR const checking (`Checker::check_const_conditions`, `compiler/rustc_const_eval/src/check_consts/check.rs:348-389`; `NeedsNonConstDrop::in_any_value_of_ty`, `qualifs.rs:178-207`) map caller context via a single rule: `Const`/`Static` -> `BoundConstness::Const`, `ConstFn` -> `BoundConstness::Maybe`, runtime `fn` -> skip `[const]` conditions (while still enforcing unconditional `T: const Trait` clauses). Across all 18 live test cases on `1.98.0-nightly` and all 9 baseline cases on `1.102.0-nightly`, `-Z next-solver=globally` (`effect_goals.rs`) and `-Z next-solver=no` (`effects.rs`) produce **zero divergences** and byte-identical stderr diagnostics.
4. **Single-Impl Coherence Guarantees CTFE-vs.-Runtime Observational Confluence**: Trait overlap checking (`compiler/rustc_trait_selection/src/traits/coherence.rs:112-167`, `specialization_graph.rs:140-160`) unifies `tcx.impl_trait_ref(impl_def_id)` and `tcx.clauses_of(impl_def_id)` without inspecting `impl_trait_header.constness`. Consequently, declaring both `const impl MyOp for u32` and `impl MyOp for u32` fails immediately with `E0119` (`ct_05`). Because every `(Trait, Self, Args)` tuple has at most one non-overlapping implementation, and both solvers select a `HostEffect` impl by requiring the unique matching trait impl to satisfy `impl_is_const`, compile-time evaluation and runtime execution are guaranteed to invoke the exact same MIR body.
5. **Generic Const Drop-Safety via `[const] Destruct` and `LiveDrop` (`E0493`)**: Dropping a local of unconstrained generic type `T` inside `const fn` fails `E0493` (`ct_03`) because `Checker::check_drop_terminator` (`check.rs:391-426`) runs flow-sensitive `NeedsDrop` and `NeedsNonConstDrop` qualifications; `NeedsNonConstDrop::in_any_value_of_ty` registers a `T: [const] Destruct` (in `const fn`) or `T: const Destruct` (in `const`/`static`) host-effect obligation. Structurally (`structural_traits.rs:787-872`, `effects.rs:449-548`), `ManuallyDrop<T>` is unconditionally `[const] Destruct` (and bypasses `needs_drop` before `const_destruct` gating even fires, verified in `ct_15`), primitives/references/raw pointers are trivial, and an ADT is `[const] Destruct` iff every field is `[const] Destruct` and any custom `Drop` impl is a `const impl Drop` whose own `[const]` bounds hold. When `T: [const] Destruct` is supplied under `#![feature(const_destruct)]`, `const fn` accepts `const impl Drop` types in CTFE (`ct_04`, `ct_14`) and non-`const` `Drop` types at runtime (`ct_04`), while rejecting non-`const` `Drop` types in `const` items with `E0277` (`ct_13`).
6. **Two-Layer Separation Between `ValTree` Canonicalization and `ConstParamTy_` Admissibility**: Type-level const generic arguments (`adt_const_params`, `min_adt_const_params`, `unsized_const_params`) require `T: ConstParamTy_`, where `pub trait ConstParamTy_: StructuralPartialEq + Eq {}` (`library/core/src/marker.rs:1105-1145`) is enforced recursively across every ADT field by `visit_implementation_of_const_param_ty` (`coherence/builtin.rs:170-245`) and `type_allowed_to_implement_const_param_ty` (`traits/misc.rs:92-201`). Although `const_to_valtree_inner` (`valtrees.rs:113-149`) can encode `ty::Float` as `ScalarInt` bits and integer-cast thin `ty::RawPtr` for *pattern elaboration* (`const_to_pat`), `ConstParamTy_` strictly forbids `f32`/`f64` (failing both `E0204` and `E0277` in `ct_07` because IEEE-754 `NaN != NaN` breaks reflexivity and `-0.0 == +0.0` collides `0x80000000` vs. `0x00000000`, verified in `ct_17`), raw pointers (failing `E0204` alone in `ct_08` because `*const u8: Eq` holds at runtime while CTFE pointer comparison fails with `RawPtrComparison` / `binary_ptr_op` due to linker/ASLR address nondeterminism, verified in `ct_16`), and unions (`valtrees.rs:174`, `misc.rs:122,150`). Unsized slices and `&'static str` lower to byte-element `ValTree::Branch` trees whose slice length is reconstructed from branch arity (`reconstruct_place_meta`, `valtrees.rs:223-255`, verified in `ct_09`).
7. **Anneal Trusted Boundary and Mechanized Lean `v4.34.1` Soundness**: At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirAst.lean` excludes `Float` types (mapped to `.unsupported`) and `TerminatorKind::Drop` (mapped to `.unsupported`), while capturing post-monomorphization MIR via `after_analysis` on pinned `1.98.0-nightly` (`f8a08b688`). Because `rustc` guarantees single-impl coherence and canonical `ValTree` monomorphization before MIR capture, supporting `const_trait_impl` and `adt_const_params` in Anneal requires no separate CTFE-vs.-runtime trait semantics, whereas adding `TerminatorKind::Drop` requires encoding drop-glue shims and preserving `NeedsNonConstDrop` drop-safety obligations. A standalone 1,660-LOC Lean `v4.34.1` formalization (`support/ConstTraitEffectsDestructAndValTreeSoundness.lean`) kernel-checks with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` `sorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, and `0` `._unsafe_rec` constants across all 779 compiled constants in `env.constants.map₁`, proving all core soundness theorems and four constructive sharpness counterexamples (`ce1`–`ce4`).

## Applicability

This report synthesizes evidence across seven durable upstream subjects recorded in `REPORT.json`, relating primary compiler source code at three revisions, live compiler execution at two nightly releases, the normative stable language reference, Anneal's trusted capture/MIR boundary, and a Lean 4 mechanization:

1. **Upstream `rustc` primary source (`rust-lang/rust` at `01afe534803b93889b85f6028117251cfbd431da`, `2026-11-22`)**: Directly audited across parsing (`rustc_parse`), AST/HIR (`rustc_ast`, `rustc_hir`), type IR (`rustc_type_ir`), HIR lowering/collection/coherence/WF (`rustc_hir_analysis`), HIR typeck (`rustc_hir_typeck`), old and next trait solvers (`rustc_trait_selection`, `rustc_next_trait_solver`), MIR lints (`rustc_mir_transform`), CTFE and `ValTree` lowering (`rustc_const_eval`, `rustc_ty_utils`, `rustc_middle`), built-in derive expansion (`rustc_builtin_macros`), and `libcore` (`library/core/src/marker.rs`, `library/core/src/ops/drop.rs`).
2. **Comparison nightly toolchain and source (`rust-lang/rust` `1.102.0-nightly` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`, `LLVM 23.1.5`, `x86_64-unknown-linux-gnu`)**: Both audited in source and represented empirically via the 9-case dual-solver baseline preserved in `support/baseline_1_102_nightly.json` (`ct_01`–`ct_09`).
3. **Executed nightly toolchain and source (`rust-lang/rust` `1.98.0-nightly` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`, `LLVM 22.1.6`, `x86_64-unknown-linux-gnu`)**: Directly audited in source and executed live across all 18 single-crate test cases (`ct_01`–`ct_18`) under both `-Z next-solver=globally` and `-Z next-solver=no` with `--edition=2024` (`support/probe_const_trait_impl_effects_and_adt_const_params.py`, `support/probe_results_1_98_nightly.json`).
4. **Anneal framework (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `2026-11-19`) and Anneal's pinned compiler (`rust-lang/rust` `1.98.0-nightly` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-30`)**: Audited directly in `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/audit/TrustedBoundary.lean`.
5. **Normative stable specification (`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `2026-11-17`)**: Audited for normative stable const evaluation (`src/const_eval.md`), const generic parameters (`src/items/generics.md`), structural equality for constant patterns (`src/patterns.md`), destructors (`src/destructors.md`), and numeric/pointer semantics (`src/types/numeric.md`, `src/types/pointer.md`).
6. **Lean 4 kernel verifier (`leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`, `2026-09-24`)**: Executed directly to kernel-check and audit `support/ConstTraitEffectsDestructAndValTreeSoundness.lean`.

### Version Scope Matrix (Shared vs. Version-Specific Behavior)

| Compiler Subsystem / Behavior | `1.98.0-nightly` (`14210df0e`) | `1.102.0-nightly` (`3ef0c22cd`) | `HEAD` (`01afe5348`) | Classification |
| :--- | :--- | :--- | :--- | :--- |
| `impl const Trait for T` legacy syntax (`compiler/rustc_parse/src/parser/item.rs`) | Accepted (`L677-680`, verified live in `ct_10`) alongside `const impl` | Removed (`L694-721`); only prefix `const impl` parses | Removed (`L695-721`); only prefix `const impl` parses | **Version-specific** |
| `T: ~const Trait` legacy bound syntax (`compiler/rustc_parse/src/parser/ty.rs`) | Accepted as `BoundConstness::Maybe` (verified live in `ct_18`) | Accepted as `BoundConstness::Maybe` (`L1382-1387` equivalent) | Accepted as `BoundConstness::Maybe` (`L1382-1387`) | **Shared** |
| Middle-IR host-effect struct (`compiler/rustc_type_ir/src/predicate.rs`) | `HostEffectPredicate<I>` (`L1009`) | `HostEffectClause<I>` (`L667`) | `HostEffectClause<I>` (`L668`) | **Version-specific** (rename) |
| `hir::Constness` representation (`compiler/rustc_hir/src/hir.rs`) | `Const \| NotConst` (`L4633-4637`) | `Const { always: bool } \| NotConst` (`L4523-4526`) | `Const { always: bool } \| NotConst` (`L4523-4526`) | **Version-specific** (`comptime` scaffolding) |
| Predicate collection module (`compiler/rustc_hir_analysis/src/collect/`) | `predicates_of.rs` (`1226` lines) | `clauses_of.rs` (`1202` lines) | `clauses_of.rs` (`1204` lines) | **Version-specific** (module rename) |
| Built-in `#[derive(ConstParamTy)]` macro module | Not in `deriving/const_param_ty.rs` (inline/prior path) | `compiler/rustc_builtin_macros/src/deriving/const_param_ty.rs` (`26` lines) | Identical `deriving/const_param_ty.rs` (`26` lines) | **Version-specific** (file extraction) |
| `unsized_const_params` tracking issue in `library/core/src/marker.rs` | `issue = "95174"` (`L1115`) | `issue = "128028"` (`L1139` equivalent; warning emitted in `ct_09`) | `issue = "128028"` (`L1139`) | **Version-specific** (issue metadata) |
| `ty::View(..)` arm in `effects.rs` and `valtrees.rs` | Absent | Absent | Added (`unimplemented!()`) | **Version-specific** (`1.102` -> `HEAD` diff) |
| `CallerBoundsIterator` + `consider_builtin_fn_static_trait_candidate` in `effect_goals.rs` | Absent | Absent | Added (`L12,41-51,311-316`) | **Version-specific** (`1.102` -> `HEAD` diff) |
| Core semantics of `ct_01`–`ct_09` (`[const]` bounds, `E0277`, `E0493`, `[const] Destruct`, `E0119` coherence, `ConstParamTy_` `E0204`/`E0277`, `&'static str` `ValTree`) and 0 next-vs.-old solver divergence | Verified by source + live execution | Verified by source + baseline execution | Verified by source (exact logic parity on audited paths; no `HEAD` binary executed) | **Shared** |

### Feature Flags, Invocation Mode, and Scope Separation

All unstable compiler observations require nightly feature gates (`#![feature(const_trait_impl)]`, `#![feature(const_destruct)]`, `#![feature(adt_const_params)]`, and `#![feature(unsized_const_params)]`), `--edition=2024`, and explicit solver selection (`-Z next-solver=globally` vs. `-Z next-solver=no`) on `x86_64-unknown-linux-gnu`. Claims about `HEAD` (`01afe5348`) runtime behavior are **derived** from direct source diffing against `1.102.0-nightly` (`3ef0c22cd`), where `effects.rs`, `effect_goals.rs`, `valtrees.rs`, and `check.rs` differ only in non-functional refactors (`CallerBoundsIterator`, `ty::View(..) => unimplemented!()`, and `consider_builtin_fn_static_trait_candidate`). No `HEAD` binary or `f8a08b688` binary was executed; claims about Anneal's pinned `f8a08b688` apply strictly to the compiler version pin and MIR AST gates inspected in `joshlf/anneal@c131b320e`.

## Findings

### 1. Const Trait Effects: Syntax Evolution, Three-Point Bound Lowering, and `HostEffectClause` Architecture

Basis: normative + source + execution

#### 1.1 Normative Baseline vs. Unstable `const_trait_impl` Extension

In the stable Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/const_eval.md:235-290`), a *const context* (`r[const-eval.const-context.def]`) comprises array type/repeat length expressions, initializers of `const` items, `static` items, and enum discriminants, const generic arguments, and `const { ... }` blocks. A `const fn` (`r[const-eval.const-fn.intro]`, `r[const-eval.const-fn.const-context]`, `r[const-eval.const-fn.outside-context]`) is interpreted in the target environment when called from a const context and executes identically to an ordinary function outside a const context, while its body may only use constant expressions (`r[const-eval.const-fn.body-restriction]`). Stable Rust has no `const trait`, `const impl`, or effect-polymorphic trait bounds, so generic `const fn`s cannot call trait methods on generic type parameters.

The unstable `const_trait_impl` feature lifts this restriction by introducing three coordinated constructs:
- **`const trait Foo`**: declares that implementations of `Foo` *may* be marked `const impl` and that bounds on `Foo` may carry `const` or `[const]` modifiers.
- **`const impl Foo for Bar`**: declares an implementation whose methods are conditionally const (const whenever the `impl`'s own `[const]` where-bounds hold) and whose body is subjected to const checking.
- **Effect-qualified trait bounds**: `T: const Foo` (unconditionally const) and `T: [const] Foo` (conditionally const, required to be `const` iff the enclosing item is evaluated in a const context).

#### 1.2 Parser Evolution: `const impl` vs. `impl const` and Persistence of `~const`

Direct comparison of `compiler/rustc_parse/src/parser/item.rs` across `1.98.0-nightly` (`14210df0e`), `1.102.0-nightly` (`3ef0c22cd`), and `HEAD` (`01afe5348`) isolates a breaking syntax cleanup between `1.98` and `1.102`:

- **At `1.98.0-nightly` (`14210df0e`, `item.rs:662-684`)**, `parse_item_impl` parses constness *before* `impl` (`let mut constness = self.parse_constness(Case::Sensitive);`) and then executes a fallback recovery *after* `impl<...>`:
  ```rust
  if let Const::No = constness {
      // FIXME(const_trait_impl): disallow `impl const Trait`
      constness = self.parse_constness(Case::Sensitive);
  }
  if let Const::Yes(span) = constness {
      self.psess.gated_spans.gate(sym::const_trait_impl, span);
  }
  ```
  Consequently, `1.98.0-nightly` accepts both `const impl LegacyOp for u32` and `impl const LegacyOp for u32` (verified live in `ct_10`, returning `LEGACY_IMPL_CONST=15` under both solvers).
- **At `1.102.0-nightly` (`3ef0c22cd`, `item.rs:694-721`) and `HEAD` (`01afe5348`, `item.rs:695-721`)**, `constness` is immutable (`let constness = self.parse_constness(Case::Sensitive);`) before `safety` and `impl`, and the post-generics `self.parse_constness` block is completely gone. Only prefix `const impl` is accepted, matching the diagnostic suggestion emitted by `1.102.0-nightly` in `ct_02` (`help: make the impl of trait Combine const` -> `+ const impl Combine for NonConst`).

By contrast, in `compiler/rustc_parse/src/parser/ty.rs:1379-1402` (`01afe5348`), `parse_bound_constness` preserves **three** syntactic forms across all three revisions:

```rust
pub fn parse_bound_constness(&mut self) -> PResult<'a, BoundConstness> {
    // FIXME(const_trait_impl): remove `~const` parser support once bootstrap has the new syntax
    // in rustfmt
    Ok(if self.eat(exp!(Tilde)) {
        let tilde = self.prev_token.span;
        self.expect_keyword(exp!(Const))?;
        let span = tilde.to(self.prev_token.span);
        self.psess.gated_spans.gate(sym::const_trait_impl, span);
        BoundConstness::Maybe(span)
    } else if self.can_begin_maybe_const_bound() {
        let start = self.token.span;
        self.bump();
        self.expect_keyword(exp!(Const)).unwrap();
        self.bump();
        let span = start.to(self.prev_token.span);
        self.psess.gated_spans.gate(sym::const_trait_impl, span);
        BoundConstness::Maybe(span)
    } else if self.eat_keyword(exp!(Const)) {
        self.psess.gated_spans.gate(sym::const_trait_impl, self.prev_token.span);
        BoundConstness::Always(self.prev_token.span)
    } else {
        BoundConstness::Never
    })
}
```

Both `~const` (`ct_18`) and `[const]` (`ct_01`) parse to identical `ast::BoundConstness::Maybe(span)`, `const` parses to `ast::BoundConstness::Always(span)`, and an unadorned bound parses to `ast::BoundConstness::Never`. Furthermore, `parse_trait_bound_modifiers` (`ty.rs:1349-1374`) enforces strict mutual exclusivity between `const`/`[const]` and `?`/`!` polarities (`PolarityAndModifiers`).

#### 1.3 Lowering from Three-Point `hir::BoundConstness` to Two-Point `ty::HostEffectClause`

In `compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs:1078-1154` (`01afe5348`), `HirTyLowerer::lower_poly_trait_ref` lowers HIR bounds under a `PredicateFilter` in two disjoint passes:

1. **Const-trait gate (`L1078-1106`)**: If `constness` is `hir::BoundConstness::Always` or `Maybe` and `!tcx.is_const_trait(trait_def_id)`, lowering immediately emits `ConstBoundForNonConstTrait` (forbidding `const` or `[const]` modifiers on non-`const` traits).
2. **Normal predicate collection (`PredicateFilter::All | SelfOnly | SelfAndAssociatedTypeBounds`, `L1111-1132`)**:
   - Every positive trait bound always emits its base `ty::ClauseKind::Trait` clause.
   - If `constness` is `hir::BoundConstness::Always(_)`, lowering **also** emits `poly_trait_ref.to_host_effect_clause(tcx, ty::BoundConstness::Const)` directly into `clauses_of` (`predicates_of` at `1.98`). Because it lives in `clauses_of`, callers must prove `T: const Trait` unconditionally—even inside ordinary runtime `fn`s (verified live by `ct_11`).
   - If `constness` is `hir::BoundConstness::Maybe(_)`, lowering deliberately emits **no** `HostEffectClause` in `clauses_of` (`L1124-1129`: *"We don't emit a const bound here, since that would mean that we unconditionally need to prove a `HostEffect` predicate, even when the predicates are being instantiated in a non-const context. This is instead handled in the `const_conditions` query."*).
   - If `constness` is `hir::BoundConstness::Never`, no `HostEffectClause` is ever emitted.
3. **Conditional const-condition collection (`PredicateFilter::ConstIfConst | SelfConstIfConst`, `L1139-1152`)**:
   - Invoked by `const_conditions` and `explicit_implied_const_bounds` in `compiler/rustc_hir_analysis/src/collect/clauses_of.rs:1045-1204` (`predicates_of.rs` at `1.98`).
   - Converts ONLY `hir::BoundConstness::Maybe(_)` bounds into `ty::HostEffectClause { trait_ref, constness: ty::BoundConstness::Maybe }` and strips the wrapper to store `&[(ty::PolyTraitRef, Span)]` indexed by `DefId`.
   - For trait items (`TraitItemKind::Fn | Type`) and conditionally-const impl items (`ImplItemKind::Fn | Type`), `const_conditions` chains the parent item's const conditions (`has_parent = true`, `clauses_of.rs:1066-1075`).

Inside `compiler/rustc_type_ir/src/predicate.rs:668-672,740-758` (`01afe5348`; `L667-671,739-757` at `3ef0c22cd`; `L1009-1012,1079-1097` at `14210df0e` as `HostEffectPredicate`), the middle-IR representation is:

```rust
pub struct HostEffectClause<I: Interner> {
    pub trait_ref: ty::TraitRef<I>,
    #[lift(identity)]
    pub constness: BoundConstness,
}

pub enum BoundConstness {
    /// `Type: const Trait` -- unconditionally const, even in a runtime function.
    Const,
    /// `Type: [const] Trait` -- requires resolving to const only in a const context.
    Maybe,
}

impl BoundConstness {
    pub fn satisfies(self, goal: BoundConstness) -> bool {
        match (self, goal) {
            (BoundConstness::Const, BoundConstness::Const | BoundConstness::Maybe) => true,
            (BoundConstness::Maybe, BoundConstness::Maybe) => true,
            (BoundConstness::Maybe, BoundConstness::Const) => false,
        }
    }
}
```

Together with the absent-clause (`Normal`/`Never`) runtime-only level, this realizes the three-point semilattice `Always <= Maybe <= Normal` (`Const` satisfies `Const`, `Maybe`, and `Normal`; `Maybe` satisfies `Maybe` and `Normal` but **not** `Const`; `Normal` satisfies only `Normal`). Live probe `ct_12` directly exercises the `(Maybe, Const) => false` entry: inside `const fn only_maybe<T: [const] Op>(x: T)`, calling `need_always<T: const Op>(x)` fails with `E0277: the trait bound T: const Op is not satisfied` under both solvers.

#### 1.4 `hir::Constness` Evolution (`comptime` Scaffolding)

Between `1.98.0-nightly` (`hir.rs:4633-4637`) and `1.102.0-nightly`/`HEAD` (`hir.rs:4523-4544`), `hir::Constness` changed from a two-variant unit enum (`Const | NotConst`) to:

```rust
pub enum Constness {
    Const { always: bool },
    NotConst,
}
```

where `Const { always: false }` is standard `const` (`"const"`) and `Const { always: true }` is experimental `"comptime"`. In `callee.rs:1144-1157`, calling a `Const { always: true }` function outside `Const`/`Static` contexts emits `ComptimeFnCalledOutsideConstContext`, while `effects.rs:471,576,610-613` explicitly bails out or marks `unimplemented!("FIXME(comptime)")` on `always: true`. Standard `const_trait_impl` and `const_destruct` programs exclusively use `Const { always: false }`.

---

### 2. Dual-Solver Evaluation (`-Z next-solver=globally` vs. `-Z next-solver=no`) and Context-Monotone Effect Enforcement

Basis: source + execution

#### 2.1 Call-Site Effect Instantiation (`HIR` Primary Gate + `MIR` Secondary Cross-Check)

At every function or method call during HIR type checking, `FnCtxt::enforce_context_effects` (`compiler/rustc_hir_typeck/src/callee.rs:1135-1206` at `01afe5348` and `3ef0c22cd`; `L1019-1073` at `14210df0e`) determines the caller's required host polarity from `tcx.hir_body_const_context(self.body_def_id)`:

```rust
let host = match const_context {
    Some(hir::ConstContext::Const { .. } | hir::ConstContext::Static(_)) => {
        ty::BoundConstness::Const
    }
    Some(hir::ConstContext::ConstFn) => ty::BoundConstness::Maybe,
    None => return,
};
```

When `tcx.features().const_trait_impl()` is enabled and `tcx.is_conditionally_const(callee_did)` holds, `enforce_context_effects` instantiates `tcx.const_conditions(callee_did)` with `callee_args` and registers each condition as a `HostEffectClause` obligation with `constness = host` (`ObligationCauseCode::HostEffectInExpr`).

Crucially, `const_eval` performs a defense-in-depth re-check during MIR const-checking in `compiler/rustc_const_eval/src/check_consts/check.rs:348-389`: it computes the exact same `host_polarity` (`ConstFn -> Maybe`, `Static | Const -> Const`), evaluates all instantiated `const_conditions`, and if any fail emits a `span_delayed_bug("this should have reported a [const] error in HIR")`. Thus:
- Calling `apply<NonConst>` inside `pub const BAD: NonConst = ...` (`ct_02`) maps `host = BoundConstness::Const`, registers `NonConst: const Combine`, and fails during HIR typeck with `E0277`.
- Calling `apply<NonConst>` inside runtime `fn main()` (`ct_01`) hits `const_context = None => return`, skipping `const_conditions` while retaining the ordinary `NonConst: Combine` trait bound—succeeding at runtime.
- Calling `require_always_const<RuntimeOnly>` inside runtime `fn main()` (`ct_11`) still registers `RuntimeOnly: const Op` from `clauses_of` (independent of `enforce_context_effects`) and fails `E0277` at runtime.

#### 2.2 Next Trait Solver (`effect_goals.rs`) vs. Old Trait Solver (`effects.rs`)

Both trait solvers evaluate `HostEffectClause` goals over the same candidate categories, but with an important structural difference in how base trait validity and impl selection are sequenced:

1. **Next Trait Solver (`compiler/rustc_next_trait_solver/src/solve/effect_goals.rs:21-520` at `01afe5348`)**:
   - Entry point `EvalCtxt::compute_host_effect_goal` (`L504-519`):
     ```rust
     let (_, proven_via) = self.probe(|_| ProbeKind::ShadowedEnvProbing).enter(|ecx| {
         let trait_goal: Goal<I, ty::TraitClause<I>> =
             goal.with(ecx.cx(), goal.predicate.trait_ref);
         ecx.compute_trait_goal(trait_goal)
     })?;
     self.assemble_and_merge_candidates(
         proven_via,
         goal,
         |_ecx| None,
         |_ecx| Err(NoSolution.into()),
     )
     ```
     The next solver **first** proves the underlying `TraitClause` goal inside a probe to determine `proven_via` (for shadowed-env preference), and only then assembles `HostEffectClause` candidates via the shared `assembly::GoalKind` machinery!
   - **Param-env assumption matching (`L41-89`)**: `fast_reject_assumption` checks `host_clause.def_id() == goal.predicate.def_id() && host_clause.constness().satisfies(goal.predicate.constness)` plus `DeepRejectCtxt::relate_rigid_rigid`.
   - **Conditionally const alias bounds (`L97-150`)**: `consider_additional_alias_assumptions` reads `explicit_implied_const_bounds(def_id)` and, upon matching, registers `cx.const_conditions(def_id)` at `goal.predicate.constness` (`GoalSource::AliasBoundConstCondition`) because `[const]` item bounds on an associated/opaque type hold only if the alias's own `[const]` conditions hold.
   - **User `impl` candidate (`L152-213`)**: `consider_impl_candidate` rejects `default impl` (`L171-173`), negative impls (`L175-178`), and crucially checks `if !cx.impl_is_const(impl_def_id) { return Err(NoSolution.into()); }` (`L180-182`). For a passing `const impl`, it adds BOTH ordinary `clauses_of(impl_def_id)` AND `const_conditions(impl_def_id)` instantiated at `goal.predicate.constness` (`L190-209`).
   - **Built-in const traits (`L224-496`)**: Only `Copy`/`Clone` (`L275-302`), `Fn`/`FnMut`/`FnOnce` on `FnDef`/closures (`L319-365`, NOT `FnPtr`), and `Destruct` (`L438-460`) have built-in host-effect candidates. Auto traits (`L224-230` -> `delay_bug`), `Sized`/`MetaSized`, `AsyncFn*`, `Tuple`, `Pointee`, `Future`, `Iterator`, `Coroutine`, `TransmuteFrom`, `Unsize`, and `Field` are never built-in const.
   - **Method-signature/impl-entailment comparison (`compare_impl_item.rs:227-315,2518-2578`)**: When checking a `const impl` item against its `const trait` definition, `rustc` checks that the impl's `[const]` where-bounds are entailed by the trait's `[const]` bounds instantiated at `BoundConstness::Maybe`.

2. **Old Trait Solver (`compiler/rustc_trait_selection/src/traits/effects.rs:25-690` at `01afe5348`)**:
   - Explicitly forbids running in coherence mode (`if selcx.typing_mode().is_coherence() { span_bug!(...); }`, `L29-34`) because coherence unconditionally builds its `InferCtxt` with `.with_next_trait_solver(true)` (`coherence.rs:196`).
   - Evaluates a prioritized waterfall (`L43-79`): (1) `param_env` `HostEffect` bounds (`L126-168`), (2) conditionally const alias item bounds (`L172-264`), (3) unconditional `HostEffect` item bounds (`L268-332`), (4) built-in `Copy`/`Clone`/`Destruct`/`Fn*` (`L334-595`), (5) user `impl` via `selcx.select(&trait_ref)` followed by checking `tcx.impl_trait_header(impl_def_id).constness == Const { always: false }` and instantiating `tcx.const_conditions(impl_def_id)` (`L597-654`), and (6) trait aliases (`L656-690`).
   - Because `selcx.select` relies on trait coherence to pick the unique matching user `impl` before checking `constness`, and `effect_goals.rs` checks `impl_is_const` over the same coherent impl set, both solvers compute identical truth values on all coherent crates (mechanized in `oldSolver_iff_nextSolver` and corroborated by 0 divergences across all 18 live test cases).

---

### 3. Single-Impl Coherence, `E0119` Rejection, and CTFE-vs.-Runtime Observational Confluence

Basis: source + execution + derived

A foundational design question for effect-polymorphic traits is whether a type `T` should be allowed to provide both an optimized runtime `impl MyOp for u32` and a separate `const impl MyOp for u32` for CTFE. `rustc` **strictly forbids** this pattern, and the mechanism is structurally enforced in coherence:

1. **Coherence Entry Point (`compiler/rustc_hir_analysis/src/coherence/mod.rs:164-189`)**: `coherent_trait(tcx, def_id)` triggers `tcx.ensure_result().specialization_graph_of(def_id)`, which inserts every local and upstream impl into the trait's specialization tree (`compiler/rustc_trait_selection/src/traits/specialize/specialization_graph.rs:76-160`).
2. **Overlap Check Ignores Impl Constness (`compiler/rustc_trait_selection/src/traits/coherence.rs:112-228`)**:
   - `overlapping_trait_impls` (`L112-134`) extracts ONLY `tcx.impl_trait_ref(impl1_def_id)` and `tcx.impl_trait_ref(impl2_def_id)` for fast rejection, then calls `overlap` (`L172-228`).
   - `overlap` constructs an `InferCtxt` in `TypingMode::Coherence` with `.with_next_trait_solver(true)` (`L193-198`), builds `ImplHeader { impl_args, self_ty, trait_ref, predicates }` via `fresh_impl_header` (`L147-167`), and equates the two headers (`equate_impl_headers`).
   - **`impl_trait_header.constness` is nowhere present in `ImplHeader` or `TraitRef`**, nor are `const_conditions` consulted to disjoin overlapping impls.
3. **Resulting Rejection (`E0119`)**: For `ct_05`:
   ```rust
   #![feature(const_trait_impl)]
   pub const trait MyOp { fn op(self) -> u32; }
   const impl MyOp for u32 { fn op(self) -> u32 { 1 } }
   impl MyOp for u32 { fn op(self) -> u32 { 2 } }
   ```
   Both impls produce the identical `TraitRef` `u32: MyOp` with empty `clauses_of`. Neither specializes the other (`tcx.specializes` is `false` in both directions), and `MyOp` is not a `#[marker]` trait (`impls_are_allowed_to_overlap` returns `None`), so `specialization_graph::insert` immediately reports **`error[E0119]: conflicting implementations of trait MyOp for type u32`** under both `-Z next-solver=globally` and `-Z next-solver=no` on both `1.98.0-nightly` and `1.102.0-nightly`.

**Derived Consequence — CTFE-vs.-Runtime Observational Confluence**: Because coherence enforces at most one non-overlapping impl per `(Trait, Self, Args)` regardless of constness, monomorphization (`Instance::resolve`) resolves a trait method call `<T as Trait>::method` to the exact same `impl_def_id` whether the call executes inside CTFE (`rustc_const_eval`) or inside runtime codegen (`rustc_codegen_llvm`). A `const impl` is therefore a **subset refinement** of ordinary trait impls (identical semantics, restricted to const-evaluable operations), never an alternate compile-time overload. (As mechanized in `ce1_dual_const_runtime_impl_breaks_ctfe_confluence`, allowing dual impls immediately permits `const C = MyOp::op(0)` to evaluate to `1` while runtime `MyOp::op(0)` evaluates to `2`, breaking the normative `r[const-eval.const-fn.outside-context]` confluence guarantee.)

*(Note on `const_eval_select`)*: Separate from trait coherence, `core::intrinsics::const_eval_select` is an explicit `unsafe`/internal escape hatch whose soundness contract requires callers to prove observational equivalence between its compile-time and runtime arms; `const_trait_impl` itself never introduces divergence through trait dispatch.

---

### 4. Generic Destructors in Const Contexts: `const_destruct`, `[const] Destruct`, `LiveDrop` (`E0493`), and `CheckConstItemMutation`

Basis: normative + source + execution

#### 4.1 Why Unconstrained Generic Drops Fail `E0493` in `const fn`

Under stable Rust (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/destructors.md:7-54`), exiting a drop scope invokes `core::ptr::drop_in_place::<T>` on initialized values. Inside a `const fn`, a generic type parameter `T` has no bound guaranteeing that its destructor can be evaluated at compile time—a caller in a `const` item could instantiate `T` with a type whose `Drop::drop` performs heap deallocation, FFI, or I/O.

`rustc` enforces compile-time drop safety through a four-stage pipeline across `libcore`, MIR const checking, and both trait solvers:

1. **Trait Definitions in `libcore`**:
   - `library/core/src/ops/drop.rs:206-210` (`01afe5348`): `#[lang = "drop"] #[rustc_const_unstable(feature = "const_destruct", issue = "133214")] pub const trait Drop`.
   - `library/core/src/marker.rs:1058-1064` (`01afe5348`; `L1056-1062` at `14210df0e`):
     ```rust
     #[unstable(feature = "const_destruct", issue = "133214")]
     #[rustc_const_unstable(feature = "const_destruct", issue = "133214")]
     #[lang = "destruct"]
     #[diagnostic::on_unimplemented(message = "can't drop `{Self}`")]
     #[rustc_deny_explicit_impl]
     #[rustc_dyn_incompatible_trait]
     pub const trait Destruct: PointeeSized {}
     ```
     Every Rust type implements non-const `Destruct` (built-in), and `#[rustc_deny_explicit_impl]` (`coherence/mod.rs:74-91`, `E0322`) prevents users from writing manual `impl Destruct` blocks that could lie about field destructors.

2. **MIR Flow-Sensitive Qualification (`compiler/rustc_const_eval/src/check_consts/check.rs:391-426`, `qualifs.rs:178-221`)**:
   At every MIR `TerminatorKind::Drop { place, .. }`, `Checker::check_drop_terminator` performs two sequential checks:
   - **Check 1 (`NeedsDrop`)**: Queries flow-sensitive `self.qualifs.needs_drop` (for locals) or `NeedsDrop::in_any_value_of_ty` (for projected places). If `!needs_drop`, it **returns immediately** (`check.rs:405-407`)—nothing is enforced and `#![feature(const_destruct)]` is not even triggered! (This explains our live probe `ct_15`: `ManuallyDrop<NonConstDrop>` inside `const fn` emits `warning: feature const_destruct is declared but not used` because `ManuallyDrop` has `needs_drop == false`.)
   - **Check 2 (`NeedsNonConstDrop`)**: If `needs_drop` is true, it queries `self.qualifs.needs_non_const_drop`. In `qualifs.rs:178-207`, `NeedsNonConstDrop::in_any_value_of_ty` registers a `HostEffectClause` obligation for `ty: <constness> Destruct`:
     ```rust
     ty::Binder::dummy(ty::TraitRef::new(cx.tcx, destruct_def_id, [ty]))
         .to_host_effect_clause(
             cx.tcx,
             match cx.const_kind() {
                 rustc_hir::ConstContext::ConstFn => ty::BoundConstness::Maybe,
                 rustc_hir::ConstContext::Static(_)
                 | rustc_hir::ConstContext::Const { .. } => ty::BoundConstness::Const,
             },
         )
     ```
     and returns `!ocx.evaluate_obligations_error_on_ambiguity().no_errors()`.
   - **Non-structural ADT Drop Subtleties (`qualifs.rs:209-221`)**: `NeedsNonConstDrop::is_structural_in_adt_value` returns `!adt.has_dtor(cx.tcx)`. Once an ADT declares a custom `Drop` impl, `rustc` refuses value-based field tracking for that ADT because (a) the `Drop` impl may carry `[const]` bounds absent from the ADT definition itself, and (b) `Drop::drop(&mut self)` may mutate fields before recursive field drops run.

3. **Error and Feature-Gate Dispatch (`compiler/rustc_const_eval/src/check_consts/ops.rs:579-641`)**:
   `check_drop_terminator` passes `ops::LiveDrop { dropped_at, dropped_ty, needs_non_const_drop }` to `check_op_spanned`:
   - If `needs_non_const_drop == true`, `status_in_item` returns `Status::Forbidden` -> hard error **`E0493: destructor of T cannot be evaluated at compile-time`** (`ct_03`). On nightly, `build_error` (`L620-637`) explicitly checks `if let Param(param_ty) = self.dropped_ty.kind()` and suggests adding `: [const] Destruct`.
   - If `needs_non_const_drop == false` (meaning `T: [const] Destruct` *was* proven, e.g., via a concrete `const impl Drop` or a `T: [const] Destruct` bound), `status_in_item` returns `Status::Unstable { gate: sym::const_destruct, .. }`: compiling cleanly when `#![feature(const_destruct)]` is active (`ct_04`, `ct_14`) and emitting a gated `E0493` feature error otherwise.
   - **Precise Live-Drop Checking (`post_drop_elaboration.rs:14-98`)**: Under `#![feature(const_precise_live_drops)]`, `check_live_drops` runs *after* MIR drop elaboration (so moved-out locals have no live `Drop` terminator) and explicitly skips unwind cleanup blocks (`if block.is_cleanup { return; }`, `L63-65`) because CTFE panics abort compilation immediately rather than unwinding.

4. **Structural `[const] Destruct` Solver Rules (`structural_traits.rs:787-872` and `effects.rs:449-548`)**:
   Both the next solver (`const_conditions_for_destruct`) and old solver (`evaluate_host_effect_for_destruct_goal`) enforce identical structural decomposition rules:

   | Type Kind | `[const] Destruct` Sub-obligations | Outcome |
   | :--- | :--- | :--- |
   | `ManuallyDrop<T>` (`adt_def.is_manually_drop()`) | `[]` | Trivially satisfied (`ct_15`) |
   | Primitives (`bool`, `char`, `i*`, `u*`, `f*`, `str`, `*const`/`*mut`, `&`/`&mut`, `FnDef`, `FnPtr`, `!`) | `[]` | Trivially satisfied |
   | `[T; N]`, `[T]`, `Pat(T, ..)` | `[T: Destruct]` | Structural on element |
   | `(T_0, ..., T_{k-1})` | `[T_0: Destruct, ..., T_{k-1}: Destruct]` | Structural on all fields |
   | Closure | `[tupled_upvars_ty: Destruct]` | Structural on captured upvars |
   | `struct`/`enum` ADT with no `Drop` impl | `[F_i: Destruct]` for all fields `F_i` | Structural on all fields |
   | `struct`/`enum` ADT with `const impl Drop` (`Const { always: false }`) | `[F_i: Destruct]` **plus** `[Self: Drop]` (as `HostEffectClause`) | Satisfied iff fields are `[const] Destruct` AND `Drop` impl's own `[const]` bounds hold (`ct_04`, `ct_14`) |
   | `struct`/`enum` ADT with non-`const` `impl Drop` (`NotConst`) | `Err(NoSolution)` | Rejected in `const`/`const fn` (`ct_13`); allowed at runtime (`ct_04`) |
   | `ty::Param(T)` | Only via `param_env` `HostEffect` bound (`T: [const] Destruct` / `T: const Destruct`) | Rejected (`E0493`) if unbounded (`ct_03`); polymorphic if `[const] Destruct` (`ct_04`) |
   | `dyn Trait`, `Coroutine`, `CoroutineClosure`, `CoroutineWitness`, `UnsafeBinder`, `Foreign`, unnormalized `Alias` | `Err(NoSolution)` (unless satisfied by `param_env` / alias bounds) | Rejected in const contexts |

#### 4.2 Interaction with `CheckConstItemMutation` MIR Lint

In `compiler/rustc_mir_transform/src/check_const_item_mutation.rs:35-74` (`01afe5348`), the `CONST_ITEM_MUTATION` MIR lint suppresses its field-mutation warning (`is_const_item_without_destructor`) whenever a concrete `const` item's type satisfies `ty.needs_drop(tcx, typing_env)` (because mutating a temporary copy of a `const` item with a `Drop` impl can be observed by `Drop::drop`, such as `LOG.msg = "wow"`), while falling through to warn when `ty.has_param()` (since `needs_drop` is conservatively `true` for type parameters). Critically, this suppression queries runtime `needs_drop` (not `needs_non_const_drop`): whether a type's destructor is `const impl Drop` or non-`const` `impl Drop`, mutating a temporary copy of a `const` item in runtime code still invokes that destructor at scope exit.

---

### 5. Type-Level Const Generics: `adt_const_params`, `unsized_const_params`, `ConstParamTy_`, and `ValTree` Canonicalization

Basis: normative + source + execution + derived

#### 5.1 Normative Stable Baseline vs. `adt_const_params` / `unsized_const_params`

In the stable Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/items/generics.md:125-225`, `compiler/rustc_hir_analysis/src/check/wfcheck.rs:829-852`), const generic parameters are restricted to integers (`u*`, `i*`, `usize`, `isize`), `bool`, and `char`. Types such as `f32`/`f64`, raw pointers, function pointers, structs, enums, and slices are rejected in `check_param_wf` (`wfcheck.rs:800-912`).

When `#![feature(min_adt_const_params)]` or `#![feature(adt_const_params)]` is enabled (`wfcheck.rs:810-819`), `check_param_wf` replaces the hardcoded primitive allowlist with a single trait bound: `ty: ConstParamTy_` (`LangItem::ConstParamTy`).

#### 5.2 The `ConstParamTy_` Trait, Derive Macro, and Recursive Field Gate (`E0204`)

In `library/core/src/marker.rs:1099-1145` (`01afe5348`; `L1075-1121` at `14210df0e`), `rustc` splits the marker trait from its built-in derive macro:

```rust
#[lang = "const_param_ty"]
#[unstable(feature = "const_param_ty_trait", issue = "95174", implied_by = "unsized_const_params")]
pub trait ConstParamTy_: StructuralPartialEq + Eq {}

#[rustc_builtin_macro]
#[allow_internal_unstable(const_param_ty_trait)]
#[unstable(feature = "min_adt_const_params", issue = "154042", implied_by = "adt_const_params")]
pub macro ConstParamTy($item:item) { /* compiler built-in */ }

marker_impls! {
    #[unstable(feature = "min_adt_const_params", issue = "154042")]
    ConstParamTy_ for
        usize, u8, u16, u32, u64, u128,
        isize, i8, i16, i32, i64, i128,
        bool, char, (),
        {T: ConstParamTy_, const N: usize} [T; N],
}

marker_impls! {
    #[unstable(feature = "unsized_const_params", issue = "128028")]
    #[unstable_feature_bound(unsized_const_params)]
    ConstParamTy_ for
        str,
        {T: ConstParamTy_} [T],
        {T: ConstParamTy_ + ?Sized} &T,
}
```

At `1.102.0-nightly` and `HEAD`, `compiler/rustc_builtin_macros/src/deriving/const_param_ty.rs:7-26` expands `#[derive(ConstParamTy)]` to an `impl ConstParamTy_` with `additional_bounds: [cmp::Eq]` and `supports_unions: false`. Then, during trait coherence, `visit_implementation_of_const_param_ty` (`compiler/rustc_hir_analysis/src/coherence/builtin.rs:170-245`) invokes `type_allowed_to_implement_const_param_ty` (`compiler/rustc_trait_selection/src/traits/misc.rs:92-201`), which enforces five hard structural invariants:

1. **Only structs, enums, and allowlisted built-ins**: `ty::Adt(adt, args) if adt.is_enum() || adt.is_struct()` is permitted; **unions**, **`f32`/`f64`**, **`*const T`/`*mut T`**, **`&mut T`**, **`fn(...)`**, **`dyn Trait`**, and closures hit `NotAnAdtOrBuiltinAllowed` (`misc.rs:150`).
2. **Recursive per-field `ConstParamTy_` check (`all_fields_implement_trait`, `misc.rs:204-284`)**: Every field of every variant is normalized and checked for `field_ty: ConstParamTy_` in its own `ObligationCtxt`, emitting **`error[E0204]: the trait ConstParamTy_ cannot be implemented for this type`** pointing to the exact infringing field (`builtin.rs:210-219`).
3. **Field-visibility & `#[non_exhaustive]` gating under `min_adt_const_params`**: Without full `adt_const_params`, private fields of more-visible structs (`builtin.rs:187-205`, `ConstParamTyFieldVisMismatch`) and `#[non_exhaustive]` variants (`misc.rs:123-134`, `NonExhaustive`) are rejected to prevent leaking private structural representations into public type equality.
4. **Feature-bound gate for unsized/reference types (`misc.rs:109-116,160-171`)**: `[T]`, `str`, and `&T` require `ty::ClauseKind::UnstableFeature(sym::unsized_const_params)`.
5. **Supertrait enforcement (`StructuralPartialEq + Eq`)**: Any type implementing `ConstParamTy_` must derive structural `PartialEq` (`#[derive(PartialEq)]`) AND satisfy `Eq` (reflexive, symmetric, transitive equivalence).

#### 5.3 Two-Layer Architecture: `ValTree` Structural Canonicalization vs. `ConstParamTy_` Rejection of Floats and Raw Pointers

`ValTree` (`compiler/rustc_middle/src/ty/consts/valtree.rs:29-105`) is an interned, structurally hashed, layout-independent tree with two constructors (`ValTreeKind::Leaf(ScalarInt)` and `ValTreeKind::Branch(&'tcx [ty::Const<'tcx>])`) created by `eval_to_valtree` -> `const_to_valtree_inner` (`compiler/rustc_const_eval/src/const_eval/valtrees.rs:21-219`):

- **Scalars (`L113-119`)**: `Bool | Int | Uint | Float | Char` become `ValTree::Leaf(ScalarInt)` (note: `ValTree` *does* store `Float` leaves ONLY because `ty::Value` is shared with constant pattern elaboration `const_to_pat`, explicitly documented at `valtree.rs:98-99` and normative `r[patterns.const.float]`).
- **Structs and tuples (`L21-60,169-190`)**: Become `ValTree::Branch([field_0, ..., field_{k-1}])`, stripping all padding bytes and memory layout artifacts. ZSTs become `ValTree::Branch([])` (`valtree_zst`).
- **Enums (`L40-46,179-189`)**: Prepend `ValTree::Leaf(variant_idx.as_u32())` (`u32`) before the active variant's field branches, so discriminant niches or packed encodings never create multiple representations of the same enum value.
- **References (`L155-158`)**: `ty::Ref` transparently dereferences the pointer (`ecx.deref_pointer(place)`) and canonicalizes the *pointee value*, completely erasing the pointer's CTFE `AllocId` and memory address!
- **Arrays, slices, and `&'static str` (`L63-80,160-162`)**: Lower to `ValTree::Branch([elem_0, ..., elem_{n-1}])` (UTF-8 `u8` leaves for `str`). When reconstructing a MIR `ConstValue` or `MPlaceTy` from a `ValTree` (`valtree_to_const_value`, `L298-408`), `reconstruct_place_meta` (`L223-255`) walks `struct_tail_raw` to the unsized `Slice`/`Str` tail and recovers `MemPlaceMeta::Meta(Scalar::from_target_usize(last_valtree.to_branch().len()))` directly from the branch arity! Thus `Route<"/api/v1/x">` (`9` byte leaves) and `Route<"/">` (`1` byte leaf) have structurally distinct `ValTree`s and reconstruct `LEN_API=9` and `LEN_ROOT=1` (`ct_09`).
- **Cycle and DoS guards (`L94-105`)**: `visited: FxHashSet<MPlaceTy>` catches cyclic const graphs (`ValTreeCreationError::CyclicConst`) and `VALTREE_MAX_NODES` bounds total tree size (`NodesOverflow`).

Crucially, `ty::Const::Value(ty::Value { ty, valtree })` is compared for **type equality** using derived structural equality (`#[derive(Hash, Eq, PartialEq)]` on `ValTree` and `Value`, `valtree.rs:29,100`). For type-level substitution `Foo<C1> == Foo<C2>` to obey Leibniz substitutivity (`P(Foo<C1>) <-> P(Foo<C2>)` for all type-level properties `P`) while remaining faithful to Rust's value equality `C1 == C2`, the type's equality relation MUST be a **deterministic, canonical equivalence relation**. Both `f32`/`f64` and `*const T` break this requirement in distinct, complementary ways:

1. **Why `f32`/`f64` are rejected (`ct_07` -> `E0204` + `E0277`; `ct_17`)**:
   - **Non-reflexivity (`NaN != NaN`)**: `f32` does not implement `Eq` (`r[type.numeric.float]`, live witness `ct_17`: `NAN_EQ_SELF=false`). If `f32` were allowed in `ConstParamTy_`, `Ty<NaN>` would equal `Ty<NaN>` by type reflexivity even though `NaN == NaN` is `false`. Consequently, `#[derive(PartialEq, Eq, ConstParamTy)] struct BadFloatParam(pub f32)` fails with **both** `E0204` (`f32` does not implement `ConstParamTy_`) and `E0277` (`f32: Eq` is not satisfied).
   - **Non-canonicity (`-0.0 == +0.0` with distinct bit patterns)**: Live witness `ct_17` demonstrates `EQ_ZEROS=true`, `BITS_EQ_ZEROS=false`, `POS_BITS=0x00000000`, `NEG_BITS=0x80000000`. Because `ValTree::Leaf` compares raw `ScalarInt` bits, `Foo<0.0>` and `Foo<-0.0>` would be *distinct* types despite `0.0 == -0.0` (breaking congruence), whereas collapsing them into one `ValTree` would violate Leibniz substitutivity for bit-observing operations like `C.to_bits()` or `1.0 / C` (`+inf` vs. `-inf`).
   - **NaN payload nondeterminism (`operator.rs:78`)**: CTFE float arithmetic (`binary_float_op`) models nondeterministic NaN payloads, further breaking canonical value identity.

2. **Why `*const T`/`*mut T` are rejected (`ct_08` -> `E0204` only; `ct_16`)**:
   - Unlike `f32`, `*const u8` **does** implement `PartialEq` and `Eq` at runtime (`r[type.pointer.raw.cmp]`), so `#[derive(PartialEq, Eq, ConstParamTy)] struct BadPtrParam(pub *const u8)` emits **only `E0204`** (`ConstParamTy_` not implemented) and **not `E0277`**.
   - However, in CTFE (`compiler/rustc_const_eval/src/const_eval/machine.rs:273-365,573-580`), pointers carry abstract `(AllocId, offset)` provenance with no compile-time concrete address:
     - `CompileTimeMachine::binary_ptr_op` (`L573-580`) unconditionally fails with `throw_unsup_format!("pointer arithmetic or comparison is not supported at compile-time")`.
     - Even before CTFE execution, `check_consts` (`ops.rs:693-701`, `RawPtrComparison`) rejects `(&A as *const u8) == (&B as *const u8)` in `const` items with `error: pointers cannot be reliably compared during const eval` (verified live in `ct_16`).
     - Even `guaranteed_cmp` (`machine.rs:280-365`) returns `2` (*unknown*) for pointers to distinct non-static constant allocations, one-past-the-end static pointers, or pointer-vs.-integer comparisons that may alias null—because the linker (ICF / `.rodata` merging) and OS loader (ASLR) determine final addresses at link/load time.
     - Correspondingly, `const_to_valtree_inner` (`valtrees.rs:130-149`) rejects every wide raw pointer (`BackendRepr::ScalarPair`) and every provenance-bearing thin pointer (`val.try_to_scalar_int()` fails in CTFE), allowing only integer-disguised thin pointers strictly for `const_to_pat` (`r[patterns.const.pointer]`) and never for `ConstParamTy_`.

3. **Unresolved `generic_const_exprs` Abstraction Layer (`compiler/rustc_ty_utils/src/consts.rs:16-402`)**:
   For symbolic const expressions (under `#![feature(generic_const_exprs)]`), `thir_abstract_const` (`consts.rs:368-398`) lifts polymorphic THIR expressions into `ty::ConstKind::Expr` using `recurse_build` (`L35-228`), explicitly excluding `BinOp::Offset` (`L22`), `RawBorrow`/`Deref` (`L153-155`), `Adt` (`L174-176`), `PointerCoercion` (`L178-180`), control flow (`L210-212`), and static/thread-local refs (`L218-223`), while concrete evaluated constants lower directly via `lit_to_const` / `ValTree::from_scalar_int` / `eval_to_valtree`.

---

### 6. Live 18-Case Differential Execution Across `1.98.0-nightly`, `1.102.0-nightly`, and Both Trait Solvers

Basis: execution

Running `support/probe_const_trait_impl_effects_and_adt_const_params.py` live on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with `--edition=2024` across both `-Z next-solver=globally` and `-Z next-solver=no` (`36` compiler invocations, `support/probe_results_1_98_nightly.json`) and comparing against the `1.102.0-nightly (3ef0c22cd 2026-11-11)` baseline (`support/baseline_1_102_nightly.json`) yields **0 solver divergences** on both toolchains:

| Case ID | Mechanism Tested | `1.98.0-nightly` (`next` & `old`) | `1.102.0-nightly` (`next` & `old`) | Solver Parity |
| :--- | :--- | :--- | :--- | :--- |
| `ct_01` | `const trait Combine`, `const impl`, `impl`, `const fn apply<T: [const] Combine>` in CTFE & runtime | `rc=0`, `CTFE=42 RT_CONST=42 RT_NONCONST=42` | `rc=0`, `CTFE=42 RT_CONST=42 RT_NONCONST=42` | Identical |
| `ct_02` | Calling `apply` with non-`const` impl inside `const BAD` | `rc=1`, `E0277` (`NonConst: const Combine`) | `rc=1`, `E0277` (`NonConst: const Combine`) | Identical |
| `ct_03` | `pub const fn drop_generic_in_const<T>(_x: T) {}` without `[const] Destruct` | `rc=1`, `E0493` (suggests `T: [const] Destruct`) | `rc=1`, `E0493` (suggests `T: [const] Destruct`) | Identical |
| `ct_04` | `const fn drop_generic<T: [const] Destruct>` with `const impl Drop` (CTFE) & `impl Drop` (runtime) | `rc=0`, `CONST_DESTRUCT_OK=77 RT=77` | `rc=0`, `CONST_DESTRUCT_OK=77 RT=77` | Identical |
| `ct_05` | Overlapping `const impl MyOp for u32` and `impl MyOp for u32` | `rc=1`, `E0119` (conflicting impls) | `rc=1`, `E0119` (conflicting impls) | Identical |
| `ct_06` | `#[derive(PartialEq, Eq, ConstParamTy)]` enum + struct `Config` as `const C: Config` | `rc=0`, `FAST=40 CHECKED=1` | `rc=0`, `FAST=40 CHECKED=1` | Identical |
| `ct_07` | `#[derive(PartialEq, Eq, ConstParamTy)] struct BadFloatParam(pub f32)` | `rc=1`, `E0204` + `E0277` (`f32: Eq`) | `rc=1`, `E0204` + `E0277` (`f32: Eq`) | Identical |
| `ct_08` | `#[derive(PartialEq, Eq, ConstParamTy)] struct BadPtrParam(pub *const u8)` | `rc=1`, `E0204` only (no `E0277`) | `rc=1`, `E0204` only (no `E0277`) | Identical |
| `ct_09` | `struct Route<const PATH: &'static str>` under `adt_const_params, unsized_const_params` | `rc=0`, `LEN_API=9 LEN_ROOT=1` + `incomplete_features` warning | `rc=0`, `LEN_API=9 LEN_ROOT=1` + `incomplete_features` warning | Identical |
| `ct_10` | Legacy `impl const LegacyOp for u32` syntax | `rc=0`, `LEGACY_IMPL_CONST=15` | *Not executed on 1.102* (source proves parser removed `impl const` in `item.rs:694-721`) | Identical (`1.98`) |
| `ct_11` | `fn require_always_const<T: const Op>` called at runtime with non-`const` impl | `rc=1`, `E0277` (`RuntimeOnly: const Op`) | *Not executed on 1.102* | Identical (`1.98`) |
| `ct_12` | `const fn only_maybe<T: [const] Op>` calling `need_always<T: const Op>` | `rc=1`, `E0277` (`T: const Op`) | *Not executed on 1.102* | Identical (`1.98`) |
| `ct_13` | Calling `drop_any<NonConstDrop>` (`T: [const] Destruct`) inside `const BAD_DROP` | `rc=1`, `E0277` (`NonConstDrop: const Destruct`) | *Not executed on 1.102* | Identical (`1.98`) |
| `ct_14` | Side-effecting `const impl<'a> Drop for DropMut<'a>` (`*self.slot += 57`) in CTFE & runtime | `rc=0`, `CTFE_DROP=99 RT_DROP=99` | *Not executed on 1.102* | Identical (`1.98`) |
| `ct_15` | `const fn accept_manually_drop<T>(x: ManuallyDrop<T>)` on `NonConstDrop` | `rc=0`, `MD_CTFE=13 MD_RT=13` (+ `unused_features` warning on `const_destruct`!) | *Not executed on 1.102* | Identical (`1.98`) |
| `ct_16` | `pub const PTR_EQ: bool = (&A as *const u8) == (&B as *const u8);` | `rc=1`, unnumbered `error: pointers cannot be reliably compared during const eval` | *Not executed on 1.102* | Identical (`1.98`) |
| `ct_17` | IEEE-754 `0.0f32 == -0.0f32`, `to_bits()`, and `f32::NAN == f32::NAN` in CTFE & runtime | `rc=0`, `EQ_ZEROS=true BITS_EQ_ZEROS=false POS_BITS=0x00000000 NEG_BITS=0x80000000 NAN_EQ_SELF=false` | *Not executed on 1.102* | Identical (`1.98`) |
| `ct_18` | Legacy `T: ~const TildeOp` bound syntax | `rc=0`, `TILDE_CONST=42` | *Not executed on 1.102* (source confirms `~const` still parsed in `ty.rs:1382-1387`) | Identical (`1.98`) |

Two subtle empirical findings from `ct_10`–`ct_18` warrant retention:
- **`ct_15` `unused_features` warning**: Wrapping a non-`const` `Drop` type in `ManuallyDrop<T>` does not merely satisfy `[const] Destruct` in the trait solver—it short-circuits `check_drop_terminator` at `if !needs_drop { return; }` (`check.rs:405-407`), so `#![feature(const_destruct)]` is not even needed!
- **`ct_14` side-effecting `const impl Drop` confluence**: A `const impl<'a> Drop` that mutates a local via `&mut u32` inside a nested block scope runs identically in CTFE (`CTFE_DROP=99`) and runtime (`RT_DROP=99`), illustrating why `NeedsNonConstDrop::is_structural_in_adt_value` (`qualifs.rs:209-221`) treats custom destructors as non-structural.

---

### 7. Anneal Trusted-Boundary Implications (`joshlf/anneal@c131b320e`)

Basis: source + derived

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/audit/TrustedBoundary.lean`) establishes four concrete boundary contracts for extending Anneal's MIR capture and trusted semantics to cover `const_trait_impl`, `const_destruct`, and `adt_const_params`:

1. **Compiler Version Pin (`driver.rs:25,45-47`)**: Anneal currently pins `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"` and hooks `after_analysis` (`driver.rs:75-84`). Because `1.98.0-nightly` still accepts legacy `impl const` (`item.rs:677-680`) and uses `HostEffectPredicate` / `predicates_of.rs`, upgrading Anneal's pinned nightly to `1.102.0-nightly` or later requires adapting any `rustc_middle` / `rustc_type_ir` queries that reference `HostEffectPredicate` -> `HostEffectClause` or `hir::Constness::Const` -> `Const { always }`, and updating test crates from `impl const` to `const impl`.
2. **Confluence Simplifies `const_trait_impl` Capture**: Because `after_analysis` executes strictly after HIR typeck, trait coherence (`E0119`), and `check_consts` have all passed, and single-impl coherence guarantees CTFE-vs.-runtime dispatch confluence (`coherentConstImpl_ctfe_eq_runtime`), monomorphized MIR bodies for `const impl` methods and `const fn` callers require **no separate CTFE vs. runtime dispatch table** in `Trusted.MirSemantics`. The same MIR `Body` captures both compile-time and runtime semantics, provided Anneal's `MirSemantics` faithfully matches `rustc`'s target-parameterized integer/layout behavior.
3. **Current Exclusions in `MirAst.lean` (`L280-321,753-785`)**:
   - `MirTy` explicitly maps `TyKind::Float` to `.unsupported` (`L308`) and models `TyKind::RawPtr` as `.rawPtr mutability pointee` (`L320`). Because `ConstParamTy_` rejects both `Float` and `RawPtr` (and `union`) from type-level const generic arguments, monomorphized const generic parameters of `adt_const_params` types (structs/enums/arrays over integers, `bool`, `char`, `()`) and `unsized_const_params` (`&'static str`, `&'static [T]`) materialize exclusively into layout-canonical `ValTree` values whose lowered `mir::ConstValue`s contain no floats or indeterminate pointer comparisons. Extending `MirAst.ConstLit` (`L504`) to capture aggregate/slice `ConstValue` constants from `adt_const_params` therefore preserves canonical equality without needing float or CTFE-pointer-equality semantics.
   - `TerminatorKind` currently maps `Drop` and `CoroutineDrop` to `.unsupported` (`L753-785`). Supporting `const_destruct` in Anneal's MIR capture requires adding `TerminatorKind::Drop` (with drop-glue shim resolution via `Instance::resolve_drop_in_place`) and honoring `ManuallyDrop`'s zero-drop-glue rule; because `check_consts` already enforces `constDestruct_drop_safety` before `after_analysis`, every drop terminator reachable from a checked `const` item resolves exclusively to `const impl Drop` shims and structural field drops.
4. **Lean Purity and `._unsafe_rec` Firewall (`MirAst.lean:79-81`, `MirSemantics.lean:177-178`, `TrustedBoundary.lean:93-101,1110-1135,1615-1778`)**:
   `TrustedBoundary.validateRepoConstant` rejects every `partial`, `unsafe`, `axiom`, and `quot` constant in repository modules, as well as forbidden compiler-reflection primitives (`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`). As documented in `MirAst.lean:79-81`, even structurally recursive computable Lean `def`s synthesize a hidden `*._unsafe_rec` codegen helper marked `partial`. Marking recursive specification functions `noncomputable def` (as done in `Trusted/MirAst.lean` and in our mechanization below) suppresses `._unsafe_rec` generation without introducing `Classical.choice`.

---

### 8. Kernel-Checked Lean `v4.34.1` Soundness and Sharpness Mechanization

Basis: source + execution + derived

The standalone mechanization `support/ConstTraitEffectsDestructAndValTreeSoundness.lean` (`1,660` lines, `66,449` bytes, namespace `Anneal.ConstTraitAndValTreeSoundness`) formalizes all four pillars without importing external libraries or violating Anneal's trusted boundary.

#### 8.1 Kernel Verification and Purity Audit Receipt

Compiled under `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) via:

```console
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
  -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/ConstTraitEffectsDestructAndValTreeSoundness.lean
```

- **Exit code**: `0` (zero errors, zero warnings under `-DwarningAsError=true`).
- **Environment audit (`env.constants.map₁`)**: `779` total compiled constants in namespace `Anneal.ConstTraitAndValTreeSoundness`, `79` explicit `theorem` declarations (`237` total `.thmInfo` constants including generated equational/sizeOf lemmas), `67` explicit `def`/`noncomputable def` declarations, `21` explicit `inductive`/`structure` declarations.
- **Zero-taint audit**:
  - `UNSAFE_REC_COUNT = 0` (`[]`)
  - `PARTIAL_COUNT = 0` (`[]`)
  - `UNSAFE_COUNT = 0` (`[]`)
  - `BAD_AXIOM_THEOREMS = 0` (`[]`)
  - Static source token counts (comments stripped): `sorry = 0`, `Classical.choice = 0`, `omega = 0`, `bv_decide = 0`, `native_decide = 0`, `partial def = 0`, `unsafe = 0`, `deriving = 0`.
  - **Union of all axioms across all 237 theorem constants**: `[propext]` (`148` zero-axiom theorems, `89` `[propext]`-only theorems; `0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).

#### 8.2 Summary of Mechanized Theorems and Sharpness Counterexamples

| Theorem / Witness | Section | Statement Summary | Axioms |
| :--- | :--- | :--- | :--- |
| `BoundConstness.le_refl`, `le_trans`, `le_antisymm`, `le_total`, `join_*`, `meet_*`, `absorb_*` | §2 | Full bounded-lattice algebra for `always <= maybe <= normal` | `{}` (zero) |
| `lowerToHostEffect_satisfies_iff_le` | §2 | Faithfulness of `lowerToHostEffect` against `rustc_type_ir::BoundConstness::satisfies` | `{}` (zero) |
| `instBound_mono_ctx`, `instBound_mono_bound` | §3 | Context and bound monotonicity of `instBound ctx b` across `constItem`, `constFn`, `runtimeFn` | `{}` (zero) |
| `const_subst_soundness`, `validSubst_mono_ctx` | §3 | Generic `const fn` trait-call substitution soundness and `constItem -> runtimeFn` weakening | `{}` (zero) |
| `oldSolver_iff_nextSolver` | §4 | Exact equivalence of old-solver (`effects.rs`) and next-solver (`effect_goals.rs`) host-effect resolution | `{}` (zero) |
| `coherentConstImpl_ctfe_eq_runtime`, `coherentConstImpl_expr_ctfe_eq_runtime` | §4 | Single-impl coherence (`Coherent reg`) implies CTFE-vs.-runtime confluence for single dispatches and arbitrary expression trees | `{}` (zero) |
| `constDestruct_drop_safety` | §5 | `ConstDestruct emptyDestructEnv .constItem ty -> ¬ DropHitsNonConst ty` | `{}` (zero) |
| `ctfe_drop_eq_runtime_drop` | §5 | `ConstDestruct` implies CTFE drop glue succeeds (`∃ n, runDropCtfe ty = some n`) and equals `runDropRuntime ty` | `[propext]` |
| `constDestruct_subst_soundness`, `constDestruct_runtime_universal` | §5 | Polymorphic `[const] Destruct` substitution preserves CTFE drop-safety while admitting all concrete drop types at runtime | `{}` (zero) |
| `manuallyDrop_shields_nonConstDrop` | §5 | `ManuallyDrop<NonConstDrop>` is unconditionally `[const] Destruct` with CTFE drop trace `some 0` | `[propext]` |
| `ValTree.beq_eq_true_iff`, `structEq_refl/symm/trans` | §6 | Structural `ValTree` equality reflects propositional equality (`v₁ = v₂`) and is an equivalence relation | `[propext]` |
| `valTree_eq_iff_type_eq`, `valTree_leibniz_substitutivity` | §6 | `StructEq v₁ v₂ <-> TyApp base v₁ = TyApp base v₂`, implying Leibniz substitutivity `P (TyApp base v₁) <-> P (TyApp base v₂)` | `[propext]` |
| `unsized_str_valtree_length_reconstruction` | §6 | Structurally equal slice/`&'static str` branch `ValTree`s necessarily reconstruct equal slice length metadata | `[propext]` |
| `leibniz_substitutivity_requires_equiv_and_canonical` | §6 | Type-level agreement `R x y <-> TyApp base (enc x) = TyApp base (enc y)` necessitates that `R` is reflexive, symmetric, transitive, and canonical (`R x y <-> enc x = enc y`) | `{}` (zero) |
| `ce1_dual_const_runtime_impl_breaks_ctfe_confluence` | §7 | Constructive counterexample: dual `const impl` (`1`) + `impl` (`2`) breaks `Coherent` and produces CTFE `1 ≠ 2` runtime | `[propext]` |
| `ce2_missing_const_destruct_executes_nonconst_drop_in_ctfe` | §7 | Constructive counterexample: dropping unconstrained `T` in `const fn` fails `ConstDestruct`, hits `DropHitsNonConst` when `T := NonConstDrop`, and gets stuck (`runDropCtfe = none` vs. `runDropRuntime = some 99`) | `[propext]` |
| `ce3_float_neg_zero_breaks_type_substitutivity` | §7 | Constructive counterexample: IEEE-754 `ieeeF32Eq (+0.0) (-0.0) = true` while `isPosZeroTy` separates their `ValTree` types, and `ieeeF32Eq qNaN qNaN = false` refutes any agreement with type equality | `[propext]` |
| `ce4_ctfe_ptr_comparison_nondeterministic` | §7 | Constructive counterexample: `ctfeConstPtrCmp ptrConstA ptrConstB = .unknown`, while `layoutMerged` yields `true` and `layoutDistinct` yields `false`, refuting any layout-independent pointer equality oracle | `{}` (zero) |
| `witness_ct01_ct02_*`, `witness_ct04_ct13_ct14_*`, `witness_ct06_ct09_*` | §8 | Concrete executable witnesses instantiating `ct_01`/`ct_02`, `ct_04`/`ct_13`/`ct_14`, and `ct_06`/`ct_09` directly in the mechanized model | `{}` / `[propext]` |

## Boundaries

To prevent over-generalization, the following negative-space boundaries apply strictly to this report:

- **Not examined**:
  - **Higher-ranked / associated-type conditional const bounds (`for<'a> T: [const] Trait<'a>` and `trait Foo { type Assoc: [const] Bar; }`)**: While `consider_additional_alias_assumptions` (`effect_goals.rs:97-150`) and `evaluate_host_effect_from_conditionally_const_item_bounds` (`effects.rs:172-264`) were audited in source, no live `rustc` probes or Lean theorems were constructed for conditionally const associated-type projections or `RPITIT`/`TAIT` const item bounds.
  - **`const` closures (`const || ...`), `Fn`/`FnMut`/`FnOnce` host-effect built-ins, and `async const` interactions**: Source paths (`effect_goals.rs:319-373`, `effects.rs:551-595`) were inspected, but no live execution suite was run against `const_closures` or `async_trait_bounds`.
  - **Live binary execution at `HEAD` (`01afe5348`) and Anneal's pinned `f8a08b688`**: Execution evidence was acquired on `1.98.0-nightly` (`14210df0e`) and `1.102.0-nightly` (`3ef0c22cd`); behavior on `HEAD` is **derived** from source diffs rather than binary execution, and `f8a08b688` (one day prior to `14210df0e`) was audited only via Anneal's capture driver pin.
  - **`generic_const_exprs` / `min_generic_const_args` (`gca!`) interaction with `adt_const_params`**: `compiler/rustc_ty_utils/src/consts.rs` was audited for `thir_abstract_const`, and `library/core/src/marker.rs:1083-1097` notes `gca!`, but symbolic const-expression unification over ADT fields was not probed empirically.
  - **Miri (`-Zmiri-tree-borrows`) execution of `const_trait_impl` / `const_destruct` binaries**: Probe cases `ct_01`–`ct_18` were compiled and executed natively on `x86_64-unknown-linux-gnu`; Miri operational validation of side-effecting `const impl Drop` (`ct_14`) was not executed.
- **Unknown**:
  - **Exact stabilization timeline and final surface syntax of `const_trait_impl`, `const_destruct`, `min_adt_const_params`, and `unsized_const_params`**: All four features remain nightly-gated with active `FIXME(const_trait_impl)`, `FIXME(comptime)`, and `FIXME(unsized_const_params)` markers in `HEAD` (`01afe5348`). In particular, `library/core/src/marker.rs:1109-1112` notes `ConstParamTy_` is intended to be renamed on stabilization, and `misc.rs:108` carries `FIXME(unsized_const_params): Make const N: [u8] work then forbid references`—so `&'static str` const-parameter syntax (`ct_09`) may change before stabilization.
  - **Whether subtle `-Z next-solver=globally` vs. `-Z next-solver=no` divergences exist on cyclic `[const]` supertraits, coinductive `HostEffect` bounds, or `[const]` alias-bound normalization**: Zero divergences were observed across our 18-case matrix, but that probe set does not exhaustively test cyclic trait-alias or projection-heavy `HostEffect` goals.
- **Known not to apply**:
  - **Legacy `impl const Trait for T` syntax on `1.102.0-nightly` and `HEAD`**: Known not to apply after `parse_item_impl` dropped the post-`impl` `self.parse_constness` fallback between `1.98.0-nightly` (`14210df0e:677-680`) and `1.102.0-nightly` (`3ef0c22cd:694-721`).
  - **Pattern-matching structural equality (`const_to_pat`) vs. `ConstParamTy_`**: `ValTree` *does* accept non-`NaN` floats and integer-cast thin raw pointers for `match` constant patterns (`r[patterns.const.float]`, `r[patterns.const.pointer]`, `valtrees.rs:113-149`); the `ConstParamTy_` rejection of `f32`/`f64` and `*const T` applies specifically to type-level const generic parameters, not to all `ValTree` consumers.
  - **`#![feature(const_param_ty_unchecked)]` and `#[rustc_do_not_const_check]`**: Both internal/escape-hatch gates explicitly bypass `visit_implementation_of_const_param_ty` (`builtin.rs:183-185`), `check_param_wf` (`wfcheck.rs:805-809`), `enforce_context_effects` (`callee.rs:1168-1170`), and `check_live_drops` (`post_drop_elaboration.rs:38-40`); soundness guarantees in this report do not apply to crates using those bypasses.
  - **`core::intrinsics::const_eval_select`**: CTFE-vs.-runtime observational confluence (`coherentConstImpl_ctfe_eq_runtime`) holds for `const_trait_impl` dispatch alone and does not prevent deliberate CTFE/runtime divergence introduced via `const_eval_select`.
- **Unsupported**:
  - **Experimental `comptime` (`hir::Constness::Const { always: true }`)**: Explicitly unfinished across `effects.rs:471,576,610-613` (`unimplemented!("FIXME(comptime)")` / early bail-out) and `callee.rs:1144-1157`.
  - **Const `FnPtr`, `AsyncFn*`, `Coroutine`, `UnsafeBinder`, and `dyn Trait` in `[const] Destruct` / `HostEffect` built-ins**: Explicitly rejected or `unimplemented!` in `effect_goals.rs:304-495`, `effects.rs:515-535`, and `structural_traits.rs:850-871`.
  - **`ty::View(..)` in `effects.rs` and `valtrees.rs` (`HEAD` `01afe5348`)**: Explicitly `unimplemented!()`.
  - **Unions, raw pointers, floats, function pointers, and `&mut T` as `ConstParamTy_` types**: Explicitly rejected by `type_allowed_to_implement_const_param_ty` (`misc.rs:92-151`) and `const_to_valtree_inner` (`valtrees.rs:130-196`).
- **Stronger conclusions NOT established**:
  - Zero divergences across 18 probes does **not** prove global old-solver vs. next-solver completeness parity across arbitrary higher-ranked or projection-heavy `const_trait_impl` programs.
  - The standalone Lean `v4.34.1` mechanization proves soundness and sharpness of the *extracted formal model* (semilattice, single-impl coherence, structural `DropTy`, canonical `ValTree`); it does **not** import or verify `rustc`'s Rust source code or `joshlf/anneal`'s `Trusted.MirSemantics` directly.

## Evidence

### Primary Git Source Citations

All 40-hex commit SHAs below were resolved and verified live via GitHub API on `2026-11-22`:

1. **`rust-lang/rust` (`01afe534803b93889b85f6028117251cfbd431da`, `2026-11-22`, `HEAD`)**:
   - `compiler/rustc_parse/src/parser/item.rs:689-765` — `Parser::parse_item_impl` (prefix-only `const impl`, post-`impl` fallback removed).
   - `compiler/rustc_parse/src/parser/ty.rs:1304-1430` — `Parser::parse_trait_bound_modifiers` and `Parser::parse_bound_constness` (`~const`, `[const]`, `const`, `Never`, polarity mutual exclusivity).
   - `compiler/rustc_hir/src/hir.rs:4522-4545` — `hir::Constness::{Const { always: bool }, NotConst}`.
   - `compiler/rustc_type_ir/src/predicate.rs:668-675,738-758` — `HostEffectClause<I>`, `BoundConstness::{Const, Maybe}`, `BoundConstness::satisfies`.
   - `compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs:966-1186` — `HirTyLowerer::lower_poly_trait_ref` (`ConstBoundForNonConstTrait`, `Always` -> `clauses_of` `HostEffectClause`, `Maybe` -> `PredicateFilter::ConstIfConst`).
   - `compiler/rustc_hir_analysis/src/collect/clauses_of.rs:775-868,1045-1204` — `const_conditions` and `explicit_implied_const_bounds`.
   - `compiler/rustc_hir_typeck/src/callee.rs:1135-1206` — `FnCtxt::enforce_context_effects` (`ConstContext` -> `BoundConstness::{Const, Maybe}` or runtime early-return; `ComptimeFnCalledOutsideConstContext`).
   - `compiler/rustc_next_trait_solver/src/solve/effect_goals.rs:21-520` — `GoalKind for ty::HostEffectClause<I>`, `consider_impl_candidate` (`impl_is_const`), `consider_builtin_destruct_candidate`, `compute_host_effect_goal`.
   - `compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs:787-872` — `const_conditions_for_destruct`.
   - `compiler/rustc_trait_selection/src/traits/effects.rs:18-690` — `evaluate_host_effect_obligation`, `evaluate_host_effect_for_destruct_goal`, `evaluate_host_effect_from_selection_candidate`.
   - `compiler/rustc_hir_analysis/src/coherence/mod.rs:54-189` — `coherent_trait`, `enforce_trait_manually_implementable` (`#[rustc_deny_explicit_impl]` -> `E0322`).
   - `compiler/rustc_trait_selection/src/traits/coherence.rs:39-230` — `ImplHeader`, `overlapping_trait_impls`, `fresh_impl_header`, `overlap` (`TypingMode::Coherence`, `.with_next_trait_solver(true)`, constness omitted from `ImplHeader`).
   - `compiler/rustc_trait_selection/src/traits/specialize/specialization_graph.rs:76-160` — `Node::insert` (`E0119` overlap detection).
   - `compiler/rustc_hir_analysis/src/check/compare_impl_item.rs:227-315,2518-2578` — `[const]` bound entailment check between `const impl` and `const trait`.
   - `compiler/rustc_const_eval/src/check_consts/check.rs:44-137,348-426` — `Qualifs`, `check_const_conditions`, `check_drop_terminator`.
   - `compiler/rustc_const_eval/src/check_consts/qualifs.rs:170-222` — `NeedsNonConstDrop::in_any_value_of_ty` and `is_structural_in_adt_value`.
   - `compiler/rustc_const_eval/src/check_consts/ops.rs:578-641,693-712` — `LiveDrop` (`E0493`, `[const] Destruct` suggestion, `const_destruct` gate), `RawPtrComparison`, `RawPtrToIntCast`.
   - `compiler/rustc_const_eval/src/check_consts/post_drop_elaboration.rs:14-98` — `check_live_drops` (`const_precise_live_drops`, cleanup-block skip).
   - `compiler/rustc_mir_transform/src/check_const_item_mutation.rs:11-174` — `CheckConstItemMutation` and `is_const_item_without_destructor`.
   - `compiler/rustc_hir_analysis/src/check/wfcheck.rs:794-914` — `check_param_wf` (`ConstParamTy_` bound under `adt_const_params`/`min_adt_const_params`).
   - `compiler/rustc_hir_analysis/src/coherence/builtin.rs:32-54,170-245` — `visit_implementation_of_const_param_ty` (`E0204`).
   - `compiler/rustc_trait_selection/src/traits/misc.rs:23-35,86-284` — `type_allowed_to_implement_const_param_ty`, `all_fields_implement_trait`.
   - `compiler/rustc_builtin_macros/src/deriving/const_param_ty.rs:1-26` — `expand_derive_const_param_ty`.
   - `library/core/src/marker.rs:1055-1146` — `Destruct`, `ConstParamTy_`, `pub macro ConstParamTy`, `marker_impls!` for `min_adt_const_params` and `unsized_const_params`.
   - `library/core/src/ops/drop.rs:206-233` — `pub const trait Drop`.
   - `compiler/rustc_middle/src/ty/consts/valtree.rs:24-255` — `ValTree`, `Value`, `destructure_adt_const`.
   - `compiler/rustc_const_eval/src/const_eval/valtrees.rs:20-491` — `branches`, `slice_branches`, `const_to_valtree_inner`, `reconstruct_place_meta`, `eval_to_valtree`, `valtree_to_const_value`, `valtree_into_mplace`.
   - `compiler/rustc_const_eval/src/const_eval/machine.rs:273-365,573-580` — `guaranteed_cmp` and `CompileTimeMachine::binary_ptr_op`.
   - `compiler/rustc_const_eval/src/interpret/operator.rs:69-94,325-410` — `binary_float_op` (NaN adjustment) and pointer operator fallback.
   - `compiler/rustc_ty_utils/src/consts.rs:16-402` — `thir_abstract_const` and `recurse_build`.

2. **`rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`, `1.102.0-nightly`)**:
   - Audited at `compiler/rustc_parse/src/parser/item.rs:688-725`, `compiler/rustc_hir/src/hir.rs:4522-4545`, `compiler/rustc_type_ir/src/predicate.rs:667-758`, `compiler/rustc_hir_analysis/src/collect/clauses_of.rs`, `compiler/rustc_hir_typeck/src/callee.rs:1135-1189`, `compiler/rustc_next_trait_solver/src/solve/effect_goals.rs`, `compiler/rustc_trait_selection/src/traits/effects.rs`, `compiler/rustc_const_eval/src/const_eval/valtrees.rs`, and `compiler/rustc_const_eval/src/check_consts/check.rs`. Diffed directly against `01afe5348`.

3. **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`, `1.98.0-nightly`)**:
   - Audited at `compiler/rustc_parse/src/parser/item.rs:656-685` (legacy `impl const` fallback), `compiler/rustc_hir/src/hir.rs:4631-4646` (unit `Constness::Const`), `compiler/rustc_type_ir/src/predicate.rs:1009-1098` (`HostEffectPredicate`), `compiler/rustc_hir_analysis/src/collect/predicates_of.rs`, `compiler/rustc_hir_typeck/src/callee.rs:1019-1073`, `compiler/rustc_trait_selection/src/traits/misc.rs:92-290`, and `library/core/src/marker.rs:1052-1122`.

4. **`rust-lang/rust` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-30`, Anneal pinned `1.98.0-nightly`)**:
   - Verified commit SHA (`2026-05-30T17:09:19Z`) matching `joshlf/anneal`'s `trusted/rustc-capture/src/driver.rs:25`.

5. **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `2026-11-17`)**:
   - `src/const_eval.md:235-290` (`r[const-eval.const-context.def]`, `r[const-eval.const-fn.const-context]`, `r[const-eval.const-fn.outside-context]`, `r[const-eval.const-fn.body-restriction]`).
   - `src/items/generics.md:125-225` (`r[items.generics.const.argument]`, `r[items.generics.const.exhaustiveness]`).
   - `src/patterns.md:977-1015` (`r[patterns.const.structural-equality]`, `r[patterns.const.pointer]`, `r[patterns.const.float]`).
   - `src/destructors.md:7-54` (`r[destructors.operation]`, `r[destructors.drop_in_place]`).
   - `src/types/numeric.md:29`, `src/types/pointer.md:55` (`r[type.numeric.float]`, `r[type.pointer.raw.cmp]`).

6. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `2026-11-19`)**:
   - `trusted/rustc-capture/src/driver.rs:25,45-84` — `COMPILER_VERSION` pin and `after_analysis` callback.
   - `trusted/lean/Trusted/MirAst.lean:79-81,280-321,504,753-785` — `._unsafe_rec` note, `MirTy` (`Float` -> `.unsupported`, `RawPtr`), `ConstLit`, `TerminatorKind` (`Drop` -> `.unsupported`).
   - `trusted/lean/Trusted/MirSemantics.lean:177-178` — `._unsafe_rec` purity note.
   - `trusted/audit/TrustedBoundary.lean:93-101,1110-1135,1615-1778` — `partial`/`unsafe`/`axiom`/`quot` and `Lean.ofReduceBool` rejection rules.

7. **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, `2026-09-24`)**:
   - Release binary `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.

### Preserved Package Support Material

All execution probes, empirical captures, and kernel-checked Lean proofs are preserved in this package under `support/`:

| File | Size (Bytes) | Lines | SHA-256 | Role |
| :--- | ---: | ---: | :--- | :--- |
| `support/probe_const_trait_impl_effects_and_adt_const_params.py` | `13,243` | `522` | `3339a69682ae8ed452e4d0994fd7117546b012b3806c999440f6ec4c593ea351` | Standalone 18-case differential `rustc` probe (`-Z next-solver=globally` vs. `-Z next-solver=no`, `--edition=2024`) |
| `support/probe_results_1_98_nightly.json` | `22,454` | `437` | `9d2b3bd9cc6044a3823b0da2b20902ff60a9bf112128aebaa66e366759198376` | Live 18-case execution results on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`0` solver divergences) |
| `support/baseline_1_102_nightly.json` | `11,680` | `224` | `8cf01eaa4e7de18440d4a035f9591932cbefd258d8f26abc5c391296956993e0` | 9-case dual-solver baseline captured on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` (`0` solver divergences) |
| `support/ConstTraitEffectsDestructAndValTreeSoundness.lean` | `66,449` | `1,660` | `4a4164f1a5806fd3ec2e5b11bcf2094b8a6919a8ef103701c658e84fc7069f7b` | Standalone Lean `v4.34.1` formalization (`779` constants, `79` explicit theorems, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`) |

## Revalidation

Use the following narrow, discriminating checks to revalidate these findings against a newer `rustc` nightly, a newer `joshlf/anneal` commit, or a newer Lean toolchain without repeating the full source crawl:

1. **Rerun the 18-Case Differential `rustc` Probe (Fastest Empirical Check)**:
   ```console
   RUSTC=/path/to/rustc python3 support/probe_const_trait_impl_effects_and_adt_const_params.py --out /tmp/ctrait_reval.json
   ```
   - Inspect `solver_divergences`: any non-empty list immediately signals a newly introduced `-Z next-solver=globally` vs. `-Z next-solver=no` divergence on `HostEffectClause`, `Destruct`, or `ConstParamTy_`.
   - Inspect `ct_10` and `ct_18`: `ct_10` (`impl const`) is expected to **fail** parse on `>= 1.102.0-nightly` and **pass** on `1.98.0-nightly`; if `ct_18` (`~const`) starts failing, the parser removed `~const` recovery (`compiler/rustc_parse/src/parser/ty.rs:1382-1387`).
   - Inspect `ct_05` (`E0119`), `ct_03` (`E0493`), `ct_07` (`E0204` + `E0277`), `ct_08` (`E0204` only), `ct_09` (`&'static str`), and `ct_16` (CTFE raw-pointer comparison): any `rc` flip indicates a major soundness or feature-gate change.

2. **Targeted Upstream Source Diffs (Zero Build Required)**:
   Diff these exact six files between `01afe534803b93889b85f6028117251cfbd431da` and a target `rust-lang/rust` commit:
   - `compiler/rustc_type_ir/src/predicate.rs` (check `BoundConstness` variants and `satisfies`)
   - `compiler/rustc_next_trait_solver/src/solve/effect_goals.rs` & `compiler/rustc_trait_selection/src/traits/effects.rs` (check `impl_is_const` and built-in const trait arms)
   - `compiler/rustc_trait_selection/src/traits/coherence.rs` (check whether `ImplHeader` remains constness-agnostic)
   - `compiler/rustc_const_eval/src/check_consts/qualifs.rs` & `compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs` (check `NeedsNonConstDrop` and `const_conditions_for_destruct`)
   - `compiler/rustc_trait_selection/src/traits/misc.rs` & `compiler/rustc_const_eval/src/const_eval/valtrees.rs` (check `type_allowed_to_implement_const_param_ty` and `const_to_valtree_inner`, especially `unsized_const_params` reference rules and float/raw-pointer exclusions)

3. **Re-Check Lean `v4.34.1` Mechanization and Zero-`._unsafe_rec` / Axiom Purity**:
   ```console
   lean -R support -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     -o /tmp/ConstTraitEffectsDestructAndValTreeSoundness.olean \
     support/ConstTraitEffectsDestructAndValTreeSoundness.lean
   ```
   Then import `ConstTraitEffectsDestructAndValTreeSoundness` in a scratch `.lean` file and run `MetaM` over `env.constants.map₁` to assert `UNSAFE_REC_COUNT = 0`, `PARTIAL_COUNT = 0`, `UNSAFE_COUNT = 0`, and `UNION_OF_ALL_AXIOMS ⊆ [propext, Quot.sound]`.

4. **Check Anneal Capture Readiness**:
   Inspect `trusted/rustc-capture/src/driver.rs` (`COMPILER_VERSION`) and `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `ConstLit`, `TerminatorKind`) in `joshlf/anneal`: if `COMPILER_VERSION` advances past `1.98.0-nightly` or `TerminatorKind::Drop` / aggregate `ConstLit` variants are added, re-verify the Section 7 boundary assumptions against the new capture implementation.
