# `rustc` `Try` Trait v2 (`?`), Homogeneous vs. Heterogeneous `try` Blocks, `do yeet`, `#[track_caller]` Location-Loss Bugs, `Infallible = !`, and Edition 2021 vs. 2024 Tail Drop Scopes

## Summary

`rustc`'s `Try` trait v2 lowering (`?`, `try {}`, `try bikeshed Ty {}`, and `do yeet`) splits across three distinct AST-to-HIR desugaring scopes, exhibits two live `libcore` `#[track_caller]` location-loss bugs that persist identically across `-O0`, `-O2`, and Miri (`-Zmiri-tree-borrows`), crosses a concrete version boundary where `core::convert::Infallible` transitions from `pub enum Infallible {}` (`rustc 1.98.0-nightly`) to `pub type Infallible = !` (`rustc 1.102.0-nightly` / `main`) while still rejecting `Result<T, Infallible>?` into `Result<T, U>` with `E0277`, flips normal-exit `try {}` tail temporary drop order between Edition `2021` and Edition `2024` while leaving sub-expression `scrut? + rhs` order invariant, and eliminates uninhabited-residual `SwitchInt` branches only between `Runtime(PostCleanup)` MIR and `Runtime(Optimized)` MIR.

1. **Three-Scope AST-to-HIR Lowering Asymmetry (`TryBlockScope::{Function, Homogeneous, Heterogeneous}`):** In `compiler/rustc_ast_lowering/src/expr.rs:729-780, 1952-2072`, `Function` and annotated `Heterogeneous` (`try bikeshed Ty { ... }`) scopes lower `?` to `LangItem::TryTraitFromResidual` (`FromResidual::from_residual`), enabling `From`-based error conversion (`SubErr -> SuperErr`) at the cost of requiring a contextual or annotated return type. Unannotated `Homogeneous` (`try { ... }`) lowers `?` to `LangItem::ResidualIntoTryType` (`residual_into_try_type`), constraining the block's result to `<R as Residual<O>>::TryType` so unannotated `try { Some(41u32)? + 1 }` infers `Option<u32>` while `let _x: Result<u32, SuperErr> = try { Err::<u32, SubErr>(SubErr)? }` fails with `E0308`. However, `lower_expr_yeet` (`do yeet e`) bypasses `ResidualIntoTryType` in all three scopes and unconditionally emits `LangItem::TryTraitFromYeet` (`from_yeet`), causing `do yeet` inside homogeneous `try {}` to accept `SubErr -> SuperErr` conversion while rejecting unannotated blocks with `E0283` and failing `const fn` evaluation with `E0015` because `from_yeet` is non-`const`.
2. **Two Live `libcore` `#[track_caller]` Location-Loss Bugs Across `-O0`, `-O2`, and Miri:**
   - **Bug 1 (`library/core/src/ops/try_trait.rs:381`):** `residual_into_try_type` carries `#[inline]` (with an open `FIXME` referencing `#148915` on `#[rustc_force_inline]`) but omits `#[track_caller]`. Any custom `Try` type whose `FromResidual::from_residual` carries `#[track_caller]` and reads `Location::caller()` reports `<RUST_SYSROOT_SRC>/library/core/src/ops/try_trait.rs:384` under homogeneous `try { mk_my_err()? }`, whereas `try bikeshed` and bare functions report the exact user `?` line.
   - **Bug 2 (`library/core/src/result.rs:2200-2208` at `main`/`1.102.0-nightly`, `2198-2206` at `1.98.0-nightly`):** Although `from_yeet` (`try_trait.rs:342`) explicitly carries `#[track_caller] // because Result::from_residual has it`, `<Result<T, F> as FromResidual<ops::Yeet<E>>>::from_residual` omits `#[track_caller]`. Every `do yeet e` targeting `Result<T, TrackedErr>` (in functions, homogeneous `try {}`, and heterogeneous `try bikeshed {}`) reports `library/core/src/result.rs:2206` (`:2204` on `1.98.0-nightly`) rather than the user's `do yeet` line, whereas custom `FromResidual<Yeet<E>>` impls with `#[track_caller]` receive the exact user line. Because `Body::caller_location_span` (`compiler/rustc_middle/src/mir/mod.rs:685-713`) is shared by both LLVM codegen (`rustc_codegen_ssa`) and Miri (`rustc_const_eval`) and walks MIR `SourceScope.inlined` frames stopping at the innermost non-`#[track_caller]` wrapper, MIR/LLVM inlining at `-O2` does not mask either bug.
3. **`Infallible = !` Version Boundary & `[const] Try` Feature Gate Coupling:** Between `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and `rustc 1.102.0-nightly` (`6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`) / `main` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), `library/core/src/convert/mod.rs` replaces `pub enum Infallible {}` (and its `#[rustc_reservation_impl]` for `From<!>`) with `pub type Infallible = !;` (stabilizing `!` at `since = "1.100.0"`). Because no blanket `impl<T> From<!> for T` exists, `r?` on `Result<u64, Infallible>` inside a closure returning `Result<u64, u32>` rejects with `E0277` in both versions (shifting only the diagnostic from `From<Infallible>` to `From<!>`). Using `?` or `try {}` inside `const fn` requires `#![feature(const_trait_impl)]` (`#143874`) in addition to `const_try` and `const_try_residual`, rejecting with `E0658` without it.
4. **Edition `2021` vs. `2024` Tail Drop-Scope Flip & `PostCleanup` -> `Optimized` MIR/LLVM Lowering:** Because `lower_expr_try_block` wraps the block's tail expression in `Try::from_output(<tail>)` as `hir::Block.expr`, `rustc_hir_analysis::check::region::resolve_block` (`region.rs:145-162`) flips `terminating = blk.span.edition().at_least_rust_2024()` for both homogeneous `try {}` and heterogeneous `try bikeshed Ty {}`. Consequently, `try { let c = RefCell::new(41u32); *c.borrow() + 1 }` fails `E0597` in Edition `2021` (drop trace `["qmark_tmp", "blk_local", "tail_tmp"]`) and compiles and runs in Edition `2024` (`["qmark_tmp", "tail_tmp", "blk_local"]`), whereas sub-expression `scrut? + rhs` retains statement-LIFO `["rhs_tmp", "scrut_tmp", "stmt_done", "fn_local"]` in both editions because `hir::ExprKind::Match` is not a terminating scope. At the MIR boundary, `qmark_infallible` retains `8` basic blocks (`1` `SwitchInt`, `1` `unreachable`, `1` live `branch` call, `1` live `from_residual` call) in `Runtime(PostCleanup)` MIR (`-O0`) and collapses to `1` basic block (`0` `SwitchInt`, `0` `unreachable`, `0` live calls) in `Runtime(Optimized)` MIR (`-O2`), lowering to `sret([16 x i8]) ... initializes((0, 4), (8, 16))` (for `-> Result<u64, CustomErr>`) or a 2-instruction scalar `add + ret` (for `-> Result<u64, Infallible>`), while `Option<NonZeroU64>?` and `try { x? + y? }` lower to branchless `select` / tag-`and` in LLVM 22.1.6 and LLVM 23.1.6.
5. **Mechanized Soundness & Anneal TCB Boundary:** `support/TryTraitResidualCallerAndDropSoundness.lean` kernel-checks all three semantic laws and three constructive sharpness counterexamples in Lean `v4.34.1` (`0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, `[propext]` at most). Against `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Trusted.MirAst` and `Trusted.MirSemantics` already admit `MirTy.never`, `TerminatorKind.switchInt`, and `TerminatorKind.unreachable`, but fail closed (`.unsupported`) on `TerminatorKind.call`, `TerminatorKind::Drop`, `StatementKind::SetDiscriminant`, and `StatementKind::BackwardIncompatibleDropHint`, and do not yet carry `SourceScope.inlined` caller-location metadata—defining the exact TCB extensions required to verify `Try` v2 programs at the `Runtime(PostCleanup)` MIR boundary.

## Applicability

This report combines primary-source audits, multi-version live compiler/Miri executions, and kernel-checked Lean 4 formalizations across seven durable upstream subjects observed on `2026-11-22`:

| Subject | Repository & Immutable Revision | Role in This Report |
| :--- | :--- | :--- |
| **`rustc` (`main` snapshot)** | `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | Primary-source audit of `libcore` (`try_trait.rs`, `result.rs`, `option.rs`, `control_flow.rs`, `convert/mod.rs`), parser, AST lowering, HIR region/scope resolution, MIR inlining, `Body::caller_location_span`, codegen, and `rustc_const_eval`. Byte-identical to `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2` across all seven audited core/compiler files. |
| **`rustc 1.102.0-nightly` + LLVM 23.1.6 + Miri 0.1.0** | `rust-lang/rust` @ `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2` | Execution baseline (`nightly-2026-11-20`, `x86_64-unknown-linux-gnu`) preserved in `support/rustc_1_102_0_nightly_llvm23_baseline.json` and cross-checked against its exact upstream source tree. Features `pub type Infallible = !` and LLVM `23.1.6`. |
| **`rustc 1.98.0-nightly` + LLVM 22.1.6 + Miri 0.1.0** | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Live execution (`nightly-2026-06-01`, `x86_64-unknown-linux-gnu`) of `support/probe_try_trait_v2_yeet_and_track_caller.py` preserved in `support/probe_rustc_1_98_0_nightly_output.json`, plus full source diff against `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`. Features pre-alias `pub enum Infallible {}` and LLVM `22.1.6`. |
| **Anneal Trusted MIR Boundary** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Source audit of `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` to determine which `Try` v2 MIR constructs are admitted vs. rejected fail-closed. |
| **Lean 4 Theorem Prover** | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Independent kernel verification (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) of `support/TryTraitResidualCallerAndDropSoundness.lean`. |
| **Rust RFC 3058 (`try_trait_v2`)** | `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | Normative design rationale for `Try`, `FromResidual`, residual coloring (`Result<!, E>`), and forward compatibility with `try {}` and `do yeet`. |
| **The Rust Reference** | `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative specification of Edition `2024` tail-expression temporary scopes (`src/destructors.md`, `r[destructors.scope.temporary.edition2024]`), `?` operator, and `#[track_caller]`. |

### Cross-Version Shared vs. Diverging Behaviors (`rustc 1.98.0-nightly` vs. `1.102.0-nightly` / `main`)

Because two nightly toolchains spanning six months of upstream `rust-lang/rust` evolution were both source-audited and executed on `x86_64-unknown-linux-gnu`, behaviors divide cleanly into **shared invariants** and **exact version-specific deltas**:

- **Shared across `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`, and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:**
  - All three `TryBlockScope` variants (`Function`, `Homogeneous`, `Heterogeneous`), `try bikeshed Ty {}` parsing, `lower_expr_try`, `lower_expr_try_block`, and `lower_expr_yeet` bypassing `ResidualIntoTryType`.
  - Both live `#[track_caller]` bugs (`residual_into_try_type` at `try_trait.rs:381` reporting line `384`, and `<Result<T, F> as FromResidual<Yeet<E>>>::from_residual` omitting `#[track_caller]`) across `-O0`, `-O2`, and Miri `-Zmiri-tree-borrows`.
  - Rejection of `Result<u64, Infallible>?` into `Result<u64, u32>` with `E0277` (no blanket `impl<T> From<!> for T`).
  - Requirement of `#![feature(const_trait_impl)]` alongside `const_try` + `const_try_residual` for `const fn` `?` / `try {}`, and rejection of `do yeet` in `const fn` with `E0015` (non-`const` `from_yeet`).
  - Edition `2021` vs. Edition `2024` tail temporary drop-scope flip for `try {}` and `try bikeshed Ty {}`, and edition invariance of sub-expression `scrut? + rhs`.
  - Exact `PostCleanup` -> `Optimized` MIR basic-block / `SwitchInt` / `unreachable` counts (`8 -> 1`, `9 -> 5`, `14 -> 8`) and branchless LLVM IR lowering (`sret` `initializes((0, 4), (8, 16))`, `select`, tag-`and`).
- **Diverging between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, LLVM 22.1.6) and `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2` / `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`1.102.0-nightly` / `main`, LLVM 23.1.6):**
  - **Type identity of `Infallible`:** `pub enum Infallible {}` (distinct from `!`; `Same<!>` fails `E0277`, `#[rustc_reservation_impl] const impl<T> From<!> for T` present at `convert/mod.rs:798-806`, `Result::Residual = Result<convert::Infallible, E>`) in `1.98.0-nightly`, versus `pub type Infallible = !;` (stabilized `!` at `since = "1.100.0"`, reservation impl removed, `Result::Residual = Result<!, E>`, `Option::Residual = Option<!>`, `ControlFlow::Residual = ControlFlow<B, !>`) in `1.102.0-nightly` and `main`.
  - **Line numbers for Bug 2 (`result.rs`):** `<Result<T, F> as FromResidual<Yeet<E>>>::from_residual` executes `Err(From::from(e))` at `library/core/src/result.rs:2204` in `1.98.0-nightly` and `library/core/src/result.rs:2206` in `1.102.0-nightly` / `main` (a +2 line shift from intervening `unwrap_failed` signature edits).
  - **Parser line numbers & LLVM IR minor attributes:** `parse_try_block` sits at `compiler/rustc_parse/src/parser/expr.rs:3622-3636` in `1.98.0-nightly` versus `3361-3377` in `1.102.0-nightly` / `main`; LLVM `23.1.6` adds the `nofree` attribute on the `sret([16 x i8])` parameter of `qmark_infallible` (`ptr dead_on_unwind noalias nofree noundef writable writeonly sret([16 x i8]) ... initializes((0, 4), (8, 16))`), whereas LLVM `22.1.6` emits the identical body and `initializes((0, 4), (8, 16))` without `nofree`.

### Feature Gate & Edition Scope

Stable Rust (`--edition=2021` and `--edition=2024`) exposes `?` on `Result`, `Option`, and `Poll`, plus `Infallible` and Edition `2024` tail-expression temporary drop scopes. All other constructs studied here require explicit nightly crate attributes (verified against `compiler/rustc_feature/src/unstable.rs` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):

- `#![feature(try_blocks)]` (`#154391`, `try { ... }`, Edition `>= 2018`)
- `#![feature(try_blocks_heterogeneous)]` (`#149488`, `try bikeshed Ty { ... }`, Edition `>= 2018`)
- `#![feature(yeet_expr)]` (`#96373`, `do yeet expr?`)
- `#![feature(try_trait_v2)]` (`#84277`), `#![feature(try_trait_v2_residual)]` (`#91285`), `#![feature(try_trait_v2_yeet)]` (`#96374`)
- `#![feature(const_trait_impl)]` (`#143874`), `#![feature(const_try)]` (`#74935`), `#![feature(const_try_residual)]` (`#91285`), `#![feature(const_convert)]` (`#143773`)

## Findings

### 1. Core Trait Family (`Try`, `FromResidual`, `Residual`, `Yeet`) and Lang Items

`Basis: normative + source`

RFC 3058 (`rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/3058-try-trait-v2.md`) separates early-exit control flow into two traits—`Try` (splitting a carrier into `ControlFlow<Self::Residual, Self::Output>` and reconstructing from `Output`) and `FromResidual<R>` (reconstructing a target carrier from a compatible residual)—plus `Residual<O>` (the inverse type-level map from `(Residual, Output)` back to the canonical `TryType`). In `library/core/src/ops/try_trait.rs` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), the exact definitions and lang items are:

```rust
// library/core/src/ops/try_trait.rs:131-160, 190-220
#[lang = "Try"]
#[rustc_const_unstable(feature = "const_try", issue = "74935")]
pub const trait Try: [const] FromResidual {
    type Output;
    type Residual: Residual<Self::Output>;

    #[lang = "from_output"]
    fn from_output(output: Self::Output) -> Self;

    #[lang = "branch"]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}

// library/core/src/ops/try_trait.rs:307-334
#[rustc_diagnostic_item = "FromResidual"]
#[rustc_const_unstable(feature = "const_try", issue = "74935")]
pub const trait FromResidual<R = <Self as Try>::Residual> {
    #[lang = "from_residual"]
    fn from_residual(residual: R) -> Self;
}

// library/core/src/ops/try_trait.rs:341-350
#[inline]
#[track_caller] // because `Result::from_residual` has it
#[lang = "from_yeet"]
#[allow(unreachable_pub)]
pub fn from_yeet<T, Y>(yeeted: Y) -> T
where
    T: FromResidual<Yeet<Y>>,
{
    FromResidual::from_residual(Yeet(yeeted))
}

// library/core/src/ops/try_trait.rs:362-385
#[rustc_const_unstable(feature = "const_try_residual", issue = "91285")]
pub const trait Residual<O>: Sized {
    type TryType: [const] Try<Output = O, Residual = Self>;
}

#[expect(unreachable_pub)]
#[inline] // FIXME: force would be nice, but fails -- see #148915
#[lang = "into_try_type"]
pub const fn residual_into_try_type<R: [const] Residual<O>, O>(
    r: R,
) -> <R as Residual<O>>::TryType {
    FromResidual::from_residual(r)
}
```

Four structural invariants in `library/core` control downstream type checking, `const` evaluation, and caller-location tracking:

| Core Type / Helper | Residual Type (`342d74463` / `6905905bb`) | Residual Type (`14210df0e`) | `const` Support | `#[track_caller]` Status |
| :--- | :--- | :--- | :--- | :--- |
| `Result<T, E>` (`Try`) | `Result<!, E>` (`result.rs:2173`) | `Result<convert::Infallible, E>` (`result.rs:2169`) | `const impl` (`const_try`) | N/A (`branch`/`from_output` invoke no `From`) |
| `Result<T, F>` (`FromResidual<Result<!, E>>`) | `Result<!, E>` (`result.rs:2191`) | `Result<convert::Infallible, E>` (`result.rs:2187`) | `const impl` (`F: [const] From<E>`) | **PRESENT** (`result.rs:2193` / `2191`) |
| `Result<T, F>` (`FromResidual<Yeet<E>>`) | `ops::Yeet<E>` (`result.rs:2203`) | `ops::Yeet<E>` (`result.rs:2201`) | `const impl` (`F: [const] From<E>`) | **MISSING (Live Bug 2)** (`result.rs:2205` / `2203`) |
| `Option<T>` (`Try`, `FromResidual<Option<!>>`, `FromResidual<Yeet<()>>`) | `Option<!>` (`option.rs:2867`) | `Option<convert::Infallible>` | `const impl` (`const_try`) | Absent (no user `From` call; constructs `None`) |
| `ControlFlow<B, C>` (`Try`, `FromResidual<ControlFlow<B, !>>`) | `ControlFlow<B, !>` (`control_flow.rs:107`) | `ControlFlow<B, convert::Infallible>` | `const impl` (`const_try`) | Absent (no `From` conversion; `Break(b) => Break(b)`) |
| `from_yeet<T, Y>` (`try_trait.rs:345`) | `T: FromResidual<Yeet<Y>>` | `T: FromResidual<Yeet<Y>>` | **NOT `const fn`** (blocks `const` `do yeet` with `E0015`) | **PRESENT** (`try_trait.rs:342`) |
| `residual_into_try_type<R, O>` (`try_trait.rs:381`) | `<R as Residual<O>>::TryType` | `<R as Residual<O>>::TryType` | `pub const fn` (`const_try_residual`) | **MISSING (Live Bug 1)** (`try_trait.rs:379-385`) |

Notice the subtle internal mismatch on `const` support for `do yeet`: both `Result<T, F>` (`result.rs:2203`) and `Option<T>` (`option.rs:2899`) implement `const impl ... FromResidual<ops::Yeet<_>>`, yet the lang-item shim `from_yeet` (`try_trait.rs:345`) is a plain `pub fn` with a non-`[const]` bound `T: FromResidual<Yeet<Y>>`. Live execution confirms that `do yeet` in any `const fn` fails with `error[E0015]: cannot call non-const function ops::try_trait::from_yeet::<Option<u32>, ()> in constant functions` even when `const_trait_impl`, `const_try`, `const_try_residual`, `try_blocks`, and `yeet_expr` are all enabled.

### 2. Parser and Three-Scope AST-to-HIR Lowering (`TryBlockScope`)

`Basis: source + execution + derived`

#### 2.1 Parser Dispatch (`compiler/rustc_parse/src/parser/expr.rs`)

In `compiler/rustc_parse/src/parser/expr.rs:3360-3396` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; lines `3621-3657` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `is_try_block` recognizes `try` followed by `{`, a block metavariable, or the placeholder contextual keyword `bikeshed` (gated to Edition `>= 2018` via `self.token_uninterpolated_span().at_least_rust_2018()`). `parse_try_block` parses:

```rust
// compiler/rustc_parse/src/parser/expr.rs:3361-3377
fn parse_try_block(&mut self, span_lo: Span) -> PResult<'a, Box<Expr>> {
    let annotation =
        if self.eat_keyword(exp!(Bikeshed)) { Some(self.parse_ty()?) } else { None };
    let (attrs, body) = self.parse_inner_attrs_and_block(None)?;
    if self.eat_keyword(exp!(Catch)) {
        Err(self.dcx().create_err(crate::diagnostics::CatchAfterTry { span: self.prev_token.span }))
    } else {
        let span = span_lo.to(body.span);
        let gate_sym =
            if annotation.is_none() { sym::try_blocks } else { sym::try_blocks_heterogeneous };
        self.psess.gated_spans.gate(gate_sym, span);
        Ok(self.mk_expr_with_attrs(span, ExprKind::TryBlock(body, annotation), attrs))
    }
}
```

Separately, `parse_expr_yeet` (`expr.rs:1709-1721` at `342d74463`; `1875-1887` at `14210df0e`) parses `do yeet expr?`, gates `sym::yeet_expr`, and emits `ExprKind::Yeet(Option<Box<Expr>>)`. Note that `try bikeshed Ty { ... }` activates **only** `try_blocks_heterogeneous` (not `try_blocks`), whereas unannotated `try { ... }` activates **only** `try_blocks`.

#### 2.2 Three-Scope Lowering State Machine (`compiler/rustc_ast_lowering/src/{lib,expr}.rs`)

`LoweringContext` maintains a `try_block_scope: TryBlockScope` field initialized to `TryBlockScope::Function` (`lib.rs:367`) and reset to `TryBlockScope::Function` across every nested body boundary (closures, async/gen blocks, `const` blocks, nested items) inside `with_new_scopes` (`lib.rs:1153-1175`, specifically line `1162`). The enum itself (`lib.rs:609-619`) has exactly three states:

```rust
// compiler/rustc_ast_lowering/src/lib.rs:609-619
#[derive(Copy, Clone, Debug)]
enum TryBlockScope {
    /// There isn't a `try` block, so a `?` will use `return`.
    Function,
    /// We're inside a `try { … }` block, so a `?` will block-break
    /// from that block using a type depending only on the argument.
    Homogeneous(HirId),
    /// We're inside a `try as _ { … }` block, so a `?` will block-break
    /// from that block using the type specified.
    Heterogeneous(HirId),
}
```

Lowering `ExprKind::TryBlock(body, opt_ty)` (`expr.rs:729-780`):

1. Selects `TryBlockScope::Heterogeneous(body_hir_id)` if `opt_ty.is_some()`, else `TryBlockScope::Homogeneous(body_hir_id)` (lines `731-735`).
2. Inside `self.with_try_block_scope(new_scope, ...)`, lowers `body` with `targeted_by_break = true` (`line 737`), extracts `block.expr.take()`—synthesizing `()` at the block's end point when absent (`lines 740-757`, which also explains why a trailing semicolon in `try { do yeet e; }` unifies `<Ret as Try>::Output == ()` and fails `E0271` if `Output != ()`)—and replaces `block.expr` with `::core::ops::Try::from_output(tail_expr)` (`LangItem::TryTraitFromOutput`, lines `763-768`).
3. If `opt_ty` is `Some(ty)`, wraps the resulting `hir::Block` in `hir::ExprKind::Type(block_expr, lowered_ty)` (`lines 773-776`); otherwise emits `hir::ExprKind::Block(whole_block, None)` (`line 778`).

Lowering `<expr>?` (`lower_expr_try`, `expr.rs:1952-2031`) emits `hir::ExprKind::Match(Try::branch(<expr>), [break_arm, continue_arm], MatchSource::TryDesugar)` where `break_arm` dispatches on `self.try_block_scope` (`lines 1992-2020`):

| Active `TryBlockScope` | `?` Constructor Lang Item (`lower_expr_try`) | `?` Control Exit | `do yeet` Constructor Lang Item (`lower_expr_yeet`) | `do yeet` Control Exit |
| :--- | :--- | :--- | :--- | :--- |
| `Function` | `LangItem::TryTraitFromResidual` (`FromResidual::from_residual`) | `return` (`checked_return`) | `LangItem::TryTraitFromYeet` (`from_yeet`) | `return` (`checked_return`) |
| `Homogeneous(block_id)` | `LangItem::ResidualIntoTryType` (`residual_into_try_type`) | `break 'block_id` | **`LangItem::TryTraitFromYeet` (`from_yeet`)** | `break 'block_id` |
| `Heterogeneous(block_id)` | `LangItem::TryTraitFromResidual` (`FromResidual::from_residual`) | `break 'block_id` | `LangItem::TryTraitFromYeet` (`from_yeet`) | `break 'block_id` |

#### 2.3 Type-Inference Determinacy vs. Heterogeneous Conversion (Empirical Matrix)

Because `<R as Residual<O>>::TryType` is an associated type (a partial function of `(R, O)`), routing homogeneous `?` through `residual_into_try_type<R, O>(r) -> <R as Residual<O>>::TryType` uniquely pins the `try {}` block's return type from the residual `R` and the tail expression's output `O` alone—eliminating `E0283` on unannotated `try {}` blocks at the exact price of forbidding `From<SubErr> for SuperErr` error widening (`E0308`). Conversely, `lower_expr_yeet` (`expr.rs:2056-2071`) never consults `ResidualIntoTryType`: even inside `TryBlockScope::Homogeneous(block_id)`, it emits `from_yeet` (which delegates directly to `FromResidual::from_residual(Yeet(yeeted))`), inverting both properties!

Live execution across both `rustc 1.98.0-nightly` (`14210df0e`) and `rustc 1.102.0-nightly` (`6905905bb`) confirms every cell of this matrix:

| Probe Case (`probe2`) | Surface Snippet | `1.98.0-nightly` Result | `1.102.0-nightly` Result | Root Cause |
| :--- | :--- | :--- | :--- | :--- |
| `homo_unannotated_ok` | `let x = try { let a = Some(41u32)?; a + 1 };` | Pass (`rc=0`, `x == Some(42)`) | Pass (`rc=0`) | `residual_into_try_type` fixes `<Option<!> as Residual<u32>>::TryType = Option<u32>`. |
| `homo_from_conv_rejected` | `let _x: Result<u32, SuperErr> = try { Err::<u32, SubErr>(SubErr)? };` | Fail `E0308` (`expected Result<u32, SuperErr>, found Result<_, SubErr>`) | Fail `E0308` (identical) | `residual_into_try_type` pins `Result<_, SubErr>`, blocking `From<SubErr> for SuperErr`. |
| `homo_yeet_from_conv_accepted` | `let x: Result<u32, SuperErr> = try { if true { do yeet SubErr(77); } 0u32 };` | Pass (`HOMO_YEET_CONV_OK=77`) | Pass (`HOMO_YEET_CONV_OK=77`) | `lower_expr_yeet` emits `from_yeet`, bypassing `ResidualIntoTryType` and invoking `Result`'s `FromResidual<Yeet<SubErr>>`. |
| `homo_yeet_unannotated_rejected` | `let _x = try { if true { do yeet 1u8; } 0u32 };` | Fail `E0283` (`must implement FromResidual<Yeet<u8>>` at `try_trait.rs:347`) | Fail `E0283` (identical) | `from_yeet` constrains only `T: FromResidual<Yeet<u8>>`, which has infinitely many solutions (`Result<u32, E>` for any `E: From<u8>`). |
| `hetero_bikeshed_from_conv_accepted` | `try bikeshed Result<u32, SuperErr> { Err::<u32, SubErr>(SubErr(107))? }` | Pass (`HETERO_BIKESHED_CONV_OK=107`) | Pass (`HETERO_BIKESHED_CONV_OK=107`) | `TryBlockScope::Heterogeneous` emits `FromResidual::from_residual`, with `ExprKind::Type` fixing `SuperErr`. |
| `infallible_alias_never_no_blanket_from` | `fn f(r: Result<u64, Infallible>) { let _out: Result<u64, u32> = (\|\| Ok(r?))(); }` | Fail `E0277` (`From<Infallible> is not implemented for u32`) | Fail `E0277` (`From<!> is not implemented for u32`) | `<Result<T, F> as FromResidual<Result<!, E>>>` requires `F: From<E>`; no blanket `impl<T> From<!> for T`. |
| `infallible_is_never_type_identity_check` | `assert_same::<Infallible, !>();` | Fail `E0277` (`Infallible: Same<!>` unsatisfied) | Type-identical by `pub type Infallible = !` (`convert/mod.rs:915`) | Version boundary: `pub enum Infallible {}` (`1.98.0-nightly`) vs. `pub type Infallible = !` (`>= 1.100.0`). |
| `const_try_missing_const_trait_impl_rejected` | `#![feature(const_try, const_try_residual, try_blocks)] const fn ... { try { a? + b? } }` | Fail `E0658` (`? is not allowed on Option<u32> in constant functions`, cites `#143874`) | Source-identical gate (`const_trait_impl`) | `Try`, `FromResidual`, `Residual` are `const trait`s gated by `const_trait_impl` (`#143874`). |
| `const_try_with_const_trait_impl_accepted` | Adding `#![feature(const_trait_impl)]` | Pass (`CONST_TRY_OK=42`) | Pass (`probe4` compiles `const fn`s) | All three traits resolve as `[const]` bounds. |
| `const_yeet_rejected_non_const_from_yeet` | `const fn yeet_opt() -> Option<u32> { if true { do yeet; } Some(1) }` | Fail `E0015` (`from_yeet` at `try_trait.rs:345` is not `const`) | Source-identical (`pub fn from_yeet` at `try_trait.rs:345`) | `from_yeet` is non-`const` despite `const impl` of `FromResidual<Yeet<_>>` on `Result` and `Option`. |

### 3. Two Live `libcore` `#[track_caller]` Location-Loss Bugs and MIR/Miri Inlining Semantics

`Basis: source + execution + derived`

#### 3.1 Shared Caller-Location Resolution Algorithm Across LLVM Codegen and Miri

In `rustc`, `#[track_caller]` forwarding is NOT defeated by inlining—and conversely, inlining NEVER heals a missing `#[track_caller]` attribute. Both LLVM codegen and Miri resolve `Location::caller()` through the exact same function, `Body::caller_location_span` in `compiler/rustc_middle/src/mir/mod.rs:685-713` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):

```rust
// compiler/rustc_middle/src/mir/mod.rs:685-713
pub fn caller_location_span<T>(
    &self,
    mut source_info: SourceInfo,
    caller_location: Option<T>,
    tcx: TyCtxt<'tcx>,
    from_span: impl FnOnce(Span) -> T,
) -> T {
    loop {
        let scope_data = &self.source_scopes[source_info.scope];

        if let Some((callee, callsite_span)) = scope_data.inlined {
            // Stop inside the most nested non-`#[track_caller]` function,
            // before ever reaching its caller (which is irrelevant).
            if !callee.def.requires_caller_location(tcx) {
                return from_span(source_info.span);
            }
            source_info.span = callsite_span;
        }

        // Skip past all of the parents with `inlined: None`.
        match scope_data.inlined_parent_scope {
            Some(parent) => source_info.scope = parent,
            None => break,
        }
    }

    // No inlined `SourceScope`s, or all of them were `#[track_caller]`.
    caller_location.unwrap_or_else(|| from_span(source_info.span))
}
```

- When MIR inlining (`compiler/rustc_mir_transform/src/inline.rs:1243-1263`, `Integrator::visit_source_scope_data`) inlines a callee, it records `scope_data.inlined = Some((callee, callsite_span))` and links `inlined_parent_scope`.
- `InstanceKind::requires_caller_location` (`compiler/rustc_middle/src/ty/instance.rs:306-318`) returns `true` iff `CodegenFnAttrFlags::TRACK_CALLER` is present on the callee `DefId` (or `track_caller` on a `ClosureOnce` shim).
- `rustc_codegen_ssa` (`compiler/rustc_codegen_ssa/src/mir/block.rs:2174-2183`, `get_caller_location`) and `rustc_const_eval` / Miri (`compiler/rustc_const_eval/src/interpret/eval_context.rs:383-415` & `intrinsics.rs:321-327`) both delegate directly to `Body::caller_location_span`.
- Consequently, whether a wrapper chain executes out-of-line (`-O0` / Miri) or fully inlined (`-O2`), **a single intermediate wrapper lacking `#[track_caller]` truncates the caller-location chain at that wrapper's internal call-site span**.

#### 3.2 Exact Anatomy of Both Live `libcore` Bugs

1. **Bug 1 — `residual_into_try_type` omits `#[track_caller]` (`library/core/src/ops/try_trait.rs:379-385`):**
   ```rust
   #[inline] // FIXME: force would be nice, but fails -- see #148915
   #[lang = "into_try_type"]
   pub const fn residual_into_try_type<R: [const] Residual<O>, O>(
       r: R,
   ) -> <R as Residual<O>>::TryType {
       FromResidual::from_residual(r) // <--- line 384: captured instead of user's `?`!
   }
   ```
   When a user writes `try { mk_my_err()? }` for a custom `Try` type `MyTry<T>` whose `impl<T> FromResidual<MyResidual> for MyTry<T>` carries `#[track_caller]` and records `Location::caller()`, the lowered call chain is `user_site -> residual_into_try_type (track_caller=false, callsite=try_trait.rs:384) -> MyTry::from_residual (track_caller=true) -> Location::caller()`. The chain terminates inside `residual_into_try_type`, returning `<RUST_SYSROOT_SRC>/library/core/src/ops/try_trait.rs:384`.
   *Why `Result<T, E>` masks Bug 1 in homogeneous `try {}` blocks:* Because `residual_into_try_type` forces `Result<O, E>` (same error type `E`), `<Result<O, E> as FromResidual<Result<!, E>>>::from_residual` invokes the reflexive identity `impl<T> From<T> for T` (`convert/mod.rs:787-793`), which never calls `Location::caller()`. Any custom `Try` type that captures `Location::caller()` directly inside `FromResidual::from_residual`—which is a primary use case for `try_trait_v2` error-context wrappers—immediately hits Bug 1! Switching to `try bikeshed MyTry<u32> { mk_my_err()? }` bypasses `residual_into_try_type` and immediately restores the exact user line.

2. **Bug 2 — `<Result<T, F> as FromResidual<ops::Yeet<E>>>::from_residual` omits `#[track_caller]` (`library/core/src/result.rs:2200-2208` at `342d74463`/`6905905bb`; `2198-2206` at `14210df0e`):**
   Contrast the two adjacent `FromResidual` impls in `library/core/src/result.rs`:
   ```rust
   // library/core/src/result.rs:2191-2199 (HAS #[track_caller])
   const impl<T, E, F: [const] From<E>> ops::FromResidual<Result<!, E>> for Result<T, F> {
       #[inline]
       #[track_caller]
       fn from_residual(residual: Result<!, E>) -> Self {
           match residual {
               Err(e) => Err(From::from(e)),
           }
       }
   }
   // library/core/src/result.rs:2203-2208 (MISSING #[track_caller]!)
   const impl<T, E, F: [const] From<E>> ops::FromResidual<ops::Yeet<E>> for Result<T, F> {
       #[inline]
       fn from_residual(ops::Yeet(e): ops::Yeet<E>) -> Self {
           Err(From::from(e)) // <--- line 2206 (main / 1.102.0) or line 2204 (1.98.0)!
       }
   }
   ```
   The irony is explicitly documented in `try_trait.rs:342`, where `from_yeet` carries `#[track_caller] // because Result::from_residual has it`. That comment reflects the author's assumption that `Result`'s `FromResidual<Yeet<E>>` impl carried `#[track_caller]` like its adjacent `FromResidual<Result<!, E>>` impl. In reality, the chain for `do yeet SubErr` into `Result<u32, TrackedErr>` is `user_site -> from_yeet (track_caller=true) -> Result::from_residual<Yeet> (track_caller=false, callsite=result.rs:2206) -> TrackedErr::from (track_caller=true) -> Location::caller()`, which stops at `result.rs:2206` (or `2204` on `1.98.0-nightly`) across ALL three scopes (`fn`, homogeneous `try {}`, and heterogeneous `try bikeshed {}`). Meanwhile, `do yeet SubErr` targeting `MyTry<u32>` (whose `impl FromResidual<Yeet<SubErr>>` carries `#[track_caller]`) preserves the exact user line in all three scopes—proving empirically that `from_yeet` forwards properly and the defect lies strictly on `result.rs:2203-2208`.

#### 3.3 Full Empirical `#[track_caller]` Matrix Across `dev` (`-O0`), `release` (`-O2`), and Miri (`-Zmiri-tree-borrows`)

Every case below produced **100% identical `in_user` / `exact_line` / `got_file` / `got_line` results** across `cargo run` (`-O0`), `cargo run --release` (`-O2`), and `MIRIFLAGS="-Zmiri-tree-borrows" cargo miri run` on both `rustc 1.98.0-nightly` (`probe_rustc_1_98_0_nightly_output.json`, 10 cases x 3 modes = 30 runs) and `rustc 1.102.0-nightly` (`rustc_1_102_0_nightly_llvm23_baseline.json`, 8 cases x 3 modes = 24 runs):

| Case | Scope & Operation | Target Type | `dev` / `release` / `Miri` (`1.98.0-nightly`, `14210df0e`) | `dev` / `release` / `Miri` (`1.102.0-nightly`, `6905905bb`) | Classification |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `fn_result_qmark` | `fn`, `?` | `Result<u32, TrackedErr>` | `in_user=true`, `src/main.rs:82` (exact) | `in_user=true`, `src/main.rs:70` (exact) | Preserved |
| `hetero_result_qmark` | `try bikeshed`, `?` | `Result<u32, TrackedErr>` | `in_user=true`, `src/main.rs:92` (exact) | `in_user=true`, `src/main.rs:79` (exact) | Preserved |
| `homo_custom_qmark` | `try {}`, `?` | `MyTry<u32>` (`#[track_caller]`) | `in_user=false`, **`try_trait.rs:384`** (expected `101`) | `in_user=false`, **`try_trait.rs:384`** (expected `88`) | **Live Bug 1** |
| `hetero_custom_qmark` | `try bikeshed`, `?` | `MyTry<u32>` (`#[track_caller]`) | `in_user=true`, `src/main.rs:110` (exact) | `in_user=true`, `src/main.rs:97` (exact) | Preserved |
| `fn_result_yeet` | `fn`, `do yeet` | `Result<u32, TrackedErr>` | `in_user=false`, **`result.rs:2204`** (expected `119`) | `in_user=false`, **`result.rs:2206`** (expected `106`) | **Live Bug 2** |
| `homo_result_yeet` | `try {}`, `do yeet` | `Result<u32, TrackedErr>` | `in_user=false`, **`result.rs:2204`** (expected `128`) | `in_user=false`, **`result.rs:2206`** (expected `114`) | **Live Bug 2** |
| `hetero_result_yeet` | `try bikeshed`, `do yeet` | `Result<u32, TrackedErr>` | `in_user=false`, **`result.rs:2204`** (expected `137`) | *(not in 8-case baseline; source-identical)* | **Live Bug 2** |
| `fn_custom_yeet` | `fn`, `do yeet` | `MyTry<u32>` (`#[track_caller]`) | `in_user=true`, `src/main.rs:146` (exact) | `in_user=true`, `src/main.rs:124` (exact) | Preserved |
| `homo_custom_yeet` | `try {}`, `do yeet` | `MyTry<u32>` (`#[track_caller]`) | `in_user=true`, `src/main.rs:155` (exact) | `in_user=true`, `src/main.rs:132` (exact) | Preserved |
| `hetero_custom_yeet` | `try bikeshed`, `do yeet` | `MyTry<u32>` (`#[track_caller]`) | `in_user=true`, `src/main.rs:164` (exact) | *(not in 8-case baseline; source-identical)* | Preserved |

### 4. `Infallible = !` Stabilization Boundary and `const_trait_impl` Coupling

`Basis: source + execution`

Diffing `library/core/src/convert/mod.rs` between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`) and `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2` / `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`rustc 1.102.0-nightly` / `main`) exposes the exact transition enacted when `!` stabilized at `1.100.0`:

- **At `14210df0e` (`1.98.0-nightly`):**
  - `pub enum Infallible {}` (`convert/mod.rs:930`), with manual `Clone`, `Debug`, `Display`, `Error`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash` impls.
  - `#[rustc_reservation_impl = "permitting this impl would forbid us from adding impl<T> From<!> for T later; see rust-lang/rust#64715 for details"] const impl<T> From<!> for T` (`convert/mod.rs:798-806`).
  - `Result<T, E>::Residual = Result<convert::Infallible, E>`, `TryFrom::Error = Infallible`.
- **At `6905905bb` and `342d74463` (`1.102.0-nightly` / `main`):**
  - `pub type Infallible = !;` (`convert/mod.rs:915`), with `#[stable(feature = "never_type", since = "1.100.0")]` `AsRef<T>` and `AsMut<T>` impls for `!` (`convert/mod.rs:866-886`), and `TryFrom::Error = !` (`convert/mod.rs:818`).
  - The `#[rustc_reservation_impl]` for `From<!>` is deleted (`convert/mod.rs:794` jumps straight from reflexive `const impl<T> From<T> for T` to `TryInto`), and NO blanket `impl<T> From<!> for T` exists.

The practical consequence for `?` is frequently misunderstood: **making `Infallible` an alias for `!` does NOT allow `Result<T, Infallible>?` to convert automatically into `Result<T, E>` for an arbitrary `E` (such as `u32`).** Because `?` desugars through `<Result<T, F> as FromResidual<Result<!, E>>>::from_residual` with the trait bound `F: From<E>` (NOT value-level never-type coercion `e: ! -> F`), `r?` requires an explicit `From<!>` (equivalently `From<Infallible>`) impl for `u32`. Without a blanket `impl<T> From<!> for T`, `rustc` rejects `(|| Ok(r?))()` into `Result<u64, u32>` with `E0277` in both versions (`the trait From<Infallible> is not implemented for u32` in `1.98.0-nightly`; `the trait From<!> is not implemented for u32` in `1.102.0-nightly`). Callers must either match/unwrap `Ok(v)` directly (`r.into_ok()`, `let Ok(v) = r;`) or define `impl From<Infallible> for CustomErr` on a local error type.

### 5. Edition `2021` vs. `2024` `Try::from_output` Tail Drop-Scope Flip vs. Sub-Expression `?` Invariance

`Basis: normative + source + execution`

The interaction between `try {}` desugaring and Edition `2024` temporary drop scopes (`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/destructors.md:279-290`, rule `r[destructors.scope.temporary.edition2024]`) flows directly from two compiler routines:

1. **`lower_expr_try_block` (`compiler/rustc_ast_lowering/src/expr.rs:729-780`):** Desugars both `try { <stmts>; <tail> }` and `try bikeshed Ty { <stmts>; <tail> }` into an ordinary `hir::Block` whose `blk.span` inherits the source edition and whose `blk.expr` is `Some(Try::from_output(<tail>))`.
2. **`resolve_block` (`compiler/rustc_hir_analysis/src/check/region.rs:145-162`):**
   ```rust
   // compiler/rustc_hir_analysis/src/check/region.rs:145-162
   if let Some(tail_expr) = blk.expr {
       let local_id = tail_expr.hir_id.local_id;
       let edition = blk.span.edition();
       let terminating = edition.at_least_rust_2024();
       if !terminating
           && !visitor.tcx.skippable_lints(()).contains(&LintId::of(TAIL_EXPR_DROP_ORDER))
       {
           visitor
               .scope_tree
               .backwards_incompatible_scope
               .insert(local_id, Scope { local_id, data: ScopeData::Node });
       }
       resolve_expr(visitor, tail_expr, terminating);
   }
   ```
   - **In Edition `2021` (`terminating = false`):** `Try::from_output(<tail>)` does NOT create a `ScopeData::Destruction` inside the `try` block. Any temporary created while evaluating `<tail>` (e.g., the `Ref<'_, u32>` returned by `c.borrow()`, or `Guard("tail_tmp")`) attaches to the enclosing terminating scope *outside* the `try` block. Meanwhile, every `let` binding inside the `try` block (`let c = RefCell::new(41u32);` or `let _blk_local = Guard("blk_local");`) attaches to `ScopeData::Remainder` *inside* `blk` (`region.rs:124-137`). On normal block exit, `blk`'s locals drop **before** `<tail>`'s temporaries.
   - **In Edition `2024` (`terminating = true`):** `resolve_expr(visitor, tail_expr, true)` enters `Scope { local_id: tail_expr.hir_id.local_id, data: ScopeData::Destruction }` *inside* `blk`'s `Remainder` scopes. Therefore, `<tail>`'s temporaries drop immediately after `Try::from_output(<tail>)` finishes and **strictly before** `blk`'s locals drop.
   - **Why statement-level `scrut? + rhs` does NOT flip across editions:** `resolve_stmt` (`region.rs:222-249`) wraps every non-`super let` statement in a terminating scope, while `lower_expr_try` lowers `scrut?` to `hir::ExprKind::Match(Try::branch(scrut), ...)`. In `resolve_expr` (`region.rs:252-396`), `hir::ExprKind::Match` is NOT a terminating scope (`_ => intravisit::walk_expr`, line `392`; only `resolve_arm` at line `195` terminates each arm body). Thus, temporaries inside `scrut` and `rhs` both live until the enclosing statement terminator and drop in LIFO creation order (`["rhs_tmp", "scrut_tmp"]` on `Ok`, `["scrut_tmp"]` on `Err`) identically in Editions `2021` and `2024`.

Live execution of `probe3_edition_drop_order` confirms identical traces on both `rustc 1.98.0-nightly` and `rustc 1.102.0-nightly` (with `hetero_try_tail_*` additionally verified live on `1.98.0-nightly`):

| Scenario | `--edition=2021` Observed Result | `--edition=2024` Observed Result |
| :--- | :--- | :--- |
| `qmark_ok` (`let x = mk_scrut_ok().1? + mk_rhs().1;`) | `Ok(16)`, drops = `["rhs_tmp", "scrut_tmp", "stmt_done", "fn_local"]` | `Ok(16)`, drops = `["rhs_tmp", "scrut_tmp", "stmt_done", "fn_local"]` (**invariant**) |
| `qmark_err` (`let x = mk_scrut_err().1? + mk_rhs().1;`) | `Err("boom")`, drops = `["scrut_tmp", "fn_local"]` | `Err("boom")`, drops = `["scrut_tmp", "fn_local"]` (**invariant**) |
| `try_tail_ok` (`try { let _blk; let a = ok("qmark_tmp")?; a + Guard("tail_tmp").val() }`) | `Ok(11)`, drops = `["qmark_tmp", "blk_local", "tail_tmp"]` | `Ok(11)`, drops = `["qmark_tmp", "tail_tmp", "blk_local"]` (**flipped**) |
| `try_tail_tuple` (`try { let _blk; (Guard("tail_tuple_tmp"), 42).1 }`) | `Ok(42)`, drops = `["blk_local", "tail_tuple_tmp"]` | `Ok(42)`, drops = `["tail_tuple_tmp", "blk_local"]` (**flipped**) |
| `hetero_try_tail_ok` (`try bikeshed Result<u32, &str> { ... }`) | `Ok(11)`, drops = `["qmark_tmp", "blk_local", "tail_tmp"]` | `Ok(11)`, drops = `["qmark_tmp", "tail_tmp", "blk_local"]` (**flipped**) |
| `try_tail_refcell_borrow` (`try { let c = RefCell::new(41u32); *c.borrow() + 1 }`) | **Compile Fail `E0597`** (`c` dropped before `Ref<'_, u32>` temp) | **Compile & Run Pass** (`Ok(42)`, exit `0`) |
| `hetero_try_tail_refcell_borrow` (`try bikeshed Result<u32, ()> { let c = ...; *c.borrow() + 1 }`) | **Compile Fail `E0597`** (`c` dropped before `Ref<'_, u32>` temp) | **Compile & Run Pass** (`Ok(42)`, exit `0`) |

### 6. `Runtime(PostCleanup)` -> `Runtime(Optimized)` MIR Collapse & LLVM 22/23 Codegen

`Basis: source + execution`

Inspecting `-Z dump-mir` at `Runtime(PostCleanup)` (`-C opt-level=0`, file `*.3-2-000.runtime-post-cleanup.after.mir`) versus `Runtime(Optimized)` (`-C opt-level=2`, file `*.3-3-000.runtime-optimized.after.mir`) reveals a sharp structural contrast directly relevant to MIR-level formal verification:

| Function | `PostCleanup` MIR (`-O0`): BBs / `SwitchInt` / `unreachable` | `PostCleanup` MIR (`-O0`): Live Calls (`branch` / `residual_into_try_type` / `from_residual`) | `Optimized` MIR (`-O2`): BBs / `SwitchInt` / `unreachable` | `Optimized` MIR (`-O2`): Live Calls vs. Inlined Scope Mentions |
| :--- | :--- | :--- | :--- | :--- |
| `qmark_infallible` (`Result<u64, Infallible> -> Result<u64, CustomErr>`) | `8` / `1` / `1` | `1` / `0` / `1` | **`1` / `0` / `0`** | **`0` / `0` / `0` live calls** (`1` inlined scope comment mentioning `from_residual`) |
| `qmark_infallible_same` (`Result<u64, Infallible> -> Result<u64, Infallible>`) | `8` / `1` / `1` | `1` / `0` / `1` | **`1` / `0` / `0`** | **`0` / `0` / `0` live calls** (`1` inlined scope comment mentioning `from_residual`) |
| `qmark_opt_nonzero` (`Option<NonZeroU64> -> Option<NonZeroU64>`) | `9` / `1` / `1` | `1` / `0` / `1` | `5` / `1` / `1` | **`0` / `0` / `0` live calls** (`1` inlined scope comment mentioning `from_residual`) |
| `homo_try_opt_u64` (`(Option<u64>, Option<u64>) -> Option<u64>` via `try { x? + y? }`) | `14` / `2` / `1` | `2` / `2` / `0` | `8` / `2` / `1` | **`0` / `0` / `0` live calls** (`2` `residual_into_try_type` + `2` `from_residual` inlined scope comments) |

Notice an important methodological clarification uncovered by comparing raw substring counts against terminator-line call counts: in `Runtime(Optimized)` MIR (`-O2`), **all** `Try::branch`, `residual_into_try_type`, and `FromResidual::from_residual` calls are completely inlined (`0` live `TerminatorKind::Call` instructions remain in all four functions!). Raw string greps for `from_residual` or `residual_into_try_type` in `*.runtime-optimized.after.mir` return `1` or `2` solely because `rustc` preserves the inlined callee symbol names inside MIR `scope N (inlined ...)` debug/caller-location metadata headers.

Direct inspection of the emitted MIR for `qmark_infallible` and `homo_try_opt_u64` makes both the uninhabited-arm elimination and Bug 1's missing `#[track_caller]` attribute directly visible in the IR itself:

```text
// lib.qmark_infallible.3-3-000.runtime-optimized.after.mir (rustc 1.98.0-nightly, -O2)
scope 2 {
    debug residual => const ZeroSized: Result<Infallible, Infallible>;
    scope 3 {
        scope 10 (inlined #[track_caller] <Result<u64, CustomErr> as FromResidual<Result<Infallible, Infallible>>>::from_residual) {
            scope 11 { scope 12 (inlined <CustomErr as From<Infallible>>::from) {} }
        }
    }
}
bb0: {
    StorageLive(_3);
    _3 = discriminant(_1);
    _5 = Eq(copy _3, const 0_isize);
    assume(move _5);
    _4 = copy ((_1 as Ok).0: u64);
    StorageDead(_3);
    StorageLive(_2);
    _2 = Add(copy _4, const 1_u64);
    _0 = Result::<u64, CustomErr>::Ok(move _2);
    StorageDead(_2);
    return;
}

// lib.homo_try_opt_u64.3-3-000.runtime-optimized.after.mir (scope header excerpt)
// Note the absence of `#[track_caller]` on `scope 13` (Bug 1):
scope 13 (inlined ops::try_trait::residual_into_try_type::<Option<Infallible>, u64>) {
    scope 14 (inlined <Option<u64> as FromResidual<Option<Infallible>>>::from_residual) { ... }
}
```

In `qmark_infallible`, `rustc` replaces the `8`-BB `SwitchInt` + `unreachable` + `from_residual` CFG from `Runtime(PostCleanup)` MIR with an explicit `NonDivergingIntrinsic::Assume` (`assume(Eq(discriminant(_1), 0_isize))`) followed by direct payload projection `(_1 as Ok).0`—confirming that dead-arm elimination happens inside MIR optimization before LLVM IR generation. Meanwhile, comparing `scope 10` (`inlined #[track_caller] ...::from_residual`) against `scope 13` (`inlined ops::try_trait::residual_into_try_type`, lacking `#[track_caller]`) illustrates directly how `Body::caller_location_span` sees `requires_caller_location == false` on `scope 13` even after full `-O2` inlining.

At `-C opt-level=2 --emit=llvm-ir`, both LLVM `22.1.6` (`1.98.0-nightly`) and LLVM `23.1.6` (`1.102.0-nightly`) produce completely branchless code for all four functions:

1. **`qmark_infallible` (`Result<u64, Infallible> -> Result<u64, CustomErr>`):** The uninhabited `Infallible` input discriminant disappears completely (`i64 noundef %r`), while the `16`-byte `Result<u64, CustomErr>` return uses `sret([16 x i8]) align 8 ... initializes((0, 4), (8, 16))`—leaving padding bytes `[4, 8)` explicitly uninitialized, storing `r + 1` at offset `8` and the `Ok` tag `0i32` at offset `0` with zero branches:
   ```llvm
   ; LLVM 23.1.6 (rustc 1.102.0-nightly, 6905905bb); LLVM 22.1.6 (14210df0e) is identical except omitting `nofree`
   define void @qmark_infallible(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([16 x i8]) align 8 captures(none) dereferenceable(16) initializes((0, 4), (8, 16)) %_0, i64 noundef %r) unnamed_addr #1 {
   start:
     %_2 = add i64 %r, 1
     %0 = getelementptr inbounds nuw i8, ptr %_0, i64 8
     store i64 %_2, ptr %0, align 8
     store i32 0, ptr %_0, align 8
     ret void
   }
   ```
2. **`qmark_infallible_same` (`Result<u64, Infallible> -> Result<u64, Infallible>`):** When both input and output carry uninhabited errors, the return slot collapses to a single `i64` register (`define noundef i64 @qmark_infallible_same(i64 noundef %r) { %_2 = add i64 %r, 1; ret i64 %_2 }`).
3. **`qmark_opt_nonzero` (`Option<NonZeroU64>`):** Niche optimization encodes `None` as `0i64` and `Some(v)` as nonzero `i64`, lowering `?` + `NonZeroU64::new(v.get() | 1)` to 4 branchless instructions (`icmp eq i64 %0, 0` + `or i64 %0, 1` + `select i1 %.not, i64 0, i64 %_4` + `ret`).
4. **`homo_try_opt_u64` (`try { x?.wrapping_add(y?) }`):** Two short-circuiting `?` operators via `residual_into_try_type` collapse into a single branchless tag conjunction (`%4 = and i64 %2, %0`, `%or.cond.not.not = icmp eq i64 %4, 0`, `%_3 = add i64 %3, %1`, `%_0.sroa.4.1 = select i1 %or.cond.not.not, i64 undef, i64 %_3`, `insertvalue { i64, i64 } poison, ...`). Note that the `None` payload slot deliberately selects `undef` (not `0`), which is valid under LLVM/Rust ABI because `None`'s payload bytes are padding/uninitialized.

### 7. Mechanized Lean `v4.34.1` Formalization (`support/TryTraitResidualCallerAndDropSoundness.lean`)

`Basis: derived + execution`

`support/TryTraitResidualCallerAndDropSoundness.lean` (`631` lines, `314` namespace declarations) formalizes all three compiler semantics and all three counterexamples under strict kernel-purity constraints (`LEAN_SYSROOT=leanprover--lean4---v4.34.1`, `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`, every value definition marked `noncomputable def`, zero `deriving` clauses):

| Theorem | Formal Statement Summary | Verified Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| `try_scope_conversion_and_inference_characterization` | Jointly proves: (a) `TryBlockScope.homogeneous` `?` uniquely determines `<R as Residual<O>>::TryType` (`UniquelyDeterminesTarget`) and rejects heterogeneous `From` widening (`¬ AdmitsHeterogeneousConversion`); (b) `fnScope` and `heterogeneous` `?` both admit heterogeneous `From` conversion and fail unannotated determinacy; (c) `do yeet` inside `homogeneous` emits `.fromYeet`, admitting conversion while breaking unannotated determinacy (`E0283`); (d) `fnScope` returns while both `try`-block scopes break. | *(none — 0 axioms)* |
| `infallible_qmark_requires_from_witness` | Proves that because `<Result<O, F> as FromResidual<Result<!, E>>>` is gated by `hasFrom e f`, lacking `hasFrom neverTy targetErrTy` renders `?` on `Result<O, !>` into `Result<O, targetErrTy>` inadmissible regardless of uninhabitedness of `!`. | *(none — 0 axioms)* |
| `evalCallStackLoc_eq_resolveInlinedScopeLoc` | Structural induction proving that top-down runtime/Miri call-stack propagation (`evalCallStackLoc userSite outerToInner`) equals bottom-up MIR inlined-scope traversal (`resolveInlinedScopeLoc outerToInner.reverse userSite`, mirroring `Body::caller_location_span`). | `[propext]` |
| `caller_location_preserved_iff_all_wrappers_track_caller` | Exact `↔` characterization: when internal wrapper call sites do not collide with `userSite`, both out-of-line (`-O0`/Miri) and inlined (`-O2`) caller-location resolution return `userSite` iff every intermediate wrapper in `outerToInner` has `trackCaller = true`. | `[propext]` |
| `edition2024_try_tail_drop_and_infallible_branch_elim_sound` | Jointly proves: (a) under `Edition.ed2024`, every `Try::from_output` tail temporary drops strictly before every block-local binding (`DropsBefore t l`); (b) statement-level `scrut? + rhs` drop order is edition-invariant; (c) eliminating the `ControlFlow::Break` switch arm and `from_residual` call for any uninhabited error type (`uninhab : E -> Empty`) preserves exact operational equivalence between `PostCleanup` MIR and single-block `Optimized` MIR. | `[propext]` |
| `ce1_residual_into_try_type_drops_caller_location` | Constructive witness for Live Bug 1: instantiating `[residual_into_try_type(tc=false, line 384), MyTry::from_residual(tc=true)]` evaluates to `line 384 != userLine101` in both models, while flipping only `residual_into_try_type.trackCaller := true` restores `userLine101`. | *(none — 0 axioms)* |
| `ce2_result_yeet_impl_drops_caller_location` | Constructive witness for Live Bug 2: instantiating `[from_yeet(tc=true, line 349), Result::from_residual<Yeet>(tc=false, line 2206), TrackedErr::from(tc=true)]` evaluates to `line 2206 != userLine119` in both models, while flipping only `Result::from_residual<Yeet>.trackCaller := true` restores `userLine119`. | *(none — 0 axioms)* |
| `ce3_edition2021_try_tail_drops_local_before_borrow_temp` | Constructive witness for Edition `2021` `E0597`: `try { let c = RefCell::new(41); *c.borrow() + 1 }` drops `[localC, borrowGuardTemp]` (`¬ DropsBefore borrowGuardTemp localC`) in Edition `2021` and `[borrowGuardTemp, localC]` (`DropsBefore borrowGuardTemp localC`) in Edition `2024`. | *(none — 0 axioms)* |

### 8. Implications for Anneal's Trusted MIR Boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

`Basis: source + derived`

Direct inspection of `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes four concrete TCB touchpoints for verifying Rust code using `Try` v2 (`?`, `try {}`, `do yeet`):

1. **Already Admitted Primitives:** `MirTy.never` (`MirAst.lean:316`) is admitted in `isSupportedScalarOrUnitTy` (`MirSemantics.lean:722`), has `liveUninitSlot .never = .live none` (`MirSemantics.lean:748-750`), and admits vacuous uninhabited-parameter proofs (`canaryNeverParamBody`, `MirSemantics.lean:2513`). `TerminatorKind.switchInt` (`MirAst.lean:787`, `MirSemantics.lean:1553-1567`) and `TerminatorKind.unreachable` (`MirAst.lean:789`, `MirSemantics.lean:1551-1552`, faulting `.fault .undefined` matching `rustc_const_eval`) are likewise implemented.
2. **`Runtime(PostCleanup)` MIR Admission Gaps:** Because `Runtime(PostCleanup)` MIR retains uninlined calls to `Try::branch`, `Try::from_output`, `FromResidual::from_residual`, `residual_into_try_type`, and `from_yeet`, as well as enum discriminant writes (`SetDiscriminant`), destructors (`TerminatorKind::Drop`), and Edition `2021` migration hints (`StatementKind::BackwardIncompatibleDropHint` emitted whenever `TAIL_EXPR_DROP_ORDER` triggers on a `try {}` tail), `Trusted.MirAst` and `Trusted.MirSemantics` currently fail closed (`.unsupported`) on all four (`MirAst.lean:654-662`, `MirAst.lean:782-795`, `MirSemantics.lean:1568-1569`).
3. **`PostCleanup` vs. `Optimized` MIR Verification Trade-off:** For `qmark_infallible`, `Runtime(PostCleanup)` MIR still contains `8` basic blocks, `1` `SwitchInt`, `1` `unreachable`, and `2` trait calls (`branch`, `from_residual`), whereas `Runtime(Optimized)` collapses all of them to `1` basic block (`0` calls, `0` switches). Any verified compiler pass or Anneal MIR-level proof obligation targeting `Runtime(PostCleanup)` MIR must either support direct monomorphized `Call` evaluation + uninhabited-variant elimination (justifying the `8 -> 1` collapse via `qmark_infallible_branch_elim_sound`) or lower `Try` calls explicitly without trusting unverified MIR inlining.
4. **Caller-Location Metadata Gap:** `TerminatorKind.call` (`MirAst.lean:793-794`) carries `(callee, args, dst, target, unwind)` with no `SourceScope.inlined` tree or implicit `caller_location` argument. Verifying functional specifications of `#[track_caller]` `From` / `FromResidual` implementations (or proving that MIR inlining preserves `Location::caller()`) therefore requires extending `Trusted.MirAst` with `SourceScope` inlining metadata and implementing `Body::caller_location_span` (validated by `evalCallStackLoc_eq_resolveInlinedScopeLoc` in our Lean module).

## Boundaries

- **Known not to apply:**
  - **Bug 1 (`residual_into_try_type`) on `Result<T, E>` homogeneous `try {}` blocks:** Because `<Result<!, E> as Residual<O>>::TryType` fixes the output error type to the identical `E`, `Result::from_residual` invokes reflexive `impl<T> From<T> for T` (`convert/mod.rs:787`), which never reads `Location::caller()`. Bug 1 therefore manifests on custom `Try` types whose `FromResidual::from_residual` carries `#[track_caller]` (or panics inside `from_residual`), not on standard `Result<T, E>` `?` in homogeneous `try {}`.
  - **Edition `2024` temporary-scope narrowing on statement-level `scrut? + rhs`:** Verified by both source (`region.rs:252-396`) and live execution (`probe3`): `hir::ExprKind::Match` scrutinees do NOT become terminating scopes in Edition `2024`; only block tail expressions (including `try {}` and `try bikeshed Ty {}` tails wrapped in `Try::from_output`) and `if let` conditions flip.
  - **Automatic `! -> E` coercion through `Result<T, Infallible>?`:** Stabilizing `pub type Infallible = !` in `>= 1.100.0` does NOT introduce blanket `impl<T> From<!> for T`; `Result<u64, Infallible>?` into `Result<u64, u32>` remains rejected with `E0277`.
  - **`const fn` support for `do yeet`:** Even with `const_trait_impl`, `const_try`, `const_try_residual`, and `yeet_expr` enabled, `do yeet` is **unsupported** in `const fn` (`E0015`) because `core::ops::try_trait::from_yeet` is non-`const`.
- **Not examined:**
  - **Other `libcore`/`libstd` `Try` carriers:** `core::task::Poll<Option<Result<T, E>>>`, `core::task::Poll<Result<T, E>>`, and `std::process::ExitCode` were not probed for `#[track_caller]` or LLVM lowering behavior.
  - **Unwinding / panic drop order inside `Try::branch` or `FromResidual::from_residual`:** `probe3` measured normal `Ok` and `Err` early-return drop orders only; panic-unwinding drop orders when a `From::from` implementation panics mid-`?` were not executed.
  - **Non-`x86_64-unknown-linux-gnu` ABI targets:** LLVM IR `sret([16 x i8])` and `{ i64, i64 }` register-return lowering in `probe4` were observed on `x86_64-unknown-linux-gnu` only; `aarch64`, `i686`, and Windows MSVC calling conventions were not compiled.
  - **Direct `import Trusted.MirSemantics` bridge in Lean:** `support/TryTraitResidualCallerAndDropSoundness.lean` is a standalone Lean `v4.34.1` module modeling `rustc`'s AST lowering, `Body::caller_location_span`, drop-scope ordering, and `ControlFlow` residual elimination; mechanically embedding `FromResidual`/`Drop` calls directly inside `joshlf/anneal`'s `Trusted.MirSemantics` awaits Anneal's admission of `TerminatorKind.call` and `TerminatorKind::Drop`.
- **Unknown:**
  - **Future stabilization syntax for heterogeneous `try` blocks (`#149488`) and `#148915`:** The `bikeshed` keyword is explicitly a placeholder pending RFC / lang-team syntax selection, and whether upstream fixes Bug 1 by adding `#[track_caller]` to `residual_into_try_type` vs. resolving `#148915` (`#[rustc_force_inline]`, which still would NOT by itself forward caller locations without `#[track_caller]` under `Body::caller_location_span`!) remains open upstream.

## Evidence

### Primary-Source Citations

1. **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (identical across all listed files to `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`):**
   - `library/core/src/ops/try_trait.rs:116-220` (`Try`), `227-334` (`FromResidual`), `336-350` (`from_yeet`, `#[track_caller]` at `342`, non-`const` `pub fn` at `345`, body call at `349`), `362-369` (`Residual<O>`), `375-385` (`residual_into_try_type`, missing `#[track_caller]`, body call at `384`), `399-463` (`NeverShortCircuit`, `Yeet`).
   - `library/core/src/result.rs:2169-2187` (`Try`), `2189-2199` (`FromResidual<Result<!, E>>` with `#[track_caller]` at `2193`), `2200-2208` (`FromResidual<Yeet<E>>` missing `#[track_caller]`, `Err(From::from(e))` at `2206`), `2210-2214` (`Residual<T>`).
   - `library/core/src/option.rs:2863-2910` (`Try`, `FromResidual<Option<!>>`, `FromResidual<Yeet<()>>`, `Residual<T>`).
   - `library/core/src/ops/control_flow.rs:103-140` (`Try`, `FromResidual<ControlFlow<B, !>>`, `Residual<C>`).
   - `library/core/src/convert/mod.rs:785-824` (reflexive `From`, `TryFrom` with `Error = !`, no `From<!>` impl), `866-915` (`AsRef`/`AsMut` for `!` `since = "1.100.0"`, `pub type Infallible = !;` at `915`).
   - `compiler/rustc_parse/src/parser/expr.rs:1709-1721` (`parse_expr_yeet`), `3361-3396` (`parse_try_block`, `is_do_yeet`, `is_try_block`).
   - `compiler/rustc_ast_lowering/src/lib.rs:367, 609-619, 1153-1175` (`TryBlockScope` enum and `with_new_scopes` reset to `TryBlockScope::Function`).
   - `compiler/rustc_ast_lowering/src/expr.rs:729-791` (`lower_expr_try_block`, `wrap_in_try_constructor`), `1630-1639` (`with_try_block_scope`), `1952-2072` (`lower_expr_try`, `lower_expr_yeet`).
   - `compiler/rustc_hir_analysis/src/check/region.rs:57-166` (`resolve_block`, Edition `2024` `terminating` flip at `145-162`), `222-249` (`resolve_stmt`), `252-396` (`resolve_expr`).
   - `compiler/rustc_middle/src/ty/instance.rs:306-318` (`InstanceKind::requires_caller_location`), `compiler/rustc_middle/src/mir/mod.rs:685-713` (`Body::caller_location_span`), `compiler/rustc_mir_transform/src/inline.rs:1243-1263` (`Integrator::visit_source_scope_data`), `compiler/rustc_codegen_ssa/src/mir/block.rs:2174-2183` (`get_caller_location`), `compiler/rustc_const_eval/src/interpret/eval_context.rs:383-415` (`InterpCx::caller_location`), `compiler/rustc_const_eval/src/interpret/intrinsics.rs:321-327` (`sym::caller_location`).
   - `compiler/rustc_feature/src/unstable.rs:463, 465, 766, 768, 802` (feature gate definitions).
2. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`):**
   - `library/core/src/convert/mod.rs:798-806` (`#[rustc_reservation_impl] const impl<T> From<!> for T`), `928-930` (`pub enum Infallible {}`).
   - `library/core/src/result.rs:2165-2212` (`FromResidual<Result<convert::Infallible, E>>` with `#[track_caller]` at `2191`; `FromResidual<ops::Yeet<E>>` omitting `#[track_caller]`, `Err(From::from(e))` at `2204`).
   - `library/core/src/ops/try_trait.rs:336-385` (`from_yeet` at `342-350`, `residual_into_try_type` at `381-385`).
   - `compiler/rustc_parse/src/parser/expr.rs:1875-1887, 3622-3657` (`parse_expr_yeet`, `parse_try_block`).
3. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
   - `trusted/lean/Trusted/MirAst.lean:316, 654-662, 770-795`; `trusted/lean/Trusted/MirSemantics.lean:721-724, 748-750, 1537-1569, 2513`.
4. **Normative Documents:**
   - `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/3058-try-trait-v2.md`.
   - `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/destructors.md:274-290` (`r[destructors.scope.temporary.edition2024]`), `src/expressions/operator-expr.md`, `src/attributes/codegen.md`.

### Preserved Support Artifacts & Recorded Runs

All executable evidence, captured outputs, and mechanized proofs are preserved inside this package's `support/` directory:

- `support/probe_try_trait_v2_yeet_and_track_caller.py`: Standalone Python 3.10+ harness executing all four suites (`probe1` `#[track_caller]` matrix across `dev`, `release`, and `cargo miri run` with `MIRIFLAGS="-Zmiri-tree-borrows"`; `probe2` 10-case scope/inference/conversion/`Infallible`/`const` matrix; `probe3` Edition `2021` vs. `2024` drop-order and `RefCell` borrow-check suite for both homogeneous and heterogeneous `try` blocks; `probe4` `-Z dump-mir` `PostCleanup` vs. `Optimized` comparison and `-O2 --emit=llvm-ir` extraction).
- `support/probe_rustc_1_98_0_nightly_output.json`: Live execution transcript captured `2026-11-22` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, `miri 0.1.0 (14210df0e2 2026-05-31)`, host `x86_64-unknown-linux-gnu` (all 4 suites exit `0`).
- `support/rustc_1_102_0_nightly_llvm23_baseline.json`: Execution baseline captured on `rustc 1.102.0-nightly (6905905bb 2026-11-19)`, LLVM `23.1.6`, `miri 0.1.0 (6905905bb7 2026-11-19)`, host `x86_64-unknown-linux-gnu`, recording `From<!>` diagnostic shift, `result.rs:2206` Bug 2 locus, and LLVM `23.1.6` IR with `nofree` + `initializes((0, 4), (8, 16))`.
- `support/TryTraitResidualCallerAndDropSoundness.lean`: `631`-line kernel-checked Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization verified `2026-11-22` with exit `0`, `314` declarations, `0` `._unsafe_rec`, `0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, and axioms subset of `[propext]`.

## Revalidation

To revalidate every finding cheaply against a newer `rustc` nightly, `joshlf/anneal` commit, or Lean release:

1. **Rerun the end-to-end `rustc` / MIR / LLVM / Miri probe** (checks both `#[track_caller]` bugs, all three `TryBlockScope` type-inference/conversion rules, `Infallible = !` identity and `E0277`, `const_trait_impl` / `const` `do yeet` gates, Edition `2021` vs. `2024` tail drop scopes, and `PostCleanup` -> `Optimized` MIR & LLVM IR lowering in ~15 seconds):
   ```console
   python3 support/probe_try_trait_v2_yeet_and_track_caller.py --out /tmp/try_trait_reval.json
   ```
   - **Bug 1 fixed signal:** `homo_custom_qmark` flips from `in_user=false` (`try_trait.rs:384`) to `in_user=true exact_line=true`.
   - **Bug 2 fixed signal:** `fn_result_yeet`, `homo_result_yeet`, and `hetero_result_yeet` flip from `in_user=false` (`result.rs:2206` / `2204`) to `in_user=true exact_line=true`.
   - **Blanket `From<!>` added signal:** `infallible_alias_never_no_blanket_from` flips from `compile_rc: 1` (`E0277`) to `compile_rc: 0`.
   - **`const` `do yeet` enabled signal:** `const_yeet_rejected_non_const_from_yeet` flips from `compile_rc: 1` (`E0015`) to `compile_rc: 0`.
   - **`try bikeshed` syntax renamed signal:** `probe1` and `probe2` `hetero_*` cases fail parsing, requiring inspection of `compiler/rustc_parse/src/parser/expr.rs` (`parse_try_block`).
2. **Diff narrow upstream source anchors:** Inspect `library/core/src/ops/try_trait.rs` (`from_yeet`, `residual_into_try_type`), `library/core/src/result.rs` (`FromResidual<ops::Yeet<E>>`), `compiler/rustc_ast_lowering/src/expr.rs` (`lower_expr_try_block`, `lower_expr_try`, `lower_expr_yeet`), and `compiler/rustc_hir_analysis/src/check/region.rs` (`resolve_block`).
3. **Re-verify the Lean `v4.34.1` kernel proofs and axiom purity:**
   ```console
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/TryTraitResidualCallerAndDropSoundness.lean
   ```
4. **Re-check Anneal's TCB admission status:** Inspect `StatementKind` and `TerminatorKind` in `joshlf/anneal`'s `trusted/lean/Trusted/MirAst.lean` and `evalTerminator` in `trusted/lean/Trusted/MirSemantics.lean` to check whether `TerminatorKind.call`, `TerminatorKind::Drop`, `SetDiscriminant`, `BackwardIncompatibleDropHint`, or `SourceScope.inlined` caller-location tracking have been admitted.
