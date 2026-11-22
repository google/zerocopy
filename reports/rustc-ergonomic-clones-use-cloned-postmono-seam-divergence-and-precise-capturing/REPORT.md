# `rustc` `ergonomic_clones` (`UseCloned` / `CallSource::Use`) Post-Monomorphization Seam Divergence and Edition 2024 `use<...>` Precise Capturing

## Summary

Enabling `#![feature(ergonomic_clones)]` introduces an unconditional, optimization-level-independent operational divergence in **100% safe (`#![forbid(unsafe_code)]`) Rust** between `Runtime(PostCleanup)` / `optimized_mir` MIR semantics (executed by Miri under both Stacked Borrows and Tree Borrows, and targeted by MIR-level verifiers) and native code generation (`rustc_codegen_ssa::mir::codegen_mir`):

1. **Unconditional post-monomorphization `Clone::clone` elision in safe Rust (`(107, 7)` vs. `(7, 7)`):** `core::clone::UseCloned` is a **safe** marker trait (`pub trait UseCloned: Clone {}`), and `Copy` is likewise a **safe** trait whose `Clone::clone` implementation is not constrained by the type system to perform a pure bitwise copy. In a generic function `fn generic_dup<T: UseCloned>(x: T) -> (T, T) { (x.use, x) }` (or equivalently with a `use ||` closure capture `let f = use || x; (f(), x)`), `T` is not statically known to implement `Copy` during MIR construction, so `rustc_mir_build` lowers `x.use` to `TerminatorKind::Call { func: <T as Clone>::clone, call_source: CallSource::Use, unwind: UnwindAction::Unreachable, .. }`. Both `rustc_const_eval` (Miri) and `vendor/lean-miri` ignore `call_source` (`call_source: _`) and execute `<SneakyCopy as Clone>::clone`, returning `(107, 7)` with `CLONE_CALLS = 1`. Conversely, `rustc_codegen_ssa::mir::optimize_use_clone` runs **post-monomorphization inside `codegen_mir` even at `-C opt-level=0 -Z mir-opt-level=0`**, matches `call_source: CallSource::Use`, sees that the monomorphized inner type `SneakyCopy` implements `Copy`, and rewrites the `Call` terminator into `Rvalue::Use(Operand::Copy(*arg_place), WithRetag::Yes)` + `TerminatorKind::Goto`, emitting zero calls to `Clone::clone` in LLVM IR and returning `(7, 7)` with `CLONE_CALLS = 0`.
2. **Documentation-vs.-implementation contradiction on `CallSource`:** `compiler/rustc_middle/src/mir/syntax.rs` documents `pub enum CallSource` as *"Used only for diagnostics"*, yet `rustc_codegen_ssa::mir::optimize_use_clone` uses `CallSource::Use` as an operationally load-bearing rewrite trigger, directly invalidating any verifier assumption that `CallSource` is non-semantic metadata.
3. **Secondary safe-code `UnwindAction::Unreachable` UB hazard on `CallSource::Use`:** `rustc_mir_build::builder::expr::into` hardcodes `unwind: UnwindAction::Unreachable` on every `CallSource::Use` call terminator. In `#![forbid(unsafe_code)]`, a panicking `Clone::clone` inside `x.use` triggers immediate Miri Undefined Behavior (`error: Undefined Behavior: unwinding past a stack frame that does not allow unwinding`) for both `PanicCopy: Copy + UseCloned` and `PanicNonCopy: !Copy + UseCloned`, whereas native `-C opt-level=0` and `-O` binaries completely suppress the panic and return `OK=(7,7)` for `PanicCopy` (via `optimize_use_clone`) and execute an unwinding `call` caught by `catch_unwind` (`CAUGHT_PANIC`) for `PanicNonCopy`.
4. **Soundness condition and verified seam envelope (mechanized in Lean `v4.34.1`):** In `support/UseClonedPostMonoSeamSoundness.lean` (`0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`), we prove that:
   - `optimize_use_clone` refines `Runtime(PostCleanup)` MIR on `Copy ∩ UseCloned` types **if and only if** the type satisfies `PureBitwiseClone` (`optimize_use_clone_refines_postcleanup_iff_pure_bitwise_clone`), generalizing to arbitrary multi-block CFGs (`optimize_use_clone_preserves_cfg`);
   - A relational nondeterministic `PostCleanup` seam permitting either the `Clone::clone` call or bitwise-copy elision on `CallSource::Use` provably envelops **both** Miri and native `rustc_codegen_ssa` across arbitrary multi-block CFGs and unlawful or panicking `Clone` implementations (`nondet_call_source_use_envelops_both_miri_and_codegen`);
   - `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` currently drops `call_source` in `Trusted.MirAst.TerminatorKind.call` (which presently fails closed with `.fault .unsupported`), establishing a concrete forward-compatibility obligation before interprocedural call semantics are admitted.
5. **Edition 2024 `use<...>` precise capturing, variance, and diagnostic taxonomy (`E0597`, uncoded `ParamNotCaptured`, `E0792`):** In Edition 2024, return-position `impl Trait` (RPIT) without an explicit `use<...>` bound captures **all** in-scope lifetime parameters (`opaque_captures_all_in_scope_lifetimes`), causing previously accepted Edition 2021 code to fail with `E0597`. Adding `+ use<...>` opts out of unmentioned lifetimes (giving them `ty::Bivariant` variance while every explicitly captured parameter is asserted `ty::Invariant`), but `check_opaque_precise_captures` currently requires **all** in-scope type and const parameters to appear in `use<...>` (emitting the **uncoded** `ParamNotCaptured` error, distinct from **`E0792`** `NonGenericOpaqueTypeParam`, which enforces generic-parameter injectivity at opaque defining sites such as TAIT `Opaque<u32>`). Both the variance-and-completeness biconditional (`precise_capture_well_formed_iff_all_ty_params_retained`) and the hidden-type substitution counterexample (`ce2_omitted_ty_param_in_use_breaks_hidden_type_subst_e0792`) are kernel-checked in Lean `v4.34.1`.

## Applicability

This report characterizes four concrete, immutable upstream subjects and their formal and operational interactions:

| Subject | Exact Identity | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (executed toolchain) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly 2026-05-31`, `miri 0.1.0`, LLVM `22.1.6`) | Primary source audit **and** live execution target for all native (`-C opt-level=0 -Z mir-opt-level=0`, `-C opt-level=0`, `-O`), MIR/LLVM-IR dump, Miri Stacked Borrows, Miri Tree Borrows, and Edition 2021/2024 diagnostic probes (`support/probe_ergonomic_clones_seam_and_use_captures.py`, `support/probe_results.json`). |
| `rust-lang/rust` (upstream `main` snapshot) | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`) | Primary source re-audit verifying whether every `ergonomic_clones`, `CallSource::Use`, `optimize_use_clone`, `unwind: UnwindAction::Unreachable`, and `check_opaque_precise_captures` mechanism persisted unchanged across ~6 months of compiler development. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Primary source audit of `Trusted.MirAst`, `Trusted.MirSemantics`, `Trusted.Correspondence`, `trusted/rustc-capture`, and `vendor/lean-miri` to evaluate concrete impact on an existing `Runtime(PostCleanup)` MIR verification boundary. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel verification engine for `support/UseClonedPostMonoSeamSoundness.lean` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. |

### Version-Specific Differences Between the Two `rust-lang/rust` Snapshots

Direct diff inspection between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`) establishes that **every behavioral mechanism documented in this report is identical across both revisions**, with only minor internal API/line-number shifts:

- **`library/core/src/clone.rs`:** `pub trait UseCloned: Clone {}` moved from line `410` to line `427` (following insertion of `#[unstable(feature = "share_trait")] pub trait Share: Clone`), still gated by `#[unstable(feature = "ergonomic_clones", issue = "132290")]`, still a safe trait, and still carrying identical documentation guidelines.
- **`compiler/rustc_middle/src/mir/syntax.rs`:** `pub enum CallSource` moved from line `633` to line `626`; its doc comment *"Used only for diagnostics."* moved from line `630` to line `623`, and `CallSource::Use` remains verbatim.
- **`compiler/rustc_mir_build/src/builder/expr/into.rs`:** `ExprKind::ByUse` lowering moved from lines `513–563` to lines `526–577` (and `ExprKind::Use` was renamed `ExprKind::ValueExpr`); the three-way `Copy` / `UseCloned` / move dispatch, `call_source: CallSource::Use`, and `unwind: UnwindAction::Unreachable` (line `548` -> `562`) are unchanged.
- **`compiler/rustc_codegen_ssa/src/mir/mod.rs`:** `codegen_mir`'s `if tcx.features().ergonomic_clones()` hook moved from lines `217–224` to lines `221–228` (switching `ty::TypingEnv::fully_monomorphized()` to `cx.typing_env()` and `EarlyBinder::bind(mir.clone())` to `EarlyBinder::bind(tcx, mir.clone())`); `optimize_use_clone` moved from lines `352–407` to lines `390–445` (switching `TerminatorKind::Goto { target }` to `TerminatorKind::goto(destination_block)`). Its unconditional execution regardless of `-C opt-level`, its `CallSource::Use` filter, its `type_is_copy_modulo_regions` check, and its `Operand::Copy(*arg_place)` + `Goto` rewrite are completely unchanged.
- **`compiler/rustc_const_eval/src/interpret/step.rs` & `eval_context.rs`:** `call_source: _` moved from line `549` to `595`; `mir::UnwindAction::Unreachable => throw_ub_format!(...)` moved from line `559` to `547`.
- **`compiler/rustc_hir_analysis/src/check/check.rs` & diagnostics module:** `check_opaque_precise_captures` moved from line `572` to `573`; the `errors` module was renamed `diagnostics` (`compiler/rustc_hir_analysis/src/errors/precise_captures.rs` -> `compiler/rustc_hir_analysis/src/diagnostics/precise_captures.rs`), with all diagnostic structs (`ParamNotCaptured`, `SelfTyNotCaptured`, `LifetimeNotCaptured`, `LifetimeImplicitlyCaptured`, `BadPreciseCapture`, `PreciseCaptureSelfAlias`, `DuplicatePreciseCapture`, `LifetimesMustBeFirst`) identical line-for-line (lines `1–89`).

### Feature-Gate, Edition, and Backend Scope

- **Ergonomic-clone findings (Findings §1–§3)** apply specifically to crates enabling the incomplete unstable nightly feature `#![feature(ergonomic_clones)]` (tracking issue `rust-lang/rust#132290`), compiling via any `rustc_codegen_ssa`-based backend (verified empirically on LLVM `22.1.6` for `x86_64-unknown-linux-gnu`; applies structurally to any backend sharing `rustc_codegen_ssa::mir::codegen_mir`, such as `rustc_codegen_llvm` and `rustc_codegen_gcc`, as argued by source inspection, while `rustc_codegen_cranelift` does not use `rustc_codegen_ssa::mir::codegen_mir` and is recorded as *not examined* in **Boundaries**).
- **Edition 2024 `use<...>` precise capturing findings (Findings §4)** apply to **stable Rust syntax** (`use<...>` precise capturing stabilized in Rust 1.82 and default RPIT lifetime capture enabled in Edition 2024) on `rustc 1.98.0-nightly` (`14210df0e2`) and upstream `main` (`342d74463a`). The `E0792` comparison probe uses `#![feature(type_alias_impl_trait)]` to trigger `NonGenericOpaqueTypeParam` directly.
- **Anneal trusted-boundary findings (Findings §6)** apply to `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` and, by derivation, to any formal verifier whose extraction seam sits at `Runtime(PostCleanup)` or `optimized_mir` prior to `rustc_codegen_ssa::mir::codegen_mir`.

## Findings

### 1. Upstream `ergonomic_clones` Pipeline: Safe Traits, Polymorphic Lowering, and Post-Monomorphization Elision

Basis: source + documentation

The `ergonomic_clones` feature (`#![feature(ergonomic_clones)]`, `rust-lang/rust#132290`) introduces postfix `expr.use` expressions and `use ||` closure capture clauses backed by the `#[lang = "use_cloned"]` trait `core::clone::UseCloned`. Tracing a single `x.use` or `use || x` expression from HIR typechecking through THIR, MIR construction, MIR optimization, Miri interpretation, and SSA codegen exposes the exact mechanism of the seam divergence.

#### 1.1 `core::clone::UseCloned` Is a Safe Trait Without a Compiler-Enforced Bitwise-Copy Contract

In `library/core/src/clone.rs` (lines `380–428` at `14210df0e2`; lines `394–445` at `342d74463a`), `UseCloned` is declared as an ordinary safe marker subtrait of `Clone`:

```rust
/// Trait for objects whose [`Clone`] impl is lightweight (e.g. reference-counted)
///
/// Cloning an object implementing this trait should in general:
/// - be O(1) (constant) time regardless of the amount of data managed by the object,
/// - not require a memory allocation,
/// - not require copying more than roughly 64 bytes (a typical cache line size),
/// - not block the current thread,
/// - not have any semantic side effects (e.g. allocating a file descriptor), and
/// - not have overhead larger than a couple of atomic operations.
#[unstable(feature = "ergonomic_clones", issue = "132290")]
#[lang = "use_cloned"]
pub trait UseCloned: Clone {
    // Empty.
}
```

Primitive scalar types (`usize`, `u8..u128`, `isize`, `i8..i128`, `f16..f128`, `bool`, `char`) implement `UseCloned` via `impl_use_cloned!`, and `alloc::rc::{Rc, Weak}` (`library/alloc/src/rc.rs:2522, 3713` at `14210df0e2`) and `alloc::sync::{Arc, Weak}` (`library/alloc/src/sync.rs:2433, 3444` at `14210df0e2`) implement `UseCloned`. Crucially:

- Neither `Copy` nor `UseCloned` is an `unsafe trait`.
- The prose guideline *"not have any semantic side effects"* is purely informative documentation, not a soundness contract enforced by the compiler or borrow checker.
- In `#![forbid(unsafe_code)]`, any user type `SneakyCopy` may simultaneously derive `Copy`, implement `UseCloned`, and provide an arbitrary custom `impl Clone for SneakyCopy` that mutates global atomic state, returns a modified payload (`SneakyCopy(self.0 + 100)`), or panics.

#### 1.2 HIR Typecheck & THIR Lowering: Three-Way `Copy` / `UseCloned` / Move Classification

1. **ExprUseVisitor (`compiler/rustc_hir_typeck/src/expr_use_visitor.rs:335–349` at `14210df0e2`; `334–348` at `342d74463a`):**
   `consume_clone_or_copy` classifies every `x.use` and `use ||` upvar capture in three ordered branches:
   ```rust
   if self.cx.type_is_copy_modulo_regions(place_with_id.place.ty()) {
       self.delegate.borrow_mut().copy(place_with_id, diag_expr_id);
   } else if self.cx.type_is_use_cloned_modulo_regions(place_with_id.place.ty()) {
       self.delegate.borrow_mut().use_cloned(place_with_id, diag_expr_id);
   } else {
       self.delegate.borrow_mut().consume(place_with_id, diag_expr_id);
   }
   ```
   For `use ||` closures, `typeck_upvar` (`compiler/rustc_hir_typeck/src/upvar.rs:2140–2155` at `14210df0e2`) records `ty::UpvarCapture::ByUse`.
2. **THIR construction (`compiler/rustc_mir_build/src/thir/cx/expr.rs:442–444, 1401–1411` at `14210df0e2`):**
   Both `hir::ExprKind::Use(expr, span)` (postfix `x.use`) and `ty::UpvarCapture::ByUse` (`use ||` closure capture in `capture_upvar`) lower to the exact same THIR node: `thir::ExprKind::ByUse { expr, span }`.
3. **MIR construction (`compiler/rustc_mir_build/src/builder/expr/into.rs:513–563` at `14210df0e2`; `526–577` at `342d74463a`):**
   Because `Category::of(ExprKind::ByUse)` is `Category::Rvalue(RvalueFunc::Into)` (`compiler/rustc_mir_build/src/builder/expr/category.rs:59`), `expr_into_dest` lowers `ExprKind::ByUse` using the **polymorphic** typing environment (`this.param_env`):
   ```rust
   if this.tcx.type_is_copy_modulo_regions(this.infcx.typing_env(this.param_env), ty) {
       this.cfg.push_assign(
           block, source_info, destination,
           Rvalue::Use(Operand::Copy(place), WithRetag::Yes),
       );
       block.unit()
   } else if this.infcx.type_is_use_cloned_modulo_regions(this.param_env, ty) {
       // Convert `expr.use` to a call like `Clone::clone(&expr)`
       let success = this.cfg.start_new_block();
       let clone_trait = this.tcx.require_lang_item(LangItem::Clone, span);
       let clone_fn = this.tcx.associated_item_def_ids(clone_trait)[0];
       let func = Operand::function_handle(this.tcx, clone_fn, [ty.into()], expr_span);
       ...
       this.cfg.terminate(
           block, source_info,
           TerminatorKind::Call {
               func,
               args: [Spanned { node: Operand::Move(ref_place), span: DUMMY_SP }].into(),
               destination,
               target: Some(success),
               unwind: UnwindAction::Unreachable,
               call_source: CallSource::Use,
               fn_span: expr_span,
           },
       );
       success.unit()
   } else {
       this.cfg.push_assign(
           block, source_info, destination,
           Rvalue::Use(Operand::Move(place), WithRetag::Yes),
       );
       block.unit()
   }
   ```

This produces a fundamental **monomorphic vs. polymorphic asymmetry** already at MIR construction:

- In a **monomorphic** function `fn concrete_dup(x: SneakyCopy) -> (SneakyCopy, SneakyCopy) { (x.use, x) }`, `type_is_copy_modulo_regions` is `true` during MIR build, so `x.use` lowers directly to `Rvalue::Use(Operand::Copy(_1))`. Neither Miri nor native binaries ever call `SneakyCopy::clone`.
- In a **polymorphic** function `fn generic_dup<T: UseCloned>(x: T) -> (T, T) { (x.use, x) }`, `param_env` contains `T: UseCloned` but **not** `T: Copy`. Thus `type_is_copy_modulo_regions` is `false`, `type_is_use_cloned_modulo_regions` is `true`, and `rustc_mir_build` emits `TerminatorKind::Call { func: <T as Clone>::clone, call_source: CallSource::Use, unwind: UnwindAction::Unreachable }`.
- In a type implementing neither `Copy` nor `UseCloned` (such as `String`), `x.use` takes the `else` branch and emits `Operand::Move(place)`, causing subsequent use of `x` to fail borrow checking with `E0382`.

#### 1.3 `CallSource` Documentation Contradiction and Post-Mono `optimize_use_clone`

In `compiler/rustc_middle/src/mir/syntax.rs` (`629–649` at `14210df0e2`; `622–642` at `342d74463a`), `CallSource` carries an explicit doc comment claiming zero operational significance:

```rust
/// Represents how a [`TerminatorKind::Call`] was constructed.
/// Used only for diagnostics.
pub enum CallSource {
    OverloadedOperator,
    MatchCmp,
    Misc,
    /// Use of value, generating a clone function call
    Use,
    Normal,
}
```

All pre-codegen MIR phases (`MirPhase::Analysis`, `MirPhase::Runtime(RuntimePhase::Initial)`, `MirPhase::Runtime(RuntimePhase::PostCleanup)` produced by `run_analysis_to_runtime_passes` in `compiler/rustc_mir_transform/src/lib.rs:572–602`, and `optimized_mir` at lines `776–821`) preserve `TerminatorKind::Call { call_source: CallSource::Use, .. }` unchanged because `T` is still polymorphic prior to monomorphization.

Both Miri and `rustc_const_eval` obtain MIR via `Machine::load_mir` -> `ecx.tcx.instance_mir(instance)` (`compiler/rustc_const_eval/src/interpret/machine.rs:197–202`; `src/tools/miri/src/machine.rs:1278–1279`) and execute `TerminatorKind::Call` in `InterpCx::eval_terminator` (`compiler/rustc_const_eval/src/interpret/step.rs:543–567` at `14210df0e2`; `589–613` at `342d74463a`) while **completely discarding `call_source`**:

```rust
Call {
    ref func,
    ref args,
    destination,
    target,
    unwind,
    call_source: _,
    fn_span: _,
} => { ... }
```

By stark contrast, `rustc_codegen_ssa::mir::codegen_mir` (`compiler/rustc_codegen_ssa/src/mir/mod.rs:209–224, 352–407` at `14210df0e2`; `211–228, 390–445` at `342d74463a`) invokes `optimize_use_clone` **after monomorphizing the MIR body and unconditionally whenever `tcx.features().ergonomic_clones()` is active** — immediately after a comment warning against arbitrary post-`deduce_param_attrs` MIR transforms:

```rust
let mut mir = tcx.instance_mir(instance.def);
// Note that the ABI logic has deduced facts about the functions' parameters based on the MIR we
// got here (`deduce_param_attrs`). That means we can *not* apply arbitrary further MIR
// transforms as that may invalidate those deduced facts!
...
if tcx.features().ergonomic_clones() {
    let monomorphized_mir = instance.instantiate_mir_and_normalize_erasing_regions(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(mir.clone()),
    );
    mir = tcx.arena.alloc(optimize_use_clone::<Bx>(cx, monomorphized_mir));
}
```

Inside `optimize_use_clone`:

```rust
/// Replace `clone` calls that come from `use` statements with direct copies if possible.
// FIXME: Move this function to mir::transform when post-mono MIR passes land.
fn optimize_use_clone<'a, 'tcx, Bx: BuilderMethods<'a, 'tcx>>(
    cx: &'a Bx::CodegenCx,
    mut mir: Body<'tcx>,
) -> Body<'tcx> {
    let tcx = cx.tcx();

    if tcx.features().ergonomic_clones() {
        for bb in mir.basic_blocks.as_mut() {
            let mir::TerminatorKind::Call {
                args, destination, target,
                call_source: mir::CallSource::Use, ..
            } = &bb.terminator().kind else { continue; };

            assert_eq!(args.len(), 1);
            let arg = &args[0];
            let arg_ty = arg.node.ty(&mir.local_decls, tcx);
            let ty::Ref(_region, inner_ty, mir::Mutability::Not) = *arg_ty.kind() else { continue };
            if !tcx.type_is_copy_modulo_regions(cx.typing_env(), inner_ty) {
                continue;
            }
            let Some(arg_place) = arg.node.place() else { continue };
            let destination_block = target.unwrap();

            bb.statements.push(mir::Statement::new(
                bb.terminator().source_info,
                mir::StatementKind::Assign(Box::new((
                    *destination,
                    mir::Rvalue::Use(
                        mir::Operand::Copy(
                            arg_place.project_deeper(&[mir::ProjectionElem::Deref], tcx),
                        ),
                        mir::WithRetag::Yes,
                    ),
                ))),
            ));

            bb.terminator_mut().kind = mir::TerminatorKind::Goto { target: destination_block };
        }
    }
    mir
}
```

Four implementation properties of `optimize_use_clone` are directly load-bearing for verification:

1. **No optimization-level gate:** `optimize_use_clone` does not inspect `-C opt-level` or `-Z mir-opt-level`. It executes identically at `-C opt-level=0 -Z mir-opt-level=0`, `-C opt-level=0`, and `-O`.
2. **Post-`optimized_mir` placement:** Because it executes inside `rustc_codegen_ssa::mir::codegen_mir`, `--emit=mir` and any MIR consumer reading `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`) or `optimized_mir` (`Runtime(Optimized)`) **never observe the rewrite**.
3. **No `func` DefId check:** The pass matches solely on `call_source: CallSource::Use`, `args.len() == 1`, `arg_ty == &inner_ty`, and `type_is_copy_modulo_regions(inner_ty)`; it never checks `func` (relying on the invariant that only `ExprKind::ByUse` sets `CallSource::Use`).
4. **Silent `unwind` edge erasure:** Replacing `TerminatorKind::Call { unwind: UnwindAction::Unreachable, .. }` with `StatementKind::Assign` + `TerminatorKind::Goto` removes not only the call's return value and side effects, but also its panic/unwind behavior.

---

### 2. Empirical Execution Matrix: Native Codegen vs. Miri (Stacked & Tree Borrows)

Basis: execution (`support/probe_ergonomic_clones_seam_and_use_captures.py`, `support/probe_results.json`)

All empirical executions were collected live on `x86_64-unknown-linux-gnu` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` with `#![forbid(unsafe_code)]`.

#### 2.1 Part A: Live Safe-Code Divergence on `x.use` and `use ||`

The probe defines `SneakyCopy(u32)` implementing `Copy`, `UseCloned`, and a custom `Clone` that increments `CLONE_CALLS: AtomicUsize` by `1` and returns `SneakyCopy(self.0 + 100)`. `CLONE_CALLS` is explicitly reset to `0` prior to each sub-test (`generic_dup`, `generic_closure_dup`, `concrete_dup`, `concrete_closure_dup`) so every counter reading measures that isolated invocation:

| Execution Configuration | `generic_dup` (`x.use`) | `CALLS_G` | `generic_closure_dup` (`use \|\|`) | `CALLS_GC` | `concrete_dup` (`x.use`) | `CALLS_C` | `concrete_closure_dup` (`use \|\|`) | `CALLS_CC` | `Rc` (`RC_OUT`, `RC_CNT`) | `String` (`MOVED_LEN`) |
| :--- | :--- | :---: | :--- | :---: | :--- | :---: | :--- | :---: | :---: | :---: |
| Native `-C opt-level=0 -Z mir-opt-level=0` | **`(7, 7)`** | **`0`** | **`(7, 7)`** | **`0`** | `(7, 7)` | `0` | `(7, 7)` | `0` | `(43, 3)` | `5` |
| Native `-C opt-level=0` | **`(7, 7)`** | **`0`** | **`(7, 7)`** | **`0`** | `(7, 7)` | `0` | `(7, 7)` | `0` | `(43, 3)` | `5` |
| Native `-O` | **`(7, 7)`** | **`0`** | **`(7, 7)`** | **`0`** | `(7, 7)` | `0` | `(7, 7)` | `0` | `(43, 3)` | `5` |
| Miri Stacked Borrows (default) | **`(107, 7)`** | **`1`** | **`(107, 7)`** | **`1`** | `(7, 7)` | `0` | `(7, 7)` | `0` | `(43, 3)` | `5` |
| Miri Tree Borrows (`-Zmiri-tree-borrows`) | **`(107, 7)`** | **`1`** | **`(107, 7)`** | **`1`** | `(7, 7)` | `0` | `(7, 7)` | `0` | `(43, 3)` | `5` |

Key empirical observations:
- **Both `x.use` and `use ||` diverge identically:** `generic_dup` and `generic_closure_dup` both produce `(107, 7)` with `1` clone call under both Miri aliasing models, and `(7, 7)` with `0` clone calls across all three native optimization levels (including `-C opt-level=0 -Z mir-opt-level=0`).
- **Concrete `Copy` sites agree (`(7, 7)`, `0` calls):** `concrete_dup` and `concrete_closure_dup` lower directly to `copy _1` during MIR construction, never emitting `CallSource::Use`.
- **Non-`Copy` `UseCloned` (`Rc<u32>`) agrees (`RC_OUT=43, RC_CNT=3`):** Because `Rc<u32>` is not `Copy`, `optimize_use_clone` skips it, and both Miri and native binaries call `Rc::clone` twice (once for `rc.use`, once for `use || *rc + 1`), producing strong count `3`.

#### 2.2 Direct MIR vs. LLVM IR Evidence at `-C opt-level=0 -Z mir-opt-level=0`

Dumping `--emit=mir` and `--emit=llvm-ir` from the exact same `-C opt-level=0 -Z mir-opt-level=0` compilation confirms the seam split directly in the compiler's own IR artifacts (`support/probe_results.json`, `part_a_ergonomic_clones_native_vs_miri_divergence`):

- **Emitted MIR (`generic_dup`):**
  ```text
  bb0: {
      StorageLive(_2);
      _3 = &_1;
      _2 = <T as Clone>::clone(move _3) -> [return: bb1, unwind unreachable];
  }
  bb1: {
      StorageLive(_4);
      _4 = move _1;
      _0 = (move _2, move _4);
      ...
      return;
  }
  ```
- **Emitted LLVM IR (`generic_dup::<SneakyCopy>` at `-C opt-level=0 -Z mir-opt-level=0`):**
  ```llvm
  define internal { i32, i32 } @_RINv...11generic_dupNtB2_10SneakyCopyEB2_(i32 %0) unnamed_addr #0 {
  start:
    %x = alloca [4 x i8], align 4
    store i32 %0, ptr %x, align 4
    %_2 = load i32, ptr %x, align 4
    %_4 = load i32, ptr %x, align 4
    %1 = insertvalue { i32, i32 } poison, i32 %_2, 0
    %2 = insertvalue { i32, i32 } %1, i32 %_4, 1
    ret { i32, i32 } %2
  }
  ```
  Notice `llvm_ir_generic_dup_calls_clone = false` and `llvm_ir_generic_closure_dup_calls_clone = false`: even with **both** LLVM and MIR optimizations explicitly disabled, `<SneakyCopy as Clone>::clone` is never emitted into LLVM IR at all.

---

### 3. Secondary Safe-Code Soundness Hazard: `unwind: UnwindAction::Unreachable` on `CallSource::Use`

Basis: source + execution (`support/probe_results.json`, `part_b_call_source_use_unwind_unreachable_hazard`)

Source inspection of `compiler/rustc_mir_build/src/builder/expr/into.rs:548` (`562` at `342d74463a`) revealed a second, independent bug in `ergonomic_clones`: `rustc_mir_build` constructs the `Clone::clone` call terminator with **`unwind: UnwindAction::Unreachable`** instead of `UnwindAction::Continue` (or a cleanup edge). In `compiler/rustc_const_eval/src/interpret/eval_context.rs:552–561` (`14210df0e2`), `UnwindAction::Unreachable` is defined as **Undefined Behavior** if unwinding reaches that frame:

```rust
mir::UnwindAction::Unreachable => {
    throw_ub_format!("unwinding past a stack frame that does not allow unwinding");
}
```

Testing two `#![forbid(unsafe_code)]` types whose `Clone::clone` invokes `panic!(...)` inside `std::panic::catch_unwind(|| generic_dup(...))` yields the following live matrix:

| Test Case (`#![forbid(unsafe_code)]`) | Native `-C opt-level=0 -Z mir-opt-level=0` | Native `-O` | Miri Stacked Borrows | Miri Tree Borrows |
| :--- | :--- | :--- | :--- | :--- |
| `PanicCopy` (`Copy + UseCloned`, `Clone::clone` panics) | `rc=0`, stdout `OK=(7,7)` (no panic, no UB) | `rc=0`, stdout `OK=(7,7)` | **`rc=1`, UB:** `unwinding past a stack frame that does not allow unwinding` at `(x.use, x)` | **`rc=1`, UB:** `unwinding past a stack frame that does not allow unwinding` at `(x.use, x)` |
| `PanicNonCopy` (`!Copy + UseCloned`, `Clone::clone` panics) | `rc=0`, stdout `CAUGHT_PANIC` (emits plain LLVM `call`, no landing pad, unwinds past frame into caller `catch_unwind`) | `rc=0`, stdout `CAUGHT_PANIC` | **`rc=1`, UB:** `unwinding past a stack frame that does not allow unwinding` at `(x.use, x)` | *(not separately run; identical `eval_context.rs` path)* |

Inspecting the emitted LLVM IR for `PanicNonCopy` (`panic_noncopy_llvm_ir_generic_dup` in `support/probe_results.json`) explains why native execution printed `CAUGHT_PANIC` despite `UnwindAction::Unreachable`:

```llvm
define internal { i32, i32 } @_RINv...11generic_dupNtB2_12PanicNonCopyEB2_(i32 %0) unnamed_addr #0 {
start:
  %x = alloca [4 x i8], align 4
  store i32 %0, ptr %x, align 4
; call <part_b_noncopy_ir::PanicNonCopy as core::clone::Clone>::clone
  %_2 = call i32 @_RNvX...PanicNonCopy...Clone5clone(ptr align 4 %x)
  ...
}
```

Because `generic_dup` has no drop glue of its own on `PanicNonCopy` (`PanicNonCopy(u32)` has no `Drop` impl) and `rustc_codegen_ssa` lowers `Call { unwind: UnwindAction::Unreachable }` as an LLVM `call` (not `invoke` with an `unreachable` landing pad, and without marking the callee `nounwind`), the DWARF unwinder happens to skip `generic_dup` into `catch_unwind` at runtime in this trivial function — **yet** in MIR semantics (`UnwindAction::Unreachable`), unwinding past `generic_dup` is **immediate Undefined Behavior** (caught by Miri on both `PanicCopy` and `PanicNonCopy`), and if `generic_dup` held live drop-requiring locals, `ElaborateDrops` would skip generating cleanup edges for them! For `PanicCopy`, the divergence is maximally acute: Miri aborts with **Undefined Behavior** while native binaries silently succeed with `OK=(7,7)`.

---

### 4. Edition 2024 `use<...>` Precise Capturing, Variance, and Diagnostic Taxonomy

Basis: source + execution (`support/probe_results.json`, `part_c_precise_capturing_and_ergonomic_clone_gates`)

Although superficially sharing the `use` keyword with `ergonomic_clones`, Edition 2024 `impl Trait + use<...>` precise capturing is a **stable** type-system feature governing opaque type generic parameter capture and variance.

#### 4.1 Edition 2021 vs. Edition 2024 Lifetime Capture Rules

In `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs:323–332` (`14210df0e2`; `322–331` at `342d74463a`), `opaque_captures_all_in_scope_lifetimes` encodes the exact capture-default switch:

```rust
fn opaque_captures_all_in_scope_lifetimes<'tcx>(opaque: &'tcx hir::OpaqueTy<'tcx>) -> bool {
    match opaque.origin {
        // if the opaque has the `use<...>` syntax, the user is telling us that they only want
        // to account for those lifetimes, so do not try to be clever.
        _ if opaque.bounds.iter().any(|bound| matches!(bound, hir::GenericBound::Use(..))) => false,
        hir::OpaqueTyOrigin::AsyncFn { .. } | hir::OpaqueTyOrigin::TyAlias { .. } => true,
        _ if opaque.span.at_least_rust_2024() => true,
        hir::OpaqueTyOrigin::FnReturn { in_trait_or_impl, .. } => in_trait_or_impl.is_some(),
    }
}
```

- **Edition 2021 RPIT (free/inherent `fn`, no `use<...>`):** returns `false`, so unmentioned lifetime parameters are **not** captured and receive `ty::Bivariant` variance (`compiler/rustc_hir_analysis/src/variance/mod.rs:155–184`). Calling `rpit_default(&local)` and returning or storing the opaque value past `local`'s drop compiles cleanly (`rc=0`).
- **Edition 2024 RPIT (no `use<...>`):** `opaque.span.at_least_rust_2024()` returns `true`, capturing **every** in-scope lifetime parameter as `ty::Invariant`. Returning or storing `rpit_default(&local)` past `local`'s scope fails with **`E0597`** (`local` does not live long enough), and when stored in a local block emits the Edition 2024 overcapture note (`this call may capture more lifetimes than intended, because Rust 2024 has adjusted the impl Trait lifetime capture rules`) with a machine-applicable `+ use<>` suggestion (`compiler/rustc_trait_selection/src/errors.rs:2027–2048`).
- **Edition 2024 RPIT with `+ use<...>`:** `GenericBound::Use` short-circuits `opaque_captures_all_in_scope_lifetimes` to `false`. Any in-scope lifetime omitted from `use<...>` (and not mentioned in explicit trait/outlives bounds) returns to `ty::Bivariant`.

#### 4.2 Opaque Variance and `check_opaque_precise_captures` Invariants

In `compiler/rustc_hir_analysis/src/variance/mod.rs:102–231` (`14210df0e2`; `97–226` at `342d74463a`):
1. `variance_of_opaque` initializes **every** generic parameter of the opaque (including inherited parent type and const parameters and duplicated captured lifetimes in `own_params`) to **`ty::Invariant`** (line `157`).
2. Parent lifetimes (except trait parameters on RPITITs when `ForceCaptureTraitArgs::Yes`) are then marked **`ty::Bivariant`** (line `177`) unless visited in the opaque's explicit bounds (`OpaqueTypeLifetimeCollector::visit_region`, line `140`).
3. `check_opaque_precise_captures` (`compiler/rustc_hir_analysis/src/check/check.rs:572–729` at `14210df0e2`; `573–730` at `342d74463a`) enforces five strict invariants on every `GenericBound::Use`:
   - **Ordering (`LifetimesMustBeFirst`, lines `599–605`):** All lifetime arguments in `use<...>` must precede non-lifetime (type/const) arguments.
   - **Uniqueness (`DuplicatePreciseCapture`, lines `611–617`):** No parameter may be named twice in `use<...>`.
   - **Invariance assertion (lines `650–656`):** `assert_eq!(variances[param.index as usize], ty::Invariant, "precise captured param should be invariant")`.
   - **Bound-lifetime coverage (`LifetimeNotCaptured` / `LifetimeImplicitlyCaptured`, lines `670–700`):** Every lifetime whose variance is `ty::Invariant` (e.g., mentioned in `+ 'a` or originating from a trait) must be named in `use<...>`.
   - **Complete type/const retention (`ParamNotCaptured` / `SelfTyNotCaptured`, lines `702–726`):** Every in-scope `GenericParamDefKind::Type` and `GenericParamDefKind::Const` parameter **must** be named in `use<...>`.

#### 4.3 Crucial Primary-Source Distinction: Uncoded `ParamNotCaptured` vs. `E0792` (`NonGenericOpaqueTypeParam`)

Direct inspection of `compiler/rustc_hir_analysis/src/errors/precise_captures.rs:5–89` (`14210df0e2`; `diagnostics/precise_captures.rs:5–89` at `342d74463a`) and `compiler/rustc_trait_selection/src/errors.rs:2051–2063` establishes an important diagnostic distinction that is easy to conflate without checking source and live `rustc` stderr:

- Omitting an in-scope type parameter `T` (or const parameter `N`) from `impl Trait + use<...>` emits **`ParamNotCaptured`**, which has **no `E`-code** (`#[diag("`impl Trait` must mention all {$kind} parameters in scope in `use<...>`")]`). In the entire `precise_captures.rs` file, only `PreciseCaptureSelfAlias` carries an error code (`E0799`).
- **`E0792`** (`NonGenericOpaqueTypeParam` in `compiler/rustc_trait_selection/src/errors.rs:2052`: `#[diag("expected generic {$kind} parameter, found `{$arg}`", code = E0792)]`) is emitted by `NonDefiningUseReason::NotAParam` (`compiler/rustc_trait_selection/src/opaque_types.rs:19, 32–41`) when a defining use of an opaque type supplies a **non-generic argument** (such as `Opaque<u32>` for `type Opaque<T> = impl Sized`). Both mechanisms protect the same underlying semantic requirement — **functional hidden-type substitution** (an opaque type's hidden type cannot validly depend on a type parameter that is not generically and injectively represented in the opaque type's identity key) — but they fire in different compiler passes with distinct diagnostics.

#### 4.4 Live 14-Case Diagnostic & Variance Verification Matrix (`support/probe_results.json`)

Every one of the 14 Part C probe cases matched its expected compiler outcome live on `rustc 1.98.0-nightly (14210df0e 2026-05-31)`:

| Probe Case | Edition | Exit Code | Observed Diagnostic / Behavior |
| :--- | :---: | :---: | :--- |
| `edition2021_rpit_omits_unmentioned_lifetime_by_default` | 2021 | `0` | Compiles cleanly; unmentioned `'a` is bivariant (not captured). |
| `edition2024_rpit_captures_lifetime_by_default_e0597` | 2024 | `1` | `error[E0597]`: `local` does not live long enough; requires `'static`. |
| `edition2024_rpit_overcapture_note_in_local_block_e0597` | 2024 | `1` | `error[E0597]` + Edition 2024 overcapture note + help `+ use<>`. |
| `edition2024_rpit_use_empty_opts_out_of_lifetime_capture` | 2024 | `0` | Compiles cleanly; `+ use<>` restores uncaptured bivariant `'a`. |
| `non_use_cloned_string_moved_by_dot_use_e0382` | 2024 | `1` | `error[E0382]`: use of moved value `s` (`String` is neither `Copy` nor `UseCloned`). |
| `rpit_use_omitting_in_scope_type_param_rejected` | 2024 | `1` | Uncoded `ParamNotCaptured`: `` `impl Trait` must mention all type parameters in scope in `use<...>` ``. |
| `rpit_use_omitting_in_scope_const_param_rejected` | 2024 | `1` | Uncoded `ParamNotCaptured`: `` `impl Trait` must mention all const parameters in scope in `use<...>` ``. |
| `rpit_use_retaining_all_ty_params_and_omitting_lifetime_accepted` | 2024 | `0` | Compiles cleanly; `+ use<T>` drops `'a` while retaining `T`. |
| `rpit_use_captures_lifetime_invariantly_rejected` | 2024 | `1` | Unconfounded (`fn mk<'a>() -> impl Sized + use<'a> where 'a: 'a`): `mk::<'static>()` vs. `mk::<'a>()` fails (`assignment requires that 'a must outlive 'static`), proving `ty::Invariant`. |
| `rpit_use_omitted_lifetime_is_bivariant_accepted` | 2024 | `0` | Exact paired control (`fn mk<'a>() -> impl Sized + use<> where 'a: 'a`): `mk::<'static>()` and `mk::<'a>()` unify cleanly, proving `ty::Bivariant`. |
| `rpit_use_lifetimes_must_be_first_rejected` | 2024 | `1` | Uncoded `LifetimesMustBeFirst`: ``lifetime parameter `'a` must be listed before non-lifetime parameters``. |
| `rpit_use_duplicate_param_rejected` | 2024 | `1` | Uncoded `DuplicatePreciseCapture`: ``cannot capture parameter `'a` twice``. |
| `rpit_use_omitting_bound_mentioned_lifetime_rejected` | 2024 | `1` | Uncoded `LifetimeNotCaptured`: `` `impl Trait` captures lifetime parameter, but it is not mentioned in `use<...>` precise captures list ``. |
| `tait_non_generic_param_rejected_e0792` | 2024 | `1` | `error[E0792]`: ``expected generic type parameter, found `u32` `` (TAIT `Opaque<u32>`). |

---

### 5. Kernel-Checked Lean `v4.34.1` Mechanization (`support/UseClonedPostMonoSeamSoundness.lean`)

Basis: source + execution (Lean `v4.34.1` kernel check) + derived

To eliminate informal reasoning about the MIR-to-codegen seam and precise capturing invariants, `support/UseClonedPostMonoSeamSoundness.lean` (1,130 lines, 51,543 bytes) formalizes both subsystems in standalone Lean `v4.34.1` under strict kernel hygiene (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`):

- **Zero forbidden constructs:** `0` `sorry` / `sorryAx`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`, `0` `partial def`, and `0` `._unsafe_rec` across all **750** generated environment constants.
- **Noncomputable recursive definitions & manual `DecidableEq`:** Every recursive definition over `List`, `MirBody`, and the recursive type AST `TyExpr` is declared `noncomputable def`, and `decEqTyTag` / `decEqTyExpr` / `decEqTyExprList` are implemented structurally without `deriving DecidableEq, Repr`, preventing Lean from synthesizing `partial` `._unsafe_rec` compiler helpers.

#### 5.1 Theorem Inventory and Kernel Axiom Audit

| Theorem | Formal Claim | Kernel Axioms |
| :--- | :--- | :--- |
| `optimize_use_clone_preserves_cfg` | For any multi-block MIR CFG `body` satisfying `BodyUseCallsWellTyped tbl body` and any lawful `TableLawful tbl` (all `Copy ∩ UseCloned` types satisfy `PureBitwiseClone`), `codegenEval tbl body fuel st = postCleanupEval tbl body fuel st` for all `fuel` and `st`. | `[propext, Quot.sound]` |
| `optimize_use_clone_refines_postcleanup_iff_pure_bitwise_clone` | For any `ty` with `(tbl ty).isCopy = true` and `(tbl ty).isUseCloned = true`, `(∀ x calls, codegenEval tbl (genericDupBody ty) 3 (mkDupInitState x calls) = postCleanupEval tbl (genericDupBody ty) 3 (mkDupInitState x calls)) ↔ PureBitwiseClone tbl ty`. | `[propext]` |
| `nondet_call_source_use_envelops_both_miri_and_codegen` | For **every** multi-block CFG `body`, **every** `TypeTable` (including unlawful `SneakyCopy` and panicking `PanicCopy`), **every** `fuel`, and **every** `st`, `NondetEval tbl body fuel st (postCleanupEval tbl body fuel st) ∧ NondetEval tbl body fuel st (codegenEval tbl body fuel st)`. | `[propext, Quot.sound]` |
| `nondet_postcondition_sound_for_miri_and_codegen` | Any postcondition `post : Outcome → Prop` verified against `NondetEval` holds simultaneously for Miri (`postCleanupEval`) and native codegen (`codegenEval`). | `[propext, Quot.sound]` |
| `precise_capture_well_formed_iff_all_ty_params_retained` | Under `PreciseCapturePreconditions` (ordering, uniqueness, bound-lifetime coverage), `PreciseCaptureWellFormed ed inScope boundMentioned args ↔ AllNonLifetimeParamsRetained inScope args`, with `listed_param_is_invariant` and `omitted_unmentioned_lifetime_is_bivariant` proved as supporting lemmas. | `[propext]` |
| `edition_2024_vs_2021_default_lifetime_capture_split` | For any unmentioned lifetime `p`, Edition 2021 yields `Variance.bivariant`, Edition 2024 default yields `Variance.invariant`, and Edition 2024 `+ use<>` restores `Variance.bivariant`. | `[propext]` |
| `substTy_eq_of_covered_agree` | If every free type variable of hidden type `t : TyExpr` is covered by `captured` (`tyVarsCovered captured t = true`), then any two substitutions agreeing on `captured` yield identical instantiated hidden types. | `[propext]` |
| `ce1_safe_sneaky_copy_refutes_deterministic_postcleanup_mir_seam` | Constructively proves `postCleanupEval` = `.returned (.pair 107 7) 1`, `codegenEval` = `.returned (.pair 7 7) 0`, `postCleanupEval ≠ codegenEval`, and `¬ PureBitwiseClone probeTypeTable .sneakyCopy`. | `[propext]` |
| `unwind_unreachable_safe_code_ub_divergence` | Constructively proves that on `PanicCopy`, `postCleanupEval` yields `.ubUnwindPastUnreachable 0` whereas `codegenEval` yields `.returned (.pair 7 7) 0`, and on `PanicNonCopy`, `postCleanupEval` yields `.ubUnwindPastUnreachable 0`. | `[propext]` |
| `ce2_omitted_ty_param_in_use_breaks_hidden_type_subst_e0792` | Constructively proves that `use<'a>` in `<'a, T>` satisfies syntactic preconditions yet fails `PreciseCaptureWellFormed`, leaves `T` uncovered (`tyVarsCovered [0] (.tyVar 1) = false`), causes `substTy` to yield distinct hidden types (`.u32Ty ≠ .boolTy`) behind the same key, and contrasts TAIT `definingUseArgsGeneric [.u32Ty] = false` (`E0792`) with `definingUseArgsGeneric [.tyVar 1] = true`. | `[propext]` |

#### 5.2 Proof-Engineering Structure

- **Biconditional sharpness (`optimize_use_clone_refines_postcleanup_iff_pure_bitwise_clone`):** The forward direction instantiates `hAgree` at `(x = 7, calls = 0)`, performs case analysis on `(tbl ty).cloneBehavior`, cancels `7 + dv = 7 + 0` via `Nat.add_left_cancel` (zero `omega` needed) and `0 + dc = 0` via `Nat.zero_add`, and eliminates `.panics` by constructor disjointness between `.returned` and `.ubUnwindPastUnreachable`. The backward direction unfolds `PureBitwiseClone` and shows step-for-step equality across all `(x, calls)`.
- **Envelope soundness (`nondet_call_source_use_envelops_both_miri_and_codegen`):** Factors through `codegenStep_in_nondetStep`, which proves that every single-block transition of `optimizeUseClone tbl body` is admitted by either `NondetStep.miriBranch` (for non-`Use` calls, non-`Copy` types, `goto`, `return_`, or statement failure) or `NondetStep.codegenElideUseBranch` / `NondetStep.codegenElideUseStuck` (when `CallSource::Use` hits `isCopy = true`), followed by fuel induction.

---

### 6. Implications for Anneal and `Runtime(PostCleanup)` MIR Verification Seams

Basis: source + derived

Auditing `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` pins the exact architectural exposure of a `Runtime(PostCleanup)` MIR verifier:

1. **Current fail-closed posture (`Trusted.MirAst` & `Trusted.MirSemantics`):**
   - `trusted/lean/Trusted/MirAst.lean:780–795` defines `TerminatorKind.call (callee : DefId) (args : List Operand) (dst : Place) (target : Option BasicBlockId) (unwind : UnwindAction)` — it **omits `call_source : CallSource` completely**.
   - `trusted/lean/Trusted/MirSemantics.lean:1568–1569` routes every `.call` to `.fault .unsupported`, so at commit `c131b320e`, Anneal is **not currently unsound** on `ergonomic_clones` because all interprocedural calls fail closed (including `Clone::clone`).
   - `trusted/correspondence/Trusted/Correspondence.lean:1317` fixes the correspondence reference MIR phase to `.Runtime .PostCleanup`, and `vendor/lean-miri/Miri/Interpreter/Call.lean:667` ignores `CallSource` (`| .Call func args dest target unwind _ _ =>`), faithfully mirroring `rustc_const_eval/src/interpret/step.rs:549`.
2. **Forward-compatibility soundness hazard when interprocedural calls are enabled:**
   If a `Runtime(PostCleanup)` or `optimized_mir` verifier admits `TerminatorKind.call` without carrying `call_source` and compiles verified crates with `#![feature(ergonomic_clones)]` through `rustc_codegen_ssa`, **any** functional correctness or safety proof over generic `T: UseCloned` code instantiated at a `Copy` type is unsound whenever `Clone` is not proven `PureBitwiseClone`:
   - A verifier proving `generic_dup(SneakyCopy(7)) == (SneakyCopy(107), SneakyCopy(7))` at `PostCleanup` MIR will produce a kernel-checked theorem that is **falsified at runtime by `-C opt-level=0` native binaries** (`(7, 7)`).
   - Worse, if a caller builds unsafe invariants downstream on the verified return value or side-effect count of a safe `T: UseCloned` function, the discrepancy between verified `PostCleanup` MIR and `optimize_use_clone` codegen can escalate from functional miscompilation into **memory-safety UB in verified code**.
3. **Three Concrete, Mechanically Grounded Mitigations for MIR Verifiers:**
   - **Mitigation A (Fail-Closed Feature/CallSource Gate — cheapest):** Reject crates enabling `#![feature(ergonomic_clones)]` (or reject any `TerminatorKind::Call { call_source: CallSource::Use, .. }` with `.fault .unsupported`) at the capture boundary (`anneal-rustc-capture`).
   - **Mitigation B (Nondeterministic `CallSource::Use` Envelope — sound without restricting safe Rust):** Preserve `call_source : CallSource` in `Trusted.MirAst.TerminatorKind.call` and add an admissible demonic `Choice` branch in `Trusted.MirSemantics.evalStep` permitting `CallSource::Use` on `Copy` types to either invoke `Clone::clone` or perform a bitwise `Operand::Copy` + `goto target` (directly justified by Theorem `nondet_call_source_use_envelops_both_miri_and_codegen`). Under this seam, proofs over `SneakyCopy` are forced to establish postconditions holding for **both** `(107, 7)` and `(7, 7)`, preventing false verification of divergent behavior.
   - **Mitigation C (`PureBitwiseClone` Proof Obligation — enables deterministic proofs):** Require an explicit side-obligation proving `PureBitwiseClone` for every `Copy ∩ UseCloned` type instantiated at a `CallSource::Use` site (directly justified by Theorems `optimize_use_clone_refines_postcleanup_iff_pure_bitwise_clone` and `optimize_use_clone_preserves_cfg`), and additionally reject or patch `unwind: UnwindAction::Unreachable` calls whose callee is not proven panic-free.

## Boundaries

To prevent over-generalization, the negative space of this investigation is classified using the four standard boundary categories:

- **known not to apply — Monomorphic `Copy` call sites:** When `x.use` or `use || x` is written at a monomorphic site where `x`'s type is statically known to implement `Copy` during MIR build (`concrete_dup`, `concrete_closure_dup`), `rustc_mir_build::builder::expr::into` emits `Operand::Copy` directly without a `CallSource::Use` terminator. Both Miri and native binaries agree (`(7, 7)`, `0` clone calls).
- **known not to apply — Non-`Copy` `UseCloned` types for value elision (except panic/unwind):** For `!Copy + UseCloned` types such as `Rc<T>` and `Arc<T>`, `optimize_use_clone` skips the call (`!type_is_copy_modulo_regions`), so Miri and native binaries agree on non-panicking execution (`RC_OUT=43, RC_CNT=3`). However, the `unwind: UnwindAction::Unreachable` hazard **does** apply to `!Copy + UseCloned` types if `Clone::clone` panics (empirically confirmed on `PanicNonCopy`).
- **known not to apply — Stable Rust without `#![feature(ergonomic_clones)]`:** `optimize_use_clone` is guarded by `if tcx.features().ergonomic_clones()` in both `codegen_mir` and `optimize_use_clone`. Stable crates cannot trigger `CallSource::Use` or `optimize_use_clone`. Conversely, the Edition 2024 `use<...>` precise capturing findings (`E0597`, `ParamNotCaptured`, variance) **do** apply to stable Rust.
- **known not to apply — Current `joshlf/anneal@c131b320e` soundness:** Because `Trusted.MirSemantics.evalTerminator` currently fails closed with `.fault .unsupported` on every `TerminatorKind.call`, no unsound verification theorem can currently be proved in `joshlf/anneal@c131b320e` via `CallSource::Use`. The hazard triggers only once interprocedural calls (or MIR extraction of `ergonomic_clones` crates) are admitted.
- **not examined — Non-`rustc_codegen_ssa` backends (`rustc_codegen_cranelift`):** Cranelift uses its own MIR-to-CLIF translator rather than `rustc_codegen_ssa::mir::codegen_mir`; whether `rustc_codegen_cranelift` replicates `optimize_use_clone` or executes `<SneakyCopy as Clone>::clone` was not inspected or executed.
- **not examined — `rustc_codegen_gcc` live execution:** While `rustc_codegen_gcc` implements `rustc_codegen_ssa::traits::BuilderMethods` and shares `codegen_mir`, live binaries from `rustc_codegen_gcc` were not compiled or executed.
- **not examined — `const fn` / CTFE evaluation of `x.use`:** Whether `#[feature(ergonomic_clones)]` interacts with `const_trait_impl` / `mir_for_ctfe` in `const` evaluation was not examined.
- **not examined — Native execution of `PanicNonCopy` with non-trivial drop glue in `generic_dup`:** While `PanicNonCopy` was observed to print `CAUGHT_PANIC` under native `-C opt-level=0` and `-O` when `generic_dup` held no `Drop` locals, native behavior when `generic_dup` holds live `Drop` locals (where `UnwindAction::Unreachable` suppresses cleanup landing pads) or under `-C panic=abort` was not empirically executed.
- **not examined — Edition 2024 `use<...>` in RPITITs (`trait` methods), `Self` alias `E0799`, and `impl_trait_in_assoc_type`:** Source inspection confirmed `ForceCaptureTraitArgs::Yes`, `SelfTyNotCaptured`, `LifetimeImplicitlyCaptured`, and `PreciseCaptureSelfAlias` (`E0799`), but live execution in Part C focused on free-function RPITs and TAIT `E0792`.
- **unknown — Upstream stabilization design for `ergonomic_clones` (`rust-lang/rust#132290`):** Because `ergonomic_clones` carries `#[warn(incomplete_features)]` and `optimize_use_clone` carries `// FIXME: Move this function to mir::transform when post-mono MIR passes land`, it is unknown whether upstream Rust will (a) keep `optimize_use_clone` and add a post-mono MIR pass consumed by Miri too, (b) make `UseCloned` or `Copy::clone` contractually side-effect-free or `unsafe`, (c) disallow `optimize_use_clone` elision on non-trivial `Clone` impls, or (d) replace `UnwindAction::Unreachable` with `UnwindAction::Continue`.
- **unsupported — Omitting type or const parameters in `use<...>`:** Upstream `rustc` explicitly rejects omitting any in-scope type or const parameter from `use<...>` (`check_opaque_precise_captures`), noting in its own diagnostic: *"currently, all type parameters are required to be mentioned in the precise captures list"*.
- **Scope limit of the Lean mechanization:** `support/UseClonedPostMonoSeamSoundness.lean` models a clean, first-order operational core (scalars, pairs, local slots, atomic `cloneCalls`, `CallSource`, `UnwindAction`, multi-block CFGs, and recursive `TyExpr` substitution). It does **not** mechanize full Rust memory provenance, Stacked/Tree Borrows aliasing retags (`WithRetag::Yes`), `deduce_param_attrs` LLVM attribute soundness, or full trait-solver normalization. Extending `optimize_use_clone` soundness to raw-pointer aliasing or `WithRetag::Yes` retag preservation requires separate provenance-level verification.

## Evidence

### 1. Primary Upstream Source Citations (Pinned 40-Hex Commits)

| Repository & Commit | File & Lines / Symbol | Verified Content |
| :--- | :--- | :--- |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `library/core/src/clone.rs:380–428` (`pub trait UseCloned`) | Safe trait `pub trait UseCloned: Clone {}` under `#[unstable(feature = "ergonomic_clones", issue = "132290")]`, `#[lang = "use_cloned"]`; prose-only side-effect guideline; primitive `impl_use_cloned!`. |
| `rust-lang/rust`<br>`342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `library/core/src/clone.rs:394–445` (`pub trait UseCloned`) | Identical safe trait definition and doc comments at upstream `main` (`2026-11-22`). |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `library/alloc/src/rc.rs:2522, 3713` & `library/alloc/src/sync.rs:2433, 3444` | `UseCloned` impls for `Rc<T, A>`, `rc::Weak<T, A>`, `Arc<T, A>`, `sync::Weak<T, A>`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `342d74463a...` | `compiler/rustc_hir_typeck/src/expr_use_visitor.rs:335–349` / `334–348` (`consume_clone_or_copy`) | Three-way classification: `type_is_copy_modulo_regions` -> `copy`, else `type_is_use_cloned_modulo_regions` -> `use_cloned`, else `consume`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_hir_typeck/src/upvar.rs:2140–2155` (`use_cloned`) & `compiler/rustc_mir_build/src/thir/cx/expr.rs:442–444, 1401–1411` | `use \|\|` upvar capture sets `ty::UpvarCapture::ByUse`, which `capture_upvar` lowers identically to `x.use` as `thir::ExprKind::ByUse`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `342d74463a...` | `compiler/rustc_middle/src/mir/syntax.rs:629–649, 817` / `622–642, 806` (`CallSource`) | Doc comment *"Used only for diagnostics."* on `pub enum CallSource` containing `CallSource::Use`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `342d74463a...` | `compiler/rustc_mir_build/src/builder/expr/into.rs:513–563` / `526–577` (`ExprKind::ByUse`) | Polymorphic lowering: `Copy` -> `Operand::Copy`; `UseCloned` -> `TerminatorKind::Call { func: Clone::clone, unwind: UnwindAction::Unreachable, call_source: CallSource::Use }`; else `Operand::Move`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `342d74463a...` | `compiler/rustc_codegen_ssa/src/mir/mod.rs:209–224, 352–407` / `211–228, 390–445` (`codegen_mir`, `optimize_use_clone`) | Unconditional post-monomorphization `optimize_use_clone` rewriting `CallSource::Use` on `Copy` types into `Operand::Copy(*arg_place)` + `Goto`, regardless of opt-level. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `342d74463a...` | `compiler/rustc_const_eval/src/interpret/step.rs:543–567` / `589–613` & `eval_context.rs:552–561` / `540–549` & `machine.rs:197–202` | `Machine::load_mir` calls `tcx.instance_mir`; `eval_terminator` ignores `call_source: _`; `unwind_to_block` throws UB on `UnwindAction::Unreachable`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/lib.rs:572–602, 776–821` | `run_analysis_to_runtime_passes` establishes `MirPhase::Runtime(RuntimePhase::PostCleanup)`; `optimized_mir` steals `mir_drops_elaborated_and_const_checked` and runs pre-monomorphization MIR optimizations (no `optimize_use_clone`). |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `342d74463a...` | `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs:323–332` / `322–331` (`opaque_captures_all_in_scope_lifetimes`) | `GenericBound::Use` -> `false`; `at_least_rust_2024()` -> `true`; Edition 2021 free/inherent RPIT -> `false`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `342d74463a...` | `compiler/rustc_hir_analysis/src/variance/mod.rs:102–231` / `97–226` (`variance_of_opaque`) | Opaque params initialized `ty::Invariant`; uncaptured parent lifetimes marked `ty::Bivariant` unless mentioned in explicit bounds. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `342d74463a...` | `compiler/rustc_hir_analysis/src/check/check.rs:572–729` / `573–730` & `errors/precise_captures.rs:1–89` / `diagnostics/precise_captures.rs:1–89` | `check_opaque_precise_captures` invariants (`LifetimesMustBeFirst`, `DuplicatePreciseCapture`, `assert_eq!(variances[param], ty::Invariant)`, `LifetimeNotCaptured`, uncoded `ParamNotCaptured`). |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_trait_selection/src/errors.rs:2027–2063` & `opaque_types.rs:17–48` & `compiler/rustc_error_codes/src/error_codes/E0792.md` | `AddPreciseCapturingForOvercapture` suggestion for Edition 2024 `E0597`, and `NonGenericOpaqueTypeParam` (`E0792`) for non-generic opaque defining-use arguments. |
| `joshlf/anneal`<br>`c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:52–57, 780–795`, `Trusted/MirSemantics.lean:1568–1569`, `trusted/correspondence/Trusted/Correspondence.lean:1317`, `vendor/lean-miri/Miri/MIR/Syntax.lean:148–154`, `vendor/lean-miri/Miri/Interpreter/Call.lean:667` | Anneal targets `Runtime(PostCleanup)` MIR, omits `call_source` from `Trusted.MirAst.TerminatorKind.call` (currently failing closed with `.fault .unsupported`), and `vendor/lean-miri` ignores `CallSource` on `.Call`. |

### 2. Preserved Package Support Artifacts & Verification Receipts (`2026-11-22`)

| Support File | Size | SHA-256 | Purpose & Verification Command |
| :--- | ---: | :--- | :--- |
| `support/probe_ergonomic_clones_seam_and_use_captures.py` | 23,362 B | `fd2132f8d49d6888d6c6be094bd4d1281c825ce79923a74aeca92b65293becd6` | Self-contained Python 3.10+ stdlib probe reproducing Parts A, B, and C live against `rustc`, native binaries, MIR/LLVM-IR dumps, and `cargo miri` (Stacked & Tree Borrows). |
| `support/probe_results.json` | 29,623 B | `40dc9be459f03c70a390df37083e13e2e153e923af7ea7e4dbabc4958b279769` | Exact machine-captured JSON output from `python3 support/probe_ergonomic_clones_seam_and_use_captures.py --out support/probe_results.json` (`exit 0`, 14/14 Part C expectations matched, Part A divergence & Part B UB divergence recorded verbatim). |
| `support/UseClonedPostMonoSeamSoundness.lean` | 51,543 B | `cb7e0f2b3ef88ba3516dbcca8d57c7884c6912f30643ff24a862e963043bc0b9` | Standalone Lean `v4.34.1` formalization (1,130 lines, 750 kernel constants, 10 theorems). Verified with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, `UNSAFE_REC_COUNT=0`, `PARTIAL_COUNT=0`, axioms strictly within `[propext]` / `[propext, Quot.sound]`). |

## Revalidation

Each major finding can be cheaply revalidated against any newer `rust-lang/rust` nightly, `joshlf/anneal` commit, or `leanprover/lean4` release using three narrow, discriminating commands:

### 1. Re-run the Live `rustc` & `Miri` Probe (Parts A, B, and C)

From the report package directory with a nightly `rustc` and `miri` component installed:

```bash
python3 support/probe_ergonomic_clones_seam_and_use_captures.py --out /tmp/reval_probe.json
```

(If running in an offline environment where `~/.cargo/config.toml` overrides `crates-io` with a project vendor directory that conflicts with `rust-src`, either pass a pre-built `MIRI_SYSROOT=/path/to/miri_sysroot` or let the script auto-configure `rust-src`'s bundled `library/vendor`.)

Check these three discriminating invariants in `/tmp/reval_probe.json`:
1. **Part A divergence still live:** `native_opt0_mir0.stdout` contains `GENERIC=(7,7) CALLS_G=0 GENERIC_CLOSURE=(7,7) CALLS_GC=0`, `miri_stacked_borrows.stdout` and `miri_tree_borrows.stdout` contain `GENERIC=(107,7) CALLS_G=1 GENERIC_CLOSURE=(107,7) CALLS_GC=1`, and `llvm_ir_generic_dup_calls_clone == false`. If Miri switches to `(7, 7)` (e.g., if `optimize_use_clone` moves into a post-mono MIR pass consumed by Miri) or native switches to `(107, 7)`, the operational seam divergence has changed and this report must be updated.
2. **Part B `UnwindAction::Unreachable` UB still live:** `panic_copy_native_opt0.stdout == "OK=(7,7)"` while `panic_copy_miri_sb.rc == 1` and `panic_noncopy_miri_sb.rc == 1` with `"unwinding past a stack frame that does not allow unwinding"`. If `rustc_mir_build` changes `unwind: UnwindAction::Unreachable` to `UnwindAction::Continue`, `panic_noncopy_miri_sb` will print `CAUGHT_PANIC` (`rc=0`).
3. **Part C 14/14 diagnostic & variance checks:** Every entry in `part_c_precise_capturing_and_ergonomic_clone_gates` has `matched_expectation == true`, and `rpit_use_omitting_in_scope_type_param_rejected` vs. `tait_non_generic_param_rejected_e0792` still separates uncoded `ParamNotCaptured` from `E0792`.

### 2. Diff the Five Load-Bearing Upstream Regions in `rust-lang/rust`

To check whether upstream `rust-lang/rust` has closed the seam without running binaries, diff only these five files against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:
- `library/core/src/clone.rs` (check whether `UseCloned` became `unsafe trait` or gained a soundness contract)
- `compiler/rustc_mir_build/src/builder/expr/into.rs` (check `ExprKind::ByUse`: `CallSource::Use` and `unwind: UnwindAction::Unreachable`)
- `compiler/rustc_codegen_ssa/src/mir/mod.rs` (check whether `optimize_use_clone` was moved out of `codegen_mir`, gated on opt-level, or removed)
- `compiler/rustc_const_eval/src/interpret/step.rs` (check whether `Call { call_source: _, .. }` started inspecting `CallSource::Use`)
- `compiler/rustc_hir_analysis/src/check/check.rs` and `compiler/rustc_hir_analysis/src/diagnostics/precise_captures.rs` (check whether omitting type/const parameters in `use<...>` was relaxed or assigned an error code)

### 3. Re-verify the Standalone Lean `v4.34.1` Formalization

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/UseClonedPostMonoSeamSoundness.lean
```

Confirm exit code `0`, zero warnings, and — by appending `#print axioms` on the ten exported theorems in a temporary scratch file — confirm that no `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `partial`, or `._unsafe_rec` constant was introduced under any newer Lean toolchain.
