<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Post-monomorphization errors, MIR semantics, and polymorphic conditional contracts in Anneal

## Summary

A Rust function can pass polymorphic type checking and borrow checking yet fail
compile-time constant evaluation (CTFE) or layout computation when instantiated
during monomorphization, producing a Post-Monomorphization Error (PME,
`error[E0080]`). Both `const { assert!(N <= 1000) }` and `zerocopy`'s
`transmute_ref<Src, Dst>` rely on this mechanism: their runtime
`MirPhase::Runtime(RuntimePhase::PostCleanup)` basic blocks omit the assertion
logic, which `rustc` extracts into `Body::required_consts` (`ConstMirBody`) for
evaluation during `rustc_monomorphize::collector::collect_items_of_instance`.
If Anneal models only a function's runtime control-flow graph, safe functions
whose memory safety or arithmetic overflow freedom depends on a PME become
unverifiable because invalid instantiations exhibit runtime undefined behavior
(UB) in the unguarded runtime CFG.

Two standalone Lean 4 (`v4.34.1`) mechanizations preserved in this package—
[PmeMirSemantics.lean](PmeMirSemantics.lean) (2,563 lines, SHA-256
`c93ee5252538031e0953e154800573701515a564d86f7bbc2083a59ad0f2cc7f`) and
[PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean)
(2,110 lines, SHA-256
`9b7d816ea84413422941fdc4609b0939cc827ec413375d20314208cbf3207495`)—establish
five core results with zero `sorryAx` and zero `Lean.ofReduceBool`:

1. **Single-interpreter PME model (`ConstMirMachine` and `CompileAdmitted`):**
   Every entry in `Body::required_consts` is itself a `Runtime(PostCleanup)`
   MIR body (`tcx.mir_for_ctfe(def_id)`). Extending `MirBody` with
   `requiredConsts : List ConstMirBody` and `requiredLayouts : List TyLayout`
   lets `ConstMirMachine` evaluate CTFE obligations using the exact same
   small-step transition function (`evalBlocksStep`) as runtime `MirMachine`.
2. **Dead-branch retention vs. post-divergence stripping in `rustc`:**
   All conditional branches (`if false`, `match false`, `if (const { false })`,
   and `let b = false; if b`) lower to `TerminatorKind::SwitchInt` on a
   temporary local, remain reachable from `START_BLOCK` (`bb0`) through
   `SimplifyCfg::Initial`, populate `Body::required_consts` and
   `Body::mentioned_items`, and fail monomorphization with `error[E0080]`.
   Only statements after unconditional divergence (`return;`, `break;`,
   `continue;`, or `loop {}` without `break`) are lowered into zero-predecessor
   basic blocks that `SimplifyCfg::Initial` deletes before `mir_promoted` runs.
3. **Why `rustc --crate-type=lib` exit code 0 does not prove
   `CompileAdmitted`:**
   Under lazy monomorphization (`MonoItemCollectionStrategy::Lazy`), `rustc`
   skips root collection for generic functions, unreachable private
   non-generic functions, and cross-crate inlinable public non-generic
   functions (`#[inline]` or `-C opt-level=2` via
   `reachable_non_generics_helper`). Anneal must therefore verify
   `CompileAdmitted` explicitly rather than trusting `rustc`'s exit status.
4. **Adjoint equivalence of Approach 1 (`PartialCompiler`) and Approach 2
   (`MirMachine.withAdmitted`):**
   In `Behavior Query Out := Query → Partial (Out → Prop)`, gating a program
   behavior by a compile-time proposition `P` (`Behavior.when P b`, collapsing
   to `Partial.bot` when `¬ P`) is constructively left adjoint to guarding a
   specification by `P` (`Behavior.given P spec`, collapsing to `Partial.ub`
   when `¬ P`). Approach 2 (`MirSemAdmitted body ≤ spec`) preserves
   `TotalStep`, `InhabitedDemonic`, and `non_vacuity_at_every_depth` and is
   constructively equivalent (`↔`) to Approach 1's conditional obligation
   `body.CompileAdmitted → MirSem body ≤ spec` (`mirSemAdmitted_le_iff`).
5. **Polymorphic and cross-crate conditional contracts (`InstCtx`, R1 vs. R2):**
   Representing a polymorphic function as an `InstCtx`-indexed family of
   `MonoMirUnit`s (Representation R1, `PolyCapturedFnR1`) or as a
   query-enriched language `PolyMirLang InstCtx` with
   `PolyQuery InstCtx := InstCtx × ExecQuery MirState` (Representation R2)
   requires no changes to `Trusted/Refinement.lean`. A two-pass
   `model-refinement` analysis shows that a naive conjunction of instantiation
   and runtime preconditions in R2 (`naiveTotalPre`) vacuously accepts a
   PME-failing program whenever the runtime argument precondition `argPre` is
   uninhabited (`naive_r2_vacuous_argPre_counterexample`). Including the 0-step
   compile-time prefix (`q.steps = 0 ∨ argPre inst q` in `unifiedTotalPre`)
   restores an exact constructive equivalence (`↔`) between R1 and R2
   (`r1_iff_r2_source_wellFormed`) and supports modular cross-crate
   verification of callers alongside three distinct failure controls (PME
   violation, `LIB-07` semantic trait violation, and runtime argument
   precondition violation).

## Applicability

The findings in this report apply to the combination of the five concrete
subjects recorded in `REPORT.json`:

- **Anneal verification framework (`joshlf/anneal` at
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):**
  Specifically the refinement lattice and `VerificationResultOn` envelope in
  [`trusted/lean/Trusted/Refinement.lean`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/lean/Trusted/Refinement.lean),
  the small-step prefix machine in
  [`trusted/lean/Trusted/StepResult.lean`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/lean/Trusted/StepResult.lean),
  the MIR AST and operational semantics in
  [`trusted/lean/Trusted/MirAst.lean`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/lean/Trusted/MirAst.lean)
  and
  [`trusted/lean/Trusted/MirSemantics.lean`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/lean/Trusted/MirSemantics.lean),
  and the MIR extractor in
  [`trusted/rustc-capture/src/lib.rs`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/rustc-capture/src/lib.rs).
- **Lean 4 theorem prover (`leanprover/lean4` at
  `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):**
  Used to elaborate and kernel-typecheck both standalone mechanizations with
  `-DElab.async=false -Ddebug.skipKernelTC=false`.
- **Rust compiler (`rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67`, `rustc 1.99.1`):**
  Examined across `compiler/rustc_middle`, `compiler/rustc_mir_build`,
  `compiler/rustc_mir_transform`, `compiler/rustc_monomorphize`, and
  `compiler/rustc_codegen_ssa`, and executed in empirical probes of
  `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked`),
  `Runtime(Optimized)` MIR (`tcx.optimized_mir`), and `tcx.mir_for_ctfe`.
- **The Rust Reference (`rust-lang/reference` at
  `82da570bafd9efed421bdbae0f8603ede8dd308b`):**
  Normative rules for `const` block evaluation (`expression.block.const`),
  type layout properties (`layout.properties`), and reference validity
  (`undefined.validity.reference-box`).
- **`zerocopy` (`google/zerocopy` at
  `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`):**
  Specifically the `transmute_ref` and `static_assert!` compile-time size and
  alignment guard patterns in `src/util/macros.rs` and `src/lib.rs`.

Results concerning `Partial`, `Behavior`, `SmallStepMachine`, `ReachesPrefix`,
and the R1/R2 equivalence are pure mathematical theorems in Lean 4 and hold
independently of host OS or target architecture. Results concerning `rustc` MIR
pass ordering, `Body::required_consts`, `Body::mentioned_items`, and
monomorphization root collection apply specifically to `rust-lang/rust` at
`58cf8f9c35b355199727627d07ae34a4e2846d67` under both `-Z mir-opt-level=0` and
default `-Z mir-opt-level=1`.

## Findings

### 1. How `rustc` Lowers and Evaluates PMEs Across the MIR Pipeline

`Basis: normative + source + execution`

According to the Rust Reference
([`src/expressions/block-expr.md`](https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions/block-expr.md),
rule `expression.block.const`), whether an inline `const { ... }` block inside
a generic item is evaluated depends on whether the enclosing item is
monomorphized and whether the `const` block is reachable in the MIR control-flow
graph prior to constant-evaluation collection.

In `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, PME obligations
pass through four stages between MIR construction and code generation:

1. **Reachable constant collection in `mir_promoted`:**
   In [`compiler/rustc_mir_transform/src/lib.rs#L473-L476`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L473-L476),
   `RequiredConstsVisitor::compute_required_consts`
   ([`compiler/rustc_mir_transform/src/required_consts.rs#L9-L23`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/required_consts.rs#L9-L23))
   traverses `body` in `traversal::reverse_postorder(body)` from `START_BLOCK`
   (`bb0`) and records every `ConstOperand` whose `const_.is_required_const()`
   is `true` (`Const::Unevaluated`, covering both inline `const { ... }`
   blocks `fn_name::{constant#k}` and associated constants `<T as Trait>::C`)
   into `body.required_consts`.
2. **Mentioned-item collection at the entry to `inner_optimized_mir`:**
   In [`compiler/rustc_mir_transform/src/lib.rs#L808-L819`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L808-L819),
   before optimization passes fold constant branches, `MentionedItemsVisitor`
   ([`compiler/rustc_mir_transform/src/mentioned_items.rs#L40-L85`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/mentioned_items.rs#L40-L85))
   records zero-sized function items (`MentionedItem::Fn`), drop types, and
   unsizing casts in `body.mentioned_items` so monomorphization still evaluates
   a callee's `required_consts` even if dead-code optimizations later delete
   the call terminator.
3. **Runtime cleanup and dead-store elimination:**
   During `run_analysis_to_runtime_passes` and `run_runtime_cleanup_passes`
   ([`compiler/rustc_mir_transform/src/lib.rs#L653-L693`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L653-L693)),
   `RemovePlaceMention` and `RemoveZsts` strip place mentions, and in
   `Runtime(Optimized)` (`-Z mir-opt-level >= 1`), dead-store elimination
   deletes unit-typed assignments `_2 = const fn_name::{constant#0};` from
   `body.basic_blocks` completely. Consequently, in optimized MIR the runtime
   basic blocks contain no reference to `{constant#0}`, and the assertion logic
   lives exclusively in `body.required_consts` and its separate CTFE MIR body
   `tcx.mir_for_ctfe(def_id)`.
4. **Monomorphization-time evaluation in `collect_items_of_instance`:**
   In [`compiler/rustc_monomorphize/src/collector.rs#L1364-L1389`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1364-L1389),
   `collect_items_of_instance` substitutes the concrete `Instance<'tcx>`
   arguments into each entry of `body.required_consts()`, evaluates it via
   `constant.eval(tcx, ty::TypingEnv::fully_monomorphized(), span)`, emits
   `error[E0080]` if CTFE panics or fails, and recursively traverses
   `body.mentioned_items()` in `CollectionMode::MentionedItems` to evaluate
   transitive `required_consts`.

### 2. Dead Branches (`if false`, `match false`) vs. Post-Divergence (`return;`)

`Basis: source + execution`

A critical distinction governs which syntactically unreachable PMEs `rustc`
evaluates and which it discards:

- **All conditional branches (`if false`, `match false`, `if (const { false })`,
  `let b = false; if b`) retain CFG edges in `mir_built` and trigger PMEs:**
  When `Builder::expr_into_dest` lowers `ExprKind::If`
  ([`compiler/rustc_mir_build/src/builder/expr/into.rs#L61-L126`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/into.rs#L61-L126)),
  `Builder::lower_if_condition`
  ([`compiler/rustc_mir_build/src/builder/matches/mod.rs#L206-L214`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/mod.rs#L206-L214))
  materializes the condition into a temporary local (`_1 = const false;`) and
  terminates `bb0` with
  `TerminatorKind::if_(Operand::Move(scrutinee), then_blk, else_blk)`
  (`switchInt(move _1) -> [0: else_blk, otherwise: then_blk]`). Similarly,
  `Builder::perform_test` for `ExprKind::Match` on a `bool` scrutinee
  ([`compiler/rustc_mir_build/src/builder/matches/test.rs#L136-L141`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/test.rs#L136-L141))
  emits the same `TerminatorKind::if_`.
  When `SimplifyCfg::Initial` runs at the end of `mir_built`
  ([`compiler/rustc_mir_transform/src/lib.rs#L422`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L422)),
  `CfgSimplifier::simplify_branch`
  ([`compiler/rustc_mir_transform/src/simplify.rs#L250-L272`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify.rs#L250-L272))
  never inspects the constant value of a `SwitchInt` operand; folding constant
  `SwitchInt` discriminants is performed only by
  `SimplifyConstCondition::{AfterConstProp, Final}`
  ([`compiler/rustc_mir_transform/src/simplify_branches.rs#L30-L98`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify_branches.rs#L30-L98))
  inside `run_optimization_passes` (`-Z mir-opt-level >= 1`), which runs
  *after* `mir_promoted` (`RequiredConstsVisitor`) and *after*
  `MentionedItems`.
- **Statements after unconditional divergence (`return;`, `break;`,
  `continue;`, `loop {}` without `break`) have zero CFG predecessors and are
  stripped before `mir_promoted`:**
  When `Builder::stmt_expr` lowers `ExprKind::Ret`, `ExprKind::Break`, or
  `ExprKind::Continue`
  ([`compiler/rustc_mir_build/src/builder/expr/stmt.rs#L96-L107`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/stmt.rs#L96-L107)),
  `Builder::break_scope`
  ([`compiler/rustc_mir_build/src/builder/scope.rs#L823-L830`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs#L823-L830))
  terminates the current block and returns `self.cfg.start_new_block().unit()`,
  a freshly allocated basic block with **zero incoming CFG edges**. Likewise,
  `Builder::in_breakable_scope` for a `loop {}` without `break`
  ([`compiler/rustc_mir_build/src/builder/scope.rs#L563-L565`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs#L563-L565))
  allocates an unreachable exit block via `self.cfg.start_new_block()`.
  `SimplifyCfg::Initial` calls `remove_dead_blocks(body)`
  ([`compiler/rustc_mir_transform/src/simplify.rs#L87`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify.rs#L87)),
  deleting those zero-predecessor blocks before `mir_promoted` runs.

| Construct with Failing Payload (`N = 2000`) | Predecessors in `mir_built` | Survives `SimplifyCfg::Initial`? | Recorded in `required_consts` / `mentioned_items`? | `rustc --emit=obj` Result |
| :--- | :--- | :--- | :--- | :--- |
| `if false { const { assert!(N <= 1000); } }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`required_consts`) | Fails (`error[E0080]`) |
| `if false { fail_const::<N>(); }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`mentioned_items`) | Fails (`error[E0080]`) |
| `match false { true => const { assert!(N <= 1000); }, false => () }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`required_consts`) | Fails (`error[E0080]`) |
| `match false { true => fail_const::<N>(), false => () }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`mentioned_items`) | Fails (`error[E0080]`) |
| `if (const { false }) { const { assert!(N <= 1000); } }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`required_consts`) | Fails (`error[E0080]`) |
| `let b = false; if b { const { assert!(N <= 1000); } }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`required_consts`) | Fails (`error[E0080]`) |
| `return; const { assert!(N <= 1000); };` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |
| `return; fail_const::<N>();` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |
| `loop { break; const { assert!(N <= 1000); }; }` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |
| `while false { continue; const { assert!(N <= 1000); }; }` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |
| `loop {} const { assert!(N <= 1000); };` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |

Because `Runtime(PostCleanup)` MIR
(`tcx.mir_drops_elaborated_and_const_checked`) is captured *after*
`SimplifyCfg::Initial` and *before* `SimplifyConstCondition`, its basic blocks
match the exact reachability horizon of `RequiredConstsVisitor` and
`MentionedItems`. Furthermore, because HIR lowering allocates a `LocalDefId` in
`tcx.mir_keys(())` even for an unreachable post-`return` `const { ... }` block,
`anneal-rustc-capture` must never attach an `InlineConst` item to a parent
function merely because its `DefId` or `--emit=mir` symbol prefix exists; a
constant body is a PME obligation of `f` if and only if `f`'s
`required_consts()` (or `Runtime(PostCleanup)` basic blocks) references it.

### 3. Single-Interpreter Model of PMEs (`ConstMirMachine`, `CompileAdmitted`)

`Basis: source + execution + derived`

In [PmeMirSemantics.lean](PmeMirSemantics.lean#L708-L724), `MirBody` is extended
with `requiredConsts : List ConstMirBody` and `requiredLayouts : List TyLayout`,
where each `ConstMirBody` (`localCount : Nat`, `blocks : List BasicBlock`) uses
the exact same `BasicBlock`, `Stmt`, `Rvalue`, and `Terminator` AST as runtime
`MirBody`:

- **Shared small-step transition function (`evalBlocksStep`):**
  Both `MirMachine`
  ([PmeMirSemantics.lean](PmeMirSemantics.lean#L984-L987)) and `ConstMirMachine`
  ([PmeMirSemantics.lean](PmeMirSemantics.lean#L1003-L1005)) execute
  `evalBlocksStep blocks s`
  ([PmeMirSemantics.lean](PmeMirSemantics.lean#L969-L976)). `ConstMirMachine`
  starts from `initCtfeState` (`locals := fun _ => none`,
  `mem := MemState.empty`, `block := 0`, `stmtIdx := 0`).
- **CTFE admissibility (`CtfeAdmitted` and `MirBody.CompileAdmitted`):**
  A constant body `c : ConstMirBody` satisfies `CtfeAdmitted c`
  ([PmeMirSemantics.lean](PmeMirSemantics.lean#L1172-L1178)) when:
  1. Every finite execution prefix from `initCtfeState` is safe (`out.isSafe`,
     ruling out `.failed .contractViolation` from `Terminator.panic` /
     `Terminator.assertNotOverflow` and `.failed .ub`), and
  2. There exists a finite step budget `steps` reaching
     `.terminated (.normal .unit)` (ruling out CTFE non-termination such as
     `const { loop {} }`, verified by `negative_control_const_loop_not_admitted`
     in [PmeMirSemantics.lean](PmeMirSemantics.lean#L2550-L2561)).
  A function body satisfies `body.CompileAdmitted`
  ([PmeMirSemantics.lean](PmeMirSemantics.lean#L1183-L1185)) when
  `AllHold (body.requiredConsts.map CtfeAdmitted)` and
  `AllHold (body.requiredLayouts.map TyLayout.WellFormed)` hold.

### 4. Why `rustc --crate-type=lib` Does Not Guarantee `CompileAdmitted`

`Basis: source + execution`

Inspecting `rustc_monomorphize::collector`
([`compiler/rustc_monomorphize/src/collector.rs#L1753-L1792`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1753-L1792))
and `rustc_codegen_ssa::back::symbol_export`
([`compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L114-L118`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L114-L118))
establishes three classes of functions for which `rustc --crate-type=lib` exits
with status `0` even when the function contains an unconditionally failing PME:

1. **Generic functions (`requires_monomorphization == true`):**
   `RootCollector::is_root` (`collector.rs:1754`) requires
   `!self.tcx.generics_of(def_id).requires_monomorphization(self.tcx)`. An
   uninstantiated generic function
   `pub fn broken<T>(x: T) -> T { const { assert!(false); } x }` is never
   collected in `--crate-type=lib`.
2. **Unreachable private non-generic functions
   (`is_reachable_non_generic == false`):**
   Under default `MonoItemCollectionStrategy::Lazy` (`collector.rs:1768-1778`),
   a private non-generic function
   `fn dead() -> usize { const_bounded_add::<2000>(5) }` is not reachable from
   any exported symbol and is skipped during monomorphization.
3. **Cross-crate inlinable public non-generic functions (`#[inline]` or
   `-C opt-level=2`):**
   In `reachable_non_generics_helper` (`symbol_export.rs:114-118`), `rustc`
   excludes any non-generic function where `instance.def.requires_inline(tcx)`
   or `tcx.cross_crate_inlinable(def_id)` holds. Consequently, a **public,
   non-generic** function
   `#[inline] pub fn call_top() -> usize { const_bounded_add::<2000>(5) }`
   (or an unannotated `pub fn` compiled with `--crate-type=lib -C opt-level=2`)
   has `is_reachable_non_generic == false`, is skipped by `RootCollector`, and
   compiles with exit code `0`, deferring the `error[E0080]` failure until a
   downstream crate codegens a call to it.

Anneal therefore cannot rely on `rustc`'s exit status to establish
`CompileAdmitted`; concrete functions require `ConcreteVerifiedAndAdmitted`
([PmeMirSemantics.lean](PmeMirSemantics.lean#L1324-L1325)) and generic functions
certifying an explicit compilation domain require `GenericVerifiedWithDomain`
([PmeMirSemantics.lean](PmeMirSemantics.lean#L1331-L1337)).

### 5. Approach 1 (`PartialCompiler`) vs. Approach 2 (`MirMachine.withAdmitted`)

`Basis: execution + derived`

In `Behavior Query Out := Query → Partial (Out → Prop)`, `Partial (Out → Prop)`
has both a top element `Partial.ub` (`defined := False`, used by `SpecOn`
outside `pre q`) and a bottom element `Partial.bot` (`defined := True`,
`val := fun _ _ => False`, representing zero runtime executions; see `bot_le`
and `le_ub` in [PmeMirSemantics.lean](PmeMirSemantics.lean#L100-L132)).

Defining the program-side compile-time gate `Behavior.when P b` and the
specification-side compile-time guard `Behavior.given P spec` purely
constructively (without `Classical.propDecidable`):

```lean
def Behavior.when (P : Prop) (b : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P → (b q).defined
    val := fun hdef out => ∃ hP : P, (b q).val (hdef hP) out
  }

def Behavior.given (P : Prop) (spec : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P ∧ (spec q).defined
    val := fun hdef out => (spec q).val hdef.2 out
  }
```

yields the constructive Galois connection `Behavior.when P ⊣ Behavior.given P`
([PmeMirSemantics.lean](PmeMirSemantics.lean#L164-L196), proved using **zero
axioms**, not even `propext`):

```text
Behavior.when P b ≤ spec  ↔  (P → b ≤ spec)  ↔  b ≤ Behavior.given P spec
```

This adjunction relates the two candidate ways of integrating `CompileAdmitted`
into Anneal:

- **Approach 1 (`PartialCompiler` at the TCB boundary,
  [PmeMirSemantics.lean](PmeMirSemantics.lean#L1192-L1266)):**
  Keeps `MirMachine` and `MirSem body` as pure runtime operational semantics.
  `PartialCompiler` models `compile : L_src.Prog → Partial L_tgt.Prog`, and
  `PartialCompiler.SoundOn` asserts both
  `(C.compile body).defined → body.CompileAdmitted` (compile-time PME gate
  soundness) and target lowering soundness for `(C.compile body).val h`.
  Equivalently, in
  [PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean#L636-L815),
  pairing `MonoMirLang.sem u` (where `defined` is
  `u.pmeOk ∧ (MirLang.sem u.body q).defined`) and
  `PartialTargetLang.sem := semTotalCompiled` embeds partial compilation
  directly into the existing `Trusted.Compiler` structure with zero changes to
  `Trusted/Refinement.lean`, where
  `verifiedTotal_iff_noPme_and_verifiedIfCompiled` proves that total
  verification is constructively equivalent to `NoPME` paired with
  `VerifiedIfCompiled`.
- **Approach 2 (`SmallStepMachine.withAdmitted`,
  [PmeMirSemantics.lean](PmeMirSemantics.lean#L438-L549) and
  [#L1273-L1315](PmeMirSemantics.lean#L1273-L1315)):**
  Defines `(M.withAdmitted Admitted).initState p s` as
  `Admitted p ∧ M.initState p s` while leaving `M.step` unchanged. Because
  `TotalStep M`, `InhabitedDemonic M`, and `ReachesPrefix M` depend only on
  `M.step`, gating `initState` preserves `TotalStep` (`totalStep_withAdmitted`),
  `InhabitedDemonic` (`inhabitedDemonic_withAdmitted`), and
  `non_vacuity_at_every_depth` identically. At the behavior level,
  `BehaviorOf (M.withAdmitted Admitted) p` is order-isomorphic to
  `Behavior.when (Admitted p) (BehaviorOf M p)`
  (`behaviorOf_withAdmitted_le_when`,
  `behavior_when_le_behaviorOf_withAdmitted`), yielding the universal
  equivalence (`mirSemAdmitted_le_iff`,
  [PmeMirSemantics.lean](PmeMirSemantics.lean#L1302-L1304)):
  ```lean
  theorem mirSemAdmitted_le_iff (body : MirBody) (spec : MirLang.Behavior) :
      MirSemAdmitted body ≤ spec ↔ (body.CompileAdmitted → MirSem body ≤ spec)
  ```

| Criterion | Approach 1 (`PartialCompiler` / `MonoMirLang` in `trusted/`) | Approach 2 (`MirMachineAdmitted` in `trusted/`) |
| :--- | :--- | :--- |
| **Trust-boundary clarity (`PRINCIPLES.md`)** | Separates compile-time PME rejection (`compile`) from runtime operational semantics (`MirSem`). | Conflates compile-time rejection with a runtime machine that has zero initial states (`Partial.bot`), allowing an uncompilable program to refine `SpecOn (fun _ => True) (fun _ _ => False)`. |
| **Interprocedural calls (`Call` terminator)** | `CompileAdmitted` is transitively closed over `mentioned_items`, matching `rustc_monomorphize::collector`. | Delegating a runtime `Call` to `MirSemAdmitted callee` without closing `caller.CompileAdmitted` over `mentioned_items` turns an uncompilable callee inside a runtime branch into a runtime `assume(false)` miracle. |
| **Proof ergonomics** | Proof authors assume `hAdm : body.CompileAdmitted` directly in `hAdm → MirSem body ≤ spec`. | Constructively equivalent via `mirSemAdmitted_le_iff` in `theory/`. |

### 6. Case Studies: `const_bounded_add<N>` and `zerocopy::transmute_ref`

`Basis: source + execution`

Section 5 of [PmeMirSemantics.lean](PmeMirSemantics.lean#L1340-L2563) mechanizes
two canonical PME patterns and four negative controls end-to-end:

1. **`const_bounded_add<const N: usize>(x: usize) -> usize`
   ([PmeMirSemantics.lean](PmeMirSemantics.lean#L1344-L1921)):**
   The runtime body `constBoundedAddBody N` branches on `x <= 1000` and computes
   `CheckedBinOp.add` (`x + N`) guarded by `Terminator.assertNotOverflow`, while
   `requiredConsts := [constBoundedAddConst0 N]` checks `N <= 1000` in CTFE.
   - `constBoundedAdd_compileAdmitted_iff` proves
     `(constBoundedAddBody N).CompileAdmitted ↔ N ≤ 1000`.
   - `constBoundedAdd_source_verified` proves that
     `(constBoundedAddBody N).CompileAdmitted` implies
     `MirSem (constBoundedAddBody N) ≤ EnsuresConstBoundedAdd N`
     for all `N : Nat` with caller precondition `pre := fun _ => True` (because
     `x0 ≤ 1000` and `N ≤ 1000` imply `x0 + N ≤ 2000 ≤ usizeMax`).
   - `constBoundedAdd_generic_verified_with_domain` establishes
     `GenericVerifiedWithDomain` for `constBoundedAddBody` over `N ≤ 1000` and
     `EnsuresConstBoundedAdd`.
   - Negative controls prove `¬ (constBoundedAddBody 2000).CompileAdmitted`
     (`constBoundedAdd_2000_not_compileAdmitted`) and
     `¬ (MirSem (constBoundedAddBody usizeMax) ≤ MirLang.WellFormed)` when the
     PME gate is omitted (`constBoundedAdd_usizeMax_unguarded_runtime_fails`).
2. **`zerocopy`-style `transmute_ref<Src, Dst>(src: &Src) -> &Dst`
   ([PmeMirSemantics.lean](PmeMirSemantics.lean#L1924-L2360)):**
   Models `zerocopy`'s safe reference transmutation
   (`&*(src as *const Src as *const Dst)`), whose runtime body executes
   `Rvalue.addrOfDeref`, `Rvalue.castPtrToPtr`, and `Rvalue.reborrowShared`
   with zero runtime branches. `evalMirStmt` on `.reborrowShared src dstLayout`
   ([PmeMirSemantics.lean](PmeMirSemantics.lean#L902-L916)) enforces Rust's
   reference validity invariant (`r[undefined.validity.reference-box]`:
   `addr ≠ 0`, `0 < dstLayout.align`, `dstLayout.align ∣ addr`, and
   `dstLayout.size ≤ s.mem.allocSize loc`), transitioning to `.failed .ub` if
   violated.
   - `transmuteRef_compileAdmitted_iff` proves that `transmuteRefBody src dst`
     is compile-time admissible if and only if `src.size = dst.size`,
     `dst.align ∣ src.align`, `src.WellFormed`, and `dst.WellFormed`.
   - `transmuteRef_source_verified` transfers reference validity from `src` to
     `dst` using `Nat.dvd_trans hAlignDvd hSrcAlignDvd` and `← hSizeEq`, proving
     `MirSem (transmuteRefBody src dst) ≤ EnsuresTransmuteRef src dst` with
     caller precondition `pre := fun _ => True`.
   - Four negative controls
     ([PmeMirSemantics.lean](PmeMirSemantics.lean#L2362-L2562)) prove that:
     - omitting the PME (`transmuteRefNoPmeBody u8Layout u64Layout`) makes the
       body compile-time admissible (`CompileAdmitted`) while triggering runtime
       `.failed .ub` on a 1-byte-aligned `&u8`
       (`negative_control_omitted_pme_rejected`);
     - placing the assertion in an unreached runtime branch (`if false`,
       `transmuteRefDeadBranchBody u8Layout u64Layout`) instead of
       `requiredConsts` fails verification
       (`negative_control_dead_branch_assertion_rejected`);
     - `pub fn broken() { const { assert!(false) }; }` fails `CompileAdmitted`
       and `ConcreteVerifiedAndAdmitted`
       (`negative_control_const_assert_false_not_admitted`); and
     - `pub fn broken_loop() { const { loop {} }; }` fails `CompileAdmitted`
       because every step budget `n` evaluates to `.running`
       (`negative_control_const_loop_not_admitted`).

### 7. Polymorphic Contracts: `InstCtx` and the R1 vs. R2 Analysis

`Basis: source + execution + derived`

A polymorphic public Rust function
`pub fn checked<T: Bound, const N: usize>(x: usize) -> usize` cannot be modeled
as a single unparameterized `MirBody` because four semantic inputs depend on the
monomorphization context `inst : InstCtx` (`rustc_middle::ty::Instance<'tcx>`):

1. **Concrete post-monomorphization layouts (`layoutValid`):** `tcx.layout_of`
   requires concrete type substitutions and can fail during monomorphization if
   a composite size exceeds `isize::MAX`.
2. **Substituted const generic operands (`constN`):** Const generic parameters
   appear as `Operand.constVal` inside MIR statements and `requiredConsts`.
3. **Caller-supplied trait implementations and `LIB-07` semantic contracts
   (`boundTraitContract`):** Associated constants (`<T as Bound>::LIMIT`) and
   trait methods (`<T as Bound>::delta()`) resolve via `Instance::try_resolve`
   against the caller's `impl Bound for T`. While `rustc` checks trait *type*
   conformance, sound verification requires the caller's `impl` to satisfy the
   trait's *semantic* contract (`delta() <= LIMIT ∧ LIMIT <= 1000`).
4. **Monomorphized `Body::required_consts` (`checkedPmeOk`):** Evaluating
   `const { assert!(N <= <T as Bound>::LIMIT); }` depends on both `N` and
   `<T as Bound>::LIMIT`.

In
[PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean#L817-L1157),
we compare two representations under `model-refinement`:

- **Representation R1 (`PolyCapturedFnR1 InstCtx`,
  [PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean#L841-L891)):**
  Models a generic function as an `InstCtx`-indexed family of `MonoMirUnit`s and
  quantifies over `inst : InstCtx` outside `VerificationResultOn`, keeping
  `MirLang.Query := ExecQuery MirState` and scoping
  `tcb : InstCtx → List TCBItem` per monomorphized instance.
- **Representation R2 (`PolyMirLang InstCtx`,
  [PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean#L905-L1099)):**
  Enriches `Language.Query` to
  `PolyQuery InstCtx := InstCtx × ExecQuery MirState` so that instantiation
  preconditions (`instPre`, `noPmePre`) and runtime argument preconditions
  (`argPre`) are both predicates on `PolyQuery InstCtx` inside the unchanged
  `VerificationResultOn` envelope.
- **Two-Pass `model-refinement` Boundary Discovery:**
  - *Pass 1 (Counterexample to naive R2 precondition merging):* Merging
    `instPre`, `noPmePre`, and `argPre` into the naive conjunction
    `naiveTotalPre` (`instPre inst ∧ noPmePre inst ∧ argPre inst q`)
    couples compile-time PME-freedom (`(prog inst).pmeOk`) to the existence of a
    runtime query `q` satisfying `argPre inst q`. Theorem
    `naive_r2_vacuous_argPre_counterexample`
    ([PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean#L1139-L1145))
    proves that `brokenPmeProg` (`pmeOk := False`) vacuously satisfies
    `WellFormedOn (naiveTotalPre ...)` whenever `argPre` is `fun _ _ => False`,
    even though `rustc` evaluates `Body::required_consts` during
    monomorphization regardless of runtime arguments
    (`brokenPmeProg_not_compiled`).
  - *Pass 2 (0-step compile-time query resolution):* In `Trusted.StepResult`,
    `q.steps = 0` represents 0 runtime transition steps, where
    `ReachesPrefix.zero` is the unique derivation and
    `(MirLang.sem body ⟨init, 0⟩).defined` is unconditionally `True`
    (`behaviorOf_defined_at_zero`,
    [PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean#L372-L377)).
    At `q.steps = 0`, `(PolyMirLang.sem prog ⟨inst, ⟨init, 0⟩⟩).defined`
    therefore reduces purely to `(prog inst).pmeOk`. Defining
    `unifiedTotalPre` as
    `instPre inst ∧ noPmePre inst ∧ (q.steps = 0 ∨ argPre inst q)`
    ([PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean#L983-L986))
    eliminates the vacuity defect
    (`refined_r2_rejects_pme_even_when_argPre_empty`,
    [#L1149-L1156](PolymorphicConditionalVerification.lean#L1149-L1156)) and
    yields a constructive two-way equivalence (`↔`) with R1
    (`r1_iff_r2_source_wellFormed`,
    [#L994-L1025](PolymorphicConditionalVerification.lean#L994-L1025)), while
    preserving monomorphic embedding (`mono_embeds_into_r2_iff`) and
    per-instance projection (`r2_projects_to_r1_instance`).

### 8. Three-Way Polymorphic Library Guarantee and Cross-Crate Composition

`Basis: execution + derived`

Sections 6 and 7 of
[PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean#L1159-L2110)
mechanize `pub fn checked<T: Bound, const N: usize>(x: usize) -> usize` and its
cross-crate callers across all three verification guarantees and four negative
controls:

| Scenario / Theorem in `PolymorphicConditionalVerification.lean` | `LIB-07` (`boundTraitContract`) | PME Check (`N ≤ T::LIMIT`) | Runtime `argPre` (`x ≤ 1000`) | Mechanized Outcome |
| :--- | :--- | :--- | :--- | :--- |
| **Guarantee 1: Polymorphic Safety If Compiled** (`checked_polymorphic_safety_if_compiled_r1` `#L1480`, `_r2` `#L1523`) | Assumed (`h_trait`) | Assumed (`h_compiled` / `polyIfCompiledPre`) | Assumed (`checkedArgPre`) | Verified: UB-free across all `steps : Nat` and satisfies `checkedPost` (`ret = x0 + N + T::delta() ≤ x0 + 2 * T::LIMIT`). |
| **Guarantee 2: `NoPME` Sufficiency** (`checked_no_pme_r1` `#L1500`, `_r2` `#L1548`) | Assumed (`h_trait`) | Assumed (`checkedNoPmePre`: `N ≤ T::LIMIT`) | Not needed (`steps = 0`) | Verified: `(MonoRustcCompiler.compile (checkedUnit inst)).defined` holds (`NoPME`). |
| **Guarantee 3: Positive Cross-Crate Client (`client_good`)** (`checked::<TypeA, 1>(50)`, `LIMIT = 10, delta = 3`, `client_good_entry_verified` `#L1931`) | Discharged (`3 ≤ 10 ≤ 1000`) | Discharged (`1 ≤ 10`, `NoPME`) | Discharged (`50 ≤ 1000`) | Verified modularly: derives `NoPME` and `VerificationResultOn` for `client_good::entry` (`ret = .usize 54`) from `checked_total_verified_r1` and `evalCheckedCallee_of_ensuresChecked` without re-proving `checkedMonoBody`. |
| **Negative Control 1: PME Violation (`client_bad_pme`)** (`checked::<TypeB, 1>(50)`, `LIMIT = 0, delta = 0`, `client_bad_entry_fails_to_compile_and_verify` `#L2004`) | Holds (`0 ≤ 0 ≤ 1000`) | Fails (`1 ≰ 0`, PME) | Holds (`50 ≤ 1000`) | Refuted: `¬ (compile (checkedUnit instB1)).defined`, `¬ (compile (clientEntryUnit instB1)).defined`, and `¬ Verified`. |
| **Negative Control 2: `LIB-07` Trait Violation (`client_bad_trait`)** (`checked::<RogueType, 1>(50)`, `LIMIT = 10, delta = usizeMax`, `client_bad_trait_fails_at_runtime` `#L2046`) | Fails (`usizeMax ≰ 10`) | Holds (`1 ≤ 10`, compiles without PME) | Holds (`50 ≤ 1000`) | Refuted: compiles without PME (`instRogue_compiles_without_pme`), but overflows in `bb1` at step 5 (`.failed .contractViolation`), refuting `WellFormedOn (checkedArgPre instRogue)`. |
| **Negative Control 3: Runtime Argument Violation (`client_bad_arg`)** (`checked::<TypeA, 1>(usizeMax)`, `client_bad_arg_refutes_unconditional_wellFormed` `#L2092`) | Holds (`3 ≤ 10 ≤ 1000`) | Holds (`1 ≤ 10`, `NoPME`) | Fails (`usizeMax ≰ 1000`) | Refuted: overflows in `bb0` at step 2 (`.failed .contractViolation`), refuting unconditional `MonoMirLang.WellFormed`. |
| **Negative Control 4: Empty `argPre` with PME (`brokenPmeProg`)** (`refined_r2_rejects_pme_even_when_argPre_empty` `#L1149`) | Holds (`True`) | Fails (`pmeOk = False`) | Empty (`False`) | Discriminates R2 preconditions: `naiveTotalPre` accepts vacuously (`#L1139`), whereas `unifiedTotalPre` rejects at `q.steps = 0`. |

## Boundaries

- **Full CTFE interpreter fidelity (`not examined`):** `ConstMirMachine` in
  [PmeMirSemantics.lean](PmeMirSemantics.lean#L1003-L1005) executes the MIR
  fragment needed for arithmetic assertions, layout queries (`size_of`,
  `align_of`), and control flow (`SwitchInt`, `panic`, `goto`, `return_`). It
  does not model heap allocation inside `const` evaluation, `const` trait
  methods, or pointer-to-integer casts in CTFE (which `rustc`'s Miri-based CTFE
  engine rejects or restricts separately).
- **Subprocess `--emit=mir` vs. in-process `rustc_driver` extraction
  (`known not to apply` for default `--emit=mir`):** Textual `rustc --emit=mir`
  at default `-Z mir-opt-level=1` omits `body.required_consts` and
  `body.mentioned_items` metadata headers, erases unit-typed
  `_2 = const ...::{constant#0};` assignments via dead-store elimination, and
  folds away `if false { callee(); }` via `SimplifyConstCondition`. Sound PME
  extraction therefore requires either in-process `TyCtxt` queries
  (`post_cleanup_body.required_consts()`, `ty::Instance::try_resolve`, and
  `tcx.mir_for_ctfe`) or passing `-Z mir-opt-level=0` and resolving constant
  operands from reachable basic blocks.
- **Unwinding vs. aborting semantics (`not examined`):** Both mechanizations
  treat `Terminator.panic` and `Terminator.assertNotOverflow` failure as
  `.failed .contractViolation` (`isSafe = False`), matching Anneal's
  total-correctness / panic-freedom verification contract rather than modeling
  stack unwinding recovery.

## Evidence

### Preserved Package Artifacts

1. **[PmeMirSemantics.lean](PmeMirSemantics.lean)** (2,563 lines, SHA-256
   `c93ee5252538031e0953e154800573701515a564d86f7bbc2083a59ad0f2cc7f`):
   - Section 1 (`#L68-L274`): `Partial.bot`, `Behavior.when`, `Behavior.given`,
     and `behavior_when_given_adjunction` (zero axioms).
   - Section 2 (`#L276-L562`): `SmallStepMachine.withAdmitted`,
     `totalStep_withAdmitted`, `inhabitedDemonic_withAdmitted`,
     `reachesPrefix_withAdmitted_iff`, and `behaviorOf_withAdmitted_le_iff`.
   - Section 3 (`#L564-L724`): `TyLayout`, `MirTy`, `MirVal`, `Rvalue`
     (`.addrOfDeref`, `.castPtrToPtr`, `.reborrowShared`), `ConstMirBody`, and
     `MirBody` (`requiredConsts`, `requiredLayouts`).
   - Section 4 (`#L726-L1338`): `evalBlocksStep`, `MirMachine`,
     `ConstMirMachine`, `CtfeAdmitted`, `MirBody.CompileAdmitted`,
     `PartialCompiler.SoundOn.verify`, `mirSemAdmitted_le_iff`,
     `ConcreteVerifiedAndAdmitted`, and `GenericVerifiedWithDomain`.
   - Section 5 (`#L1340-L2563`): `constBoundedAdd_compileAdmitted_iff`,
     `constBoundedAdd_source_verified`, `transmuteRef_compileAdmitted_iff`,
     `transmuteRef_source_verified`, and Negative Controls 1–4.
2. **[PolymorphicConditionalVerification.lean](PolymorphicConditionalVerification.lean)**
   (2,110 lines, SHA-256
   `9b7d816ea84413422941fdc4609b0939cc827ec413375d20314208cbf3207495`):
   - Section 1 (`#L80-L274`): Layer 1A definitions (`Partial`, `Language`,
     `SpecOn`, `WellFormedOn`, `Compiler.Verified`, `VerificationResultOn`,
     `specOn_antitone_pre`, `Compiler.Verified.mono`).
   - Section 2 (`#L276-L618`): Layer 1B small-step machine,
     `behaviorOf_defined_at_zero`, `CheckedInstCtx`, and `evalMirStep`.
   - Section 3 (`#L620-L815`): `MonoMirUnit`, `MonoMirLang`, `semIfCompiled`,
     `semTotalCompiled`, `semIfCompiled_le_iff`,
     `semTotalCompiled_le_iff_of_defined`, `defined_of_semTotalCompiled_le`, and
     `verifiedTotal_iff_noPme_and_verifiedIfCompiled`.
   - Section 4 (`#L817-L1099`): Representation R1 (`PolyCapturedFnR1`,
     `polyTotalVerifiedR1_of_ifCompiled_and_noPme`) vs. Representation R2
     (`PolyMirLang`, `unifiedTotalPre`, `r1_iff_r2_source_wellFormed`,
     `mono_embeds_into_r2_iff`, `r2_projects_to_r1_instance`,
     `r2_total_verified_of_ifCompiled_and_noPme`).
   - Section 5 (`#L1101-L1157`): `brokenPmeProg`,
     `naive_r2_vacuous_argPre_counterexample`, and
     `refined_r2_rejects_pme_even_when_argPre_empty`.
   - Sections 6–7 (`#L1159-L2110`): `checked<T: Bound, const N: usize>`,
     Guarantees 1–3 (`checked_polymorphic_safety_if_compiled_r1`,
     `checked_no_pme_r1`, `client_good_entry_verified`), and Negative Controls
     1–3 (`client_bad_entry_fails_to_compile_and_verify`,
     `client_bad_trait_fails_at_runtime`,
     `client_bad_arg_refutes_unconditional_wellFormed`).

### Primary Source Coordinates

- **`joshlf/anneal@e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`:**
  - [`trusted/lean/Trusted/Refinement.lean#L1-L245`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/lean/Trusted/Refinement.lean#L1-L245)
  - [`trusted/lean/Trusted/StepResult.lean#L1-L150`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/lean/Trusted/StepResult.lean#L1-L150)
  - [`trusted/lean/Trusted/MirAst.lean#L1-L140`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/lean/Trusted/MirAst.lean#L1-L140)
  - [`trusted/lean/Trusted/MirSemantics.lean#L1-L280`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/lean/Trusted/MirSemantics.lean#L1-L280)
  - [`trusted/rustc-capture/src/lib.rs#L84-L91`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/rustc-capture/src/lib.rs#L84-L91)
- **`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`:**
  - [`compiler/rustc_middle/src/mir/mod.rs#L278-L295`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L278-L295)
    (`Body::required_consts` and `Body::mentioned_items` declarations)
  - [`compiler/rustc_mir_build/src/builder/matches/mod.rs#L206-L214`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/mod.rs#L206-L214)
    and
    [`compiler/rustc_mir_build/src/builder/matches/test.rs#L136-L141`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/test.rs#L136-L141)
    (`if` and `match` lowering to `TerminatorKind::SwitchInt`)
  - [`compiler/rustc_mir_build/src/builder/scope.rs#L563-L565`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs#L563-L565)
    and
    [`#L823-L830`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs#L823-L830)
    (`loop {}` and `return`/`break`/`continue` allocating zero-predecessor
    blocks via `start_new_block`)
  - [`compiler/rustc_mir_transform/src/simplify.rs#L81-L377`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify.rs#L81-L377)
    (`SimplifyCfg::Initial` and `remove_dead_blocks`)
  - [`compiler/rustc_mir_transform/src/required_consts.rs#L9-L23`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/required_consts.rs#L9-L23)
    (`RequiredConstsVisitor::compute_required_consts`)
  - [`compiler/rustc_mir_transform/src/mentioned_items.rs#L40-L85`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/mentioned_items.rs#L40-L85)
    (`MentionedItemsVisitor`)
  - [`compiler/rustc_mir_transform/src/simplify_branches.rs#L30-L98`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify_branches.rs#L30-L98)
    (`SimplifyConstCondition`)
  - [`compiler/rustc_monomorphize/src/collector.rs#L1364-L1389`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1364-L1389)
    and
    [`#L1753-L1792`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1753-L1792)
    (`collect_items_of_instance` and `RootCollector::is_root`)
  - [`compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L114-L118`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L114-L118)
    (`reachable_non_generics_helper` excluding `cross_crate_inlinable` items)

## Revalidation

1. **Re-verify the preserved Lean 4.34.1 mechanizations:**
   Run the Lean 4 (`v4.34.1`) kernel checker with asynchronous elaboration and
   kernel-check skipping disabled from this package directory:
   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false PmeMirSemantics.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false PolymorphicConditionalVerification.lean
   ```
   Both commands must exit with status `0` and produce zero warnings or errors.
2. **Revalidate `rustc` MIR pass ordering and dead-branch vs. post-divergence
   PME behavior on a newer `rustc` revision:**
   Compile a minimal probe containing `if false`, `match false`, and `return;`
   followed by `const { assert!(N <= 1000); }` instantiated at `N = 2000` with
   `rustc --emit=obj` and
   `rustc -Z dump-mir=Built,SimplifyCfg-initial,RemovePlaceMention`.
   Verify whether `RequiredConstsVisitor` (`mir_promoted`) and `MentionedItems`
   (`inner_optimized_mir`) still execute after `SimplifyCfg::Initial` and before
   `SimplifyConstCondition`, and check `reachable_non_generics_helper` in
   `compiler/rustc_codegen_ssa/src/back/symbol_export.rs` to confirm whether
   `cross_crate_inlinable` functions remain excluded from `--crate-type=lib`
   monomorphization roots.
