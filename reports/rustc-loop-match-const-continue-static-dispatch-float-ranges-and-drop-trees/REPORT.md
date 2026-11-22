# `rustc` `#![feature(loop_match)]` and `#[const_continue]`: Static `ValTree` Target Resolution, IEEE-754 Float-Range Parity, `Or`-Pattern Rebinding, and `FalseEdge` Scope `DropTree` Lowering

## Summary

`rustc`'s unstable `#![feature(loop_match)]` and `#[const_continue]` attributes (tracking issue `rust-lang/rust#132306`) compile state-machine loops of the canonical shape `#[loop_match] loop { state = 'blk: { match state { ... } }; }` by resolving constant state transitions to target arm basic blocks during MIR construction rather than relying on downstream LLVM jump-threading. Direct primary-source inspection across `rust-lang/rust` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), live `rustc`/`MIR`/`LLVM`/`Miri` (`-Zmiri-tree-borrows`) execution (`support/probe_loop_match_and_const_continue.py`), and a constructive kernel-checked Lean `v4.34.1` formalization (`support/LoopMatchConstContinueAndDropTreeSoundness.lean`) establish seven core findings:

1. **Structural and Type Gating (`rustc_hir_typeck`, THIR lowering, and MIR build):** `#[loop_match]` requires an unprojected local-variable scrutinee (`Res::Local(hir_id)` with `!is_upvar`) assigned back to that exact same local (`LoopMatchInvalidMatch`, `LoopMatchInvalidUpdate`), restricts the state type via `is_supported_loop_match_type` to `Uint | Int | Float | Bool | Char` and fieldless `Enum`s (`LoopMatchUnsupportedType`), rejects all arm guards (`LoopMatchArmWithGuard`), and restricts `#[const_continue]` operands to monomorphic literals, fieldless ADT constructors, or `NamedConst` items (rejecting `ConstParam` and `ConstBlock` via `ConstContinueNotMonomorphicConst`, and rejecting labels outside the enclosing `#[loop_match]` labeled block via `ConstContinueBadLabel`).
2. **Direct `state_place` Write, Liveness Read, `FalseEdge`, and Dual `DropTree` Lowering:** Unlike normal arm exits and ordinary `break 'blk` (which stage values through a fresh `state_result_place` temporary to avoid self-assign overlap before copying into `state_place` and branching to `loop_block`), `break_const_continuable_scope` evaluates the target constant to a `ValTree`, resolves `real_target = sub_branch.success_block` via `static_pattern_match`, writes `state_place` directly via `expr_into_dest`, emits a liveness read (`Rvalue::Discriminant(state_place)` for fieldless enums; `Rvalue::Use(Operand::Copy(state_place), WithRetag::Yes)` for primitives), terminates with `TerminatorKind::FalseEdge { real_target: drop_and_continue_block, imaginary_target }`, and builds two structurally parallel `DropTree`s over `scopes[stack_index + 1..]`: `const_continue_drops` on `imaginary_target` (merging into `loop_block` so borrowck remains oblivious to static jump-threading precision) and a private exit `DropTree` on `drop_and_continue_block` jumping directly to `real_target` (bypassing the loop-header `SwitchInt`). `CleanupPostBorrowck` later lowers `FalseEdge` to `TerminatorKind::goto(real_target)`, dead-eliminating the entire `imaginary_target` tree. On a live runtime-input 3-state byte-stream DFA, this eliminates the loop-header state-dispatch `switch` completely in both `runtime-optimized` MIR (`6 -> 5` `switchInt`, `1 -> 0` `discriminant`) and `-C opt-level=2` LLVM IR (`1 -> 0` `switch`, `14 -> 11` basic blocks), whereas an identical plain `loop` retains the centralized `switch` even at `-O2`.
3. **Exact Inner-to-Outer Lexical LIFO Destruction and Unwind Continuity:** Folding `scopes[stack_index + 1..].iter().flat_map(|s| &s.drops)` from `ROOT_NODE` via `DropTree::add_drop` reverses both scope nesting and intra-scope declaration order, guaranteeing exact lexical LIFO destruction before `real_target` entry (`DROPS=["arm0_inner", "arm0_outer", "arm1"]` under native execution and `Miri -Zmiri-tree-borrows`) while `build_exit_tree` wires every `DropKind::Value` block into `unwind_drops` so panics inside an inner destructor still drop outer live arm guards (`LOG=["arm0_inner_panics", "arm0_outer"]`).
4. **IEEE-754 Float-Range Total Parity (`-0.0`, `+0.0`, `±inf`, `NaN`):** `rustc_pattern_analysis` lowers float literals to singleton `F{16,32,64,128}Range(v, v, Included)` and open-ended ranges (`0.0..`, `..0.0`) by substituting `±INFINITY` (with THIR enforcing non-twice-open ranges and `RangeEnd::Included` for `lo..`). Under those exact THIR invariants, static `(*l..=*h).contains(&actual)` / `(*l..*h).contains(&actual)` (`rustc_apfloat`) and dynamic MIR `BinOp::{Eq,Le,Lt}` (`TestKind::{ScalarEq,Range}`) agree on all $2^{32}$ binary32 bit patterns: `-0.0_f32` (`0x8000_0000` = `2147483648`) jumps statically to `0.0 =>` and `0.0.. =>` while preserving its negative-zero bit pattern in `state_place` and `@`-bindings, whereas every `NaN` fails every float range and routes to `_ =>`.
5. **`Or`-Pattern `sub_branches` Rebinding and Confirmed Compiler ICE on Nested Binding-Wrapped `Or`:** For flat top-level `Or`-patterns (`x @ 0 | x @ 2`, `x @ (0 | 2)`, `0 | 2`), `static_pattern_match` indexes `branch.sub_branches.get(pat.idx).or_else(|| branch.sub_branches.last())`, jumping to `sub_branch.success_block` where `bind_matched_candidate_for_arm_body` copies the freshly written `state_place` into `x` (`OR_BIND=22`). However, because `expand_or_pat` only peels direct `PatKind::Or` without recursing through `PatKind::Binding { subpattern: Some(...) }` while `static_pattern_match` peels only one `Constructor::Or` layer, nested binding-wrapped `Or`-patterns such as `(x @ (0 | 1)) | x @ 2` trigger an internal compiler error (`exit 101`, `unsupported pattern constructor Or` at `matches/mod.rs:2996` / `3023`).
6. **Empirically Confirmed `Drop`-Enum State-Overwrite Divergence in `rustc`:** `is_supported_loop_match_type` admits any fieldless enum without checking `!ty.needs_drop`, yet neither normal `#[loop_match]` state updates (`into.rs:383-391`) nor `#[const_continue]` updates (`scope.rs:999`) emit `TerminatorKind::Drop { replace: true }` (`drop_and_replace`) before overwriting `state_place`. Consequently, for a fieldless enum implementing `Drop`, both `#[const_continue]` and normal `break 'blk` inside `#[loop_match]` silently omit `Drop::drop` on the overwritten state value (`LM_CONST_CONTINUE = LM_NORMAL_BREAK = ["armA_inner", "armA_outer", "armB", "drop_S::B"]` vs `PLAIN_LOOP = ["armA_inner", "armA_outer", "drop_S::A", "armB", "drop_S::B"]`, reproduced under both native execution and `Miri -Zmiri-tree-borrows`). Observational equivalence with plain `loop` therefore holds **iff** `!needs_drop(state_ty)`.
7. **Trusted MIR Boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) and Mechanized Proof:** Because `CleanupPostBorrowck` erases `FalseEdge` and `FalseUnwind` into `Goto` before `Runtime(PostCleanup)` / `ElaborateDrops` MIR capture, integer and fieldless-enum `#[loop_match]` bodies without active `Drop` terminators require no `FalseEdge` support in `Trusted.MirAst`; conversely, `Float`, `Char`, and `TerminatorKind::Drop` currently fail closed as `.unsupported` in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`. All 11 primary theorems and sharpness counterexamples in `support/LoopMatchConstContinueAndDropTreeSoundness.lean` (`517` declarations) pass `Lean v4.34.1` kernel checking with `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, and `0` `._unsafe_rec`.

## Applicability

This report characterizes the exact combination of five durable upstream artifacts recorded in `REPORT.json`, and distinguishes source-audited revisions from live execution hosts:

- **Primary-source `rust-lang/rust` revisions (`source`):**
  - `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`rust-lang/rust` HEAD as of `2026-11-22`): primary source audit for all line-range citations in `compiler/rustc_hir_typeck/src/loops.rs`, `compiler/rustc_mir_build/src/thir/cx/expr.rs`, `compiler/rustc_mir_build/src/thir/pattern/mod.rs`, `compiler/rustc_mir_build/src/builder/expr/{into,stmt}.rs`, `compiler/rustc_mir_build/src/builder/scope.rs`, `compiler/rustc_mir_build/src/builder/matches/{mod,test}.rs`, `compiler/rustc_pattern_analysis/src/rustc.rs`, `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`, and `tests/ui/loop-match/*`.
  - `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`, `LLVM 23.1.5`): programmatically SHA-256 compared and unified-diffed against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`. `loops.rs` (`df043168...`) and `matches/mod.rs` (`391fb840...`) are byte-for-byte identical between `3ef0c22cd` and `342d74463`; the only deltas in `into.rs` (3 lines in unrelated `write_via_move` intrinsic matching at lines 407–437) and `scope.rs` (6 lines in unrelated `dropline_to` debug assertions in `build_scope_drops` at line 1907) do not touch any `loop_match` or `const_continue` code.
  - `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, `LLVM 22.1.6`, `miri 0.1.0`): both source-diffed against `342d74463` and executed live on `x86_64-unknown-linux-gnu`. Across `14210df0e` and `342d74463`, `is_supported_loop_match_type`, `ExprKind::LoopMatch` lowering, `break_const_continuable_scope`, `in_const_continuable_scope`, `static_pattern_match`, and `static_pattern_match_inner` implement the exact same algorithms; line numbers shift slightly (`static_pattern_match_inner`'s `Constructor::Or` panic is line `3023` in `14210df0e` vs `2996` in `3ef0c22cd`/`342d74463`), and `rustc_hir_typeck/src/loops.rs` gained `OrdSpan` and `UnlabeledBlock { wrap_end }` unrelated to `Context::LoopMatch`.
- **Execution environment (`execution`):**
  - All 18 probe cases in `support/probe_loop_match_and_const_continue.py` (producing `support/probe_results.json`) were executed live on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with `LLVM 22.1.6`, `--edition=2024`, `-C opt-level=0` and `-C opt-level=2`, `-Z dump-mir`, and `miri 0.1.0 (14210df0e2 2026-05-31)` with `-Zmiri-tree-borrows` on `x86_64-unknown-linux-gnu`.
  - Cross-toolchain behavioral alignment with `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11, LLVM 23.1.5)` is established directly for source semantics via the zero-diff audit above and by matching diagnostic text, drop order (`["arm0_inner", "arm0_outer", "arm1"]`), IEEE-754 outputs (`NEG_ZERO=("zero_arm", 2147483648)`, `NAN=nan_wildcard`, `OR_BIND=22`), and `-O0` LLVM branch-count reduction (`br: 9` vs `11` on `3ef0c22cd`/`LLVM 23.1.5` and `br: 4` vs `6` on our compact `step_loop_match` vs `step_plain_loop` under `14210df0e`/`LLVM 22.1.6`). Note that LLVM IR instruction counts are LLVM-version- and function-body-sensitive; counts reported in `support/probe_results.json` come exclusively from live execution on `LLVM 22.1.6` unless explicitly labeled as `3ef0c22cd` / `LLVM 23.1.5`.
- **Trusted MIR verifier boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `source`):**
  - Connects `rustc`'s MIR lowering stages directly to `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` (which pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` in `driver.rs:25`).
- **Mechanized proof artifact (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, `derived` + `execution`):**
  - `support/LoopMatchConstContinueAndDropTreeSoundness.lean` is a standalone, zero-import Lean `v4.34.1` model of `rustc`'s `#[loop_match]` / `#[const_continue]` semantics, `DropTree` fold, and IEEE-754 binary32 range predicates. It does **not** import `joshlf/anneal`'s `Trusted.MirSemantics`; its claims apply to any MIR semantics matching the modeled abstract transitions, subject to the exact preconditions documented under **Findings** and **Boundaries** (notably `!needs_drop(state_ty)`, guard-free arms, flat top-level `Or`-patterns, and non-NaN THIR range bounds).

## Findings

### 1. Frontend Validation, HIR Context Tracking, and THIR Structural Gating

Basis: source + execution

`#[loop_match]` and `#[const_continue]` enforce their structural invariants across three distinct compiler stages before MIR code generation begins:

1. **HIR Loop-Context Checking (`compiler/rustc_hir_typeck/src/loops.rs:44-49, 153-160, 219-241, 439-465`, commit `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):**
   - `Context::LoopMatch { labeled_block: Destination }` (lines 44–49) tracks the `Destination` of the inner labeled block (not the outer `loop`).
   - When `CheckLoopVisitor::visit_expr` enters `hir::ExprKind::Loop(b, _, source, _)` (lines 153–160), it calls `is_loop_match(e, b)` (lines 439–465). `is_loop_match` checks `find_attr!(self.tcx, e.hir_id, LoopMatch(_))`, requires the loop body to contain either a single trailing expression `state = expr` or a single statement `state = expr;`, requires `hir::ExprKind::Assign(_, rhs_expr, _)`, and requires `rhs_expr` to be `hir::ExprKind::Block(block, label)`, returning `Some(Destination { label, target_id: Ok(block.hir_id) })`.
   - When `visit_expr` visits `hir::ExprKind::Break(break_destination, _)` annotated with `ConstContinue(_)` (lines 219–241), it first requires `break_destination.label` to be `Some(label)`, and then walks `self.cx_stack.iter().rev()` checking that some enclosing `Context::LoopMatch { labeled_block }` has `break_destination.target_id == labeled_block.target_id` (matching by `HirId` rather than label `Span` so macro hygiene works cleanly). Failure emits fatal `ConstContinueBadLabel` (empirically verified in `c4f_reject_bad_label`: ``error: `#[const_continue]` must break to a labeled block that participates in a `#[loop_match]` ``).
   - Because `require_break_cx` (line 351) accepts `LoopMatch { .. }` alongside `Loop(_)`, ordinary labeled breaks to `'outer` or `'blk` remain legal inside `#[loop_match]`.

2. **THIR Lowering and Scrutinee Place Restrictions (`compiler/rustc_mir_build/src/thir/cx/expr.rs:1010-1028, 1075-1155`, commit `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):**
   - `hir::ExprKind::Break` with `ConstContinue(_)` lowers to `thir::ExprKind::ConstContinue { label: region::Scope { local_id: target_id.local_id, data: region::ScopeData::Node }, value }` (lines 1011–1025), rejecting missing label or missing break expression via fatal `ConstContinueMissingLabelOrValue`.
   - `hir::ExprKind::Loop` with `LoopMatch(_)` validates the full syntactic skeleton (lines 1076–1155):
     * No extra statements in the loop body (`LoopMatchMissingAssignment`, `LoopMatchBadStatements`);
     * RHS must be a block whose statements are restricted to `StmtKind::Item(_)` only (line 1104) and whose tail expression is `hir::ExprKind::Match(scrutinee, arms, _)` (`LoopMatchBadRhs`);
     * The helper `local(cx, expr)` (lines 1118–1130) checks `hir::ExprKind::Path(QPath::Resolved(_, path))` with `Res::Local(hir_id)` AND `!cx.is_upvar(hir_id)`. Both the match `scrutinee` and the assignment LHS `state` must resolve to the **exact same non-upvar local variable** (`LoopMatchInvalidMatch` at line 1133; `LoopMatchInvalidUpdate` at line 1137).
   - **Why projected places and closure upvars are rejected:** Restricting `state_place` to a bare `Local` with zero `PlaceElem` projections guarantees that `state_place.as_local().unwrap()` succeeds in `scope.rs:943`, that reading or overwriting `state_place` cannot dereference a pointer, index a slice, or trigger projection-evaluation UB/panics, and that the scrutinee and assignment target cannot alias different projections or captured environment slots. Empirically verified by `c4c_reject_projected_place` (`match h.s` fails with `error: invalid match on #[loop_match] state` / `note: a local variable must be the scrutinee within a #[loop_match]`) and `c4g_reject_mismatched_update` (`s2 = 'blk: { match s1 { ... } }` fails with `error: invalid update of the #[loop_match] state`).

3. **MIR-Build State-Type and Arm-Guard Gates (`compiler/rustc_mir_build/src/builder/expr/into.rs:270-287, 314-324`, commit `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):**
   - `is_supported_loop_match_type` (lines 270–281):
     ```rust
     fn is_supported_loop_match_type(ty: Ty<'_>) -> bool {
         match ty.kind() {
             ty::Uint(_) | ty::Int(_) | ty::Float(_) | ty::Bool | ty::Char => true,
             ty::Adt(adt_def, _) => match adt_def.adt_kind() {
                 ty::AdtKind::Struct | ty::AdtKind::Union => false,
                 ty::AdtKind::Enum => {
                     adt_def.variants().iter().all(|v| v.fields.is_empty())
                 }
             },
             _ => false,
         }
     }
     ```
     Every other type (structs, unions, enums with any field, tuples, references, slices, `&str`, arrays, closures) triggers fatal `LoopMatchUnsupportedType` (verified in `c4b_reject_payload_enum`: `enum E { A(u8), B }` emits `only integers, floats, bool, char, and enums without fields are supported`).
   - **Why payload ADTs and structs are excluded:** `static_pattern_match_inner` (`matches/mod.rs:2921-3008`) intentionally does **not** recurse into compound pattern constructors (`Struct`, `Ref`, `Slice`, `UnionField`, `DerefPattern`, `Str` all hit `bug!`). Restricting the state type to flat scalars and fieldless enums ensures every valid value reduces to a single scalar leaf or a single-element `ValTreeKind::Branch([Leaf(variant_idx)])` without sub-place projections or partial-move drop flags.
   - **Why match guards are unconditionally forbidden (`into.rs:318-321`):** Every arm is checked for `arm.guard.is_some()` and rejected with fatal `LoopMatchArmWithGuard` (verified in `c4a_reject_arm_guard`). Because `static_pattern_match` selects a single static `sub_branch.success_block` solely from the target constant's `ValTree`, it cannot evaluate runtime guard expressions, cannot observe guard side effects, and cannot fall through to subsequent arms when a guard returns `false` (formalized sharply in Lean theorem `ce1_arm_guard_side_effect_breaks_static_dispatch`).

| Gate | Stage & Primary Source (`342d74463`) | Diagnostic Struct | Live Probe Case (`probe_results.json`) |
| :--- | :--- | :--- | :--- |
| Arm guard (`0 if true =>`) | MIR build (`into.rs:318-321`) | `LoopMatchArmWithGuard` | `c4a_reject_arm_guard` (`rc=1`) |
| Payload enum (`enum E { A(u8), B }`) | MIR build (`into.rs:270-287`) | `LoopMatchUnsupportedType` | `c4b_reject_payload_enum` (`rc=1`) |
| Projected place (`match h.s`) | THIR build (`thir/cx/expr.rs:1118-1134`) | `LoopMatchInvalidMatch` | `c4c_reject_projected_place` (`rc=1`) |
| Mismatched target (`s2 = ... match s1`) | THIR build (`thir/cx/expr.rs:1136-1141`) | `LoopMatchInvalidUpdate` | `c4g_reject_mismatched_update` (`rc=1`) |
| Const generic param (`break 'blk NEXT`) | MIR build (`scope.rs:917-930`) | `ConstContinueNotMonomorphicConst` (`ConstantParameter`) | `c4d_reject_const_param` (`rc=1`) |
| Inline const block (`break 'blk const { 1 }`) | MIR build (`scope.rs:917-930`) | `ConstContinueNotMonomorphicConst` (`ConstBlock`) | `c4e_reject_const_block` (`rc=1`) |
| Non-loop-match label (`break 'outer`) | HIR typeck (`loops.rs:220-240`) | `ConstContinueBadLabel` | `c4f_reject_bad_label` (`rc=1`) |
| Manual `PartialEq` const pattern (`PAT_A`) | MIR pattern check (`const_to_pat`) | non-structural constant error | `c2_opaque_manual_partial_eq_rejection` (`rc=1`) |

### 2. MIR Construction of `ExprKind::LoopMatch` vs `break_const_continuable_scope`, `FalseEdge`, and Dual `DropTree`s

Basis: source + execution

#### 2.1 Normal Exit Staging (`state_result_place`) vs Direct `#[const_continue]` Write (`state_place`)

In `compiler/rustc_mir_build/src/builder/expr/into.rs:289-403` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), lowering `ExprKind::LoopMatch` constructs three nested scopes inside the outer loop's `in_breakable_scope(Some(loop_block), destination, ...)`:

1. **Loop header (`loop_block` -> `body_block`):** Emits `TerminatorKind::FalseUnwind { real_target: body_block, unwind: UnwindAction::Continue }`, lowers the scrutinee (`lower_scrutinee`, emitting `PlaceMention(state_place)`), and builds the match decision tree (`lower_match_tree(..., Exhaustive::Yes)` -> `built_tree`).
2. **Staging temporary (`state_result_place`, lines 338–340):** Allocates a fresh temporary `let state_result = this.temp(state_ty, expr_span); let state_result_place = Place::from(state_result);`. Normal arm completion and non-`#[const_continue]` `break 'blk expr` write into `state_result_place` inside the innermost `in_breakable_scope(None, state_result_place, ...)`. Only after `lower_match_arms` rejoins does `into.rs:383-391` copy `state_result_place` back to `state_place`:
   ```rust
   this.cfg.push_assign(
       block,
       source_info,
       state_place,
       Rvalue::Use(this.consume_by_copy_or_move(state_result_place), WithRetag::Yes),
   );
   ```
   This staging prevents overlapping self-assignments (`state = state`, regression-tested in upstream `tests/ui/loop-match/no-self-assign-ice.rs` for `rust-lang/rust#143806`).
3. **Middle `in_const_continuable_scope` (`scope.rs:585-634`):** Wraps the inner `in_breakable_scope`, storing `ConstContinuableScope { region_scope, state_place, arms, built_match_tree, const_continue_drops: DropTree::new() }`. When `in_const_continuable_scope` pops, it calls `build_exit_tree(const_continue_scope.const_continue_drops, region_scope, span, None)` (lines 609–614) and joins its root with `normal_exit_block` into a fresh `target` block (lines 618–631), which then exits `in_scope(region_scope)` and executes `this.cfg.goto(body_block, source_info, loop_block)` (`into.rs:399`).

#### 2.2 Step-by-Step Lowering of `#[const_continue] break 'blk value`

`compiler/rustc_mir_build/src/builder/expr/stmt.rs:101-103` dispatches `ExprKind::ConstContinue { label, value }` to `Builder::break_const_continuable_scope` (`compiler/rustc_mir_build/src/builder/scope.rs:869-1047`):

1. **Monomorphic Constant Extraction (lines 879–932):** Unwraps the mandatory `ExprKind::Scope` wrapper around `value` and accepts only:
   - `ExprKind::Adt(AdtExpr { variant_index, fields, base, .. })` (asserting `base == AdtExprBase::None` and `fields.is_empty()`), directly synthesizing `Const::Ty(ty, ty::Const::new_value(tcx, ValTree::from_branches([ValTree::from_scalar_int(variant_index.as_u32())]), ty))`;
   - `ExprKind::Literal | NonHirLiteral | ZstLiteral | NamedConst`, lowered via `self.as_constant(...)`.
   - Any other expression (`ConstParam`, `ConstBlock`, local variable, function call) emits `ConstContinueNotMonomorphicConst` and aborts lowering of the statement (verified by `c4d_reject_const_param` and `c4e_reject_const_block`).
2. **`ValTree` Evaluation & Static Target Resolution (lines 957–995):** Evaluates `constant` via `eval_unevaluated_mir_constant_to_valtree` (asserting `!ty.has_param()`, emitting `ConstContinueBadConst` on `ErrorHandled::TooGeneric`), constructs a temporary `RustcPatCtxt` over a `DroplessArena` (`typing_env: post_typeck_through_borrowck_for_mir_build`, `known_valid_scrutinee: true`), and calls `self.static_pattern_match(&cx, valtree, &*scope.arms, &scope.built_match_tree)`. If `None` is returned (e.g., an opaque pattern that cannot be matched structurally), emits fatal `ConstContinueUnknownJumpTarget`.
3. **Direct `state_place` Write & Liveness Read (lines 945–953, 997–1007):**
   - Executes `block = self.expr_into_dest(state_place, block, value).into_block();` writing the new state directly into `state_place` **before** dropping arm-local variables and **before** jumping to `real_target`. This write is semantically mandatory because `real_target` (`sub_branch.success_block`) executes arm bindings (such as `x @ 0 | x @ 2` reading `state_place`) without re-entering the loop header.
   - Emits `self.cfg.push_assign(block, source_info, discr, rvalue)` where `rvalue` is `Rvalue::Discriminant(scope.state_place)` for fieldless enums and `Rvalue::Use(Operand::Copy(scope.state_place), WithRetag::Yes)` for primitives. This synthetic read ensures `state_place` is visibly read along the `#[const_continue]` path for unused-assignment analysis and borrowck liveness, even when the destination arm does not bind or read `state_place`.
4. **`FalseEdge` + Dual `DropTree` Construction (lines 1008–1046):**
   - Allocates `drop_and_continue_block` and `imaginary_target`, terminating `block` with:
     ```rust
     TerminatorKind::FalseEdge { real_target: drop_and_continue_block, imaginary_target }
     ```
   - **Imaginary-edge `DropTree` (for borrowck, lines 1016–1025):** Folds `self.scopes.scopes[stack_index + 1..].iter().flat_map(|scope| &scope.drops)` into `scope.const_continue_drops`, registers `imaginary_target` as an entry point, and plants a placeholder `TerminatorKind::UnwindResume` (later overwritten to `goto` by `ExitScopes::link_entry_point` at `scope.rs:2110-2120` when `in_const_continuable_scope` calls `build_exit_tree(..., None)`). Because `const_continue_drops` merges into `loop_block`, borrowck sees a CFG path from every `#[const_continue]` back to the loop header and hence into every match arm, guaranteeing that borrowck acceptance/rejection does not depend on static jump-threading precision.
   - **Real-edge `DropTree` (for runtime execution, lines 1027–1044):** Allocates a **fresh local `DropTree::new()`**, executes the exact same fold over `self.scopes.scopes[stack_index + 1..]`, registers `drop_and_continue_block` as its entry point with a placeholder `UnwindResume`, and immediately calls `self.build_exit_tree(drops, region_scope, span, Some(real_target))`! Passing `Some(real_target)` as `continue_block` makes `ROOT_NODE` jump directly to `real_target` (`sub_branch.success_block`), bypassing `loop_block` and the loop-header `SwitchInt`.

#### 2.3 Verbatim Observed MIR (`built.after` -> `CleanupPostBorrowck` -> `runtime-optimized`) and LLVM CFG Comparison

Live MIR dumping of `drop_order_loop_match` (`rustc 1.98.0-nightly`, `14210df0e`) confirms every single block emitted by `scope.rs:997-1046`:

```mir
    bb11: {                              // Arm 0 body
        StorageLive(_8);
        _8 = Guard(const "arm0_outer");
        FakeRead(ForLet(None), _8);
        StorageLive(_10);
        _10 = Guard(const "arm0_inner");
        FakeRead(ForLet(None), _10);
        _5 = const 1_u8;                 // Direct expr_into_dest(state_place, ...)
        _11 = copy _5;                   // Synthetic Copy liveness read
        falseEdge -> [real: bb12, imaginary: bb13];
    }
    bb12: { goto -> bb14; }              // drop_and_continue_block -> real DropTree
    bb13: { goto -> bb27; }              // imaginary_target -> const_continue_drops -> loop_block (bb2)
    bb14: { drop(_10) -> [return: bb15, unwind: bb35]; }   // arm0_inner dropped FIRST
    bb15: { StorageDead(_10); drop(_8) -> [return: bb16, unwind: bb36]; } // arm0_outer SECOND
    bb16: { StorageDead(_8); goto -> bb10; }               // Direct jump to Arm 1 (bb10), bypassing bb3 switchInt!
```

`CleanupPostBorrowck` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:64-69`) replaces every `TerminatorKind::FalseEdge { real_target, .. }` and `TerminatorKind::FalseUnwind { real_target, .. }` with `TerminatorKind::goto(real_target)`. Subsequent CFG simplification immediately prunes `bb13` and `const_continue_drops`.

Empirical MIR and LLVM IR CFG metrics recorded in `support/probe_results.json` (`rustc 1.98.0-nightly`, `14210df0e`, `LLVM 22.1.6`) across the runtime-input 3-state byte-stream DFA (`dfa_stream_loop_match` vs `dfa_stream_plain_loop`), the 3-step scalar DFA (`step_loop_match` vs `step_plain_loop`), and `drop_order_loop_match`:

| Function (`opt-level`) | `built` MIR (`BB / sw / FE / discr`) | `CleanupPostBorrowck` (`BB / sw / FE`) | `runtime-optimized` MIR (`BB / sw / discr / goto`) | LLVM IR (`switch / br / BB`) |
| :--- | :---: | :---: | :---: | :---: |
| `dfa_stream_loop_match` (`-O0`) | `88 / 6 / 7 / 6` | `43 / 6 / 0` | `27 / 6 / 1 / 8` | `1 / 19 / 29` |
| `dfa_stream_plain_loop` (`-O0`) | `73 / 6 / 2 / 1` | `38 / 6 / 0` | `29 / 6 / 1 / 10` | `1 / 21 / 31` |
| **`dfa_stream_loop_match` (`-O2`)** | `84 / 6 / 7 / 6` | `39 / 6 / 0` | **`17 / 5 / 0 / 8`** | **`0 / 9 / 11`** |
| **`dfa_stream_plain_loop` (`-O2`)** | `69 / 6 / 2 / 1` | `34 / 6 / 0` | **`23 / 6 / 1 / 12`** | **`1 / 10 / 14`** |
| `step_loop_match` (`-O0`) | `37 / 1 / 5 / 0` | `18 / 1 / 0` | `12 / 1 / 0 / 4` | `1 / 4 / 7` |
| `step_plain_loop` (`-O0`) | `33 / 1 / 3 / 0` | `19 / 1 / 0` | `14 / 1 / 0 / 6` | `1 / 6 / 9` |
| `step_loop_match` (`-O2`) | `37 / 1 / 5 / 0` | `18 / 1 / 0` | `6 / 1 / 0 / 4` | `1 / 3 / 6` |
| `step_plain_loop` (`-O2`) | `33 / 1 / 3 / 0` | `19 / 1 / 0` | `8 / 1 / 0 / 6` | `1 / 4 / 7` |
| `drop_order_loop_match` (`-O2`) | `37 / 1 / 3 / 0` (`9` drops) | `20 / 1 / 0` (`6` drops) | `8 / 0 / 0 / 0` (`4` drops) | `2 / 9 / 24` |

**Key empirical takeaway:** On `dfa_stream_loop_match` at `-O2`, MIR constant propagation folds even the initial `State::S0` entry into `goto -> bb2`, leaving **`0` `discriminant()` reads** and **`0` LLVM `switch` instructions** (`5` MIR `switchInt`s correspond solely to the 5 runtime byte/bounds checks `i >= input.len()`, `b & 1`, `b & 2`). On the semantically identical `dfa_stream_plain_loop`, neither MIR optimization nor LLVM `-O2` threads the centralized state switch (`1` LLVM `switch`, `6` MIR `switchInt`s, `1` `discriminant()`, `14` vs `11` LLVM basic blocks). On `rustc 1.102.0-nightly (3ef0c22cd, LLVM 23.1.5)`, a constant-input DFA (`DFA=337`) similarly exhibited fewer `-O0` LLVM branches for `#[loop_match]` (`switch: 1, br: 9` vs `switch: 1, br: 11`) while collapsing both functions to `switch: 0, br: 0` at `-O2` via constant folding, and matched `DROPS=["arm0_inner", "arm0_outer", "arm1"]` under `Miri -Zmiri-tree-borrows`.

### 3. Lexical LIFO `DropTree` Semantics, Unwind Continuity, and the Discovered `Drop`-Enum State-Overwrite Bug

Basis: source + execution + derived

#### 3.1 Why the `DropTree` Fold Preserves Exact Lexical LIFO Order

In `compiler/rustc_mir_build/src/builder/scope.rs:1031-1035`:
```rust
let drop_idx = self.scopes.scopes[stack_index + 1..]
    .iter()
    .flat_map(|scope| &scope.drops)
    .fold(ROOT_NODE, |drop_idx, &drop| drops.add_drop(drop, drop_idx));
```
`self.scopes.scopes[stack_index + 1..]` lists active scopes inside `'blk` from **outermost to innermost**, and each `scope.drops` lists scheduled locals (`DropKind::{Value,Storage,ForLint}`) in **declaration order**. Because `DropTree::add_drop(data, next)` (`scope.rs:299-307`) creates a node whose `.next` pointer points to the **previously accumulated `drop_idx`**, folding left-to-right builds a singly linked chain from the last-declared local in the innermost scope back down to `ROOT_NODE` (`real_target`):

$$\text{fold}(\text{ROOT}, [d_0, d_1, \dots, d_k]) \implies d_k \to d_{k-1} \to \dots \to d_0 \to \text{real\_target}.$$

Furthermore, `build_exit_tree` (`scope.rs:1976-2005`) iterates over `drops.drop_nodes` and links every `DropKind::Value` block's unwind edge to `self.scopes.unwind_drops` at `unwind_indices[drop_node.next]`. Thus, if `d_k`'s destructor panics during a `#[const_continue]`, unwinding drops `d_{k-1}, \dots, d_0` and outer enclosing scopes without ever entering `real_target`. Both properties are verified empirically:
- Normal execution & `Miri -Zmiri-tree-borrows` (`c1_dfa_opt0`, `c1_dfa_opt2`, `c1_miri_tree_borrows`): `DROPS=["arm0_inner", "arm0_outer", "arm1"]`.
- Panicking inner destructor (`c6_unwind_through_const_continue_drops`, `c6_miri_tree_borrows`): `UNWIND_CAUGHT=true LOG=["arm0_inner_panics", "arm0_outer"]` (never enters arm 1).

#### 3.2 Newly Discovered `rustc` Defect: Silent `Drop` Omission on `Drop`-Implementing Fieldless Enum State Overwrites

**Primary-source root cause (`source`):**
1. `is_supported_loop_match_type` (`into.rs:275-277`) permits **any** fieldless enum (`adt_def.variants().iter().all(|v| v.fields.is_empty())`) without requiring `Copy` or `!ty.needs_drop(...)`.
2. In an ordinary Rust assignment `s = expr` (`compiler/rustc_mir_build/src/builder/expr/stmt.rs`), MIR construction calls `drop_and_replace` (emitting `TerminatorKind::Drop { place: s, replace: true }` prior to overwriting `s`).
3. Inside `#[loop_match]`, **neither** the normal exit path (`into.rs:383-391`: `this.cfg.push_assign(block, source_info, state_place, Rvalue::Use(...))`) **nor** the `#[const_continue]` path (`scope.rs:999`: `this.expr_into_dest(state_place, block, value)`) emits `TerminatorKind::Drop { replace: true }` on `state_place`. Because `ElaborateDrops` only elaborates existing `Drop` terminators (it does not synthesize drops for raw `StatementKind::Assign`), the old value stored in `state_place` is silently overwritten without running `Drop::drop`.

**Empirical verification (`execution`, `c5_drop_fieldless_enum_divergence` & `c5_miri_tree_borrows`):** For `enum DropState { A, B }` with `impl Drop for DropState` logging `"drop_S::A"` / `"drop_S::B"`, transitioning `DropState::A -> DropState::B` inside arm A (with guards `armA_outer`, `armA_inner`) and exiting in arm B (with guard `armB`) followed by `drop(s)` yields:

| Lowering Mode | Observed Destructor Trace (Native & `Miri -Zmiri-tree-borrows`, `rc=0`) | Missing Destructor |
| :--- | :--- | :---: |
| `#[loop_match]` + `#[const_continue] break 'blk DropState::B` | `["armA_inner", "armA_outer", "armB", "drop_S::B"]` | **`drop_S::A` omitted** |
| `#[loop_match]` + normal `break 'blk DropState::B` | `["armA_inner", "armA_outer", "armB", "drop_S::B"]` | **`drop_S::A` omitted** |
| Plain `loop { s = 'blk: { match s { ... } }; }` | `["armA_inner", "armA_outer", "drop_S::A", "armB", "drop_S::B"]` | none |

MIR inspection of `ElaborateDrops.after` confirms `run_plain_loop` emits `bb7: drop(_5) -> [return: bb8, unwind: bb9]; bb8: _5 = move _8;`, whereas `run_loop_match` emits `bb3: _22 = const true; _5 = S::B; _12 = discriminant(_5); drop(_11) -> ...` with zero `drop(_5)` before overwriting `_5`. Notice also a secondary ordering asymmetry: `#[const_continue]` overwrites `_5` *before* dropping arm locals `_11`/`_9`, so if `_11`'s destructor panics, the unwind pad `bb15 (cleanup): drop(_5)` drops the *new* state `S::B` while `S::A` was never dropped. Because both `into.rs:270-281, 383-391` and `scope.rs:999` are identical in `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, this defect persists at `rust-lang/rust` HEAD. Any sound observational-equivalence claim for `#[loop_match]` therefore requires the sharp precondition `!needs_drop(state_ty)` (verified in Lean via `ce4_drop_state_overwrite_omits_old_state_drop`).

### 4. IEEE-754 Float-Range Static-vs-Dynamic Parity (`-0.0`, `+0.0`, `±inf`, `NaN`)

Basis: normative (IEEE-754) + source + execution + derived

Static resolution and dynamic matching take completely different code paths for floating-point scrutinees (`f16`, `f32`, `f64`, `f128`), yet agree on every bit pattern because of two load-bearing THIR invariants:

1. **Static `ValTree` path (`rustc_pattern_analysis/src/rustc.rs:561-592, 623-653` -> `matches/mod.rs:2957-2984`, commit `342d74463`):**
   - A float literal pattern (e.g., `0.0_f32`) is lowered by `lower_pat` to a closed singleton range `Constructor::F32Range(value, value, RangeEnd::Included)` using `rustc_apfloat::ieee::Single::from_bits(bits.into())` (`rustc_apfloat 0.2.3+llvm-462a31f5a5ab`).
   - A float range pattern (`lo..=hi`, `lo..hi`, `lo..`, `..hi`, `..=hi`) replaces absent lower bounds with `-Single::INFINITY` and absent upper bounds with `+Single::INFINITY`.
   - `static_pattern_match_inner` (`matches/mod.rs:2964-2970`) converts the `#[const_continue]` `ValTree` leaf via `valtree.to_leaf().to_f32()` and evaluates `(*l..=*h).contains(&actual)` (`RangeEnd::Included`) or `(*l..*h).contains(&actual)` (`RangeEnd::Excluded`), delegating to `rustc_apfloat`'s IEEE-754 `PartialOrd` (`-0.0 == +0.0`, `NaN` unordered with all values including `±inf`).
2. **Dynamic MIR path (`compiler/rustc_mir_build/src/builder/matches/test.rs:49-53, 225-275`, commit `342d74463`):**
   - Float constants use `TestKind::ScalarEq`, emitting MIR `BinOp::Eq(expected, Copy(actual))` (lines 227–235).
   - Float ranges use `TestKind::Range`, emitting `BinOp::Le(lo, val)` only when `range.lo.as_finite()` is `Some` and `BinOp::Le`/`BinOp::Lt(val, hi)` only when `range.hi.as_finite()` is `Some` (omitting non-finite endpoints entirely!).
3. **Why the two paths agree across all $2^{32}$ `f32` bit patterns (THIR invariants in `compiler/rustc_mir_build/src/thir/pattern/mod.rs:250-280`):**
   - **Invariant A (no twice-open `..`):** Lines 250–253 reject `lo.is_none() && hi.is_none()`. If `..` were lowered as `PatKind::Range(NegInfinity, PosInfinity)`, dynamic `TestKind::Range` would emit zero comparisons (accepting `NaN`), whereas static `(-inf..=+inf).contains(&NaN)` would return `false`.
   - **Invariant B (upper-unbounded `lo..` uses `RangeEnd::Included`):** Lines 277–279 explicitly force `RangeEnd::Included` for `lo..` (even though `..` syntax looks exclusive). If `0.0..` used `RangeEnd::Excluded` with `hi = +inf`, static `(0.0..+inf).contains(&+inf)` would return `false`, contradicting dynamic `0.0 <= +inf` (`true`).
   - Under Invariants A and B, our Lean theorem `ieee754_range_static_eq_dynamic` proves bit-exact equivalence across all $2^{32}$ binary32 values, and `f32_singleton_range_eq_scalar_eq` proves singleton `F32Range(v, v, Included)` equals `BinOp::Eq(v, x)`.
4. **Live execution & Miri verification (`c3_ieee754_float_and_or_bindings`, `c3_miri_tree_borrows`, `rc=0`):**
   - `#[const_continue] break 'blk (-0.0_f32)` matches `x @ 0.0 =>` with exact output `NEG_ZERO=("zero_arm", 2147483648)` (`0x8000_0000` sign bit preserved in `state_place` and bound `x`!).
   - `#[const_continue] break 'blk f32::NAN` skips `0.0`, `5.0..`, and `..0.0`, routing to `_ =>` (`NAN=nan_wildcard`).
   - `#[const_continue] break 'blk f32::INFINITY` matches `5.0.. =>` (`PINF=("ge5_or_pos_inf", 2139095040)` = `0x7f80_0000`).
   - `#[const_continue] break 'blk f32::NEG_INFINITY` matches `..0.0 =>` (`NINF=("lt0_or_neg_inf", 4286578688)` = `0xff80_0000`).
   - Against `..0.0 =>` followed by `0.0.. =>`, `-0.0_f32` fails `..0.0` (`-0.0 < 0.0` is `false`) and matches `0.0..` (`OPEN_NZ=("ge_zero_open_range", 2147483648)`), matching plain `loop` bit-for-bit on every input.

### 5. `Or`-Pattern `sub_branches` Rebinding, Structural-Equality Gating, and the Nested-`Or` Compiler ICE

Basis: source + execution

1. **Per-alternative `sub_branches` and `@`-binding rebinding (`compiler/rustc_mir_build/src/builder/matches/mod.rs:498-550, 1389-1458, 2882-2916`):**
   - `BuiltMatchTree` represents each match arm as a `MatchTreeBranch { sub_branches: Vec<MatchTreeSubBranch> }`. Each `sub_branch` owns a `success_block` (its `pre_binding_block`), into which `bind_pattern` -> `bind_and_guard_matched_candidate` -> `bind_matched_candidate_for_arm_body` (lines 2522–2526) emits the local binding copies (e.g., `_x = copy state_place`) before jumping to the shared arm-body `target_block` (lines 533–548).
   - When an `Or`-pattern has distinct bindings (such as `x @ 0 | x @ 2`), `branch.sub_branches` contains one `MatchTreeSubBranch` per alternative; when all alternatives have identical/empty bindings (such as `0 | 2`), match simplification collapses them into a single `sub_branch`.
   - `static_pattern_match` (lines 2894–2910) handles both cases via:
     ```rust
     if let rustc_pattern_analysis::rustc::Constructor::Or = pat.ctor() {
         for pat in pat.iter_fields() {
             let sub_branch = branch
                 .sub_branches
                 .get(pat.idx)
                 .or_else(|| branch.sub_branches.last())
                 .unwrap();
             match self.static_pattern_match_inner(valtree, &pat.pat) {
                 true => return Some(sub_branch.success_block),
                 false => continue,
             }
         }
     }
     ```
   - Live probe `c3_ieee754_float_and_or_bindings` & `c3_miri_tree_borrows` verify all three legal `Or` forms: `x @ 0 | x @ 2` (`OR_BIND=22`), outer-bound `x @ (0 | 2)` (`OR_OUTER=22`), and bindingless `0 | 2` (`OR_NOBIND=102`), confirming that `state_place` is written to `2` before jumping to `sub_branch.success_block` and that `x` rebinds cleanly to `2` (contrast Lean sharpness counterexample `ce2_skipping_state_write_before_subbranch_breaks_at_binding`).
2. **Opaque Patterns and Structural Equality (`matches/mod.rs:2988`, `rustc_pattern_analysis/src/rustc.rs:601-608`):**
   - `static_pattern_match_inner` returns `false` on `Constructor::Opaque(_)` (`matches/mod.rs:2988`). For manual `impl PartialEq` on a fieldless enum (`enum CustomEq { A, B }`, `c2_opaque_manual_partial_eq_rejection`), Rust's structural-match check rejects `PAT_A` at compile time (`error: constant of non-structural type 'CustomEq' in a pattern`, `rc=1`) before `#[const_continue]` resolution can silently disagree with a custom `PartialEq::eq`.
3. **Confirmed `rustc` ICE on Nested Binding-Wrapped `Or`-Patterns (`c3_nested_binding_or_ice`):**
   - In `compiler/rustc_pattern_analysis/src/rustc.rs:1051-1065`, `expand_or_pat` flattens nested `PatKind::Or` nodes *only* when a child is directly `PatKind::Or`:
     ```rust
     fn expand<'p, 'tcx>(pat: &'p Pat<'tcx>, vec: &mut Vec<&'p Pat<'tcx>>) {
         if let PatKind::Or { pats } = &pat.kind {
             for pat in pats.iter() { expand(pat, vec); }
         } else { vec.push(pat) }
     }
     ```
   - When an arm writes `(x @ (0 | 1)) | x @ 2` (or `x @ (0 | 1) | x @ 2`), `expand_or_pat` leaves `x @ (0 | 1)` intact because its outer node is `PatKind::Binding { subpattern: Some(Or) }`. Subsequently, `lower_pat` (`rustc.rs:471-472`) strips `PatKind::Binding` and lowers `subpat` into a **nested `Constructor::Or`** inside the outer `Constructor::Or`'s field list!
   - When `static_pattern_match` (`matches/mod.rs:2895-2905`) passes that child to non-recursive `static_pattern_match_inner`, it hits line `2996` (`3023` in `14210df0e`): `Constructor::Or => bug!("unsupported pattern constructor {:?}", pat.ctor())`.
   - Empirically confirmed in `c3_nested_binding_or_ice`: `rustc` panics with exit code `101` (`error: internal compiler error: .../compiler/rustc_mir_build/src/builder/matches/mod.rs:3023:38: unsupported pattern constructor Or`). Because `expand_or_pat` and `static_pattern_match` are identical at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, this ICE persists on `rust-lang/rust` HEAD.

### 6. Seam with `joshlf/anneal` Trusted MIR Semantics (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Basis: source

Inspecting `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs` at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` defines the exact verified-MIR capture boundary for `#[loop_match]` functions:

| `#[loop_match]` / `#[const_continue]` MIR Construct | Stage Emitted / Erased in `rustc` | Status in `joshlf/anneal@c131b320e` (`Trusted/MirAst.lean`) | Implication for Verified MIR Capture |
| :--- | :--- | :--- | :--- |
| `TerminatorKind::FalseEdge` & `FalseUnwind` | Emitted in `built` MIR (`scope.rs:1013`, `into.rs:300`); erased to `Goto` by `CleanupPostBorrowck` (`cleanup_post_borrowck.rs:64-69`) | `.unsupported` (`MirAst.lean:782-784`) | **Zero blocker** if MIR is captured at `Runtime(PostCleanup)` / post-`CleanupPostBorrowck`; **hard fail-closed rejection** if captured from `mir_built`! |
| `StatementKind::PlaceMention` / `FakeRead` | Emitted in `built` MIR; `FakeRead` replaced with `Nop` by `CleanupPostBorrowck`; `PlaceMention` persists past `ElaborateDrops` until `RemovePlaceMention` | `.unsupported` (`MirAst.lean:654-656`) | Capture must occur after `RemovePlaceMention` (or strip `PlaceMention` / admit as no-op under validity) to admit `#[loop_match]` bodies. |
| `Rvalue::Discriminant(state_place)` & fieldless `EnumTy` | Emitted in loop header & `#[const_continue]` (`scope.rs:947`) | **Supported** (`MirAst.lean:265, 600`; `MirSemantics.lean:1222-1280`) | Fieldless-enum state machines without `Drop` locals and using constant enum transitions align with `Trusted.MirAst` once `AggregateKind::Adt` enum construction is constant-folded or admitted (`MirAst.lean:262-264` currently fails closed on `Rvalue::Aggregate(AggregateKind::Adt, [])`). |
| `MirTy::Float` (`f16`/`f32`/`f64`/`f128`) & `Char` | Permitted by `is_supported_loop_match_type` (`into.rs:272`) | `.unsupported` (`MirAst.lean:308`) | Float and `char` `#[loop_match]` state machines fail closed in `Trusted.MirAst` until float bit-level semantics (`F32Bits`) and `char` validity are added. |
| `TerminatorKind::Drop` (`DropTree` blocks) | Emitted by `build_exit_tree` (`scope.rs:1044`) and elaborated by `ElaborateDrops` | `.unsupported` (`MirAst.lean:782-784`) | `#[loop_match]` arms containing non-trivial `Drop` locals fail closed in `Trusted.MirAst` until `Drop` terminator semantics (and `deinitMovedPlace = true` interaction at `MirSemantics.lean:947-976`) are integrated. |
| `deinitMovedPlace = true` (`MirSemantics.lean:69, 947`) | Non-ZST `Operand::Move` marks moved local as `liveUninitSlot` | Active opt-in mode in `Trusted.MirSemantics` | For `Copy` scalar / `Copy` fieldless-enum states, `scope.rs:950` uses `Operand::Copy(state_place)` and `Rvalue::Discriminant(state_place)` (non-moving reads), preserving `state_place` initialization across `#[const_continue]`. |

### 7. Kernel-Checked Lean `v4.34.1` Formalization (`support/LoopMatchConstContinueAndDropTreeSoundness.lean`)

Basis: derived + execution (`Lean v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`)

`support/LoopMatchConstContinueAndDropTreeSoundness.lean` (`1,337` lines, `58,307` bytes, `517` module declarations) mechanizes the full semantics of `#[loop_match]`, `#[const_continue]`, `DropTree`, and IEEE-754 `binary32` float ranges in constructive Lean `v4.34.1` with **zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide` / `Lean.ofReduceBool`, zero `partial def`, and zero `._unsafe_rec`** (all recursive definitions are `noncomputable def`, no `deriving` clauses appear on any inductive type, and `Nat` boolean equality uses constructive `decide (a = b)` to avoid Lean `v4.34.1`'s `Nat.instLawfulEqOrd` -> `Classical.choice` dependency!).

| Theorem / Lemma (`LoopMatchSoundness.*`) | Formal Statement Summary | Verified Kernel Axioms |
| :--- | :--- | :---: |
| `f32Le_negInf_left` / `f32Le_posInf_right` | For every valid `x : F32Bits` (`exp < 256 ∧ frac < 2^23`), `f32Le (-inf) x = !x.isNaN` and `f32Le x (+inf) = !x.isNaN`. | `[propext, Quot.sound]` |
| `f32_singleton_range_eq_scalar_eq` | For all `v x : F32Bits`, `apfloatRangeContains v v true x = mirDynamicFloatEqTest v x`. | `[propext, Quot.sound]` |
| `ieee754_range_static_eq_dynamic` | Under `rustc`'s THIR invariants (`lo.isSome ∨ hi.isSome`, `hi = none → incl = true`), static `F32Range` (`lo.getD (-inf)`, `hi.getD (+inf)`) equals dynamic MIR `TestKind::Range` on all $2^{32}$ valid `F32Bits`. | `[propext, Quot.sound]` |
| `ieee754_signed_zero_and_nan_static_vs_dynamic_agree` | (a) `-0.0` (`2147483648`) matches `0.0 =>` statically & dynamically; (b) every `NaN` fails every `F32Range`/`Eq` test; (c) `0.0..` matches `-0.0`, `+inf` and rejects `-inf`, `NaN`; (d) `..0.0` matches `-inf` and rejects `-0.0`, `NaN`. | `[propext]` |
| `const_continue_drop_tree_preserves_lexical_lifo` | For every arbitrarily nested `scopes : List (List DropTag)`, `buildScopeDropTree scopes` executed with `entry < fuel` terminates at `ROOT_NODE` (`real_target`) with exact output `lexicalLifoDrops scopes`. | `[propext]` |
| `dual_drop_tree_imaginary_edge_matches_real_edge` | Real-edge `DropTree` (`drop_and_continue_block -> real_target`) and borrowck `const_continue_drops` (`imaginary_target -> loop_block`) emit identical lexical LIFO drop sequences. | `[propext]` |
| `static_pattern_match_eq_dynamic_match` | For all guard-free arm lists (including `Or`-pattern `sub_branches`) and all valid `StateVal`s (`nat`, `enumTag`, `f32`), `staticPatternMatch arms v = dynamicPatternMatch arms v`. | `[propext, Quot.sound]` |
| `const_continue_direct_jump_bisimulates_loop_header_switch` | Lock-step bisimulation: for every `WellFormedLoopMatch arms`, valid initial `ExecState`, and arbitrary `fuel : Nat`, `runStatic arms fuel PC.loopHeader st = runDynamic arms fuel st` (bit-exact return value, final `state_place`, and full observable + destructor trace). | `[propext, Quot.sound]` |
| `ce1_arm_guard_side_effect_breaks_static_dispatch` | Sharpness CE1: false-evaluating side-effecting arm guard yields `some (20, [armEmit "guard_eval" 0])` dynamically vs `some (10, [])` under naive static jump-threading (`≠`). | `[propext]` |
| `ce2_skipping_state_write_before_subbranch_breaks_at_binding` | Sharpness CE2: on `x @ 0 | x @ 2`, skipping `state_place := 2` before jumping to `sub_branch[1]` causes stale `x = 0` rebinding and non-termination (`running acc=60`) vs `halted 22` (`≠`). | `[propext]` |
| `ce3_omitting_drop_tree_leaks_inner_arm_guard` | Sharpness CE3: skipping the real-edge `DropTree` on `nestedDropArms` emits `[drop "arm1"]` instead of `[drop "arm0_inner", drop "arm0_outer", drop "arm1"]` (`≠`). | `[propext]` |
| `ce4_drop_state_overwrite_omits_old_state_drop` | Sharpness CE4: formalizes the empirically discovered `DropState` divergence (`plainLoopTrace ≠ loopMatchTrace`), proving `!needs_drop(state_ty)` is necessary for Theorem 1. | `[propext]` |

## Boundaries

- **`known not to apply` — `Drop`-implementing fieldless enum states:** Observational equivalence between `#[loop_match]` and plain `loop` does **not** hold for fieldless enums implementing `Drop`. Both `#[const_continue]` (`scope.rs:999`) and normal `break 'blk` (`into.rs:383-391`) omit `drop_and_replace` on `state_place`, silently dropping the destructor of overwritten state values (empirically established in `c5_drop_fieldless_enum_divergence` and `c5_miri_tree_borrows`).
- **`known not to apply` — Nested binding-wrapped `Or`-patterns (`(x @ (0 | 1)) | x @ 2`):** Static dispatch does **not** handle `PatKind::Binding` wrapping an inner `PatKind::Or` inside an outer `PatKind::Or`; `rustc` crashes with ICE `unsupported pattern constructor Or` (`c3_nested_binding_or_ice`, `matches/mod.rs:2996` / `3023`).
- **`known not to apply` — Direct ingestion into `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` `Trusted.MirSemantics`:** The Lean proof in `support/LoopMatchConstContinueAndDropTreeSoundness.lean` is a standalone model (zero `Trusted.*` imports). It does not mechanically verify `rustc`'s Rust compiler implementation itself, nor does `Trusted.MirAst` at `c131b320e` yet admit `Float`, `Char`, `TerminatorKind::Drop`, `Rvalue::Aggregate(AggregateKind::Adt, [])`, or pre-`CleanupPostBorrowck` `FalseEdge`/`FalseUnwind`.
- **`unsupported` (by `rustc`) — Guards, payload ADTs, projected/upvar scrutinees, `ConstParam`, `ConstBlock`, and manual `PartialEq` constants:** All seven categories are hard-rejected by `rustc` before MIR codegen (`c2`, `c4a`–`c4g`).
- **`not examined` — `f16` / `f128` hardware execution and `async`/`gen` coroutine `#[loop_match]` interactions:** `F16Range`, `F64Range`, and `F128Range` were inspected in `matches/mod.rs:2957-2984` and `rustc_pattern_analysis/src/rustc.rs:561-653` (where they follow the identical `rustc_apfloat` `Range::contains` pattern as `F32Range`), and `build_exit_tree`'s coroutine `dropline_to` wiring was inspected in `scope.rs:2007-2032`, but neither `f16`/`f128` native execution nor `#[loop_match]` inside `async fn` / `gen` blocks across `.await`/`yield` points was executed empirically.
- **`not examined` — Live native execution on `LLVM 23.1.5` (`3ef0c22cd`) or `rust-lang/rust` HEAD (`342d74463`) on this host:** The local execution host installed `rustc 1.98.0-nightly (14210df0e 2026-05-31, LLVM 22.1.6, Miri 0.1.0)`. Source equivalence of all `loop_match` lowering logic between `3ef0c22cd` and `342d74463` was verified directly by SHA-256 and `diff -u`, and prior `1.102.0-nightly`/`LLVM 23.1.5` observations are cited strictly with their exact toolchain identity rather than extrapolated to `dfa_stream_loop_match` LLVM 23 instruction counts.
- **`unknown` — Future stabilization design for `Drop`-implementing fieldless enums and nested `Or`-patterns (`rust-lang/rust#132306`):** Whether upstream will resolve the `Drop`-enum omission by restricting `is_supported_loop_match_type` to `!ty.needs_drop` / `Copy` or by emitting `drop_and_replace` before overwriting `state_place` (and whether `expand_or_pat` or `static_pattern_match` will be made recursive for nested `Or`-patterns) is not yet decided upstream.
- **Attractive stronger conclusions NOT established by this evidence:**
  - Eliminating a loop-header `switch` in MIR/LLVM IR does **not** by itself prove wall-clock runtime speedup on every CPU microarchitecture (indirect-branch / BTB / I-cache footprint trade-offs across large DFAs were not benchmarked).
  - Passing `Miri -Zmiri-tree-borrows` on the four probe crates (`c1`, `c3`, `c5`, `c6`) establishes absence of Tree Borrows UB on those concrete executions, not universal memory-safety of all unsafe code combined with `#[loop_match]`.

## Evidence

### Primary Upstream Source Citations

1. **`rust-lang/rust` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (observed `2026-11-22`, verified via GitHub API):**
   - `compiler/rustc_hir_typeck/src/loops.rs:44-49` (`Context::LoopMatch { labeled_block }`), `:153-160` (`ExprKind::Loop` context dispatch), `:219-241` (`ConstContinueBadLabel` validation), `:439-465` (`is_loop_match`). File SHA-256: `df0431681c94a0f3baf7eeb238621a98847ae82345e92fedb725358589c2f8f4` (identical at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
   - `compiler/rustc_mir_build/src/thir/cx/expr.rs:1010-1028` (`ExprKind::ConstContinue` THIR lowering), `:1075-1155` (`ExprKind::LoopMatch` THIR lowering, `local()` non-upvar check, `LoopMatchInvalidMatch`, `LoopMatchInvalidUpdate`).
   - `compiler/rustc_mir_build/src/thir/pattern/mod.rs:240-285` (`lower_pattern_range`: twice-open `..` bug check at `:250-253`; `x..` forced `RangeEnd::Included` at `:277-279`).
   - `compiler/rustc_mir_build/src/builder/expr/into.rs:258-404` (`is_supported_loop_match_type` at `:270-281`, `LoopMatchArmWithGuard` at `:318-321`, `lower_match_tree`, `state_result_place` staging at `:338-392`, `in_const_continuable_scope`, `goto(loop_block)` at `:399`). Zero diff vs `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` across lines `258-404`.
   - `compiler/rustc_mir_build/src/builder/expr/stmt.rs:101-103` (`ExprKind::ConstContinue` -> `break_const_continuable_scope`).
   - `compiler/rustc_mir_build/src/builder/scope.rs:184-195` (`ConstContinuableScope`), `:230-310` (`DropTree`, `DropNode`, `add_drop`), `:585-634` (`in_const_continuable_scope`), `:833-866` (`eval_unevaluated_mir_constant_to_valtree`), `:869-1047` (`break_const_continuable_scope`: constant extraction, `Discriminant`/`Copy` liveness read, `static_pattern_match`, direct `expr_into_dest(state_place, ...)`, `FalseEdge`, `const_continue_drops`, private exit `DropTree` + `build_exit_tree(..., Some(real_target))`), `:1965-2034` (`build_exit_tree` unwind/dropline wiring), `:2104-2121` (`ExitScopes::link_entry_point`). Zero diff vs `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` across all `loop_match`/`const_continue` code.
   - `compiler/rustc_mir_build/src/builder/matches/mod.rs:260-332` (match `FalseEdge` borrowck rationale), `:498-550` (`bind_pattern` multi-`sub_branch` lowering), `:1372-1458` (`MatchTreeSubBranch`, `MatchTreeBranch`, `BuiltMatchTree`), `:2518-2528` (`bind_matched_candidate_for_arm_body`), `:2882-3008` (`static_pattern_match` & `static_pattern_match_inner`, including `F16/F32/F64/F128Range`, `Constructor::Opaque(_) => false`, and `Constructor::Or => bug!` at `:2996`). File SHA-256: `391fb84098b6e4e5c6d788e1329526b3b02a1f022e0007e1eba82d564ce937ea` (identical at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
   - `compiler/rustc_mir_build/src/builder/matches/test.rs:49-53, 225-275` (`TestKind::ScalarEq` -> `BinOp::Eq`; `TestKind::Range` -> finite-only `BinOp::Le`/`BinOp::Lt`).
   - `compiler/rustc_pattern_analysis/src/rustc.rs:471-477` (`PatKind::Binding` stripping in `lower_pat`), `:561-592` (float literal -> singleton `F{16,32,64,128}Range`), `:623-653` (open float ranges -> `±INFINITY`), `:685-695` & `:1051-1065` (`PatKind::Or` & `expand_or_pat`).
   - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:64-69` (`FalseEdge` / `FalseUnwind` -> `TerminatorKind::goto(real_target)`).
   - `Cargo.lock`: `rustc_apfloat` `0.2.3+llvm-462a31f5a5ab` (checksum `486c2179b4796f65bfe2ee33679acf0927ac83ecf583ad6c91c3b4570911b9ad`).
   - `tests/ui/loop-match/{drop-in-match-arm.rs,or-patterns.rs,no-self-assign-ice.rs,unwind.rs}` (28 UI test files under `tests/ui/loop-match/`).
2. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (observed `2026-11-22`):**
   - `trusted/lean/Trusted/MirAst.lean:262-265, 308, 600, 612-615, 654-656, 742-795` (`EnumTy`, `MirTy.unsupported`, `Rvalue.discriminant`, `StatementKind`, `TerminatorKind`).
   - `trusted/lean/Trusted/MirSemantics.lean:69, 141, 921-976, 1222-1280` (`deinitMovedPlace = true`, `readDiscriminant`).
   - `trusted/rustc-capture/src/driver.rs:25` (`COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`).

### Preserved Support Artifacts and Verification Receipts

All support material is preserved inside this package under `support/`:

| Artifact | Size / Lines | SHA-256 | Purpose & Recorded Verification Result |
| :--- | :---: | :--- | :--- |
| `support/probe_loop_match_and_const_continue.py` | `32,160 B` / `1,053` lines | `3c798a5210012b35fdc4393aab89a5523aa659f34634b0bc1e33745681fe070c` | Standalone Python 3 harness compiling and executing all 18 `rustc`/MIR/LLVM/`Miri` cases (no hardcoded metrics; builds offline Miri sysroot from active toolchain `rust-src` vendor when `MIRI_SYSROOT` is unset). |
| `support/probe_results.json` | `27,957 B` / `566` lines | `701cf86b26abffc0ab1f3f541bbd58fd940f4cb3b9bf23a99bd815813dc0a893` | Verbatim machine output captured `2026-11-22` on `rustc 1.98.0-nightly (14210df0e 2026-05-31, LLVM 22.1.6)` & `miri 0.1.0 (14210df0e2)`: `c1`, `c3`, `c5`, `c6` native + Miri (`rc=0`), `c2` & `c4a`–`c4g` compile-time rejections (`rc=1`), `c3_nested_binding_or_ice` (`rc=101`). |
| `support/LoopMatchConstContinueAndDropTreeSoundness.lean` | `58,307 B` / `1,337` lines | `b084ebcf013e61a7018f9abb9c6e50a87de8bc370872174a81f7f7369b842720` | Kernel-checked Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization: `LEAN_MAIN_EXIT=0` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`; `TOTAL_DECLS=517`, `UNSAFE_REC=0`, `CLASSICAL_CHOICE=0`, `SORRY=0`, `OF_REDUCE_BOOL=0`, `0` `omega`/`bv_decide`/`native_decide`/`partial def`/`deriving`. |

## Revalidation

To cheaply determine whether all primary findings still hold on a newer `rustc` nightly (or a newer `joshlf/anneal` revision):

1. **Rerun the standalone `rustc` / MIR / LLVM / `Miri` probe (`~35s` with fresh Miri sysroot, `~8s` if `MIRI_SYSROOT` is cached):**
   ```bash
   python3 support/probe_loop_match_and_const_continue.py /tmp/reval_probe.json
   ```
   Check the key discriminators in `/tmp/reval_probe.json`:
   - `cases.c1_dfa_opt2.llvm_fn_cfg.dfa_stream_loop_match.switch == 0` and `cases.c1_miri_tree_borrows.miri_rc == 0` with `DROPS=["arm0_inner", "arm0_outer", "arm1"]`.
   - `cases.c3_ieee754_float_and_or_bindings.stdout` and `cases.c3_miri_tree_borrows.stdout` match `NEG_ZERO=("zero_arm", 2147483648)`, `NAN=nan_wildcard`, `PINF=("ge5_or_pos_inf", 2139095040)`, `NINF=("lt0_or_neg_inf", 4286578688)`, `OPEN_NZ=("ge_zero_open_range", 2147483648)`, `OR_BIND=22`, `OR_OUTER=22`, `OR_NOBIND=102`.
   - `cases.c2_opaque_manual_partial_eq_rejection.compile_rc == 1` and all `c4a`..`c4g` have `compile_rc == 1`.
   - **Defect regression trackers:**
     * If `cases.c5_drop_fieldless_enum_divergence.compile_rc == 1` (upstream restricted `is_supported_loop_match_type` to `!needs_drop`) OR `LM_CONST_CONTINUE` and `LM_NORMAL_BREAK` begin emitting `"drop_S::A"` matching `PLAIN_LOOP`, then the `Drop`-enum state-overwrite defect has been fixed upstream and **Findings §3.2** and **Boundaries** should be updated for the new revision.
     * If `cases.c3_nested_binding_or_ice.compile_rc == 0` (instead of `101`), then the nested binding-wrapped `Or`-pattern ICE has been fixed upstream and **Findings §5** and **Boundaries** should be updated.
2. **Diff the five determining `rust-lang/rust` source regions against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:**
   - `compiler/rustc_hir_typeck/src/loops.rs` (`is_loop_match`, `Context::LoopMatch`)
   - `compiler/rustc_mir_build/src/thir/cx/expr.rs` (`ExprKind::LoopMatch` / `ConstContinue`)
   - `compiler/rustc_mir_build/src/builder/expr/into.rs` (`is_supported_loop_match_type`, `ExprKind::LoopMatch`)
   - `compiler/rustc_mir_build/src/builder/scope.rs` (`in_const_continuable_scope`, `break_const_continuable_scope`)
   - `compiler/rustc_mir_build/src/builder/matches/mod.rs` (`static_pattern_match`, `static_pattern_match_inner`)
3. **Re-verify the Lean `v4.34.1` proof artifact (`~8s`):**
   ```bash
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/LoopMatchConstContinueAndDropTreeSoundness.lean
   ```
   (Wrapped in `~/.local/bin/anneal-lean-run --mode file -- ...` on resource-governed hosts.)
4. **Check `joshlf/anneal` MIR AST support delta:** Inspect `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `Rvalue`, `StatementKind`, `TerminatorKind`) to check whether `Float`, `Char`, `TerminatorKind::Drop`, `Rvalue::Aggregate(AggregateKind::Adt, [])`, or `PlaceMention` status has changed relative to `c131b320eeeb26ef692e5afd5ec8db49ee518613`.
