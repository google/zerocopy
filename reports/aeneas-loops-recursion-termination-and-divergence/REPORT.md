# Aeneas loop translation, context joins, recursion, partial fixed points, termination, and divergence

## Summary

Across `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`release: nightly-2026.06.03`) and `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` paired with `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Aeneas handles control-flow joins, loops, recursion, termination, and divergence through six interconnected mechanisms that separate **static ownership fixed points** in the OCaml symbolic interpreter from **semantic domain fixed points** (`partial_fixpoint`) and **well-founded termination proofs** in Lean:

1. **Symbolic context joins, right-projection replay, and 2-iteration loop-entry fixed points**:
   - In `InterpJoin.join_ctxs` (`src/interp/InterpJoin.ml` L640–923), joining two symbolic environments preserves their common skeleton (`compute_fixed_abs_ids`), refreshes non-fixed abstraction identifiers on the **left**, marks differing components with `PLeft` / `PRight` (`PNone` for shared), and creates fresh symbolic values or region-bearing abstraction projections (`InterpMatchCtxs.MakeJoinMatcher` L621–766). Because an analysis join summary is not itself a synthesized computation from either incoming branch, `match_ctx_with_target` (L1348–1665) joins the summary (left) with the concrete target state (right) with continuations enabled, collapses an unprojected copy to **record** the sequence of abstraction merges and shared-borrow insertions, projects the pre-collapse joined context to `PRight`, and **replays** the recorded merge sequence on that projected context to synthesize branch-specific continuations (`SA.Join` in `eval_switch_with_join`, `InterpStatements.ml` L1053–1199).
   - For loops, `compute_loop_entry_fixed_point` (`src/interp/InterpLoopsFixedPoint.ml` L44–237) first reborrows shared loans and symbolic borrows on fixed abstractions (`reborrow_ashared_loans_symbolic_borrows`), then iterates at most **`Config.loop_fixed_point_max_num_iters = 2` times**: evaluating the loop body, retaining `Continue 0` contexts, joining them with the entry context, reducing (`InterpReduceCollapse.reduce_ctx` L840–871, the abstract-interpretation widening analogue), and checking alpha-equivalence of ownership state (`InterpMatchCtxs.ctxs_are_equivalent` / `match_ctxs` L2176–2390, ignoring `.cont` fields and using meta-only equality in `Values.ml` L181–249, L1572–1576). This 2-iteration cap bounds static ownership-shape discovery, **not** runtime loop iterations.
   - `compute_loop_break_context` (L239–381) separately collects `Break 0` contexts from the entry fixed point; when multiple break paths exist, it evaluates the loop body **a second time** with fresh loan/borrow IDs before joining so shared branch loans do not suppress required abstractions.
2. **Pure loop decomposition: fixed-point `loop` (`ControlFlow`) vs. structural recursive helpers**:
   - In `SymbolicAst.ml`, loops produce `LoopContinue`, `LoopBreak`, and `Loop` nodes. During `PureMicroPassesLoops.ml` (`support/aeneas-loops/revalidation.json`), `decompose_loops` extracts every loop into an auxiliary `@[rust_loop]` function `<fn>_loop` (plus an extracted `@[rust_loop_body]` function `<fn>_loop.body` when lowered via `loops_to_fixed_points`), keeping loop-invariant values as constant arguments and packaging varying state (and loop backward continuations) into loop inputs/outputs.
   - By default (`Config.loops_to_recursive_functions = false`, `Config.no_recursive_loops = false`; overridable via `-loops-to-rec` and `-loops-no-rec`), `loops_to_recursive` converts a loop into direct self-recursion only when its input/output relation has a structural termination measure, identity input continuations, and compatible call-shaped reentry/exit continuations (`list_mem_loop` and `list_nth_mut_loop` in `tests/lean/Loops.lean`, `Tree.explore_loop` in `tests/lean/MiniTree.lean`).
   - All remaining loops are lowered by `loops_to_fixed_points` to Aeneas's generic `loop` combinator (`def loop (body : α → Result (ControlFlow α β)) (x : α) : Result β ... partial_fixpoint` in `backends/lean/Aeneas/Std/Primitives.lean`), where `continue` becomes `ok (ControlFlow.cont next_state)` and `break` becomes `ok (ControlFlow.done output)` (`iter_loop` / `iter_loop.body` and `single_break_loop` in `Loops.lean`).
3. **Source recursion via signature abstraction and default `partial_fixpoint` extraction**:
   - During symbolic execution (`eval_function_call_symbolic` / `eval_function_call_symbolic_from_inst_sig` in `src/interp/InterpStatements.ml` L1230–1249, L1346–1477), ordinary and recursive function calls instantiate the callee's signature and region abstractions (`EFunCall`) without inlining or symbolically re-executing the callee body.
   - `Translate.export_functions_group_scc` (`src/Translate.ml` L838–913) classifies recursive SCCs into `SingleRec`, `MutRecFirst`, `MutRecInner`, and `MutRecLast`, and `ExtractBase.fun_decl_kind_to_post_qualif` (`src/extract/ExtractBase.ml` L1536–1544) maps **every** recursive kind (including structurally recursive loop helpers and mutual blocks like `even`/`odd` in `tests/lean/Tutorial/Exercises.lean`) to Lean's `partial_fixpoint` post-qualifier (`src/extract/Extract.ml` L2356–2361).
4. **Domain-theoretic partiality (`Result.div` bottom, `CCPO`, `MonoBind`) vs. total `WP.spec` proofs**:
   - At `ac9f1bc5262a5e4ff1e24ca78617121382202727`, `Aeneas/Std/Primitives.lean` (blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`, L62–65, L117–142, L159–179, L196–222) equips `Result α` (`ok v | fail e | div`) with `FlatOrder .div`, a `Lean.Order.CCPO (Result α)` instance whose bottom is `Result.div`, `MonoBind Result`, and `partial_fixpoint_monotone` lemmas for `uncurry`. Lean's `partial_fixpoint` elaborator (`src/Lean/Elab/PreDefinition/PartialFixpoint/Main.lean` blob `e83567283e7079a0c2f9c1a188d0f096d50dd13f`, L79–115, L154–190) defines recursive functions as least fixed points over this CCPO and generates unfolding equation theorems without requiring a translation-time termination proof (witnessed by `i32_id` in `tests/lean/BaseTutorial.lean` L319–384, which diverges on negative inputs).
   - At the specification layer (`backends/lean/Aeneas/Std/WP.lean` blob `018c456bcab5374de0b09b17eda0df1a48e2288b`, L23–36, L54–61, L178–188), `WP.spec m P` maps both `fail _` and `div` to `False` (`spec_div : spec div p ↔ False`, `spec_equiv_exists : spec m P ↔ ∃ y, m = ok y ∧ P y`). Thus proving `f x ⦃ y => P y ⦄` proves termination on covered inputs. Recursive specification theorems (`i32_id_spec`, `even_spec`/`odd_spec`) are ordinary Lean theorems checked by Lean's well-founded `termination_by` / `decreasing_by`, while `loop` combinator proofs use `loop.spec` (arbitrary `WellFoundedRelation`) or `loop.spec_decr_nat` (`Nat` measure).
5. **Extrinsic termination facilities (`-decreases-clauses` vs. `-use-fuel`) and Lean grammar conflict**:
   - While `PureMicroPassesGeneral.ml` (blob `32d37b2363a69b9cf8a765b6446deb753aadc27b`) implements fuel threading gated on `Config.use_fuel`, `src/Main.ml` explicitly **rejects `-use-fuel` for the Lean backend** (and rejects combining `-use-fuel` with `-decreases-clauses`).
   - When opt-in `-decreases-clauses` (`Config.extract_decreases_clauses = false` by default) is passed for Lean (`support/aeneas-extrinsic-termination/termination-facilities-matrix.json`), `Main.ml` (L112–123, L577–590) rejects crates containing any mutually recursive group. For singly recursive functions and loops (`functions_with_decreases_clause` in `Translate.ml` L1411–1430), `Extract.ml` generates `<fn>_terminates` (tuple of forward inputs) and `<fn>_decreases` (`sorry` macro template in `Clauses/Template.lean`, imported as `Clauses.Clauses`) and emits `termination_by <fn>_terminates ...` followed by `decreasing_by <fn>_decreases ...`. However, `Extract.ml` then **unconditionally emits `fun_decl_kind_to_post_qualif` (`partial_fixpoint`) after `decreasing_by`**, which conflicts with Lean `v4.30.0-rc2`'s `Termination.suffix` grammar (`src/Lean/Parser/Term.lean` blob `16b73a52ad5c2e6819a9d009012a5e2d75f30559` L594–617, which accepts at most one of `termination_by` or `partial_fixpoint` before optional `decreasing_by`).
6. **Divergence analysis (`can_diverge`) vs. rejection of breakless infinite loops (`NoBreak`)**:
   - `src/llbc/FunsAnalysis.ml` (blob `a2678ba12e8baaaf14fc99c3f061b10edae2da86`) sets `can_diverge = true` on recursive SCC calls, any loop, or calls to functions with `can_diverge = true` (so a non-recursive caller propagates `Result.div` via `Result.bind` without needing `partial_fixpoint` itself), but **does not propagate `can_diverge` across trait-method calls** (documented `TODO`).
   - Crucially, although `Result.div` models semantic nontermination, `InterpLoops.eval_loop_symbolic` (`src/interp/InterpLoops.ml` blob `94630c8c9052e326782cc6f71b1f346df451f3e5` / `21345f80fa212c596f6437378d7d57984fa2ea77` L344–435) rejects any loop whose exit analysis returns `NoBreak` with `(Infinite) loops which do not contain breaks are not supported yet` (while concrete-mode `eval_loop_concrete` re-evaluates `Continue 0` indefinitely).

---

## Applicability

This report synthesizes findings across the subjects listed in `REPORT.json`:

1. **Aeneas `nightly-2026.06.03`** (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`), selected by Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` in `anneal/flake.nix`) and paired with Charon `0.1.210` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`).
2. **Aeneas symbolic interpreter revision** (`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`), examined for the detailed join, right-projection replay, loop-entry fixed-point, second-break-evaluation, and recursive call-abstraction algorithms (`support/aeneas-joins-loops-fixed-points-21345f80/source-reading.json`).
3. **Lean 4 `v4.30.0-rc2`** (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), pinned by `backends/lean/lean-toolchain` at `ac9f1bc5262a5e4ff1e24ca78617121382202727` and examined for the `partial_fixpoint` parser/elaborator (`Term.lean`, `Order/Basic.lean`, `PartialFixpoint/Main.lean`) and `Termination.suffix` grammar.

### Shared vs. Revision-Specific Behavior

- **Shared across `ac9f1bc5262a5e4ff1e24ca78617121382202727` and `21345f80fa212c596f6437378d7d57984fa2ea77`**:
  - The symbolic join and loop fixed-point engine (`InterpJoin.ml`, `InterpJoinCore.ml`, `InterpMatchCtxs.ml`, `InterpReduceCollapse.ml`, `InterpLoops.ml`, `InterpLoopsFixedPoint.ml`, `InterpStatements.ml`), including `Config.loop_fixed_point_max_num_iters = 2`, the `NoBreak` rejection (`(Infinite) loops which do not contain breaks are not supported yet`), the prohibition on nonzero cross-loop `Continue`/`Break` indices in symbolic loop synthesis, and signature-based symbolic evaluation of recursive calls.
  - Pure loop lowering (`PureMicroPassesLoops.ml`: `loops_to_recursive`, `decompose_loops`, `loops_to_fixed_points`) and Lean `partial_fixpoint` emission on both `loop` and recursive functions/loop helpers.
- **Specific to `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`) and Lean `v4.30.0-rc2`**:
  - `Aeneas/Std/Primitives.lean` (blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`) defines `Result α` as the 3-constructor inductive `ok v | fail e | div` with `FlatOrder .div` and `CCPO (Result α)`.
  - Checked-in Lean loop and recursion fixtures (`tests/lean/Loops.lean`, `tests/lean/MiniTree.lean`, `tests/lean/BaseTutorial.lean`, `tests/lean/Tutorial/Exercises.lean`) and the `-decreases-clauses` vs. `partial_fixpoint` suffix analysis against Lean `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) are pinned to this revision.
- **Specific to `21345f80fa212c596f6437378d7d57984fa2ea77`**:
  - Line-anchored inspection of `InterpJoin.ml` (`join_ctxs` L640–923, `join_ctxs_list` L924–1013, `match_ctx_with_target` L1348–1665), `InterpLoopsFixedPoint.ml` (`compute_loop_entry_fixed_point` L44–237, `compute_loop_break_context` L239–381), `InterpLoops.ml` (`eval_loop_symbolic` L344–505), and `InterpStatements.ml` (`eval_switch_with_join` L1053–1199, `eval_function_call_symbolic` L1230–1477).

---

## Findings

### 1. Symbolic Context Joins, Right-Projection Replay, and Equivalence Matching

#### 1.1 `join_ctxs`, `PLeft`/`PRight` Markers, and Loan Update Requests

In `src/interp/InterpJoin.ml` (`21345f80fa212c596f6437378d7d57984fa2ea77` L640–923, L924–1013), `src/interp/InterpJoinCore.ml` (L9–32, L859), and `src/interp/InterpMatchCtxs.ml` (L621–766):

- **Environment partitioning and left-ID refresh**: Given two contexts with ordered entries (locals, dummy values, borrow abstractions, stack frames), `join_ctxs` intersects dummy identifiers, computes unchanged abstractions (`compute_fixed_abs_ids`), refreshes non-fixed abstraction identifiers on the **left** input, matches retained locals, and converts non-common structure into marked abstraction content (`PLeft`, `PRight`, or `PNone` for shared content).
- **Symbolic value and borrow summaries (`MakeJoinMatcher`)**: Distinct concrete literals join into a fresh symbolic value whose left and right originals are recorded in `symbolic_to_value`. Admissible values containing borrows refresh erased regions, create abstraction projections (including a static-region abstraction when required) linking both branches to the fresh symbol, and construct backward expression continuations when continuations are enabled.
- **Iterative loan ending (`join_ctxs_list`)**: A join attempt returns `join_info_or_update`; if loans obstruct the join (`LoanInLeft`, `LoanInRight`, or plural variants), `join_ctxs_list` ends the obstructing loans in the respective input context (with synthesis disabled), retries the join, collapses projection markers, and returns both the updated input contexts and the joined summary.

Basis: **source** + source-comment **documentation**.

#### 1.2 Why Synthesis Requires `match_ctx_with_target` and Right-Projection Replay

As documented in `src/interp/InterpJoin.mli` (L75–126), a joined summary context cannot be used directly for code synthesis because refreshing left-side abstraction IDs during analysis would otherwise make refreshed abstractions appear without computational provenance. When matching a concrete branch or loop state (target) against a joined summary (source), `InterpJoin.match_ctx_with_target` (`src/interp/InterpJoin.ml` L1348–1665) executes a 7-step algorithm:

1. Simplify unnecessary target borrows/loans, prepare the match by ending or moving obstructing content, and simplify a second time.
2. Destructure fresh shared loans and reduce the target context with continuations enabled.
3. Join `source` (left) and `target` (right) with continuations enabled.
4. Collapse an unprojected copy of that joined context solely to **record the sequence of abstraction merges and shared-borrow insertions** (because projecting continuations after a two-sided collapse is intractable, while projecting before collapse loses required merge triggers).
5. Project the pre-collapse joined context to `PRight` (retaining only the target branch's state and right-side shared-borrow insertions) and **replay the recorded merge sequence** on the projected context while tracking static ownership.
6. Simplify empty abstractions without snapshots that reference not-yet-bound outputs, reorder fresh abstractions, and match the resulting context against the summary.
7. Compose `source -> joined` and `joined -> target` identifier maps to extract the branch's actual symbolic input values and abstraction arguments alongside the synthesized continuation.

In `InterpStatements.eval_switch_with_join` (`src/interp/InterpStatements.ml` L1053–1199; gated by `Config.recover_joins = true`), surviving `Unit`-result switch branches are joined into a summary with `EJoin` continuations, each branch is matched via `match_ctx_with_target` to emit `SymbolicAst.Join` with its branch-specific arguments, and code after the switch is bound via a symbolic `Let` (or duplicated across branches if a recoverable join failure occurs).

Basis: **source** + **derived** provenance requirement.

#### 1.3 Alpha-Equivalence of Ownership State vs. Synthesis Matching

In `src/interp/InterpMatchCtxs.ml` (L2176–2390), `src/interp/InterpMatchCtxs.mli` (L124–159), and `src/llbc/Values.ml` (L181–249, L1572–1576):

- `match_ctxs` builds injective substitutions across regions, borrow/loan IDs, abstractions, and symbolic values while keeping fixed identifiers identity-mapped.
- Abstraction matching compares IDs, parents, static ownership, region maps, ended-sub-abstraction levels, and `avalues`, while **explicitly ignoring `.cont` continuation expressions** and using meta-only value equality (`Values.ml`).
- Fixed-point convergence calls `ctxs_are_equivalent` (equivalence mode), whereas `match_ctx_with_target` calls `match_ctxs` with `check_equiv:false`, `check_kind:false`, and `check_can_end:false`.

Basis: **source**.

---

### 2. Loop Fixed-Point Analysis, Break Contexts, and Pure Loop Lowering

#### 2.1 Bounded 2-Iteration Loop-Entry Fixed Point (`compute_loop_entry_fixed_point`)

In `src/interp/InterpLoopsFixedPoint.ml` (`21345f80fa212c596f6437378d7d57984fa2ea77` L13–41, L44–237; `ac9f1bc5262a5e4ff1e24ca78617121382202727` blob `InterpLoopsFixedPoint.ml`) and `src/interp/InterpJoin.mli` (L5–60):

1. **Pre-loop shared-loan reborrowing**: Before iterating, `reborrow_ashared_loans_symbolic_borrows` reborrows shared loans and symbolic borrows tied to fixed abstractions (without continuation synthesis) so that subsequent loop expansions do not mutate entry-fixed abstractions.
2. **Iterative join and widening (`reduce_ctx`)**: On each iteration (bounded by the immutable constant `Config.loop_fixed_point_max_num_iters = 2` in `src/Config.ml` L176–182), Aeneas evaluates the loop body symbolically, filters for `Continue 0` contexts (ignoring `Return`, `Panic`, and `Break`, and raising an unsupported error on `Continue i` for `i > 0`), joins the current entry summary with those `Continue 0` states, reduces the joined context via `InterpReduceCollapse.reduce_ctx` (`src/interp/InterpReduceCollapse.ml` L624–697, L840–871) with `with_abs_conts:false`, and tests `ctxs_are_equivalent`.
3. **Convergence or failure**: If equivalence holds within 2 iterations, `loop_abs_reorder_and_add_info` reorders fresh loop abstractions and attaches `ELoop` continuations. If equivalence is not reached within 2 iterations, Aeneas raises an error (under `fail_hard`, the final iteration runs the throwing matcher to expose a diagnostic stack trace).

Basis: **source** + **documentation** (`src/interp/InterpLoops.mli`).

#### 2.2 Separate Break-Context Collection and Second-Evaluation Trick (`compute_loop_break_context`)

In `src/interp/InterpLoopsFixedPoint.ml` (L239–381) and `src/interp/InterpLoops.ml` (`21345f80fa212c596f6437378d7d57984fa2ea77` L78–505; `ac9f1bc5262a5e4ff1e24ca78617121382202727` blob `94630c8c9052e326782cc6f71b1f346df451f3e5`):

- Starting from the converged loop-entry fixed point (stripped of loop continuations), `compute_loop_break_context` evaluates the body to collect `Break 0` contexts (rejecting `Break i` with `i > 0`).
- **NoBreak rejection**: If no `Break 0` context exists (`NoBreak`), `eval_loop_symbolic` fails with `(Infinite) loops which do not contain breaks are not supported yet`.
- **Multiple-break second evaluation**: When multiple `Break 0` paths exist, branches within a single symbolic evaluation can share freshly allocated loan/borrow IDs created before branching, causing a single-pass join to omit abstractions needed for matching. Aeneas therefore **evaluates the loop body a second time** to generate fresh loan/borrow IDs, joins the combined list of break contexts from both evaluations, reduces, reorders, and attaches loop continuation metadata.
- **Entry, body, and exit synthesis**: `eval_loop_symbolic` then matches the initial pre-loop context to the entry fixed point (`eval_loop_symbolic_apply_loop`), synthesizes the loop body (`eval_loop_symbolic_synthesize_loop_body`, emitting `SymbolicAst.LoopContinue` on `Continue 0` and `SymbolicAst.LoopBreak` on `Break 0`, while raising `Unexpected return` if an unlowered early `Return` reaches loop-body synthesis), and emits `SymbolicAst.Loop`.

Basis: **source**.

#### 2.3 Pure Loop Lowering: Generic `loop` (`ControlFlow`) vs. Structural Recursion

In `src/pure/PureMicroPasses.ml` (blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`) and `src/pure/PureMicroPassesLoops.ml` (at `ac9f1bc5262a5e4ff1e24ca78617121382202727`, witnessed by `tests/src/loops.rs`, `tests/lean/Loops.lean`, `tests/src/mini_tree.rs` blob `fbed6893fb840c0f0bc21bbf3b4e58b69db5ab6c`, and `tests/lean/MiniTree.lean` blob `ae54d4543872edac62862c999a2f91a227489b2f`):

| Loop Lowering Path | Selection Criteria (`Config.ml` / `PureMicroPassesLoops.ml`) | Generated Lean Representation (`tests/lean/Loops.lean`, `MiniTree.lean`) |
| --- | --- | --- |
| Fixed-point combinator (`loop` + `ControlFlow`) | Default when `loops_to_recursive` criteria are not met, or forced by `-loops-no-rec` (`Config.no_recursive_loops = true`). | Emits `@[rust_loop_body] def <fn>_loop.body ... : Result (ControlFlow State Output)` (where `continue` is `ok (.cont next_state)` and `break` is `ok (.done out)`) and `@[rust_loop] def <fn>_loop ... := do loop (fun s => <fn>_loop.body const_args s) init_state`. Witnessed by `iter_loop`, `sum_loop`, `single_break_loop`. |
| Direct recursive helper (`@[rust_loop] ... partial_fixpoint`) | Selected by `loops_to_recursive` when loop input/output analysis finds a structural decrease measure, identity input continuations, equal counts of input/output continuations, and call-compatible reentry/output continuations (or forced by `-loops-to-rec`). | Emits a single recursive `@[rust_loop] def <fn>_loop ... : Result Output := do ... partial_fixpoint` without `ControlFlow` or `.body`, where `continue` becomes a direct recursive call `<fn>_loop ...` and `break` becomes `ok out`. Witnessed by `list_mem_loop`, `list_nth_mut_loop` (returning `Result (T × (T → List T))`), and `Tree.explore_loop`. |

In `backends/lean/Aeneas/Std/Primitives.lean` (blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`), the generic `loop` combinator is itself defined via `partial_fixpoint`:

```lean
def loop (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  match body x with
  | .ok (.cont x') => loop body x'
  | .ok (.done y) => .ok y
  | .fail e => .fail e
  | .div => .div
partial_fixpoint
```

Thus **both** loop lowering shapes rely on `partial_fixpoint` in Lean at this revision.

Basis: **source** + checked-in generated **execution** artifacts.

---

### 3. Recursion, `partial_fixpoint`, Extrinsic Termination, and Divergence

#### 3.1 Symbolic Call Abstraction and Effect Analysis (`can_diverge`, `is_rec`)

- **Symbolic call evaluation (`InterpStatements.ml` L1230–1249, L1346–1477)**: `eval_function_call_symbolic` evaluates ordinary and recursive calls by instantiating the callee's signature (`eval_function_call_symbolic_from_inst_sig`), introducing fresh symbolic return values and region abstractions with `EFunCall` backward continuations, and emitting a call node without inlining the callee body.
- **Divergence and recursion flags (`src/llbc/FunsAnalysis.ml` blob `a2678ba12e8baaaf14fc99c3f061b10edae2da86`, `src/pure/Pure.ml` blob `acde8579d6861a08efae086c72f3156283110342`)**:
  - `FunsAnalysis` computes one effect summary per SCC declaration group: calling any function in the current SCC sets `is_rec = true` and `can_diverge = true`; containing a loop or calling an already-analyzed function with `can_diverge = true` sets `can_diverge = true`.
  - Consequently, a non-recursive caller of a potentially diverging function inherits `can_diverge = true` and propagates `Result.div` via `Result.bind` without needing `partial_fixpoint` on its own definition.
  - **Trait-method gap**: The call visitor in `FunsAnalysis.ml` assumes trait method calls can fail (`can_fail = true`) but **cannot diverge (`can_diverge = false`)** and are stateless (noting a `TODO` for fuel mode).
  - For all non-global, non-builtin functions, `FunsAnalysis.ml` conservatively forces `can_fail = true`, so `SymbolicToPureTypes.ml` wraps their return types in `Result`.

Basis: **source**.

#### 3.2 `Result.div`, `CCPO`, and Lean's `partial_fixpoint` Elaboration

In `src/Translate.ml` (`export_functions_group_scc` L838–913) and `src/extract/ExtractBase.ml` (`fun_decl_kind_to_post_qualif` L1536–1544), single recursive definitions (`SingleRec`) and mutually recursive definitions (`MutRecFirst`, `MutRecInner`, `MutRecLast`, emitted inside a `mutual ... end` block as in `even`/`odd` in `tests/lean/Tutorial/Exercises.lean` blob `6db5aeffbaec39f5d3a335995b948e2d72ca1f07`) all receive the `partial_fixpoint` suffix (`src/extract/Extract.ml` L2356–2361).

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`:

- `src/Init/Internal/Order/Basic.lean` (blob `10e5888e1e43cc87e64509b489de2204fc3ea296`) and `src/Lean/Elab/PreDefinition/PartialFixpoint/Main.lean` (blob `e83567283e7079a0c2f9c1a188d0f096d50dd13f`, L79–115, L154–190) construct the least fixed point of a monotone functional over a chain-complete partial order (`Lean.Order.CCPO`), packing mutual cliques into product domains and generating unfolding equation lemmas.
- `backends/lean/Aeneas/Std/Primitives.lean` (blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`, L62–65, L117–142, L159–179, L196–222) satisfies this obligation by equipping `Result α` with `FlatOrder .div`, `CCPO (Result α)` with bottom `Result.div`, `MonoBind Result`, and `partial_fixpoint_monotone` lemmas for `uncurry`.
- In `tests/lean/BaseTutorial.lean` (blob `52a9947feab2f607729e23c10dfc9e12bba02d41`, L319–384), `i32_id` (over signed 32-bit `Std.IScalar`) is defined via `partial_fixpoint` (diverging to `Result.div` on negative `x`), while `i32_id_spec` (`0 ≤ x.val → i32_id x ⦃ y => y = x ⦄`) proves total termination on non-negative inputs using `termination_by x.val.toNat` and `decreasing_by scalar_decr_tac`.

Basis: Aeneas and Lean 4 **source** + checked-in tutorial **execution** artifacts.

#### 3.3 Comparison of Termination Facilities and the `-decreases-clauses` Suffix Bug

As cataloged in `support/aeneas-extrinsic-termination/termination-facilities-matrix.json` and `support/aeneas-extrinsic-termination/source-map.json`:

| Mechanism | Configuration / Entry Point | Scope & Mutually Recursive Support | Status at `ac9f1bc5262a5e4ff1e24ca78617121382202727` + Lean `v4.30.0-rc2` |
| --- | --- | --- | --- |
| Default `partial_fixpoint` definitions + proof-time `termination_by` / `decreasing_by` | Default (`extract_decreases_clauses = false`, `use_fuel = false`); `WP.spec` in `Std/WP.lean` | Supports single recursion, mutual recursion (`even`/`odd`), and recursive loop helpers. | **Supported and verified in checked-in fixtures** (`BaseTutorial.lean`, `Tutorial/Exercises.lean`, `MiniTree.lean`). |
| Proof-time well-founded loop lemmas (`loop.spec`, `loop.spec_decr_nat`) | `backends/lean/Aeneas/Std/WP.lean` (blob `018c456bcab5374de0b09b17eda0df1a48e2288b`) | Applies to any loop lowered to `Aeneas.Std.loop` over `ControlFlow`. | **Supported**; requires invariant + strict measure decrease on every `.cont x'` branch. |
| Translation-time `-decreases-clauses` | `-decreases-clauses` (`Config.extract_decreases_clauses = true`); registers `<fn>_terminates` and `<fn>_decreases` (`Clauses/Template.lean` with `sorry` macro) | **Rejects mutual recursion** in `Main.ml` (L577–590); rejects combination with `-use-fuel`. | **Grammar conflict on Lean `v4.30.0-rc2`**: `Extract.ml` emits `termination_by ... decreasing_by ...` and then still appends `partial_fixpoint` from `ExtractBase.ml`, which violates `Termination.suffix` in `src/Lean/Parser/Term.lean` (L594–617). No checked-in Lean `Clauses` fixture exists. |
| Fuel parameter threading (`-use-fuel`) | `-use-fuel` (`Config.use_fuel = true`, `PureMicroPassesGeneral.ml` blob `32d37b2363a69b9cf8a765b6446deb753aadc27b`) | N/A for Lean | **Explicitly rejected for the Lean backend** in `src/Main.ml`. |

Basis: Aeneas and Lean 4 **source** + **documentation** (`documentation/aeneas-overview.md`, `documentation/proof-strategies.md`, `documentation/tips-and-tricks.md` blob `c5d891ed25f689f2fe42578efdedc428bdecfe5e`, `tests/README.md` blob `5aa96fab26146514d0ecb2e26fcc40a5a45c94d9`).

---

## Boundaries

- **Not examined**: No fresh execution of Charon, Aeneas, or Lean was performed for this report; all fixture observations (`Loops.lean`, `MiniTree.lean`, `BaseTutorial.lean`, `Tutorial/Exercises.lean`) come from checked-in repository files at `ac9f1bc5262a5e4ff1e24ca78617121382202727`. Non-Lean backend decreases-clause and fuel generation (such as F\* `Clauses` files) was not audited beyond confirming their presence in the repository tree.
- **Unknown**: Whether the join and reduction operators in `InterpJoin.ml` and `InterpReduceCollapse.ml` satisfy formal abstract-interpretation lattice/widening laws (commutativity, associativity, least upper bound) across all admitted Rust programs; and the exact parser error message emitted by Lean `v4.30.0-rc2` if `-backend lean -decreases-clauses` is executed on a singly recursive function.
- **Known not to apply**:
  - `Config.loop_fixed_point_max_num_iters = 2` does **not** bound the number of runtime loop iterations or recursive calls.
  - Emitting a structurally recursive loop helper (`list_mem_loop`, `list_nth_mut_loop`) or a `partial_fixpoint` definition does **not** prove termination; conversely, `partial_fixpoint` does **not** mean the source function actually diverges.
  - `FunsAnalysis.can_diverge = false` does **not** guarantee termination in the presence of trait-method calls (which `FunsAnalysis.ml` currently treats as non-diverging).
  - Concrete-mode loop evaluation (`eval_loop_concrete`) does **not** produce `Result.div` on infinite loops; it re-evaluates `Continue 0` indefinitely.
- **Unsupported**:
  - Syntactically breakless loops (`NoBreak` in `compute_loop_break_context` / `eval_loop_symbolic`), which fail with `(Infinite) loops which do not contain breaks are not supported yet` rather than translating to `Result.div`.
  - Cross-loop `break` or `continue` transfers targeting an outer loop (`index > 0`) during symbolic loop evaluation, unlowered early `Return` inside `eval_loop_symbolic_synthesize_loop_body` (`Unexpected return`), and `UnwindResume` in `eval_statement_raw` (`InterpStatements.ml` L774–791).
  - `-use-fuel` on the Lean backend, and `-decreases-clauses` on mutually recursive function groups in Lean (`Main.ml`).

---

## Evidence

### 1. Primary Aeneas Source and Fixtures — `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`)

- **Loop interpretation, fixed points, and pure loop passes**:
  - `src/interp/InterpLoops.mli`, `src/interp/InterpLoops.ml` (blob `94630c8c9052e326782cc6f71b1f346df451f3e5`), `src/interp/InterpLoopsFixedPoint.ml`, `src/symbolic/SymbolicAst.ml`, `src/pure/PureMicroPassesLoops.ml`, `src/pure/PureMicroPasses.ml` (blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`), `src/pure/PureMicroPassesGeneral.ml` (blob `32d37b2363a69b9cf8a765b6446deb753aadc27b`).
- **Effect analysis, SCC classification, CLI flags, and extraction**:
  - `src/llbc/FunsAnalysis.ml` (blob `a2678ba12e8baaaf14fc99c3f061b10edae2da86`), `src/pure/Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`), `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`), `src/Translate.ml` (blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`, L838–913, L1411–1430), `src/extract/ExtractBase.ml` (blob `4fc8a3f35643ba66555f0889790d50993feef1b9`, L1536–1544), `src/extract/Extract.ml` (blob `52754e4fdb25b50fce63abe2d2184751d69632e8`, L2356–2361), `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`, L216–245), `src/Main.ml` (blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`, L112–123, L577–590).
- **Lean primitives, WP library, documentation, and checked-in fixtures**:
  - `backends/lean/Aeneas/Std/Primitives.lean` (blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`, L62–65, L117–142, L159–179, L196–222), `backends/lean/Aeneas/Std/WP.lean` (blob `018c456bcab5374de0b09b17eda0df1a48e2288b`, L23–36, L54–61, L178–188).
  - `documentation/aeneas-overview.md` (blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`), `documentation/proof-strategies.md` (blob `2b10ed04a1594d6b8a95a80c742af10885974143`), `documentation/tips-and-tricks.md` (blob `c5d891ed25f689f2fe42578efdedc428bdecfe5e`), `tests/README.md` (blob `5aa96fab26146514d0ecb2e26fcc40a5a45c94d9`).
  - `tests/src/loops.rs`, `tests/lean/Loops.lean`, `tests/src/mini_tree.rs` (blob `fbed6893fb840c0f0bc21bbf3b4e58b69db5ab6c`, L13–20), `tests/lean/MiniTree.lean` (blob `ae54d4543872edac62862c999a2f91a227489b2f`, L33–48), `tests/lean/BaseTutorial.lean` (blob `52a9947feab2f607729e23c10dfc9e12bba02d41`, L319–384), `tests/lean/Tutorial/Exercises.lean` (blob `6db5aeffbaec39f5d3a335995b948e2d72ca1f07`).

### 2. Symbolic Join and Fixed-Point Source — `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`

- `src/interp/InterpJoin.mli` (L5–60, L75–126), `src/interp/InterpJoin.ml` (`join_ctxs` L640–923, `join_ctxs_list` L924–1013, `match_ctx_with_target` L1348–1665), `src/interp/InterpJoinCore.ml` (`join_info_or_update` L9–32, `compute_fixed_abs_ids` L859).
- `src/interp/InterpMatchCtxs.mli` (L124–159), `src/interp/InterpMatchCtxs.ml` (`MakeJoinMatcher` L621–766, `match_ctxs` L2176–2390), `src/llbc/Values.ml` (L181–249, L1572–1576).
- `src/interp/InterpReduceCollapse.ml` (L624–697, `reduce_ctx` L840–871).
- `src/interp/InterpLoopsFixedPoint.ml` (`loop_abs_reorder_and_add_info` L13–41, `compute_loop_entry_fixed_point` L44–237, `compute_loop_break_context` L239–381), `src/interp/InterpLoops.ml` (`eval_loop_symbolic_apply_loop` & `eval_loop_symbolic_synthesize_loop_body` L78–343, `eval_loop_symbolic` L344–505).
- `src/interp/InterpStatements.ml` (`eval_statement_raw` L774–791, `eval_switch_with_join` L1053–1199, `eval_function_call_symbolic` L1230–1249, `eval_function_call_symbolic_from_inst_sig` L1346–1477), `src/interp/Invariants.ml` (L1002–1011), `src/Config.ml` (L176–182).

### 3. Lean 4 `partial_fixpoint` and Grammar Source — `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`)

- `src/Lean/Parser/Term.lean` (blob `16b73a52ad5c2e6819a9d009012a5e2d75f30559`, L594–617): `Termination.suffix`, `partial_fixpoint`, `termination_by`, `decreasing_by`.
- `src/Init/Internal/Order/Basic.lean` (blob `10e5888e1e43cc87e64509b489de2204fc3ea296`): `CCPO` and `FlatOrder`.
- `src/Lean/Elab/PreDefinition/PartialFixpoint/Main.lean` (blob `e83567283e7079a0c2f9c1a188d0f096d50dd13f`, L79–115, L154–190): mutual packing, monotonicity proof obligations, and fixed-point construction.

### 4. Preserved Package Support Artifacts

- `support/aeneas-loops/revalidation.json`: revalidation targets and specimen mapping for loop translation at `ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- `support/aeneas-joins-loops-fixed-points-21345f80/source-reading.json`: blob identities and line ranges for context joins, matching, and loop fixed points at `21345f80fa212c596f6437378d7d57984fa2ea77`.
- `support/aeneas-extrinsic-termination/source-map.json` and `support/aeneas-extrinsic-termination/termination-facilities-matrix.json`: source map and comparison matrix of extrinsic termination mechanisms at `ac9f1bc5262a5e4ff1e24ca78617121382202727`.

---

## Revalidation

To revalidate this report on an updated Aeneas or Lean revision:

1. **Symbolic join and loop fixed-point diff**:
   - Inspect `InterpJoin.join_ctxs` (left non-fixed ID refresh) and `match_ctx_with_target` (`PRight` projection + recorded collapse replay).
   - Inspect `InterpLoopsFixedPoint.compute_loop_entry_fixed_point` (`Config.loop_fixed_point_max_num_iters`), `compute_loop_break_context` (second evaluation on multiple breaks), and `InterpLoops.eval_loop_symbolic` (check whether `NoBreak` is still rejected or lowered to `Result.div`).
   - Inspect `FunsAnalysis.ml` to see whether trait-method calls still omit `can_diverge` propagation.
2. **Pure loop lowering, `partial_fixpoint`, and `-decreases-clauses` diff**:
   - Diff `PureMicroPassesLoops.ml` (`loop_satisfies_recursive_criteria_aux`, `decompose_loops`, `loops_to_fixed_points`) and `ExtractBase.ml` (`fun_decl_kind_to_post_qualif`) / `Extract.ml` (`extract_fun_decl_gen`). Specifically check whether `Extract.ml` suppresses `partial_fixpoint` when `has_decreases_clause` is true, and compare against `Termination.suffix` in Lean's `src/Lean/Parser/Term.lean`.
   - Diff `backends/lean/Aeneas/Std/Primitives.lean` (`Result`, `loop`, `CCPO`, `MonoBind`) and `backends/lean/Aeneas/Std/WP.lean` (`spec_div`, `spec_equiv_exists`, `loop.spec`, `loop.spec_decr_nat`).
3. **Minimal execution probe matrix**:
   - Translate and elaborate: (a) a scalar `while` counter loop (`iter`), (b) a structural list-tail mutable loop (`list_nth_mut`), (c) a loop with two break paths sharing a pre-branch loan, (d) an unconditional `loop {}` (`NoBreak`), (e) a singly recursive partial function (`i32_id`) and a mutually recursive pair (`even`/`odd`), and (f) a singly recursive function with `-backend lean -decreases-clauses`.
   - Confirm that (a) uses `loop` + `ControlFlow`, (b) becomes a recursive `@[rust_loop] ... partial_fixpoint` helper, (d) triggers the `NoBreak` error, (e) elaborates with `partial_fixpoint` and supports `WP.spec` proofs with `termination_by`/`decreasing_by` and `loop.spec_decr_nat`, and (f) tests whether the `termination_by ... decreasing_by ... partial_fixpoint` suffix conflict has been fixed.
