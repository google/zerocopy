# Aeneas context joins, loop fixed points, and recursive calls

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

At Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`, a context join constructs an ownership summary that can guide synthesis. It is not by itself a synthesized computation from either incoming branch. Joining refreshes non-fixed abstraction identifiers on the left; synthesis must recover computational provenance by matching a real incoming context to the summary, projecting the right side, and reproducing abstraction merges with continuations.

Loop analysis repeatedly evaluates a symbolic body, joins entry with continue contexts, reduces the result, and checks equivalence modulo identifier renaming. The configured cap is **two analysis iterations**. This is a convergence guard, not a bound on Rust execution or a proof of termination. Successful analysis is followed by separate entry/body/exit synthesis. Symbolic ordinary function calls use instantiated signatures and abstractions; they do not obtain their meaning by running this loop fixed-point algorithm over recursive call bodies.

## Applicability

This package addresses A15 (joins, matching, fixed points) and A16 (loops and recursion) through a bounded reading of selected OCaml files from [AeneasVerif/aeneas at the exact pin](https://github.com/AeneasVerif/aeneas/tree/21345f80fa212c596f6437378d7d57984fa2ea77), acquired read-only on 2026-10-15. It covers the symbolic interpreter's analysis and symbolic-AST construction. It does not establish Rust-to-LLBC fidelity or backend recursion/partiality semantics, and it does not report an interpreter run or a checked proof.

Configuration facts below describe source defaults or constants at this pin. In particular, `loop_fixed_point_max_num_iters` is an immutable OCaml binding to `2`; `sanity_checks` defaults false; `recover_joins` defaults true; and `loops_to_recursive_functions` is a separate mutable option defaulting false. The downstream meaning of that last extraction option is not examined here. These are not reconstructed command-line settings from an execution.

## Findings

### 1. Context join preserves a common skeleton and abstracts differences

Basis: source + documentation. [`InterpJoin.join_ctxs`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoin.ml#L640-L923), [`InterpJoinCore.compute_fixed_abs_ids`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoinCore.ml#L859).

The two inputs have ordered environment entries for locals, dummy values, abstractions, and frames. `join_ctxs` intersects dummy identifiers and computes abstractions that occur unchanged in both contexts. It refreshes the **left** non-fixed abstraction identifiers, partitions each environment into the retained part and its remaining entries, matches corresponding retained entries, and turns suitable non-common structure into marked abstraction content. `PLeft` and `PRight` record which incoming context supplied a component; `PNone` denotes unmarked content. Retained ordinary locals are matched rather than dropped because they must occur on both sides.

Different literals can become a fresh symbolic value. The join records the new symbol's left and right source values in `symbolic_to_value`. For admissible values containing borrows, a helper refreshes erased regions and creates abstraction projections linking both incoming values to the fresh symbolic summary. It includes a static-region abstraction when needed. When continuations are enabled, the helper also constructs expression content that can project back to each input. This is materially richer than joining scalar values alone. [`InterpMatchCtxs.MakeJoinMatcher`, distinct literals and region-bearing symbolic summaries](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpMatchCtxs.ml#L621-L766).

The result type is either join information or a request to update an input environment (`LoanInLeft`, `LoanInRight`, and plural forms, among the update constructors). The list join simplifies inputs, attempts a join, ends the requested loans with no synthesis, retries, then collapses projection markers. It returns updated inputs as well as the joined summary. A caller must account for those updates and cannot assume its original inputs are already matched to the summary. [`join_ctxs_list`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoin.ml#L924-L1013), [`join_info_or_update`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoinCore.ml#L9-L32).

### 2. Analysis joins and synthesis matching have different contracts

Basis: source + documentation. The public [join contract](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoin.mli#L75-L126) warns that refreshed abstractions can otherwise appear “out of nowhere” during synthesis. It describes an earlier dangling-identifier problem caused by refreshing the opposite side. A joined state may be used for fixed-point or exit analysis; a synthesis caller must project it appropriately. `with_abs_conts = true` alone does not erase that provenance obligation.

`match_ctx_with_target` uses the summary as source and the real incoming state as target. Its current algorithm is:

1. Simplify unnecessary target borrows/loans, prepare the match by ending or moving obstructing content, and simplify again. The source explains the double simplification as avoiding currently unsupported matches.
2. Destructure appropriate fresh shared loans and reduce the target with continuations enabled.
3. Join source and target with continuations enabled.
4. Collapse an unprojected copy to **record** the sequence of abstraction merges and shared-borrow insertions.
5. Project the pre-collapse joined context to `PRight`, which corresponds to the target, and retain only the right shared-borrow insertions. Replay the recorded merge sequence on that projected context. Track static ownership through the sequence as well.
6. Simplify empty abstractions without snapshots that might refer to not-yet-bound outputs, reorder fresh abstractions, and match the result against the summary.
7. Compose source-to-joined and joined-to-target maps to recover actual symbolic inputs and abstraction arguments; return these with the symbolic-AST continuation.

The implementation records the collapse sequence before projection because collapsing continuations using both sides and only then trying to project them is difficult; projecting first without the sequence can fail to perform necessary merges. This ordering is a concrete algorithmic constraint. [`match_ctx_with_target`, preparation](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoin.ml#L1348-L1417), [join, collapse, projection and replay](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoin.ml#L1419-L1535), [matching and input recovery](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoin.ml#L1547-L1665).

Derived semantic requirement: the summary must cover both incoming states, while each branch's synthesized continuation must be justified using **that branch's** actual values and abstractions. Shape agreement with a fabricated summary is insufficient. The mapping and right-projection machinery is where the inspected implementation recovers that branch-specific provenance.

### 3. Equality for convergence is alpha equivalence of ownership state

Basis: source. [`InterpMatchCtxs.match_ctxs`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpMatchCtxs.ml#L2176-L2390), [`ctxs_are_equivalent` contract](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpMatchCtxs.mli#L124-L159).

The matcher initializes injective identifier substitutions with identity mappings for fixed identifiers. It compares the environment structure while building correspondences for regions, borrow/loan identifiers, abstractions, and symbolic values. In equivalence mode it compares up to this renaming; in mapping mode it can associate source symbols with target values. Shared-value lookup callbacks permit matching a partial environment without losing access to the full context's shared loans.

Abstraction matching checks identifiers, parents, static ownership, region mappings, ended-sub-abstraction levels, and corresponding `avalues`; it optionally compares abstraction kind and `can_end`. It explicitly ignores `cont`. The synthesis matching call uses `check_equiv:false`, `check_kind:false`, and `check_can_end:false`, with frozen source abstractions fixed. The fixed-point call uses equivalence mode. These are distinct operations, so “the contexts match” is incomplete unless mode and fixed identifiers are supplied.

Meta-only equality in `Values.ml` and the explicit omission of continuations mean convergence is about the analysis ownership state, not syntactic equality of synthesized programs. This is intentional separation of concerns. It still requires a separate correctness argument that the recovered computational continuations correspond to the accepted state transitions. [`Values`, meta equality](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L181-L249), [captured meta-environment equality](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L1572-L1576).

### 4. Branch joins introduce outputs and backward continuations

Basis: source. [`InterpStatements.eval_switch_with_join`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpStatements.ml#L1053-L1199).

This helper expects surviving results to be `Unit`, because it is used for branches eligible for joining rather than branches containing return/break/continue; explicit panic paths have already stopped. No surviving contexts produce no continuation state; one context continues directly; multiple contexts produce a joined summary. Fresh summary abstractions receive `EJoin` continuations, changed symbolic values become outputs, and fresh abstractions become abstraction outputs.

Each actual branch context is independently matched to the summary using `match_ctx_with_target`. The resulting branch emits `SA.Join` with its actual output values and abstraction arguments. The branch expression is then bound by a symbolic `Let` whose outputs are the summary symbols and abstractions; following code executes in the joined state. Thus a successful branch join has a value-producing forward component and may also produce backward continuations needed when references later end.

The source describes recoverable join failure as allowing code after the switch to be duplicated. This is a limitation-management strategy for unsupported joins, not evidence that all joins succeed or that arbitrary unsupported borrowing becomes accepted. The exact caller fallback and all exceptions were not comprehensively traced in this package; the helper's recoverable flag and intended behavior are directly inspected.

### 5. Loop entry analysis is a bounded join/reduce/equivalence iteration

Basis: source + documentation. [`InterpLoopsFixedPoint.compute_loop_entry_fixed_point`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpLoopsFixedPoint.ml#L44-L237).

The algorithm first reborrows shared loans and symbolic borrows associated with fixed abstractions, without continuation synthesis. This prevents later symbolic expansions and additional shared borrowing from changing the supposedly fixed abstractions. The reborrowing deliberately loses information to simplify joins. Only appropriate loan identifiers with borrows in regular values are reborrowed; an abstraction-to-abstraction shared edge is not automatically treated the same way. [`reborrow_ashared_loans_symbolic_borrows` contract](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoin.mli#L5-L60).

Starting from that state, one analysis iteration:

1. Symbolically evaluates the loop body and collects its result contexts.
2. Keeps `Continue 0` contexts; ignores return, panic, and break contexts for entry convergence. A continue to an outer loop raises an unsupported-case error.
3. Joins the current entry summary with continue states, updating the tracked fixed symbolic/abstraction identifiers by intersection with newly observed states.
4. Computes fixed abstractions relative to the original entry and original dummy identifiers; reduces the joined state with `with_abs_conts:false`.
5. Checks equivalence modulo allowed identifier renaming. If unequal, repeats with the reduced summary; if no iterations remain, raises an explicit failure.

`Config.loop_fixed_point_max_num_iters = 2`. The failure says it could not compute a loop fixed point in the allotted iterations. With `fail_hard` and one iteration left, the code directly uses the throwing matcher to expose a useful stack instead of swallowing the mismatch. After convergence, it reorders fresh abstractions and adds `ELoop` continuation expressions. [`Config.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Config.ml#L176-L182), [`loop_abs_reorder_and_add_info`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpLoopsFixedPoint.ml#L13-L41).

The reduce operation merges newly introduced abstraction structures connected by borrows/loans or symbolic projectors. Its documentation calls this the analogue of abstract interpretation's widening. Collapse additionally eliminates left/right markers, including duplicate marked borrows/loans; reduction without markers and marker collapse are related but distinct uses of the machinery. Some long examples describe an older dummy-conversion arrangement, and the comment explicitly says that conversion is no longer done there. The current call paths and helpers should control interpretation of those examples. [`InterpReduceCollapse`, reduce description and distinction](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpReduceCollapse.ml#L624-L697), [current `reduce_ctx`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpReduceCollapse.ml#L840-L871).

### 6. Loop exits are analyzed separately, including a fresh-ID second evaluation

Basis: source. [`compute_loop_break_context`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpLoopsFixedPoint.ml#L239-L381).

The exit pass starts from the entry fixed point, removes relevant loop continuation expressions for analysis, and evaluates the body to collect `Break 0` contexts. It distinguishes no breaks, one break, and multiple breaks. A break to an outer loop is explicitly rejected in this collection pass.

For multiple break contexts it evaluates the body **again** and joins the combined list from both evaluations. The source explains that branch paths in a single evaluation can share freshly introduced loan/borrow identifiers; joining only those paths can omit abstractions later required for matching. Reevaluation obtains fresh identifiers so the join introduces the necessary structure. This is analysis reevaluation, not a claim that the emitted Rust behavior executes the body twice. The result is reduced, reordered, and equipped with loop continuation information; fresh function-call abstractions in the body are also classified as loop abstractions for this purpose.

`eval_loop_symbolic` currently rejects `NoBreak` with the error that infinite loops without breaks are unsupported. That guard is phrased in terms of the collected break category; the source read here does not justify broad claims about every possible divergence shape in Rust. [`InterpLoops.eval_loop_symbolic`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpLoops.ml#L344-L435).

### 7. Successful analysis is followed by entry, body, and exit synthesis

Basis: source. [`eval_loop_symbolic`, synthesis and AST assembly](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpLoops.ml#L395-L505), [`eval_loop_symbolic_apply_loop`, `eval_loop_symbolic_synthesize_loop_body`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpLoops.ml#L78-L343).

The loop driver obtains ordered symbolic input parameters and loop abstractions from the fixed point, computes exit information, matches the original state to the entry summary, and synthesizes the body separately. Reentry and break handling match actual body states to the appropriate summaries, producing value and abstraction arguments. The resulting `SymbolicAst.Loop` records the loop identifier, entry symbols/abstractions and their argument maps, break symbols/abstractions, the loop expression, the following expression, and entry context. The driver continues with the break context.

Derived correspondence requirements are therefore separate: analysis convergence must provide an inductive ownership summary; entry matching must establish the initial state satisfies it; each synthesized reentry must reestablish it; break matching must establish the exit summary; and the loop's backward continuations must return the values required by external loans. Matching up to renaming alone proves none of these semantic relations. The source implements the machinery intended to maintain them; this report does not establish its complete correctness.

The exit categories have additional limits in current source. Loop body synthesis raises `Unexpected return` on an early `Return`, even though entry analysis merely filters such results out; preprocessing may eliminate some source shapes before this path, and that coverage was not checked. `eval_statement_raw` passes `Break` and `Continue` indices through, preserves `Return`, maps panic/unwind-termination/undefined-behavior nodes to panic behavior (with no continuing symbolic context), and explicitly rejects `UnwindResume`. Consequently the implementation's panic node does not by itself describe Rust unwinding or cleanup semantics. Some comments in loop synthesis still say breaks are forbidden, whereas the immediately following executable branches handle breaks; the code paths, not that stale sentence, support the findings above. [`eval_loop_symbolic_synthesize_loop_body`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpLoops.ml#L159-L184), [`eval_statement_raw`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpStatements.ml#L774-L791).

### 8. Source recursion uses signature abstraction; termination is a separate question

Basis: source + derived. [`InterpStatements.eval_function_call_symbolic`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpStatements.ml#L1230-L1249), [`eval_function_call_symbolic_from_inst_sig`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpStatements.ml#L1346-L1477).

Ordinary symbolic function-call handling creates a symbolic return value and region abstractions from the instantiated signature, with `EFunCall` backward expressions and a synthesized regular call node. This path does not recursively interpret the callee body. Consequently, a recursive call can be represented through the same interface rather than by unbounded symbolic inlining of that call. This is a statement about the inspected call path, not proof that every recursive program or mutually recursive declaration group is supported.

Loop entry fixed points summarize ownership states within loop translation; source function recursion is represented by calls. The number `2` in the former does not bound recursive calls in the latter. The separate proof obligations are call-summary correctness, recursive-function semantics, failure/partiality behavior, and any termination argument required by a selected backend or proof interface. This package does not trace downstream recursive-definition generation, measure inference, fuel, or Lean WP partiality. A successful borrow summary must not be advertised as proof of functional correctness or termination.

## Boundaries

- **Unsupported in identified paths:** multiple join/destructure helpers explicitly reject nested-borrow shapes; outer-loop continues and breaks are rejected by the fixed-point collectors; `NoBreak` is rejected by the symbolic loop driver. Assertions in loop body synthesis also reject some nonzero loop indices. This does not establish a blanket absence of every form of syntactically nested loop.
- **Unknown:** convergence for all admitted loops, leastness of a computed summary, commutativity/associativity of the actual implementation join, and a complete semantic ordering on current contexts. Source comments call reduction a widening analogue; this report has not proved the corresponding abstract-domain laws. The two-iteration cap is an implementation guard, not a verified bound theorem.
- **Not examined:** complete matcher cases, all error recovery behavior, full normalization order, all loop tests, backend recursive functions, totality/partiality models, or concrete runs.
- **Current versus paper:** projection markers in `Values.ml` link to a paper's section 5, but this report has not used that paper as theorem evidence. Current synthesis includes evalue continuation composition, right projection with merge replay, static ownership tracking, and a special second break evaluation. A paper-level join/fixed-point theorem cannot be assumed to apply to these exact implementation paths without a correspondence argument.

Invariant preservation remains relevant throughout: identifier freshness and fixed-ID stability, borrow/loan correspondence, mutable projector noncollision, shared-value lookup consistency, endability of frozen/static abstractions, and stable input/output ordering must survive joins, reductions, projection, and replay. `Invariants.check_invariants` is gated by `Config.sanity_checks`; it is useful dynamic checking when enabled, not proof evidence, and this investigation did not enable or run it. [`Invariants.check_invariants`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/Invariants.ml#L1002-L1011).

## Evidence

All linked implementation facts concern repository `AeneasVerif/aeneas`, full revision `21345f80fa212c596f6437378d7d57984fa2ea77`. The companion `source-reading.json` records path/blob identities, selected reading regions, and A15/A16 coverage. Source files were acquired through read-only connected GitHub tools; full responses were held transiently to select relevant regions. No build, installation, Docker action, upstream execution, external write, or Git mutation was performed for this package. Evidence roles are source, source-comment documentation, and explicitly identified derived requirements; no execution or normative proof evidence is claimed.

## Revalidation

The cheapest source checks for another pin are narrowly discriminating:

1. Inspect `join_ctxs` for which side's non-fixed abstraction identifiers are refreshed; inspect `match_ctx_with_target` for right projection and recorded merge replay. A change here requires reviewing both provenance and continuation composition.
2. Inspect `match_ctxs` for fixed-identifier injection, ignored continuations, ended-level comparison, and the options used by equivalence versus synthesis matching.
3. Inspect `compute_loop_entry_fixed_point` and `Config.loop_fixed_point_max_num_iters` together. Confirm continue filtering, reduction with absent continuations, and the exact convergence check rather than merely searching for the constant.
4. Inspect `compute_loop_break_context` for second evaluation and the no/single/multiple distinction; inspect `eval_loop_symbolic` for the no-break guard and the later synthesis stages.
5. Inspect ordinary symbolic call handling separately from loop code before drawing conclusions about recursion or termination.

For future execution-based revalidation, useful minimal discriminators are a branch returning two distinct mutable reborrows, a list-tail mutable traversal requiring an ownership fixed point, a loop with two break paths sharing a newly created loan before branching, and a loop without a break. Preserve input Rust, exact LLBC, invocation flags, symbolic trace, accepted/rejected result, and generated loop/continuation shape. A separate recursive call example can show signature abstraction without body inlining. None of these proposed probes was executed here; none alone establishes general join laws or semantic soundness.
