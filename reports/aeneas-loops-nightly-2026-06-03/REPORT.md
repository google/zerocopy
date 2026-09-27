# Aeneas loop translation at nightly-2026.06.03

## Summary

At Aeneas `nightly-2026.06.03`, a Rust loop does not survive as Rust-style control flow in the Lean output. Aeneas first symbolically executes the loop until the abstract interpreter reaches a stable loop-entry context. That context determines which symbolic values and borrow abstractions become loop state. A later pure-AST pipeline then extracts the loop into an auxiliary Lean definition and chooses between two shapes:

- a call to Aeneas's generic `loop` fixed-point combinator, with `ControlFlow.cont` carrying the next iteration's state and `ControlFlow.done` carrying the loop result; or
- a directly recursive loop helper when Aeneas can recognize a structural decrease and its continuation plumbing meets additional restrictions.

Both shapes are partial in Lean at this revision. The generic `loop` combinator is defined with Lean's `partial_fixpoint`, and the checked-in generated examples also put `partial_fixpoint` on structurally recursive loop helpers. The structural-decrease analysis therefore changes the generated program shape; it is not itself a Lean termination proof.

The static loop-entry fixed point is a separate concept from Lean's `partial_fixpoint`. Aeneas bounds the former to two abstract-interpretation iterations as a sanity check. This is not a bound on the number of iterations the translated Rust loop may execute.

For Anneal, the important interface is the generated loop helper's state. Ordinary mutable locals become explicit arguments and results. Borrow state can also affect the helper signature: for example, the checked-in translation of a loop returning `&mut T` returns both the selected value and a backward function that rebuilds the original list when the value is updated. Verification of a non-structural loop can use Aeneas's `loop.spec` theorem, which asks for a loop invariant plus a well-founded measure for every `cont` step.

## Applicability

This report describes `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the revision selected by Aeneas release `nightly-2026.06.03`. It focuses on the loop-specific path: loop-state discovery, `break`/`continue` lowering, borrow-aware state, generated Lean shape, and the loop proof interface.

It does not inventory ordinary Rust recursion, Aeneas's general partial-function facility, extrinsic termination support, or every generated loop testcase. Those are adjacent subjects. In particular, `partial_fixpoint` is discussed here only where it determines the loop interface.

## Findings

### Aeneas computes loop state by finding an abstract loop-entry fixed point

The symbolic interpreter does not choose loop parameters from Rust syntax alone. `eval_loop_symbolic` allocates a loop id, calls `compute_loop_entry_fixed_point`, records the abstractions marked for that loop, computes the symbolic values introduced or modified between the original context and the fixed-point context, and separately computes the context reached by exits from the loop.

`compute_loop_entry_fixed_point` repeatedly evaluates the loop body, keeps only contexts that reach `Continue 0`, joins those contexts back into the loop-entry context, reduces the result, and checks context equivalence. The configured maximum is two iterations. The source describes this bound as a sanity check: Aeneas expects a fixed point quickly and treats failure to find one as likely a translator bug.

This fixed point is about the *shape of the symbolic environment*. It identifies values, loans, borrows, and abstractions that must be stable across iterations. It is not the semantic fixed point used later to define potentially diverging Lean functions.

The borrow-specific machinery is visible in the loop interpreter. Before entering a symbolic loop, Aeneas simplifies unused borrow state and reborrows shared loans so fixed abstractions are not mutated by later loop analysis. The loop fixed-point representation can introduce loop abstractions that relate mutable borrows on entry to loans in the next iteration. This is why the resulting loop state can include backward continuations rather than only ordinary scalar locals.

### `continue` carries the next loop state; `break` carries loop outputs

Aeneas's symbolic AST has explicit `LoopContinue`, `LoopBreak`, and `Loop` nodes. A `Loop` records ordered input symbolic values and abstractions, output symbolic values and abstractions at the break context, the symbolically executed body, and the expression after the loop.

When the symbolic evaluator reaches a continue, it matches that context back to the fixed-point context and emits `LoopContinue` with the reordered loop inputs. When it reaches an exit, it reduces or joins the exit contexts and emits `LoopBreak` with the values and abstractions that leave the loop.

The later pure pass lowers these nodes differently depending on the chosen loop shape. For a recursive helper, `continue` becomes a recursive call and `break` becomes `Result.ok` of the loop result. For a non-recursive helper, `continue` becomes `Result.ok (ControlFlow.cont next_state)` and `break` becomes `Result.ok (ControlFlow.done output)`.

Cross-loop control transfers remain restricted in this implementation: the interpreter asserts that a `break` or `continue` handled by the current loop has index zero. Checked-in generated output contains nested loops, so this is not a blanket prohibition on nesting; it is a limitation on control transfers that target an outer loop from the loop currently being synthesized.

A genuinely exitless loop is also rejected by this symbolic path. If Aeneas finds no break context, `eval_loop_symbolic` raises `(Infinite) loops which do not contain breaks are not supported yet`. That is narrower than saying all syntactically unbounded Rust loops fail: source loops whose normalized control flow has an exit are represented normally.

### The pure pipeline extracts every loop into an auxiliary definition

Before extraction, Aeneas runs several loop-specific pure-AST passes. It decomposes tuple outputs, simplifies composed backward continuations, filters unused loop inputs and outputs, reorders outputs, tries to recognize loops that are naturally recursive, and then calls `decompose_loops`.

`decompose_loops` creates a separate function declaration for each loop. Values used by the body but not modified by the iteration become constant arguments to the helper; iteration-varying state remains in the loop input tuple. The parent Rust function is rewritten to call the helper. A later `loops_to_fixed_points` pass removes any remaining internal `Loop` nodes by replacing them with the generic fixed-point operator. Extraction therefore never expects a raw `Loop` AST node.

The Lean backend tags the generated declarations with `@[rust_loop]`, and separately extracted loop-body functions with `@[rust_loop_body]`. Source spans in the generated comments point back to the Rust loop.

### Default translation chooses recursive helpers only when a structural-decrease heuristic succeeds

At this revision, `loops_to_recursive_functions` defaults to `false`, while `no_recursive_loops` also defaults to `false`. The command line exposes `-loops-to-rec` to force recursive loop helpers and `-loops-no-rec` to disable the attempt. With neither flag, Aeneas decides per loop.

The automatic test is stronger than merely seeing a syntactically smaller value. Aeneas computes relationships between loop inputs and outputs, requires a structural termination measure, requires input continuations to be identities, requires loop-back and output continuations to be calls to the corresponding input continuations, and requires the number of input and output continuations to agree. Only then does the `loops_to_recursive` pass replace internal continue points with recursive calls.

The source comment explains the intended use: if each continue dives deeper into a recursive data structure, a recursive function is a natural presentation of the loop. Otherwise Aeneas leaves the loop in fixed-point form.

This analysis is a translation heuristic, not a proof that Lean's termination checker will accept a total recursive definition. The generated recursive loop helpers in the pinned test corpus use `partial_fixpoint`.

### Non-structural loops become `loop body initial_state`

The simplest checked-in example starts from:

```rust
pub fn iter(max: u32) -> u32 {
    let mut i = 0;
    while i < max {
        i += 1;
    }
    i
}
```

Its generated Lean has a body helper

```lean
@[rust_loop_body]
def iter_loop.body
  (max : Std.U32) (i : Std.U32) : Result (ControlFlow Std.U32 Std.U32) := ...
```

and a loop helper

```lean
@[rust_loop]
def iter_loop (max : Std.U32) (i : Std.U32) : Result Std.U32 := do
  loop (fun i1 => iter_loop.body max i1) i
```

`max` is constant across iterations, while `i` is carried by `ControlFlow.cont`. Examples with several mutable locals use a tuple for the varying state. The generated `sum_loop`, for example, carries `(i, s)` while keeping `max` as a separate constant argument.

The generic Lean helper is itself defined by `partial_fixpoint`:

```lean
def loop (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  match body x with
  | .ok (.cont x') => loop body x'
  | .ok (.done y) => .ok y
  | .fail e => .fail e
  | .div => .div
partial_fixpoint
```

Thus ordinary loop execution has the same `Result`-level divergence representation as other Aeneas partial computations.

### Structurally decreasing list traversals become recursive loop helpers

Aeneas recognizes a different shape for loops that advance structurally through a recursive datatype. The checked-in Rust `list_mem` repeatedly assigns `ls = tl`. Its generated Lean helper directly recurses on `tl`:

```lean
@[rust_loop]
def list_mem_loop (x : Std.U32) (ls : List Std.U32) : Result Bool := do
  match ls with
  | .Cons y tl => if y = x then ok true else list_mem_loop x tl
  | .Nil => ok false
partial_fixpoint
```

The same transformation applies to mutable traversals when the continuation plumbing fits the recursive criteria. For `list_nth_mut`, the loop helper returns `Result (T × (T → List T))`: recursive calls traverse the tail, while the returned function rebuilds each `Cons` layer on the way back. The original mutable reference has therefore become a pure value plus a backward update function.

This distinction matters for Anneal proofs. Two Rust loops with similar surface syntax can expose materially different Lean proof interfaces: one through `Aeneas.Std.loop` and `ControlFlow`, another through a named recursive helper.

### Explicit `break` maps to `ControlFlow.done` on the fixed-point path

The test `single_break` is a direct source-level example:

```rust
fn single_break(d: &[u8]) {
    loop {
        if d[0] == 0 {
            break;
        }
    }
}
```

The checked-in output makes the exit explicit in the body helper: the true branch returns `ok (done ())`, while the other branch returns `ok (cont ())`. The enclosing `single_break_loop` calls the generic `loop` combinator. This makes the semantic role of `break` concrete: it is an ordinary successful loop result, not an exception-like exit.

### The generic loop proof rule separates execution semantics from termination evidence

Aeneas's Lean library defines `loop.spec`. To prove a postcondition for `loop body x`, the caller supplies:

- a measure from loop state into a type with a `WellFoundedRelation`;
- an invariant over loop states;
- a postcondition over completed loop results; and
- a proof that each body step either produces a `done` value satisfying the postcondition or a `cont` state satisfying the invariant whose measure strictly decreases.

There is also `loop.spec_decr_nat` specialized to a natural-number measure.

The generated program therefore does not need to carry a termination certificate. The verification layer can establish termination together with the loop invariant when proving the desired specification. If no such proof is supplied, the generated `partial_fixpoint` still gives the translated program a meaning that includes `Result.div`.

## Boundaries

This report is source-based. No fresh Aeneas translation, Lean compilation, or proof was executed in this run. Generated Lean examples under `tests/lean/` are checked-in artifacts at the pinned Aeneas revision; they establish what that repository snapshot records, not that this run regenerated them successfully.

The report does not claim that every Rust loop accepted by rustc is accepted by Aeneas. The pinned source has explicit unsupported cases, including the lack of a break context and cross-loop `break`/`continue` handling in the current symbolic loop. Other preprocessing or unsupported-language restrictions can fail before the mechanisms described here apply.

The report also does not treat Aeneas's abstract loop-entry fixed point as a semantic equivalence proof. It is internal translation machinery used to choose a stable symbolic state and can fail when the expected context fixed point is not found within the configured sanity bound.

The structurally recursive path should not be confused with Lean total recursion. Although Aeneas detects a structural decrease to choose that representation, the checked-in Lean loop helpers at this revision still use `partial_fixpoint`.

Ordinary Rust recursive functions, the full `partial_fixpoint` trust/semantic story, generated function specifications, and extrinsic termination facilities are separate inventory items.

## Evidence

- **source** — Aeneas `InterpLoops.mli` documents the loop fixed-point abstraction using a mutable-list traversal and identifies the loop abstraction derived from the fixed-point environment: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/interp/InterpLoops.mli>.
- **source** — `InterpLoops.ml` implements concrete and symbolic loop evaluation, context matching for `continue`/`break`, loop input/output synthesis, the no-break rejection, and construction of `SymbolicAst.Loop`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/interp/InterpLoops.ml>.
- **source** — `InterpLoopsFixedPoint.ml` joins continue contexts, checks context equivalence, enforces the fixed-point iteration bound, and computes joined break contexts: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/interp/InterpLoopsFixedPoint.ml>.
- **source** — `SymbolicAst.ml` defines `LoopContinue`, `LoopBreak`, and the `loop` record containing ordered inputs, break outputs, loop body, next expression, context, and source span: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/symbolic/SymbolicAst.ml>.
- **source** — `PureMicroPassesLoops.ml` lowers continue/break nodes, recognizes structural recursive loops, extracts auxiliary loop definitions, and converts remaining loops to the generic fixed-point operator: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/pure/PureMicroPassesLoops.ml>.
- **source** — `PureMicroPasses.ml` records the loop-specific pass order: output decomposition and simplification, recursive-shape recognition, loop decomposition, loop-body decomposition, and conversion of remaining loops to fixed points: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/pure/PureMicroPasses.ml>.
- **source** — `Config.ml` sets the loop fixed-point search bound to 2 and defaults both `loops_to_recursive_functions` and `no_recursive_loops` to false: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/Config.ml>.
- **source** — `Main.ml` exposes `-loops-to-rec` and `-loops-no-rec`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/Main.ml>.
- **source** — the pinned Rust loop corpus includes scalar loops, borrow-heavy loops, structural list traversals, explicit `break`, and nested loops: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/tests/src/loops.rs>.
- **source** — the checked-in Lean translation shows the corresponding `@[rust_loop]` and `@[rust_loop_body]` declarations, generic-loop examples, structurally recursive `partial_fixpoint` helpers, and explicit `ControlFlow.cont`/`done`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/tests/lean/Loops.lean>.
- **source** — Aeneas's Lean primitives define `ControlFlow`, the generic `loop`, and its `partial_fixpoint` semantics: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/Aeneas/Std/Primitives.lean>.
- **source** — Aeneas's WP library defines `loop.spec` and `loop.spec_decr_nat`, which require an invariant and a well-founded decreasing measure for continue steps: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/Aeneas/Std/WP.lean>.

## Revalidation

For another Aeneas revision, first inspect `src/interp/InterpLoops*.ml`, `src/pure/PureMicroPassesLoops.ml`, `src/Config.ml`, and the Lean definition of `Aeneas.Std.loop`. The cheapest concrete discriminator is then to translate two tiny Rust functions: one scalar counter loop and one traversal that advances through the tail of a recursive list. Compare whether the first still becomes `loop` plus `ControlFlow` and whether the second still becomes a recursive helper.

If exact generated shape matters for Anneal, regenerate the pinned `tests/src/loops.rs` corpus with that revision and compare `tests/lean/Loops.lean`, including helper signatures, `@[rust_loop]`/`@[rust_loop_body]`, use of `partial_fixpoint`, and source spans. To test the proof interface, compile a minimal theorem using `loop.spec_decr_nat` for the scalar loop and verify that the proof requires both invariant preservation and strict decrease on every `cont` branch.
