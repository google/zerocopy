# A concrete source-reconstructed trace: `loops::list_nth_mut`

*Authored by an AI agent acting on joshlf's behalf.*

This supplement answers A05.1 by following one particular function through the existing pipeline. The endpoints are retained files at Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`: [`tests/src/loops.rs`, lines 80–107][rust] and [`tests/lean/Loops.lean`, lines 216–268][lean]. The latter's source comments explicitly name the former and its line spans. This is **source evidence plus a reconstructed intermediate trace**, not an executed trace or a claim that these bytes were regenerated in this investigation. No `.llbc` file was found in the bounded tracked `tests` tree listing; therefore no exact serialized local IDs, LLBC statement IDs, extraction invocation, or transient interpreter snapshots are asserted. Aeneas's [`charon-pin`][pin] identifies compatible Charon `1aebab5f03a58067e5dc0ede2fec584117f54964`; reproducing the endpoints would additionally require the original extraction flags, target, and build inputs.

## The concrete endpoints

The Rust input defines `List<T> = Cons(T, Box<List<T>>) | Nil`, then:

```rust
pub fn list_nth_mut<T>(mut ls: &mut List<T>, mut i: u32) -> &mut T {
    while let List::Cons(x, tl) = ls {
        if i == 0 { return x; }
        else { ls = tl; i -= 1; }
    }
    panic!()
}
```

The retained Lean endpoint is a value/continuation pair rather than a heap reference:

```lean
def list_nth_mut_loop
  {T : Type _} (ls : List T) (i : Std.U32) : Result (T × (T → List T)) := do
  match ls with
  | List.Cons x tl =>
    if i = 0#u32
    then ok (x, fun t => List.Cons t tl)
    else
      let i1 ← i - 1#u32
      let (t, back) ← list_nth_mut_loop tl i1
      let back1 := fun t1 => let l := back t1
                             List.Cons x l
      ok (t, back1)
  | List.Nil => fail panic
partial_fixpoint

@[reducible]
def list_nth_mut
  {T : Type _} (ls : List T) (i : Std.U32) : Result (T × (T → List T)) := do
  list_nth_mut_loop ls i
```

These are narrow excerpts from the two inspected files. The Lean `List` declaration at lines 219–222 has no `Box`; its tail is another `List T`. For a schematic two-cell list `Cons a (Cons b Nil)` and index one, unfolding the retained equations on successful arithmetic gives selected value `b` and a backward function equivalent to `fun z => Cons a (Cons z Nil)`. This is a derived equation, not an observed evaluation. The function restores the whole list after the returned mutable view is changed; it is not merely a second copy of the selected element.

## The controlling path, tied to this function

| Stage | Concrete content followed | Exact controlling implementation |
| --- | --- | --- |
| Decode and select | The declaration for `loops::list_nth_mut` has a structured body, generic `T`, mutable-list input, `u32` index, and mutable-element output. The structured-body classification is required for this reconstructed interpreter path; its serialized record was not acquired. | `Translate.translate_function_to_symbolics`, `StructuredBody` branch, lines 22–36; ordinary load/preset guard is `Main`, lines 583–602. |
| LLBC preprocessing | The source's early `return x` occurs inside a loop, with a panic path after the while-loop. Current loop preprocessing moves returns out of loops using break transformations. | `PrePasses.update_loops`, lines 490–680. It replaces in-loop returns with breaks; with existing breaks, it can move the post-loop panic into break paths. Exact choice depends on the unretained structured LLBC. |
| Initialize ownership | `ls` begins as a fresh symbolic mutable-list value, `i` as a fresh symbolic scalar; non-input locals/return place begin at bottom. Input region abstractions retain loan projections and are initially non-endable. | `Interp.initialize_symbolic_context_for_fun`, lines 286–378. |
| Expand and branch | Inspecting `ls` requires revealing the reference and then `Cons`/`Nil`; the `Cons` fields introduce a head and tail, and `i == 0` divides the execution. `Nil` reaches panic. | `InterpExpansion.expand_symbolic_value_borrow`, `expand_symbolic_adt`, `expand_symbolic_bool`; the synthesis counterparts are `SymbolicToPureExpressions.translate_expansion` and `translate_expr`. |
| Find loop interface | The continue path carries the mutable tail plus decremented index while retaining enough information to reconstruct the outer list. The ownership summary has an abstraction connecting the original list loan to the current tail borrow. | `InterpLoopsFixedPoint.compute_loop_entry_fixed_point`, lines 44–237; `InterpJoin.join_ctxs`/`match_ctx_with_target`. The current `InterpJoin.mli`, lines 174–295, explicitly illustrates `list_nth_mut` and the old-list/current-tail connection. |
| Generate backward result | Returning the head creates a forward value and a continuation that rebuilds the list from a future replacement head. Ending relevant abstractions accounts for the accumulated outer list cells. | `Interp.evaluate_function_symbolic_synthesize_backward_from_return`; `InterpBorrows.end_abs_aux`; `SymbolicToPureAbs.abs_cont_to_texpr_aux`. |
| Build pure loop | Input symbols become pure variables, loop identifiers are renumbered, and symbolic loop inputs/output abstractions become pure values and continuation inputs/outputs. | `Translate.translate_function_to_pure_aux`, lines 166–268; `SymbolicToPureExpressions.translate_loop`, starting line 1850. |
| Simplify and restructure | `Box` and reference wrappers disappear from value types; tuple/continuation and loop relation passes retain the list reconstruction while permitting recursive loop extraction. | `SymbolicToPureTypes`, `translate_fwd_ty` family (`TBox` and `TRef` cases); `PureMicroPasses.passes`, lines 13–155; `PureMicroPassesLoops.loop_satisfies_recursive_criteria_aux`, lines 2475–2581. |
| Emit the retained shape | The emitted auxiliary takes the whole list and index, returns selected value plus backward function, recurses on the tail, and reconstructs `Cons` on return. The wrapper simply calls it. | `PureMicroPassesLoops.decompose_loops`; `Extract.extract_fun_decl_gen`, lines 2082 onward; `ExtractBase.fun_decl_kind_to_post_qualif` supplies `partial_fixpoint` for recursive declaration kinds. Retained concrete output is `Loops.lean`, lines 243–268. |

Each implementation region is pinned in [supplement-source-reading.json](supplement-source-reading.json); the table does not claim to have observed every runtime transition. In particular, it does not infer that a particular internal fresh ID or exact pass delta occurred just because the output resembles that pass's intended result.

## The ownership transition reconstructed for the tail case

Using schematic names, before examining a node there is an input abstraction holding the original-list loan and a live borrow containing the current list. After exposing `Cons`, the head and tail can be borrowed separately. In the nonzero branch, the local `ls` becomes the tail borrow; the outer list structure cannot simply vanish, because the backward result must later rebuild the original list.

The source's concrete `list_nth_mut` matching example in [`InterpJoin.mli`, lines 174–295][join] describes exactly this relationship: the fixed-point state has the current list under a fresh borrow plus a fresh abstraction connecting that borrow to the original loan; a reentry state contains dummy values for `Cons`, boxed tail, and head. Matching introduces an identity abstraction linking the current tail to the fixed-point interface, rather than equating unrelated borrow identifiers. This source example is documentation of the algorithm, not a log of this endpoint's generation.

The retained Lean `else` branch makes the reconstruction computationally visible: after the recursive call returns `(t, back)`, `back1` first applies the tail continuation and then wraps the result in `List.Cons x`. In the index-zero branch, it returns the existing head and the one-cell reconstruction `fun t => Cons t tl`. This is the representative trace's important cross-phase invariant: the forward result tracks the selected element; the backward continuation tracks the path from that element back to the original list root. Treating intermediate dummy values or continuations as dead merely because `ls` was reassigned would lose that invariant.

## Why the observed output is compatible with these phases, and what remains unproved

The retained definition exhibits several effects of the inspected pipeline simultaneously: `Box` elimination, mutable-reference purification, checked scalar subtraction in a monadic bind, panic on `Nil`, an auxiliary loop function, composed backward lambdas, and a reducible wrapper. This is more discriminating than a generic phase diagram. It also exposes why pure cleanup must preserve effect ordering: the recursive call and subtraction occur in the monad, while the final list-rebuilding lambda is pure.

The current loop-to-recursive criteria require identity input continuations, compatible uses of input continuations, and a structural-decrease relation. Traversal into a tail is compatible with that recognition, and the retained recursive auxiliary is consistent with it. Without the intermediate pure IR and invocation flags, this remains a source-supported reconstruction, not proof that one particular optimization branch was taken during the historical generation of this file. Neither the emitted `partial_fixpoint` nor the structurally smaller tail proves source termination: out-of-range input reaches panic, and target semantics include partial computations.

The cheapest future discriminating revalidation is to preserve the exact Rust build/target, compatible Charon invocation and `.llbc`, Aeneas flags, symbolic trace, pre/post pure AST, and newly generated `Loops.lean` fragment. Compare the forward/backward type, both successful branches, the nil panic, and the recursive reconstruction. No such regeneration or execution was performed in this investigation.

[rust]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/tests/src/loops.rs#L80-L107
[lean]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/tests/lean/Loops.lean#L216-L268
[pin]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/charon-pin
[join]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpJoin.mli#L174-L295
