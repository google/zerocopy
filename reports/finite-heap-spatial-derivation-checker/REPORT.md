# A finite partial-heap certificate checker and matched frame judgments

## Summary

The retained Lean prototype checks a data-only grammar for disjoint splitting, a named two-cell predicate, framed updates and sequential links. Its soundness results connect accepted derivations to heap execution and to preservation of every address outside the selected write location. The same concrete frame statement is also proved directly.

This is a genuine partial-heap separation algebra, not an agreement check on arbitrary authority labels. Overlapping ownership is invalid even when stored values agree. The observed kernel results are conditional on Lean 4.31's implementation; that exact version contains the known omitted nested-parameter validation path described in [the kernel comparison](../independent-kernels-and-model-checking-certificates/REPORT.md).

## Applicability

The mathematical model is `Fin n → Option Nat`: a finite address space with absent or owned natural-valued cells. It represents exclusive, disjoint ownership. It does not model fractions, Rust allocations/provenance/lifetimes, bytes, deallocation, concurrency or Iris step-indexing.

The source `support/Heap.lean` is the full original definition/proof artifact. The portable JSON loader admits exactly three addresses, bounded natural literals and depth at most 16. Its independent fixed challenge is `[7,11,99] → [7,12,99]` with all writes restricted to address 1 and every other address preserved. The parser/renderer is an explicitly trusted narrow frontend; the logical checker accepts data constructors, not arbitrary producer Lean code.

## Findings

### The algebra has partial composition and cancellation

Basis: **source**, **execution** of conditional kernel checking.

`Disjoint h k` requires at least one absent cell at every address. `Join h k total` requires disjointness and exact left-biased union. `join_empty`, `join_comm`, `join_assoc` and `join_cancel` prove identity, commutativity, associative regrouping and cancellation. Because disjointness is a premise, left bias never licenses two owners of the same cell.

Assertions are predicates on partial heaps. `sep P Q h` existentially splits `h` into disjoint witnesses satisfying `P` and `Q`. `sep_comm`, `frame_entail` and `split_assertion` justify the corresponding ownership judgments. They are semantic rules for this algebra, not uninterpreted metadata.

### Data rules are checked against separate semantic predicates

Basis: **source**.

The grammar is:

| Constructor | Data | Checked meaning |
| --- | --- | --- |
| split | left, right, total vectors | `Join left right total` |
| pair | two addresses, two values, total | disjoint singleton join; exact named predicate unfolding |
| update | before, after, owned, frame, address, old, new | entry split, owned old value, exact write result |
| seq | two certificates | both valid and exact intermediate endpoint equality |

Vectors and addresses are data. `check_sound` proves that Boolean success implies `Valid`. `certificate_sound` gives the separately defined `Reach` relation of writes and composition. `step_sound` proves both updated ownership/frame composition and preservation outside the write address. `certificate_frame` adds `writesOnly a` to prove preservation outside `a` over the whole linked derivation; final endpoint equality alone is not used to hide intermediate writes elsewhere.

`pairPredicate` is defined by separation of two singleton assertions, and `unfold_pair` proves its meaning. This prototype supports that exact named predicate, not arbitrary user-defined inductive predicates or a general unfolding oracle.

### One update can be expressed in four logic styles

Basis: **derived** matched example, **source**.

For the same update of address 1 from 11 to 12, keeping 0=7 and 2=99:

| Style | Obligation on this example | What it contributes |
| --- | --- | --- |
| Dynamic frame | explicit modifies set `{1}` and equality outside it | states the protected footprint; separately justify write authority |
| Implicit dynamic frame | permission to address 1 and its entry value; unmodified permissions frame the other cells | joins access authority with heap-dependent value facts |
| First-order separation | `1↦11 * (0↦7 * 2↦99)` to `1↦12 * (0↦7 * 2↦99)` | disjoint footprint composition and local update |
| Higher-order separation | quantify arbitrary assertion `R` in `{1↦11 * R} write {1↦12 * R}` | abstracts the client's frame instead of enumerating it |

`higher_order_frame` proves the last rule for every heap predicate `R`, while the checker instantiates a concrete finite frame. These are matched semantic obligations, not executions of four existing tools. Dynamic frames alone do not grant ownership, and the presence of higher-order quantification is not evidence of a richer operational model.

[Parkinson and Summers, LMCS 2012](https://lmcs.episciences.org/802/pdf), Theorem 3.20, relates partial heaps to total heaps restricted by permission masks; Theorem 5.6/Corollary 5.7 relate a restricted SL syntax to Chalice verification conditions. The side conditions and restricted syntax matter. Our Boolean exclusive-cell adapter is a smaller constructed example, not a mechanization of that entire paper or a general equivalence of program logics.

### Actual controls distinguish ownership and original-subject binding

Basis: **execution**.

`check_fixtures.py` retained ten JSON fixtures. Eight render to fixed constructor-only Lean inputs and complete with the expected Boolean theorem; two are rejected by the loader (unknown constructor and address 3 outside `Fin 3`). The two accepted cases are the update and split-then-update chain. Negative logical cases cover overlap, changed frame, wrong old value, missing owned cell, unlinked intermediate state and a valid update over a different original frame.

The script binds candidate input/output to the fixed consumer vectors and requires `writesOnly 1`. It proves the consumer's frame statement for each accepted fixture. Unknown keys/constructors are not converted into proof declarations. Source generation is limited to literals and known constructors, but its correctness is still outside the logical proof.

`Heap.lean` additionally checks same-value duplicate ownership, aliased pair unfolding and broken sequence links. Printed dependencies of the main algebra, soundness, frame and direct/certificate examples are `propext` and `Quot.sound`, with no `sorryAx` in successful retained runs. This axiom observation does not remove the known kernel implementation frontier.

### The matched costs are small observations with wide variance

Basis: **execution**.

`measure.py` repeats the identical concrete theorem 100 times in each fresh process, using either `step_sound good (by decide)` or a direct conjunction proof by decision. Five warm-filesystem samples per route include startup, imported precompiled model, elaboration and kernel work. Median times were approximately 1401 ms for the data route and 1678 ms for the direct route; ranges overlap substantially (810–2470 ms and 944–2007 ms). Sources are 16,540 and 16,340 bytes. This does not establish a performance ranking, realistic proof-generation cost or end-to-end source-verification cost.

For Anneal, a small resource derivation format is feasible when every constructor has a fixed interpretation and frame/entry/endpoint side conditions. Direct host proofs remain useful for richer higher-order rules. Integrating Gillian-Rust would require its actual symbolic/execution/entailment operations to produce evidence interpreted by such a sound judgment; no Gillian replay implementation is claimed here.

### Separate parent replay under Lean4.34.1

Basis: execution. The same logical Heap.lean and ten fixture data files were independently replayed in a fresh parent copy under Lean4.34.1@5045d0056413266e57c625dcd7c365b10e377c52: eight kernel observations and two loader rejections matched. Accepted endpoints print propext/Quot.sound and no sorryAx. `support/parent-lean434` preserves this separate observation. The replay helper now requires caller-selected LEAN_BINARY; its private fallback was removed without changing grammar/theorems. This neither rewrites the historical4.31 measurement nor proves the newer kernel universally sound. No4.34 timing comparison is claimed.

## Boundaries

**Not examined:** fractional permissions, arbitrary predicate unfolding, proof DAG compression, magic wand, weak memory, Rust source import or a complete Gillian entailment language. **Known not established:** adversarial acceptance assurance under the old Lean kernel pin. The finite algebra and checker investigation is answered; deploying it as a Rust resource checker is future engineering with a separately named semantic interpretation.

## Evidence

support/Heap.lean, JSON fixtures, generated constructor-only Lean files, stdout/stderr, fixture-results.json, matched-costs.json and reproduction scripts retain the exact definitions, observations and domains. The paper is primary semantic comparison evidence, not a source implementation dependency.

## Revalidation

Run `python3 -B check_fixtures.py` in support with the exact toolchain available, then optionally `python3 -B measure.py`. Inspect stdout assumptions and every expected rejection. For another checker version, record a separate observation and its implementation boundary; do not infer continuity from the same theorem text.

*Authored by an AI agent acting on joshlf's behalf.*
