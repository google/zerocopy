# Tree Borrows -- Read-read reorderings

Example 18 focuses on the reordering of adjacent reads.
We claim that Tree Borrows allows reordering of any two adjacent read accesses.
The correctness of this optimization is trivial w.r.t. the state of the heap,
but not so much w.r.t. the state of the trees of borrows.
In fact this optimization is incorrect in Stacked Borrows!

Our general framework is not at the moment capable of proving these optimizations because
they require one of
- absence of concurrency, or
- ability to reason about data races.
The latter has been demonstrated to be *possible* in simuliris (see `theories/simulang`),
but combining this with Tree Borrows is outside of our current scope.
Instead we opt for the former: this subdirectory only considers the sequential semantics,
no concurrency.

The main theorem for this proof is `read_reorder` in `read_reorder.v`,
which states that the two example programs given that differ in the ordering
of two reads are equivalent according to the notion defined in `equivalence_def.v`.
In addition, the intermediate lemmas in `low_level.v` should give confidence
that this reordering is indeed a more general property of the model and not
merely applicable to only this simple example.

## Files

In addition to the regular definitions of TB that are in the parent directory,
this proof is subdivided into
 * `equivalence_def.v`: definition of a simple notion of program equivalence for a sequential setting.
 * `low_level.v`: lemmas against the operational semantics.
 * `read_reorder.v`: actual proof of equivalence between two programs in which adjacent reads have been swapped. (Example 18)

