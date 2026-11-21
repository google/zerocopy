# Tricolor marking invariants and write-barrier soundness in a toy Lean model

## Summary

This package is a self-contained, Mathlib-free Lean 4 development of a **toy model** of
incremental tracing (tricolor mark) garbage collection. A state is a finite heap of objects
`Fin n` with a Boolean pointer graph, a root set and an object color (white, grey, black). The
collector step `scan` blackens a grey object and greys its white successors; the mutator steps
are `store`, `erase`, `load`, `drop` and `alloc`. A configuration chooses a heap write barrier
(none, the Dijkstra insertion barrier, or the Yuasa deletion barrier), whether root loads are
shaded (a load barrier), and which allocation colors are allowed. The executions are those of
the generated relations `Step cfg` (one enabled step), `Run cfg` (a finite sequence of enabled
steps) and `InfRun cfg` (an infinite sequence of enabled steps), whose enabling conditions
(`Op.Enabled`) are quoted under **Findings → Definitions**.

The package contains 20 kernel-checked results: 15 theorems, 1 characterization (an `↔`) and 4
counterexample results (three concrete instances and one instance quantified over
configurations). Every hypothesis of every result is marked `tight` and has a named,
kernel-checked counterexample in which all other hypotheses hold and the conclusion fails; the
ledgers record the class of each counterexample (for example "a 2-object heap state"), and
tightness means no more than that the hypothesis cannot be dropped within that class. Every
theorem and the characterization has a kernel-checked non-vacuity witness (an instance satisfying
all its hypotheses), and every counterexample result has a positive control. The summary sentences below are the
plain-language claims recorded in `results.json`, verbatim. Every result also has **non-claims**,
listed first under **Boundaries**; read them before relying on a result.

These are statements about the toy model; they neither establish nor refute the corresponding
claims about the Go, V8, OCaml or JVM collectors, or about any other production collector. Every
claim connecting a result to a real system is a separate `derived (modeling bridge)` statement,
never a theorem.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Distinctions a design should retain. Each bullet restates results below with all of their
hypotheses, stated before their conclusions; "cannot be dropped" means that the named,
kernel-checked counterexample, of the stated class, satisfies all other hypotheses of the
theorem and violates its conclusion. All executions are those of the generated relations
`Step cfg`, `Run cfg` and `InfRun cfg` over the step alphabet `Op` of a single marking phase
(collector `scan`; mutator `store`, `erase`, `load`, `drop` and `alloc`; no `initMark`, `rescan`
or sweep step). A step `op` is enabled in a state `s` (`op.Enabled cfg s`) under these
conditions: `scan g` requires `g` to be grey; a heap store `store x y` requires the stored
pointer to be held in the roots (`s.root y = true`); a root load `load y` requires `y` to be
reachable from the roots (`Live s y`); an allocation `alloc a c` requires an allowed color
(`cfg.allocOk c = true`) and an isolated non-root object (`s.root a = false` and
`Isolated s a`); `erase` and `drop` are always enabled.

- **End of marking.** For every state with no grey object: if the strong invariant holds and
  every root is non-white, then every object reachable from the roots is black
  (`no-grey-strong-nonwhite-roots-implies-live-black`); if the weak invariant holds and every
  white root is grey protected, then every object reachable from the roots is black
  (`no-grey-weak-roots-protected-implies-live-black`). For each hypothesis of either theorem, a
  1- or 2-object heap state satisfies the other two hypotheses and has a reachable non-black
  object; in particular, the 1-object state with one white root has no grey object, satisfies
  the strong invariant and the weak invariant, and has a reachable non-black object
  (`noGrey_strong_and_not_allLiveBlack`, `noGrey_weak_and_not_allLiveBlack`), so neither
  invariant constrains the roots by itself.
- **Strong versus weak.** For every state, if the strong invariant holds then the weak
  invariant holds (`strong-implies-weak`); the 3-object state `sWeakNotStrong` satisfies the
  weak invariant and not the strong invariant (`weak_and_not_strong`).
- **One step under the Dijkstra barrier.** For every configuration whose heap barrier is the
  Dijkstra barrier (any load shading, any allowed allocation colors), every state `s` satisfying
  the strong invariant, and every `s'` with `Step cfg s s'` (one enabled step; in particular an
  allocation takes an isolated non-root object in an allowed color), the strong invariant holds
  in `s'` (`dijkstra-barrier-preserves-strong`). The isolation condition on allocations cannot
  be dropped (`dijkstra_unisolated_alloc_breaks_strong`,
  `dijkstra_unisolated_blackAlloc_breaks_strong`: a 3-object heap state and one allocation of a
  non-isolated object, white or black).
- **One step under the Yuasa barrier.** For every configuration whose heap barrier is the Yuasa
  barrier and whose allowed allocation colors exclude white (either load shading), every state
  `s` satisfying the weak invariant and its root clause `RootsProtected`, and every `s'` with
  `Step cfg s s'` (one enabled step; in particular a heap store writes a pointer held in the
  roots, a root load takes an object reachable from the roots, and an allocation takes an
  isolated non-root object), the weak invariant and `RootsProtected` hold in `s'`
  (`yuasa-nonwhite-alloc-preserves-weak-and-roots-protected`). `RootsProtected` cannot be
  dropped from that theorem (`yuasa_store_without_rootsProtected_breaks_weak`: a 2-object heap
  state and one enabled store), nor can the allocation hypothesis
  (`alloc_white_yuasa_breaks_rootsProtected`: a 2-object heap state and one enabled white
  allocation), nor can the enabling conditions on stores, loads and allocations
  (`yuasa_store_of_unreachable_breaks_weak`, `load_of_unreachable_breaks_rootsProtected`,
  `yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak`: 2- and 3-object heap states and one step
  that violates one of these conditions). In the 3-object state `sChainR`, which satisfies the
  strong invariant and `RootsProtected`, one enabled store under the Yuasa barrier yields a
  state in which the strong invariant fails while the weak invariant and `RootsProtected` hold
  (`yuasa-barrier-breaks-strong`).
- **Load barrier instead of a heap barrier.** For every configuration with shaded root loads
  and allowed allocation colors excluding white, under every heap barrier (none, Dijkstra or
  Yuasa), every state `s` satisfying the strong invariant in which every root is non-white, and
  every `s'` with `Step cfg s s'` (one enabled step; in particular a heap store writes a pointer
  held in the roots and an allocation takes an isolated non-root object), the strong invariant
  holds in `s'` and every root of `s'` is non-white
  (`shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots`). Neither of these two
  enabling conditions can be dropped
  (`shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong`,
  `shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong`: a 3-object heap state and one step
  that violates one of them, with no heap barrier).
- **Allocation color.** For every state in which every white root is grey protected, every
  isolated object `a` and every color `c`: allocating `a` into the roots with color `c` keeps
  every white root grey protected if and only if `c` is not white
  (`isolated-alloc-preserves-roots-protected-iff-nonwhite`).
- **Whole marking cycles from a root snapshot.** `initMark s₀` greys every root and whitens every
  other object in one atomic step. For every configuration whose heap barrier is the Yuasa
  barrier and whose allowed allocation colors exclude white (either load shading), every initial
  state `s₀`, and every state `s` reached from `initMark s₀` by a run of `Run cfg` (enabled steps
  only), if `s` has no grey object then every object reachable from the roots in `s` is black
  (`yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`). For every
  configuration with shaded root loads and allowed allocation colors excluding white, under
  every heap barrier including none, every `s₀`, and every state `s` reached from `initMark s₀`
  by a run of `Run cfg`, if `s` has no grey object then every object reachable from the roots in
  `s` is black (`shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`). For
  every configuration whose heap barrier is the Dijkstra barrier (any load shading, any allowed
  allocation colors), every `s₀`, every state `s` reached from `initMark s₀` by a run of
  `Run cfg`, and every state `s'` reached from `rescan s` (every white root greyed) by a run of
  `Run cfg` consisting of collector scans (`ScansOnly`), if `s'` has no grey object then every
  object reachable from the roots in `s'` is black
  (`dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`). The enabling conditions of the
  steps inside `Run cfg` carry weight: for each theorem, a 2- or 4-step sequence from a 2- or
  3-object root snapshot in which exactly one step violates exactly one enabling condition
  (isolation of an allocation, for all three theorems; reachability of a stored or loaded
  object, for the Yuasa theorem; a held pointer in a store, for the load-barrier theorem) ends,
  for the Dijkstra theorem after a rescan and an empty drain, in a state with no grey object in
  which not every reachable object is black (the counterexamples in the `hrun` rows of the three
  ledgers).
- **What fails without a rescan.** For the configuration `cfgDW` (Dijkstra barrier, shaded root
  loads, every allocation color allowed), the enabled 2-step run 'allocate 1 white into the
  roots; scan 0' from the root snapshot of a 2-object heap ends with no grey object and the
  reachable root `1` white (`dijkstra-white-alloc-without-rescan-leaves-live-white`). For the
  configuration `cfgD0` (Dijkstra barrier, black-only allocation, unshaded root loads), an
  enabled 4-step run from the root snapshot of a 3-object heap ends with no grey object and the
  reachable root `2` white (`dijkstra-unshaded-loads-without-rescan-leaves-live-white`). These
  counterexamples show that neither the shaded-loads hypothesis nor the non-white-allocation
  hypothesis can be dropped from
  `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black` (within the
  classes recorded in its ledger: a 2-object heap with a 2-step run, and a 3-object heap with a
  4- or 6-step run); they do not show that every collector without a rescan must shade loads
  and avoid white allocation.
- **Neither barrier.** For every configuration with no heap barrier and unshaded root loads (any
  allowed allocation colors), the enabled 6-step interleaving `traceLostObject` from the root
  snapshot of the 3-object heap `0 → 1 → 2` (root `0`) ends with no grey object and the
  reachable object `2` white (`no-barrier-unshaded-loads-leaves-live-white`). The same trace
  does not end in that way under the configurations `cfgD0` (Dijkstra barrier), `cfgY` (Yuasa
  barrier) and `cfgU` (no heap barrier, shaded loads)
  (`traceLostObject_dijkstra_unshadedLoads_not_lost`,
  `traceLostObject_yuasa_unshadedLoads_not_lost`,
  `traceLostObject_unbarriered_shadeLoads_not_lost`).
- **Termination.** For every configuration, every state `s` and every run of `Run cfg` from `s`
  that consists of collector scans (`ScansOnly`; each scan is enabled, so it takes a grey
  object), the number of steps is at most `markMeasure s` and at most `2·n`, where
  `markMeasure s = 2·#white + #grey` (`scans-only-run-length-at-most-mark-measure`). For every
  configuration and every state `s`, some run of `Run cfg` from `s` that consists of enabled
  collector scans (`ScansOnly`) reaches a state with no grey object
  (`scans-only-run-to-no-grey-exists`). For every configuration and every run of `Run cfg` from
  `s` to `s'` (enabled steps only, so every scanned object is grey), the number of scans in the
  run plus `markMeasure s'` is at most `markMeasure s` plus the sum, over the run's allocation
  steps counted with multiplicity, of the weights of their colors (white 2, grey 1, black 0)
  (`scans-plus-measure-at-most-initial-plus-alloc-weight`). For every configuration and every
  infinite execution of `InfRun cfg` (every step enabled, so every scanned object is grey; the
  single-marking-phase alphabet `Op`, with no `initMark`, `rescan` or sweep step) in which the
  collector is weakly fair (`CollectorFair`) and either from some point on every allocation is
  black (`EventuallyOnlyBlackAllocs`;
  `fair-collector-eventually-black-allocs-eventually-always-no-grey`) or every allocation takes a
  cell that is white in the state where it happens (`WhiteTargetAllocs`;
  `fair-collector-white-target-allocs-eventually-always-no-grey`), from some point on no object
  is grey and no scan occurs. Fairness cannot be dropped (`starvedCollector_never_noGrey`: an
  infinite execution over a 1-object heap), nor can the allocation hypothesis
  (`greyAllocCycle_collectorFair_never_noGrey`: a periodic infinite execution over a 2-object
  heap that re-colors marked cells grey), nor can the enabledness of scans
  (`unenabledScans_collectorFair_never_noGrey`: an infinite execution over a 2-object heap that
  satisfies the state equations but scans a black object forever). In every infinite execution
  of `InfRun cfg` that satisfies all hypotheses of either termination theorem, the antecedent of
  `CollectorFair` is false from every point on
  (`collectorFair_antecedent_false_of_eventuallyOnlyBlackAllocs`,
  `collectorFair_antecedent_false_of_whiteTargetAllocs`).

Results (plain-language claims, verbatim from `results.json`):

*End of marking.*

- **`no-grey-strong-nonwhite-roots-implies-live-black`** (`allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite`; theorem, T0): In a state with no grey object in which the strong invariant holds (no black-to-white edge) and every root is non-white, every object reachable from the roots is black.
- **`weak-and-roots-protected-imply-live-white-grey-protected`** (`greyProtected_of_live_of_white_of_weak_of_rootsProtected`; theorem, T0): If the weak invariant holds and every white root is grey protected, then every white object reachable from the roots is grey protected (reachable from a grey object through white objects only).
- **`no-grey-weak-roots-protected-implies-live-black`** (`allLiveBlack_of_noGrey_of_weak_of_rootsProtected`; theorem, T0): In a state with no grey object in which the weak invariant holds and every white root is grey protected, every object reachable from the roots is black.
- **`strong-implies-weak`** (`weak_of_strong`; theorem, T0): The strong invariant implies the weak invariant.

*One step under barriers and allocation.*

- **`dijkstra-barrier-preserves-strong`** (`strong_preserved_of_dijkstra`; theorem, T0): For every configuration whose heap barrier is the Dijkstra insertion barrier (shade the target of every heap store), with any root-load discipline and allocation colors, every state s satisfying the strong invariant, and every successor s' of s under the generated step relation `Step cfg` (an enabled collector scan of a grey object, heap store of a pointer held in the roots, erase, root load of an object reachable from the roots, root drop, or allocation of an isolated non-root object, in any color the configuration allows), the strong invariant holds in s'.
- **`yuasa-nonwhite-alloc-preserves-weak-and-roots-protected`** (`weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc`; theorem, T0): For every configuration whose heap barrier is the Yuasa deletion barrier (shade the old target of every erased pointer) and whose allocator never allocates white, with root loads shaded or not, every state s satisfying the weak invariant and its root clause (every white root is grey protected), and every successor s' of s under the generated step relation `Step cfg` (an enabled collector scan of a grey object, heap store of a pointer held in the roots, erase, root load of an object reachable from the roots, root drop, or allocation of an isolated non-root object), the weak invariant and its root clause hold in s'.
- **`yuasa-barrier-breaks-strong`** (`store_yuasa_breaks_strong`; counterexample, T0): The Yuasa barrier does not preserve the strong invariant: in the 3-object state sChainR (black root 0, grey 1, white root 2, edges 0 -> 1 -> 2), which satisfies the strong invariant and the root clause, the enabled Yuasa store of the held pointer 2 into 0 creates a black-to-white edge while the weak invariant and its root clause still hold.
- **`isolated-alloc-preserves-roots-protected-iff-nonwhite`** (`rootsProtected_alloc_iff_ne_white`; characterization, T0): If every white root is grey protected and object a is isolated, then allocating a into the roots with color c keeps every white root grey protected if and only if c is not white.
- **`shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots`** (`strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc`; theorem, T0): For every configuration with shaded root loads (a load barrier) and an allocator that never allocates white, under any heap barrier including none, every state s satisfying the strong invariant in which every root is non-white, and every successor s' of s under the generated step relation `Step cfg` (an enabled collector scan of a grey object, heap store of a pointer held in the roots, erase, root load of an object reachable from the roots, root drop, or allocation of an isolated non-root object), the strong invariant holds in s' and every root of s' is non-white.

*Whole marking cycles.*

- **`yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`** (`allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark`; theorem, T0): For every configuration with the Yuasa barrier and an allocator that never allocates white, every initial state s₀, and every state s reached from initMark s₀ (every root shaded at once and every other object white: a stop-the-world root snapshot) by a run of the generated relation `Run cfg` (a finite sequence of enabled steps: collector scans of grey objects, heap stores of pointers held in the roots, erases, root loads of objects reachable from the roots, root drops, and allocations of isolated non-root objects), if s has no grey object then every object reachable from the roots in s is black, without a root rescan or shading of root loads.
- **`no-barrier-unshaded-loads-leaves-live-white`** (`unbarriered_unshadedLoads_traceLostObject_leaves_live_white`; counterexample, T0): On the heap 0 (root) -> 1 -> 2, starting from the root snapshot initMark (0 grey, 1 and 2 white), under every configuration with no heap barrier and unshaded root loads, the enabled interleaving 'scan 0; load 2 into the roots; store 2 into the black root 0; drop 2 from the roots; erase 1 -> 2; scan 1' reaches a state with no grey object in which object 2 is reachable (through the edge 0 -> 2) and white.
- **`dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`** (`allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run`; theorem, T0): For every configuration with the Dijkstra barrier (any allocation colors, either root-load discipline), every initial state s₀, every state s reached from initMark s₀ by a run of the generated relation `Run cfg` (a finite sequence of enabled steps: collector scans of grey objects, heap stores of pointers held in the roots, erases, root loads of objects reachable from the roots, root drops, and allocations of isolated non-root objects), and every state s' reached from rescan s (every white root greyed) by a run of `Run cfg` consisting only of collector scans (`ScansOnly`: the mutator is paused), if s' has no grey object then every object reachable from the roots in s' is black.
- **`dijkstra-white-alloc-without-rescan-leaves-live-white`** (`dijkstra_whiteAlloc_run_from_initMark_leaves_live_white`; counterexample, T0): On the heap with root 0 and an isolated free object 1, starting from the root snapshot initMark (0 grey, 1 white), under the Dijkstra barrier with shaded root loads and white allocation allowed, the run 'allocate 1 white into the roots; scan 0' reaches a state with no grey object in which the root 1 is white.
- **`dijkstra-unshaded-loads-without-rescan-leaves-live-white`** (`dijkstra_unshadedLoads_run_from_initMark_leaves_live_white`; counterexample, T0): On the heap 0 (root) -> 1 -> 2, starting from the root snapshot initMark, under the Dijkstra barrier with black-only allocation but unshaded root loads, the run 'scan 0; load 2 into the roots; erase 1 -> 2; scan 1' reaches a state with no grey object in which the root 2 is white.
- **`shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`** (`allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark`; theorem, T0): For every configuration with shaded root loads and an allocator that never allocates white, under any heap barrier including none, every initial state s₀, and every state s reached from initMark s₀ (a stop-the-world root snapshot) by a run of the generated relation `Run cfg` (a finite sequence of enabled steps: collector scans of grey objects, heap stores of pointers held in the roots, erases, root loads of objects reachable from the roots, root drops, and allocations of isolated non-root objects), if s has no grey object then every object reachable from the roots in s is black, without a root rescan.

*Termination.*

- **`scans-only-run-length-at-most-mark-measure`** (`length_le_markMeasure_and_le_two_mul_of_scansOnly_run`; theorem, T0): For every configuration and every run of the generated relation `Run cfg` from a state s (enabled steps only, so every scanned object is grey) that consists only of collector scans (`ScansOnly`), the number of steps is at most markMeasure s, where markMeasure s = 2 · (number of white objects of s) + (number of grey objects of s), and at most 2 · n.
- **`scans-only-run-to-no-grey-exists`** (`exists_scansOnly_run_to_noGrey`; theorem, T0): For every configuration and every state s, the generated relation `Run cfg` has a run from s that consists only of collector scans (`ScansOnly`; each scan is enabled, i.e. scans a grey object) and reaches a state with no grey object.
- **`scans-plus-measure-at-most-initial-plus-alloc-weight`** (`scanCount_add_markMeasure_le`; theorem, T1): For every configuration (heap barrier none, Dijkstra or Yuasa; any root-load discipline and allocation colors) and every run of the generated relation `Run cfg` from s to s' (enabled steps only, so every scanned object is grey), the number of scans in the run plus markMeasure s' is at most markMeasure s plus the sum, with multiplicity, of the weights of the run's allocation colors (white 2, grey 1, black 0).
- **`fair-collector-eventually-black-allocs-eventually-always-no-grey`** (`eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs`, `infinitely_often_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs`; theorem, T0): For every configuration and every infinite execution (ops, st) of the generated relation `InfRun cfg` (every step ops i is enabled in st i and st (i+1) is its result, so every scanned object is grey; the step alphabet is that of a single marking phase, with no initMark, rescan or sweep step) in which the collector is weakly fair (`CollectorFair`: if from some point on a grey object exists in every state, scans happen infinitely often) and from some point on every allocation is black (`EventuallyOnlyBlackAllocs`), there is a point after which no object is ever grey and no scan occurs (in particular, states with no grey object occur infinitely often).
- **`fair-collector-white-target-allocs-eventually-always-no-grey`** (`eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs`; theorem, T1): For every configuration and every infinite execution (ops, st) of the generated relation `InfRun cfg` (every step ops i is enabled in st i and st (i+1) is its result, so every scanned object is grey; the step alphabet is that of a single marking phase, with no initMark, rescan or sweep step) in which the collector is weakly fair (`CollectorFair`) and every allocation, of any color, takes a cell that is white in the state where it happens (`WhiteTargetAllocs`), there is a point after which no object is ever grey and no scan occurs.

Non-claims for every result are listed first under **Boundaries**.

## Applicability

### Model fidelity

This is a **toy model**, written to make the logical structure of tricolor marking and its
barrier disciplines precise; it is not a model of any particular collector. Its definitions are
quoted verbatim under **Findings → Definitions**. The modeling choices that matter most for
reading the results are:

- **Heap.** Objects are `Fin n`. The heap is a Boolean adjacency matrix `edge`: `edge x y = true`
  means some field of `x` points to `y`. Fields are not modeled, so two fields of `x` that point
  to the same object are one edge, and an overwrite `x.f := y` that replaces a pointer to `z` is
  an `erase x z` followed by a `store x y`.
- **Roots.** The Boolean root set `root` abstracts the mutator's registers and stack slots. There
  is one mutator and one root set. Root writes (`load`, `drop`, `alloc`) never run the heap write
  barrier; `load` runs the load barrier (shading the loaded object) when `shadeLoads = true`.
- **Atomicity.** Every step is atomic, and each barrier runs atomically with its write.
  `initMark` greys every root and whitens every other object in one step: a stop-the-world root
  snapshot after which the mutator is black. Thread stacks that stay grey and are scanned
  concurrently with the heap are not modeled. `rescan` greys every white root in one step.
- **Mutator discipline** (`Op.Enabled`). The collector scans only grey objects. A heap store
  writes a pointer that the mutator holds in its roots. A root load takes an object that is
  currently reachable from the roots (abstracting a chain of field loads). Erases and drops are
  always enabled. An allocation takes an isolated non-root object (no edge into or out of it,
  modeling a zeroed cell) and an allowed color. The object whose field is written (`x` in
  `store x y` and `erase x z`) is not constrained, which enlarges the step relation.
- **Allocation.** Allocating an object that is white in the current state models taking a free
  cell; allocating an object that is already grey or black in the current marking cycle
  re-colors it (no sweep runs in between). This re-coloring stands in for fresh cells beyond
  the `n` initial ones and is what lets allocation add marking work in the termination results.
- **Sweeping and cycles.** Sweeping is not modeled: the white objects that remain when marking
  ends are the ones a sweep would free. Executions (`Run`, `InfRun`) contain the steps of one
  marking phase; repeated mark-sweep cycles, color flips and heap growth are not modeled.
- **Termination measure.** `markMeasure s` is `2·#white + #grey`, written as a sum of color
  weights.

### What real systems the definitions are meant to capture, and known gaps

The definitions are meant to capture the logical core of three textbook disciplines: Dijkstra et
al.'s on-the-fly collector with its insertion barrier and the strong invariant P1 (`dijkstra`
barrier, `Strong`); the snapshot-at-the-beginning deletion barrier attributed to Yuasa, with the
weak tricolor invariant in the form attributed to Pirinen (`yuasa` barrier, `Weak`,
`RootsProtected`); and black-mutator load barriers (`shadeLoads`). The design document of
Clements and Hudson for the Go collector, which describes Go 1.7's coarsened Dijkstra barrier
with a stop-the-world stack re-scan and the hybrid barrier that replaced it, is used as prior art
and as the source of the modeling bridges; the hybrid barrier itself (deletion shading plus
insertion shading while stacks are grey) is not modeled.

Known gaps, each restated in the non-claims of the results it affects: multi-threaded mutators,
per-thread stacks and their concurrent scanning, weak memory, fine-grained interleaving of a
barrier with its write, copying or moving collectors, sweeping and later cycles, weak or soft
references, finalizers and untraced native handles, objects whose fields are initialized at
allocation time with pointers (allocation requires an isolated object), and heap growth or
allocation pacing.

Basis: derived (modeling bridge). Reasoning: the correspondence rests on comparing the
definitions quoted under **Findings** with the descriptions in the cited sources (P1, the
shading actions and the root definition of EWD 520; the barrier descriptions in the Go design
document; the section titles of the handbook); no production collector was executed or
inspected.

These are statements about the toy model; they neither establish nor refute the corresponding
claims about the Go, V8, OCaml or JVM collectors. No production collector's source code was
examined for this package.

### Relationship of the subjects

The Lean 4 toolchain release is the checker of every theorem in this package. The papers, the
handbook, the Archive of Formal Proofs entry and the Go design document listed as subjects are
prior art for the definitions and for the known results restated here (tiers `T0` and `T1`);
each card records what is attributed to which source, and **Evidence → Primary sources** records
what was read of each. None of them is a dependency of the Lean project.

### Lean version and project

- Lean `leanprover/lean4:v4.34.1` (pinned in `lean/lean-toolchain`); **no Mathlib**, no Lake
  dependencies (`lean/lakefile.toml` declares one library, `Toy`, and no `[[require]]`).
- All declarations live in the namespace `Toy.Tricolor`; **Findings** omits that prefix.
- Library modules (`lean/Toy/Tricolor/`): `Basic.lean` (states, colors, reachability,
  invariants, operations, barriers, configurations, the step relation and runs), `Examples.lean`
  (concrete states; positive and negative examples for the definitions of `Basic.lean`),
  `EndOfMarking.lean` (end-of-marking theorems and their counterexamples), `Preservation.lean`
  (one-step preservation by barriers and allocation), `Marking.lean` (whole marking cycles),
  `Counterexamples.lean` (interleavings, step-relation counterexamples, positive controls,
  non-vacuity witnesses), `Termination.lean` (the measure, run bounds, fairness-based
  termination and its counterexamples), `Tightness.lean` (further counterexamples) and
  `RunExamples.lean` (examples for `Step`, `Run`, `ScansOnly` and the termination definitions).
- `lean/RevalidationAudit.lean` (outside the library target) prints the axioms of every
  declaration that `results.json` references.

## Findings

### Notation

In prose, objects are the numbers of `Fin n`; `0 → 1` is the edge `edge 0 1 = true`; "the root snapshot" of a heap `h` is `initMark h`; "enabled" refers to `Op.Enabled`. Each result below gives: kind, tier and depth; the plain claim (prose) and the tier justification (prose); the Lean statement quoted verbatim, the first line of each Lean block being a `-- file:line` comment that cites the quoted source range (paths relative to the package directory); for most theorems an unfolded statement, which is a Lean term that elaborates in the theorem's context and is definitionally equal to it; the hypothesis ledger with the verbatim statements of all counterexamples; the non-vacuity witness or positive control, verbatim; prior art; the design question; and the basis lines.

### Definitions

Every definition of the library is quoted verbatim from the Lean source, doc comment included (the doc comment states what the definition is meant to capture); the first line of each block is a `-- file:line` comment citing the quoted source range (paths relative to the package directory). Proved positive and negative examples of the definitions of `Basic.lean` are in `lean/Toy/Tricolor/Examples.lean`; those of `Step`, `Run`, `ScansOnly` and the termination definitions are in `lean/Toy/Tricolor/RunExamples.lean`.

#### Colors, states and reachability

`Color`:

```lean
-- lean/Toy/Tricolor/Basic.lean:32-38
/-- Object colors in tricolor marking. White: not yet reached by the collector (freed if still
white when marking ends). Grey: reached, successors not yet scanned. Black: reached and scanned. -/
inductive Color where
  | white
  | grey
  | black
  deriving DecidableEq, Repr
```

`St`:

```lean
-- lean/Toy/Tricolor/Basic.lean:40-47
/-- A heap state over objects `Fin n`: pointer graph, root set and object colors. -/
structure St (n : Nat) where
  /-- `edge x y = true` iff some field of object `x` points to object `y`. -/
  edge : Fin n → Fin n → Bool
  /-- `root r = true` iff `r` is held by the mutator's roots (registers, stack slots). -/
  root : Fin n → Bool
  /-- The current color of each object. -/
  color : Fin n → Color
```

`Live`:

```lean
-- lean/Toy/Tricolor/Basic.lean:57-61
/-- `Live s y`: object `y` is reachable from the root set along heap edges (a root itself is
live). These are the objects a correct collector must not free. -/
inductive Live (s : St n) : Fin n → Prop where
  | root {r : Fin n} : s.root r = true → Live s r
  | step {x y : Fin n} : Live s x → s.edge x y = true → Live s y
```

#### Invariants and root conditions

`NoGrey`:

```lean
-- lean/Toy/Tricolor/Basic.lean:63-64
/-- `NoGrey s`: no grey object remains; this is the termination test of the mark phase. -/
def NoGrey (s : St n) : Prop := ∀ x, s.color x ≠ .grey
```

`Strong`:

```lean
-- lean/Toy/Tricolor/Basic.lean:66-68
/-- The strong tricolor invariant: no edge from a black object to a white object. -/
def Strong (s : St n) : Prop :=
  ∀ x y, s.edge x y = true → s.color x = .black → s.color y ≠ .white
```

`GreyProtected`:

```lean
-- lean/Toy/Tricolor/Basic.lean:70-76
/-- `GreyProtected s y`: `y` is white and is reachable from some grey object along a path of
length at least one all of whose objects after the grey start (including `y`) are white. -/
inductive GreyProtected (s : St n) : Fin n → Prop where
  | direct {g y : Fin n} :
      s.color g = .grey → s.edge g y = true → s.color y = .white → GreyProtected s y
  | chain {w y : Fin n} :
      GreyProtected s w → s.edge w y = true → s.color y = .white → GreyProtected s y
```

`Weak`:

```lean
-- lean/Toy/Tricolor/Basic.lean:78-81
/-- The weak tricolor invariant: every white object pointed to by a black object is grey
protected. -/
def Weak (s : St n) : Prop :=
  ∀ x y, s.edge x y = true → s.color x = .black → s.color y = .white → GreyProtected s y
```

`RootsNonWhite`:

```lean
-- lean/Toy/Tricolor/Basic.lean:83-84
/-- Every root is non-white. -/
def RootsNonWhite (s : St n) : Prop := ∀ r, s.root r = true → s.color r ≠ .white
```

`RootsProtected`:

```lean
-- lean/Toy/Tricolor/Basic.lean:86-89
/-- Every white root is grey protected. This is the root clause of the weak invariant for a
mutator whose roots are not rescanned (the roots are treated like a black object). -/
def RootsProtected (s : St n) : Prop :=
  ∀ r, s.root r = true → s.color r = .white → GreyProtected s r
```

`AllLiveBlack`:

```lean
-- lean/Toy/Tricolor/Basic.lean:91-93
/-- Marking safety: every live object is black (so freeing the white objects frees no live
object). -/
def AllLiveBlack (s : St n) : Prop := ∀ y, Live s y → s.color y = .black
```

`Isolated`:

```lean
-- lean/Toy/Tricolor/Basic.lean:95-98
/-- `Isolated s a`: no edge leaves or enters `a` (a cell with null fields that no object points
to). Allocation requires it: a freshly allocated object has zeroed pointer fields, which the
mutator fills later with ordinary (barriered) stores. -/
def Isolated (s : St n) (a : Fin n) : Prop := ∀ v, s.edge a v = false ∧ s.edge v a = false
```

#### Operations and barriers

`shade`:

```lean
-- lean/Toy/Tricolor/Basic.lean:111-113
/-- Shade `y`: grey it if it is white, otherwise leave it unchanged. -/
def shade (c : Fin n → Color) (y : Fin n) : Fin n → Color :=
  fun v => if v = y ∧ c v = .white then .grey else c v
```

`addEdge`:

```lean
-- lean/Toy/Tricolor/Basic.lean:115-117
/-- Add the edge `x → y`. -/
def addEdge (e : Fin n → Fin n → Bool) (x y : Fin n) : Fin n → Fin n → Bool :=
  fun u v => if u = x ∧ v = y then true else e u v
```

`delEdge`:

```lean
-- lean/Toy/Tricolor/Basic.lean:119-121
/-- Remove the edge `x → z`. -/
def delEdge (e : Fin n → Fin n → Bool) (x z : Fin n) : Fin n → Fin n → Bool :=
  fun u v => if u = x ∧ v = z then false else e u v
```

`scan`:

```lean
-- lean/Toy/Tricolor/Basic.lean:123-128
/-- Collector step: grey the white successors of `g` and blacken `g`. As a step of the
system (`Op.Enabled`) it requires `g` to be grey. -/
def scan (s : St n) (g : Fin n) : St n :=
  { s with color := fun v =>
      if v = g then .black
      else if s.edge g v = true ∧ s.color v = .white then .grey else s.color v }
```

`Barrier`:

```lean
-- lean/Toy/Tricolor/Basic.lean:130-137
/-- Heap write barriers. `none`: no barrier. `dijkstra`: insertion barrier, shades the new
target of a store. `yuasa`: deletion (snapshot-at-the-beginning) barrier, shades the old target
of an erased pointer. -/
inductive Barrier where
  | none
  | dijkstra
  | yuasa
  deriving DecidableEq, Repr
```

`store`:

```lean
-- lean/Toy/Tricolor/Basic.lean:139-143
/-- Mutator store `x.f := y` into a previously null field: add `x → y`; the Dijkstra barrier
shades `y`. -/
def store (b : Barrier) (s : St n) (x y : Fin n) : St n :=
  { s with edge := addEdge s.edge x y,
           color := if b = .dijkstra then shade s.color y else s.color }
```

`erase`:

```lean
-- lean/Toy/Tricolor/Basic.lean:145-149
/-- Mutator erase of the pointer `x → z` (the deletion half of an overwrite, or a store of
null): remove `x → z`; the Yuasa barrier shades the old target `z` if the edge existed. -/
def erase (b : Barrier) (s : St n) (x z : Fin n) : St n :=
  { s with edge := delEdge s.edge x z,
           color := if b = .yuasa ∧ s.edge x z = true then shade s.color z else s.color }
```

`load`:

```lean
-- lean/Toy/Tricolor/Basic.lean:151-156
/-- Mutator root load: `y` becomes a root. Root writes run no heap barrier; with
`shadeLoads = true` the loaded object is shaded (a load barrier, the load-side discipline
that keeps the mutator black). -/
def load (shadeLoads : Bool) (s : St n) (y : Fin n) : St n :=
  { s with root := fun v => if v = y then true else s.root v,
           color := if shadeLoads then shade s.color y else s.color }
```

`drop`:

```lean
-- lean/Toy/Tricolor/Basic.lean:158-160
/-- Mutator root drop: `r` stops being a root. -/
def drop (s : St n) (r : Fin n) : St n :=
  { s with root := fun v => if v = r then false else s.root v }
```

`alloc`:

```lean
-- lean/Toy/Tricolor/Basic.lean:162-170
/-- Allocation of object `a` with color `c` into the roots. As a step (`Op.Enabled`) it
requires `a` to be an isolated non-root object of any current color. An allocation of a cell
that is white in the current state models taking a free cell; an allocation of a cell that is
already grey or black in the current marking cycle re-colors it (no sweep runs in between),
which stands in for a fresh cell beyond the `n` initial ones and is what lets allocation add
collector work (see the termination module). -/
def alloc (s : St n) (a : Fin n) (c : Color) : St n :=
  { s with root := fun v => if v = a then true else s.root v,
           color := fun v => if v = a then c else s.color v }
```

`initMark`:

```lean
-- lean/Toy/Tricolor/Basic.lean:172-177
/-- Start of a marking cycle: grey every root, whiten everything else. This is one atomic step
that shades every root-referenced object at once, modeling a stop-the-world root snapshot (the
mutator is black from the start of the cycle); it does not model thread stacks that stay grey
and are scanned concurrently with the heap. -/
def initMark (s : St n) : St n :=
  { s with color := fun v => if s.root v = true then .grey else .white }
```

`rescan`:

```lean
-- lean/Toy/Tricolor/Basic.lean:179-181
/-- Root rescan: grey every white root. -/
def rescan (s : St n) : St n :=
  { s with color := fun v => if s.root v = true ∧ s.color v = .white then .grey else s.color v }
```

#### Configurations, steps and runs

`Config`:

```lean
-- lean/Toy/Tricolor/Basic.lean:183-188
/-- A collector configuration: heap barrier, whether root loads are shaded, and which
allocation colors the allocator may use. -/
structure Config where
  barrier : Barrier
  shadeLoads : Bool
  allocOk : Color → Bool
```

`Op`:

```lean
-- lean/Toy/Tricolor/Basic.lean:190-198
/-- Steps of the system (collector `scan`, mutator operations). -/
inductive Op (n : Nat) where
  | scan (g : Fin n)
  | store (x y : Fin n)
  | erase (x z : Fin n)
  | load (y : Fin n)
  | drop (r : Fin n)
  | alloc (a : Fin n) (c : Color)
  deriving DecidableEq, Repr
```

`Op.apply`:

```lean
-- lean/Toy/Tricolor/Basic.lean:200-207
/-- The effect of a step. -/
def Op.apply (cfg : Config) : Op n → St n → St n
  | .scan g, s => Tricolor.scan s g
  | .store x y, s => Tricolor.store cfg.barrier s x y
  | .erase x z, s => Tricolor.erase cfg.barrier s x z
  | .load y, s => Tricolor.load cfg.shadeLoads s y
  | .drop r, s => Tricolor.drop s r
  | .alloc a c, s => Tricolor.alloc s a c
```

`Op.Enabled`:

```lean
-- lean/Toy/Tricolor/Basic.lean:209-219
/-- When a step may fire. The collector scans only grey objects. The mutator may store into a
heap field only a pointer it holds in its roots (`s.root y = true`), and may load into its roots
only an object it can reach (`Live s y`). Allocation takes an isolated non-root object and an
allowed color. -/
def Op.Enabled (cfg : Config) : Op n → St n → Prop
  | .scan g, s => s.color g = .grey
  | .store _ y, s => s.root y = true
  | .erase _ _, _ => True
  | .load y, s => Live s y
  | .drop _, _ => True
  | .alloc a c, s => cfg.allocOk c = true ∧ s.root a = false ∧ Isolated s a
```

`Run`:

```lean
-- lean/Toy/Tricolor/Basic.lean:221-225
/-- `Run cfg s ops s'`: executing the enabled steps `ops` from `s` reaches `s'`. -/
inductive Run (cfg : Config) : St n → List (Op n) → St n → Prop where
  | nil (s : St n) : Run cfg s [] s
  | cons {s s' : St n} {op : Op n} {ops : List (Op n)} :
      op.Enabled cfg s → Run cfg (op.apply cfg s) ops s' → Run cfg s (op :: ops) s'
```

`Step`:

```lean
-- lean/Toy/Tricolor/Basic.lean:227-229
/-- One enabled step. -/
def Step (cfg : Config) (s s' : St n) : Prop :=
  ∃ op : Op n, op.Enabled cfg s ∧ s' = op.apply cfg s
```

`runOps`:

```lean
-- lean/Toy/Tricolor/Basic.lean:231-233
/-- The final state of executing `ops` (ignoring enabledness). -/
def runOps (cfg : Config) (ops : List (Op n)) (s : St n) : St n :=
  ops.foldl (fun t op => op.apply cfg t) s
```

`Op.isScan`:

```lean
-- lean/Toy/Tricolor/Basic.lean:235-238
/-- Whether a step is a collector scan. -/
def Op.isScan : Op n → Bool
  | .scan _ => true
  | _ => false
```

#### Paused mutator and color bookkeeping

`ScansOnly`:

```lean
-- lean/Toy/Tricolor/Marking.lean:29-30
/-- `ScansOnly ops`: every step in `ops` is a collector scan (the mutator is paused). -/
def ScansOnly (ops : List (Op n)) : Prop := ∀ op ∈ ops, op.isScan = true
```

`ShadeLe`:

```lean
-- lean/Toy/Tricolor/Preservation.lean:20-22
/-- `ShadeLe s s'`: the colors of `s'` are those of `s` with some white objects greyed. -/
def ShadeLe (s s' : St n) : Prop :=
  ∀ v, s'.color v = s.color v ∨ (s.color v = .white ∧ s'.color v = .grey)
```

#### Termination

`weight`:

```lean
-- lean/Toy/Tricolor/Termination.lean:28-32
/-- Weight of a color in the termination measure. -/
def weight : Color → Nat
  | .white => 2
  | .grey => 1
  | .black => 0
```

`markMeasure`:

```lean
-- lean/Toy/Tricolor/Termination.lean:34-35
/-- The termination measure `2·#white + #grey`. -/
def markMeasure (s : St n) : Nat := ((List.finRange n).map (fun x => weight (s.color x))).sum
```

`Op.allocWeight`:

```lean
-- lean/Toy/Tricolor/Termination.lean:37-41
/-- The measure increase an allocation may cause (`weight c` for an allocation of color `c`,
zero for every other step). -/
def Op.allocWeight : Op n → Nat
  | .alloc _ c => weight c
  | _ => 0
```

`AllocTargetsWhite`:

```lean
-- lean/Toy/Tricolor/Termination.lean:306-312
/-- `AllocTargetsWhite cfg s ops`: along the execution of `ops` from `s`, every allocation takes
a cell that is white in the state where it happens (a cell not yet reached in this marking
cycle), rather than re-coloring a grey or black cell. -/
def AllocTargetsWhite (cfg : Config) : St n → List (Op n) → Prop
  | _, [] => True
  | s, op :: ops =>
    (∀ a c, op = .alloc a c → s.color a = .white) ∧ AllocTargetsWhite cfg (op.apply cfg s) ops
```

`InfRun`:

```lean
-- lean/Toy/Tricolor/Termination.lean:330-332
/-- An infinite execution: every step is enabled and determines the next state. -/
def InfRun (cfg : Config) (ops : Nat → Op n) (st : Nat → St n) : Prop :=
  ∀ i, (ops i).Enabled cfg (st i) ∧ st (i + 1) = (ops i).apply cfg (st i)
```

`CollectorFair`:

```lean
-- lean/Toy/Tricolor/Termination.lean:334-337
/-- Weak fairness of the collector: if from some point on a grey object always exists (so a
scan is always enabled), then scans occur infinitely often. -/
def CollectorFair (ops : Nat → Op n) (st : Nat → St n) : Prop :=
  ∀ M, (∀ i, M ≤ i → ¬ NoGrey (st i)) → ∀ N, ∃ i, N ≤ i ∧ (ops i).isScan = true
```

`EventuallyOnlyBlackAllocs`:

```lean
-- lean/Toy/Tricolor/Termination.lean:339-341
/-- From some point on, every allocation is black (allocation weight zero). -/
def EventuallyOnlyBlackAllocs (ops : Nat → Op n) : Prop :=
  ∃ N, ∀ i, N ≤ i → (ops i).allocWeight = 0
```

`WhiteTargetAllocs`:

```lean
-- lean/Toy/Tricolor/Termination.lean:343-346
/-- Every allocation of the infinite execution takes a cell that is white in the state where it
happens. -/
def WhiteTargetAllocs (ops : Nat → Op n) (st : Nat → St n) : Prop :=
  ∀ i a c, ops i = .alloc a c → (st i).color a = .white
```

#### Named instances

Concrete states, configurations, step sequences and executions used by the statements, counterexamples, non-vacuity witnesses and positive controls below (`mk n edges roots colors` builds a state over `Fin n`; objects beyond the color list are white).

`cfgU`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:17-18
/-- No heap barrier; root loads shaded (a load barrier); black allocation only. -/
def cfgU : Config := { barrier := .none, shadeLoads := true, allocOk := fun c => c == .black }
```

`cfgN0`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:19-21
/-- No heap barrier; root loads not shaded; black allocation only. -/
def cfgN0 : Config :=
  { barrier := .none, shadeLoads := false, allocOk := fun c => c == .black }
```

`cfgD`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:22-23
/-- Dijkstra barrier; root loads shaded; black allocation only. -/
def cfgD : Config := { barrier := .dijkstra, shadeLoads := true, allocOk := fun c => c == .black }
```

`cfgD0`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:24-26
/-- Dijkstra barrier; root loads not shaded; black allocation only. -/
def cfgD0 : Config :=
  { barrier := .dijkstra, shadeLoads := false, allocOk := fun c => c == .black }
```

`cfgDW`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:27-28
/-- Dijkstra barrier; root loads shaded; every allocation color allowed. -/
def cfgDW : Config := { barrier := .dijkstra, shadeLoads := true, allocOk := fun _ => true }
```

`cfgY`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:29-30
/-- Yuasa barrier; root loads not shaded; black allocation only. -/
def cfgY : Config := { barrier := .yuasa, shadeLoads := false, allocOk := fun c => c == .black }
```

`cfgYW`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:31-32
/-- Yuasa barrier; root loads not shaded; every allocation color allowed. -/
def cfgYW : Config := { barrier := .yuasa, shadeLoads := false, allocOk := fun _ => true }
```

`hChain`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:39-41
/-- Heap shape: root `0` points to `1`, which points to `2` (colors irrelevant before
`initMark`). -/
def hChain : St 3 := mk 3 [(0, 1), (1, 2)] [0] []
```

`sChain`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:42-43
/-- Mid-marking: black root `0`, grey `1`, white `2` along `0 → 1 → 2`. -/
def sChain : St 3 := mk 3 [(0, 1), (1, 2)] [0] [.black, .grey, .white]
```

`hAlloc`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:44-45
/-- Heap shape: root `0`; object `1` isolated and not a root (free for allocation). -/
def hAlloc : St 2 := mk 2 [] [0] []
```

`sChainR`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:47-49
/-- Mid-marking: black root `0`, grey `1`, and the white object `2`, which is held in the roots
and grey protected through `1 → 2`. -/
def sChainR : St 3 := mk 3 [(0, 1), (1, 2)] [0, 2] [.black, .grey, .white]
```

`sChainShaded`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:50-51
/-- As `sChainR`, but `2` was shaded when it was loaded into the roots. -/
def sChainShaded : St 3 := mk 3 [(0, 1), (1, 2)] [0, 2] [.black, .grey, .grey]
```

`sFree`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:132-133
/-- Black root `0`; object `1` isolated, not a root, white. -/
def sFree : St 2 := mk 2 [] [0] [.black, .white]
```

`sWhiteRootUnprotected`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:147-149
/-- Black root `0` and white root `1`, no edges: the weak invariant holds, its root clause
fails. -/
def sWhiteRootUnprotected : St 2 := mk 2 [] [0, 1] [.black, .white]
```

`traceLostObject`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:179-181
/-- Scan the root `0`; load the white object `2` into the roots; store it into the black root
`0`; drop it from the roots; erase its other path `1 → 2`; scan `1`. -/
def traceLostObject : List (Op 3) := [.scan 0, .load 2, .store 0 2, .drop 2, .erase 1 2, .scan 1]
```

`sLost`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:198-199
/-- The final state of `traceLostObject` without a heap barrier and without load shading. -/
def sLost : St 3 := runOps cfgN0 traceLostObject (initMark hChain)
```

`traceLostObjectHeld`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:218-221
/-- `traceLostObject` with every heap write made through a held pointer: `1` is loaded before
the erase and dropped afterwards. -/
def traceLostObjectHeld : List (Op 3) :=
  [.scan 0, .load 2, .store 0 2, .drop 2, .load 1, .erase 1 2, .drop 1, .scan 1]
```

`traceLoadLost`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:320-322
/-- Scan the root; load the white object `2` into the roots; erase its heap path `1 → 2`;
scan `1`. -/
def traceLoadLost : List (Op 3) := [.scan 0, .load 2, .erase 1 2, .scan 1]
```

`sLoadLost`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:331-332
/-- The final state of `traceLoadLost` under the Dijkstra barrier without load shading. -/
def sLoadLost : St 3 := runOps cfgD0 traceLoadLost (initMark hChain)
```

`sAfterScan0`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:378-379
/-- After the first scan of `traceLoadLost`. -/
def sAfterScan0 : St 3 := runOps cfgD0 [.scan 0] (initMark hChain)
```

`drainWithMutator`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:380-381
/-- Mutator steps during the drain after a remark. -/
def drainWithMutator : List (Op 3) := [.load 2, .erase 1 2, .scan 1]
```

`sDrainLost`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:382-382
def sDrainLost : St 3 := runOps cfgD0 drainWithMutator (rescan sAfterScan0)
```

`traceWhiteAlloc`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:405-406
/-- Allocate `1` white into the roots, then scan the root. -/
def traceWhiteAlloc : List (Op 2) := [.alloc 1 .white, .scan 0]
```

`sWhiteAlloc`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:412-412
def sWhiteAlloc : St 2 := runOps cfgDW traceWhiteAlloc (initMark hAlloc)
```

`sWhiteAllocY`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:433-433
def sWhiteAllocY : St 2 := runOps cfgYW traceWhiteAlloc (initMark hAlloc)
```

`traceUnisolatedBlackAlloc`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:643-645
/-- An enabled scan of `0`, then a black allocation of the object `1`, which is not isolated
(it still points to the white object `2`). -/
def traceUnisolatedBlackAlloc : List (Op 3) := [.scan 0, .alloc 1 .black]
```

`traceUnheldStore`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:647-649
/-- An enabled scan of `0`, a heap store `0 → 2` of the object `2`, which is reachable but not
held in the roots (it was never loaded), then an erase of `1 → 2` and an enabled scan of `1`. -/
def traceUnheldStore : List (Op 3) := [.scan 0, .store 0 2, .erase 1 2, .scan 1]
```

`mk`:

```lean
-- lean/Toy/Tricolor/Examples.lean:13-18
/-- Build a concrete state from an edge list, a root list and a color list (objects beyond
the color list are white). -/
def mk (n : Nat) (edges : List (Nat × Nat)) (roots : List Nat) (colors : List Color) : St n :=
  { edge := fun u v => edges.contains (u.val, v.val)
    root := fun r => roots.contains r.val
    color := fun x => colors.getD x.val .white }
```

`sBlackWhite`:

```lean
-- lean/Toy/Tricolor/Examples.lean:20-21
/-- Root `0` is black and points to the white object `1`; nothing is grey. -/
def sBlackWhite : St 2 := mk 2 [(0, 1)] [0] [.black, .white]
```

`sGreyWhite`:

```lean
-- lean/Toy/Tricolor/Examples.lean:22-23
/-- Root `0` is grey and points to the white object `1`. -/
def sGreyWhite : St 2 := mk 2 [(0, 1)] [0] [.grey, .white]
```

`sWhiteRoot`:

```lean
-- lean/Toy/Tricolor/Examples.lean:24-25
/-- A single white root with no edges. -/
def sWhiteRoot : St 1 := mk 1 [] [0] [.white]
```

`sWeakNotStrong`:

```lean
-- lean/Toy/Tricolor/Examples.lean:26-27
/-- Black root `0` points to grey `1` and to white `2`; grey `1` also points to `2`. -/
def sWeakNotStrong : St 3 := mk 3 [(0, 1), (1, 2), (0, 2)] [0] [.black, .grey, .white]
```

`sDone`:

```lean
-- lean/Toy/Tricolor/Examples.lean:28-29
/-- Marking finished: root `0` and its successor `1` are black; `2` is unreachable and white. -/
def sDone : St 3 := mk 3 [(0, 1), (2, 1)] [0] [.black, .black, .white]
```

`sProtectedRoot`:

```lean
-- lean/Toy/Tricolor/Examples.lean:30-31
/-- Root `1` is white but grey protected through the grey non-root `0`. -/
def sProtectedRoot : St 2 := mk 2 [(0, 1)] [1] [.grey, .white]
```

`cfgNone`:

```lean
-- lean/Toy/Tricolor/Examples.lean:167-169
/-- The configuration without any barrier, without load shading, allowing every allocation
color. -/
def cfgNone : Config := { barrier := .none, shadeLoads := false, allocOk := fun _ => true }
```

`opsFrom`:

```lean
-- lean/Toy/Tricolor/Termination.lean:529-532
/-- The prefix `ops i, …, ops (i + k - 1)` of an infinite execution. -/
def opsFrom (ops : Nat → Op n) (i : Nat) : Nat → List (Op n)
  | 0 => []
  | k + 1 => ops i :: opsFrom ops (i + 1) k
```

`cfgGreyAlloc`:

```lean
-- lean/Toy/Tricolor/Termination.lean:555-556
/-- Grey allocation allowed. -/
def cfgGreyAlloc : Config := { barrier := .dijkstra, shadeLoads := true, allocOk := fun _ => true }
```

`cycSt`:

```lean
-- lean/Toy/Tricolor/Termination.lean:558-566
/-- A six-step cycle over two garbage objects that are repeatedly allocated grey, dropped from
the roots and scanned. -/
def cycSt : Nat → St 2
  | 0 => mk 2 [] [] [.grey, .black]
  | 1 => mk 2 [] [1] [.grey, .grey]
  | 2 => mk 2 [] [] [.grey, .grey]
  | 3 => mk 2 [] [] [.black, .grey]
  | 4 => mk 2 [] [0] [.grey, .grey]
  | _ => mk 2 [] [] [.grey, .grey]
```

`cycOp`:

```lean
-- lean/Toy/Tricolor/Termination.lean:568-574
def cycOp : Nat → Op 2
  | 0 => .alloc 1 .grey
  | 1 => .drop 1
  | 2 => .scan 0
  | 3 => .alloc 0 .grey
  | 4 => .drop 0
  | _ => .scan 1
```

`cycStates`:

```lean
-- lean/Toy/Tricolor/Termination.lean:576-576
def cycStates (i : Nat) : St 2 := cycSt (i % 6)
```

`cycOps`:

```lean
-- lean/Toy/Tricolor/Termination.lean:577-577
def cycOps (i : Nat) : Op 2 := cycOp (i % 6)
```

`sOneGrey`:

```lean
-- lean/Toy/Tricolor/Termination.lean:646-647
/-- A single grey object that the mutator never lets the collector scan. -/
def sOneGrey : St 1 := mk 1 [] [] [.grey]
```

`starveOps`:

```lean
-- lean/Toy/Tricolor/Termination.lean:649-649
def starveOps : Nat → Op 1 := fun _ => .drop 0
```

`starveStates`:

```lean
-- lean/Toy/Tricolor/Termination.lean:650-650
def starveStates : Nat → St 1 := fun _ => sOneGrey
```

`sOneBlack`:

```lean
-- lean/Toy/Tricolor/Termination.lean:673-674
/-- One black object. -/
def sOneBlack : St 1 := mk 1 [] [] [.black]
```

`sGreyAndBlack`:

```lean
-- lean/Toy/Tricolor/Termination.lean:696-697
/-- Grey `0` and black `1`. -/
def sGreyAndBlack : St 2 := mk 2 [] [] [.grey, .black]
```

`badScanOps`:

```lean
-- lean/Toy/Tricolor/Termination.lean:698-698
def badScanOps : Nat → Op 2 := fun _ => .scan 1
```

`badScanStates`:

```lean
-- lean/Toy/Tricolor/Termination.lean:699-699
def badScanStates : Nat → St 2 := fun _ => sGreyAndBlack
```

`activeStates`:

```lean
-- lean/Toy/Tricolor/Termination.lean:724-729
/-- Scan a grey root, then allocate the free cell `1` black and drop it, forever (black
allocation occurs infinitely often). -/
def activeStates : Nat → St 2
  | 0 => mk 2 [] [0] [.grey, .white]
  | 1 => mk 2 [] [0] [.black, .white]
  | k + 2 => if k % 2 = 0 then mk 2 [] [0, 1] [.black, .black] else mk 2 [] [0] [.black, .black]
```

`activeOps`:

```lean
-- lean/Toy/Tricolor/Termination.lean:731-733
def activeOps : Nat → Op 2
  | 0 => .scan 0
  | k + 1 => if k % 2 = 0 then .alloc 1 .black else .drop 1
```

`wStates`:

```lean
-- lean/Toy/Tricolor/Termination.lean:783-787
/-- Allocate the white free cell `1` white into the roots and drop it, forever: every allocation
takes a white cell, white allocation occurs infinitely often (so allocation is never eventually
black-only), and the collector is fair. -/
def wStates (i : Nat) : St 2 :=
  if i % 2 = 0 then mk 2 [] [0] [.black, .white] else mk 2 [] [0, 1] [.black, .white]
```

`wOps`:

```lean
-- lean/Toy/Tricolor/Termination.lean:788-788
def wOps (i : Nat) : Op 2 := if i % 2 = 0 then .alloc 1 .white else .drop 1
```

`wtStates`:

```lean
-- lean/Toy/Tricolor/Termination.lean:894-902
/-- Start with the grey root `0` and the free cells `1`, `2`; allocate the white cell `1` grey,
scan `0` and `1`, then allocate the white cell `2` white and drop it, forever. -/
def wtStates : Nat → St 3
  | 0 => mk 3 [] [0] [.grey, .white, .white]
  | 1 => mk 3 [] [0, 1] [.grey, .grey, .white]
  | 2 => mk 3 [] [0, 1] [.black, .grey, .white]
  | k + 3 =>
    if k % 2 = 0 then mk 3 [] [0, 1] [.black, .black, .white]
    else mk 3 [] [0, 1, 2] [.black, .black, .white]
```

`wtOps`:

```lean
-- lean/Toy/Tricolor/Termination.lean:904-908
def wtOps : Nat → Op 3
  | 0 => .alloc 1 .grey
  | 1 => .scan 0
  | 2 => .scan 1
  | k + 3 => if k % 2 = 0 then .alloc 2 .white else .drop 2
```

`sWhiteRootFree`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:18-19
/-- White root `0`; object `1` isolated, not a root. -/
def sWhiteRootFree : St 2 := mk 2 [] [0] [.white, .white]
```

`sGreyToOne`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:33-34
/-- Grey root `0` pointing to the non-isolated object `1`. -/
def sGreyToOne : St 2 := mk 2 [(0, 1)] [0] [.grey, .white]
```

`sevenDrops`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:107-108
/-- Seven root drops. -/
def sevenDrops : List (Op 3) := [.drop 0, .drop 0, .drop 0, .drop 0, .drop 0, .drop 0, .drop 0]
```

### End of marking

#### `no-grey-strong-nonwhite-roots-implies-live-black`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** In a state with no grey object in which the strong invariant holds (no black-to-white edge) and every root is non-white, every object reachable from the roots is black.
- **Tier justification (prose):** Known: the end-of-marking argument for P1 in Dijkstra et al. ('after the collector had initialized the marking phase by shading all roots, the validity of P1 allowed us to conclude that the existence of a white reachable node implied the existence of a grey node'), restated for an explicit root set with the root condition as a hypothesis.

**Lean statement** (`allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:21-24
/-- **End-of-marking safety (strong invariant).** If no object is grey, the strong invariant
holds and every root is non-white, then every live object is black. -/
theorem allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite {s : St n}
    (hng : NoGrey s) (hs : Strong s) (hr : RootsNonWhite s) : AllLiveBlack s := by
```

Unfolded statement of `allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite` (a Lean term with `NoGrey`, `Strong`, `RootsNonWhite` and `AllLiveBlack` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
(∀ x, s.color x ≠ .grey) →
  (∀ x y, s.edge x y = true → s.color x = .black → s.color y ≠ .white) →
  (∀ r, s.root r = true → s.color r ≠ .white) →
  ∀ y, Live s y → s.color y = .black
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hng : NoGrey s` | Marking has terminated; a grey object may still have reachable white successors. | tight | `strong_rootsNonWhite_and_not_allLiveBlack` | a 2-object heap state |
| `hs : Strong s` | Propagates blackness along edges. | tight | `noGrey_rootsNonWhite_and_not_allLiveBlack` | a 2-object heap state |
| `hr : RootsNonWhite s` | Base case: roots are black once nothing is grey. | tight | `noGrey_strong_and_not_allLiveBlack` | a 1-object heap state |

Counterexample statements (verbatim):

`strong_rootsNonWhite_and_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:99-102
/-- `NoGrey` cannot be dropped (a 2-object state): a grey root pointing to a white object satisfies the strong invariant
and has non-white roots, yet a live object is white. -/
theorem strong_rootsNonWhite_and_not_allLiveBlack :
    Strong sGreyWhite ∧ RootsNonWhite sGreyWhite ∧ ¬ AllLiveBlack sGreyWhite :=
```

`noGrey_rootsNonWhite_and_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:105-108
/-- The invariant cannot be dropped (a 2-object state): a black root pointing to a white
object, nothing grey. -/
theorem noGrey_rootsNonWhite_and_not_allLiveBlack :
    NoGrey sBlackWhite ∧ RootsNonWhite sBlackWhite ∧ ¬ AllLiveBlack sBlackWhite :=
```

`noGrey_strong_and_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:111-113
/-- Non-white roots cannot be dropped (a 1-object state): a lone white root. -/
theorem noGrey_strong_and_not_allLiveBlack :
    NoGrey sWhiteRoot ∧ Strong sWhiteRoot ∧ ¬ AllLiveBlack sWhiteRoot :=
```

**Non-vacuity witness (prose):** sDone: black root 0 -> black 1, unreachable white 2 (with an edge 2 -> 1); no grey object.

`allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:165-166
theorem allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite_nonvacuous :
    NoGrey sDone ∧ Strong sDone ∧ RootsNonWhite sDone :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. P1: 'during marking there will be no edge pointing from a black node to a white one'; the roots are 'one or more fixed nodes —called “the roots”— with a constant place in memory', and the collector initializes the marking phase by shading all roots.
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsection 'The strong and weak tricolour invariants'.
- Gammie, Hosking, Engelhardt. Relaxing safely: verified on-the-fly garbage collection for x86-TSO. PLDI 2015, pp. 99-109. doi:10.1145/2737924.2738006. Isabelle/HOL development: Archive of Formal Proofs, entry ConcurrentGC (2015), https://isa-afp.org/entries/ConcurrentGC.html (a safety proof of a Schism-style collector on x86-TSO; no termination proof). Its lemma reachable_blackD is the analogous end-of-marking statement for the snapshot invariant: Defines reachable_snapshot_inv (every reachable object is black or grey protected, via in_snapshot) and proves reachable_blackD (no grey references, reachable_snapshot_inv and reachability imply black), with lemmas including reachable_snapshot_inv_load (root loads) and reachable_snapshot_inv_alloc (allocation).

**Design question.** What does the strong invariant guarantee at the end of marking, and which additional condition on roots is needed?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge), a separate claim connecting the theorem to a collector that sweeps (sweeping is not part of the model; not a theorem). Reasoning: A sweep that frees exactly the white objects of a state satisfying the conclusion frees no object reachable from the roots; sweeping is not modeled.

Non-claims: see **Boundaries → Non-claims** (`no-grey-strong-nonwhite-roots-implies-live-black`).

#### `weak-and-roots-protected-imply-live-white-grey-protected`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** If the weak invariant holds and every white root is grey protected, then every white object reachable from the roots is grey protected (reachable from a grey object through white objects only).
- **Tier justification (prose):** Known: Lemmas 2 and 3 of the appendix of Clements and Hudson prove the analogous statement for the hybrid barrier's invariant; the conclusion is P2 of Dijkstra et al. for the current roots; the AFP entry ConcurrentGC mechanizes the related invariant reachable_snapshot_inv. Restated here with the root clause as an explicit hypothesis.

**Lean statement** (`greyProtected_of_live_of_white_of_weak_of_rootsProtected`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:51-55
/-- **Grey protection of live white objects.** Under the weak invariant together with its root
clause (every white root is grey protected), every live white object is grey protected. -/
theorem greyProtected_of_live_of_white_of_weak_of_rootsProtected {s : St n}
    (hw : Weak s) (hr : RootsProtected s) {y : Fin n} (hy : Live s y)
    (hwh : s.color y = .white) : GreyProtected s y := by
```

Unfolded statement of `greyProtected_of_live_of_white_of_weak_of_rootsProtected` (a Lean term with `Weak` and `RootsProtected` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
(∀ x y, s.edge x y = true → s.color x = .black → s.color y = .white → GreyProtected s y) →
  (∀ r, s.root r = true → s.color r = .white → GreyProtected s r) →
  ∀ {y : Fin n}, Live s y → s.color y = .white → GreyProtected s y
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hw : Weak s` | Handles black predecessors on the path from a root. | tight | `rootsProtected_live_white_and_not_greyProtected` | a 2-object heap state |
| `hr : RootsProtected s` | Base case at the roots. | tight | `weak_live_white_and_not_greyProtected` | a 1-object heap state |
| `hy : Live s y` | Unreachable white objects are not constrained by the root clause. | tight | `weak_rootsProtected_white_and_not_greyProtected` | a 3-object heap state |
| `hwh : s.color y = .white` | Grey protection is defined for white objects only. | tight | `weak_rootsProtected_live_and_not_greyProtected` | a 2-object heap state |

Counterexample statements (verbatim):

`rootsProtected_live_white_and_not_greyProtected`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:132-136
/-- The weak invariant cannot be dropped from grey protection of live white objects (a
2-object state: a black root pointing to a white object, nothing grey). -/
theorem rootsProtected_live_white_and_not_greyProtected :
    RootsProtected sBlackWhite ∧ Live sBlackWhite 1 ∧ sBlackWhite.color 1 = .white ∧
      ¬ GreyProtected sBlackWhite 1 :=
```

`weak_live_white_and_not_greyProtected`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:139-143
/-- The root clause cannot be dropped from grey protection of live white objects (a 1-object
state: a lone white root). -/
theorem weak_live_white_and_not_greyProtected :
    Weak sWhiteRoot ∧ Live sWhiteRoot 0 ∧ sWhiteRoot.color 0 = .white ∧
      ¬ GreyProtected sWhiteRoot 0 :=
```

`weak_rootsProtected_white_and_not_greyProtected`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:146-149
/-- Liveness cannot be dropped (a 3-object state): an unreachable white object need not be
grey protected. -/
theorem weak_rootsProtected_white_and_not_greyProtected :
    Weak sDone ∧ RootsProtected sDone ∧ sDone.color 2 = .white ∧ ¬ GreyProtected sDone 2 :=
```

`weak_rootsProtected_live_and_not_greyProtected`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:153-157
/-- Whiteness cannot be dropped (a 2-object state): a live grey root is not grey protected (protection is defined for
white objects only). -/
theorem weak_rootsProtected_live_and_not_greyProtected :
    Weak sGreyWhite ∧ RootsProtected sGreyWhite ∧ Live sGreyWhite 0 ∧
      ¬ GreyProtected sGreyWhite 0 :=
```

**Non-vacuity witness (prose):** sWeakNotStrong, object 2: reachable through the black root 0 and protected by grey 1.

`greyProtected_of_live_of_white_of_weak_of_rootsProtected_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:177-181
/-- Non-vacuity of the grey-protection lemma, with a live white object reached through a black
root (so the weak invariant is used, not just a grey parent). -/
theorem greyProtected_of_live_of_white_of_weak_of_rootsProtected_nonvacuous :
    Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧ Live sWeakNotStrong 2 ∧
      sWeakNotStrong.color 2 = .white :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. P2: 'during the marking cycle (that the collector has initialized by shading all roots) there exists for each white reachable node a so-called “propagation path”, leading to it from a (not necessarily reachable) grey node, and consisting solely of edges with white targets (and, as a consequence, without black sources)'.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). States the weak tricolor invariant, attributed to Pirinen (1998): 'Any white object pointed to by a black object is reachable from a grey object via a chain of white pointers (it is grey-protected).' Its appendix 'Proof of soundness, completeness, and boundedness' gives paper proofs for the hybrid barrier: Lemmas 2 and 3 (a white object reachable from a black object, or from a black goroutine, is grey-protected by a heap object), Theorem 1 (the hybrid write barrier satisfies the weak tricolor invariant) and Theorem 2 (marking terminates in a finite number of steps, bounded via the number of objects at the start of the cycle).
- Pirinen. Barrier techniques for incremental tracing. ISMM 1998, pp. 20-25. doi:10.1145/286860.286863. Source of the weak tricolor invariant as quoted in Clements and Hudson (2016).
- Gammie, Hosking, Engelhardt. Relaxing safely: verified on-the-fly garbage collection for x86-TSO. PLDI 2015, pp. 99-109. doi:10.1145/2737924.2738006. Isabelle/HOL development: Archive of Formal Proofs, entry ConcurrentGC (2015), https://isa-afp.org/entries/ConcurrentGC.html (a safety proof of a Schism-style collector on x86-TSO; no termination proof). Defines reachable_snapshot_inv (every reachable object is black or grey protected, via in_snapshot) and proves reachable_blackD (no grey references, reachable_snapshot_inv and reachability imply black), with lemmas including reachable_snapshot_inv_load (root loads) and reachable_snapshot_inv_alloc (allocation).

**Design question.** Why can a snapshot-style collector let the mutator load reachable objects into its roots, and store pointers it holds into black objects, without shading them?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`weak-and-roots-protected-imply-live-white-grey-protected`).

#### `no-grey-weak-roots-protected-implies-live-black`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** In a state with no grey object in which the weak invariant holds and every white root is grey protected, every object reachable from the roots is black.
- **Tier justification (prose):** End-of-marking form of the weak invariant for a collector that does not rescan roots, with the root clause explicit; the AFP entry ConcurrentGC mechanizes the analogous lemma reachable_blackD.

**Lean statement** (`allLiveBlack_of_noGrey_of_weak_of_rootsProtected`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:66-70
/-- **End-of-marking safety (weak invariant, protected roots).** If no object is grey, the
weak invariant holds and every white root is grey protected, then every live object is
black. -/
theorem allLiveBlack_of_noGrey_of_weak_of_rootsProtected {s : St n}
    (hng : NoGrey s) (hw : Weak s) (hr : RootsProtected s) : AllLiveBlack s := by
```

Unfolded statement of `allLiveBlack_of_noGrey_of_weak_of_rootsProtected` (a Lean term with `NoGrey`, `Weak`, `RootsProtected` and `AllLiveBlack` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
(∀ x, s.color x ≠ .grey) →
  (∀ x y, s.edge x y = true → s.color x = .black → s.color y = .white → GreyProtected s y) →
  (∀ r, s.root r = true → s.color r = .white → GreyProtected s r) →
  ∀ y, Live s y → s.color y = .black
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hng : NoGrey s` | Marking has terminated. | tight | `weak_rootsProtected_and_not_allLiveBlack` | a 2-object heap state |
| `hw : Weak s` | Propagation along black predecessors. | tight | `noGrey_rootsProtected_and_not_allLiveBlack` | a 2-object heap state |
| `hr : RootsProtected s` | Root clause. | tight | `noGrey_weak_and_not_allLiveBlack` | a 1-object heap state |

Counterexample statements (verbatim):

`weak_rootsProtected_and_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:124-125
theorem weak_rootsProtected_and_not_allLiveBlack :
    Weak sGreyWhite ∧ RootsProtected sGreyWhite ∧ ¬ AllLiveBlack sGreyWhite :=
```

`noGrey_rootsProtected_and_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:128-129
theorem noGrey_rootsProtected_and_not_allLiveBlack :
    NoGrey sBlackWhite ∧ RootsProtected sBlackWhite ∧ ¬ AllLiveBlack sBlackWhite :=
```

`noGrey_weak_and_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:120-121
theorem noGrey_weak_and_not_allLiveBlack :
    NoGrey sWhiteRoot ∧ Weak sWhiteRoot ∧ ¬ AllLiveBlack sWhiteRoot :=
```

**Non-vacuity witness (prose):** sDone.

`allLiveBlack_of_noGrey_of_weak_of_rootsProtected_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:173-174
theorem allLiveBlack_of_noGrey_of_weak_of_rootsProtected_nonvacuous :
    NoGrey sDone ∧ Weak sDone ∧ RootsProtected sDone :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsections 'The strong and weak tricolour invariants' and 'Snapshot-at-the-beginning solutions'.
- Gammie, Hosking, Engelhardt. Relaxing safely: verified on-the-fly garbage collection for x86-TSO. PLDI 2015, pp. 99-109. doi:10.1145/2737924.2738006. Isabelle/HOL development: Archive of Formal Proofs, entry ConcurrentGC (2015), https://isa-afp.org/entries/ConcurrentGC.html (a safety proof of a Schism-style collector on x86-TSO; no termination proof). Defines reachable_snapshot_inv (every reachable object is black or grey protected, via in_snapshot) and proves reachable_blackD (no grey references, reachable_snapshot_inv and reachability imply black), with lemmas including reachable_snapshot_inv_load (root loads) and reachable_snapshot_inv_alloc (allocation).
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). States the weak tricolor invariant, attributed to Pirinen (1998): 'Any white object pointed to by a black object is reachable from a grey object via a chain of white pointers (it is grey-protected).'

**Design question.** What must a collector that never rescans roots know about its roots at the end of marking?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge), a separate claim connecting the theorem to a collector that sweeps (sweeping is not part of the model; not a theorem). Reasoning: A sweep that frees exactly the white objects of a state satisfying the conclusion frees no object reachable from the roots; sweeping is not modeled.

Non-claims: see **Boundaries → Non-claims** (`no-grey-weak-roots-protected-implies-live-black`).

#### `strong-implies-weak`

- **Kind:** theorem · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** The strong invariant implies the weak invariant.
- **Tier justification (prose):** Immediate from the definitions; mechanized in the AFP entry ConcurrentGC ('strong_tricolour_inv s ⟹ weak_tricolour_inv s') and stated in the textbook treatment.

**Lean statement** (`weak_of_strong`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:30-31
/-- **Strong implies weak.** -/
theorem weak_of_strong {s : St n} (hs : Strong s) : Weak s :=
```

Unfolded statement of `weak_of_strong` (a Lean term with `Strong` and `Weak` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
(∀ x y, s.edge x y = true → s.color x = .black → s.color y ≠ .white) →
  ∀ x y, s.edge x y = true → s.color x = .black → s.color y = .white → GreyProtected s y
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hs : Strong s` | Premise. | tight | `not_weak_sBlackWhite` | a 2-object heap state |

Counterexample statements (verbatim):

`not_weak_sBlackWhite`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:12-15
/-- The premise of `weak_of_strong` cannot be dropped (a 2-object state): a black root pointing
to a white object, nothing
grey, violates the weak invariant. -/
theorem not_weak_sBlackWhite : ¬ Weak sBlackWhite := fun h =>
```

**Non-vacuity witness (prose):** sDone, which has a black object 0 with an edge 0 -> 1 (so the implication inside Weak is exercised).

`weak_of_strong_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:185-188
/-- Non-vacuity of `weak_of_strong` with a black object that has an outgoing edge (so the
implication inside `Weak` is exercised, not vacuous for lack of black objects). -/
theorem weak_of_strong_nonvacuous :
    Strong sDone ∧ sDone.edge 0 1 = true ∧ sDone.color 0 = .black :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Gammie, Hosking, Engelhardt. Relaxing safely: verified on-the-fly garbage collection for x86-TSO. PLDI 2015, pp. 99-109. doi:10.1145/2737924.2738006. Isabelle/HOL development: Archive of Formal Proofs, entry ConcurrentGC (2015), https://isa-afp.org/entries/ConcurrentGC.html (a safety proof of a Schism-style collector on x86-TSO; no termination proof). Defines strong_tricolour_inv, grey_protects_white and weak_tricolour_inv and proves 'strong_tricolour_inv s ⟹ weak_tricolour_inv s'.
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsection 'The strong and weak tricolour invariants'.
- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. Note 2: 'In the absence of edges from a black node to a white one, relation P2 is clearly satisfied' (P1 implies P2 in a cycle whose roots have been shaded; this is not the root-free implication from the strong to the weak invariant stated here).

**Design question.** How do the two tricolor invariants relate?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`strong-implies-weak`).

### One step under barriers and allocation

#### `dijkstra-barrier-preserves-strong`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every configuration whose heap barrier is the Dijkstra insertion barrier (shade the target of every heap store), with any root-load discipline and allocation colors, every state s satisfying the strong invariant, and every successor s' of s under the generated step relation `Step cfg` (an enabled collector scan of a grey object, heap store of a pointer held in the roots, erase, root load of an object reachable from the roots, root drop, or allocation of an isolated non-root object, in any color the configuration allows), the strong invariant holds in s'.
- **Tier justification (prose):** The insertion barrier of Dijkstra et al. maintaining P1 (their coarse-grained solution); restated for an explicit step relation including unbarriered root loads, root drops and allocation.

**Lean statement** (`strong_preserved_of_dijkstra`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Preservation.lean:168-172
/-- **Dijkstra barrier soundness.** With the Dijkstra insertion barrier, every enabled step
(collector scan, store, erase, root load, root drop, allocation of any allowed color)
preserves the strong invariant. -/
theorem strong_preserved_of_dijkstra {cfg : Config} (hb : cfg.barrier = .dijkstra)
    {s s' : St n} (hs : Strong s) (hstep : Step cfg s s') : Strong s' := by
```

Unfolded statement of `strong_preserved_of_dijkstra` (a Lean term with `Strong` and `Step` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
cfg.barrier = .dijkstra → ∀ {s s' : St n},
  (∀ x y, s.edge x y = true → s.color x = .black → s.color y ≠ .white) →
  (∃ op : Op n, op.Enabled cfg s ∧ s' = op.apply cfg s) →
  ∀ x y, s'.edge x y = true → s'.color x = .black → s'.color y ≠ .white
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : cfg.barrier = .dijkstra` | The stored target must be shaded. | tight | `store_unbarriered_breaks_strong`, `store_yuasa_breaks_strong` | a 3-object heap state and one step |
| `hs : Strong s` | Invariant in the pre-state. | tight | `dijkstra_step_from_nonStrong_not_strong` | a 2-object heap state and one step |
| `hstep : Step cfg s s'` | The transition is an enabled step. Load-bearing part: an allocation takes an isolated object (no incoming or outgoing pointers). The store-value and load conditions are not used (strong_store_dijkstra, strong_load hold for every target). | tight | `dijkstra_unisolated_alloc_breaks_strong`, `dijkstra_unisolated_blackAlloc_breaks_strong` | a 3-object heap state and one non-enabled allocation (white or black) |

Counterexample statements (verbatim):

`store_unbarriered_breaks_strong`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:65-69
/-- Without a barrier, a store of a white object held in the roots into a black object breaks
the strong invariant. -/
theorem store_unbarriered_breaks_strong :
    cfgN0.barrier ≠ .dijkstra ∧ Strong sChainR ∧ Step cfgN0 sChainR (store .none sChainR 0 2) ∧
      ¬ Strong (store .none sChainR 0 2) :=
```

`store_yuasa_breaks_strong`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:72-79
/-- **The Yuasa barrier does not preserve the strong invariant** (it preserves the weak one):
from a strong state with a grey-protected white root, the same store under the Yuasa barrier
creates a black-to-white edge. -/
theorem store_yuasa_breaks_strong :
    cfgY.barrier = .yuasa ∧ Strong sChainR ∧ RootsProtected sChainR ∧
      Step cfgY sChainR (store .yuasa sChainR 0 2) ∧
      ¬ Strong (store .yuasa sChainR 0 2) ∧
      Weak (store .yuasa sChainR 0 2) ∧ RootsProtected (store .yuasa sChainR 0 2) := by
```

`dijkstra_step_from_nonStrong_not_strong`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:90-94
/-- The invariant premise of Dijkstra soundness cannot be dropped (a 2-object state and one
step): a step does not repair it. -/
theorem dijkstra_step_from_nonStrong_not_strong :
    cfgD.barrier = .dijkstra ∧ ¬ Strong sBlackWhite ∧ Step cfgD sBlackWhite (drop sBlackWhite 0) ∧
      ¬ Strong (drop sBlackWhite 0) :=
```

`dijkstra_unisolated_alloc_breaks_strong`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:484-492
/-- `Isolated s a` on allocation cannot be dropped from Dijkstra preservation (a 3-object
state): re-coloring the non-isolated
object `1` white and making it a root (all other enabling conditions hold) breaks the strong
invariant. -/
theorem dijkstra_unisolated_alloc_breaks_strong :
    cfgDW.barrier = .dijkstra ∧ Strong sDone ∧ cfgDW.allocOk .white = true ∧
      sDone.root 1 = false ∧ ¬ Isolated sDone 1 ∧
      ¬ (Op.alloc 1 .white).Enabled cfgDW sDone ∧
      ¬ Strong ((Op.alloc 1 .white).apply cfgDW sDone) :=
```

`dijkstra_unisolated_blackAlloc_breaks_strong`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:748-755
/-- `Isolated s a` on allocation cannot be dropped from Dijkstra preservation even for black
allocation (a 3-object state): the allocation step runs no heap barrier, so re-coloring the
object `1`, which points to the white object `2`, black creates a black-to-white edge. -/
theorem dijkstra_unisolated_blackAlloc_breaks_strong :
    cfgD.barrier = .dijkstra ∧ Strong sChain ∧ cfgD.allocOk .black = true ∧
      sChain.root 1 = false ∧ ¬ Isolated sChain 1 ∧
      ¬ (Op.alloc 1 .black).Enabled cfgD sChain ∧
      ¬ Strong ((Op.alloc 1 .black).apply cfgD sChain) :=
```

**Non-vacuity witness (prose):** sChainR (black root 0, grey 1, white root 2 protected by 1) with the Dijkstra store 0 -> 2.

`strong_preserved_of_dijkstra_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:586-587
theorem strong_preserved_of_dijkstra_nonvacuous :
    cfgD.barrier = .dijkstra ∧ Strong sChainR ∧ Step cfgD sChainR (store .dijkstra sChainR 0 2) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. P1: 'during marking there will be no edge pointing from a black node to a white one'; the roots are 'one or more fixed nodes —called “the roots”— with a constant place in memory', and the collector initializes the marking phase by shading all roots. The coarse-grained mutator shades the target of each edge it introduces. In the final fine-grained solution the mutator performs 'redirect for a reachable node an outgoing edge towards a reachable node' and 'shade the target of the edge just placed' as two separate indivisible subactions.
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsection 'Incremental update solutions'; Sec. 15.2 'Barrier techniques for concurrent collection' (pp. 337-344), subsection 'Grey mutator techniques'.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). States the strong tricolor invariant: 'No black object may contain a pointer to a white object.' Describes Go 1.7's coarsened Dijkstra write barrier: stack writes have no barrier, so stacks must be 'permagrey' and are re-scanned 'with the world stopped'; it notes that 'Go already allocates black for other reasons'.
- Gammie, Hosking, Engelhardt. Relaxing safely: verified on-the-fly garbage collection for x86-TSO. PLDI 2015, pp. 99-109. doi:10.1145/2737924.2738006. Isabelle/HOL development: Archive of Formal Proofs, entry ConcurrentGC (2015), https://isa-afp.org/entries/ConcurrentGC.html (a safety proof of a Schism-style collector on x86-TSO; no termination proof). Defines strong_tricolour_inv, grey_protects_white and weak_tricolour_inv and proves 'strong_tricolour_inv s ⟹ weak_tricolour_inv s'.

**Design question.** Which invariant does the insertion barrier maintain, under which mutator operations?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`dijkstra-barrier-preserves-strong`).

#### `yuasa-nonwhite-alloc-preserves-weak-and-roots-protected`

- **Kind:** theorem · **Tier:** T0 · **Depth:** substantive
- **Plain claim (prose):** For every configuration whose heap barrier is the Yuasa deletion barrier (shade the old target of every erased pointer) and whose allocator never allocates white, with root loads shaded or not, every state s satisfying the weak invariant and its root clause (every white root is grey protected), and every successor s' of s under the generated step relation `Step cfg` (an enabled collector scan of a grey object, heap store of a pointer held in the roots, erase, root load of an object reachable from the roots, root drop, or allocation of an isolated non-root object), the weak invariant and its root clause hold in s'.
- **Tier justification (prose):** Snapshot-at-the-beginning correctness with the weak invariant (Pirinen) and an explicit root clause. Clements and Hudson give a paper proof for the related hybrid barrier (appendix, Theorem 1); the AFP entry ConcurrentGC has mechanized lemmas for the related reachable_snapshot_inv under root loads and allocation (reachable_snapshot_inv_load, reachable_snapshot_inv_alloc).

**Lean statement** (`weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Preservation.lean:344-353
/-- **Yuasa barrier soundness (non-white allocation).** With the Yuasa deletion barrier and an
allocator that never allocates white, every enabled step (a scan of a grey object, a store of a
pointer held in the roots, an erase, a root load of a live object, a root drop, an allocation of
an isolated object) preserves the weak invariant together with its root clause (every white
root is grey protected). The theorem has no hypothesis on root-load shading. -/
theorem weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc {cfg : Config}
    (hb : cfg.barrier = .yuasa)
    (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white) {s s' : St n}
    (hw : Weak s) (hr : RootsProtected s) (hstep : Step cfg s s') :
    Weak s' ∧ RootsProtected s' := by
```

Unfolded statement of `weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc` (a Lean term with `Weak`, `RootsProtected` and `Step` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
cfg.barrier = .yuasa → (∀ c, cfg.allocOk c = true → c ≠ .white) → ∀ {s s' : St n},
  (∀ x y, s.edge x y = true → s.color x = .black → s.color y = .white → GreyProtected s y) →
  (∀ r, s.root r = true → s.color r = .white → GreyProtected s r) →
  (∃ op : Op n, op.Enabled cfg s ∧ s' = op.apply cfg s) →
  (∀ x y, s'.edge x y = true → s'.color x = .black → s'.color y = .white → GreyProtected s' y) ∧
    (∀ r, s'.root r = true → s'.color r = .white → GreyProtected s' r)
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : cfg.barrier = .yuasa` | Erasing the last protecting edge must shade its target. | tight | `erase_unbarriered_breaks_weak`, `erase_dijkstra_breaks_weak` | a 3-object heap state and one step |
| `halloc : ∀ c, cfg.allocOk c = true → c ≠ .white` | A white object allocated into the roots is not grey protected. | tight | `alloc_white_yuasa_breaks_rootsProtected` | a 2-object heap state and one step |
| `hw : Weak s` | Invariant in the pre-state. | tight | `yuasa_step_from_nonWeak_not_weak` | a 2-object heap state and one step |
| `hr : RootsProtected s` | Root clause; the weak invariant alone is not preserved by stores. | tight | `yuasa_store_without_rootsProtected_breaks_weak` | a 2-object heap state and one step |
| `hstep : Step cfg s s'` | The transition is an enabled step. Load-bearing parts: a heap store writes a pointer held in the roots (the weaker condition that the stored object is reachable suffices: for every barrier b, if the weak invariant and RootsProtected hold in s and y is reachable from the roots of s, both hold after store b s x y, by weak_rootsProtected_store), a root load takes a reachable object, and an allocation takes an isolated object. | tight | `yuasa_store_of_unreachable_breaks_weak`, `load_of_unreachable_breaks_rootsProtected`, `yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak` | 2- and 3-object heap states and one non-enabled step |

Counterexample statements (verbatim):

`erase_unbarriered_breaks_weak`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:112-118
/-- Without a barrier, erasing the only grey-protected path to a white object pointed to by a
black object breaks the weak invariant. -/
theorem erase_unbarriered_breaks_weak :
    cfgU.barrier ≠ .yuasa ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧
      Step cfgU sWeakNotStrong (erase .none sWeakNotStrong 1 2) ∧
      ¬ Weak (erase .none sWeakNotStrong 1 2) :=
```

`erase_dijkstra_breaks_weak`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:122-128
/-- **The Dijkstra barrier does not preserve the weak invariant** (from a weak, non-strong
state): the same erase under the Dijkstra barrier. -/
theorem erase_dijkstra_breaks_weak :
    cfgD.barrier ≠ .yuasa ∧ (∀ c, cfgD.allocOk c = true → c ≠ .white) ∧
      Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧
      Step cfgD sWeakNotStrong (erase .dijkstra sWeakNotStrong 1 2) ∧
      ¬ Weak (erase .dijkstra sWeakNotStrong 1 2) :=
```

`alloc_white_yuasa_breaks_rootsProtected`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:135-139
/-- White allocation into the roots breaks the root clause under the Yuasa barrier. -/
theorem alloc_white_yuasa_breaks_rootsProtected :
    cfgYW.barrier = .yuasa ∧ cfgYW.allocOk .white = true ∧
      Weak sFree ∧ RootsProtected sFree ∧ Step cfgYW sFree (alloc sFree 1 .white) ∧
      ¬ RootsProtected (alloc sFree 1 .white) := by
```

`yuasa_step_from_nonWeak_not_weak`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:165-170
/-- The invariant premise of Yuasa soundness cannot be dropped (a 2-object state and one
step). -/
theorem yuasa_step_from_nonWeak_not_weak :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      ¬ Weak sBlackWhite ∧ RootsProtected sBlackWhite ∧
      Step cfgY sBlackWhite (drop sBlackWhite 0) ∧ ¬ Weak (drop sBlackWhite 0) := by
```

`yuasa_store_without_rootsProtected_breaks_weak`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:151-157
/-- The root clause cannot be dropped (a 2-object state and one step): a store of an
unprotected white root into a black object breaks the weak invariant under the Yuasa barrier. -/
theorem yuasa_store_without_rootsProtected_breaks_weak :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sWhiteRootUnprotected ∧ ¬ RootsProtected sWhiteRootUnprotected ∧
      Step cfgY sWhiteRootUnprotected (store .yuasa sWhiteRootUnprotected 0 1) ∧
      ¬ Weak (store .yuasa sWhiteRootUnprotected 0 1) := by
```

`yuasa_store_of_unreachable_breaks_weak`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:140-147
/-- The condition on stored pointers cannot be dropped from Yuasa preservation (a 2-object
state; holding the pointer in the roots, or at least its liveness, suffices):
storing the unreachable white object `1` into the black root `0` (all other hypotheses hold)
breaks the weak invariant. -/
theorem yuasa_store_of_unreachable_breaks_weak :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sFree ∧ RootsProtected sFree ∧ ¬ Live sFree 1 ∧
      ¬ (Op.store 0 1).Enabled cfgY sFree ∧ ¬ Weak ((Op.store 0 1).apply cfgY sFree) := by
```

`load_of_unreachable_breaks_rootsProtected`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:155-161
/-- The liveness condition on root loads cannot be dropped from Yuasa preservation (a 2-object
state): loading the unreachable white
object `1` into the roots (all other hypotheses hold) breaks the root clause. -/
theorem load_of_unreachable_breaks_rootsProtected :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sFree ∧ RootsProtected sFree ∧ ¬ (Op.load 1).Enabled cfgY sFree ∧
      ¬ RootsProtected ((Op.load 1).apply cfgY sFree) := by
```

`yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:495-503
/-- `Isolated s a` on allocation cannot be dropped from Yuasa preservation, even for black
allocation (a 3-object state):
re-coloring the protecting grey object `1` black leaves `2` unprotected. -/
theorem yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧ cfgY.allocOk .black = true ∧
      sWeakNotStrong.root 1 = false ∧ ¬ Isolated sWeakNotStrong 1 ∧
      ¬ (Op.alloc 1 .black).Enabled cfgY sWeakNotStrong ∧
      ¬ Weak ((Op.alloc 1 .black).apply cfgY sWeakNotStrong) := by
```

**Non-vacuity witness (prose):** sWeakNotStrong (black root 0 -> 2 protected by grey 1 -> 2) with the Yuasa erase 1 -> 2.

`weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:590-593
theorem weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc_nonvacuous :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧
      Step cfgY sWeakNotStrong (erase .yuasa sWeakNotStrong 1 2) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Yuasa. Real-time garbage collection on general-purpose machines. J. Syst. Softw. 11(3):181-198, 1990. doi:10.1016/0164-1212(90)90084-Y. The deletion (snapshot-at-the-beginning) barrier; as described by Clements and Hudson (2016), 'As originally proposed, the Yuasa barrier takes a complete snapshot of the stack before proceeding with marking.' The weak-invariant formulation used here is Pirinen's (1998), not Yuasa's.
- Pirinen. Barrier techniques for incremental tracing. ISMM 1998, pp. 20-25. doi:10.1145/286860.286863. Source of the weak tricolor invariant as quoted in Clements and Hudson (2016).
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). States the weak tricolor invariant, attributed to Pirinen (1998): 'Any white object pointed to by a black object is reachable from a grey object via a chain of white pointers (it is grey-protected).' On the deletion barrier: 'The Yuasa barrier requires a STW at the beginning of marking to either scan or snapshot stacks'; 'It's sufficient to ensure all stacks are black before scanning any heap objects.' Proposes the hybrid barrier 'shade(*slot); if current stack is grey: shade(ptr)', which requires black allocation and maintains the weak but not the strong invariant. Its appendix 'Proof of soundness, completeness, and boundedness' gives paper proofs for the hybrid barrier: Lemmas 2 and 3 (a white object reachable from a black object, or from a black goroutine, is grey-protected by a heap object), Theorem 1 (the hybrid write barrier satisfies the weak tricolor invariant) and Theorem 2 (marking terminates in a finite number of steps, bounded via the number of objects at the start of the cycle).
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsections 'Allocation colour' and 'Snapshot-at-the-beginning solutions'; Sec. 15.2 'Barrier techniques for concurrent collection' (pp. 337-344), subsection 'Black mutator techniques'.
- Gammie, Hosking, Engelhardt. Relaxing safely: verified on-the-fly garbage collection for x86-TSO. PLDI 2015, pp. 99-109. doi:10.1145/2737924.2738006. Isabelle/HOL development: Archive of Formal Proofs, entry ConcurrentGC (2015), https://isa-afp.org/entries/ConcurrentGC.html (a safety proof of a Schism-style collector on x86-TSO; no termination proof). Defines reachable_snapshot_inv (every reachable object is black or grey protected, via in_snapshot) and proves reachable_blackD (no grey references, reachable_snapshot_inv and reachability imply black), with lemmas including reachable_snapshot_inv_load (root loads) and reachable_snapshot_inv_alloc (allocation).

**Design question.** Which invariant does the deletion barrier maintain, and what root, load and allocation discipline does it need?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`yuasa-nonwhite-alloc-preserves-weak-and-roots-protected`).

#### `yuasa-barrier-breaks-strong`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** The Yuasa barrier does not preserve the strong invariant: in the 3-object state sChainR (black root 0, grey 1, white root 2, edges 0 -> 1 -> 2), which satisfies the strong invariant and the root clause, the enabled Yuasa store of the held pointer 2 into 0 creates a black-to-white edge while the weak invariant and its root clause still hold.
- **Tier justification (prose):** Standard observation (also stated for the hybrid barrier by Clements and Hudson).

**Lean statement** (`store_yuasa_breaks_strong`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:72-79
/-- **The Yuasa barrier does not preserve the strong invariant** (it preserves the weak one):
from a strong state with a grey-protected white root, the same store under the Yuasa barrier
creates a black-to-white edge. -/
theorem store_yuasa_breaks_strong :
    cfgY.barrier = .yuasa ∧ Strong sChainR ∧ RootsProtected sChainR ∧
      Step cfgY sChainR (store .yuasa sChainR 0 2) ∧
      ¬ Strong (store .yuasa sChainR 0 2) ∧
      Weak (store .yuasa sChainR 0 2) ∧ RootsProtected (store .yuasa sChainR 0 2) := by
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity (prose):** The statement is a closed concrete instance.

**Positive control** (a nearby setting in which the failure does not occur), verbatim:

`strong_preserved_of_dijkstra_nonvacuous`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:586-587
theorem strong_preserved_of_dijkstra_nonvacuous :
    cfgD.barrier = .dijkstra ∧ Strong sChainR ∧ Step cfgD sChainR (store .dijkstra sChainR 0 2) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). Proposes the hybrid barrier 'shade(*slot); if current stack is grey: shade(ptr)', which requires black allocation and maintains the weak but not the strong invariant.
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsection 'The strong and weak tricolour invariants'.

**Design question.** Which invariant does the deletion barrier maintain? (reference point)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`yuasa-barrier-breaks-strong`).

#### `isolated-alloc-preserves-roots-protected-iff-nonwhite`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** If every white root is grey protected and object a is isolated, then allocating a into the roots with color c keeps every white root grey protected if and only if c is not white.
- **Tier justification (prose):** Allocation colour is a textbook topic (Handbook Sec. 15.1 'Allocation colour'); the exact condition for a collector that never rescans roots is stated here as an equivalence.

**Lean statement** (`rootsProtected_alloc_iff_ne_white`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Preservation.lean:374-377
/-- **Allocation color under the weak invariant.** Allocating an isolated object into the roots
preserves the root clause exactly when the allocation color is non-white. -/
theorem rootsProtected_alloc_iff_ne_white {s : St n} (hr : RootsProtected s) {a : Fin n}
    (hiso : Isolated s a) (c : Color) : RootsProtected (alloc s a c) ↔ c ≠ .white := by
```

Unfolded statement of `rootsProtected_alloc_iff_ne_white` (a Lean term with `RootsProtected` and `Isolated` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
(∀ r, s.root r = true → s.color r = .white → GreyProtected s r) → ∀ {a : Fin n},
  (∀ v, s.edge a v = false ∧ s.edge v a = false) → ∀ (c : Color),
  ((∀ r, (alloc s a c).root r = true → (alloc s a c).color r = .white →
      GreyProtected (alloc s a c) r) ↔ c ≠ .white)
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hr : RootsProtected s` | Other roots must already be protected; otherwise no allocation color helps. | tight | `isolated_and_not_rootsProtected_alloc_black` | a 2-object heap state |
| `hiso : Isolated s a` | A non-isolated object could be protected by a grey predecessor even if allocated white. | tight | `rootsProtected_alloc_white_of_not_isolated` | a 2-object heap state |

Counterexample statements (verbatim):

`isolated_and_not_rootsProtected_alloc_black`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:21-27
/-- The premise `RootsProtected s` of the allocation-color characterization cannot be dropped
(a 2-object state): with
an unprotected white root already present, black allocation does not yield
`RootsProtected`. -/
theorem isolated_and_not_rootsProtected_alloc_black :
    Isolated sWhiteRootFree 1 ∧ (Color.black ≠ .white) ∧
      ¬ RootsProtected (alloc sWhiteRootFree 1 .black) := by
```

`rootsProtected_alloc_white_of_not_isolated`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:36-41
/-- Isolation cannot be dropped from the allocation-color characterization (a 2-object state):
an object reached from a
grey object can be "allocated" white into the roots and stay grey protected. -/
theorem rootsProtected_alloc_white_of_not_isolated :
    RootsProtected sGreyToOne ∧ ¬ Isolated sGreyToOne 1 ∧
      RootsProtected (alloc sGreyToOne 1 .white) := by
```

**Non-vacuity witness (prose):** sFree (black root 0, isolated white 1) with a = 1.

`rootsProtected_alloc_iff_ne_white_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:605-606
theorem rootsProtected_alloc_iff_ne_white_nonvacuous :
    RootsProtected sFree ∧ Isolated sFree 1 :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsection 'Allocation colour'; Chapter 16 'Concurrent mark-sweep' (pp. 349-366), Sec. 16.3 'Allocation'.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). States that the hybrid barrier requires black allocation ('allocate-white is a common policy, but incompatible with this barrier').

**Design question.** Which allocation color does a snapshot (no rescan) collector need?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`isolated-alloc-preserves-roots-protected-iff-nonwhite`).

#### `shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every configuration with shaded root loads (a load barrier) and an allocator that never allocates white, under any heap barrier including none, every state s satisfying the strong invariant in which every root is non-white, and every successor s' of s under the generated step relation `Step cfg` (an enabled collector scan of a grey object, heap store of a pointer held in the roots, erase, root load of an object reachable from the roots, root drop, or allocation of an isolated non-root object), the strong invariant holds in s' and every root of s' is non-white.
- **Tier justification (prose):** Black-mutator discipline with a load barrier (Handbook Sec. 15.2 'Black mutator techniques' and 'Load barriers'; Pirinen's result as quoted by Clements and Hudson that every black-mutator barrier other than Yuasa's requires a read barrier), restated: the load barrier alone suffices, with no heap write barrier.

**Lean statement** (`strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Preservation.lean:453-460
/-- **Load-barrier (black mutator) soundness, under any heap barrier.** With shaded root loads
and an allocator that never allocates white, every enabled step preserves the strong invariant
together with `RootsNonWhite`, whatever the heap barrier is (including none): a heap store writes
a pointer held in the roots, which `RootsNonWhite` keeps non-white. -/
theorem strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc {cfg : Config}
    (hsh : cfg.shadeLoads = true) (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white)
    {s s' : St n} (hs : Strong s) (hr : RootsNonWhite s) (hstep : Step cfg s s') :
    Strong s' ∧ RootsNonWhite s' := by
```

Unfolded statement of `strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc` (a Lean term with `Strong`, `RootsNonWhite` and `Step` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
cfg.shadeLoads = true → (∀ c, cfg.allocOk c = true → c ≠ .white) → ∀ {s s' : St n},
  (∀ x y, s.edge x y = true → s.color x = .black → s.color y ≠ .white) →
  (∀ r, s.root r = true → s.color r ≠ .white) →
  (∃ op : Op n, op.Enabled cfg s ∧ s' = op.apply cfg s) →
  (∀ x y, s'.edge x y = true → s'.color x = .black → s'.color y ≠ .white) ∧
    (∀ r, s'.root r = true → s'.color r ≠ .white)
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hsh : cfg.shadeLoads = true` | A loaded white object would be a white root. | tight | `unshadedLoad_breaks_rootsNonWhite` | a 3-object heap state and one step |
| `halloc : ∀ c, cfg.allocOk c = true → c ≠ .white` | A white allocation would be a white root. | tight | `shadeLoads_whiteAlloc_breaks_rootsNonWhite` | a 2-object heap state and one step |
| `hs : Strong s` | Invariant in the pre-state. | tight | `shadeLoads_step_from_nonStrong_not_strong` | a 2-object heap state and one step |
| `hr : RootsNonWhite s` | A white root stored into a black object (no heap barrier) is a black-to-white edge. | tight | `shadeLoads_store_of_whiteRoot_breaks_strong` | a 2-object heap state and one step |
| `hstep : Step cfg s s'` | The transition is an enabled step. Load-bearing parts: a heap store writes a pointer held in the roots, and an allocation takes an isolated object. | tight | `shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong`, `shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong` | a 3-object heap state and one non-enabled step |

Counterexample statements (verbatim):

`unshadedLoad_breaks_rootsNonWhite`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:74-80
/-- Shaded loads cannot be dropped from load-barrier preservation (a 3-object state and one
step): loading a white live object into the roots
without shading it breaks `RootsNonWhite` (here without a heap barrier). -/
theorem unshadedLoad_breaks_rootsNonWhite :
    cfgN0.shadeLoads = false ∧ (∀ c, cfgN0.allocOk c = true → c ≠ .white) ∧
      Strong sChain ∧ RootsNonWhite sChain ∧ Step cfgN0 sChain (load false sChain 2) ∧
      ¬ RootsNonWhite (load false sChain 2) :=
```

`shadeLoads_whiteAlloc_breaks_rootsNonWhite`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:83-88
/-- Non-white allocation cannot be dropped from load-barrier preservation (a 2-object state and
one step). -/
theorem shadeLoads_whiteAlloc_breaks_rootsNonWhite :
    cfgDW.shadeLoads = true ∧ cfgDW.allocOk .white = true ∧
      Strong sFree ∧ RootsNonWhite sFree ∧ Step cfgDW sFree (alloc sFree 1 .white) ∧
      ¬ RootsNonWhite (alloc sFree 1 .white) :=
```

`shadeLoads_step_from_nonStrong_not_strong`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:91-96
/-- The strong invariant in the pre-state cannot be dropped from load-barrier preservation (a
2-object state and one step). -/
theorem shadeLoads_step_from_nonStrong_not_strong :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      ¬ Strong sBlackWhite ∧ RootsNonWhite sBlackWhite ∧
      Step cfgU sBlackWhite (drop sBlackWhite 0) ∧ ¬ Strong (drop sBlackWhite 0) :=
```

`shadeLoads_store_of_whiteRoot_breaks_strong`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:535-542
/-- `RootsNonWhite` in the pre-state cannot be dropped from load-barrier preservation (a
2-object state): storing a white root into
a black object (no heap barrier) breaks the strong invariant. -/
theorem shadeLoads_store_of_whiteRoot_breaks_strong :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Strong sWhiteRootUnprotected ∧ ¬ RootsNonWhite sWhiteRootUnprotected ∧
      Step cfgU sWhiteRootUnprotected (store .none sWhiteRootUnprotected 0 1) ∧
      ¬ Strong (store .none sWhiteRootUnprotected 0 1) :=
```

`shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:523-531
/-- The held-pointer condition on stores cannot be dropped from load-barrier preservation (a
3-object state): if the mutator
could store the live but unheld white object `2` into the black root `0` (bypassing the load
barrier), the strong invariant would break without a heap barrier. -/
theorem shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Strong sChain ∧ RootsNonWhite sChain ∧ Live sChain 2 ∧
      ¬ (Op.store 0 2).Enabled cfgU sChain ∧
      ¬ Strong ((Op.store 0 2).apply cfgU sChain) :=
```

`shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:511-519
/-- `Isolated s a` on allocation cannot be dropped from load-barrier preservation, even for
black allocation (a 3-object state):
an object allocated black with a pointer to a white object creates a black-to-white edge. -/
theorem shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Strong sChain ∧ RootsNonWhite sChain ∧ cfgU.allocOk .black = true ∧
      sChain.root 1 = false ∧ ¬ Isolated sChain 1 ∧
      ¬ (Op.alloc 1 .black).Enabled cfgU sChain ∧
      ¬ Strong ((Op.alloc 1 .black).apply cfgU sChain) :=
```

**Non-vacuity witness (prose):** sChainShaded (black root 0, grey 1, grey root 2) with an unbarriered store 0 -> 2 under cfgU (no heap barrier, shaded loads, black allocation).

`strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:597-602
/-- Non-vacuity of load-barrier preservation with no heap barrier, exercising a store of a
pointer that was shaded when loaded. -/
theorem strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc_nonvacuous :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧
      (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧ Strong sChainShaded ∧
      RootsNonWhite sChainShaded ∧ Step cfgU sChainShaded (store .none sChainShaded 0 2) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Sec. 15.2 'Barrier techniques for concurrent collection' (pp. 337-344), subsections 'Black mutator techniques', 'Completeness of barrier techniques' and 'Load barriers'.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). Quotes Pirinen's result: 'as shown by Pirinen, all possible black mutator barriers other than the Yuasa barrier require a read barrier [Pirinen '98]'.
- Pirinen. Barrier techniques for incremental tracing. ISMM 1998, pp. 20-25. doi:10.1145/286860.286863. Cited by Clements and Hudson (2016) for the result that every black-mutator barrier other than the Yuasa barrier requires a read barrier.

**Design question.** What lets a collector skip both the root rescan and the heap write barrier?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots`).

### Whole marking cycles

#### `yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every configuration with the Yuasa barrier and an allocator that never allocates white, every initial state s₀, and every state s reached from initMark s₀ (every root shaded at once and every other object white: a stop-the-world root snapshot) by a run of the generated relation `Run cfg` (a finite sequence of enabled steps: collector scans of grey objects, heap stores of pointers held in the roots, erases, root loads of objects reachable from the roots, root drops, and allocations of isolated non-root objects), if s has no grey object then every object reachable from the roots in s is black, without a root rescan or shading of root loads.
- **Tier justification (prose):** Whole-cycle safety of snapshot-at-the-beginning marking started by an atomic root snapshot, with no rescan, unshaded root loads and non-white allocation (Yuasa's collector snapshots the stack at the start of marking; Clements and Hudson state that the Yuasa barrier needs the stacks scanned or snapshotted at the start).

**Lean statement** (`allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Marking.lean:55-65
/-- **Yuasa marking safety (non-white allocation, root snapshot).** With the Yuasa barrier and
an allocator that never allocates white, any run of `Run cfg` from the start of a marking cycle
(`initMark`: every root shaded at once) that reaches a state with no grey object ends with every
live object black. `Run` admits only enabled steps: heap stores of pointers held in the roots,
root loads of live objects and allocations of isolated non-root objects (dropping isolation:
`yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack`). There is no hypothesis on
root-load shading and no root rescan. -/
theorem allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark {cfg : Config}
    (hb : cfg.barrier = .yuasa)
    (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white) {s₀ s : St n} {ops : List (Op n)}
    (hrun : Run cfg (initMark s₀) ops s) (hng : NoGrey s) : AllLiveBlack s := by
```

Unfolded statement of `allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark` (a Lean term with `NoGrey` and `AllLiveBlack` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
cfg.barrier = .yuasa → (∀ c, cfg.allocOk c = true → c ≠ .white) →
  ∀ {s₀ s : St n} {ops : List (Op n)}, Run cfg (initMark s₀) ops s →
  (∀ x, s.color x ≠ .grey) → ∀ y, Live s y → s.color y = .black
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : cfg.barrier = .yuasa` | Deletion barrier. | tight | `unbarriered_unshadedLoads_blackAlloc_run_from_initMark_not_allLiveBlack`, `dijkstra_unshadedLoads_run_from_initMark_leaves_live_white` | a 3-object heap and a 4- or 6-step run |
| `halloc : ∀ c, cfg.allocOk c = true → c ≠ .white` | Non-white allocation. | tight | `yuasa_whiteAlloc_run_from_initMark_not_allLiveBlack` | a 2-object heap and a 2-step run |
| `hrun : Run cfg (initMark s₀) ops s` | The run consists of enabled steps of `Run cfg` and starts at a root snapshot initMark s₀. Load-bearing enabling conditions inside `Run`: a heap store writes a pointer held in the roots (liveness of the stored object suffices, as in the Yuasa preservation card), a root load takes an object reachable from the roots, and an allocation takes an isolated non-root object (`Isolated s a`); dropping any one of them, with every other step enabled, leaves a reachable object white at the end of marking. | tight | `yuasa_run_not_from_initMark_not_allLiveBlack`, `yuasa_store_of_unreachable_cycle_not_allLiveBlack`, `yuasa_load_of_unreachable_cycle_not_allLiveBlack`, `yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack` | an empty run from a 2-object state that is not of the form initMark s₀; or a 2-step sequence from a 2- or 3-object root snapshot in which exactly one step violates exactly one enabling condition (stored object live; loaded object reachable; isolation of an allocation) |
| `hng : NoGrey s` | Marking has terminated. | tight | `yuasa_run_from_initMark_with_grey_not_allLiveBlack` | an empty run from a 3-object root snapshot |

Counterexample statements (verbatim):

`unbarriered_unshadedLoads_blackAlloc_run_from_initMark_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:299-303
/-- The barrier hypothesis of Yuasa marking safety cannot be dropped (a 3-object heap and a
6-step run; no barrier, unshaded loads, black-only allocation). -/
theorem unbarriered_unshadedLoads_blackAlloc_run_from_initMark_not_allLiveBlack :
    cfgN0.barrier ≠ .yuasa ∧ (∀ c, cfgN0.allocOk c = true → c ≠ .white) ∧
      Run cfgN0 (initMark hChain) traceLostObject sLost ∧ NoGrey sLost ∧ ¬ AllLiveBlack sLost :=
```

`dijkstra_unshadedLoads_run_from_initMark_leaves_live_white`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:337-345
/-- **Unshaded root loads defeat Dijkstra marking without a rescan, even with black
allocation.** Under the Dijkstra barrier with unshaded loads and black-only allocation, the
interleaving `traceLoadLost` from the start of a marking cycle on the heap `0 (root) → 1 → 2`
reaches a state with no grey object in which the live root `2` is white. -/
theorem dijkstra_unshadedLoads_run_from_initMark_leaves_live_white :
    cfgD0.barrier = .dijkstra ∧ cfgD0.shadeLoads = false ∧
      (∀ c, cfgD0.allocOk c = true → c ≠ .white) ∧
      Run cfgD0 (initMark hChain) traceLoadLost sLoadLost ∧ NoGrey sLoadLost ∧
      Live sLoadLost 2 ∧ sLoadLost.color 2 = .white :=
```

`yuasa_whiteAlloc_run_from_initMark_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:435-440
/-- The allocation-color hypothesis of Yuasa marking safety cannot be dropped (a 2-object heap
and a 2-step run). -/
theorem yuasa_whiteAlloc_run_from_initMark_not_allLiveBlack :
    cfgYW.barrier = .yuasa ∧ cfgYW.allocOk .white = true ∧
      Run cfgYW (initMark hAlloc) traceWhiteAlloc sWhiteAllocY ∧ NoGrey sWhiteAllocY ∧
      ¬ AllLiveBlack sWhiteAllocY :=
```

`yuasa_run_not_from_initMark_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:451-457
/-- The start at `initMark` cannot be dropped from Yuasa marking safety (a 2-object state):
all other hypotheses hold for an
empty run from a black-to-white state that is not of the form `initMark s₀`. -/
theorem yuasa_run_not_from_initMark_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      (∀ s₀, sBlackWhite ≠ initMark s₀) ∧
      Run cfgY sBlackWhite [] sBlackWhite ∧ NoGrey sBlackWhite ∧ ¬ AllLiveBlack sBlackWhite :=
```

`yuasa_store_of_unreachable_cycle_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:789-799
/-- The condition on stored pointers inside `Run` cannot be dropped from Yuasa marking safety (a
2-object root snapshot and a 2-step sequence): after the scan of the root `0`, storing the
unreachable white object `1` into `0` is the only non-enabled step, and the final state has no
grey object while the reachable object `1` is white. -/
theorem yuasa_store_of_unreachable_cycle_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Run cfgY (initMark hAlloc) [.scan 0] (runOps cfgY [.scan 0] (initMark hAlloc)) ∧
      ¬ Live (runOps cfgY [.scan 0] (initMark hAlloc)) 1 ∧
      (∀ s, ¬ Run cfgY (initMark hAlloc) [.scan 0, .store 0 1] s) ∧
      NoGrey (runOps cfgY [.scan 0, .store 0 1] (initMark hAlloc)) ∧
      ¬ AllLiveBlack (runOps cfgY [.scan 0, .store 0 1] (initMark hAlloc)) := by
```

`yuasa_load_of_unreachable_cycle_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:769-780
/-- The liveness condition on root loads inside `Run` cannot be dropped from Yuasa marking safety
(a 2-object root snapshot and a 2-step sequence): loading the unreachable white object `1`
(unshaded) is the only non-enabled step, and after the scan of the root `0` no object is grey
while the root `1` is white. -/
theorem yuasa_load_of_unreachable_cycle_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      ¬ Live (initMark hAlloc) 1 ∧
      Run cfgY (runOps cfgY [.load 1] (initMark hAlloc)) [.scan 0]
        (runOps cfgY [.load 1, .scan 0] (initMark hAlloc)) ∧
      (∀ s, ¬ Run cfgY (initMark hAlloc) [.load 1, .scan 0] s) ∧
      NoGrey (runOps cfgY [.load 1, .scan 0] (initMark hAlloc)) ∧
      ¬ AllLiveBlack (runOps cfgY [.load 1, .scan 0] (initMark hAlloc)) := by
```

`yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:709-720
/-- `Isolated s a` on allocation inside `Run` cannot be dropped from Yuasa marking safety, even
for black allocation (a 3-object root snapshot and a 2-step sequence): the scan of `0` is a run from the root snapshot, the allocation of `1` satisfies
every enabling condition except isolation, and the final state has no grey object while the
reachable object `2` is white. -/
theorem yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Run cfgY (initMark hChain) [.scan 0] (runOps cfgY [.scan 0] (initMark hChain)) ∧
      cfgY.allocOk .black = true ∧ (runOps cfgY [.scan 0] (initMark hChain)).root 1 = false ∧
      ¬ Isolated (runOps cfgY [.scan 0] (initMark hChain)) 1 ∧
      (∀ s, ¬ Run cfgY (initMark hChain) traceUnisolatedBlackAlloc s) ∧
      NoGrey (runOps cfgY traceUnisolatedBlackAlloc (initMark hChain)) ∧
      ¬ AllLiveBlack (runOps cfgY traceUnisolatedBlackAlloc (initMark hChain)) := by
```

`yuasa_run_from_initMark_with_grey_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:121-125
/-- `NoGrey` at the end of the run cannot be dropped from Yuasa marking safety (an empty run
from a 3-object root snapshot). -/
theorem yuasa_run_from_initMark_with_grey_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Run cfgY (initMark hChain) [] (initMark hChain) ∧ ¬ AllLiveBlack (initMark hChain) :=
```

**Non-vacuity witness (prose):** The lost-object interleaving traceLostObject under the Yuasa barrier, followed by a scan of object 2.

`allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:609-613
theorem allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark_nonvacuous :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Run cfgY (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Yuasa. Real-time garbage collection on general-purpose machines. J. Syst. Softw. 11(3):181-198, 1990. doi:10.1016/0164-1212(90)90084-Y. The deletion (snapshot-at-the-beginning) barrier; as described by Clements and Hudson (2016), 'As originally proposed, the Yuasa barrier takes a complete snapshot of the stack before proceeding with marking.' The weak-invariant formulation used here is Pirinen's (1998), not Yuasa's.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). On the deletion barrier: 'The Yuasa barrier requires a STW at the beginning of marking to either scan or snapshot stacks'; 'It's sufficient to ensure all stacks are black before scanning any heap objects.' Proposes the hybrid barrier 'shade(*slot); if current stack is grey: shade(ptr)', which requires black allocation and maintains the weak but not the strong invariant. Its appendix 'Proof of soundness, completeness, and boundedness' gives paper proofs for the hybrid barrier: Lemmas 2 and 3 (a white object reachable from a black object, or from a black goroutine, is grey-protected by a heap object), Theorem 1 (the hybrid write barrier satisfies the weak tricolor invariant) and Theorem 2 (marking terminates in a finite number of steps, bounded via the number of objects at the start of the cycle).
- Pirinen. Barrier techniques for incremental tracing. ISMM 1998, pp. 20-25. doi:10.1145/286860.286863. Source of the weak tricolor invariant as quoted in Clements and Hudson (2016).
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsection 'Snapshot-at-the-beginning solutions'; Chapter 16 'Concurrent mark-sweep' (pp. 349-366), Sec. 16.1 'Initialisation'.
- Gammie, Hosking, Engelhardt. Relaxing safely: verified on-the-fly garbage collection for x86-TSO. PLDI 2015, pp. 99-109. doi:10.1145/2737924.2738006. Isabelle/HOL development: Archive of Formal Proofs, entry ConcurrentGC (2015), https://isa-afp.org/entries/ConcurrentGC.html (a safety proof of a Schism-style collector on x86-TSO; no termination proof). Defines reachable_snapshot_inv (every reachable object is black or grey protected, via in_snapshot) and proves reachable_blackD (no grey references, reachable_snapshot_inv and reachability imply black), with lemmas including reachable_snapshot_inv_load (root loads) and reachable_snapshot_inv_alloc (allocation).

**Design question.** Is a snapshot collector without root rescans safe, and under which allocation rule?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge), a separate claim connecting the theorem to a collector that sweeps (sweeping is not part of the model; not a theorem). Reasoning: A sweep that frees exactly the white objects of a state satisfying the conclusion frees no object reachable from the roots; sweeping is not modeled.

Non-claims: see **Boundaries → Non-claims** (`yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`).

#### `no-barrier-unshaded-loads-leaves-live-white`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** On the heap 0 (root) -> 1 -> 2, starting from the root snapshot initMark (0 grey, 1 and 2 white), under every configuration with no heap barrier and unshaded root loads, the enabled interleaving 'scan 0; load 2 into the roots; store 2 into the black root 0; drop 2 from the roots; erase 1 -> 2; scan 1' reaches a state with no grey object in which object 2 is reachable (through the edge 0 -> 2) and white.
- **Tier justification (prose):** The classic lost-object interleaving (Handbook Sec. 15.1 'The lost object problem'), in a model with registers.

**Lean statement** (`unbarriered_unshadedLoads_traceLostObject_leaves_live_white`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:201-210
/-- **No heap barrier and unshaded root loads are unsound.** Under any configuration without a
heap barrier and without load shading, the enabled interleaving `traceLostObject` from the start
of a marking cycle on the heap `0 (root) → 1 → 2` reaches a state with no grey object in which
the object `2` is live (through the edge `0 → 2` from the black root) and white. -/
theorem unbarriered_unshadedLoads_traceLostObject_leaves_live_white (cfg : Config)
    (hb : cfg.barrier = .none) (hsh : cfg.shadeLoads = false) :
    Run cfg (initMark hChain) traceLostObject (runOps cfg traceLostObject (initMark hChain)) ∧
      NoGrey (runOps cfg traceLostObject (initMark hChain)) ∧
      Live (runOps cfg traceLostObject (initMark hChain)) 2 ∧
      (runOps cfg traceLostObject (initMark hChain)).color 2 = .white := by
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : cfg.barrier = .none` | No heap barrier. | tight | `traceLostObject_dijkstra_unshadedLoads_not_lost`, `traceLostObject_yuasa_unshadedLoads_not_lost` | the same 3-object heap and 6-step trace under another configuration |
| `hsh : cfg.shadeLoads = false` | No load barrier. | tight | `traceLostObject_unbarriered_shadeLoads_not_lost` | the same 3-object heap and 6-step trace under another configuration |

Counterexample statements (verbatim):

`traceLostObject_dijkstra_unshadedLoads_not_lost`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:241-249
/-- The heap-barrier hypothesis of `unbarriered_unshadedLoads_traceLostObject_leaves_live_white`
cannot be dropped from that counterexample: with unshaded loads and the Dijkstra barrier the
same 3-object, 6-step trace ends with `2` grey. -/
theorem traceLostObject_dijkstra_unshadedLoads_not_lost :
    cfgD0.shadeLoads = false ∧ cfgD0.barrier ≠ .none ∧
      ¬ (Run cfgD0 (initMark hChain) traceLostObject (runOps cfgD0 traceLostObject (initMark hChain)) ∧
        NoGrey (runOps cfgD0 traceLostObject (initMark hChain)) ∧
        Live (runOps cfgD0 traceLostObject (initMark hChain)) 2 ∧
        (runOps cfgD0 traceLostObject (initMark hChain)).color 2 = .white) :=
```

`traceLostObject_yuasa_unshadedLoads_not_lost`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:252-258
/-- The same with unshaded loads and the Yuasa barrier. -/
theorem traceLostObject_yuasa_unshadedLoads_not_lost :
    cfgY.shadeLoads = false ∧ cfgY.barrier ≠ .none ∧
      ¬ (Run cfgY (initMark hChain) traceLostObject (runOps cfgY traceLostObject (initMark hChain)) ∧
        NoGrey (runOps cfgY traceLostObject (initMark hChain)) ∧
        Live (runOps cfgY traceLostObject (initMark hChain)) 2 ∧
        (runOps cfgY traceLostObject (initMark hChain)).color 2 = .white) :=
```

`traceLostObject_unbarriered_shadeLoads_not_lost`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:261-268
/-- The unshaded-loads hypothesis of the lost-object counterexample cannot be dropped: without a
heap barrier but with shaded loads the same 3-object, 6-step trace ends with `2` grey. -/
theorem traceLostObject_unbarriered_shadeLoads_not_lost :
    cfgU.barrier = .none ∧ cfgU.shadeLoads ≠ false ∧
      ¬ (Run cfgU (initMark hChain) traceLostObject (runOps cfgU traceLostObject (initMark hChain)) ∧
        NoGrey (runOps cfgU traceLostObject (initMark hChain)) ∧
        Live (runOps cfgU traceLostObject (initMark hChain)) 2 ∧
        (runOps cfgU traceLostObject (initMark hChain)).color 2 = .white) :=
```

**Non-vacuity (prose):** The trace is concrete; every step is enabled (2 is reachable when loaded and held in the roots when stored).

The hypotheses `hb` and `hsh` hold for the configuration `cfgN0` (no heap barrier, unshaded root loads, black-only allocation) by its definition, quoted under **Findings → Definitions**; `sLost`, also quoted there, is by definition the final state of the trace under `cfgN0`.

**Positive control** (a nearby setting in which the failure does not occur), verbatim:

`dijkstra_traceLostObject_then_scan_safe`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:271-277
/-- Positive control: under the Dijkstra barrier (unshaded loads) the same interleaving,
followed by scanning the object the barrier greyed, ends with every live object black. -/
theorem dijkstra_traceLostObject_then_scan_safe :
    Run cfgD0 (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgD0 (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgD0 (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgD0 (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
```

`yuasa_traceLostObject_then_scan_safe`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:281-286
/-- Positive control: the same under the Yuasa barrier (unshaded loads). -/
theorem yuasa_traceLostObject_then_scan_safe :
    Run cfgY (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
```

`shadeLoads_traceLostObject_then_scan_safe`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:290-295
/-- Positive control: the same without any heap barrier but with shaded loads. -/
theorem shadeLoads_traceLostObject_then_scan_safe :
    Run cfgU (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsection 'The lost object problem'.

**Design question.** What goes wrong with neither a heap write barrier nor a load barrier?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge), a separate claim connecting the theorem to a collector that sweeps (sweeping is not part of the model; not a theorem). Reasoning: A sweep that frees the white objects of the final state would free the reachable object; sweeping is not modeled.

Non-claims: see **Boundaries → Non-claims** (`no-barrier-unshaded-loads-leaves-live-white`).

#### `dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every configuration with the Dijkstra barrier (any allocation colors, either root-load discipline), every initial state s₀, every state s reached from initMark s₀ by a run of the generated relation `Run cfg` (a finite sequence of enabled steps: collector scans of grey objects, heap stores of pointers held in the roots, erases, root loads of objects reachable from the roots, root drops, and allocations of isolated non-root objects), and every state s' reached from rescan s (every white root greyed) by a run of `Run cfg` consisting only of collector scans (`ScansOnly`: the mutator is paused), if s' has no grey object then every object reachable from the roots in s' is black.
- **Tier justification (prose):** The grey-mutator discipline (Go 1.7 with stop-the-world stack re-scanning; Handbook 'Grey mutator techniques') restated: the rescan lemma allLiveBlack_of_strong_of_rescan_of_scansOnly_run (strong invariant in s, a scans-only run of `Run cfg` from rescan s to s', no grey object in s') combined with preservation of the strong invariant by every enabled step under the Dijkstra barrier along the run of `Run cfg` from initMark s₀ to s.

**Lean statement** (`allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Marking.lean:80-90
/-- **Dijkstra marking with a final rescan and a paused drain, for every allocation color.**
With the Dijkstra barrier (any root-load discipline, any allocation colors), a concurrent run of
`Run cfg` from the start of a marking cycle (enabled steps only; allocations take isolated
non-root objects, and dropping isolation fails:
`dijkstra_unisolated_alloc_cycle_rescan_not_allLiveBlack`) followed by a root rescan and a
scans-only run of `Run cfg` that reaches a state with no grey object ends with every live
object black. -/
theorem allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run {cfg : Config}
    (hb : cfg.barrier = .dijkstra) {s₀ s s' : St n} {ops ops₂ : List (Op n)}
    (hrun : Run cfg (initMark s₀) ops s) (hrem : Run cfg (rescan s) ops₂ s')
    (hscan : ScansOnly ops₂) (hng : NoGrey s') : AllLiveBlack s' :=
```

Unfolded statement of `allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run` (a Lean term with `ScansOnly`, `NoGrey` and `AllLiveBlack` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
cfg.barrier = .dijkstra → ∀ {s₀ s s' : St n} {ops ops₂ : List (Op n)},
  Run cfg (initMark s₀) ops s → Run cfg (rescan s) ops₂ s' →
  (∀ op ∈ ops₂, op.isScan = true) → (∀ x, s'.color x ≠ .grey) →
  ∀ y, Live s' y → s'.color y = .black
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : cfg.barrier = .dijkstra` | Keeps the strong invariant during the concurrent run. | tight | `unbarriered_run_rescan_not_allLiveBlack` | a 3-object heap, a 6-step run and an empty drain |
| `hrun : Run cfg (initMark s₀) ops s` | The concurrent run consists of enabled steps of `Run cfg` and starts at a root snapshot initMark s₀. Load-bearing enabling condition inside `Run`: an allocation takes an isolated non-root object (`Isolated s a`); dropping it, with every other step enabled, leaves a reachable object white even after the rescan and drain. The store and load conditions are not used (the Dijkstra preservation lemmas strong_store_dijkstra and strong_load hold for every target). | tight | `rescan_from_nonStrong_not_allLiveBlack`, `dijkstra_unisolated_alloc_cycle_rescan_not_allLiveBlack` | a 2-object state not reachable from any initMark s₀; or a 2-step sequence from a 3-object root snapshot whose allocation is not isolated, followed by a rescan and an empty drain |
| `hrem : Run cfg (rescan s) ops₂ s'` | The drain starts after the rescan. | tight | `dijkstra_run_without_rescan_scansOnly_not_allLiveBlack` | a 3-object heap, a 4-step run and an empty drain without rescan |
| `hscan : ScansOnly ops₂` | The drain is collector-only (mutator paused). | tight | `dijkstra_rescan_then_mutator_not_allLiveBlack` | a 3-object heap and a 3-step drain with mutator steps |
| `hng : NoGrey s'` | The drain has finished. | tight | `dijkstra_rescan_with_grey_not_allLiveBlack` | a 3-object root snapshot and an empty drain |

Counterexample statements (verbatim):

`unbarriered_run_rescan_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:306-313
/-- The barrier hypothesis of Dijkstra marking with a final rescan cannot be dropped (a
3-object heap, a 6-step run and an empty drain): without a barrier
(and without load shading) the rescan finds no white root, the drain is empty, and the live
object `2` is still white. -/
theorem unbarriered_run_rescan_not_allLiveBlack :
    cfgN0.barrier ≠ .dijkstra ∧ Run cfgN0 (initMark hChain) traceLostObject sLost ∧
      Run cfgN0 (rescan sLost) [] (rescan sLost) ∧ ScansOnly ([] : List (Op 3)) ∧
      NoGrey (rescan sLost) ∧ ¬ AllLiveBlack (rescan sLost) := by
```

`rescan_from_nonStrong_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:470-475
/-- The start at `initMark` cannot be dropped from the rescan theorem under the Dijkstra
barrier (a 2-object state): a black-to-white state is not reachable that way, and rescanning it is not enough. -/
theorem rescan_from_nonStrong_not_allLiveBlack :
    cfgD.barrier = .dijkstra ∧ (∀ s₀ ops, ¬ Run cfgD (initMark s₀) ops sBlackWhite) ∧
      Run cfgD (rescan sBlackWhite) [] (rescan sBlackWhite) ∧ ScansOnly ([] : List (Op 2)) ∧
      NoGrey (rescan sBlackWhite) ∧ ¬ AllLiveBlack (rescan sBlackWhite) := by
```

`dijkstra_unisolated_alloc_cycle_rescan_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:726-741
/-- `Isolated s a` on allocation inside the concurrent `Run` cannot be dropped from Dijkstra
marking with a final rescan (a 3-object root snapshot, a 2-step sequence and an empty drain): the scan of `0` is a run from the root snapshot, the black allocation of `1`
satisfies every enabling condition except isolation, and after the rescan (both roots are
already black) the empty drain ends with no grey object while the reachable object `2` is
white. -/
theorem dijkstra_unisolated_alloc_cycle_rescan_not_allLiveBlack :
    cfgD.barrier = .dijkstra ∧
      Run cfgD (initMark hChain) [.scan 0] (runOps cfgD [.scan 0] (initMark hChain)) ∧
      cfgD.allocOk .black = true ∧ (runOps cfgD [.scan 0] (initMark hChain)).root 1 = false ∧
      ¬ Isolated (runOps cfgD [.scan 0] (initMark hChain)) 1 ∧
      (∀ s, ¬ Run cfgD (initMark hChain) traceUnisolatedBlackAlloc s) ∧
      Run cfgD (rescan (runOps cfgD traceUnisolatedBlackAlloc (initMark hChain))) []
        (rescan (runOps cfgD traceUnisolatedBlackAlloc (initMark hChain))) ∧
      ScansOnly ([] : List (Op 3)) ∧
      NoGrey (rescan (runOps cfgD traceUnisolatedBlackAlloc (initMark hChain))) ∧
      ¬ AllLiveBlack (rescan (runOps cfgD traceUnisolatedBlackAlloc (initMark hChain))) := by
```

`dijkstra_run_without_rescan_scansOnly_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:368-374
/-- The rescan cannot be dropped from Dijkstra marking (a 3-object heap, a 4-step run with
unshaded loads, and an empty drain): the drain runs from the un-rescanned state. All other
hypotheses of the rescan theorem hold. -/
theorem dijkstra_run_without_rescan_scansOnly_not_allLiveBlack :
    cfgD0.barrier = .dijkstra ∧ Run cfgD0 (initMark hChain) traceLoadLost sLoadLost ∧
      Run cfgD0 sLoadLost [] sLoadLost ∧ ScansOnly ([] : List (Op 3)) ∧
      NoGrey sLoadLost ∧ ¬ AllLiveBlack sLoadLost :=
```

`dijkstra_rescan_then_mutator_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:384-389
/-- The drain after the remark must be collector-only: mutator steps between the rescan and
the end of marking can again hide a live white root. -/
theorem dijkstra_rescan_then_mutator_not_allLiveBlack :
    cfgD0.barrier = .dijkstra ∧ Run cfgD0 (initMark hChain) [.scan 0] sAfterScan0 ∧
      Run cfgD0 (rescan sAfterScan0) drainWithMutator sDrainLost ∧
      ¬ ScansOnly drainWithMutator ∧ NoGrey sDrainLost ∧ ¬ AllLiveBlack sDrainLost := by
```

`dijkstra_rescan_with_grey_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:396-400
/-- Before marking has finished, live objects may be white. -/
theorem dijkstra_rescan_with_grey_not_allLiveBlack :
    cfgD.barrier = .dijkstra ∧ Run cfgD (initMark hChain) [] (initMark hChain) ∧
      Run cfgD (rescan (initMark hChain)) [] (rescan (initMark hChain)) ∧
      ScansOnly ([] : List (Op 3)) ∧ ¬ AllLiveBlack (rescan (initMark hChain)) := by
```

**Non-vacuity witness (prose):** White allocation into the roots, scan of the root, rescan, scan of the allocated object.

`allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:617-621
theorem allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run_nonvacuous :
    cfgDW.barrier = .dijkstra ∧ cfgDW.allocOk .white = true ∧
      Run cfgDW (initMark hAlloc) traceWhiteAlloc sWhiteAlloc ∧
      Run cfgDW (rescan sWhiteAlloc) [.scan 1] (scan (rescan sWhiteAlloc) 1) ∧
      ScansOnly [(Op.scan 1 : Op 2)] ∧ NoGrey (scan (rescan sWhiteAlloc) 1) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). Describes Go 1.7's coarsened Dijkstra write barrier: stack writes have no barrier, so stacks must be 'permagrey' and are re-scanned 'with the world stopped'; it notes that 'Go already allocates black for other reasons'.
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Sec. 15.2 'Barrier techniques for concurrent collection' (pp. 337-344), subsection 'Grey mutator techniques'; Chapter 16 'Concurrent mark-sweep' (pp. 349-366), Sec. 16.2 'Termination'.
- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. The coarse-grained mutator shades the target of each edge it introduces. In the final fine-grained solution the mutator performs 'redirect for a reachable node an outgoing edge towards a reachable node' and 'shade the target of the edge just placed' as two separate indivisible subactions.
- Zakowski, Cachera, Demange, Petri, Pichardie, Jagannathan, Vitek. Verifying a concurrent garbage collector with a rely-guarantee methodology. J. Autom. Reason. 63(2):489-515, 2019. doi:10.1007/s10817-018-9489-x. Coq proof of a fully concurrent mark-and-sweep collector; its conference version (ITP 2017) states the main result as safety (no reference reachable from a mutator is on the free list).

**Design question.** What makes an insertion barrier safe for every allocation color and root-load discipline?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge), a separate claim connecting the theorem to a collector that sweeps (sweeping is not part of the model; not a theorem). Reasoning: A sweep that frees exactly the white objects of a state satisfying the conclusion frees no object reachable from the roots; sweeping is not modeled.

Non-claims: see **Boundaries → Non-claims** (`dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`).

#### `dijkstra-white-alloc-without-rescan-leaves-live-white`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** On the heap with root 0 and an isolated free object 1, starting from the root snapshot initMark (0 grey, 1 white), under the Dijkstra barrier with shaded root loads and white allocation allowed, the run 'allocate 1 white into the roots; scan 0' reaches a state with no grey object in which the root 1 is white.
- **Tier justification (prose):** Folklore (Handbook 'Allocation colour'; Clements and Hudson call white allocation incompatible with their no-rescan barrier).

**Lean statement** (`dijkstra_whiteAlloc_run_from_initMark_leaves_live_white`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:417-423
/-- **White allocation defeats Dijkstra marking without a rescan, even with shaded loads.**
On the heap `0 (root)`, `1` (isolated, free), allocating `1` white into the roots and scanning
the root reaches a state with no grey object in which the live root `1` is white. -/
theorem dijkstra_whiteAlloc_run_from_initMark_leaves_live_white :
    cfgDW.barrier = .dijkstra ∧ cfgDW.shadeLoads = true ∧ cfgDW.allocOk .white = true ∧
      Run cfgDW (initMark hAlloc) traceWhiteAlloc sWhiteAlloc ∧ NoGrey sWhiteAlloc ∧
      Live sWhiteAlloc 1 ∧ sWhiteAlloc.color 1 = .white :=
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity (prose):** Concrete two-step run.

**Positive control** (a nearby setting in which the failure does not occur), verbatim:

`dijkstra_whiteAlloc_then_rescan_safe`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:426-430
/-- Positive control: with a final rescan (then a scan of the greyed root) the same white
allocation is safe. -/
theorem dijkstra_whiteAlloc_then_rescan_safe :
    Run cfgDW (rescan sWhiteAlloc) [.scan 1] (scan (rescan sWhiteAlloc) 1) ∧
      NoGrey (scan (rescan sWhiteAlloc) 1) ∧ AllLiveBlack (scan (rescan sWhiteAlloc) 1) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 15 'Concurrent garbage collection' (from p. 329), Sec. 15.1 'Correctness of concurrent collection' (pp. 331-337), subsection 'Allocation colour'.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). States that allocate-white is incompatible with the hybrid barrier.

**Design question.** With an insertion barrier, when is allocating white safe?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge), a separate claim connecting the theorem to a collector that sweeps (sweeping is not part of the model; not a theorem). Reasoning: A sweep that frees the white objects of the final state would free the reachable object; sweeping is not modeled.

Non-claims: see **Boundaries → Non-claims** (`dijkstra-white-alloc-without-rescan-leaves-live-white`).

#### `dijkstra-unshaded-loads-without-rescan-leaves-live-white`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** On the heap 0 (root) -> 1 -> 2, starting from the root snapshot initMark, under the Dijkstra barrier with black-only allocation but unshaded root loads, the run 'scan 0; load 2 into the roots; erase 1 -> 2; scan 1' reaches a state with no grey object in which the root 2 is white.
- **Tier justification (prose):** The reason for 'permagrey' stacks and stop-the-world re-scanning in Clements and Hudson (Go already allocated black at the time); grey mutators under an insertion barrier need a rescan (Handbook 'Grey mutator techniques').

**Lean statement** (`dijkstra_unshadedLoads_run_from_initMark_leaves_live_white`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:337-345
/-- **Unshaded root loads defeat Dijkstra marking without a rescan, even with black
allocation.** Under the Dijkstra barrier with unshaded loads and black-only allocation, the
interleaving `traceLoadLost` from the start of a marking cycle on the heap `0 (root) → 1 → 2`
reaches a state with no grey object in which the live root `2` is white. -/
theorem dijkstra_unshadedLoads_run_from_initMark_leaves_live_white :
    cfgD0.barrier = .dijkstra ∧ cfgD0.shadeLoads = false ∧
      (∀ c, cfgD0.allocOk c = true → c ≠ .white) ∧
      Run cfgD0 (initMark hChain) traceLoadLost sLoadLost ∧ NoGrey sLoadLost ∧
      Live sLoadLost 2 ∧ sLoadLost.color 2 = .white :=
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity (prose):** Concrete four-step run.

**Positive control** (a nearby setting in which the failure does not occur), verbatim:

`dijkstra_shadeLoads_traceLoadLost_then_scan_safe`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:348-354
/-- Positive control: with shaded loads the same interleaving leaves `2` grey; scanning it
ends with every live object black. -/
theorem dijkstra_shadeLoads_traceLoadLost_then_scan_safe :
    Run cfgD (initMark hChain) (traceLoadLost ++ [.scan 2])
        (runOps cfgD (traceLoadLost ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgD (traceLoadLost ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgD (traceLoadLost ++ [.scan 2]) (initMark hChain)) :=
```

`yuasa_traceLoadLost_then_scan_safe`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:358-364
/-- Positive control: under the Yuasa barrier unshaded loads are harmless here (the erase
shades `2`). -/
theorem yuasa_traceLoadLost_then_scan_safe :
    Run cfgY (initMark hChain) (traceLoadLost ++ [.scan 2])
        (runOps cfgY (traceLoadLost ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgY (traceLoadLost ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgY (traceLoadLost ++ [.scan 2]) (initMark hChain)) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). Describes Go 1.7's coarsened Dijkstra write barrier: stack writes have no barrier, so stacks must be 'permagrey' and are re-scanned 'with the world stopped'; it notes that 'Go already allocates black for other reasons'.
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Sec. 15.2 'Barrier techniques for concurrent collection' (pp. 337-344), subsection 'Grey mutator techniques'.

**Design question.** With an insertion barrier, is black allocation enough to avoid a root rescan?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge), a separate claim connecting the theorem to a collector that sweeps (sweeping is not part of the model; not a theorem). Reasoning: A sweep that frees the white objects of the final state would free the reachable object; sweeping is not modeled.

Non-claims: see **Boundaries → Non-claims** (`dijkstra-unshaded-loads-without-rescan-leaves-live-white`).

#### `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every configuration with shaded root loads and an allocator that never allocates white, under any heap barrier including none, every initial state s₀, and every state s reached from initMark s₀ (a stop-the-world root snapshot) by a run of the generated relation `Run cfg` (a finite sequence of enabled steps: collector scans of grey objects, heap stores of pointers held in the roots, erases, root loads of objects reachable from the roots, root drops, and allocations of isolated non-root objects), if s has no grey object then every object reachable from the roots in s is black, without a root rescan.
- **Tier justification (prose):** Whole-cycle form of shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots.

**Lean statement** (`allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Marking.lean:94-104
/-- **Load-barrier marking without a rescan, under any heap barrier.** With shaded root loads
and an allocator that never allocates white (any heap barrier, including none), any run of
`Run cfg` from the start of a marking cycle that reaches a state with no grey object ends with
every live object black. `Run` admits only enabled steps; the load-bearing enabling conditions
are that heap stores write pointers held in the roots
(`shadeLoads_nonWhiteAlloc_unheld_store_cycle_not_allLiveBlack`) and that allocations take
isolated objects (`shadeLoads_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack`). -/
theorem allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark {cfg : Config}
    (hsh : cfg.shadeLoads = true)
    (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white) {s₀ s : St n} {ops : List (Op n)}
    (hrun : Run cfg (initMark s₀) ops s) (hng : NoGrey s) : AllLiveBlack s := by
```

Unfolded statement of `allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark` (a Lean term with `NoGrey` and `AllLiveBlack` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
cfg.shadeLoads = true → (∀ c, cfg.allocOk c = true → c ≠ .white) →
  ∀ {s₀ s : St n} {ops : List (Op n)}, Run cfg (initMark s₀) ops s →
  (∀ x, s.color x ≠ .grey) → ∀ y, Live s y → s.color y = .black
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hsh : cfg.shadeLoads = true` | Load barrier. | tight | `dijkstra_unshadedLoads_run_from_initMark_leaves_live_white`, `unbarriered_unshadedLoads_blackAlloc_run_from_initMark_not_allLiveBlack` | a 3-object heap and a 4- or 6-step run |
| `halloc : ∀ c, cfg.allocOk c = true → c ≠ .white` | Non-white allocation. | tight | `dijkstra_whiteAlloc_run_from_initMark_leaves_live_white` | a 2-object heap and a 2-step run |
| `hrun : Run cfg (initMark s₀) ops s` | The run consists of enabled steps of `Run cfg` and starts at a root snapshot initMark s₀. Load-bearing enabling conditions inside `Run`: a heap store writes a pointer held in the roots (`s.root y = true`), which `RootsNonWhite` keeps non-white, and an allocation takes an isolated non-root object (`Isolated s a`); dropping either one, with every other step enabled, leaves a reachable object white at the end of marking. The reachability condition on root loads is not load-bearing here (a shaded load of any object keeps both invariants: strong_load, rootsNonWhite_load_shaded). | tight | `shadeLoads_run_not_from_initMark_not_allLiveBlack`, `shadeLoads_nonWhiteAlloc_unheld_store_cycle_not_allLiveBlack`, `shadeLoads_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack` | an empty run from a 2-object state that is not of the form initMark s₀; or a 4- or 2-step sequence from a 3-object root snapshot in which exactly one step violates exactly one enabling condition (held pointer in a store; isolation of an allocation) |
| `hng : NoGrey s` | Marking has terminated. | tight | `shadeLoads_run_from_initMark_with_grey_not_allLiveBlack` | an empty run from a 3-object root snapshot |

Counterexample statements (verbatim):

`dijkstra_unshadedLoads_run_from_initMark_leaves_live_white`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:337-345
/-- **Unshaded root loads defeat Dijkstra marking without a rescan, even with black
allocation.** Under the Dijkstra barrier with unshaded loads and black-only allocation, the
interleaving `traceLoadLost` from the start of a marking cycle on the heap `0 (root) → 1 → 2`
reaches a state with no grey object in which the live root `2` is white. -/
theorem dijkstra_unshadedLoads_run_from_initMark_leaves_live_white :
    cfgD0.barrier = .dijkstra ∧ cfgD0.shadeLoads = false ∧
      (∀ c, cfgD0.allocOk c = true → c ≠ .white) ∧
      Run cfgD0 (initMark hChain) traceLoadLost sLoadLost ∧ NoGrey sLoadLost ∧
      Live sLoadLost 2 ∧ sLoadLost.color 2 = .white :=
```

`unbarriered_unshadedLoads_blackAlloc_run_from_initMark_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:299-303
/-- The barrier hypothesis of Yuasa marking safety cannot be dropped (a 3-object heap and a
6-step run; no barrier, unshaded loads, black-only allocation). -/
theorem unbarriered_unshadedLoads_blackAlloc_run_from_initMark_not_allLiveBlack :
    cfgN0.barrier ≠ .yuasa ∧ (∀ c, cfgN0.allocOk c = true → c ≠ .white) ∧
      Run cfgN0 (initMark hChain) traceLostObject sLost ∧ NoGrey sLost ∧ ¬ AllLiveBlack sLost :=
```

`dijkstra_whiteAlloc_run_from_initMark_leaves_live_white`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:417-423
/-- **White allocation defeats Dijkstra marking without a rescan, even with shaded loads.**
On the heap `0 (root)`, `1` (isolated, free), allocating `1` white into the roots and scanning
the root reaches a state with no grey object in which the live root `1` is white. -/
theorem dijkstra_whiteAlloc_run_from_initMark_leaves_live_white :
    cfgDW.barrier = .dijkstra ∧ cfgDW.shadeLoads = true ∧ cfgDW.allocOk .white = true ∧
      Run cfgDW (initMark hAlloc) traceWhiteAlloc sWhiteAlloc ∧ NoGrey sWhiteAlloc ∧
      Live sWhiteAlloc 1 ∧ sWhiteAlloc.color 1 = .white :=
```

`shadeLoads_run_not_from_initMark_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:461-466
/-- The start at `initMark` cannot be dropped from load-barrier marking safety (an empty run
from a 2-object state). -/
theorem shadeLoads_run_not_from_initMark_not_allLiveBlack :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      (∀ s₀, sBlackWhite ≠ initMark s₀) ∧
      Run cfgU sBlackWhite [] sBlackWhite ∧ NoGrey sBlackWhite ∧ ¬ AllLiveBlack sBlackWhite :=
```

`shadeLoads_nonWhiteAlloc_unheld_store_cycle_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:688-702
/-- The held-pointer condition on stores inside `Run` cannot be dropped from load-barrier marking
safety (a 3-object root snapshot and a 4-step sequence): with no
heap barrier, shaded loads and black allocation, storing the reachable but unheld white object
`2` (skipping the shaded load of `traceLostObject`) is the only non-enabled step, and the final
state has no grey object while the reachable object `2` is white. -/
theorem shadeLoads_nonWhiteAlloc_unheld_store_cycle_not_allLiveBlack :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Run cfgU (initMark hChain) [.scan 0] (runOps cfgU [.scan 0] (initMark hChain)) ∧
      Live (runOps cfgU [.scan 0] (initMark hChain)) 2 ∧
      (runOps cfgU [.scan 0] (initMark hChain)).root 2 = false ∧
      Run cfgU (runOps cfgU [.scan 0, .store 0 2] (initMark hChain)) [.erase 1 2, .scan 1]
        (runOps cfgU traceUnheldStore (initMark hChain)) ∧
      (∀ s, ¬ Run cfgU (initMark hChain) traceUnheldStore s) ∧
      NoGrey (runOps cfgU traceUnheldStore (initMark hChain)) ∧
      ¬ AllLiveBlack (runOps cfgU traceUnheldStore (initMark hChain)) := by
```

`shadeLoads_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:671-682
/-- `Isolated s a` on allocation inside `Run` cannot be dropped from load-barrier marking safety,
even for black allocation (a 3-object root snapshot and a 2-step sequence): with no heap barrier, shaded loads and black allocation, the scan of `0` is a run
from the root snapshot, the allocation of `1` satisfies every enabling condition except
isolation, and the final state has no grey object while the reachable object `2` is white. -/
theorem shadeLoads_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Run cfgU (initMark hChain) [.scan 0] (runOps cfgU [.scan 0] (initMark hChain)) ∧
      cfgU.allocOk .black = true ∧ (runOps cfgU [.scan 0] (initMark hChain)).root 1 = false ∧
      ¬ Isolated (runOps cfgU [.scan 0] (initMark hChain)) 1 ∧
      (∀ s, ¬ Run cfgU (initMark hChain) traceUnisolatedBlackAlloc s) ∧
      NoGrey (runOps cfgU traceUnisolatedBlackAlloc (initMark hChain)) ∧
      ¬ AllLiveBlack (runOps cfgU traceUnisolatedBlackAlloc (initMark hChain)) := by
```

`shadeLoads_run_from_initMark_with_grey_not_allLiveBlack`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:128-132
/-- `NoGrey` at the end of the run cannot be dropped from load-barrier marking safety (an empty
run from a 3-object root snapshot). -/
theorem shadeLoads_run_from_initMark_with_grey_not_allLiveBlack :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Run cfgU (initMark hChain) [] (initMark hChain) ∧ ¬ AllLiveBlack (initMark hChain) :=
```

**Non-vacuity witness (prose):** The lost-object interleaving under cfgU (no heap barrier, shaded loads), followed by a scan of object 2.

`allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:625-632
/-- Non-vacuity of load-barrier marking with no heap barrier: the lost-object interleaving
under shaded loads, followed by a scan of the shaded object. -/
theorem allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark_nonvacuous :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧
      (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Run cfgU (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Sec. 15.2 'Barrier techniques for concurrent collection' (pp. 337-344), subsections 'Black mutator techniques' and 'Load barriers'.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). Quotes Pirinen's result: 'as shown by Pirinen, all possible black mutator barriers other than the Yuasa barrier require a read barrier [Pirinen '98]'.
- Pirinen. Barrier techniques for incremental tracing. ISMM 1998, pp. 20-25. doi:10.1145/286860.286863. Cited by Clements and Hudson (2016) for the result that every black-mutator barrier other than the Yuasa barrier requires a read barrier.

**Design question.** What lets a collector skip both the root rescan and the heap write barrier?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge), a separate claim connecting the theorem to a collector that sweeps (sweeping is not part of the model; not a theorem). Reasoning: A sweep that frees exactly the white objects of a state satisfying the conclusion frees no object reachable from the roots; sweeping is not modeled.

Non-claims: see **Boundaries → Non-claims** (`shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`).

### Termination

#### `scans-only-run-length-at-most-mark-measure`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every configuration and every run of the generated relation `Run cfg` from a state s (enabled steps only, so every scanned object is grey) that consists only of collector scans (`ScansOnly`), the number of steps is at most markMeasure s, where markMeasure s = 2 · (number of white objects of s) + (number of grey objects of s), and at most 2 · n.
- **Tier justification (prose):** Standard potential argument (monotone darkening).

**Lean statement** (`length_le_markMeasure_and_le_two_mul_of_scansOnly_run`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Termination.lean:235-239
/-- **Paused-mutator termination bound.** Every run consisting of collector scans only has at
most `markMeasure s` steps and at most `2·n` steps. -/
theorem length_le_markMeasure_and_le_two_mul_of_scansOnly_run {cfg : Config} {s s' : St n}
    {ops : List (Op n)} (hrun : Run cfg s ops s') (hscan : ScansOnly ops) :
    ops.length ≤ markMeasure s ∧ ops.length ≤ 2 * n :=
```

Unfolded statement of `length_le_markMeasure_and_le_two_mul_of_scansOnly_run` (a Lean term with `ScansOnly` and `markMeasure` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
∀ {cfg : Config} {s s' : St n} {ops : List (Op n)}, Run cfg s ops s' →
  (∀ op ∈ ops, op.isScan = true) →
  ops.length ≤ ((List.finRange n).map (fun x => weight (s.color x))).sum ∧ ops.length ≤ 2 * n
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hrun : Run cfg s ops s'` | The steps are enabled: every scanned object is grey. | tight | `length_bound_fails_without_enabled_scans` | a 1-object heap state and a one-step non-enabled scan |
| `hscan : ScansOnly ops` | The mutator is paused. | tight | `drops_run_longer_than_markMeasure` | a 3-object heap state and seven root drops |

Counterexample statements (verbatim):

`length_bound_fails_without_enabled_scans`:

```lean
-- lean/Toy/Tricolor/Termination.lean:676-683
/-- Enabled scans cannot be dropped from the paused-mutator bound (a 1-object state): a scan of
a black object is not enabled, and
the one-step scan list exceeds the measure `0`. -/
theorem length_bound_fails_without_enabled_scans :
    ScansOnly [(Op.scan 0 : Op 1)] ∧
      ¬ Run cfgD sOneBlack [.scan 0] (runOps cfgD [.scan 0] sOneBlack) ∧
      ¬ ([(Op.scan 0 : Op 1)].length ≤ markMeasure sOneBlack ∧
        [(Op.scan 0 : Op 1)].length ≤ 2 * 1) := by
```

`drops_run_longer_than_markMeasure`:

```lean
-- lean/Toy/Tricolor/Tightness.lean:110-115
/-- Scans only cannot be dropped from the paused-mutator length bound (a 3-object state): seven
root drops from a state of measure
two on three objects exceed both the measure and `2·n = 6`. -/
theorem drops_run_longer_than_markMeasure :
    Run cfgD sDone sevenDrops (runOps cfgD sevenDrops sDone) ∧ ¬ ScansOnly sevenDrops ∧
      ¬ (sevenDrops.length ≤ markMeasure sDone ∨ sevenDrops.length ≤ 2 * 3) := by
```

**Non-vacuity witness (prose):** Two scans from sGreyWhite.

`length_le_markMeasure_and_le_two_mul_of_scansOnly_run_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Termination.lean:824-826
theorem length_le_markMeasure_and_le_two_mul_of_scansOnly_run_nonvacuous :
    Run cfgD sGreyWhite [.scan 0, .scan 1] (scan (scan sGreyWhite 0) 1) ∧
      ScansOnly [(Op.scan 0 : Op 2), .scan 1] :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. 'during marking each node will darken monotonically' (their monotonicity argument for termination).
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 16 'Concurrent mark-sweep' (pp. 349-366), Sec. 16.2 'Termination'.

**Design question.** How long can marking take with the mutator paused?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`scans-only-run-length-at-most-mark-measure`).

#### `scans-only-run-to-no-grey-exists`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every configuration and every state s, the generated relation `Run cfg` has a run from s that consists only of collector scans (`ScansOnly`; each scan is enabled, i.e. scans a grey object) and reaches a state with no grey object.
- **Tier justification (prose):** Standard.

**Lean statement** (`exists_scansOnly_run_to_noGrey`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Termination.lean:243-246
/-- **Paused-mutator termination.** From every state some scans-only run reaches a state with
no grey object. -/
theorem exists_scansOnly_run_to_noGrey (cfg : Config) (s : St n) :
    ∃ ops s', Run cfg s ops s' ∧ ScansOnly ops ∧ NoGrey s' := by
```

Unfolded statement of `exists_scansOnly_run_to_noGrey` (a Lean term with `ScansOnly` and `NoGrey` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
∀ (cfg : Config) (s : St n),
  ∃ ops s', Run cfg s ops s' ∧ (∀ op ∈ ops, op.isScan = true) ∧ ∀ x, s'.color x ≠ .grey
```

**Hypothesis ledger.**

No `Prop` hypotheses. The statement is universally quantified over the heap size `n`, every configuration `cfg : Config` and every state `s : St n`; it is not a statement about concrete instances.

**Non-vacuity witness (prose):** Any state with a grey object, e.g. sGreyWhite.

`exists_scansOnly_run_to_noGrey_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Termination.lean:820-820
theorem exists_scansOnly_run_to_noGrey_nonvacuous : ¬ NoGrey sGreyWhite := by decide
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. 'during marking each node will darken monotonically' (their monotonicity argument for termination).
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 16 'Concurrent mark-sweep' (pp. 349-366), Sec. 16.2 'Termination'.

**Design question.** Does marking with a paused mutator always terminate?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`scans-only-run-to-no-grey-exists`).

#### `scans-plus-measure-at-most-initial-plus-alloc-weight`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Plain claim (prose):** For every configuration (heap barrier none, Dijkstra or Yuasa; any root-load discipline and allocation colors) and every run of the generated relation `Run cfg` from s to s' (enabled steps only, so every scanned object is grey), the number of scans in the run plus markMeasure s' is at most markMeasure s plus the sum, with multiplicity, of the weights of the run's allocation colors (white 2, grey 1, black 0).
- **Tier justification (prose):** Folklore (only allocation can add marking work under target-shading barriers; Clements and Hudson's Theorem 2 bounds marking work for the hybrid barrier with black allocation); the exact accounting with an allocation surcharge for every allocation color is made precise here.

**Lean statement** (`scanCount_add_markMeasure_le`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Termination.lean:276-281
/-- **Collector work is bounded by the initial measure plus allocation weight.** In every run
(any barrier, any configuration), the number of scans plus the final measure is at most the
initial measure plus the summed weights of the allocation colors. -/
theorem scanCount_add_markMeasure_le {cfg : Config} {s s' : St n} {ops : List (Op n)}
    (hrun : Run cfg s ops s') :
    ops.countP Op.isScan + markMeasure s' ≤ markMeasure s + (ops.map Op.allocWeight).sum := by
```

Unfolded statement of `scanCount_add_markMeasure_le` (a Lean term with `markMeasure` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
∀ {cfg : Config} {s s' : St n} {ops : List (Op n)}, Run cfg s ops s' →
  ops.countP Op.isScan + ((List.finRange n).map (fun x => weight (s'.color x))).sum ≤
    ((List.finRange n).map (fun x => weight (s.color x))).sum + (ops.map Op.allocWeight).sum
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hrun : Run cfg s ops s'` | The steps are enabled: every scanned object is grey. | tight | `scanCount_bound_fails_without_enabled_scans` | a 1-object heap state and a one-step non-enabled scan |

Counterexample statements (verbatim):

`scanCount_bound_fails_without_enabled_scans`:

```lean
-- lean/Toy/Tricolor/Termination.lean:689-693
/-- Enabled scans cannot be dropped from the work bound (a 1-object state and one scan). -/
theorem scanCount_bound_fails_without_enabled_scans :
    ¬ Run cfgD sOneBlack [.scan 0] (runOps cfgD [.scan 0] sOneBlack) ∧
      ¬ ([(Op.scan 0 : Op 1)].countP Op.isScan + markMeasure (runOps cfgD [.scan 0] sOneBlack) ≤
        markMeasure sOneBlack + ([(Op.scan 0 : Op 1)].map Op.allocWeight).sum) :=
```

**Non-vacuity witness (prose):** One cycle (6 steps) of the grey-allocation execution, in which allocation re-colors black cells grey and the allocation term cannot be dropped from the bound for that 2-object, 6-step run (allocWeight_needed_greyAllocCycle).

`scanCount_add_markMeasure_le_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Termination.lean:829-833
/-- Non-vacuity of the work bound on a run in which allocation re-colors black cells grey, so
that the allocation term cannot be dropped from the bound for that 2-object run
(`allocWeight_needed_greyAllocCycle`). -/
theorem scanCount_add_markMeasure_le_nonvacuous :
    Run cfgGreyAlloc (cycStates 0) (opsFrom cycOps 0 6) (cycStates 6) :=
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). Its appendix 'Proof of soundness, completeness, and boundedness' gives paper proofs for the hybrid barrier: Lemmas 2 and 3 (a white object reachable from a black object, or from a black goroutine, is grey-protected by a heap object), Theorem 1 (the hybrid write barrier satisfies the weak tricolor invariant) and Theorem 2 (marking terminates in a finite number of steps, bounded via the number of objects at the start of the cycle).
- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. 'during marking each node will darken monotonically' (their monotonicity argument for termination).
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 16 'Concurrent mark-sweep' (pp. 349-366), Sec. 16.2 'Termination' and Sec. 16.3 'Allocation'.

**Design question.** How much collector work can a running mutator cause?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`scans-plus-measure-at-most-initial-plus-alloc-weight`).

#### `fair-collector-eventually-black-allocs-eventually-always-no-grey`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every configuration and every infinite execution (ops, st) of the generated relation `InfRun cfg` (every step ops i is enabled in st i and st (i+1) is its result, so every scanned object is grey; the step alphabet is that of a single marking phase, with no initMark, rescan or sweep step) in which the collector is weakly fair (`CollectorFair`: if from some point on a grey object exists in every state, scans happen infinitely often) and from some point on every allocation is black (`EventuallyOnlyBlackAllocs`), there is a point after which no object is ever grey and no scan occurs (in particular, states with no grey object occur infinitely often).
- **Tier justification (prose):** Fairness-based termination of marking is mechanized in Coq (Coupet-Grimal and Nouvet) and Nqthm (Russinoff, for Ben-Ari's collector); restated for this model. Each of the three hypotheses is tight, with counterexamples that are infinite executions over 1- and 2-object heaps (the allocation counterexample re-colors already-marked cells mid-cycle). This does not make eventually-black allocation necessary for termination in general: the execution of the white-target-allocation card terminates with white allocation forever (eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous).

**Lean statement (first theorem)** (`eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Termination.lean:491-497
/-- **Active-mutator termination (fair collector, eventually black-only allocation).** In an
infinite execution where the collector is weakly fair and, from some point on, every allocation
is black, from some point on no object is grey and no scan occurs. -/
theorem eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (halloc : EventuallyOnlyBlackAllocs ops) :
    ∃ K, ∀ i, K ≤ i → NoGrey (st i) ∧ (ops i).isScan = false := by
```

**Lean statement (second theorem)** (`infinitely_often_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Termination.lean:505-509
/-- Corollary: states with no grey object occur infinitely often. -/
theorem infinitely_often_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (halloc : EventuallyOnlyBlackAllocs ops) :
    ∀ M, ∃ i, M ≤ i ∧ NoGrey (st i) := by
```

Unfolded statement of `eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs` (a Lean term with `InfRun`, `CollectorFair` and `EventuallyOnlyBlackAllocs` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
(∀ i, (ops i).Enabled cfg (st i) ∧ st (i + 1) = (ops i).apply cfg (st i)) →
  (∀ M, (∀ i, M ≤ i → ¬ NoGrey (st i)) → ∀ N, ∃ i, N ≤ i ∧ (ops i).isScan = true) →
  (∃ N, ∀ i, N ≤ i → (ops i).allocWeight = 0) →
  ∃ K, ∀ i, K ≤ i → NoGrey (st i) ∧ (ops i).isScan = false
```

Unfolded statement of `infinitely_often_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs` (a Lean term with `InfRun`, `CollectorFair`, `EventuallyOnlyBlackAllocs` and `NoGrey` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
(∀ i, (ops i).Enabled cfg (st i) ∧ st (i + 1) = (ops i).apply cfg (st i)) →
  (∀ M, (∀ i, M ≤ i → ¬ (∀ x, (st i).color x ≠ .grey)) → ∀ N, ∃ i, N ≤ i ∧ (ops i).isScan = true) →
  (∃ N, ∀ i, N ≤ i → (ops i).allocWeight = 0) →
  ∀ M, ∃ i, M ≤ i ∧ ∀ x, (st i).color x ≠ .grey
```

**Hypothesis ledger.** The two theorems have the same hypotheses, and every row names counterexamples that refute both conclusions: the conjunct `¬ ∃ K, …` of `unenabledScans_collectorFair_never_noGrey`, `starvedCollector_never_noGrey` and `greyAllocCycle_collectorFair_never_noGrey` refutes the first theorem's conclusion, and the conjunct `∀ i, ¬ NoGrey (…)` (every state of the execution has a grey object) of `unenabledScans_collectorFair_not_infinitely_often_noGrey`, `starvedCollector_never_noGrey` and `greyAllocCycle_collectorFair_never_noGrey` refutes the second theorem's conclusion.

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hrun : InfRun cfg ops st` | Every step is enabled (in particular every scanned object is grey). | tight | `unenabledScans_collectorFair_never_noGrey`, `unenabledScans_collectorFair_not_infinitely_often_noGrey` | an infinite execution over a 2-object heap |
| `hfair : CollectorFair ops st` | The mutator cannot starve the collector. | tight | `starvedCollector_never_noGrey` | an infinite execution over a 1-object heap |
| `halloc : EventuallyOnlyBlackAllocs ops` | Allocation stops adding marking work. | tight | `greyAllocCycle_collectorFair_never_noGrey` | a periodic infinite execution over a 2-object heap |

Counterexample statements (verbatim):

`unenabledScans_collectorFair_never_noGrey`:

```lean
-- lean/Toy/Tricolor/Termination.lean:701-710
/-- Enabled scans cannot be dropped from the termination results (an infinite execution over a
2-object heap): scanning the black object `1` forever satisfies
the state equations, collector fairness and both allocation assumptions, yet the grey object
`0` stays grey. -/
theorem unenabledScans_collectorFair_never_noGrey :
    (∀ i, badScanStates (i + 1) = (badScanOps i).apply cfgD (badScanStates i)) ∧
      ¬ InfRun cfgD badScanOps badScanStates ∧
      CollectorFair badScanOps badScanStates ∧ EventuallyOnlyBlackAllocs badScanOps ∧
      WhiteTargetAllocs badScanOps badScanStates ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (badScanStates i) ∧ (badScanOps i).isScan = false := by
```

`unenabledScans_collectorFair_not_infinitely_often_noGrey`:

```lean
-- lean/Toy/Tricolor/Companions.lean:11-22
/-- Enabled scans cannot be dropped from the infinitely-often corollary either (an infinite
execution over a 2-object heap): the execution of `unenabledScans_collectorFair_never_noGrey`,
which scans the black object `1` forever, satisfies the state equations, collector fairness and
both allocation assumptions and is not an `InfRun`; every one of its states has a grey object,
so states with no grey object do not occur infinitely often (they never occur). -/
theorem unenabledScans_collectorFair_not_infinitely_often_noGrey :
    (∀ i, badScanStates (i + 1) = (badScanOps i).apply cfgD (badScanStates i)) ∧
      ¬ InfRun cfgD badScanOps badScanStates ∧
      CollectorFair badScanOps badScanStates ∧ EventuallyOnlyBlackAllocs badScanOps ∧
      WhiteTargetAllocs badScanOps badScanStates ∧
      (∀ i, ¬ NoGrey (badScanStates i)) ∧
      ¬ ∀ M, ∃ i, M ≤ i ∧ NoGrey (badScanStates i) := by
```

`starvedCollector_never_noGrey`:

```lean
-- lean/Toy/Tricolor/Termination.lean:652-658
/-- **Collector fairness cannot be dropped** (an infinite execution over a 1-object heap). An
infinite execution of root drops only, with no allocation, keeps a grey object forever. -/
theorem starvedCollector_never_noGrey :
    InfRun cfgD starveOps starveStates ∧ EventuallyOnlyBlackAllocs starveOps ∧
      WhiteTargetAllocs starveOps starveStates ∧
      ¬ CollectorFair starveOps starveStates ∧ (∀ i, ¬ NoGrey (starveStates i)) ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (starveStates i) ∧ (starveOps i).isScan = false := by
```

`greyAllocCycle_collectorFair_never_noGrey`:

```lean
-- lean/Toy/Tricolor/Termination.lean:596-604
/-- **Without the allocation assumption, collector fairness is not enough.** The six-step
cycle is an infinite execution in which allocation re-colors the black objects `1` and `0` grey
(they are isolated garbage cells, not swept), the collector scans every third step, yet a grey
object exists in every state. -/
theorem greyAllocCycle_collectorFair_never_noGrey :
    InfRun cfgGreyAlloc cycOps cycStates ∧ CollectorFair cycOps cycStates ∧
      ¬ EventuallyOnlyBlackAllocs cycOps ∧ ¬ WhiteTargetAllocs cycOps cycStates ∧
      (∀ i, ¬ NoGrey (cycStates i)) ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (cycStates i) ∧ (cycOps i).isScan = false := by
```

**Non-vacuity witness (prose):** Scan a grey root, then allocate the free cell 1 black and drop it, forever (black allocation infinitely often).

`eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Termination.lean:735-738
theorem eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs_nonvacuous :
    InfRun cfgD activeOps activeStates ∧ CollectorFair activeOps activeStates ∧
      EventuallyOnlyBlackAllocs activeOps ∧
      (∀ N, ∃ i, N ≤ i ∧ activeOps i = .alloc 1 .black) := by
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. 'during marking each node will darken monotonically' (their monotonicity argument for termination).
- Russinoff. A mechanically verified incremental garbage collector. Formal Aspects Comput. 6(4):359-390, 1994. doi:10.1007/BF01211305. Mechanical proof (an extension of the Boyer-Moore prover, Manna-Pnueli model of concurrency) that Ben-Ari's incremental collector collects nothing but garbage (safety) and eventually collects all garbage (liveness).
- Coupet-Grimal, Nouvet. Formal verification of an incremental garbage collector. J. Log. Comput. 13(6):815-833, 2003. doi:10.1093/logcom/13.6.815. Coq proof of safety and liveness properties of an incremental collector represented as an infinite transition system, using an axiomatization of LTL over co-inductive executions.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). Its appendix 'Proof of soundness, completeness, and boundedness' gives paper proofs for the hybrid barrier: Lemmas 2 and 3 (a white object reachable from a black object, or from a black goroutine, is grey-protected by a heap object), Theorem 1 (the hybrid write barrier satisfies the weak tricolor invariant) and Theorem 2 (marking terminates in a finite number of steps, bounded via the number of objects at the start of the cycle).
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 16 'Concurrent mark-sweep' (pp. 349-366), Sec. 16.2 'Termination'.

**Design question.** What fairness or allocation discipline does concurrent marking need to terminate?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`fair-collector-eventually-black-allocs-eventually-always-no-grey`).

#### `fair-collector-white-target-allocs-eventually-always-no-grey`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Plain claim (prose):** For every configuration and every infinite execution (ops, st) of the generated relation `InfRun cfg` (every step ops i is enabled in st i and st (i+1) is its result, so every scanned object is grey; the step alphabet is that of a single marking phase, with no initMark, rescan or sweep step) in which the collector is weakly fair (`CollectorFair`) and every allocation, of any color, takes a cell that is white in the state where it happens (`WhiteTargetAllocs`), there is a point after which no object is ever grey and no scan occurs.
- **Tier justification (prose):** Folklore (on a fixed heap, allocation of free cells cannot outpace marking within a cycle) made precise. Each hypothesis is tight, with counterexamples that are infinite executions over 1- and 2-object heaps (the allocation counterexample re-colors already-marked cells mid-cycle). This does not make white-cell allocation necessary for termination in general: the non-vacuity execution (activeOps, activeStates) of the eventually-black-allocation card satisfies all hypotheses of that card (eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs_nonvacuous), so from some point on no object is grey in it, yet it allocates the black cell 1 black and so does not satisfy WhiteTargetAllocs (activeOps_not_whiteTargetAllocs).

**Lean statement** (`eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs`, verbatim, with its doc comment):

```lean
-- lean/Toy/Tricolor/Termination.lean:515-522
/-- **Active-mutator termination (fair collector, allocation of white cells only).** In an
infinite execution where the collector is weakly fair and every allocation takes a cell that is
white in the current state (any allocation color), from some point on no object is grey and no
scan occurs. -/
theorem eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (hw : WhiteTargetAllocs ops st) :
    ∃ K, ∀ i, K ≤ i → NoGrey (st i) ∧ (ops i).isScan = false := by
```

Unfolded statement of `eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs` (a Lean term with `InfRun`, `CollectorFair` and `WhiteTargetAllocs` unfolded; it elaborates in the theorem's context and is definitionally equal to the theorem's statement):

```lean
(∀ i, (ops i).Enabled cfg (st i) ∧ st (i + 1) = (ops i).apply cfg (st i)) →
  (∀ M, (∀ i, M ≤ i → ¬ NoGrey (st i)) → ∀ N, ∃ i, N ≤ i ∧ (ops i).isScan = true) →
  (∀ i a c, ops i = .alloc a c → (st i).color a = .white) →
  ∃ K, ∀ i, K ≤ i → NoGrey (st i) ∧ (ops i).isScan = false
```

**Hypothesis ledger.**

`tight` means: each named counterexample is a kernel-checked theorem stating that all other hypotheses hold and the conclusion fails, for an instance in the stated witness class; it shows no more than that the hypothesis cannot be dropped within that class.

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hrun : InfRun cfg ops st` | Every step is enabled (in particular every scanned object is grey). | tight | `unenabledScans_collectorFair_never_noGrey` | an infinite execution over a 2-object heap |
| `hfair : CollectorFair ops st` | The mutator cannot starve the collector. | tight | `starvedCollector_never_noGrey` | an infinite execution over a 1-object heap |
| `hw : WhiteTargetAllocs ops st` | Allocation never re-colors a grey or black cell. | tight | `greyAllocCycle_collectorFair_never_noGrey` | a periodic infinite execution over a 2-object heap |

Counterexample statements (verbatim):

`unenabledScans_collectorFair_never_noGrey`:

```lean
-- lean/Toy/Tricolor/Termination.lean:701-710
/-- Enabled scans cannot be dropped from the termination results (an infinite execution over a
2-object heap): scanning the black object `1` forever satisfies
the state equations, collector fairness and both allocation assumptions, yet the grey object
`0` stays grey. -/
theorem unenabledScans_collectorFair_never_noGrey :
    (∀ i, badScanStates (i + 1) = (badScanOps i).apply cfgD (badScanStates i)) ∧
      ¬ InfRun cfgD badScanOps badScanStates ∧
      CollectorFair badScanOps badScanStates ∧ EventuallyOnlyBlackAllocs badScanOps ∧
      WhiteTargetAllocs badScanOps badScanStates ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (badScanStates i) ∧ (badScanOps i).isScan = false := by
```

`starvedCollector_never_noGrey`:

```lean
-- lean/Toy/Tricolor/Termination.lean:652-658
/-- **Collector fairness cannot be dropped** (an infinite execution over a 1-object heap). An
infinite execution of root drops only, with no allocation, keeps a grey object forever. -/
theorem starvedCollector_never_noGrey :
    InfRun cfgD starveOps starveStates ∧ EventuallyOnlyBlackAllocs starveOps ∧
      WhiteTargetAllocs starveOps starveStates ∧
      ¬ CollectorFair starveOps starveStates ∧ (∀ i, ¬ NoGrey (starveStates i)) ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (starveStates i) ∧ (starveOps i).isScan = false := by
```

`greyAllocCycle_collectorFair_never_noGrey`:

```lean
-- lean/Toy/Tricolor/Termination.lean:596-604
/-- **Without the allocation assumption, collector fairness is not enough.** The six-step
cycle is an infinite execution in which allocation re-colors the black objects `1` and `0` grey
(they are isolated garbage cells, not swept), the collector scans every third step, yet a grey
object exists in every state. -/
theorem greyAllocCycle_collectorFair_never_noGrey :
    InfRun cfgGreyAlloc cycOps cycStates ∧ CollectorFair cycOps cycStates ∧
      ¬ EventuallyOnlyBlackAllocs cycOps ∧ ¬ WhiteTargetAllocs cycOps cycStates ∧
      (∀ i, ¬ NoGrey (cycStates i)) ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (cycStates i) ∧ (cycOps i).isScan = false := by
```

**Non-vacuity witness (prose):** Start with the grey root 0 and the free cells 1 and 2; allocate the white cell 1 grey (allocation adds marking work), scan 0 and 1, then allocate the white cell 2 white and drop it, forever: the initial state has a grey object, two scans occur, every allocation takes a white cell, and allocation is never eventually black-only. A second witness allocates the white cell 1 white and drops it forever, from a state with no grey object.

`eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous_with_marking_work` (verbatim):

```lean
-- lean/Toy/Tricolor/Termination.lean:910-919
/-- Non-vacuity of the white-target-allocation theorem on an execution with collector work: all
hypotheses hold, the initial state has a grey object, the first allocation is grey (allocation
adds marking work), two scans occur, and white allocation occurs infinitely often (so
allocation is never eventually black-only). -/
theorem eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous_with_marking_work :
    InfRun cfgGreyAlloc wtOps wtStates ∧ CollectorFair wtOps wtStates ∧
      WhiteTargetAllocs wtOps wtStates ∧ ¬ EventuallyOnlyBlackAllocs wtOps ∧
      ¬ NoGrey (wtStates 0) ∧ wtOps 0 = .alloc 1 .grey ∧
      (wtOps 1).isScan = true ∧ (wtOps 2).isScan = true ∧
      (∀ N, ∃ i, N ≤ i ∧ wtOps i = .alloc 2 .white) := by
```

`eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous` (verbatim):

```lean
-- lean/Toy/Tricolor/Termination.lean:790-792
theorem eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous :
    InfRun cfgGreyAlloc wOps wStates ∧ CollectorFair wOps wStates ∧
      WhiteTargetAllocs wOps wStates ∧ ¬ EventuallyOnlyBlackAllocs wOps := by
```

**Prior art** (as recorded in `results.json`; what was read of each source is under **Evidence → Primary sources**):

- Dijkstra, Lamport, Martin, Scholten, Steffens. On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21(11):966-975, 1978. doi:10.1145/359642.359655. Manuscript EWD 520 (20 October 1975), E. W. Dijkstra Archive, https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html. 'during marking each node will darken monotonically' (their monotonicity argument for termination).
- Russinoff. A mechanically verified incremental garbage collector. Formal Aspects Comput. 6(4):359-390, 1994. doi:10.1007/BF01211305. Mechanical proof (an extension of the Boyer-Moore prover, Manna-Pnueli model of concurrency) that Ben-Ari's incremental collector collects nothing but garbage (safety) and eventually collects all garbage (liveness).
- Coupet-Grimal, Nouvet. Formal verification of an incremental garbage collector. J. Log. Comput. 13(6):815-833, 2003. doi:10.1093/logcom/13.6.815. Coq proof of safety and liveness properties of an incremental collector represented as an infinite transition system, using an axiomatization of LTL over co-inductive executions.
- Clements, Hudson. Proposal: Eliminate STW stack re-scanning. golang/proposal, design/17503-eliminate-rescan.md at commit 0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407 (2016). Its appendix 'Proof of soundness, completeness, and boundedness' gives paper proofs for the hybrid barrier: Lemmas 2 and 3 (a white object reachable from a black object, or from a black goroutine, is grey-protected by a heap object), Theorem 1 (the hybrid write barrier satisfies the weak tricolor invariant) and Theorem 2 (marking terminates in a finite number of steps, bounded via the number of objects at the start of the cycle).
- Jones, Hosking, Moss. The Garbage Collection Handbook, 2nd ed., CRC Press, 2023. doi:10.1201/9781003276142. Chapter 16 'Concurrent mark-sweep' (pp. 349-366), Sec. 16.2 'Termination'.

**Design question.** Is black allocation needed for termination when allocation takes free cells of a fixed heap?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims** (`fair-collector-white-target-allocs-eventually-always-no-grey`).

### Auxiliary lemmas cited by name

The lemmas below are cited by name in the cards, ledgers, non-claims or summary without being a
card's main result, counterexample, non-vacuity witness or positive control. Each statement is
quoted verbatim from the Lean sources (proofs elided), and each is listed in the `lean_names`
field of the citing cards in `results.json`, so its statement and definition-closure hashes are
recorded in `audit/statements.json` (see **Evidence → Kernel-check record**). Basis: execution
(Lean kernel check).

`floatingGarbage_yuasa_run` (cited by: `no-grey-strong-nonwhite-roots-implies-live-black`, `no-grey-weak-roots-protected-implies-live-black`, `yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`, `dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`, `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:567-576
/-- `AllLiveBlack` is soundness, not completeness: a Yuasa run from the start of a marking
cycle that allocates `1` black and drops it ends with no grey object, every live object black,
and the unreachable object `1` black (floating garbage that this cycle does not free). -/
theorem floatingGarbage_yuasa_run :
    Run cfgY (initMark hAlloc) [.alloc 1 .black, .drop 1, .scan 0]
        (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)) ∧
      NoGrey (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)) ∧
      AllLiveBlack (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)) ∧
      ¬ Live (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)) 1 ∧
      (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)).color 1 = .black := by
```

`rootsProtected_of_rootsNonWhite` (cited by: `no-grey-weak-roots-protected-implies-live-black`):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:44-44
theorem rootsProtected_of_rootsNonWhite {s : St n} (hr : RootsNonWhite s) : RootsProtected s :=
```

`rootsNonWhite_of_rootsProtected_of_noGrey` (cited by: `no-grey-weak-roots-protected-implies-live-black`):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:47-48
theorem rootsNonWhite_of_rootsProtected_of_noGrey {s : St n} (hng : NoGrey s)
    (hr : RootsProtected s) : RootsNonWhite s :=
```

`strong_of_weak_of_noGrey` (cited by: `no-grey-weak-roots-protected-implies-live-black`):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:34-35
/-- With no grey object, the weak invariant collapses to the strong one. -/
theorem strong_of_weak_of_noGrey {s : St n} (hng : NoGrey s) (hw : Weak s) : Strong s :=
```

`allLiveBlack_of_noGrey_of_weak_of_rootsNonWhite` (cited by: `no-grey-weak-roots-protected-implies-live-black`):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:38-41
/-- **End-of-marking safety (weak invariant).** If no object is grey, the weak invariant
holds and every root is non-white, then every live object is black. -/
theorem allLiveBlack_of_noGrey_of_weak_of_rootsNonWhite {s : St n}
    (hng : NoGrey s) (hw : Weak s) (hr : RootsNonWhite s) : AllLiveBlack s :=
```

`weak_and_not_strong` (cited by: `strong-implies-weak`):

```lean
-- lean/Toy/Tricolor/EndOfMarking.lean:161-162
/-- **The converse of `weak_of_strong` fails.** -/
theorem weak_and_not_strong : Weak sWeakNotStrong ∧ ¬ Strong sWeakNotStrong :=
```

`strong_store_dijkstra` (cited by: `dijkstra-barrier-preserves-strong`, `dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:124-125
theorem strong_store_dijkstra {s : St n} (hs : Strong s) (x y : Fin n) :
    Strong (store .dijkstra s x y) := by
```

`strong_load` (cited by: `dijkstra-barrier-preserves-strong`, `dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`, `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:144-145
theorem strong_load {s : St n} (hs : Strong s) (sh : Bool) (y : Fin n) :
    Strong (load sh s y) :=
```

`strong_alloc_grey` (cited by: `dijkstra-barrier-preserves-strong`, `isolated-alloc-preserves-roots-protected-iff-nonwhite`, `shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots`, `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:483-485
/-- Allocating an object grey preserves the strong invariant even if the object already has
pointers: a grey object is neither the black source nor the white target of an edge. -/
theorem strong_alloc_grey {s : St n} (hs : Strong s) (a : Fin n) : Strong (alloc s a .grey) := by
```

`strong_alloc_black_of_successors_nonWhite` (cited by: `dijkstra-barrier-preserves-strong`, `isolated-alloc-preserves-roots-protected-iff-nonwhite`, `shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots`, `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:495-498
/-- Allocating an object black preserves the strong invariant even if the object already has
pointers, provided every object it points to is non-white (its initial targets were shaded). -/
theorem strong_alloc_black_of_successors_nonWhite {s : St n} (hs : Strong s) {a : Fin n}
    (hsucc : ∀ v, s.edge a v = true → s.color v ≠ .white) : Strong (alloc s a .black) := by
```

`weak_rootsProtected_store` (cited by: `yuasa-nonwhite-alloc-preserves-weak-and-roots-protected`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:252-254
theorem weak_rootsProtected_store {s : St n} (hw : Weak s) (hr : RootsProtected s)
    (b : Barrier) (x : Fin n) {y : Fin n} (hy : Live s y) :
    Weak (store b s x y) ∧ RootsProtected (store b s x y) := by
```

`rootsNonWhite_alloc_iff_ne_white` (cited by: `isolated-alloc-preserves-roots-protected-iff-nonwhite`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:394-397
/-- **Allocation color under non-white roots.** Allocating into the roots preserves
`RootsNonWhite` exactly when the allocation color is non-white. -/
theorem rootsNonWhite_alloc_iff_ne_white {s : St n} (hr : RootsNonWhite s) (a : Fin n)
    (c : Color) : RootsNonWhite (alloc s a c) ↔ c ≠ .white := by
```

`allLiveBlack_of_noGrey_of_scansOnly_run_from_initMark` (cited by: `no-barrier-unshaded-loads-leaves-live-white`):

```lean
-- lean/Toy/Tricolor/Marking.lean:45-50
/-- **Paused-mutator marking from a root snapshot.** Under any configuration, a scans-only run
from the start of a marking cycle that reaches a state with no grey object ends with every live
object black. -/
theorem allLiveBlack_of_noGrey_of_scansOnly_run_from_initMark {cfg : Config} {s₀ s : St n}
    {ops : List (Op n)} (hrun : Run cfg (initMark s₀) ops s) (hscan : ScansOnly ops)
    (hng : NoGrey s) : AllLiveBlack s := by
```

`unbarriered_unshadedLoads_heldTrace_reaches_sLost` (cited by: `no-barrier-unshaded-loads-leaves-live-white`):

```lean
-- lean/Toy/Tricolor/Counterexamples.lean:223-226
/-- The register-disciplined variant reaches the same final state `sLost` without a heap
barrier and without load shading. -/
theorem unbarriered_unshadedLoads_heldTrace_reaches_sLost :
    Run cfgN0 (initMark hChain) traceLostObjectHeld sLost := by
```

`allLiveBlack_of_strong_of_rescan_of_scansOnly_run` (cited by: `dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`):

```lean
-- lean/Toy/Tricolor/Marking.lean:70-75
/-- **Remark phase.** From any state satisfying the strong invariant, rescanning the roots and
then draining grey objects with collector scans only (mutator paused) until no grey object
remains ends with every live object black, whatever the root colors were. -/
theorem allLiveBlack_of_strong_of_rescan_of_scansOnly_run {cfg : Config} {s s' : St n}
    {ops : List (Op n)} (hs : Strong s) (hrun : Run cfg (rescan s) ops s')
    (hscan : ScansOnly ops) (hng : NoGrey s') : AllLiveBlack s' := by
```

`strong_alloc_black_of_successors_held` (cited by: `shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots`, `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:509-514
/-- Under `RootsNonWhite`, allocating an object black preserves the strong invariant even if
the object already has pointers, provided every object it points to is held in the roots
(fields initialized from registers, which a load barrier keeps non-white). -/
theorem strong_alloc_black_of_successors_held {s : St n} (hs : Strong s)
    (hr : RootsNonWhite s) {a : Fin n} (hheld : ∀ v, s.edge a v = true → s.root v = true) :
    Strong (alloc s a .black) :=
```

`rootsNonWhite_load_shaded` (cited by: `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:418-419
theorem rootsNonWhite_load_shaded {s : St n} (hr : RootsNonWhite s) (y : Fin n) :
    RootsNonWhite (load true s y) := by
```

`markMeasure_eq_two_mul_countWhite_add_countGrey` (cited by: `scans-only-run-length-at-most-mark-measure`):

```lean
-- lean/Toy/Tricolor/Termination.lean:116-119
/-- The measure is twice the number of white objects plus the number of grey objects. -/
theorem markMeasure_eq_two_mul_countWhite_add_countGrey (s : St n) :
    markMeasure s = 2 * (List.finRange n).countP (fun x => s.color x == .white) +
      (List.finRange n).countP (fun x => s.color x == .grey) :=
```

`markMeasure_le_two_mul` (cited by: `scans-only-run-length-at-most-mark-measure`, `scans-plus-measure-at-most-initial-plus-alloc-weight`):

```lean
-- lean/Toy/Tricolor/Termination.lean:101-102
/-- The measure is at most `2·n`. -/
theorem markMeasure_le_two_mul (s : St n) : markMeasure s ≤ 2 * n := by
```

`markMeasure_scan_lt` (cited by: `scans-only-run-length-at-most-mark-measure`):

```lean
-- lean/Toy/Tricolor/Termination.lean:130-132
/-- **A collector scan of a grey object strictly decreases the measure.** -/
theorem markMeasure_scan_lt {s : St n} {g : Fin n} (hg : s.color g = .grey) :
    markMeasure (scan s g) < markMeasure s := by
```

`scan_black_markMeasure_eq` (cited by: `scans-only-run-length-at-most-mark-measure`):

```lean
-- lean/Toy/Tricolor/Tightness.lean:99-103
/-- Greyness of the scanned object cannot be dropped from the measure decrease (a 3-object
state): scanning a black object whose
successors are black leaves the measure unchanged. -/
theorem scan_black_markMeasure_eq :
    sDone.color 0 = .black ∧ markMeasure (scan sDone 0) = markMeasure sDone := by
```

`allocWeight_needed_greyAllocCycle` (cited by: `scans-plus-measure-at-most-initial-plus-alloc-weight`):

```lean
-- lean/Toy/Tricolor/Termination.lean:635-641
/-- The allocation term of the work bound cannot be dropped (a 2-object heap and a 6-step run):
over one cycle of the grey-allocation execution, the number of scans plus the final measure
exceeds the initial measure. -/
theorem allocWeight_needed_greyAllocCycle :
    Run cfgGreyAlloc (cycStates 0) (opsFrom cycOps 0 6) (cycStates 6) ∧
      markMeasure (cycStates 0) <
        (opsFrom cycOps 0 6).countP Op.isScan + markMeasure (cycStates 6) := by
```

`greyAllocCycle_scans_exceed_two_mul_n` (cited by: `scans-plus-measure-at-most-initial-plus-alloc-weight`):

```lean
-- lean/Toy/Tricolor/Termination.lean:626-630
/-- With re-coloring grey allocation the number of scans in a run exceeds `2·n`: the first 18
steps of the cycle (on `n = 2` objects) contain 6 scans. -/
theorem greyAllocCycle_scans_exceed_two_mul_n :
    Run cfgGreyAlloc (cycStates 0) (opsFrom cycOps 0 18) (cycStates 18) ∧
      2 * 2 < (opsFrom cycOps 0 18).countP Op.isScan := by
```

`scanCount_add_markMeasure_le_of_allocTargetsWhite` (cited by: `scans-plus-measure-at-most-initial-plus-alloc-weight`):

```lean
-- lean/Toy/Tricolor/Termination.lean:314-319
/-- **Work bound without re-coloring allocation.** In every run whose allocations take white
cells only, the number of scans plus the final measure is at most the initial measure, for
every allocation color. -/
theorem scanCount_add_markMeasure_le_of_allocTargetsWhite {cfg : Config} {s s' : St n}
    {ops : List (Op n)} (hrun : Run cfg s ops s') (hw : AllocTargetsWhite cfg s ops) :
    ops.countP Op.isScan + markMeasure s' ≤ markMeasure s := by
```

`shadeLe_store` (cited by: `scans-plus-measure-at-most-initial-plus-alloc-weight`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:62-62
theorem shadeLe_store (b : Barrier) (s : St n) (x y : Fin n) : ShadeLe s (store b s x y) := by
```

`shadeLe_erase` (cited by: `scans-plus-measure-at-most-initial-plus-alloc-weight`):

```lean
-- lean/Toy/Tricolor/Preservation.lean:68-68
theorem shadeLe_erase (b : Barrier) (s : St n) (x z : Fin n) : ShadeLe s (erase b s x z) := by
```

`collectorFair_antecedent_false_of_eventuallyOnlyBlackAllocs` (cited by: `fair-collector-eventually-black-allocs-eventually-always-no-grey`):

```lean
-- lean/Toy/Tricolor/Termination.lean:838-844
/-- In every execution satisfying the hypotheses of the eventually-black-allocation termination
theorem, the antecedent of `CollectorFair` is false from every point on: grey objects do not
persist from any point onward. -/
theorem collectorFair_antecedent_false_of_eventuallyOnlyBlackAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (halloc : EventuallyOnlyBlackAllocs ops) :
    ∀ M, ¬ (∀ i, M ≤ i → ¬ NoGrey (st i)) := by
```

`activeOps_not_whiteTargetAllocs` (cited by: `fair-collector-white-target-allocs-eventually-always-no-grey`):

```lean
-- lean/Toy/Tricolor/Termination.lean:887-890
/-- The non-vacuity execution of the eventually-black-allocation theorem re-colors the black
cell `1` black at step `3`, so it is not an execution in which every allocation takes a white
cell. -/
theorem activeOps_not_whiteTargetAllocs : ¬ WhiteTargetAllocs activeOps activeStates := by
```

`collectorFair_antecedent_false_of_whiteTargetAllocs` (cited by: `fair-collector-white-target-allocs-eventually-always-no-grey`):

```lean
-- lean/Toy/Tricolor/Termination.lean:850-855
/-- In every execution satisfying the hypotheses of the white-target-allocation termination
theorem, the antecedent of `CollectorFair` is false from every point on. -/
theorem collectorFair_antecedent_false_of_whiteTargetAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (hw : WhiteTargetAllocs ops st) :
    ∀ M, ¬ (∀ i, M ≤ i → ¬ NoGrey (st i)) := by
```

`eventually_only_white_alloc_of_whiteTargetAllocs` (cited by: `fair-collector-white-target-allocs-eventually-always-no-grey`):

```lean
-- lean/Toy/Tricolor/Termination.lean:860-866
/-- In every infinite execution in which every allocation takes a white cell (no fairness
assumption), only finitely many allocations are grey or black: from some point on every
allocation is white. -/
theorem eventually_only_white_alloc_of_whiteTargetAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hw : WhiteTargetAllocs ops st) :
    ∃ K, ∀ i, K ≤ i → ∀ a c, ops i = .alloc a c → c = .white := by
```

## Boundaries

### Non-claims (per result)

What each result does **not** show, verbatim from `results.json`. These are part of each result's meaning.

**`no-grey-strong-nonwhite-roots-implies-live-black`** (`allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite`):

- Says nothing about states in which a grey object remains; it is a statement about the final state.
- Does not say that the strong invariant is maintained by any particular barrier (see dijkstra-barrier-preserves-strong).
- The hypotheses must hold in the state in which white objects are freed. With unbarriered root writes, this package establishes RootsNonWhite by a root rescan (dijkstra-rescan-and-paused-drain-no-grey-implies-live-black) or by shaded root loads with non-white allocation (shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black); the strong invariant alone does not give it (noGrey_strong_and_not_allLiveBlack).
- `AllLiveBlack` expresses soundness (`Live s y → s.color y = .black`), not completeness: unreachable objects that were allocated black or shaded before becoming unreachable remain black (floating garbage) until a subsequent cycle, and starting a new cycle requires resetting or flipping black marks during sweep. (Example of floating garbage: floatingGarbage_yuasa_run. Sweeping and later cycles are not modeled.)
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`weak-and-roots-protected-imply-live-white-grey-protected`** (`greyProtected_of_live_of_white_of_weak_of_rootsProtected`):

- Grey protection may start at an unreachable grey object; the result does not say the protecting grey object is reachable.
- The converse direction is not claimed: protection of reachable white objects says nothing about black-to-white edges among unreachable objects, which the weak invariant also constrains (not proved here).
- Does not by itself say that any barrier preserves its hypotheses (see yuasa-nonwhite-alloc-preserves-weak-and-roots-protected).
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`no-grey-weak-roots-protected-implies-live-black`** (`allLiveBlack_of_noGrey_of_weak_of_rootsProtected`):

- In every state, RootsNonWhite implies RootsProtected (rootsProtected_of_rootsNonWhite) and the strong invariant implies the weak one (weak_of_strong); in a state with no grey object, RootsProtected implies RootsNonWhite (rootsNonWhite_of_rootsProtected_of_noGrey) and the weak invariant implies the strong one (strong_of_weak_of_noGrey). So the two root conditions, and the two invariants, can differ only in a state that has a grey object. The variant with RootsNonWhite in place of RootsProtected is allLiveBlack_of_noGrey_of_weak_of_rootsNonWhite: in a state with no grey object in which the weak invariant holds and every root is non-white, every object reachable from the roots is black.
- `AllLiveBlack` expresses soundness (`Live s y → s.color y = .black`), not completeness: unreachable objects that were allocated black or shaded before becoming unreachable remain black (floating garbage) until a subsequent cycle, and starting a new cycle requires resetting or flipping black marks during sweep. (Example of floating garbage: floatingGarbage_yuasa_run. Sweeping and later cycles are not modeled.)
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`strong-implies-weak`** (`weak_of_strong`):

- The converse fails: weak_and_not_strong (sWeakNotStrong satisfies the weak but not the strong invariant).
- Does not say that a barrier preserving the weak invariant preserves the strong one (false for the Yuasa barrier: store_yuasa_breaks_strong), nor the reverse (the Dijkstra barrier does not preserve the weak invariant from weak, non-strong states: erase_dijkstra_breaks_weak).
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`dijkstra-barrier-preserves-strong`** (`strong_preserved_of_dijkstra`):

- Preserving the strong invariant is not by itself safety: roots may become white (unshaded root loads, white allocation), so the end-of-marking theorem has the hypothesis RootsNonWhite (tight in a 1-object state), which this result does not provide (dijkstra_unshadedLoads_run_from_initMark_leaves_live_white, dijkstra_whiteAlloc_run_from_initMark_leaves_live_white).
- No hypothesis on root-load shading or allocation color is needed for this invariant.
- Does not cover a non-atomic barrier (shade and write as separate steps). In the final fine-grained solution of Dijkstra et al. the mutator places an edge and then, as a separate indivisible action, shades the target of the edge just placed; that interleaving is not modeled.
- Allocating black without shading initial fields is covered here because `alloc` requires `Isolated s a` (no pointers into or out of the object at birth, modeling zeroed memory); its fields are populated later by separate `store` steps, whose targets the Dijkstra barrier shades. The allocation step itself runs no heap barrier, so if a runtime initializes fields of a newly allocated black object directly with pointers to white objects (e.g., constructor-time tuple allocation), black allocation can create a black-to-white edge (one step: dijkstra_unisolated_blackAlloc_breaks_strong; whole cycle with a final rescan: dijkstra_unisolated_alloc_cycle_rescan_not_allLiveBlack). For the state update alone, allocating such an object grey, or black when every initial target is already non-white, preserves the strong invariant (strong_alloc_grey, strong_alloc_black_of_successors_nonWhite); a step relation that admits such allocations is not studied here.
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.
- Any connection to a production collector (Go's hybrid barrier, a JVM or JavaScript collector) is a modeling bridge, not a consequence of this result; the result neither establishes nor refutes any claim about such collectors.

**`yuasa-nonwhite-alloc-preserves-weak-and-roots-protected`** (`weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc`):

- The weak invariant alone is not preserved by these steps: the root clause cannot be dropped (yuasa_store_without_rootsProtected_breaks_weak: a 2-object heap state and one enabled Yuasa store).
- Does not say the Yuasa barrier preserves the strong invariant (it does not: store_yuasa_breaks_strong).
- Allocation in grey is as safe as black here; the result does not say grey allocation is harmless for termination (see the termination results).
- Overwrites are modeled as erase then store; a store into a previously null field shades nothing under this barrier.
- Unshaded root loads and heap stores are covered here because `Op.Enabled` restricts both operations to objects already strongly `Live` from traced roots (a store writes a pointer held in the roots, which is live). Promoting a white object reachable only through a weak or soft reference, a finalizer queue, or an untraced native handle (`¬Live s y`) into mutator roots or heap fields can violate `RootsProtected` / `Weak` (`load_of_unreachable_breaks_rootsProtected`, `yuasa_store_of_unreachable_breaks_weak`) and requires an explicit shading barrier. (Weak references, finalizers and native handles are not modeled.)
- `initMark` shades every root-referenced heap object atomically in a single step, modeling a stop-the-world root snapshot/scan (or blackening all stacks before any heap object is blackened). It does not show that a pure Yuasa deletion barrier is safe when mutator thread stacks remain unscanned (grey) while heap objects are blackened; in that setting a mutator can move a white pointer from an unscanned stack into a null field of a black heap object without shading it, requiring an additional insertion shade on grey stacks (as in Go's hybrid barrier). (That failure is not proved here; concurrent stack scanning is not modeled.)
- Overwriting a pointer with `null` or bulk-clearing pointer-containing heap memory (`memclr`, slice truncation) corresponds to `erase` and must execute the Yuasa deletion barrier on every overwritten pointer; only stores into already-null fields of freshly zeroed objects omit shading. (Without the deletion barrier an erase can break the weak invariant: erase_unbarriered_breaks_weak.)
- Allocating black without shading initial fields is covered here because `alloc` requires `Isolated s a` (no pointers into or out of the object at birth, modeling zeroed memory); its fields are populated later by separate enabled `store` steps, which write only pointers held in the roots and which the Yuasa barrier does not shade (a store into a null field deletes no pointer; a white stored target is grey protected by the weak invariant and its root clause: greyProtected_of_live_of_white_of_weak_of_rootsProtected). If a runtime initializes fields of a newly allocated black object directly with pointers to white objects (e.g., constructor-time tuple allocation), black allocation can leave a reachable white object unprotected (one step: yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak; whole cycle from a root snapshot: yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack). Whether shading the initial targets or allocating such objects grey restores the weak invariant is not proved here.
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.
- Any connection to a production collector (Go's hybrid barrier, a JVM or JavaScript collector) is a modeling bridge, not a consequence of this result; the result neither establishes nor refutes any claim about such collectors.

**`yuasa-barrier-breaks-strong`** (`store_yuasa_breaks_strong`):

- Not a safety failure: the weak invariant and its root clause still hold in the resulting state.
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`isolated-alloc-preserves-roots-protected-iff-nonwhite`** (`rootsProtected_alloc_iff_ne_white`):

- Says nothing about collectors that rescan roots (for those, white allocation is safe: dijkstra-rescan-and-paused-drain-no-grey-implies-live-black).
- Grey and black are both acceptable for safety; the result does not distinguish them (see the termination results).
- The companion lemma rootsNonWhite_alloc_iff_ne_white is the analogue for RootsNonWhite, with different hypotheses: it assumes that every root of s is non-white (RootsNonWhite s) and has no isolation hypothesis, and states that for every object a and every color c, every root of alloc s a c is non-white if and only if c is not white.
- Allocating black without shading initial fields is covered here because `alloc` requires `Isolated s a` (no pointers into or out of the object at birth, modeling zeroed memory); its fields are populated later by separate `store` steps, each subject to the configuration's heap barrier and to the store enabling condition (the stored pointer is held in the roots). If a runtime initializes fields of a newly allocated black object directly with pointers to white objects (e.g., constructor-time tuple allocation), black allocation can break the strong invariant (shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong, dijkstra_unisolated_blackAlloc_breaks_strong) or the weak invariant (yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak). For the strong invariant and the state update alone, allocating such an object grey, or black when every initial target is already non-white, avoids this (strong_alloc_grey, strong_alloc_black_of_successors_nonWhite); the weak-invariant analogue is not proved here.
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots`** (`strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc`):

- No hypothesis on the heap barrier: the result covers none, Dijkstra and Yuasa alike.
- In this model no heap write barrier is needed alongside shaded loads and non-white allocation because every heap store writes a pointer the mutator holds in its roots, which `RootsNonWhite` keeps non-white. If the mutator could copy a pointer between heap fields without loading it (for example a bulk pointer copy that bypasses the load barrier), the strong invariant can break without a heap barrier (shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong).
- Shading root loads is a cost on every pointer load into a register or stack slot; the result does not compare costs.
- Allocating black without shading initial fields is covered here because `alloc` requires `Isolated s a` (no pointers into or out of the object at birth, modeling zeroed memory); its fields are populated later by separate enabled `store` steps of root-held, hence (by `RootsNonWhite`) already non-white, pointers, so no heap write barrier is involved. If a runtime initializes fields of a newly allocated black object directly with pointers to white objects that bypass the load barrier (pointers not held in the roots), black allocation can create a black-to-white edge (shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong). For the state update alone, starting from a state s that satisfies the strong invariant: if also every root of s is non-white (RootsNonWhite s), allocating an object black whose initial fields point only to objects held in the roots preserves the strong invariant (strong_alloc_black_of_successors_held); allocating an object grey preserves it (strong_alloc_grey); and allocating an object black whose initial targets are all non-white preserves it (strong_alloc_black_of_successors_nonWhite); a step relation that admits such allocations is not studied here.
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.
- Any connection to a production collector (Go's hybrid barrier, a JVM or JavaScript collector) is a modeling bridge, not a consequence of this result; the result neither establishes nor refutes any claim about such collectors.

**`yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`** (`allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark`):

- This is a safety statement: it does not say marking terminates (see the termination results).
- `AllLiveBlack` expresses soundness (`Live s y → s.color y = .black`), not completeness: unreachable objects that were allocated black or shaded before becoming unreachable remain black (floating garbage) until a subsequent cycle, and starting a new cycle requires resetting or flipping black marks during sweep. (Example of floating garbage: floatingGarbage_yuasa_run. Sweeping and later cycles are not modeled.)
- Unshaded root loads and heap stores are covered here because `Op.Enabled` restricts both operations to objects already strongly `Live` from traced roots (a store writes a pointer held in the roots, which is live). Promoting a white object reachable only through a weak or soft reference, a finalizer queue, or an untraced native handle (`¬Live s y`) into mutator roots or heap fields can violate `RootsProtected` / `Weak` (`load_of_unreachable_breaks_rootsProtected`, `yuasa_store_of_unreachable_breaks_weak`) and requires an explicit shading barrier. (Weak references, finalizers and native handles are not modeled.)
- `initMark` shades every root-referenced heap object atomically in a single step, modeling a stop-the-world root snapshot/scan (or blackening all stacks before any heap object is blackened). It does not show that a pure Yuasa deletion barrier is safe when mutator thread stacks remain unscanned (grey) while heap objects are blackened; in that setting a mutator can move a white pointer from an unscanned stack into a null field of a black heap object without shading it, requiring an additional insertion shade on grey stacks (as in Go's hybrid barrier). (That failure is not proved here; concurrent stack scanning is not modeled.)
- Overwriting a pointer with `null` or bulk-clearing pointer-containing heap memory (`memclr`, slice truncation) corresponds to `erase` and must execute the Yuasa deletion barrier on every overwritten pointer; only stores into already-null fields of freshly zeroed objects omit shading. (Without the deletion barrier an erase can break the weak invariant: erase_unbarriered_breaks_weak.)
- Allocating black without shading initial fields is covered here because `alloc` requires `Isolated s a` (no pointers into or out of the object at birth, modeling zeroed memory); its fields are populated later by separate enabled `store` steps, which write only pointers held in the roots and which the Yuasa barrier does not shade (a store into a null field deletes no pointer; a white stored target is grey protected by the weak invariant and its root clause: greyProtected_of_live_of_white_of_weak_of_rootsProtected). If a runtime initializes fields of a newly allocated black object directly with pointers to white objects (e.g., constructor-time tuple allocation), black allocation can leave a reachable white object unprotected (one step: yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak; whole cycle from a root snapshot: yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack). Whether shading the initial targets or allocating such objects grey restores the weak invariant is not proved here.
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.
- Any connection to a production collector (Go's hybrid barrier, a JVM or JavaScript collector) is a modeling bridge, not a consequence of this result; the result neither establishes nor refutes any claim about such collectors.

**`no-barrier-unshaded-loads-leaves-live-white`** (`unbarriered_unshadedLoads_traceLostObject_leaves_live_white`):

- Escape hatches that defeat this counterexample include: pausing the mutator during marking (`ScansOnly`; allLiveBlack_of_noGrey_of_scansOnly_run_from_initMark), adding a Dijkstra insertion barrier or Yuasa deletion barrier (positive controls), or using a shading load barrier (`shadeLoads = true`) with non-white allocation (shadeLoads_traceLostObject_then_scan_safe and allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark).
- Allocation colors play no role in the trace.
- Does not say that every interleaving without a barrier is unsafe.
- The erase in traceLostObject writes to object 1, which is reachable but not held in the roots. Under cfgN0 (no heap barrier, unshaded root loads, black-only allocation), the variant traceLostObjectHeld, which loads 1 before the erase and drops it afterwards, is an enabled run from initMark hChain to sLost, the final state of traceLostObject under cfgN0 (unbarriered_unshadedLoads_heldTrace_reaches_sLost).
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`** (`allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run`):

- Does not bound the length of the drain beyond the paused-mutator termination bound; nothing here is about pause times.
- The core is the state-level lemma allLiveBlack_of_strong_of_rescan_of_scansOnly_run: for every configuration cfg, every state s satisfying the strong invariant, and every state s' reached from rescan s by a run of `Run cfg` that consists of collector scans (`ScansOnly`), if s' has no grey object then every object reachable from the roots in s' is black. Its hypotheses say nothing about how s was reached, about the heap barrier, or about the colors of the roots of s.
- `AllLiveBlack` expresses soundness (`Live s y → s.color y = .black`), not completeness: unreachable objects that were allocated black or shaded before becoming unreachable remain black (floating garbage) until a subsequent cycle, and starting a new cycle requires resetting or flipping black marks during sweep. (Example of floating garbage: floatingGarbage_yuasa_run. Sweeping and later cycles are not modeled.)
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.
- Any connection to a production collector (Go's hybrid barrier, a JVM or JavaScript collector) is a modeling bridge, not a consequence of this result; the result neither establishes nor refutes any claim about such collectors.

**`dijkstra-white-alloc-without-rescan-leaves-live-white`** (`dijkstra_whiteAlloc_run_from_initMark_leaves_live_white`):

- Escape hatches that avoid freeing the newly allocated live object under an insertion barrier are: (1) a final root `rescan` followed by a collector-only `ScansOnly` drain (positive control and `dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`), (2) disallowing white allocation while also preventing unshaded white pointers from entering roots (e.g., shaded root loads, `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`, or barriered root writes, not modeled here), or (3) a fixed-root architecture in which newly allocated cells are linked only through barriered heap stores rather than unbarriered root allocation (not modeled or proved here).
- The Yuasa barrier with white allocation fails in the same way (yuasa_whiteAlloc_run_from_initMark_not_allLiveBlack).
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`dijkstra-unshaded-loads-without-rescan-leaves-live-white`** (`dijkstra_unshadedLoads_run_from_initMark_leaves_live_white`):

- Escape hatches that prevent losing a live object moved into unshaded roots are: (1) a stop-the-world root `rescan` and `ScansOnly` drain at the end of marking (`dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`), (2) a deletion or hybrid write barrier that shades overwritten heap pointers (`yuasa_traceLoadLost_then_scan_safe`; Go's hybrid barrier when stacks are scanned concurrently is not modeled here), or (3) shading pointers when they are loaded into or written to roots (`dijkstra_shadeLoads_traceLoadLost_then_scan_safe` and `shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`).
- Black allocation alone does not remove the need for a rescan under an insertion barrier with unshaded loads (this card: cfgD0 allocates black only).
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black`** (`allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark`):

- In this model, 'the Dijkstra barrier is safe without a rescan if new objects are allocated black or grey' is false unless root loads are also shaded (dijkstra_unshadedLoads_run_from_initMark_leaves_live_white).
- In this model no heap write barrier is needed alongside shaded loads and non-white allocation because every heap store writes a pointer the mutator holds in its roots, which `RootsNonWhite` keeps non-white. If the mutator could copy a pointer between heap fields without loading it (for example a bulk pointer copy that bypasses the load barrier), the strong invariant can break without a heap barrier (one step: shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong) and a reachable object can be left white at the end of marking (whole cycle from a root snapshot: shadeLoads_nonWhiteAlloc_unheld_store_cycle_not_allLiveBlack).
- Allocating black without shading initial fields is covered here because `alloc` requires `Isolated s a` (no pointers into or out of the object at birth, modeling zeroed memory); its fields are populated later by separate enabled `store` steps of root-held, hence (by `RootsNonWhite`) already non-white, pointers, so no heap write barrier is involved. If a runtime initializes fields of a newly allocated black object directly with pointers to white objects that bypass the load barrier (pointers not held in the roots), black allocation can lose a reachable object (one step: shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong; whole cycle from a root snapshot, ending with no grey object and a reachable white object: shadeLoads_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack). For the state update alone, starting from a state s that satisfies the strong invariant: if also every root of s is non-white (RootsNonWhite s), allocating an object black whose initial fields point only to objects held in the roots preserves the strong invariant (strong_alloc_black_of_successors_held); allocating an object grey preserves it (strong_alloc_grey); and allocating an object black whose initial targets are all non-white preserves it (strong_alloc_black_of_successors_nonWhite); a whole cycle whose step relation admits such allocations is not studied here.
- `AllLiveBlack` expresses soundness (`Live s y → s.color y = .black`), not completeness: unreachable objects that were allocated black or shaded before becoming unreachable remain black (floating garbage) until a subsequent cycle, and starting a new cycle requires resetting or flipping black marks during sweep. (Example of floating garbage: floatingGarbage_yuasa_run. Sweeping and later cycles are not modeled.)
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.
- Any connection to a production collector (Go's hybrid barrier, a JVM or JavaScript collector) is a modeling bridge, not a consequence of this result; the result neither establishes nor refutes any claim about such collectors.

**`scans-only-run-length-at-most-mark-measure`** (`length_le_markMeasure_and_le_two_mul_of_scansOnly_run`):

- markMeasure s = 2 · #white + #grey is markMeasure_eq_two_mul_countWhite_add_countGrey; markMeasure s ≤ 2 · n is markMeasure_le_two_mul.
- A single scan of a grey object strictly decreases the measure (markMeasure_scan_lt; its greyness premise cannot be dropped: scanning a black object of a 3-object state leaves the measure unchanged, scan_black_markMeasure_eq).
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`scans-only-run-to-no-grey-exists`** (`exists_scansOnly_run_to_noGrey`):

- Existence of a terminating run, not safety of its final state (that needs the invariants).
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`scans-plus-measure-at-most-initial-plus-alloc-weight`** (`scanCount_add_markMeasure_le`):

- Does not bound non-scan mutator steps; a mutator can run forever without letting the collector scan (starvedCollector_never_noGrey).
- In a run of `Run cfg` from s in which every allocation is black, every allocation weight is 0, so this result bounds the number of scans by markMeasure s, which is at most 2 · n (markMeasure_le_two_mul). When allocation may re-color a cell that is already grey or black in the current cycle (the model's stand-in for fresh cells beyond the initial heap), the number of scans is not bounded by 2 · n: an 18-step run of `Run cfgGreyAlloc` on a 2-object heap contains 6 > 2 · 2 scans (greyAllocCycle_scans_exceed_two_mul_n). For every run of `Run cfg` from s to s' in which every allocation takes a cell that is white in the state where it happens (`AllocTargetsWhite cfg s ops`), the allocation term can be dropped for every allocation color: #scans + markMeasure s' ≤ markMeasure s (scanCount_add_markMeasure_le_of_allocTargetsWhite), and markMeasure s ≤ 2 · n (markMeasure_le_two_mul); starting from initMark, free cells are already counted at weight 2, so allocating them adds no work.
- The configuration range in the plain claim, 'For every configuration (heap barrier none, Dijkstra or Yuasa; any root-load discipline and allocation colors)', is the range of `Barrier = none | dijkstra | yuasa`; under each of these barriers, every heap store and every erase leaves the color of each object unchanged or turns a white object grey (`ShadeLe`; shadeLe_store, shadeLe_erase). Write barriers that re-grey black source objects (`black → grey`), such as card-marking schemes that re-dirty a card, are not modeled; they can increase `markMeasure` on heap stores, and this bound is not claimed for them (not proved here).
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`fair-collector-eventually-black-allocs-eventually-always-no-grey`** (`eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs`, `infinitely_often_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs`):

- This is a termination statement: it does not say the final state is safe; combine it with the safety results for correctness of the final state.
- `InfRun` contains neither `initMark` nor sweep operations: the conclusion means that a single mark phase reaches `NoGrey` and remains there, not that repeated mark-sweep cycles complete. Moreover, `greyAllocCycle_collectorFair_never_noGrey` avoids `NoGrey` on a fixed `Fin 2` heap only because `Op.alloc` is permitted to re-allocate isolated black objects as grey mid-mark without sweeping; when every allocation takes a white cell, fairness alone suffices (fair-collector-white-target-allocs-eventually-always-no-grey). In a growing heap, black allocation bounds collector scan work for the current cycle (`allocWeight = 0`) but does not bound heap growth without allocation pacing (not modeled here).
- In every execution satisfying all three hypotheses the antecedent of CollectorFair is false from every point on (collectorFair_antecedent_false_of_eventuallyOnlyBlackAllocs); the fairness hypothesis acts only by excluding executions such as starvedCollector_never_noGrey.
- No hypothesis on the barrier is needed; every barrier here only shades.
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

**`fair-collector-white-target-allocs-eventually-always-no-grey`** (`eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs`):

- Termination, not safety: white allocation without a rescan can leave a reachable object white (dijkstra_whiteAlloc_run_from_initMark_leaves_live_white, yuasa_whiteAlloc_run_from_initMark_not_allLiveBlack).
- Specific to a fixed heap: if allocation keeps supplying fresh cells (modeled here by re-coloring cells already marked in this cycle), this hypothesis fails and termination can fail (greyAllocCycle_collectorFair_never_noGrey).
- `InfRun` contains neither `initMark` nor rescan nor sweep steps: the conclusion means that a single mark phase reaches `NoGrey` and remains there, not that repeated mark-sweep cycles complete, and not that heap occupancy stays bounded (allocation pacing is not modeled here).
- In every execution satisfying all three hypotheses the antecedent of `CollectorFair` is false from every point on (collectorFair_antecedent_false_of_whiteTargetAllocs); the fairness hypothesis acts only by excluding executions such as starvedCollector_never_noGrey.
- Under `InfRun` and `WhiteTargetAllocs` alone (no fairness), only finitely many allocations are grey or black: from some point on every allocation is white (eventually_only_white_alloc_of_whiteTargetAllocs). So the card covers executions with unboundedly many allocations only when, eventually, all of them are white.
- Toy model: a finite Boolean pointer graph with no fields (two fields of one object that point to the same target are a single edge), a root set abstracting registers and stacks, and atomic steps (each barrier runs atomically with its write). It says nothing about multi-threaded mutators, weak memory, per-thread stacks, fine-grained interleaving of a barrier with its write, copying or moving collectors, or sweeping.

### Escape hatches

Which hypotheses or modeling choices, if dropped or changed, defeat a counterexample result or a
theorem (each item cites the kernel-checked theorem that shows it):

- `no-barrier-unshaded-loads-leaves-live-white`: on the same 3-object heap and 6-step trace the
  object is not lost under the Dijkstra barrier (`traceLostObject_dijkstra_unshadedLoads_not_lost`),
  under the Yuasa barrier (`traceLostObject_yuasa_unshadedLoads_not_lost`), or with shaded loads
  (`traceLostObject_unbarriered_shadeLoads_not_lost`); with any of the three, the trace followed by
  a scan ends with every reachable object black (`dijkstra_traceLostObject_then_scan_safe`,
  `yuasa_traceLostObject_then_scan_safe`, `shadeLoads_traceLostObject_then_scan_safe`).
- `dijkstra-white-alloc-without-rescan-leaves-live-white`: a final root rescan followed by a scan
  restores safety on the same run (`dijkstra_whiteAlloc_then_rescan_safe`); in general, see
  `dijkstra-rescan-and-paused-drain-no-grey-implies-live-black`.
- `dijkstra-unshaded-loads-without-rescan-leaves-live-white`: on the same trace, shading the loads
  (`dijkstra_shadeLoads_traceLoadLost_then_scan_safe`) or using the Yuasa barrier
  (`yuasa_traceLoadLost_then_scan_safe`) restores safety after one more scan.
- `yuasa-barrier-breaks-strong`: the Dijkstra barrier preserves the strong invariant for every
  enabled step (`strong_preserved_of_dijkstra`), with a non-vacuity witness on the same state
  `sChainR` (`strong_preserved_of_dijkstra_nonvacuous`).
- The preservation and whole-cycle theorems quantify over the generated relations `Step cfg` and
  `Run cfg`, and their enabling conditions carry weight. A step that violates one enabling
  condition can break the conclusion: a non-isolated allocation
  (`dijkstra_unisolated_alloc_breaks_strong`, `dijkstra_unisolated_blackAlloc_breaks_strong`,
  `yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak`,
  `shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong`), a store or load of an unreachable
  object under the Yuasa barrier (`yuasa_store_of_unreachable_breaks_weak`,
  `load_of_unreachable_breaks_rootsProtected`), or a store of a pointer not held in the roots
  under a load barrier (`shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong`). The
  whole-cycle counterexamples listed in the `hrun` rows of the cycle theorems each violate one
  enabling condition of one step (described in the witness class of that row).
- Termination: dropping collector fairness (`starvedCollector_never_noGrey`), the allocation
  hypothesis (`greyAllocCycle_collectorFair_never_noGrey`) or the enabledness of scans
  (`unenabledScans_collectorFair_never_noGrey`) admits an infinite execution that satisfies the
  other hypotheses and has no point after which no object is grey and no scan occurs; each of
  these executions has a grey object in every state, so it also refutes the conclusion of
  `infinitely_often_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs` (for the enabledness of
  scans this is stated by `unenabledScans_collectorFair_not_infinitely_often_noGrey`). Dropping
  the allocation term from the work bound fails for a 2-object, 6-step run of
  `Run cfgGreyAlloc` (`allocWeight_needed_greyAllocCycle`), and with re-coloring allocation the
  number of scans is not bounded by `2·n` (`greyAllocCycle_scans_exceed_two_mul_n`: an 18-step
  run of `Run cfgGreyAlloc` on a 2-object heap with 6 scans); in every run of `Run cfg` in which
  every allocation takes a cell that is white in the state where it happens
  (`AllocTargetsWhite`), the allocation term can be dropped
  (`scanCount_add_markMeasure_le_of_allocTargetsWhite`).

### Hypotheses with `unknown` tightness

None. Every hypothesis of every result is `tight`, with a named, kernel-checked counterexample in
which all other hypotheses hold and the conclusion fails; the class of each counterexample is
recorded in the ledgers.

### Stronger or adjacent statements not established here

Each of these is **not proved** in this package (status: *not examined* unless stated):

- Safety of Go's hybrid barrier, or of any discipline in which thread stacks stay grey and are
  scanned concurrently with the heap (not modeled).
- Preservation of the weak invariant when a newly allocated object starts with pointers, for
  example by allocating it grey or by shading its initial targets (*unknown*; not proved here).
  For the strong invariant, what is proved is a set of state-level lemmas about the update
  `alloc` in a state `s` that satisfies the strong invariant: allocating an object grey
  preserves it (`strong_alloc_grey`); allocating an object black whose initial targets are all
  non-white preserves it (`strong_alloc_black_of_successors_nonWhite`); and, if also every root
  of `s` is non-white (`RootsNonWhite s`), allocating an object black whose initial targets are
  all held in the roots preserves it (`strong_alloc_black_of_successors_held`). A step relation
  that admits such allocations is not studied here.
- Completeness of marking (that every unreachable object is eventually white and freed):
  `AllLiveBlack` expresses soundness, and an unreachable object can be black when marking ends
  (`floatingGarbage_yuasa_run`: a 2-object heap and a 3-step Yuasa run that ends with no grey
  object and the unreachable object `1` black); sweeping and later cycles are not modeled.
- Termination of repeated mark-sweep cycles, bounds on heap occupancy, and allocation pacing.
- Any statement about several mutators, per-thread roots, weak memory, non-atomic barriers,
  moving collectors, weak references, finalizers or native handles.
- Quantitative bounds other than those of `scans-only-run-length-at-most-mark-measure` and
  `scans-plus-measure-at-most-initial-plus-alloc-weight`.

### Disproved or dropped statements

None: every result recorded in `results.json` is proved, and no stated result was disproved. The
following natural stronger statements are **known not to apply** in this model; each is refuted
by a kernel-checked theorem in the package:

- "The weak invariant implies the strong invariant": false (`weak_and_not_strong`).
- "The Yuasa barrier preserves the strong invariant": false (`store_yuasa_breaks_strong`).
- "The Yuasa barrier preserves the weak invariant without `RootsProtected`": false
  (`yuasa_store_without_rootsProtected_breaks_weak`: a 2-object heap state satisfying the weak
  invariant and one enabled Yuasa store, under a configuration with no white allocation, after
  which the weak invariant fails).
- "Marking with neither a heap write barrier nor a load barrier is safe": false
  (`unbarriered_unshadedLoads_traceLostObject_leaves_live_white`).
- "The Dijkstra barrier without a rescan is safe": false with white allocation
  (`dijkstra_whiteAlloc_run_from_initMark_leaves_live_white`) and with unshaded loads
  (`dijkstra_unshadedLoads_run_from_initMark_leaves_live_white`).
- "With shaded loads and non-white allocation, the strong invariant is preserved even if a heap
  store may write a reachable pointer that is not held in the roots": false
  (`shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong`).
- "Black allocation is safe even when the new object starts with pointers to white objects":
  false (`dijkstra_unisolated_blackAlloc_breaks_strong`,
  `yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak`).
- "A fair collector always terminates": false when allocation may re-color marked cells grey
  (`greyAllocCycle_collectorFair_never_noGrey`).

## Evidence

### Kernel-check record

Basis: execution (Lean kernel check).

- Toolchain: `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), no Mathlib, no Lake dependencies. `lake build` of the library `Toy` succeeds with no `sorry` warnings; no Lean source contains `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe`.
- Axioms (`Lean.collectAxioms`, recorded in `audit/axioms.json`) over all 570 non-internal declarations of the library: 267 use no axioms; 236 use [propext]; 52 use [Quot.sound, propext]; 15 use [Classical.choice, Quot.sound, propext].sound, propext]; 15 use [Classical.choice, Quot.sound, propext]. Every set is a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Statement and definition-closure hashes (`audit/statements.json`, 132 names): SHA-256 of the Lean `repr` of each declaration's type, and SHA-256 of its definition closure (the sorted, newline-joined list, over every package-local constant reachable from the statement, of the constant's name, the `repr` of its type, and, for non-theorems, the `repr` of its value; theorem bodies are excluded). `support/revalidate.py` recomputes both.

| Declaration | Used by | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite` | no-grey-strong-nonwhite-roots-implies-live-black: result | none | `63416f0c81f08ec02dd2f101d2871654089a6e7aa86354b032b40fb476f35546` | `d7ecf6bc85c4cd97893e531b9e3c44b85becaf403cf2ff155aab9e9b6bb2f098` (16) |
| `allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite_nonvacuous` | no-grey-strong-nonwhite-roots-implies-live-black: non-vacuity | propext | `41720e584dfe1e5fb34c0e3bf28b45a7fbd1efbef30e8a0177c97866bc789798` | `0b442e4129bab8b5ae6423ef13ba1e01842ead4fe9c5a012b116811430378fb2` (14) |
| `strong_rootsNonWhite_and_not_allLiveBlack` | no-grey-strong-nonwhite-roots-implies-live-black: counterexample for `hng` | propext | `f5f0001aed0063b142d7d55ff30f592123cf70e5c563f163f06ddd80dcc78eb6` | `e8c0080486586fd2e8b3e14eb7f34a5959e3679bd7597f6c688a37422a8b9342` (17) |
| `noGrey_rootsNonWhite_and_not_allLiveBlack` | no-grey-strong-nonwhite-roots-implies-live-black: counterexample for `hs` | propext | `ccd393434bc77902cc235fecee36d87abac1020fe47b4499c25ae16833ed5aac` | `66b8e9744235cadeb38b4d46e92f7ef1918f55c8eb9585bf71c3fdc9bc357bd7` (17) |
| `noGrey_strong_and_not_allLiveBlack` | no-grey-strong-nonwhite-roots-implies-live-black: counterexample for `hr` | propext | `d7ce6ac7465ba1c38bdf731360988b181b6e19d2a0c8daee0bec4aaa4a6bd2ed` | `6726198e7b87d96463c87780a3511763c0202f31449f74910bd5bcedcec20cd1` (17) |
| `greyProtected_of_live_of_white_of_weak_of_rootsProtected` | weak-and-roots-protected-imply-live-white-grey-protected: result | none | `d76b808e3313d1686afd1d1fe7f4fa2c56685fe13de308b317a2db8558400480` | `1bf5181e244c79738512ceb924cac764dbf81aad129c11f2f55f06a3821bd5c6` (17) |
| `greyProtected_of_live_of_white_of_weak_of_rootsProtected_nonvacuous` | weak-and-roots-protected-imply-live-white-grey-protected: non-vacuity | propext | `1a67bea03536dd6b29fed267c3a2e7e2649046c0127512ec3935bbe53bbed66f` | `56f41d204027752b567a343c6afee5c81dafe241735376ae0b8a0e686794a0d9` (19) |
| `rootsProtected_live_white_and_not_greyProtected` | weak-and-roots-protected-imply-live-white-grey-protected: counterexample for `hw` | propext | `fbe1759c9d878486b26cc89e00312329cb979fbe60aef4d7fcf572824237ba11` | `164eb7faca6645154c58ac95edbca78dd04cabcdbf53903e199e5d77696f4037` (18) |
| `weak_live_white_and_not_greyProtected` | weak-and-roots-protected-imply-live-white-grey-protected: counterexample for `hr` | propext | `f3122cf0519abf9142346e2951c7e9e1019a07335b7e45f59accd8aa3aba38a7` | `6633efad73e01d6eeaf360b2c63bb1602d06f5430eba922465475b52645ee96d` (18) |
| `weak_rootsProtected_white_and_not_greyProtected` | weak-and-roots-protected-imply-live-white-grey-protected: counterexample for `hy` | propext | `eeddaf26318af2fd03e42ab73404c2a3394274ab8bb67482a979b1ab3723c21d` | `5f7a78e3cdfa67251a35e93a5c53e3d465e29a88c6f35d70bae25936e7d738f0` (16) |
| `weak_rootsProtected_live_and_not_greyProtected` | weak-and-roots-protected-imply-live-white-grey-protected: counterexample for `hwh` | propext | `2ec1d38643f62275b411fe81f79f4a56149fb0f5e398eb576d8b485aca74d791` | `6f52d37cd4b18bba1e0059c7d4c81a1f674c4ec49720796e150836889b008bf0` (19) |
| `allLiveBlack_of_noGrey_of_weak_of_rootsProtected` | no-grey-weak-roots-protected-implies-live-black: result | none | `68f6b6ce31d20bbfd10c3af25dba3b3e95452a79736ed5c77bfdf879a351668a` | `968366ce472f51ed64a35e5b3946d4f191c7225e64a16506053ce1e1a04c4489` (19) |
| `allLiveBlack_of_noGrey_of_weak_of_rootsProtected_nonvacuous` | no-grey-weak-roots-protected-implies-live-black: non-vacuity | propext | `dcf62f678fb19a4afd1e0b52510deb2fccf576830f71640c0a554f1fd60336ea` | `35f03dfbf06513c3981cb695a3697018733097ddcddafe7eb8a188b528698a36` (17) |
| `weak_rootsProtected_and_not_allLiveBlack` | no-grey-weak-roots-protected-implies-live-black: counterexample for `hng` | propext | `6a3758be01c66e948395e605a8b7ad9260960466280d28854c77c65b7332f762` | `2386a2d105c2b57d6aaf0f3b7740889390b0a4ecec362dcfc5486d5b026dbb08` (20) |
| `noGrey_rootsProtected_and_not_allLiveBlack` | no-grey-weak-roots-protected-implies-live-black: counterexample for `hw` | propext | `d8a27bfb360d5df395b176e2580bf93474429b5dd2dd5038f2043002c661fc31` | `67ad0ebf03b4cff927d3cca9132937327c92a202d1a06973708d8b74083958c7` (20) |
| `noGrey_weak_and_not_allLiveBlack` | no-grey-weak-roots-protected-implies-live-black: counterexample for `hr` | propext | `991f3232eb2d6809b3b873910295e46b25fbb1c9b3a05677d7939f4cc4a17643` | `75e7c428a47fff5dd808fe1f3db15dce9f90201a8a39af281e65b164752fe0b3` (20) |
| `weak_of_strong` | strong-implies-weak: result | none | `2083ad724d4f0f6ea4dbce5ccdca357b33143f28388789d645ea48c2122d938a` | `08ade748e58488e5dd5e56705f9ce89fdc5eeeae9c8b675cda6715207757d006` (13) |
| `weak_of_strong_nonvacuous` | strong-implies-weak: non-vacuity | propext | `e886c01cf1111cf5f58e297586d3c654c418b5af749725acfa8fc9538008ef6a` | `8e5c94723a5cef140d26cd64de323df12035613371003943ae76e49ac63807e5` (11) |
| `not_weak_sBlackWhite` | strong-implies-weak: counterexample for `hs` | propext | `91422f6d47ddc939f7a602beab1ccc197f2d244fe09b65128885728a11cc9579` | `cd432715641059831873f8713683c76e9350524ec63fe7b143bd7c6aa09a15cc` (14) |
| `strong_preserved_of_dijkstra` | dijkstra-barrier-preserves-strong: result | propext | `61a270b0a228c9d394d010692ebe977c9f92f9ccdfe3d0b26ea5dd887068712e` | `6f4f11245a0ccb836f257f0951cc1ddb7f425fbee2460bb9473b403c73d0cb05` (57) |
| `strong_preserved_of_dijkstra_nonvacuous` | dijkstra-barrier-preserves-strong: non-vacuity; yuasa-barrier-breaks-strong: positive control | propext | `1d594945c105060823f7fc380a27fa09827a8cebf2d1788bc69c71b3ca627239` | `f21d90f9e60d8e0d5218f15034200d93229736d79aeaa1f9c703f555633d8c4f` (60) |
| `store_unbarriered_breaks_strong` | dijkstra-barrier-preserves-strong: counterexample for `hb` | propext | `b46ce60f2a1ce4dcc8d44b96ff61046ff1ec8cf94979e3c46c29df43e78049fe` | `1e46902dac960065c49d4804172e2ac50079eb4f7c743f77e8d7722bb463ea35` (60) |
| `store_yuasa_breaks_strong` | dijkstra-barrier-preserves-strong: counterexample for `hb`; yuasa-barrier-breaks-strong: result | Quot.sound, propext | `41a0cf98bfd2479ab009e28416be8fcece65b77f2c00c0024cc18c1890f34217` | `d412565bde7c4e13d30f6615a7ad2d62fca248743c849ccff2a0a3ae07d0f9f3` (65) |
| `dijkstra_step_from_nonStrong_not_strong` | dijkstra-barrier-preserves-strong: counterexample for `hs` | propext | `8512604b3d4fd71caf601ec8ec694de38f85131d7e4157f5f9833ac54c22b380` | `a1a759f5b96523f86b87cc56169cec5f9ee5557543485c1179b448a2e578114a` (60) |
| `dijkstra_unisolated_alloc_breaks_strong` | dijkstra-barrier-preserves-strong: counterexample for `hstep` | propext | `990c1aec2105491bb38781db99a06d341d4f4e55efdc85155d38686dde809933` | `3e247cbab9a74fc07457dfc48147cbd5f92bdc23e78d92cff1c6e87bc3ec0511` (59) |
| `dijkstra_unisolated_blackAlloc_breaks_strong` | dijkstra-barrier-preserves-strong: counterexample for `hstep` | propext | `0caae8659fd5d3f921f23ba29c95fc3112db834f71d9c0f029c089a94f73e4f2` | `e5a858a0cfaece0ad64af5e2a4f6179ab25ba1124b879ac21b23878f5f75e02c` (59) |
| `weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: result | Quot.sound, propext | `2be95e8dbf2474f066608c173e7ec46f5d91dd29c540c582863704369c46c7b0` | `35dddbfd45e737867351d51337687d1de32f212326e0a00deea0ccdb8d9a1e1e` (61) |
| `weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc_nonvacuous` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: non-vacuity | propext | `f9f0420707ce995882f801d1dc4f8778a3aa55e7cfae6eaf58f611da0fa1f7d6` | `62e5c95e653e11cbfd2ac9ac67e370f130913e63cccaff8661653bce821cfb05` (64) |
| `erase_unbarriered_breaks_weak` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: counterexample for `hb` | propext | `b65735ff5c80fa8b5d4e56547a9ceaa020fbab6ffc0dfb39912ea4cb679132fc` | `7f596c52c85fe977c21bccac1f5a6e445df3f221c736d3d65a20af572e5f4097` (64) |
| `erase_dijkstra_breaks_weak` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: counterexample for `hb` | propext | `f7e42ac730d0bb5093f3f68a5e8ac6d2276dad432c04c1bd1e45111b6941132b` | `b3ab76fecf9ae9be0e0d8fcf2d791fbaba224688a1fc8ebf801105108e333db5` (64) |
| `alloc_white_yuasa_breaks_rootsProtected` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: counterexample for `halloc` | propext | `9f848c66d90a703027643ed9b458a3481d77962e011fd9f2556ec95c9793b2e7` | `d50ea2fd726e4bef97bf7c19a450a6d6d3b4f5f431bf27c6fc9e99ae0317fc3c` (64) |
| `yuasa_step_from_nonWeak_not_weak` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: counterexample for `hw` | propext | `37d54f0c72c9973f4ed495e7013dbd5f795e807721fcc10d1d56a96ef5df16b2` | `f85fce465c9806a281489b9a94b4aba6428aec659ef26f3186630a38d81aed7b` (64) |
| `yuasa_store_without_rootsProtected_breaks_weak` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: counterexample for `hr` | propext | `20f009f089c01443ec9cb13147c6e74399bf31769142fc4fac2cd50548b07660` | `7d3424352bc23f36f9811ff9afea5bb5ab55930f66486828c28a518d005782f2` (64) |
| `yuasa_store_of_unreachable_breaks_weak` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: counterexample for `hstep` | propext | `7e3ba0b84c97023829da1edfd0ece95d6dce400e763dc22fb47d2e1e70d8d716` | `c5fba0e4dfdddd5679d38479c8301df29d04cc2ccdca5a93c4ce7463df372937` (63) |
| `load_of_unreachable_breaks_rootsProtected` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: counterexample for `hstep` | propext | `b11636bcd82d6e32bd627f807819884ee74c109015537ebba0a30d3be4a80343` | `c5fba0e4dfdddd5679d38479c8301df29d04cc2ccdca5a93c4ce7463df372937` (63) |
| `yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: counterexample for `hstep` | propext | `2cba078e27c52c2ee7e55f947d88c96015216fd503228036bf548642b500bcff` | `55406960c71c47f244f39fc534466c697352a0289337f8c65693bded098854e2` (63) |
| `rootsProtected_alloc_iff_ne_white` | isolated-alloc-preserves-roots-protected-iff-nonwhite: result | Quot.sound, propext | `8edf385cfc17f71e4d09d68f2f6130caabf9db59ce015a046ccb04dd15e1a49e` | `414ee36b1f81ae5c31b0d7c32679bdf620573f00ce5321e2263120a82fc859fd` (15) |
| `rootsProtected_alloc_iff_ne_white_nonvacuous` | isolated-alloc-preserves-roots-protected-iff-nonwhite: non-vacuity | propext | `e47ae619e0300ffa4711b23b8a0bfaa9b783d8e947cfde3de0b3282616a3ab7a` | `dcf715dde4bea8999fd2bfe0864da2d473fe584fe4caf2ef5f95549ec897f9d1` (16) |
| `isolated_and_not_rootsProtected_alloc_black` | isolated-alloc-preserves-roots-protected-iff-nonwhite: counterexample for `hr` | propext | `ec9cc266378d7401c76c0b728416763e37e0d78b9d786fd4be064eb0d43acacd` | `9b49639f1dbc9f21a0092a171af12f49def48f31eab9fc15ff3162282466fff9` (17) |
| `rootsProtected_alloc_white_of_not_isolated` | isolated-alloc-preserves-roots-protected-iff-nonwhite: counterexample for `hiso` | propext | `f394bf0d823c30a925af88143a0d454b60ae5b5ae7cb3e799f4a649abe496ce4` | `ee50c3e57b59dcbf483ccee6606bb87c2dd0aba2f1865858b5e11a17112603a4` (17) |
| `allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: result | Quot.sound, propext | `11b4f5ec5f788d66f098c833a0ccd9d2ea2ff1aa2adadbad9a63b486e5c67867` | `cc0188b314cbc77069e976692c92a3327f9a49962214a37566dd01a033e06e56` (61) |
| `allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark_nonvacuous` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: non-vacuity | propext | `bf7ebc659e3b698d26403e6a0ab48914953eba94c00d61245cc133e19c501e6a` | `7320d11509aa14bccc50436b110bf570617a3fe7517254800352895d367defbd` (66) |
| `unbarriered_unshadedLoads_blackAlloc_run_from_initMark_not_allLiveBlack` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hb`; shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hsh` | propext | `1c78912500ccbcc652cf447cbf8851980deef2750c5407188eee184eecdfeefb` | `cd008c5435acd223e8691bc2010329bd8d21686844fd9e9225ce3248768b0c1a` (68) |
| `dijkstra_unshadedLoads_run_from_initMark_leaves_live_white` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hb`; dijkstra-unshaded-loads-without-rescan-leaves-live-white: result; shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hsh` | propext | `8f2a069e8641391a8980e4de7562d294d9d49b83acabc712a621fe8895e832de` | `98317146e920b1241cd4075e15eef4a5c7bc468159e8a3a20ab19b85b35cdea9` (67) |
| `yuasa_whiteAlloc_run_from_initMark_not_allLiveBlack` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `halloc` | propext | `aac3e98dd8f06187c80e2eaa484de1e52d648fdb43640298cff78440d24a206b` | `91a6f62cc6bac9b2adddde6ce0fd8e8b5271433358dad60e1727fdd971793f70` (68) |
| `yuasa_run_not_from_initMark_not_allLiveBlack` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hrun` | propext | `34f6d198bb6fbf0266f858a603696fe9fbc2b263d0115ddbb368c38c282cc6ee` | `5c891b15e1c30fcc0c63bb6a9bc9aa8ab19d4149d72dbaeba8ae127b177c65bb` (64) |
| `yuasa_store_of_unreachable_cycle_not_allLiveBlack` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hrun` | propext | `c1b359696b84796362602e776d9effba8939ac159683bdac730a05cf13d4b11b` | `ba89f87be87777363b537223ae94a0e9bc7185d6e46cfcdbc698fb1a03654d32` (65) |
| `yuasa_load_of_unreachable_cycle_not_allLiveBlack` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hrun` | propext | `114a18628bcf1b4108094130b929db1aec0d5556cf8798368ff725b1e6f6b85a` | `ba89f87be87777363b537223ae94a0e9bc7185d6e46cfcdbc698fb1a03654d32` (65) |
| `yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hrun` | propext | `28f6d9f56f352a83b2097efa02dadda14984412fb5cad1afcb6956fa86623619` | `132cf5eaeb5f4747d4fd709fdedb18e44fcf25040434cd4e75f50a6e6ce71220` (67) |
| `yuasa_run_from_initMark_with_grey_not_allLiveBlack` | yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hng` | propext | `81d827f765b5c66689326bd913746649fda91c764272c1e5d239f5577c77a07a` | `269af017963443ba80a78d1521cea1dbf737c606aa7aad4a32d8f3f38567aa3c` (63) |
| `unbarriered_unshadedLoads_traceLostObject_leaves_live_white` | no-barrier-unshaded-loads-leaves-live-white: result | propext | `345ac34be56d8727f49b46afdedbaba9240370fbcafa3e6ad9a2a593d3afc532` | `a55385bd6d13e885a72c828a877a75977ae52935beac7a778a5d935395ec3759` (65) |
| `dijkstra_traceLostObject_then_scan_safe` | no-barrier-unshaded-loads-leaves-live-white: positive control | propext | `2b7a51f8231bf3e28399cdcddc7e236dc9df7df56e8cf34759c3f0324a27010e` | `f45a647dcfe4f2a44c080881dff1ae842cadf9f21880ef3b473ae00c3c5c4e26` (67) |
| `yuasa_traceLostObject_then_scan_safe` | no-barrier-unshaded-loads-leaves-live-white: positive control | propext | `5ffa6e9bdb59033c8c199950eace557e9f41c3e88f2d20e295465088bc76c564` | `22e9370d15da7554a4737aab3d5e0373f8b673c8379821dda633c9c4a22c18fe` (67) |
| `shadeLoads_traceLostObject_then_scan_safe` | no-barrier-unshaded-loads-leaves-live-white: positive control | propext | `d73210c15349fc151fcae5b42bf9ca7716ad293c5f1f5eb65796a6cbba2b0f0f` | `e6c05e99d3622536ae766051d13b6966991aeaff93a17ab225214d263d47edd0` (67) |
| `traceLostObject_dijkstra_unshadedLoads_not_lost` | no-barrier-unshaded-loads-leaves-live-white: counterexample for `hb` | propext | `225b23ebc1e38f5ec5f6445bd3cd328791253f29718e61cd858ec91996aa372e` | `679a3b18e1269ee8c970d8b17c8cbed8c5cea871d65398b6ea1f73a53c414a8e` (66) |
| `traceLostObject_yuasa_unshadedLoads_not_lost` | no-barrier-unshaded-loads-leaves-live-white: counterexample for `hb` | propext | `76dca7eb862fb5e968191c1ce6ab888c2322a1a56d83907e66ec7ddc409d23f7` | `7320d11509aa14bccc50436b110bf570617a3fe7517254800352895d367defbd` (66) |
| `traceLostObject_unbarriered_shadeLoads_not_lost` | no-barrier-unshaded-loads-leaves-live-white: counterexample for `hsh` | propext | `de405365c874549378eecb44ab2e490843f9123b0714dae349034f6dcdcae9b6` | `8ff954f422c898edb812d46fcfff7771102eaf742954aa724f87458a9aa9be2d` (66) |
| `allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: result | propext | `e92b4eb14d8eda08e39560de4fc99be216428683401bf030c1e6b19d4a707f76` | `92e2411930505d735ab20a860b368f3fb6e3237e2a91ee8de947a3fd96406514` (67) |
| `allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run_nonvacuous` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: non-vacuity | Quot.sound, propext | `41c2fe3e036ba02bca8b1d928dc1ad6c1f0b2cc2b604432a059b63ec6a7ee230` | `997141953cbc769fe27de3e8c0af0139923fbcac52ab728a93fc77cc9f5eb89a` (73) |
| `unbarriered_run_rescan_not_allLiveBlack` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: counterexample for `hb` | propext | `17586cee707e8ba87121885ae105a411e7cd5b5e0f2f6e70d3554400605ccdc9` | `2adbc104acb835a66bed2c848efe2d7c2067e7f1208ee048cc4ed3d7b775dd7b` (74) |
| `rescan_from_nonStrong_not_allLiveBlack` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: counterexample for `hrun` | propext | `156131c027f271f5ed0032599031f65423445547514f52bf0f0cb32f6d139d0f` | `cca7ed231c7ddc311ff203cdcd2bf6eae34e0a15ff32142033470dccf08d4b22` (70) |
| `dijkstra_unisolated_alloc_cycle_rescan_not_allLiveBlack` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: counterexample for `hrun` | propext | `4b7084840eb019cf0f5164493f6c68cc8f7a3ad3ba66e81c9444f5b3e4fdaf03` | `0baf194b71b40276485e0e50a710609d6f1ad5b73945ef467886c4f542c882e6` (73) |
| `dijkstra_run_without_rescan_scansOnly_not_allLiveBlack` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: counterexample for `hrem` | propext | `b9eb2bd5965a709c741b95b3629c3dd539cdab82d58ae80d768724f98316deaf` | `d11b45da81d04a6874799d609ba630a77a2c1ac4803fdfa5c7b0fd3e968b69f3` (73) |
| `dijkstra_rescan_then_mutator_not_allLiveBlack` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: counterexample for `hscan` | propext | `b10b54f3406a05ea19be3c9e1f0984f91cdd24215e2c30f25be680ebfa5edf1b` | `ee623efaf151f3ee3c08382cbb19368dfc0497898c0884b612514285640bbef2` (75) |
| `dijkstra_rescan_with_grey_not_allLiveBlack` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: counterexample for `hng` | propext | `8e68b2f16425a5cfaf4d802419872f893d04b16a4c10330fd3c5a58fe539d91f` | `3f7c0037d820740274d7d9e3a392fac83d42d1de30b971133d7a130e53d9e875` (69) |
| `dijkstra_whiteAlloc_run_from_initMark_leaves_live_white` | dijkstra-white-alloc-without-rescan-leaves-live-white: result; shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `halloc` | propext | `4e1b1f2ebcf799c311f9469d755d4d3f2c206a38c73ae8c811d16f756c46ba8e` | `540c8bd46a469b3ae6280ae5ea4453c8951a35017db862d1a3c0938febdf4492` (67) |
| `dijkstra_whiteAlloc_then_rescan_safe` | dijkstra-white-alloc-without-rescan-leaves-live-white: positive control | propext | `e2df25842a373fb5e52ce17d40baf87ebd6387f8f0057f7ab1a34a95484c34c7` | `2f7d399da46c0f7cba1164c3eab0dbdf892794c50939506bd02f51615b4bb1ff` (69) |
| `dijkstra_shadeLoads_traceLoadLost_then_scan_safe` | dijkstra-unshaded-loads-without-rescan-leaves-live-white: positive control | propext | `ab0916729523ea2e2a976399bc36065c615aab16e401bacbeecb4062b7b1db85` | `c0cbbdfe264e40bacf002ef262d2560db350be6ebb75dc02cf77ce58a26561ea` (67) |
| `yuasa_traceLoadLost_then_scan_safe` | dijkstra-unshaded-loads-without-rescan-leaves-live-white: positive control | propext | `9e8e7d9c5af6d856e87a2c637910acb6242ef2d8e0382ae7743c16e7082a6927` | `b0aa39897fb2a48c887512ae93df6e05d205425dbfab1f90f2d6c3f28fe6f926` (67) |
| `strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: result | Quot.sound, propext | `72e25f978aae0a933edd2b684728bca45164daa44f8528d65c81b5ad48391ac3` | `fc5e211aad55f952923a989d4962cdfc154987985e723fd133fd1a1d236921df` (58) |
| `strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc_nonvacuous` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: non-vacuity | propext | `393b3d38b66ade29b2a342767ced328de8344c9be9bfedcdc93650faf54723ac` | `11198c94219372ba6c1ee42a604060b763d67b91c6a6d1335c6bef9b585a33b5` (61) |
| `unshadedLoad_breaks_rootsNonWhite` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: counterexample for `hsh` | propext | `d347c64587aa86ff19f306cdc4a7aeaeee774c3293358f6c052b992e8c6b07de` | `8e763086ac9aedbc2ef78f7ebb68a3fd9e163f93a0da131442ce5e2b6cfc5fa6` (61) |
| `shadeLoads_whiteAlloc_breaks_rootsNonWhite` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: counterexample for `halloc` | propext | `cd8849e831a8b6d0dfe4c807cc5ea5bc07dc8e31ffbc3a36b4b76fb952e19397` | `3bd7dfaef5314552ad35fe8cc7129b3b4ba8be261ca5421d489c2d93b330f201` (61) |
| `shadeLoads_step_from_nonStrong_not_strong` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: counterexample for `hs` | propext | `1421e10d57afa13ca3890cd02d8e1162d708ad44fa86f12bd9d2b8bce2fd4376` | `d9054e575b0b720fdcbc30d966b95d4778db9503a8827f76f5e91a2a7fb3c7f8` (61) |
| `shadeLoads_store_of_whiteRoot_breaks_strong` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: counterexample for `hr` | propext | `d6507eca1c89dd3da4954794f3daea2e731e943b7ac20397359fcb1390e18f8d` | `c7829de21cf1d7e31a6700ca6f3bb1b3e61e119d4e443b3980b2f414477b40e7` (61) |
| `shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: counterexample for `hstep` | propext | `d3dfafdf42c7a53fe63a14d2bdaa348696ce2c78fa6e0849adcd022e6cf0ed44` | `c2a53c2c31730e5576aab8322233dadd1d03ba9bc3066fabb5e141ff2ddefc9c` (60) |
| `shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: counterexample for `hstep` | propext | `7fc5082599b3b79fc27633dcdac77cd664110ca27558fdac907879ffa794fffb` | `c2a53c2c31730e5576aab8322233dadd1d03ba9bc3066fabb5e141ff2ddefc9c` (60) |
| `allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark` | shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: result | Quot.sound, propext | `1d41e105108c22ec02f5c3a6b8f19f430f870b715df93c004a249e439658fb58` | `cc0188b314cbc77069e976692c92a3327f9a49962214a37566dd01a033e06e56` (61) |
| `allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark_nonvacuous` | shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: non-vacuity | propext | `e67572c086bf67dc9afdfb5d5eee6d094dacdf144eba47ba30f65c3eccbc7b38` | `8ff954f422c898edb812d46fcfff7771102eaf742954aa724f87458a9aa9be2d` (66) |
| `shadeLoads_run_not_from_initMark_not_allLiveBlack` | shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hrun` | propext | `a86299b00a198e4d1f1bcc81a1de4717c9c7ea79a09db02296ca9e6c226ddf06` | `ed61ead494473d51365b7e50fbeea26db73f29a142e987b2bd56be23ffccf611` (64) |
| `shadeLoads_nonWhiteAlloc_unheld_store_cycle_not_allLiveBlack` | shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hrun` | propext | `1b13f41f9dc1fa8b6e77add22502e14ed154cc38bce809ce92995b2b1b5c2483` | `71c0f8e1381a1dcc293b990d95e53e7f90c00bea37b8cabe9dcc53047d7212fc` (67) |
| `shadeLoads_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack` | shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hrun` | propext | `68f2f434d5adb0c2e87fdadf92ca394f46520afbf09f00a26d581c2b48e02638` | `846608eda4a96b05d98db65d3cc8f03114503f3f56cdb5c6cd509eca0c758b0c` (67) |
| `shadeLoads_run_from_initMark_with_grey_not_allLiveBlack` | shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: counterexample for `hng` | propext | `26ca719a9d53809a0df4e7c11c7802102a3fe91271698cbb66d6d49fff2c6808` | `345eb11018c864b4171aa042f7d32e1018e350fbf03ba9613aa68aca0d1421c4` (63) |
| `length_le_markMeasure_and_le_two_mul_of_scansOnly_run` | scans-only-run-length-at-most-mark-measure: result | Quot.sound, propext | `23375dd8b779bf40d2d91ef2bc816f60a0c8c50ec3291e13e1fcfd167c2683fc` | `7275d67832caa1e16d538262b6ac6d4a2e552b77888bc792fd845079ecc951e0` (66) |
| `length_le_markMeasure_and_le_two_mul_of_scansOnly_run_nonvacuous` | scans-only-run-length-at-most-mark-measure: non-vacuity | Quot.sound, propext | `9f6e237ad3607e40a0ea2f2080b8bbbac7866e4e95ca990f48774628195d0c0e` | `bfb418f39c86142d1ad2a17e97c4d714c625405320f10efd7a1fc5bdade29e66` (66) |
| `length_bound_fails_without_enabled_scans` | scans-only-run-length-at-most-mark-measure: counterexample for `hrun` | Quot.sound, propext | `55f8f39b4c47bd1b0e9d95163041253bd3b8eb4eb09c4be9063c7af9b626f494` | `3c29d0f4c841532c49a8d4743aedb048eb7829a867c5972ee9c77eaeac8bae9e` (70) |
| `drops_run_longer_than_markMeasure` | scans-only-run-length-at-most-mark-measure: counterexample for `hscan` | propext | `807838db4e477d7a17135f4724628881718f802c6f36a53aa511c255ada12a6d` | `7845cf3554852fcb5d618d567bbff371b656289acad43fd00c06d23e733c31fa` (72) |
| `exists_scansOnly_run_to_noGrey` | scans-only-run-to-no-grey-exists: result | Classical.choice, Quot.sound, propext | `c5f75aafed8613be0efd1c95ae022d58b04b9ee82bab6bdfbb4562661ad10b3b` | `fe527dedb46746a5b455a06e27dfb7d86c140f809bf1967fdb1797e669838be1` (64) |
| `exists_scansOnly_run_to_noGrey_nonvacuous` | scans-only-run-to-no-grey-exists: non-vacuity | propext | `3205814f6bf7447421155b82dabb5688bd7955c7b2860b2ad6e32f339b9456f0` | `0c0aa4d4b2b71c938006845ed24cf53b078a3de668eda67fe0f2586dbc635913` (10) |
| `scanCount_add_markMeasure_le` | scans-plus-measure-at-most-initial-plus-alloc-weight: result | Classical.choice, Quot.sound, propext | `35a3d81cc98e9c05056236c489ee76bc0172e97e6995f87bb8e42a18f80b003e` | `c8acada2d08dc3bf4282d0e33f3b4841410ab9b7e2d9d706fd03b0fbe85a21bb` (68) |
| `scanCount_add_markMeasure_le_nonvacuous` | scans-plus-measure-at-most-initial-plus-alloc-weight: non-vacuity | Quot.sound, propext | `d5b1b305ab55582433799a984c20f6ff0d1d3fc35af733636773578a772b5cc9` | `aae5cd34171481fb7f667f370bef0bee089284a61166b5bfdcd16a843b3d86a1` (69) |
| `scanCount_bound_fails_without_enabled_scans` | scans-plus-measure-at-most-initial-plus-alloc-weight: counterexample for `hrun` | Quot.sound, propext | `27db976282dd2e9f411efeb2bc8b2ad246fe866111120970c48f8aa56537bea7` | `e5e16407963ea1d4a189fcbb14216d3d1a7650a2e2dd1b554773c90d47b43ac9` (72) |
| `eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs` | fair-collector-eventually-black-allocs-eventually-always-no-grey: result | Classical.choice, Quot.sound, propext | `be3e11b09e9fc6a9bd07a5ed05a312ed7ecad92fa88644822f64c6594f758a2d` | `6597d1d1296cb220650314f9f0e8b96c042bbe8569dbcde41744cc91d5a2f612` (68) |
| `infinitely_often_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs` | fair-collector-eventually-black-allocs-eventually-always-no-grey: result | Classical.choice, Quot.sound, propext | `6fdd9623a5ac9074bbb1b8794d1fe2a34875b78a01bc881a8651eb3f53b48765` | `6597d1d1296cb220650314f9f0e8b96c042bbe8569dbcde41744cc91d5a2f612` (68) |
| `eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs_nonvacuous` | fair-collector-eventually-black-allocs-eventually-always-no-grey: non-vacuity | Quot.sound, propext | `f5b642be81d792241e86bd6ccfee38488b6a6428a798a668c013d2bb189e0a0d` | `29cbf07a83c523675d10b8412e045001746a40fb2200d3b64bb29dd407461e11` (75) |
| `unenabledScans_collectorFair_never_noGrey` | fair-collector-eventually-black-allocs-eventually-always-no-grey: counterexample for `hrun`; fair-collector-white-target-allocs-eventually-always-no-grey: counterexample for `hrun` | Quot.sound, propext | `d588cbec10380e61444b043365d7e4087ce6bef7417d1b8fbbb9affb2b93824c` | `d73d6ed2168464079848d9463ec8fc59cbfd1ab222a6f64eca29c04100979c49` (75) |
| `unenabledScans_collectorFair_not_infinitely_often_noGrey` | fair-collector-eventually-black-allocs-eventually-always-no-grey: counterexample for `hrun` | Quot.sound, propext | `86e9b576e6608b8efd5ec46fec59ef53e6bd8ca6ed127de3051bc36166dfd712` | `d73d6ed2168464079848d9463ec8fc59cbfd1ab222a6f64eca29c04100979c49` (75) |
| `starvedCollector_never_noGrey` | fair-collector-eventually-black-allocs-eventually-always-no-grey: counterexample for `hfair`; fair-collector-white-target-allocs-eventually-always-no-grey: counterexample for `hfair` | Quot.sound, propext | `1e2d9382c196c83cd57fcff051d2b4684f340f3578e817314279ecef0c0c3b31` | `00dc9b0d9d736dd3744c4178752394200aceaa7da38711c11e79a98e94c0bab7` (75) |
| `greyAllocCycle_collectorFair_never_noGrey` | fair-collector-eventually-black-allocs-eventually-always-no-grey: counterexample for `halloc`; fair-collector-white-target-allocs-eventually-always-no-grey: counterexample for `hw` | Quot.sound, propext | `7acf826e8b13653a459673f4a0f93be892d646c669eeb2ea8d89c7501de5d529` | `af8fda1a9c5af4cdd68dfb0edf24b56c1230aef923d627d39fec78586f0f682b` (77) |
| `eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs` | fair-collector-white-target-allocs-eventually-always-no-grey: result | Classical.choice, Quot.sound, propext | `2782a363b380f32e0c581e77e1c79baa477b686cb84dff0c1b167e6f9cc37d1b` | `33ab6174dfa4ac2d625e6b73de9a255c9bf4aa24de6351bbd5c5a264dc9ad40a` (63) |
| `eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous_with_marking_work` | fair-collector-white-target-allocs-eventually-always-no-grey: non-vacuity | Quot.sound, propext | `aea27eb200350c81b485865bf54f78312cc7970be17079990ea91a75f357e4d0` | `9c0ddd485b1f97383f8ca4ed188aa7d583f1e62c8da5e29a48be85401706318f` (75) |
| `eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous` | fair-collector-white-target-allocs-eventually-always-no-grey: non-vacuity | Quot.sound, propext | `4ba9204a2b0089c3ea7a0750ebf6217d5dbc26631d71fa1ec6afef005d96f479` | `358e9004debe2726d90eb792c742b77b4ef220fa18409de6d3cd690e19af8276` (74) |
| `floatingGarbage_yuasa_run` | no-grey-strong-nonwhite-roots-implies-live-black: cited lemma; no-grey-weak-roots-protected-implies-live-black: cited lemma; yuasa-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: cited lemma; dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: cited lemma; shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: cited lemma | propext | `8cea39602534f49619c6da79e53d96b386fdfce79a0bc097045025d60070c25e` | `ba89f87be87777363b537223ae94a0e9bc7185d6e46cfcdbc698fb1a03654d32` (65) |
| `rootsProtected_of_rootsNonWhite` | no-grey-weak-roots-protected-implies-live-black: cited lemma | none | `9ee9e4b230cd1f75448509a2fa0091c4fd997a13e1cd161c78367850ba693994` | `4cafa2f5aca6c51fe9fa63d3ffbaddf13a9dc25068d098c9c4c44ae175037d8e` (14) |
| `rootsNonWhite_of_rootsProtected_of_noGrey` | no-grey-weak-roots-protected-implies-live-black: cited lemma | none | `fce5c972b5e1bcd5b02ad62a1c44058316ef824c64987ce82d997fe268aa49ea` | `1c8750b4fe7ccefdef981ddec5ea1deae11af2fc6b219932182c3c53ef0fc284` (15) |
| `strong_of_weak_of_noGrey` | no-grey-weak-roots-protected-implies-live-black: cited lemma | none | `1a0b5f03a34c6ea1c1c81b5bf1586a87713ba104864f62fb02cfb65e5650db80` | `42b8d23861a85a8de5b5da6217df5332a060453f89d6eeac20f3e7c98cadc335` (14) |
| `allLiveBlack_of_noGrey_of_weak_of_rootsNonWhite` | no-grey-weak-roots-protected-implies-live-black: cited lemma | none | `bdb678651e2f12fb12799aad0999a5e21979ba09c5a333f72fc33c29899f1952` | `555b65fccdc7011ab4d73966faff3c7e0b17c7103dfd761e5e3aea6ee9aa21bd` (19) |
| `weak_and_not_strong` | strong-implies-weak: cited lemma | propext | `10918c5693d6505a6003f4299ce88f3d350c6b19e6c7def0ee10359d03603c37` | `7fa72e8cae0a415c7f618b076bec4da9ae39f42350abced9dfb172ef0f16317b` (15) |
| `strong_store_dijkstra` | dijkstra-barrier-preserves-strong: cited lemma; dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: cited lemma | propext | `f8a1d6a6c061eed32121182058df0c1f558ccf16eaa2023ac4d7a15b10899f9f` | `f6fda3ceaf37fbfdb70bc20ed54fd58610dd87e1086171134a8cb840f373b68c` (29) |
| `strong_load` | dijkstra-barrier-preserves-strong: cited lemma; dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: cited lemma; shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: cited lemma | none | `eb0a47c4617a02d64648a5f98cd44519a80cf3fcf4aa6e945313482df0c6016e` | `52754a52827ad813bd033cac1e288bba44eaadc35dd5e41154ee997822fb70cb` (18) |
| `strong_alloc_grey` | dijkstra-barrier-preserves-strong: cited lemma; isolated-alloc-preserves-roots-protected-iff-nonwhite: cited lemma; shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: cited lemma; shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: cited lemma | Quot.sound, propext | `2f6db1a8be2eb0277c4730661c44e3c7748c2e92da0fef6fcf60c9b96b31f3fa` | `79625d639d2fa7c1776e2c41bef8b30032ea9a6c787bc9697ca3c48ee959d199` (11) |
| `strong_alloc_black_of_successors_nonWhite` | dijkstra-barrier-preserves-strong: cited lemma; isolated-alloc-preserves-roots-protected-iff-nonwhite: cited lemma; shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: cited lemma; shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: cited lemma | Quot.sound, propext | `43fb28b3eaa1e3b7e5d8e44f9cae0963a169768ab59dd76716d42f36786044a5` | `79625d639d2fa7c1776e2c41bef8b30032ea9a6c787bc9697ca3c48ee959d199` (11) |
| `weak_rootsProtected_store` | yuasa-nonwhite-alloc-preserves-weak-and-roots-protected: cited lemma | propext | `9cbb0cc4a17857f005d45c75ff1c1fc7bb7f97f9ebd974238b10f15cad92b7f6` | `8366df27fb2b00dad572d441730dc91018fe5d5d25c13bfede28b188bd169a7e` (36) |
| `rootsNonWhite_alloc_iff_ne_white` | isolated-alloc-preserves-roots-protected-iff-nonwhite: cited lemma | Quot.sound, propext | `d011631f46a5ab2e0e6b3b01dc14d0d08853807da9763b4313444a50b4c6fae8` | `a54037ca4c57b4ed329e93a2f3b0ebfad7fc6207aac5369dd6791f66b978b256` (11) |
| `allLiveBlack_of_noGrey_of_scansOnly_run_from_initMark` | no-barrier-unshaded-loads-leaves-live-white: cited lemma | propext | `a875c0d85207f0a77132f368e1ee7bdfd28ae06ebdb0bb842794f005617cedf2` | `472546f91ee9deb09712583c940389e79e585cf6185e295ce0d25348ff2ff4b6` (66) |
| `unbarriered_unshadedLoads_heldTrace_reaches_sLost` | no-barrier-unshaded-loads-leaves-live-white: cited lemma | Quot.sound, propext | `d6d6e50495aa1d435890788014f2ebd8dea195a4f0f9767f1cae5295b658c5fd` | `d385d62339b7e80256236ade8f638559af99cd47c0a46841fe0ce43a39d66993` (67) |
| `allLiveBlack_of_strong_of_rescan_of_scansOnly_run` | dijkstra-rescan-and-paused-drain-no-grey-implies-live-black: cited lemma | propext | `f894f7ad0fa9c630b1af1a9a9b601eab4af758aa44c50db44e30f3f30c8c5abf` | `9776501996085a1b0e99b3f4a0ee4f3a8aeb28f6bd1d8a846ede8e7011a8e7f0` (67) |
| `strong_alloc_black_of_successors_held` | shaded-loads-nonwhite-alloc-preserve-strong-and-nonwhite-roots: cited lemma; shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: cited lemma | Quot.sound, propext | `f162b8fbd98f32399fb8f40f79ebf8f509e253a5226ec8445dd6cb110e55bb27` | `47728987fc820ce3fd4e081c82558176e0d30c571b29b41ea408f5bace1215ac` (12) |
| `rootsNonWhite_load_shaded` | shaded-loads-nonwhite-alloc-from-root-snapshot-no-grey-implies-live-black: cited lemma | Quot.sound, propext | `00c4252c8b3bfa6015f748a83453f1999e13476068bdb33091b600509b6c1cc9` | `986d39bc47a93280f8662be10b922fc5970f001a2c0bbe978bd118c006a01c81` (18) |
| `markMeasure_eq_two_mul_countWhite_add_countGrey` | scans-only-run-length-at-most-mark-measure: cited lemma | Quot.sound, propext | `3e92139836170e25206d5ba546f0efd5a8c2b4efd35f51a8f9e9c5c51ce008fe` | `3c95ed1b6638c9269615d8546827013cc627679dd1f470229e38fb493316a2e4` (16) |
| `markMeasure_le_two_mul` | scans-only-run-length-at-most-mark-measure: cited lemma; scans-plus-measure-at-most-initial-plus-alloc-weight: cited lemma | Quot.sound, propext | `3dd19ded505ffd4f49e7b6a19932a826481eae04c4cf20796fe19d429332c683` | `666436f78fe8202d572c21c0467bfaed2b621a10f6645117ba412251a4f4799f` (12) |
| `markMeasure_scan_lt` | scans-only-run-length-at-most-mark-measure: cited lemma | Quot.sound, propext | `d1390d20168076d0c5592a4156ab69bcb05cb2d508367db14352940651fc7a29` | `9497c4c10cd2e056e156d4213404c5f49870f8b8123c2b947c300e6e1f3353f9` (19) |
| `scan_black_markMeasure_eq` | scans-only-run-length-at-most-mark-measure: cited lemma | propext | `1ef52b6e6313123e02b113619fa3ab2ac0485f5eeaef8497276bf5439c5c9d29` | `3162f4237cabc807314efe87402d5a7805ff8049d0479ea8eeb7e840278d17b4` (21) |
| `allocWeight_needed_greyAllocCycle` | scans-plus-measure-at-most-initial-plus-alloc-weight: cited lemma | Quot.sound, propext | `c6f2381d8c57f1ab44b4130873172e140301a3d6e8c313db07d68f665562a267` | `48a20a0e14f15f27e104aa9e6c1ca320640f4008729aae9cbf4b49d501fa3881` (76) |
| `greyAllocCycle_scans_exceed_two_mul_n` | scans-plus-measure-at-most-initial-plus-alloc-weight: cited lemma | Quot.sound, propext | `00203e4726eb8af3c8f8013fe98dcd203bb005f8107a379bd428c859ef47671a` | `a34be5693aa6a8c25ac5748da068937f3514bfcdaa7b89c81e113119c9e23352` (73) |
| `scanCount_add_markMeasure_le_of_allocTargetsWhite` | scans-plus-measure-at-most-initial-plus-alloc-weight: cited lemma | Classical.choice, Quot.sound, propext | `e1dd86c2415e13ca9b98f9966a50dfdf32e1cf9c5f8b5e67ca68b554a77b8259` | `bdda1d42c769b54693295a24bbd921b9f437075ea54544f72c7a0898539d1dba` (68) |
| `collectorFair_antecedent_false_of_eventuallyOnlyBlackAllocs` | fair-collector-eventually-black-allocs-eventually-always-no-grey: cited lemma | Classical.choice, Quot.sound, propext | `077edb75b5385a97ca03eecbf2de7f7a72401d27306cf713cdb96127f89cd897` | `6597d1d1296cb220650314f9f0e8b96c042bbe8569dbcde41744cc91d5a2f612` (68) |
| `activeOps_not_whiteTargetAllocs` | fair-collector-white-target-allocs-eventually-always-no-grey: cited lemma | propext | `32bcab4441da1700cb91d721f3a54e8773235355b12c88d099db7dfb2c2f04ed` | `8d4b25ed9cefd71980b60e4fac77c06c768a23f96388f921830d00be5896717d` (21) |
| `collectorFair_antecedent_false_of_whiteTargetAllocs` | fair-collector-white-target-allocs-eventually-always-no-grey: cited lemma | Classical.choice, Quot.sound, propext | `97e939df03ec4b512c5297455504f450ea3a5688c01d0e3c03876c4c479823da` | `33ab6174dfa4ac2d625e6b73de9a255c9bf4aa24de6351bbd5c5a264dc9ad40a` (63) |
| `eventually_only_white_alloc_of_whiteTargetAllocs` | fair-collector-white-target-allocs-eventually-always-no-grey: cited lemma | Classical.choice, Quot.sound, propext | `1855dba49947dcb175b7295f31694b565015cd0c5ee280e8010ff68de3e2da8a` | `888803df86dd222d1ed5c27c77d101337a05427121cfd4962855ec1855f4865a` (57) |
| `shadeLe_erase` | scans-plus-measure-at-most-initial-plus-alloc-weight: cited lemma | propext | `1910990029c11ed4d2c450d10df282f27c45f243b91ac1757fea28ac37af0b97` | `fb97fb01b91b1ab90039ea09861499b41b04c4a169a796f51b5297aa2c5da212` (29) |
| `shadeLe_store` | scans-plus-measure-at-most-initial-plus-alloc-weight: cited lemma | propext | `efc852d1c1db8c8ba634ad4d601e7745e185fa5f1690e88e656d5b1f0ed74b7e` | `008e925ab447e02155fbedb2c3e69fc25ef06d6b3c0f18d5f0593d349529105b` (29) |

### Primary sources (prior art)

Bibliographic records were checked against Crossref on the observation date. Each entry states
what was read of the source; the cards attribute no statement to a source whose relevant text was
not read (a source cited only through another source is marked as such in the card).

- **Dijkstra, Lamport, Martin, Scholten, Steffens**, "On-the-fly garbage collection: an exercise
  in cooperation", *Communications of the ACM* 21(11):966-975, 1978, doi:10.1145/359642.359655
  (record verified via Crossref). The manuscript EWD 520 (20 October 1975) was read in the
  transcription of the E. W. Dijkstra Archive,
  https://www.cs.utexas.edu/~EWD/transcriptions/EWD05xx/EWD520.html: the roots are "one or more
  fixed nodes —called “the roots”— with a constant place in memory"; P1 is "during marking there
  will be no edge pointing from a black node to a white one"; "during marking each node will
  darken monotonically"; and the collector's first action C1 is "shade all the roots". The
  transcription is a mutable web page with no revision identifier, and no copy with a fixed
  timestamp or content hash could be retrieved, so none is recorded; the passages relied on are
  quoted verbatim here (they were last re-read in the transcription on 2026-11-21) so that they
  can be checked against any copy of the transcription or of the manuscript.
- **Jones, Hosking, Moss**, *The Garbage Collection Handbook: The Art of Automatic Memory
  Management*, 2nd ed., CRC Press, 2023, doi:10.1201/9781003276142 (record verified via
  Crossref). The table of contents at https://gchandbook.org/contents.html was read: Chapter 15
  "Concurrent garbage collection" (p. 329); Sec. 15.1 "Correctness of concurrent collection"
  (p. 331) with the subsections "The lost object problem" (332), "The strong and weak tricolour
  invariants" (334), "Allocation colour" (336), "Incremental update solutions" (336) and
  "Snapshot-at-the-beginning solutions" (337); Sec. 15.2 "Barrier techniques for concurrent
  collection" (p. 337) with "Grey mutator techniques" (337), "Black mutator techniques" (339),
  "Completeness of barrier techniques" (340) and "Load barriers" (341); Chapter 16 "Concurrent
  mark-sweep" (p. 349) with Sec. 16.1 "Initialisation" (349), 16.2 "Termination" (351) and 16.3
  "Allocation" (352). The cards cite these sections by title and page only; no statement of the
  book's text is attributed.
- **Gammie, Hosking, Engelhardt**, "Relaxing safely: verified on-the-fly garbage collection for
  x86-TSO", PLDI 2015, pp. 99-109, doi:10.1145/2737924.2738006 (record verified via Crossref),
  and the Isabelle/HOL development, Archive of Formal Proofs entry `ConcurrentGC` (April 2015),
  https://isa-afp.org/entries/ConcurrentGC.html. Read: the entry page (Schism modeled with
  ConcurrentIMP and shown safe on x86-TSO; session theories including `Global_Invariants`,
  `Global_Invariants_Lemmas` and `StrongTricolour`), which is a mutable web page with no
  revision identifier, and the theory sources pinned as follows: repository
  `isabelle-prover/mirror-afp-devel` (a Git mirror of the Archive of Formal Proofs development
  repository), commit `523cdc72b5ae4a91c9ab8e1025d4a30b40472720` (committed 2026-11-18), files
  `thys/ConcurrentGC/Global_Invariants.thy` (SHA-256
  `6bf3e80cd3e4d0bb119f471e612208bfd8dfc8f50a466cf69d2683b0bcc4d267`, Git blob
  `956076d15dab64021fc8e72f8e5ee18a43d2a995`) and
  `thys/ConcurrentGC/Global_Invariants_Lemmas.thy` (SHA-256
  `12ed3b0a24b5ada50bf7dd2ffbe5a20e29cbf0c7566592b24dd2f05336e83e5b`, Git blob
  `a6420d9f4e5005db8696688386921bf9ac287c9a`). In these files `Global_Invariants` defines
  `strong_tricolour_inv`, `grey_protects_white` and `weak_tricolour_inv` (lines 54-75) and
  proves `strong_tricolour_inv s ⟹ weak_tricolour_inv s` (line 77), and
  `Global_Invariants_Lemmas` proves `reachable_blackD` (lines 910-911:
  `⟦ no_grey_refs s; reachable_snapshot_inv s; reachable r s ⟧ ⟹ black r s`) together with
  lemmas including `reachable_snapshot_inv_alloc` (line 1097) and `reachable_snapshot_inv_load`
  (line 1113). The development contains no termination
  proof.
- **Clements, Hudson**, "Proposal: Eliminate STW stack re-scanning", repository
  `golang/proposal`, file `design/17503-eliminate-rescan.md` at commit
  `0bdeab75fa2b7e79fc41fd33f269a5ef6d92e407` (2016). Fetched at that commit; the passages the
  cards rely on were read: the strong tricolor invariant (line 41); Go 1.7's coarsened Dijkstra
  write barrier (line 49), "permagrey" stacks that must be re-scanned (lines 76-77), with the
  re-scan done "with the world stopped" (line 88); the hybrid barrier's allocation requirement
  ("allocate-white is a common policy, but incompatible with this barrier", lines 120-122; Go
  already allocates black, lines 123-124); the weak tricolor invariant attributed to Pirinen
  (lines 143-146); the Yuasa barrier's "complete snapshot of the stack" (lines 276-277);
  Pirinen's result that black-mutator barriers other than Yuasa's require a read barrier (lines
  294-295); and the appendix proofs about the hybrid barrier (Theorem 1 at line 788).
- **Pirinen**, "Barrier techniques for incremental tracing", ISMM 1998, pp. 20-25,
  doi:10.1145/286860.286863 (record verified via Crossref; full text not consulted). Cited only
  as quoted by Clements and Hudson.
- **Yuasa**, "Real-time garbage collection on general-purpose machines", *Journal of Systems and
  Software* 11(3):181-198, 1990, doi:10.1016/0164-1212(90)90084-Y (record verified via Crossref;
  full text not consulted). Cited only as described by Clements and Hudson.
- **Russinoff**, "A mechanically verified incremental garbage collector", *Formal Aspects of
  Computing* 6(4):359-390, 1994, doi:10.1007/BF01211305 (record verified via Crossref; abstract
  read at the publisher: a proof system based on the Manna-Pnueli model of concurrency,
  implemented as an extension of the Boyer-Moore prover, proves Ben-Ari's incremental collector
  correct by two theorems, that nothing except garbage is ever collected and that all garbage is
  eventually collected).
- **Coupet-Grimal, Nouvet**, "Formal verification of an incremental garbage collector", *Journal
  of Logic and Computation* 13(6):815-833, 2003, doi:10.1093/logcom/13.6.815 (the Crossref record
  lists the first author only; the co-authorship of Nouvet is as given by the publisher's page
  and the description of the accompanying Coq development). Read: the description of the Coq
  development (safety and liveness of an incremental collector represented as an infinite
  transition system, using an axiomatization of LTL over co-inductive executions); the exact
  liveness statement was not read and is not stated in the cards.
- **Zakowski, Cachera, Demange, Petri, Pichardie, Jagannathan, Vitek**, "Verifying a concurrent
  garbage collector with a rely-guarantee methodology", *Journal of Automated Reasoning*
  63(2):489-515, 2019, doi:10.1007/s10817-018-9489-x (record verified via Crossref, which gives
  the online publication date 2018-11-01 and the print issue date August 2019). Read: the
  abstract (a rely-guarantee methodology in the Coq proof assistant) and the conference version
  (ITP 2017), which states the main result as safety.

### Observation dates

The kernel check, the axiom and hash audit, the reading of the Go design document at the pinned commit, of EWD 520, of the handbook's table of contents and of the Archive of Formal Proofs entry, and the bibliographic verification were done on 2026-11-20 and 2026-11-21; all were revalidated on 2026-11-21. The `ConcurrentGC` theory files were fetched at the pinned mirror commit, and their SHA-256 hashes computed, on 2026-11-21.

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is installed; there are no Lake dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and

1. runs `lake build` (the library `Toy`);
2. rejects any Lean source containing `sorry`, `admit`, `native_decide`, or an `axiom` declaration;
3. computes, with Lean's `collectAxioms`, the axioms of every declaration of the library and fails if any is outside `propext`, `Classical.choice`, `Quot.sound`;
4. for every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, `scope_witnesses_lean`, `corollaries_lean`, and hypothesis `counterexample`s) and every name recorded in `audit/statements.json`, recomputes the SHA-256 of the statement (the Lean `repr` of the declaration's type) and of its definition closure (for every package-local constant reachable from the statement: its name, the `repr` of its type, and, for non-theorems, the `repr` of its value, sorted and newline-joined; theorem bodies are excluded) and compares both, with the closure size, against `audit/statements.json`.

It prints `REVALIDATED` and exits 0 if and only if all checks pass. A name that is referenced but has no recorded hash is only checked for existence and reported in the count of unrecorded names (expected: 0).

**Manual axiom listing.** From `lean/`:

```sh
lake build
lake env lean RevalidationAudit.lean
```

This prints `#print axioms` output for each of the 132 declarations listed in **Evidence**, all of which have a recorded hash. Each line must report no axioms or a subset of `propext`, `Classical.choice`, `Quot.sound`.

**What a passing check establishes.** It establishes that the theorems quoted in **Findings** are kernel-checked under the pinned toolchain with the recorded axioms and that their statements and definition closures are the recorded ones. It does not check the prose, the modeling bridges or the citations.
