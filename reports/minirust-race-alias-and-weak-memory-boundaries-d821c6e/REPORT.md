# Alias-sensitive byte memory, race detection and weak-memory composition

## Summary

MiniRust's concurrent wrapper records address ranges for loads/stores and compares the current step with the previous step. This is a precise SC-oriented starting point, not a history-based happens-before detector or a relaxed-memory Rust model. Zero-size ranges and retag/protector events expose concrete seams that a combined adequacy theorem must address.

Iris weak-memory developments supply view-indexed resources and adequacy for their own languages. They do not automatically extend MiniRust's byte/provenance/Tree Borrows state, and the examined ORC11 fragment excludes SC operations.

## Applicability

Direct sources: MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, Miri `0e1a23b0794bec7860df8c06a774f4316746795a`, the 2024 GPFSL-derived artifact `kaist-cp/relaxed-memory-separation-logic@6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`, and Rust atomic contract source `d8ef4f3fe7031514cbd7d056b7b058814987ecec`. The latter GPFSL artifact is directly inspected at its adequacy endpoint and is not assumed identical to the POPL 2020 development.

This wave rechecked the earlier relaxed-memory report's primary adequacy endpoint and relevant contracts, then added MiniRust-specific source comparisons and finite discriminators. No actual concurrent Rust, upstream model checker or Rocq build was run.

## Findings

### F1. Actual wrapper and machine granularity

Basis: **source**.

`ConcurrentMemory<M>` adds `Access {type, atomicity, addr, len}` to each load/store before delegating to M. Read/read pairs never race; two atomic accesses never race; otherwise the overlap predicate is `a+n > b && b+m > a`. The atomicity enum has only `Atomic` (documented SC) and `None`. Allocation, deallocation, retagging and end-call hooks delegate without adding Access entries. The introductory “atomicity is ignored” prose does not describe the race exemption in the actual code; it cannot override it. [Wrapper](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/concurrent.md).

`Machine::step` saves the previous step's accesses/synchronized-thread set, picks an enabled thread, executes one statement or terminator, then checks that step against the saved accesses unless synchronization exempts it. It does not compare against an accumulated per-location history. A normal successful run can therefore contain separated conflicting accesses that are not detected in that schedule. This alone does not establish a universal safety defect: another schedule may place them adjacent, and the semantics quantifies over choices. Any completeness argument must justify the reordering needed to expose conflicts, particularly with alias-state effects. [Machine step](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/machine.md#L197), [reset](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/machine.md#L355).

Atomic load/store/RMW are whole intrinsic evaluations under this step scheduler. Failing compare-exchange emits a load but no store, preserving the read/read nonconflict distinction. Atomic width is power-of-two bounded by `MAX_ATOMIC_SIZE`; the wrapper does not check partial-overlap mixed atomic widths. [Atomic intrinsics](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/intrinsics.md#L425).

### F2. Bounded discriminators expose limits of a per-run interpretation

Basis: **execution** of exact-formula transcriptions, not upstream executions.

The owned probe exhausts 80 accesses: address 0–4, length 0–3, read/write and atomic/non-atomic. Of 6,400 ordered pairs, 198 disagree with overlap as intersection of the corresponding byte sets; every disagreement has an empty interval. Example: zero-byte read at address two versus a write of bytes [1,3) is called racy by the wrapper formula. Zero-size access at a range boundary is not. BasicMemory itself accepts zero-size dereferenceability without provenance, so an embedding must explicitly resolve this wrapper-level behavior rather than silently use a byte-set overlap lemma.

The same probe confirms mixed atomic/non-atomic reads do not race and both-atomic partial overlaps bypass the race predicate. Rust's access-based C++20-derived contract separately prohibits non-synchronized conflicting partial-overlap atomic accesses. This comparison identifies a model feature gap; it is not a claim that every MiniRust SC trace corresponds to a particular unsynchronized source execution. [Rust atomic contract](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/sync/atomic.rs#L26).

A three-step witness writes byte one, reads unrelated byte four, then reads byte one from another thread. Adjacent pairs do not conflict, while first/third do. This demonstrates previous-step granularity on one schedule only. It does not close the required all-schedules commutation argument or prove an upstream bug.

### F3. Alias events need an explicit concurrency interpretation

Basis: **source** + **derived** composition obligations.

TreeBorrowsMemory loads mutate permission trees even though their concrete bytes are unchanged. Retags can implicitly read/write inside ranges, and protector removal performs foreign read/write effects. These hooks run through delegated M methods and are absent from the wrapper's explicit Access list. Miri, by contrast, reports nonempty retag implicit accesses as non-atomic race events. [MiniRust retag/exit](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/memory.md#L128), [Miri retag race reporting](https://github.com/rust-lang/miri/blob/0e1a23b0794bec7860df8c06a774f4316746795a/src/borrow_tracker/tree_borrows/mod.rs#L390).

A combined model must define, and prove consistent, at least these interfaces:

| Interaction | Required proof obligation |
|---|---|
| Concurrent reads | Read/read byte nonconflict must coexist with alias-tree permission updates and protected Unique restrictions |
| Disjoint fields | Range splitting must preserve allocation-wide tag ancestry while showing unrelated byte updates commute |
| Partial overlap | Both race and alias components use the same physical footprint, including padding and operation atomicity |
| Retag/protector exit | Decide which implicit accesses count as memory events; prove any omission preserves the intended observable safety |
| Allocation/free/reuse | Relate address ranges to fresh allocation instances; prevent a reused address from transferring old liveness/permission |
| Synchronization | Thread/lock/join effects must order exactly the accesses whose resources are transferred |
| Error paths | Failing access or exit cannot be treated as successful resource restoration |

This table is a **derived specification of obligations**, not a proof. Alias rejection can make an otherwise commuting schedule impossible, so a race-detector completeness proof established for plain bytes need not survive the addition of Tree Borrows.

The PLDI Tree Borrows optimization model deliberately allows racy SC executions; protector-based transformations avoid needing race reasoning. That theorem consequently does not fill this composition gap. [PLDI §5](https://research.ralfj.de/papers/2025-pldi-tree-borrows.pdf).

### F4. Weak-memory ownership requires observation, not just fractions

Basis: **documentation/source** plus identified **derived** implications.

RustBelt Meets Relaxed Memory re-establishes lifetime reasoning over ORC11/iRC11, using synchronized ghost state for observation-sensitive resource transfer and reclamation. Relaxed accesses/fences require reverified library proofs and adapted borrow rules. The development does not support SC accesses/fences; its appendix's RC11 correspondence is explicitly a paper proof rather than included mechanization. Its race-reflection argument and value-cell language do not prove byte/alias-sensitive MiniRust adequacy. [Paper §§4–6](https://plv.mpi-sws.org/rustbelt/rbrlx/paper.pdf), [appendix preface and §2](https://plv.mpi-sws.org/rustbelt/rbrlx/appendix.pdf).

The directly inspected 2024 artifact's `noprol_adequacy` requires physical `Wf σ`, initial thread view membership `𝓥 ∈ σ.mem`, ghost pre-state instances, and a WP proof for every allocated logic instance and thread identifier. It concludes `adequate NotStuck (e at 𝓥) σ (λ v _, φ v)`. This is finite reachable-state safety and a postcondition for reached results, not termination/fairness. The ghost pre-state explicitly includes freeable, read-event, atomic-write and thread-view resources. [Exact adequacy source](https://github.com/kaist-cp/relaxed-memory-separation-logic/blob/6fe1475af1f8c49f8c144a67d9175b5b3e6bc472/gpfsl/base_logic/adequacy.v#L50).

For MiniRust, moving from a single current byte array to histories/views would change load results, validity observations, allocation liveness and the meaning of returned ownership. Alias tags also need a defined relation to observations and concurrent updates; choosing iRC11 alone does not answer that design question. A source theorem requires every relevant bad-source execution to be represented or ruled out by justified source premises. Inclusion of model behaviors in Rust behaviors is the wrong direction for proving Rust safety from model safety.

### F5. A small litmus distinguishes SC reasoning from view transfer

Basis: **execution**, with a deliberately limited model.

For producer `Wx=42; Wflag=1` and consumer `Rflag; Rx`, enumerating all six order-preserving SC interleavings permits outcomes (0,0), (0,42), (1,42); it forbids (1,0). A separate explicitly toy view rule permits flag=1/data=0 for relaxed communication and excludes it when a release/acquire observation imports the producer's view. This checks the missing premise in a proposed SC-to-relaxed argument, not actual ORC11 acceptance.

No reference-counting or reclamation implementation was verified. To prove those cases, a resource count reaching zero must be connected to visibility of every prior access and absence of future dereferences, before reclaiming the allocation. A count equality or all fractions in one hand does not itself construct that synchronization. The existing view-sensitive reclamation report remains useful for the detailed GPFSL protocol endpoints; this report adds the MiniRust composition boundary.

## Boundaries

- **Established:** exact wrapper/machine event inventory, bounded overlap and SC-interleaving outcomes, and the named adequacy premises.
- **Not established:** race-detector completeness under alias-sensitive interleavings, full MiniRust–Miri race agreement, a byte/alias weak-memory logic, or Rust source correspondence.
- **Known not to apply:** ORC11's cited fragment does not cover SC operations; MiniRust's two-valued atomicity does not specify Relaxed/Acquire/Release/fences.
- **Not examined:** actual reference-counting/hazard/epoch implementations, partial-overlap source litmus executions, compiler/hardware model mappings, fairness, or a mechanized proof's complete axiom/dependency closure.
- The toy view probe is neither a model checker for RC11/ORC11 nor proof of any concurrent Rust program.

## Evidence

Observed 2026-10-14. `source-evidence.json` records pinned blobs and narrow excerpts for the wrapper, machine, retag integration, atomics contract and adequacy. `probe.py` and `results.json` preserve all finite checks. Command: `python3 probe.py > results.json`, Python 3.9.6, exit 0. No invalid Rust or actual racy native program ran.

The earlier `relaxed-memory-reclamation-premises-2026` package was substantively reviewed; this package independently re-read the 2024 adequacy source and Rust atomic contract. A newer 2026 GPFSL signature discussed there is not silently substituted for this report's 2024 subject.

## Revalidation

Diff memory footprints, machine step boundaries, synchronization state and alias hooks together. Re-run the overlap probe before assuming zero-size accesses are empty events. Revalidate any all-schedules argument after adding alias UB or changing step granularity. For a weak-memory extension, preserve explicit orderings and reads-from/view events, inspect adequacy and source race-reflection directions, and kernel-check the selected logic plus newly proved memory-composition lemmas.

*Authored by an AI agent acting on joshlf's behalf.*
