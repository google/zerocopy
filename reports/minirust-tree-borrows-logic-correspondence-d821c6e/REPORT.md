# Tree Borrows operations and the boundary of the λTB program logic

## Summary

At the examined pins, MiniRust and Miri have a useful correspondence between their per-location permission transitions, but this does not identify their complete memory semantics. A bounded transcription comparison found no difference in 81,915 short traces. Retag construction, protector exit, byte representation, wildcard provenance and race integration remain separate obligations.

Peterson's λTB logic provides reusable reasoning mechanisms for a simplified operational language. Its reported adequacy cannot be imported as a MiniRust library-soundness theorem.

## Applicability

This report compares MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` with Miri `0e1a23b0794bec7860df8c06a774f4316746795a`. The latter is an independently selected source revision, not the Miri version evaluated in PLDI 2025. Relevant parameters are MiniRust `implicit_writes`, the function's `fn_implicit_writes`, and Miri's `implicit_writes` and `precise_interior_mut`. No default is inferred from the presence of an implementation branch.

The formal comparisons concern the PLDI 2025 Tree Borrows paper and Rudy Peterson's 2025 thesis, whose stated development commit is `ccca9f325f909dceed4fd88008862f64296dbfd9`. ETH GitLab source access was unavailable. This report distinguishes paper-reported mechanization from source-inspected definitions and locally executed transcriptions. No upstream interpreter or Rocq development was built.

## Findings

### F1. The state relation is small; the operational relation is not

Basis: **source** + **execution** of an owned transcription.

MiniRust's unprotected states `Cell, Reserved, ReservedIm, Unique, Frozen, Disabled` correspond to Miri's `Cell, ReservedFrz, ReservedIM, Unique, Frozen, Disabled`, with the Miri conflict bit irrelevant while unprotected. For protected locations, MiniRust stores `had_local_read` and `had_foreign_read` in permission variants; Miri stores an accessed bit in `LocationState` and a conflict bit in `ReservedFrz`. Miri first updates the permission, then rejects a transition to Disabled when protected and accessed. MiniRust encodes those rejection cases directly. [MiniRust unprotected table](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_unprotected.md), [protected table](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_protected.md), [Miri permission transition](https://github.com/rust-lang/miri/blob/0e1a23b0794bec7860df8c06a774f4316746795a/src/borrow_tracker/tree_borrows/perms.rs#L130), [Miri location transition](https://github.com/rust-lang/miri/blob/0e1a23b0794bec7860df8c06a774f4316746795a/src/borrow_tracker/tree_borrows/tree.rs#L130).

The owned probe independently transcribes these two table presentations, normalizes their states, and enumerates every four-action trace of length zero through six from 15 representative states: 81,915 traces, zero differences. A trace stops after modeled UB. It does not enumerate tree construction or prove unbounded correspondence. Negative controls distinguish protected Reserved + foreign read + local write (rejected) from the unprotected sequence (Unique), and ReservedIm + foreign write + local write (Unique) from ordinary Reserved (rejected). These controls catch erasure of protection and interior mutability.

### F2. Operation-by-operation comparison

Basis: **source**; each row identifies the required relation rather than asserting equivalence.

| Operation | MiniRust definition | Miri definition and remaining obligation |
|---|---|---|
| Ordinary read/write | One permission per byte; recursive traversal classifies an access as local to its ancestors, foreign elsewhere | Location range maps, traversal skipping and per-node defaults; prove compressed ranges/skipped accesses preserve every byte's result |
| Retag range | Child has permissions over the whole allocation, with special inside permissions and initial accesses only where required | Inside range map plus outside defaults; prove initial access order, children and byte masks correspond |
| Protector release | Convert protected permissions, derive read/write exit accesses, traverse to foreign branches, stop at protected node and its children | `perform_protector_end_access` visits accessed ranges and skips children; establish same tag relation, including exposed descendants |
| Zero-size retag | Basic dereferenceability succeeds; absent provenance returns unchanged pointer; present provenance can create a child even when size zero | Non-live allocations with a zero-length reborrow can return new provenance without tracking bytes; no complete dead-allocation/path correspondence proved |
| Interior mutability | Exact `UnsafeCellStrategy` mask; shared frozen bytes start Frozen, cell bytes Cell; unprotected mutable cell bytes start ReservedIm | Precise-mask branch or whole-`!Freeze` approximation depending on parameter; compare matching settings only |
| Exposed provenance | Separate angelic provenance prediction selects a concrete old provenance/tag | Wildcard trees and exposure caches approximate uncertain parentage; table agreement says nothing about this choice relation |
| Allocation/free | Allocation ID + tree path; deallocation writes full range and rejects applicable strong protection | Concrete/wildcard tags; per-range strong-protector checks exempt Cell; prove allocation/tag freshness and reuse relation |
| Implicit accesses and races | Retag/end-call delegate through the memory wrapper without recording race Access entries | Retag explicitly reports nonempty implicit read/write ranges to Miri's race model; alias and race integration differ at this interface |

Narrow endpoints are preserved in `source-evidence.json`. In particular, prose preceding MiniRust's `NodeRelation` describes local nodes in the opposite direction to its `Node::access` code. The code determines the table above: from a node's perspective, an access through that node or its descendant is local. Treat the prose/code disagreement as an audit hazard. [Tree traversal](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/tree.md#L95), [Miri retag/race integration](https://github.com/rust-lang/miri/blob/0e1a23b0794bec7860df8c06a774f4316746795a/src/borrow_tracker/tree_borrows/mod.rs#L328).

### F3. What λTB establishes and what it leaves out

Basis: **documentation** of reported mechanization, not a fresh kernel check.

Peterson reports Iris adequacy for a block/value calculus, permission weakening, subtree deletion and lateral split/recombination. The supported retags are unprotected with static sizes; bytes, interior mutability and full protector lifecycle are excluded. Zero-size retagging requires a live block, and the logic needs ownership at its start offset. Vertical subtree separation is not supplied: naive subtree ownership would omit foreign effects on its parent. The reported adequacy applies to λTB executions with the required WP/state interpretation, not Rust or MiniRust. The exact theorem signature, dependency closure and axioms could not be independently inspected. [Thesis §§4.1, 6.1–6.4](https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/MasterTheses/2025-Rudy-Thesis.pdf).

The PLDI paper instead proves optimization refinements using Simuliris, including unknown code under stated restrictions. Its model uses SC interleavings and allows races; the activating write and the restoration of simulated values at protector exit or exposure constrain transformations. It does not establish safe-code soundness for Rust's borrow checker. [Paper §§5, 7](https://research.ralfj.de/papers/2025-pldi-tree-borrows.pdf).

These are different theorem directions. Optimization refinement may assume source safety to justify a transformed program. An API proof must establish safety of the original implementation for its client domain. A proof framework shared by both does not supply this implication. This is a **derived** conclusion about theorem reuse.

### F4. Local resource contracts must account for the caller's protected tree

Basis: **source** + **derived** obligations.

At MiniRust function entry, references receive strong protection, Boxes weak protection. Mutable references/Boxes to `!Unpin` pointees skip retagging. With enabled implicit writes, protected mutable inside bytes begin Unique and perform writes; outside bytes do not get that implicit-write treatment. Shared Cell bytes receive no initial access. Consequently a contract parameterized only by range size cannot determine what retagging requires. It also needs pointee layout, unsafe-cell mask, freeze/unpin facts, call mode and implicit-write policy. [Reborrow settings](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/reborrow_settings.md#L88).

For a shared four-byte mixed object with a cell at offsets 1–2, the reconstructed mask is Frozen/Cell/Cell/Frozen. Treating the whole range as Cell loses the outer immutability obligation. Treating it all as Frozen forbids permitted cell mutation. Nested cells require the layout-provided normalized mask; the probe tests only this simple case.

A callback that retains sibling aliases must satisfy a rely condition strong enough to preserve each protected accessed byte. A returned descendant reference must remain usable after protector removal, which is why exit traversal skips descendants. Normal or exceptional exit therefore cannot simply reclaim every permission as exclusive ownership of the numeric range. A future compositional logic needs a sound weakening/framing relation for tree effects, plus an obligation to perform release exactly once on each frame exit. These are proposed contract requirements; this wave does not prove them in Iris.

## Boundaries

- **Established only for the stated bounded transcription:** matching one-location access outcomes. Upstream execution equivalence, all tree topologies, retag insertion and dynamic ranges remain unproved.
- **Unknown:** direct correspondence with the inaccessible λTB Rocq theorem and the exact artifact-level Simuliris retag-size fragment. The thesis's §4.1 discussion and §6.4 comparison describe the latter differently; this report does not resolve that by selecting one sentence.
- **Known not to apply:** the λTB adequacy account above does not include byte encoding, full protectors or interior mutability.
- **Not examined:** an Iris lifetime layer for MiniRust, recursive-reborrow/callback proofs, wildcard exactness, all zero-size/dead-allocation paths, nested-cell mask construction, or a complete Miri/MiniRust simulation.
- **Not established:** safe Rust client quantification, LLVM `noalias` correspondence, or a machine-level alias/race composition theorem.

## Evidence

Acquired/rechecked 2026-10-14. `source-evidence.json` records immutable revisions, blob IDs, line slices and their text for directly inspected code. Paper URLs identify inspected editions, not byte hashes; no PDF download was obtained. ETH GitLab exact-file request was inaccessible; the Simuliris source link returned HTTP 429. Neither failure establishes missing formalization.

`probe.py` and `results.json` preserve the executed finite comparison. Python 3.9.6, macOS aarch64 host; command from this package: `python3 probe.py > results.json`, exit 0. No Rust UB was executed.

## Revalidation

Diff both permission tables and Miri's `LocationState::perform_access`, then rerun the transcription comparison after reviewing its source mapping. Next check retag masks, protector release, wildcard and race hooks separately. The cheap table probe cannot validate a changed tree traversal. Before importing λTB rules, obtain its exact revision and kernel-check adequacy/assumptions, then prove a relation to the selected MiniRust memory/target/parameters.

*Authored by an AI agent acting on joshlf's behalf.*

