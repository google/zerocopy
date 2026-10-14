# Weak-memory visibility and reclamation premises for Rust resource proofs

## Summary

Resource reclamation under weak memory requires the reclaiming thread to have observed the accesses it must precede. Fraction arithmetic alone is insufficient. iRC11 makes assertions depend on thread views and uses synchronized ghost resources to carry visibility through physical synchronization. Its adequacy establishes safety and reached-result facts for its ORC11-based language, with explicit initial-state and WP premises.

Rust's current atomic contract uses a C++20-derived, access-based model. ORC11 excludes SC operations in the inspected development; no theorem here identifies these subjects. Send/Sync, data-race freedom, memory reclamation and fair progress are distinct obligations.

## Applicability

Primary sources are `iris/gpfsl@48b7183f1b91f7cc53cfdab16e21387e9bfe9c14` (2026-09-25), the author-associated GitHub artifact `kaist-cp/relaxed-memory-separation-logic@6fe1475af1f8c49f8c144a67d9175b5b3e6bc472` (2024-05-20), Rust stdlib `d8ef4f3fe7031514cbd7d056b7b058814987ecec`, and Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`. The two formalization revisions are compared only at named endpoints; they are not interchangeable dependency environments. The POPL 2020 paper supplies historical explanation, not a fresh theorem for current std::Arc. No weak-memory execution, Rocq build or exhaustive compiler-transformation analysis was performed.

## Findings

### Rust orders accesses and forbids unsynchronized conflicting races

The pinned atomic-module contract follows C++20 atomic rules without consume, translated from C++ objects to Rust accesses. Conflicting accesses overlap and include a write; a data race additionally has a non-atomic participant and lacks happens-before order. Failed compare-exchange is not a write. Concurrent atomic and non-atomic reads are permitted; partially overlapping, differently sized conflicting atomic accesses require synchronization. These distinctions must survive a source-to-model mapping. Basis: **normative** stdlib contract, [atomic memory model](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/sync/atomic.rs#L25).

The same contract guarantees available atomic types are lock-free, but not wait-free, and conditions availability on target support. It describes `target_has_atomic` widths. Thus a proof using an atomic operation needs its selected target/width/order, and a progress theorem cannot replace lock-free with wait-free. Basis: **normative** contract, `atomic.rs:115–155`.

### The modeled language and adequacy are explicit

GPFSL's README identifies ORC11 as an operational RC11 model without SC accesses or fences. Its CPS expression language combines expression evaluation with view-machine transitions and pre/post race detection. The direct machine source is `gpfsl/orc11/thread.v`; race checks are model rules, rather than a theorem that every other Rust UB class is encoded there. Basis: **documentation** + **source**. [Pinned README](https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/48b7183f1b91f7cc53cfdab16e21387e9bfe9c14/README.md).

Current `noprol_adequacy` requires well-formed physical state, membership of the initial thread view in the memory state, the ghost pre-state instances and a WP proof for every allocated logic instance/thread identifier, with `time_ctx` supplied. It concludes `adequate NotStuck (e at 𝓥) σ (λ v _, φ v)`. `noprol_adequacy_no_time` instead accepts an unconditional WP proof; it discharges the extra time-context premise without using it. Empty-state wrappers specialize initialization. Basis: **source**, [adequacy](https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/48b7183f1b91f7cc53cfdab16e21387e9bfe9c14/gpfsl/base_logic/adequacy.v#L55).

The 2024 GitHub artifact's `noprol_adequacy` has the no-time WP premise directly. The 2026 file therefore materially changes the exposed interface; a theorem name alone does not bind its premises. Both inspected endpoints concern finite reachable configurations and reached-result postconditions through Iris adequacy, not termination or fairness. Basis: **source** + **derived**, [2024 endpoint](https://github.com/kaist-cp/relaxed-memory-separation-logic/blob/6fe1475af1f8c49f8c144a67d9175b5b3e6bc472/gpfsl/base_logic/adequacy.v#L50).

### View-indexed ownership connects tokens to observation

`vProp` is a monotone predicate indexed by a view, rather than an ordinary unindexed proposition. `view_join V P` evaluates `P` at the caller's view joined with `V`; `view_at V P` fixes evaluation at the named view. The adequacy pre-state includes authoritative freeable, read-event, write-event, non-atomic-view and thread-view resources. Thus cancellation and points-to facts can depend on what the owning thread has seen. Basis: **source**, `gpfsl/base_logic/vprop.v:20–45`, `adequacy.v:17–48`.

The RustBelt relaxed-memory paper explains why unsynchronized fractional cancellation tokens are insufficient: reclaiming all fractions need not order all prior accesses before reclamation. Synchronized ghost state records the owner's observations, and transfers must be backed by physical synchronization. Its lifetime adaptation re-establishes the borrow logic on this foundation. These are historical model results; importing the SC cancellation token unchanged into a weak-memory instance would discard a premise. Basis: **documentation** + **derived**, [POPL 2020 paper](https://plv.mpi-sws.org/rustbelt/rbrlx/paper.pdf), §§4–5.

The current `surface.v` exports `surface_vSP.v`, where `GPS_vSP_dealloc` is defined. The theorem requires both history and protocol namespace inclusion in the mask, `hist_inv`, the full `view_tok γi 1`, and `GPS_vSP_Reader` ownership. It returns existentially updated time/state/value, non-atomic points-to ownership and the guarded terminal protocol assertion. The physical `drf_pre_dealloc` rule separately requires the current thread view to cover the relevant write and access histories at every deallocated location. These are **source** endpoints; “counter equals zero implies free” omits premises. A Rust Arc/hazard/RCU proof must establish concrete synchronization and absence of future dereferences before consuming allocator deallocation permission. This is a **derived** obligation; actual hazard-pointer and RCU algorithms are not verified in this wave.

### Send and Sync constrain thread transfer but do not prove a reclamation protocol

The standard-library `Send` contract concerns transfer across threads; `Sync` means `&T` is Send and sharing cannot permit UB, including data races. Both are unsafe auto traits. `UnsafeCell` removes shared immutability only and does not prevent races. A manual Send/Sync implementation consequently needs a protocol for every accessible alias, destructor, callback and mutation path, not just an atomic counter inside the representation. Basis: **normative** contracts + **derived** consequence, [marker traits](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/marker.rs#L511), [UnsafeCell](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/cell.rs#L2145).

For an Arc-like resource, reference-count observation, exclusive destruction, allocation liveness and target atomic availability must agree. A proof of abstract counter arithmetic does not by itself order deallocation after another thread's read. ABA/address reuse also requires an allocation-instance relation; equal addresses do not revive an expired resource. Basis: **derived** from the above contracts and view-sensitive resource mechanism.

### Source compatibility and progress require separate relations

A safety proof in a model excludes bad *modeled* executions. To transfer it to source Rust, each relevant bad-source execution must be represented or ruled out by applicable Rust premises. Proving that a restrictive model's executions are permitted by Rust gives the opposite inclusion and is insufficient. No direction of inclusion between the full Rust C++20-derived model and ORC11 is established here. Basis: **derived** logical direction; models' scopes above are **source/documentation**.

Spawned code must satisfy the fork WP/postcondition required by the instance; unrelated threads and external effects must be represented by its environment or invariant assumptions. Non-stuckness permits divergence and scheduling starvation. Fair progress, bounded blocking and external response require additional liveness/environment hypotheses. A source safety certificate must not erase a possibly failing operation into a successful silent transition or justify source termination merely because its model omitted interference. Basis: **derived** from the adequacy target, relevant to T074.

## Boundaries

- **Known not to apply:** the inspected ORC11 instance excludes SC accesses/fences; its theorem is not a complete Rust or C++20 theorem.
- **Not examined:** complete RC11/ORC11 correspondence proof and transformation closure, memory-order compilation mappings, full current std::Arc proof, hazard-pointer/RCU algorithms and downstream Send/Sync coverage.
- **Unknown:** a Rust-to-ORC11 bad-execution preservation relation. This is a condition on applying the answered adequacy/model comparison, not evidence that the inspected model lacks an adequacy theorem.
- **Not examined:** fair/lock-free algorithm progress proof, complete assumption closure or a fresh formalization build.

## Evidence

`source-evidence.json` records full commits, Git blob or SHA-256 identities and exact symbols. The POPL 2020 paper (DOI `10.1145/3371102`) acquired SHA-256 is `462155546e6f213ec01fac35b5162088e44cb39b1039497b76a7a4ca2480770d`; its official page links the formalizations. GitLab archive requests returned HTTP 429 while exact-file APIs worked. These failures are acquisition limitations, not unsupported memory orders beyond what the README explicitly states. Evidence acquired 2026-10-14 is **source**, **normative**, **documentation** and identified **derived** reasoning; there is no execution of a concurrent program.

## Revalidation

Diff atomic contracts and the chosen model's machine steps, race checks, WP and adequacy together. Preserve every memory order and access width in a case trace. For reclamation, trace each token's view, physical release/acquire transfer and terminal allocator permission. Check the exact theorem assumptions and bad-execution correspondence direction before transporting a verified model result to Rust. Revalidate safety and progress independently.

*Authored by an AI agent acting on joshlf's behalf.*
