# Arc, hazard pointers, and weak-memory RCU: whole protocol boundaries

## Summary

Reclamation proofs need a protocol that connects publication, validation, protected access, retirement, and eventual permission to free. Three inspected artifacts provide different protocols: a relaxed-memory semantic `Arc`, sequentially consistent hazard-pointer/Harris proofs, and an operational weak-memory RCU/epoch scheme with explicit SC fences. None of these source-level proof endpoints alone proves the current Rust implementation or compiler lowering.

## Applicability

This report directly inspects the source artifacts identified in metadata, including whole implementation/specification records and their language adequacy endpoints. It compares them with current Rust `Arc` and atomic documentation at `f6c1107f8be13e48465e12c0fd26e6a39fe18e4f`. The weak-SMR and hazard-pointer artifacts were publicly deposited on 2025-04-07 and 2025-04-09, respectively, before the observation date. Only their small source ZIPs were downloaded; the large proof/benchmark VMs were not. Rocq/Coq builds, compiled assumption closures, and native concurrent algorithms were not run. Source proofs and paper results are distinguished from replayed verification.

## Findings

### F1. Rust atomic and Send/Sync premises are separate from ownership protocols

Basis: documentation + source + derived.

Rust's examined atomic-module documentation derives its access-based rules from C++20 atomics, excludes consume ordering, and defines conflicting unsynchronized accesses involving a non-atomic access as data races. It separately constrains overlapping mixed-size atomic accesses. Available atomic types are documented as lock-free, not necessarily wait-free. Thus an atomic instruction contract, a whole algorithm's progress contract, and race freedom are three different obligations.

Current `Arc<T,A>` Send/Sync implementations require the payload to be both `Send` and `Sync`, with allocator bounds. The relaxed-memory semantic Arc has corresponding `arc_send` and `arc_sync` instances requiring both semantic payload predicates. Those predicates concern transfer/shared interpretation across thread IDs. A shared counter alone does not justify sharing a payload with an unproved interior-mutability discipline.

RC11 and the artifacts' operational model are research semantics; the Rust API documentation is the contract examined for actual Rust operations. Their names and common acquire/release vocabulary do not establish an equivalence theorem. A source-correspondence certificate must preserve allowed observations, synchronization, access regions/sizes, race exclusions, and reclamation legality, including effects of fences and compiler transformations.

### F2. Arc proves a counter-and-lifetime protocol, with concrete implementation differences

Basis: source + documentation + derived.

In pinned lambda-rust weak-memory `arc.v`, strong/weak counters use protocols and associated ghost state. `arc_persist` combines the counter invariant, a shared payload interpretation or dead lifetime, and a guarded lifetime-ending restoration of owned payload bytes plus a freeable allocation. `arc_persist_send` explicitly uses both shared and owned semantic transfer laws. `arc_clone_type` accepts a shared borrow of Arc at a quantified lifetime and returns Arc; `arc_drop_type` consumes Arc and returns `option ty`. The latter returns the last-owned payload to its caller rather than modeling all current Rust destructor code.

The model's clone increments via a relaxed load/CAS loop; its last release decrements via release CAS and an acquire fence before ownership restoration. Current native source uses `fetch_add(Relaxed)` for clone and `fetch_sub(Release)` for drop, then an acquire macro and `drop_slow` on the last strong reference. The macro uses an acquire load under the thread-sanitizer configuration rather than the ordinary fence. The model explicitly says it does not support Rust's maximum-clone overflow prevention; native source contains the counter limit and abort guard. This is a meaningful primitive/failure-behavior boundary, not a reason to discard the abstract ownership protocol.

The source theorem supports modular typing of the modeled Arc operations under `typeG`, `arcG`, payload well-formedness, and the lifetime/resource interfaces. It is not a theorem that every current Rust `Arc` operation, custom allocator, overflow path, panic cleanup, or compiler-generated destructor implements that model. Those exact bindings remain future correspondence obligations.

### F3. Hazard protection requires validation, not merely announcing an address

Basis: source + documentation + derived.

The PLDI 2025 hazard-pointer source defines `Deactivated`, `NotValidated p`, and `Validated(p, ghost-id, resource, size)` shield states. Domain registration transfers owned bytes, freeability, and the user resource into management. Setting a shield only announces an address. `shield_validate` needs management evidence establishing reachability; the logically atomic protect interface reads the source location together with its managed-resource invariant before giving a validated shield. `shield_acc` then exposes protected bytes/resource with a closing update that restores the invariant. Retirement and reclamation consume different protocol resources; a stale numerical pointer is not an access capability.

The actual reclamation algorithm snapshots hazard slots, takes the retired list, and frees only retired entries absent from the hazard snapshot. `hazard_pointer_impl` fills the entire specification record with proved registration, shield, access, retirement, and reclamation lemmas, instantiated with slot-bag and retired-list implementations. This goes beyond trusting a deallocation interface. `harris_find_spec` and `harris_op_impl` connect the protocol to actual modeled Harris traversal and the new/lookup/insert/delete ordered-set record, under heap/ghost-state and namespace-disjointness premises.

The proof language is sequentially consistent. Its hazard code comments discuss fences but elide them in that language. The accompanying Rust list implementation instead announces through `protect_raw`, calls `light_membarrier`, validates an anchor or predecessor with acquire loads, and uses operation-specific CAS orderings. For an optimistically traversed marked node, it validates the protected anchor; for an unmarked node, the protected predecessor. This code illustrates why immutable retired links permit fewer protection operations. The inspected source does not provide a compiler/Rust-memory-model correspondence theorem connecting these native operations to the SC proof. No unsafe native traversal was executed here.

### F4. The weak-memory RCU artifact includes an SC-fence protocol

Basis: source + documentation + derived.

The PLDI 2025 weak-SMR artifact contains an operational memory model, view-indexed separation logic, and epoch/history resources. Its algorithm activates a guard by publishing an epoch into a slot, executing `FenceSC`, and rereading the global epoch until validation succeeds. Epoch advancement executes another `FenceSC`, scans announced slots, and conditionally advances the epoch. Reclamation frees a retired entry only once the observed global epoch reaches its retirement epoch plus three. Deactivation/drop releases the guard's announcement; retirement records its epoch under an internally activated guard. The language uses mathematical integer literals and unbounded integer addition; this epoch-plus-three argument does not itself justify a fixed-width native counter through wraparound.

The base specification distinguishes inactive/active guard resources, retired-set views, protected block information, and retirement permission. `Guard_acc` returns the resource at a justified view with a closing update; `Guard_protected` excludes the retired entries already visible to that guard. These are interference/visibility premises, not an ordinary sequential borrow of any address.

`rcu_impl` fills the whole base record with the actual guard, registration, retirement, and reclamation proofs. It requires `noprolG`, `atomicG`, `rcuG`, disjoint namespace `N ## histN`, and supplied slot-bag/retired-list specifications. The source contains implementations of those specifications, including `proof_slot_bag_onat.v:slot_bag_impl` with additional ghost-resource premises. Traversal lifting gives a higher interface used by `harris_impl` and `msqueue_impl_rcu` to close their operation records and linearizability predicates. This is a whole algorithm proof architecture, not merely a free rule.

Importantly, this exact artifact contains `sc_fence_base_step` and `iwp_sc_fence`, with SC state/view constraints, and uses them in the algorithm. A blanket exclusion of SC fences from another ORC11/GPFSL snapshot must not be applied to it. This source observation does not establish all SC load/store support or correspondence to every Rust fence configuration.

### F5. Adequacy establishes modeled safety/results, not unconditional progress

Basis: source + derived.

The hazard artifact's `heap_adequacy` requires a weakest-precondition proof for every fresh `heapGS`, using the invariant-heap interpretation, and concludes `adequate s e σ` for the modeled language. The choice of stuckness parameter is explicit. The weak-SMR `noprol_adequacy` requires a well-formed physical state, an initial thread view contained in memory, and a WP for every fresh `noprolG` and thread ID; it concludes `adequate NotStuck (e at view) σ` with the result predicate. Its empty-state wrapper supplies particular initial conditions.

These inspected endpoints justify partial-correctness/non-stuckness claims in their languages when instantiated appropriately. They do not by themselves require a retry loop to finish, guarantee eventual epoch advancement, or ensure eventual reclamation in the presence of permanently active readers. A lock-free or wait-free claim needs a separate scheduler/fairness/visibility and progress argument; native atomic lock freedom is insufficient. The model also explicitly differs from Rust for uninitialized loads, returning poison in a documented language definition. Translating Rust invalid/uninitialized behavior into that model therefore needs an explicit bad-state/reflection obligation.

## Boundaries

Answered research: actual Arc resource/lifetime endpoints, whole hazard-pointer and RCU algorithm/specification closure, differing memory models/orderings, and environmental/progress premises. Not replayed: Coq/Rocq builds, compiled theorem assumption inventories, native benchmarks, and native weak-memory executions. These are evidence-quality limits, not unsupported results. Unknown here: a precise current Rust/compiler correspondence for the modeled algorithms, all SC atomic support in this artifact, and a total-correctness proof with stated fairness for each algorithm. Future use must instantiate caller resources and access/retirement invariants. This report does not answer async-cancellation or FFI cases within the wider R099 question.

## Evidence

Immutable revisions, archive and paper hashes are in `REPORT.json`; selected artifact paths and SHA-256 identities are in `artifact-source-identities.json`. Evidence was acquired 2026-10-14. No upstream sources or VMs are mirrored in this package.

- [Current Rust Arc](https://github.com/rust-lang/rust/blob/f6c1107f8be13e48465e12c0fd26e6a39fe18e4f/library/alloc/src/rcs/arc.rs): Send/Sync implementations, clone lines 2514–2548, drop lines 2949 onward, acquire macro and `drop_slow`; [atomic API](https://github.com/rust-lang/rust/blob/f6c1107f8be13e48465e12c0fd26e6a39fe18e4f/library/core/src/sync/atomic.rs), access-based memory model and portability guarantees. Full Git blob identities are in `source-identities.json`.
- [RustBelt relaxed-memory model](https://gitlab.mpi-sws.org/iris/lambda-rust/-/tree/186900b2cf948835873281646ce20c7e8f084f17): `theories/lang/arc.v:clone_arc,drop_arc`; `theories/typing/lib/arc.v:arc_persist` lines 29–36, `arc_send/arc_sync` lines 264–279, `arc_clone_type` lines 636–637, `arc_drop_type` lines 847–848. [POPL 2020 paper](https://doi.org/10.1145/3371102) motivates the relaxed-memory semantic typing, with the examined current model pinned separately.
- [Hazard-pointer artifact](https://zenodo.org/records/15183251): `proof/theories/hazptr/spec_hazptr.v:shield_state,shield_validate',shield_acc'`; `code_hazptr.v`, whole algorithm; `closed_proofs.v:hazard_pointer_impl,harris_op_impl,harris_impl` lines 40–96; `proof_harris_find.v:harris_find_spec` lines 989 onward; `lang/adequacy.v:heap_adequacy` lines 29–60. Native contrast: `implementation/src/ds_impl/hp/list.rs:traverse_with_anchor`, lines 103–165. [PLDI 2025 paper](https://doi.org/10.1145/3729247) presents the immutability optimization.
- [Weak-SMR artifact](https://zenodo.org/records/15167032): `gpfsl-examples/smr/rcu/code.v:try_advance,activate_loop,rcu_domain_do_reclamation_loop`; `base_spec.v`, guard/retirement interfaces; `base_proof.v:rcu_impl` lines 30–53; `traversal_proof.v:rcu_traversal_impl`; `proof_slot_bag_onat.v:slot_bag_impl` lines 1855–1893; `proof_retired_list.v:retired_list_impl` lines 401–424; `gpfsl-examples/harris/proof_harris_rcu.v:harris_impl` lines 18–42; `queue/proof_ms_rcu.v:msqueue_impl_rcu` lines 3751–3763. `gpfsl/lang/lang.v:sc_fence_base_step`, `base_logic/base_lifting.v:iwp_sc_fence`, and `base_logic/adequacy.v:noprol_adequacy` lines 50–95 bind the actual model endpoint. [PLDI 2025 paper](https://doi.org/10.1145/3729246) presents the weak-memory reclamation interface.

## Revalidation

Retrieve and hash the small pinned source artifacts, then inspect the named whole records, supplied component implementations, algorithm orderings and adequacy premises. Rediff native Arc and hazard-pointer operations before reusing their comparison. For proof replay, use the artifact's declared exact dependencies and collect compiled assumption output for the closure rather than accepting a paper claim or source `Qed` alone. The weak artifact documents a substantial build; no quick source probe replaces it. For a chosen native algorithm, separately identify its fence/atomic implementation and prove the observation/race/reclamation relation to the exact model before importing its safety theorem.

*Authored by an AI agent acting on joshlf's behalf.*
