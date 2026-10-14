# Resource transitions and proof-producing automation for Rust verification

## Summary

Cameras constrain legal resource composition; lifetimes govern temporary access and recovery; invariant masks govern opening; prophecies relate current contracts to future observations. These are separate interfaces. Automation can infer their entailments while producing checked proofs, but cannot supply an omitted operational interpretation or Rust safety premise.

MoSeL, Lithium, Diaframe and Quiver automate different judgments. Quiver additionally infers specifications, under a C semantics that omits alignment checking. Their evidence supports reusable mechanisms, not Rust feature parity or a measured Rust-facing authoring experience.

## Applicability

The inspected developments are deliberately separate: Iris `8e4909593a3a84f850d224a344cbd3a380672088`; historical RustBelt popl18 archive SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`; RustHornBelt 2022 archive `7e67c2d49b3b655113675c0d517d76589d615c9622eac2d91417d99263959121`; Lithium in RefinedRust's 2026-v2 artifact `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`; Diaframe 2022 source artifact `2f93bc6b13e99f4a37ce95c57fa99c5d131643676baca0b2d5388bacb9a49f12`; Quiver `e9636365a782e5a7e86cb14afb0016065116bf8d`. They were inspected, not rebuilt together. No dependency compatibility is asserted.

## Findings

### Cameras preserve compatible frames rather than just byte geometry

Iris `CmraMixin` requires composition/core/validity laws and an extension property. `cmra_update` quantifies over every compatible frame at every index. `auth_both_validN` connects fragments to an authoritative state by inclusion and validity. Consequently a resource update cannot be justified only against the visible current proof context. Basis: **source** and **derived**. [Camera laws](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/algebra/cmra.v), [updates](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/algebra/updates.v).

RefinedRust's concrete Radium instance uses authoritative address cells combining fractional ownership, exclusive-writer/reader-count state, and agreement on allocation identifier plus memory byte. Bytes distinguish ordinary bytes, pointer fragments and poison; separate maps track metadata and allocation liveness. Thus range geometry is accompanied by initialization, allocation identity and access state. These source definitions demonstrate an available design; their existence does not prove agreement with Rust's evolving aliasing/provenance rules. Basis: **source** + **derived**, identified artifact `radium/ghost_state.v`, `loc.v`, `val.v`.

### Guarded recursion is a contract on definitions

Iris OFE fixpoints require completeness, inhabitance and contractiveness. Recursive predicates must discharge these premises; moving a recursive occurrence beneath a later can provide the required guard. Later elimination is controlled: `lc_le_upd_elim_later` consumes one later credit and returns a later-eliminating update, rather than proving unrestricted `▷P → P`. `lc_soundness` requires a `Plain` proposition and a proof universally quantified over the allocated credit instance. Basis: **source**, [credits](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/base_logic/lib/later_credits.v#L282), [fixpoint](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/algebra/ofe.v).

A recursive Rust invariant is consequently a higher-order semantic definition plus a checked guardedness argument, not an arbitrary recursive Boolean accepted by notation. Author-facing inference may hide the proof but must retain its evidence. This is a **derived** interface obligation.

### Lifetime access carries the closing and recovery resources

The RustBelt lifetime signature distinguishes fractional live tokens, persistent dead evidence, inclusion and borrow assertions. `lft_tok_dead` excludes live/dead coexistence. `bor_shorten` consumes inclusion in its actual direction: `κ ⊑ κ'` and a borrow for `κ'` yield a borrow for `κ`. `idx_bor_unnest` requires ownership of the indexed borrow and a nested borrow of its ownership token, yielding an intersection lifetime. This is stronger than treating reborrow as pointer duplication. Basis: **source**, `lifetime_sig.v:89–121` in the hash-identified archive.

`bor_create` stores guarded ownership and returns a recovery continuation requiring dead-lifetime evidence. `idx_bor_acc` needs the lifetime context, mask inclusion, full indexed-borrow ownership and a live fractional token; it returns guarded contents plus a continuation restoring ownership and the token. An ancestor can be suspended while the child owns access, then recovered through that continuation. Inclusion and closing resources, not numerical address equality, justify recovery. These are **source** endpoints plus a **derived** Rust-facing reading. Signature `Parameter`s are module-interface declarations; the historical implementation includes concrete proofs, rather than thereby adding global axioms.

### Ordinary and parametric prophecies have different consistency premises

Modern Iris `proph_map_interp` ties client predictions to the remaining observation trace. A language instance must emit the relevant resolution events and maintain that interpretation. RustHornBelt's `proph_dep` instead tracks dependence on specified prophecy variables. `proph_resolve` requires namespace-mask inclusion, a dependency proof, the prophecy context, an exclusive resolution token and fractional dependency tokens. It produces an observation equation. `proph_obs_sat` derives existence of a valuation satisfying observations from the context and observation resource. Basis: **source**, [ordinary prophecy map](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/base_logic/lib/proph_map.v), RustHornBelt `theories/prophecy/prophecy.v:32,336,393`.

This is a concrete bridge for mutable-reference final-value contracts: the contract may mention a future value, but cannot resolve arbitrarily chosen inconsistent equations. It does not establish that Creusot, RustHorn or a new Lean encoding implements the same interface. Basis: **derived**; translation/caller correspondence remains a separate obligation.

### Masks and protocols justify interior mutation and logical atomicity

`inv_acc` requires the invariant namespace inside the current mask; opening removes that namespace and returns guarded contents with a closing update. The mask prevents reopening the same invariant while it is open. `cinv_acc` additionally requires a fractional cancellation token; `cinv_cancel` requires the full token to reclaim contents. Shared persistent knowledge of an invariant is therefore distinct from permission to mutate or reclaim its physical state. Basis: **source**, [invariants](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/base_logic/lib/invariants.v#L129), [cancellation](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/base_logic/lib/cancelable_invariants.v#L145).

`atomic_acc` provides an abort branch restoring the precondition and a commit branch consuming the atomic postcondition. `atomic_update` is its greatest fixpoint, allowing retries. `atomic_wp` universally quantifies over the caller's postcondition and accepts the corresponding atomic-update resource before supplying ordinary WP. `atomic_wp_inv` requires namespace inclusion and a proof restoring the invariant around the atomic contract. Logical atomicity specifies an operation's interaction with interference; it does not turn every implementation step into an atomic machine step. Basis: **source** + **derived**, [atomic updates](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/bi/lib/atomic.v), [atomic WP](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/program_logic/atomic.v#L61).

Rust's `UnsafeCell` contract removes shared immutability for its contents while preserving mutable-reference exclusivity and data-race restrictions. A protocol must therefore connect invariant ownership to each actual load/store; merely putting bytes in `UnsafeCell` supplies no synchronization. Basis: **normative** stdlib contract, `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec`, `library/core/src/cell.rs:2145–2191`.

The same file supplies a concrete dynamic-borrow protocol: `RefCell::try_borrow` constructs a `Ref` with `BorrowRef`, `try_borrow_mut` uses `BorrowRefMut`, and dropping `BorrowRef` decrements the borrow counter. `Ref` deliberately stores `NonNull<T>` instead of a reference; its comment limits immutability to the guard's lifetime rather than an entire function-argument scope. The guard state is therefore material to a cached shared observation; a value-level specification that forgets it cannot justify arbitrary later reads. Basis: **source** + **derived**, `cell.rs:1161–1175,1258–1268,1585–1591,1617–1622`. Full protocol proof and all leak/guard transitions were not audited here.

### Automation infers witnesses for different judgments

| Mechanism | Directly inspected judgment/interface | What remains supplied |
| --- | --- | --- |
| MoSeL/Iris proof mode | `Frame` witnesses a BI entailment that separates the framed resource from the residual goal | Logic instance, resource semantics, proof-bearing instances |
| Lithium | `SimplifyHyp` carries an implication; `Subsume` carries an implication to the requested resource and residual continuation | Typed rules, extensions and residual arithmetic/proofs |
| Diaframe | `BiAbd` proves that supplied resource plus inferred missing resource entails requested resource plus inferred remainder under a modality | Specifications, custom hints, invariants and language-specific stepping rules |
| Quiver/Argon | `abduct Δ P R` is entailment from interpreted context plus inferred resource `R` to goal `P` | Specification sketches, semantic types, callee specifications and C frontend |

Basis: **source**, Iris `proofmode/classes.v:386`; Lithium `definitions.v:69–93`; Diaframe `solve_defs.v:98–104`, `symb_exec/weakestpre.v`; Quiver `argon/abduction/abduct.v:467–471`. Diaframe's registered instances carry proofs; extending search need not enlarge logical trust when generated terms and their assumptions are checked. Failure to find a proof is not a counterexample or unsupported-feature theorem. Basis: **derived**.

Quiver's paper Theorem 5.1 targets its Caesium C semantics; Corollary 5.2 retains the standard-library specification premise. Its footnote explicitly removes alignment checks and a newer integer-pointer interpretation. Source `docs/OUTPUT.md` presents inferred predicate transformers with separate requirements and continuations for ensured resources. An inferred specification must be compared to the intended safe/unsafe caller contract: inference that discovers a stronger precondition does not justify silently imposing it on a safe API. Basis: **documentation**, **source** and **derived**. [Exact paper](https://plv.mpi-sws.org/quiver/paper-quiver.pdf), §5; source pin above.

### Safety credits and progress obligations have distinct conclusions

Ordinary Iris WP adequacy concerns finite reachable states, reached-result postconditions and `NotStuck`; later credits do not add fairness. The distinct TWP is a least fixpoint. `twp_total` requires universal invariant initialization, state interpretation, fork postconditions and the stated TWP proof, and concludes strong normalization of `erased_step` from the initial thread pool. That excludes every infinite execution in that modeled relation; it is different from progress only under fair scheduling. Basis: **source**, [total adequacy](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/program_logic/total_adequacy.v#L120).

For a nonterminating reactor, strong normalization is the wrong end goal. A liveness theorem needs explicit scheduler/environment premises and obligation discharge. This does not follow from counting physical steps or holding a fractional resource. Basis: **derived**.

## Boundaries

- **Not examined:** an exhaustive dynamic/implicit-frame/FOL-SL versus higher-order-SL experiment on the same Anneal examples; transfinite Iris or fair-termination framework endpoints; full automation performance or Rust-user usability study.
- **Unknown:** model compatibility across the listed dependency combinations and complete rustc/source correspondence. This is not a missing literature comparison between their inspected interfaces; it is a condition on transporting results.
- **Known not to apply:** Quiver's identified semantic theorem cannot discharge alignment or Rust-specific aliasing obligations absent from its subject.
- **Not examined:** a generated proof's full assumption closure, fresh Rocq proof checking, portable entailment certificates, and Lean-native implementation feasibility. Checked source statements are not new proof-checking execution.

## Evidence

`source-evidence.json` binds Git file identities and selected archive-member SHA-256 values. Source definitions above were read directly on 2026-10-14. The Quiver PDF bytes have SHA-256 `f868c976531a9ed386d4a396ede212d948a843fef946be1b7712b338c227df3f`, DOI `10.1145/3656413` (PLDI 2024). Diaframe source is [Zenodo 6414787](https://zenodo.org/records/6414787), an April 2022 artifact; no VM was acquired. RefinedRust's [2026-v2 artifact](https://zenodo.org/records/21636474) was published July 2026. Historical archive hashes bind inspected bytes where a full Git commit was not independently resolved.

## Revalidation

Check each judgment's actual premises and dependency versions before transporting an extension. For a new camera, prove its laws and updates with arbitrary compatible frames, then derive operational rules. For an inferred resource/specification, retain the theorem term, all admitted assumptions and the callee contracts; compare inferred admission to the intended caller domain. Revalidate guardedness, masks and closing continuations after changing a recursive predicate or borrow rule. Measure Rust authoring and automation on shared examples separately from these source results.

*Authored by an AI agent acting on joshlf's behalf.*
