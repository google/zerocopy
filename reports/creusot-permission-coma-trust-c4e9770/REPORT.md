# Creusot permissions, prophecy contracts and the Coma evidence chain

## Summary

At the inspected 2026 revision, Creusot supports permission-carrying raw-pointer and interior-mutability APIs, lifetime resources and atomic interfaces. Historical descriptions of Creusot as exclusively a safe-Rust verifier do not describe this source. These facilities use explicit trusted primitives and erased ghost resources; their presence is not a foundational proof of all Rust unsafe operations.

Its acceptance chain runs from rustc/MIR and Pearlite specifications through Coma, Why3/Why3find, transformations and configured provers. The Coma core theorem concerns its own verification conditions and semantics. It does not discharge Creusot's extraction, library contracts or actual Rust memory-model correspondence.

## Applicability

Source is pinned to `creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`, dated 2026-10-14. It requests `nightly-2026-08-03`, OCaml 5.3.0, Why3 `05bf4ddf55cb3042f34c3bc0ed3aff56a226978a`, and Why3find `0f054b93c86ac7ba20bca7df5d1563a9a4434a30`. These are declared source dependencies, not an installed/tested combination.

The separately inspected Coma formal subject is the [ESOP 2025 author paper](https://paulpatault.fr/pdfs/papers/esop2025.pdf), acquired SHA-256 `a52ad7b745fb8a1d0b54bf52b54f0cfaec18e59f587eda551a54702cf61a8d8e`. A 2026 TOPLAS extension is indexed as DOI `10.1145/3816735`; its additional proofs/features were not audited in this package. No identity between the formal core and every feature of the pinned backend is assumed. All source/documentary evidence was acquired on 2026-10-14; no translation or prover was run.

## Findings

### Pearlite logical values and ghost resources have different disciplines

`ARCHITECTURE.md` describes Pearlite as a pure specification language with quantification, logical equality and current/final operators on mutable borrows. Mutable references are translated using a current value and a prophecy for the value when the borrow ends; resolution connects the final value with the final current state. Logical expressions are type-checked through rustc/THIR without ordinary ownership checking. Program functions are translated from MIR after borrow checking, with dataflow information. Basis: upstream **documentation**, cross-checked against the inspected backend structure.

That document's opening still describes a safe-Rust verifier. Current `ghost/perm.rs`, `ghost/lifetime_logic.rs` and `std/ptr.rs` expose a further resource layer, distinct from unrestricted mathematical Pearlite values. A `Perm<C>` represents ownership of a container's logical value; its documentation makes it unsized to prevent replacement that would let a permission outlive its borrowed reference. The lifetime layer has fractional live tokens, splitting/joining, full borrows and ending/recovery interfaces; ending a lifetime requires a whole token. These are concrete interfaces, not a port of Iris adequacy established by this investigation. Basis: **source** + **documentation**; `perm.rs:30–39,75–103`, `lifetime_logic.rs:53–149,174–190`.

A reused specification must therefore distinguish a duplicable logical snapshot from ghost ownership enabling an operation. The presence of prophecy syntax does not prove any chosen prophecy/resource system consistent.

### Pointer and interior-mutability support comes through trusted permission APIs

`Perm<*const T>` associates a pointer with typed contents. Its invariant requires a non-null pointer, matching metadata and the pointed value's type invariant. Its disjointness relation distinguishes non-zero-size objects; zero-sized permissions cannot be treated as ordinary distinct addresses. `Perm::from_mut` returns a raw pointer and a guarded permission borrow, relating current and final logical values; it is trusted and intrinsic. `as_ref`/`as_mut` require a matching permission and relate the result to its contents; their raw dereferences are trusted intrinsic bodies. `to_box` consumes ownership under a matching pointer condition and erases to `Box::from_raw`; `drop` then uses that conversion. Basis: **source**, `std/ptr.rs:514–539,578–699`.

`cell/permcell.rs` wraps `UnsafeCell` as `PCell`, with permission-carrying `set`, `replace`, `borrow` and `borrow_mut` operations. Its resource-sensitive methods and thread trait declarations use trusted annotations. This directly supports interior-mutability reasoning through that API. It does not justify every existing `Cell`/`RefCell` implementation or arbitrary raw-pointer dereference. Basis: **source**.

The inspected pointer deep model contains address and runtime metadata; the permission interface and intrinsic encoding add further constraints. This limited inspection does not establish a complete byte-level initializedness/provenance model or compatibility with Stacked Borrows/Tree Borrows. In particular, reading this datatype alone would be insufficient to conclude that the entire frontend erases provenance. Those remain operational-model audit questions.

### Atomic contracts are sensitive to features and memory ordering

Current `std/sync/atomic.rs` has type-level Relaxed, Acquire, Release and AcqRel orderings, committers and synchronization-view resources. Its atomic load/store implementations select the type-level ordering unless `sc-drf` is enabled, in which case they execute SeqCst operations. The selected methods and synchronization-view primitives are trusted. A separate `atomic_sc.rs` interface executes SeqCst operations. Basis: **source**, `atomic.rs:12–57,228–261`, `atomic_sc.rs`, `view.rs`, `committer.rs`.

The ghost invariant module separates `AtomicInvariantSC` under `sc-drf`, `AtomicInvariant`, and non-atomic invariants. Opening contracts require namespace tokens and a ghost callback whose postcondition restores the invariant's protocol/public state. Thus these are protocol interfaces with explicit checking and trusted resource operations, rather than a blanket assertion that every atomics program is verified. The weak-memory history/view interpretation and actual Rust memory-model correspondence were not formally audited here. Basis: **source** + **derived** boundary.

### MIR extraction and primitive assumptions precede VC proving

The backend translates program statements into Coma, including mutable-place operations and resolution obligations. Pearlite clauses, program contracts, logical functions, loop invariants and termination conditions contribute different obligations. Externally supplied/trusted specifications bypass implementation justification at their intended boundaries. A caller proof can consequently be conditional on an unproved callee contract, even when the emitted caller VC is valid. The selected backend explicitly rejects the MIR `Offset` binary operation (`program.rs:688`); permission-wrapper presence must not be generalized to every direct pointer operation. Basis: **source** + **derived**, backend and selected trusted APIs.

`cargo-creusot/src/main.rs:38–39` selects both Coma generation and proving when no `--only` stage is requested; `--only=coma` or `--only=prove` selects one stage. The latter requires care about stale generated input. This source confirms the current “prove by default” behavior described by the [0.12.0 devlog](https://devlog.creusot.rs/v0-12-0/) dated 2026-06-24. Older workflows that equate a plain command with generation only are version-specific. Basis: **source** + **documentation**.

No inspected theorem proves rustc processing or Rust-to-Coma translation correct. A validated Coma subject needs that separate source relationship before it supports the intended Rust-level claim.

### Coma correctness is partial correctness of its formal core

The ESOP paper defines a correct Coma program by validity of its fully evaluated full-mode VC with the primitive recipe environment. Caller/callee modes distinguish interface obligations from implementation obligations across explicit abstraction barriers. Theorem 3 preserves correctness under a Coma step; Theorem 4 says a correct program is halted or can step. These are core partial-correctness results; termination requires additional well-founded variants. The formal semantics itself interprets assertions/primitive conditions by semantic validity. Basis: **documentation**, §3–4 of the pinned paper.

Those premises are stronger and more specific than a solver process returning success on an arbitrary printed formula. Connecting a practical VC generator, transformations, drivers, axioms and solver result to that validity judgment remains part of the acceptance chain. This is a **derived** distinction, not an independently checked Coma/Creusot proof obtained here.

### Why3find sessions and replay are not a Lean checking boundary by themselves

The inspected wrapper invokes `why3find prove`, passes selected files, configured paths and parallelism, optionally requests replay or no cache, and checks the subprocess status. `why3find.json` selects Alt-Ergo, Z3, CVC5 and CVC4 with `compute_specified`/`split_vc` tactics. Thus proof status depends on the exact generated file and configured prover/transformation environment. Basis: **source**, `why3find_wrapper.rs:70–109`, `why3find.json`.

Replay/session management is useful for reproducibility but does not itself specify an independently checked semantic certificate. This package did not audit Why3's VC-generator implementation, transformation proofs, drivers, optional interactive-prover exports, or solver proof traces. It does not claim Why3 lacks such integrations. A Lean route would need the accepted formula's semantics, transformations and axioms as well as checked solver evidence and the source-to-Coma connection. Basis: **derived** requirements, with those mechanisms explicitly **not examined**.

## Boundaries

- **Known not to apply:** pointer permissions and atomic wrappers are not evidence of general arbitrary-unsafe Rust support, all standard-library APIs or foundational rustc correctness.
- **Not examined:** actual command execution, a complete supported-operation matrix, primitive/resource consistency, effective feature configurations, backend proof assumption closure and independent certificates.
- **Unknown:** full initializedness/provenance/alias semantics, weak-memory correspondence, or a source-safety reflection theorem sufficient for Anneal acceptance.
- **Temporal conflict preserved:** the architecture document's safe-only wording and the 2025 Gillian comparison are historical/descriptive boundaries; inspected 2026 source has permission-based unsafe and concurrency facilities. They do not establish parity with Gillian or Iris.
- **Separate paper scope:** the ESOP Coma core does not automatically cover every 2026 extension or the entire Creusot frontend.

## Evidence

`source-evidence.json` and `additional-source-evidence.json` record immutable source paths/blob identities; metadata identifies the principal source and formal paper separately. Direct evidence is source/upstream documentation, with derived acceptance implications and no execution or independent kernel checking. Published dates of the 2025 paper and June 2026 workflow change precede the observation date. Solver/frontend dependency pins were read from `creusot-deps.opam`, not inferred from moving documentation.

## Revalidation

Pin frontend/rustc, ghost library, feature flags, generated Coma, Why3/Why3find, transformations, drivers and provers. Record trusted/extern contracts and ensure the checked generated file belongs to the current Rust input. Inspect the exact permission/ordering API used by the target code, including erasure and ordinary caller assumptions. For independent checking, define the complete certificate/translation interface and discharge its semantic premises; session replay or process success alone is insufficient.


*Authored by an AI agent acting on joshlf's behalf.*
