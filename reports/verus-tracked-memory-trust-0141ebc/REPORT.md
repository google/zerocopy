# Verus tracked permissions, compiled code and verification trust

## Summary

Verus makes ownership of ghost permissions part of the proof/program type discipline, while exposing mathematical specification values without that ownership restriction. Its raw-pointer APIs explicitly track initialization and permissions, but their contracts and abstract provenance are trusted primitives. The inspected solver path accepts an SMT unsatisfiability answer; it does not independently check a proof certificate.

The resulting guarantee belongs to the verified Verus program and its trusted boundaries. It does not automatically become a guarantee for every ordinary Rust caller of the ghost-erased API or every Rust alias/provenance model.

## Applicability

The inspected implementation is `verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`, dated 2026-10-14, with declared Rust toolchain `1.98.1`. Source and upstream documentation were read without building or executing Verus. `source-evidence.json` and `additional-source-evidence.json` record immutable file coordinates.

The formal-language comparison is the separate versioned [2023 extended paper](https://arxiv.org/pdf/2303.05491v2), arXiv `2303.05491v2`, released 2023-03-11, SHA-256 `05aa2097cf5740f2d1119426fbc1066277a010b7e8e1239095684c7931b14849`. Its small lambda calculus is not the 2026 Rust frontend, library or compiler. No revision-to-paper correspondence theorem was examined.

## Findings

### Modes and erasure define an accepted program different from plain source text

The mode guide distinguishes `spec`, `proof` and `exec`; specification/proof code is ghost code and is removed for executable artifacts. Specification mode cannot invoke proof or executable functions; proof mode cannot invoke executable functions. The implementation has a separate mode check in `vir/modes.rs`, and the verifier invokes `vir::modes::check_crate`. Its lifetime phase invokes rustc MIR borrow checking for eligible Verus-aware items, excluding external bodies/specifications. The verifier also has a `no_lifetime` bypass. A trustworthy result must retain the effective checking configuration. Basis: **source** + upstream **documentation**; `verifier.rs:2887,3278–3327`.

Ghost erasure is an additional correspondence boundary. `erasure.md` warns that executable conditional compilation under `verus_only` can make verification and compilation see different bodies. Its illustrative example is internally inconsistent as written: the verification branch returns zero while its shown postcondition excludes zero. The warning is documentary evidence; the example was not executed and is not retained as an observed successful unsoundness reproducer. Basis: **documentation** + **derived** reading of the displayed example.

Existing Rust therefore needs an accepted syntax/subset and the specifications/permissions expected by Verus, rather than acquiring verification through an unchanged compiler invocation. Replacing pointer operations with permission-carrying wrappers is a concrete adoption cost visible in the inspected API. Whole-project rewrite effort was not measured.

### Tracked values enforce resource transfer within the checked boundary

`PointsTo<T>` is a tracked type containing a non-copy marker, while `MemContents<T>` is a ghost `Uninit | Init(T)` model. A typed permission couples a particular pointer to a current logical value. Moving the tracked permission transfers access; borrowing it shares or temporarily lends access according to the checked resource discipline. A mathematical snapshot of its model does not itself carry read/write authority. Basis: **source**, `raw_ptr.rs:143–183`, with mode/lifetime checking above.

`builtin/src/lib.rs:546–570` exposes a zero-runtime-data `Tracked` wrapper and a hidden public `assume_new` marked external during verification. Primitive implementations use such construction under trusted contracts. Thus ghost erasure does not enforce semantic permission ownership against arbitrary unverified Rust code at runtime. To expose a safe abstraction to ordinary callers, the library additionally needs an actual Rust API/invariant boundary and a client/linking argument; an erased tracked parameter alone is insufficient. Basis: **source** + **derived** implication.

### Raw-pointer support is a permission interface with abstract provenance

`raw_ptr.rs` models a pointer by address, provenance and metadata; logical equality retains all three, while runtime pointer equality compares address/metadata. Provenance is declared abstract in an `external_body` ghost type. The comments associate reference-derived access tags with provenance but do not provide a Stacked Borrows or Tree Borrows operational implementation. This report consequently does not identify the model with either alias semantics. Basis: **source** + upstream **documentation**.

Typed permissions distinguish known initialized contents from forgotten/uninitialized knowledge. `ptr_mut_ref` requires the matching initialized permission and connects the returned reference's current/final value to the permission's current/final contents; its unsafe implementation is an external body. Alignment, non-nullness, forgetting contents and disjointness are supplied as axioms. `is_disjoint` explicitly excludes zero-sized arguments; those edge cases must not be generalized from distinct-address reasoning. Basis: **source**, `raw_ptr.rs:271–313,632–649`.

`PointsToRaw` owns an address-domain set and provenance. Axiomatic split/join operations redistribute that domain; conversion to typed permission requires an aligned exact-size range and yields uninitialized knowledge. Conversion back requires uninitialized knowledge. This does not constitute an inspected byte-content preservation theorem for arbitrary casts or zerocopy representations. Deallocation consumes both the matching whole-range raw permission and a matching size/alignment/provenance deallocation token. Allocation aborts on allocation failure. These operations are external bodies/axioms, with explicit trusted specifications. Basis: **source**, `raw_ptr.rs:770–855,908–969`.

`simple_pptr.rs` is explicitly a simpler pointer model; it must not silently stand in for the richer raw-pointer interface or ordinary Rust pointer semantics.

### Concurrent resources require invariant and atomic-operation discipline

`AtomicInvariant` is shareable and permits temporary access to its resource only through constrained invariant opening. Its documentation requires one atomic executable operation in an opening block, with additional checker rules governing control flow and opening. Open credits are created in executable mode and consumed when opening in proof mode, to prevent unbounded purely logical opening. The invariant types and opening primitives are trusted/external declarations. Basis: **source** + upstream **documentation**, `invariant.rs`.

The inspected integer-atomic wrapper's `load`, `store` and compare-exchange contracts connect the atomic cell's identity/value to a tracked permission. Its bodies call Rust atomics with `Ordering::SeqCst` and are external bodies. This establishes the observed wrapper's ordering choice, not a claim that every Verus concurrency API has the same ordering or that weaker-memory correctness follows. Tokenized state-machine macros provide a separate way to represent permitted transitions as exchanges of tracked tokens; generated obligations remain subject to Verus checking and their primitive contracts. Full macro correctness and every state-machine/concurrency feature were not audited. Basis: **source**, `atomic.rs:155–217`; state-machine token-exchange documentation and checker source.

### Formal core safety and SMT acceptance cover different subjects

The 2023 paper's §10.4 states preservation/progress for its typed heap-expression calculus and termination only for specification/proof modes, under well-formed declarations and the calculus's typing premises. Those endpoints do not establish current Rust-to-VIR translation, concurrent library contracts, or SMT solver correctness. Basis: **documentation**, versioned paper.

The implementation's AIR `check_valid` type-checks a query, lowers mutable variables and blocks, then calls `smt_check_query`. The SMT path reads `sat`, `unsat` or `unknown`; an unsatisfiable query produces `ValidityResult::Valid`. Optional unsat-core retrieval records used axioms, not an independently checked derivation of unsatisfiability. Unknown/canceled/type-error states are distinguished from validity. Basis: **source**, `air/context.rs:46–52,487–516`, `air/smt_verify.rs:249–275,335–364`.

A Lean acceptance boundary would therefore need checked evidence for both the VC and its meaning: trusted primitive contracts, the source/model translation, ghost/executable typing and erasure premises, and the solver derivation. Checking only an SMT formula or transporting a success count cannot supply those missing links. This is a **derived** integration requirement, not an implemented Verus-to-Lean route.

## Boundaries

- **Known not to apply:** the inspected formal calculus does not prove the current frontend/compiler correct or justify arbitrary unverified callers; specification/proof termination is not executable termination.
- **Not examined:** a fresh build; whole accepted Rust feature matrix; proof assumptions for all vstd primitives; byte-preserving transmutation; full state-machine generation correctness; all atomic orderings and concurrent scheduling models.
- **Unknown:** a source-safety reflection theorem connecting the verified/erased program to actual Rust UB, and compatibility with a chosen operational alias model.
- **Unsupported:** treating abstract provenance, tracked syntax, unsat cores or SMT success as an independent foundational certificate.
- **Contradiction preserved:** the erasure guide's displayed example has a postcondition/branch mismatch; only its warning is used as documentary evidence.

## Evidence

Evidence is direct source and upstream documentation plus explicit derived implications, acquired 2026-10-14. No execution evidence was obtained. `source-evidence.json` pins examined paths and Git blob identities. The formal paper's version/date/digest bind the separate calculus subject. No Verus, Z3 or Why3 executable was available via the inspected command search; no installation was attempted.

## Revalidation

Pin Verus, rustc, library contracts, configuration and the actual executable build inputs together. Check that conditional compilation preserves the verified executable body. Audit external bodies/axioms and resource creation points before claiming an ordinary-client API guarantee. For a target memory operation, inspect its exact permission/initialization/provenance preconditions. Before using solver results as certificates, retain VC meaning and assumptions and require a defined independently checked proof format. A future implementation/paper comparison needs a correspondence argument rather than version adjacency.


*Authored by an AI agent acting on joshlf's behalf.*
