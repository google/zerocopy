# Refinement and permission inference, CHCs and Flux's concrete Lean VC route

## Summary

Flux, Thrust, RustHorn and Prusti can reduce annotation or memory-reasoning effort by exploiting Rust ownership and generating refinements, clauses or permission obligations. Their formal/implementation boundaries differ. The examined Flux and Thrust core theorems explicitly retain the possibility of borrow errors; ownership-dependent functional reasoning does not by itself verify arbitrary unsafe code.

Current Flux also has a concrete Lean VC-generation/checking path. It checks an external proof against the generated VC type and rejects transitive `sorryAx`, while leaving the Rust-to-VC translation and other axioms as distinct assumptions. This is a useful acceptance architecture to inspect, not a completed Rust semantic certificate.

## Applicability

The source comparison uses separate, uncombined subjects:

- Flux `6769bb9cbd1216380f542349494efafafd6104a3` (2026-10-14), declaring `nightly-2026-10-11`;
- Thrust `187a1e975edece50b896f1ee478ab665d7a1204e` (2026-10-13), declaring `nightly-2025-09-08`;
- RustHorn `4823f8f9c8e9e1deca71fdffe3c38061ae519c52` (2024-08-27), declaring `nightly-2022-01-22`;
- Prusti `0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2` (2024-03-26), obtained through the current canonical `prusti/prusti` repository after following metadata from the old `viperproject/prusti-dev` location.

The separately inspected Flux PLDI 2023 and Thrust PLDI 2025 author papers are bound to acquired byte hashes in metadata. RustHorn's updated author full-version PDF is similarly bound; it is not identified with the original ESOP PDF bytes. Formal paper calculi are not equated with every feature of these implementation commits. No verifier, Lean/lake, solver or compiler translation was executed.

## Findings

### Refinement inference relies on an ownership and call-interface premise

Flux's core λLR Theorem 3.1 starts from a well-typed expression/state and a finite execution. Its alternatives retain an alias-error step, a correctly typed value, or a further well-typed step. Consequently, the non-stuck conclusion depends on excluding borrow errors. Its algorithmic account separates shape inference, refinement constraints and liquid inference; compiler typing/borrowing information supplies the spatial premise. This is a conditional core-language result, not a proof of rustc or arbitrary unsafe implementations. Basis: **documentation**, [Flux paper](https://nilehmann.github.io/papers/pldi23-flux.pdf), §3.4–4.

Thrust's λCOR Theorem 4.1 assumes an empty initial heap/environment, a typed expression of its stated form and function types satisfying Φ; after finite execution, the expression is a value, can step, or reaches `BorrowError`. Its prophecy-based refinements describe current and eventual mutable-reference values, enabling update information to return to owners. The exceptional branch remains material. Basis: **documentation**, [Thrust paper](https://www.riec.tohoku.ac.jp/~unno/papers/pldi2025.pdf), §4.3.

These statements answer the foundational comparison question with known constraints. Producing a Rust correspondence proof or another verifier integration is future engineering/proof work, rather than a missing reading of those theorem premises.

### Current Flux separates shape inference, refinement checking and trusted bodies

`flux-refineck/src/lib.rs:64–116` implements shape inference at joins, refinement-tree generation and a backend query. It explicitly routes selected external/Lean modes to `execute_lean_query`; otherwise it uses a fixpoint query and reports its errors. Ghost statements feed this process. Thus inferred refinements and logical values are analysis artifacts, distinct from executable Rust ownership enforcement. Basis: **source**.

The same source returns success without checking a body marked trusted; trusted derived code can also be skipped. `checker.rs:268–275` can skip trait-method subtyping when either side is marked `trusted_impl`. A trusted abstraction's declared refinement can therefore be available to clients without its body being established by the checker. That contract dependency belongs in the accepted result. Basis: **source** + **derived**, `lib.rs:149–180`.

This is a concrete trust distinction, not a claim that all unsafe Rust is rejected or accepted by current Flux. A complete accepted-feature/unsafe-operation matrix was not examined.

### Flux's Lean route checks the generated proposition, with explicit modes and cache binding

`infer.rs:207–240` simplifies the refinement tree, creates a Lean-backend task, generates Lean files when the task hash is not cached, and records a pending task. The generation call itself returns success without proving the task. The driver later finalizes files, and in Lean-check mode runs `check_proofs` for pending external proofs; emit mode can generate without checking. Checked status is bound to a digest of the Lean project/configuration and invalidated when that digest changes. Basis: **source**, `flux-driver/callbacks.rs:142–195`, `lean_encoding.rs:165–194`.

Generated checking modules import the VC and human proof, use `#check` to require the exact expected proposition, and print the proof's axioms. `run_lake_build` builds those specific checking modules. `ProofReport::status` requires an elaborated axiom report, no relevant errors, and absence of `sorryAx`, including transitive dependencies. This is a real implementation interface for externally checked VC proofs. Basis: **source**, `lean_encoding.rs:293–348,1180–1194`.

The inspected predicate is not an allowlist for every other axiom: it specifically rejects `sorryAx`. The generator also has opaque constants represented as Lean axioms. A proof depending on another declared axiom is therefore a distinct assumption to retain; kernel elaboration checks a proof *under* its axioms. This is a **source-derived** acceptance constraint, not an executed demonstration that a particular Flux program was falsely accepted. Full imported assumptions and every generated primitive encoding were not audited.

For Anneal, this route demonstrates that a frontend can separate VC generation from checked external proof acceptance. It does not by itself establish source-safety reflection or that an arbitrary property domain is a conservative extension of the Rust interpretation.

### Thrust's CHC backend accepts a satisfiable clause system under trusted contracts

The source declares trusted/callable interfaces whose bodies need not be analyzed, as documented by the README and recognized in `local_def.rs`. The type/template and reborrow modules implement concrete refinement construction, with explicit unsupported ADT/ABI cases. Generic arguments and trait-method types are represented, but their presence is not evidence every Rust generic or higher-order feature is supported. Basis: **source** + upstream **documentation**.

`src/chc/solver.rs:118–189` defaults to Z3 with Spacer and solver-side validation options, configurable timeout, optional preprocessing and environment overrides. It writes a `check-sat` query and accepts exactly `sat`; `unsat` and other output produce different error results. This differs from ordinary VC validity, often established by unsatisfiability of a negated goal: CHC verification seeks a satisfying interpretation of unknown relations. The solver's validation option is not an independently checked Lean certificate. Basis: **source** + **derived** semantic distinction.

An inferred predicate solution can reduce annotation effort, but acceptance still owes the clause-generation meaning, callable/trusted contract assumptions, and borrowing premise. A timeout or `unknown` is an operational failure to establish the result, not a counterexample theorem.

### RustHorn's clause correspondence has a narrower formal subject than its compiler

The RustHorn author full-version Theorem 1 relates its COR operational input/output relation to the least CHC model for a simple function: no lifetime parameters and no reference input/output types. The proof uses an ownership-sensitive readout and abstract semantics. It supports functional reasoning over the modeled recursive structures without independently justifying arbitrary unsafe library implementations. Basis: **documentation**, [author PDF](https://shiatsumat.github.io/papers/esop2020-rust-horn.pdf), §3.3.

The pinned implementation is a rustc driver that configures optimization, disables debug assertions, analyzes MIR and stops compilation after emitting analysis output. Its analysis substitutes generic arguments and has explicit unsupported branching cases. These facts establish a concrete translation subject and source-side configuration, not proof that the old compiler pipeline implements the paper theorem or supports current zerocopy unchanged. Basis: **source**, `main.rs:39–79`, `analyze.rs:411,462`.

Recursive CHC solving, a recursive model theorem and support for arbitrary generic Rust programs are separate capabilities. The retrieved source/paper does not justify treating those phrases as interchangeable.

### Prusti makes borrowing recovery into permission and deferred-contract obligations

The pinned Prusti source defines separate raw memory-block and typed-owned permissions. Its procedure contract records permissions for arguments/returns and magic wands passed out by a call, with a TODO for blocked lifetimes via nested wands. Borrow expiry processing removes duplicated read permissions and restores write permissions; it explicitly notes a simplified restoration case and missing precision for nested projections. This is a concrete resource/automation boundary. Basis: **source**, permission inference, `contracts.rs:18–40`, `process_expire_borrows.rs:275–336`.

The pledge guide exposes `after_expiry`/`before_expiry` properties, while the trusted-function guide says bodies are ignored and contracts assumed. These deferred functional facts and permissions are related but distinct from Thrust's prophecy values or Flux's strong updates. The README also documents configurable overflow checking versus unbounded integers. Basis: upstream **documentation** at the pinned source.

Paper descriptions of Prusti also differ: the Flux 2023 paper presents its approach as permitting unsafe verification, while the Gillian-Rust 2025 comparison groups it with safe-only tools. Neither broad statement is adopted as a current feature matrix here. Actual fractional-permission amounts, Viper backend semantics/certificates and a complete unsafe-support inventory were not audited. These remain research subquestions; implementing a new unsafe extension is a separate future engineering task.

### Checked inference should retain its proposed solution and model meaning

A useful small-checker architecture can accept proposed refinements/invariants, then verify initiation, preservation/subtyping and required postconditions under the model. That separates search from logical acceptance, but it must also retain trusted contracts, borrowing assumptions and source translation. Flux's Lean VC interface is a concrete example of the logical-checking stage, with the assumption caveats above.

This comparison does not examine MIRAI, Infer, SeaHorn, SMACK or their certificate interfaces. Their names do not establish that they emit the same evidence, cover unsafe Rust, or can reuse this exact model. Performance and annotation comparisons across these tools would require matched subjects/configurations and measured runs.

## Boundaries

- **Known constraints:** core Flux/Thrust safety is conditional on borrowing; trusted bodies/contracts and backend assumptions remain part of the result; generated Lean VCs differ from Rust semantic certificates.
- **Not examined:** full core proof supplements/assumption closure, every frontend feature/primitive, a Lean build, all generated Lean encodings, Viper fractional/backend evidence and the other named abstract interpreters.
- **Unknown:** source-safety reflection/correspondence for these exact pipelines and unrestricted ordinary-caller guarantees for trusted unsafe abstractions.
- **No parity inference:** prophecy syntax, generic parameters, CHC generation and permission types represent different inspected capabilities.
- **No measurement claim:** no solver runtime, annotation-effort or existing zerocopy compatibility result was obtained.

## Evidence

`source-evidence.json` and `additional-source-evidence.json`, `prusti-source-evidence.json` pin examined source paths/blob identities. Flux paper SHA-256 is `69cae6293c84a7f42e90a883d6d4645449b7216e00c80219e262609528c52b51`, DOI `10.1145/3591283`; Thrust paper SHA-256 is `adc13d87e09a61e5ef42057c61c5602a38c5befa1416f0b76ba7edc919882695`, DOI `10.1145/3729333`. RustHorn's acquired updated author PDF SHA-256 is `0bcf21029350d89ec36ead06489a5eef681af5d3308c31ea90a33fff9fe32ef9`. Versioned source/artifact identity takes precedence over interpreting a mutable paper URL as an original release. Evidence is source/documentation and explicit derived constraints, acquired 2026-10-14, without execution or fresh kernel checking.

## Revalidation

Record the exact frontend/compiler, trusted contracts, constraints, inferred solutions and backend configuration. For Flux Lean checking, distinguish emit from check mode, retain the exact VC/proof types, project/dependency identities and accepted axiom set; audit cache and primitive assumptions. For CHCs, validate the relation solution against the generated clauses and their source meaning. For permissions, inspect borrower expiry, fractions and framing under the chosen backend. Treat a source correspondence proof, a real integration implementation and matched benchmark measurements as separate follow-up obligations.


*Authored by an AI agent acting on joshlf's behalf.*
