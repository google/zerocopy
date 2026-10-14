# Inference, compositional specifications and verification result meaning

## Summary

An inferred summary, a solver answer, a bug report and a checked certificate are different outputs. MIRAI explicitly tracks incomplete summaries and uses a diagnostic policy that can silence them. Current Infer Pulse carries exceptional, stopped and latent-error executions; its Rust frontend is experimental and has explicit unsupported cases. SeaHorn produces CHC results and optional invariants under configurable memory abstractions. SMACK distinguishes bounded/modular runs and failure categories. Prusti/Viper permission representations provide a specification vocabulary, while SAW/Crux method-spec construction and override use do not by themselves prove the substituted callee. These interfaces are useful candidates for inference and proof construction, with their result meaning retained.

## Applicability

Directly inspected Git subjects: MIRAI `aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`; Infer `5aac32c06952a2f3a6b7043e91457920f065833b`; SeaHorn `892780176731ec8e97bbb9f6b172fcacd77a8ff4`; SMACK `0a64471206645c250164e8df6027f5a5193e5e85`; Viper Silver `b4094c37a08f91ac41b3952194b73405c1221c5f`; Prusti `0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2`; SAW `27a7ae98256544b55a7a3ce4ce620c1a7889713b`. They were not built or run together.

Historical Infer `99464c01da5809e7159ed1a75ef10f60d34506a4` (v0.17.0, 2019-08-05) is examined separately for its bi-abduction interface. It is not equated with current Pulse or the current Rust frontend. The 2009 POPL paper is a historical algorithm/theory source, not a specification of October 2026 Infer.

## Findings

### F1. Output roles and what a downstream checker needs

Basis: **source** and **derived**.

| Interface | Actual inspected result | Useful downstream role | Additional obligation before a proof claim |
|---|---|---|---|
| MIRAI | Computed/incomplete summary, preconditions, side effects, postcondition and diagnostics | Candidate contract and call-context analysis | Check complete source coverage and accepted summary, including unknown-call effects and recursive handling |
| Historical Infer bi-abduction | Missing heap/frame/substitution result; call success/not-met/not-found/skip | Infer resource preconditions and frames | Independently establish inferred entailment, atomic-command rules, callee coverage and satisfiable source entry |
| Current Infer Pulse | Pre/post summaries plus continuing, exception, stopped and latent-error paths | Bug evidence and specialized summary candidates | Preserve path/result categories and experimental frontend exclusions |
| SeaHorn | SAT/UNSAT/UNKNOWN; optional solver model/invariants and counterexample | CHC invariant candidate or bounded query result | Check initiation, consecution and property clauses, plus exact LLVM/memory abstraction |
| SMACK | Verified/error category/timeout/unknown with run mode and bounds | Bounded counterexample or modular Boogie verification evidence | Retain unroll/modular mode, frontend, memory model and backend assumptions |
| Prusti/Viper | Permission/invariant encoding and backend success/failure | Generate resource verification conditions | Validate encoding and trusted contracts; backend success is not a Rust safety theorem by itself |
| SAW/Crux MIR method specs | Constructed pre/post/memory relation; overrides assert pre and assume post | Compositional call replacement | Prove the actual callee satisfies the spec; preserve frames, alias restrictions and native translation |

No selected path was found to provide a fully checked Rust-to-kernel certificate covering all these premises. That observation concerns the examined paths, not an established tool-wide absence of certificate exports.

### F2. MIRAI incompleteness and diagnostic policy

In `checker/src/summaries.rs`, a summary records `is_computed`, `is_incomplete`, preconditions, side effects and postcondition. Incompleteness includes unavailable MIR, time limits, insufficient widening and missing side effects. In [Overview.md](https://github.com/endorlabs/MIRAI/blob/aae0a56f91d9a0a62073bb86e7b2c9793cefc24b/documentation/Overview.md), the default policy suppresses missing/incomplete-function diagnostics and treats those paths as unreachable. The documentation explicitly describes this diagnostic choice as unsound. Verify diagnostics report reachable incompleteness, but analysis still conditions its continuation on excluding those branches. A verification policy therefore has to reject or discharge the reported incompleteness; merely selecting verify mode does not make every result unconditional.

`call_visitor.rs` inspects unavailable/external calls and summary reuse with specialized type/function arguments; recursive calls use depth-dependent handling. These are analysis policies, not proof-producing inference rules. A default unknown summary does not establish that an arbitrary external call preserves all memory. Unexamined summary/certificate paths remain unknown.

### F3. Bi-abduction theory and historical implementation boundary

The [POPL 2009 paper](https://www.cs.ox.ac.uk/people/hongseok.yang/paper/popl09.pdf), §4–6, defines inference of missing heap M and leftover frame F with the entailment `Delta * M entails H * F`. Theorem 5 states soundness of successful BiAbd under its component procedures' specifications. Theorem 9 conditions inferred Hoare triples on sound abstract atomic-command semantics. The algorithm rejects provably inconsistent strengthened preconditions; failure of that test is not a completeness theorem for satisfiability. These are restricted symbolic-heap results, not full Rust lifetime/provenance correspondence.

The historical [Prover.mli](https://github.com/facebook/infer/blob/99464c01da5809e7159ed1a75ef10f60d34506a4/infer/src/biabduction/Prover.mli) exposes substitutions, checks, spatial/pure components and missing/frame information in `ImplOK`. Its ordinary Boolean entailment helpers document that false can mean lack of knowledge. `Tabulation.mli` distinguishes call success, failed precondition, missing specs and skipped callee. `Rearrange.mli` exposes symbolic dereference rearrangement and checks for null/freed/undefined accesses. This is actual implementation vocabulary for inference, not an exported kernel proof.

The current Infer source inventory no longer has the inspected historical `infer/src/biabduction` directory; a GET for that path returned 404. This inventory change does not establish that current Infer lacks every bi-abductive idea or resource inference facility.

### F4. Current Pulse and experimental Rust lowering

`PulseSummary.mli` records pre/post specifications, a nondisjunctive summary and specialized summary maps. `PulseExecutionDomain.mli` distinguishes continuing program states, raised exceptions and stopped paths: normal exit, reported abort, latent abort, latent invalid access and related categories. Collapsing these into one Boolean would lose the meaning required to replay a caller.

`infer/src/rust/RustMir2Textual.ml` lowers Charon ULLBC to Textual and distinguishes raw/reference pointer attributes. Generic type variables and some unsupported type cases map to Void, with an explicit warning for unsupported types; other operations raise a user-facing unsupported error. The official [Pulse documentation](https://fbinfer.com/docs/next/checker-pulse/) calls Rust support experimental. This source evidence supports a bounded frontend comparison; it does not establish ordinary Rust memory-model coverage. No current Pulse Rust run was made.

### F5. SeaHorn and SMACK query boundaries

SeaHorn's pinned README describes LLVM 14 and separate register-only, pointer-address and memory-content tracking options. CHC queries, BMC, inlining and Crab invariant injection are configuration choices. `HornSolver.cc` reports SAT/UNSAT/UNKNOWN and, after UNSAT, can extract/print a solver model as invariants. A model can serve as a certificate candidate: independently check every initial, transition and error clause against it. That still leaves LLVM lowering, abstraction, assumptions and Rust compilation outside that logical check.

SMACK's `top.py` enumerates verified, assertion, dereference, free, leak, overflow and Rust-panic outcomes, plus timeout and unknown. Its frontend includes Rust-to-LLVM handling. The pinned usage notes distinguish bounded checking from modular verification; the bounded success message reports the unroll bound. `no_verify` produces Boogie input without establishing backend success. A Rust panic result is not automatically Rust UB, and neither a timeout nor unknown is a counterexample. No actual SeaHorn/SMACK certificate replay or Rust run was executed here.

### F6. Fractional permissions and Prusti inference

Silver's AST represents fractional permissions using integer numerator/denominator expressions, full permission and no permission; wildcard permission denotes an unspecified amount, not one fixed fraction shared throughout a method. Accessibility predicates default to full permission. Its `VerificationResult` separates Success and Failure carrying structured errors, source positions, identifiers and cached status.

Prusti's high-level inference represents `MemoryBlock`, `Owned` and `MutBorrowed`; an owned permission can lower into unique-reference or fractional-reference resources. Its fold/unfold bookkeeping separates access and predicate permissions. MIR type-invariant encoding handles structs/enums, tuples, closures and references/boxes with type-specific machinery; borrow contracts track lifetimes and returned references. These source encodings explain how safe Rust borrow facts become permission VCs. They do not prove that arbitrary unsafe code, byte storage or a user contract is adequately represented. An extension needs a native meaning for its primitive and preservation of all permission invariants, not merely another Silver predicate.

### F7. SAW and Crux compositional MIR specifications

In [crux-mir-comp/DESIGN.md](https://github.com/GaloisInc/saw-script/blob/27a7ae98256544b55a7a3ce4ce620c1a7889713b/crux-mir-comp/DESIGN.md), `gather_assumes` and `gather_asserts` construct a method spec. Assertions generated while constructing that spec are discarded as proof goals; they define the proposed postcondition rather than verify its implementation. The builder filters variables and rejects unsupported symbolic-variable dependencies. It conservatively freshens mutable memory reachable through arguments, including UnsafeCell contents; raw constant pointers are treated as potentially mutable. It also handles mutable globals conservatively, but the documented specification language cannot constrain them.

The actual `Override.hs:314–339` converts preconditions to assertions and postconditions to assumptions. Its introductory comment says postconditions are asserted, but the implementation is decisive: they are assumed on the replacement path. It checks disjointness of matched allocations. Memory outside specified post-points-to information is retained, so the builder/frame relation must describe all relevant mutation. Restrictions on alias graphs, array extent and globals bound the compositional domain.

Installing a method override therefore checks callers against the specification; it does not establish the callee. Separate SAW verification/equivalence APIs may supply that evidence, but their complete Rust frontend, solver/certificate and existing zerocopy integration were not executed or exhaustively examined. This closes the method-spec/override research gap while leaving the actual equivalence experiment open.

## Boundaries

Answered with known constraints: result roles, incompleteness policies, permission vocabulary, inference endpoints, and the inspected compositional builder/override distinction. Known unsupported cases are only the explicit frontend/specification branches described above.

Remaining research: exhaustive current Infer Rust model/certificate scope; all inference soundness implementation connections; complete SAW verified-callee lifecycle and certificate routes; every tool's solver export options. No undocumented certificate is classified as absent. Existing zerocopy reuse, performance, independent replay and acceptance measurements require future experiments; this wave does not claim those prototypes exist.

## Evidence

Observed 2026-10-14. `source-evidence.json` supplies full repository revisions, Git blob identities and immutable links for all named implementation files, including the distinct historical Infer interface. The POPL paper's exact published version and theorem numbers are recorded in `literature.json`. The current Infer inventory/404 is a primary-source operational response and directory observation, not a negative result about all tool behavior. No executable source/tool installation occurred.

## Revalidation

Inspect the summary/result enums and every fallback path before comparing a new release. Preserve frontend, target, memory abstraction, bounds, solver and trusted contracts beside each run. Replay an inferred contract with explicit entry satisfiability and complete call coverage. For SAW/Crux, separately test spec construction, call replacement and actual callee verification, including an aliasing/mutation case; successful replacement alone must not count as a proof of the callee.

*Authored by an AI agent acting on joshlf's behalf.*
