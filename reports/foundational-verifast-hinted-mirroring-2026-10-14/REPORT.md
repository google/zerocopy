# Foundational VeriFast: checked replay and its remaining Rust semantic frontier

## Summary

Hinted mirroring is a useful mechanism for Anneal: an untrusted fast verifier records search decisions, while a simpler foundational replay checks the resulting semantic obligations. It can remove the original search implementation from the justification of an accepted derivation without requiring the checker to rediscover the search.

The examined VeriFast development separates replay soundness from Rust semantic adequacy. At the pinned implementation, the replay has a proved connection to an Iris axiomatic semantics, but that semantics still contains admitted definitions and rules, including explicitly unsound treatment of local storage lifetime operations. Its theorem named `verified_program_has_no_ub` concludes a proposition defined through that axiomatic semantics; the name does not establish an independently proved operational Rust safety theorem.

The transferable result is a certificate architecture and a concrete account of its remaining obligations, not an end-to-end proof for arbitrary unsafe Rust. No Rocq development was built in this investigation.

## Applicability

This report compares the January 2026 paper's proposed architecture with directly inspected files at VeriFast revision `0a83dba42db7ce0b445034ece5298afe980e57dc`. The paper and source are separate subjects: source observations do not establish that this commit is the paper's artifact revision. Anneal implications refer to the PR stack at `cce761ad53785973ec2f4a6b13715b770b340c87`, particularly its requirement to retain the obligations preceding source UB.

Agenda scope: R038 and T027 are directly addressed; T114 is addressed for the comparison between verifying an executor implementation and checking per-run replay. P043 and P052 receive a concrete replay mechanism. Broader Rust verification capabilities, current build success, and general performance are outside this report.

## Findings

### Hints select witnesses; checking must still justify the selected step

The paper records heap-chunk choices, implicit predicate operations, and branch-pruning decisions in a symbolic execution tree. Replay translates those choices into logical obligations rather than accepting an SMT answer as authority. The source implements this distinction concretely: `consume_chunk` takes a chunk index from the tree and rejects an absent index, while `consume_points_to` requires matching type and pointer equalities before continuing.

Thus the search engine can choose the wrong chunk; an accepted replay still needs the facts making that chunk suitable. For Anneal, hints can identify a borrow resource, frame, primitive summary, or branch invariant without granting permission to assume it. Each hint constructor requires a checked semantic interpretation.

Basis: **documentation**, paper §3; **source**, `SymbolicExecution.v`, `consume_chunk` and `consume_points_to`; **derived**, proposed Anneal hint boundary.

### Replay is about explicit bodies, contracts, and proof trees

`body_is_correct` compares the specification's parameter and result types with the body's types, introduces typed arguments, produces the precondition, verifies the body, and consumes the postcondition. `named_body_is_correct` requires a specification and replay tree for each listed function. `bodies_are_correct` folds correctness over the provided body list.

These are useful local binding checks. They do not by themselves prove that the list is the complete executable closure of the requested Rust subject, that the bodies faithfully encode compiler MIR, or that the contracts express the consumer's intended property. Those are separate required arguments. The paper makes faithful body encoding and specification meaning explicit conditions of its interpretation.

Basis: **source**, `SymbolicExecution.v`, `body_is_correct`, `named_body_is_correct`, `bodies_are_correct`; **documentation**, paper §3; **derived**, distinction between list-local correctness and Rust claim coverage.

### The replay theorem's target is an axiomatic semantics

`SymexSoundness.v` proves a chain of lemmas relating symbolic heap operations and execution steps to Iris assertions, culminating in `bodies_are_correct_sound`. Its final `verified_program_has_no_ub` theorem uses a selected `main` contract and concludes `program_has_no_ub`.

The latter is defined in `AxSem.v` as provability of `wp_Program` for `main`. At this revision, `wp_Program` and its introduction rule are admitted; so are lower-level memory and evaluation primitives. The investigated chain establishes a conditional relationship to these primitives. It does not supply a concrete machine interpretation merely because the final proposition has a Rust-safety name.

The structural audit found 32 `Admitted.` tokens, four `Axiom` declarations, and two `Parameter` declarations in `AxSem.v`; `SymexSoundness.v` contains five `Axiom` and one `Parameter` declarations. These are lexical counts of the inspected files, not transitive theorem-assumption counts. Some admitted objects are definitions rather than inference lemmas, and the counts cannot substitute for `Print Assumptions` on a built artifact.

Basis: **source**, `AxSem.v` and `SymexSoundness.v`; **execution**, retained lexical audit; **derived**, limit on the semantic conclusion.

### Ignoring local storage transitions is a concrete adequacy defect

`SymbolicExecution.v` preserves the same state through `StorageLive` and `StorageDead`. The corresponding axiomatic rules are named with an `UNSOUND` suffix and carry comments linking upstream issue #948. `SymexSoundness.v` applies those rules and notes that the local typing environment will need to change when storage transitions are supported.

Upstream issue #948 was open when observed and describes the refinement checker ignoring these operations even though their placement can affect UB. This current issue observation and the immutable source observation have different freshness: the report's code facts remain about the pinned revision if the issue later closes.

This is especially relevant to Anneal's admission and lowering boundary. A checker can replay every step of a simplified model correctly while the simplification loses a source lifetime obligation. Source-to-model correspondence and concrete semantics adequacy must therefore remain independent acceptance obligations.

Basis: **source**, `SymbolicExecution.v:488`, `AxSem.v:115`, `SymexSoundness.v:677`; **documentation**, upstream issue #948 and paper §4; **derived**, Anneal constraint.

### Conservative incompleteness is visible in the replay interface

The replay emits error propositions for unsupported operands/rvalues, missing function specifications or proof trees, absent blocks, and exhausted block fuel. `VfMir.v` itself defines a small representation with raw pointers, booleans, scalar type names, a limited set of rvalues, and a few terminators; constructor presence is not proof that every constructor is semantically supported.

For example, block execution uses fuel derived from the number of blocks. This is an implementation observation, not a guarantee that arbitrary loops are handled through invariants. The paper lists loops, structs, generics, unwinding, fractional permissions, and safe-abstraction semantic typing among work remaining in that paper's system.

Anneal can use a similarly conservative checker, provided inability to replay is never normalized into an ordinary verified result. Adding a new hint or IR operation requires either a proved semantics rule or an explicit remaining trusted premise.

Basis: **source**, `VfMir.v`, `verify_basic_blocks`, `verify_body`, and error branches; **documentation**, paper §5; **derived**, fail-closed extension criterion.

### Verifying the executor and replaying its runs have different maintenance costs

A once-for-all proof of an executor implementation must cover the algorithm and the actual implementation path used. Hinted replay instead concentrates proof obligations on a simpler step checker and the semantics of hints; the original implementation may change its heuristics freely when it still emits checkable evidence.

Neither route removes input capture, semantic definition, contract adequacy, closure coverage, or checker execution from consideration. Replay also pays per-run evidence-generation/checking costs, and its accepted domain may be smaller than the producer's domain. This investigation did not measure those costs or establish feature parity.

For a future Anneal prototype, the discriminating test is a mutation suite: select the wrong resource, omit a side condition, mark a feasible path impossible, alter a body, omit a callee, and remove a storage transition. The expected rejection criterion must be tied to the independently selected source claim, rather than just the producer's replay model.

Basis: **derived** from the inspected producer/replay separation and the observed admission limitations.

## Boundaries

- **Not examined:** a fresh Rocq build, the original OCaml verifier as a whole, its complete Rust frontend, solver interactions, or all imported dependencies.
- **Unknown:** transitive assumptions of the compiled final theorem, current performance, and whether all paper examples build at this source pin.
- **Known not to establish:** an independently justified source-Rust UB-freedom theorem from the inspected replay theorem alone; its semantic primitives and import correspondence remain separate obligations.
- **Unsupported in the paper's stated prototype:** the listed extensions in §5. This list is not silently generalized to every later VeriFast configuration.
- No claim is made that all of VeriFast is unsound, that every use of the narrow prototype fails, or that a logical kernel accepted an invalid proof. The identified limitation is the concrete adequacy of the interpreted model and the assumptions under which its replay theorem operates.

## Evidence

- **documentation:** Bart Jacobs, [Foundational VeriFast, arXiv:2601.13727v1](https://arxiv.org/html/2601.13727v1), §§3–5, inspected 2026-10-14. The paper's interpretation and limitations are distinct from this report's implementation audit.
- **source:** [VfMir.v](https://github.com/verifast/verifast/blob/0a83dba42db7ce0b445034ece5298afe980e57dc/bin/rust/rocq/VfMir.v), types and statement/terminator constructors.
- **source:** [SymbolicExecution.v](https://github.com/verifast/verifast/blob/0a83dba42db7ce0b445034ece5298afe980e57dc/bin/rust/rocq/SymbolicExecution.v), `consume_chunk`, `consume_points_to`, `verify_statement`, `verify_basic_blocks`, and body-correctness definitions.
- **source:** [AxSem.v](https://github.com/verifast/verifast/blob/0a83dba42db7ce0b445034ece5298afe980e57dc/bin/rust/rocq/AxSem.v), admitted primitive semantics, storage rules, `wp_Program`, and `program_has_no_ub`.
- **source:** [SymexSoundness.v](https://github.com/verifast/verifast/blob/0a83dba42db7ce0b445034ece5298afe980e57dc/bin/rust/rocq/SymexSoundness.v), storage-step proof, `bodies_are_correct_sound`, and final theorem.
- **documentation:** [VeriFast issue #948](https://github.com/verifast/verifast/issues/948), observed open 2026-10-14; an issue's current state is not an immutable code fact.
- **source:** [Anneal admission design](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/ADMISSION_DESIGN.md), original-MIR retention and first-bad-step obligations.
- **execution:** `support/selected-source-audit.json`, produced by lexical scan of four files at the identified source pin. No Rocq executable was found by local command lookup; this is an environment observation, not an upstream support classification.

## Revalidation

Run `python3 support/audit_upstream.py /path/to/verifast-clone`. The script reads the immutable Git objects at this report's pin instead of trusting the checkout contents and returns only counts and storage-transition line locations. Compare the definitions and theorem statements at a new revision explicitly rather than merely relabeling this report.

For stronger assurance, build the exact upstream Rocq development with its compatible dependencies, obtain `Print Assumptions` for the final theorem, and inspect a proved operational adequacy theorem covering the same VF MIR representation. Then separately establish source import, executable closure, contract domain, and caller coverage. The lexical probe cannot discharge those obligations.

*Authored by an AI agent acting on joshlf's behalf.*
