# Theorem construction, proof-object checking, and consumer-selected statements

## Summary

HOL Light's abstract theorem type restricts ordinary callers to the kernel's theorem-producing operations. Lean and Rocq instead check a supplied proof body against its declared type. These boundaries remove ordinary proof search from logical acceptance authority, subject to the checker, environment, and configuration actually used. Neither mechanism selects the user's intended proposition.

At the inspected Lean comparator revision, statement comparison, assumption-policy checking, and fresh kernel replay are separate stages. This is a concrete way to reject a valid proof of a changed question. It remains a source-audited implementation pattern: this report does not prove the comparator, export parser, process sandbox, or deployed checker binary correct.

## Applicability

The report directly inspects HOL Light `233b83c3202370e03c54de2bd090e4d34f677e91`, Lean `5045d0056413266e57c625dcd7c365b10e377c52` (4.34.1), Rocq `0b9568e12875891c1b9463fa3548f36384ea6f99`, and Lean comparator `865edc14486c3388e9225daa971da8e157488c3e`. These are separate subjects compared at their theorem/statement interfaces. No common executable composition of them was tested.

“Ordinary caller” means code respecting the host-language abstraction interface. It excludes arbitrary memory corruption, representation forging through privileged unsafe facilities, a substituted kernel, and direct access to trusted axiom constructors outside the consumer's permitted policy. The report identifies the boundary; it does not verify OCaml or every runtime beneath it.

The Lean source observations concern 4.34.1. Anneal's separately selected 4.31 toolchain was not examined, and no adjacent-version applicability is inferred.

## Findings

### HOL Light seals the theorem representation but exports several kinds of authority

In `fusion.ml`, `Hol_kernel` exposes `type thm` without its representation; the implementing `Hol` module represents it as a sequent of hypotheses and conclusion. External callers receive theorem values through the exported rules rather than a public sequent constructor. Rules such as `TRANS` and `EQ_MP` check the relevant equation or antecedent shape before combining hypotheses and producing a result. The type boundary prevents an ordinary tactic from directly constructing an arbitrary closed sequent.

The same signature exports `ASSUME` and `new_axiom`. They have different meanings: `ASSUME` creates a sequent retaining the supplied proposition as a hypothesis; `new_axiom` creates a closed theorem and records a new trusted root after checking that the term is propositional. Abstractness therefore does not itself prevent consumers from granting inappropriate axiom authority. Acceptance requires a policy for the exported roots as well as encapsulation of the theorem representation.

Basis: **source**, `fusion.ml`, `Hol_kernel`, `Hol`, `ASSUME`, `new_axiom`, `TRANS`, `EQ_MP`; **derived** authority interpretation.

### Definitional extension uses constrained kernel operations

`new_basic_definition` requires a closed right-hand term and rejects type variables not reflected in the constant's declared type. Its fresh constant is introduced with a defining equation. `new_basic_type_definition` requires a theorem with no hypotheses witnessing membership in a closed predicate, requires fresh abstraction/representation constants, and returns the two characteristic equations of the new type.

These are dedicated extension operations with explicit side conditions. Adding definitions through them differs from adding an unrestricted assertion through `new_axiom`. This source audit identifies the checks and resulting equations; it does not supply an independent semantic conservativity proof for every deployed HOL Light extension mechanism.

Basis: **source**, `fusion.ml`, `new_basic_definition`, `new_basic_type_definition`; **derived** distinction from arbitrary axiom introduction.

### Lean checks the core body, not the tactic's success report

Lean's `environment::add_theorem`, when checking is enabled, checks the declaration header, verifies that its type is a proposition, rejects unresolved metavariables/free variables, obtains the proof body's type with `type_checker::check`, and compares that type with the declared theorem type by definitional equality. `check` invokes inference in checking mode; the lighter `infer_type` uses an inference-only mode. A caller cannot substitute the latter's narrower contract for full checking of unvalidated terms.

The expression checker also rejects unsafe constants in non-unsafe declarations and partial definitions in safe declarations. Elaboration and tactics can propose a core term; acceptance depends on this checking path rather than the producer's claim that a tactic succeeded. Kernel bypass, admissions, native evaluation, and imported environments are qualified separately in the companion Lean report.

Basis: **source**, Lean `src/kernel/environment.cpp`, `add_theorem`; `src/kernel/type_checker.cpp`, `infer_constant`, `infer_type_core`, `check`.

### Rocq retains checking obligations for opaque proofs

At the inspected Rocq revision, `Constant_typing.infer_definition` infers the body's type and checks a cast against an explicitly supplied type. `infer_opaque` checks the header and retains a typing context for delayed body checking. `check_delayed` processes the proof and its side effects, infers its type, and checks it against the retained expected type. The fact that a body becomes opaque does not mean the body has no checking obligation.

This report does not audit the complete asynchronous scheduler or imported compiled-library checker. It also does not treat trusted side-effect signatures as freshly validated solely because the final cast is checked; their provenance and validity are additional premises in the inspected path.

Basis: **source**, Rocq `kernel/constant_typing.ml`, `infer_definition`, `infer_opaque`, `check_delayed`; `kernel/safe_typing.ml`, constant and opaque-proof entry paths.

### Statement comparison covers definitions as well as theorem names

Comparator's `compareAt` starts from consumer-selected theorem targets, allowed axioms, and designated definition holes. Theorem target headers must match in declaration kind and constant metadata, while the bodies may differ. It then traverses constants referenced by those types. Ordinary dependent declarations must match between challenge and solution; a declared definition hole may vary in body only while its header and safety match. Primitive targets are checked too, because matching a theorem's surface name while changing the definitions it uses changes its meaning.

The relation is the implementation's equality over exported core declarations, not an arbitrary semantic-equivalence decision procedure. A mathematically equivalent differently encoded statement may be rejected; this is a completeness issue for that comparison interface. Conversely, producer-generated challenge and solution artifacts that share the same mistake are not independently bound to an intended Rust claim by equality alone.

Basis: **source**, `Comparator/Compare.lean`, `definitionHoleMatches`, `compareAt`, `Compare.loop`; `Comparator/Util.lean`, `runForUsedConsts`; `Main.lean`, `primitiveTargets`, `verifyMatch`; **derived** meaning and completeness limits.

### Comparing statements and rechecking proofs answer different questions

`verifyMatch` parses challenge and solution exports, compares selected declarations, checks the solution's transitive axiom use, invokes configured external kernels, and replays the solution in a fresh built-in Lean kernel environment. Its quotient post-check compares exported quotient declarations with those created by the kernel. Any recorded checker failure prevents the final successful result.

The axiom allowlist is name-based, but `verifyMatch` also includes permitted axioms in the challenge-versus-solution comparison targets. The proposition attached to an allowed name therefore participates in a distinct comparison step. This is stronger than an isolated name allowlist; its assurance still depends on the challenge, export parser, equality relation, and replay path.

Multiple implementations do not establish independence merely because the configuration contains several names. Ports can share algorithms, primitives, exporter mistakes, or assumptions. This audit observes the orchestration and exact replay endpoints; it does not classify the external kernels' correlated-failure risks or execute them.

Basis: **source**, `Comparator/Axioms.lean`, `checkAxioms`; `Main.lean`, `verifyMatch`, `runBuiltinKernel`, `runExternalKernel`; **derived** independence limits.

## Boundaries

- **Not examined:** HOL Light or Rocq execution, a verified OCaml runtime, complete import and asynchronous proof checking, or all kernel escape hatches.
- **Not examined:** MM0 trusted challenges, Metamath, Dedukti, Lambdapi, and formal cross-logic encodings. Their agenda questions remain open.
- **Not examined:** comparator builds, parser fuzzing, sandbox enforcement, its migrated implementation, or independently run external checkers. The pin is an observed source snapshot, not a deployment recommendation.
- **Unknown:** whether a chosen external kernel supports every declaration needed by a particular Anneal theorem with the same primitive and assumption interpretation.
- **Not established:** consumer challenge correctness, a Rust-to-logic correspondence theorem, semantic adequacy of user contracts, or an end-to-end acceptance theorem for Anneal.
- **Not established:** a proof that the inspected C++/OCaml implementations correctly implement their mathematical logics. Source inspection and implementation soundness are separate evidence obligations.

## Evidence

All Git links below identify immutable primary source. `support/source-index.json` preserves retrieval identities and source-text hashes.

- [HOL Light fusion kernel](https://github.com/jrh13/hol-light/blob/233b83c3202370e03c54de2bd090e4d34f677e91/fusion.ml): module signature/representation at lines 12–104; inference and root constructors at lines 488–640.
- [Lean theorem insertion](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/kernel/environment.cpp#L192): `add_theorem`, lines 192–209.
- [Lean expression checking](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/kernel/type_checker.cpp#L101): `infer_constant`, lines 101–121; `infer_type_core` and `check`, lines 323–372.
- [Rocq constant checking](https://github.com/rocq-prover/rocq/blob/0b9568e12875891c1b9463fa3548f36384ea6f99/kernel/constant_typing.ml#L212): `infer_definition`, `infer_opaque`, `check_delayed`, lines 212–291.
- [Comparator core comparison](https://github.com/leanprover/comparator/blob/865edc14486c3388e9225daa971da8e157488c3e/Comparator/Compare.lean): `compareAt` and dependency worklist.
- [Comparator axiom closure](https://github.com/leanprover/comparator/blob/865edc14486c3388e9225daa971da8e157488c3e/Comparator/Axioms.lean) and [dependency traversal](https://github.com/leanprover/comparator/blob/865edc14486c3388e9225daa971da8e157488c3e/Comparator/Util.lean).
- [Comparator acceptance stages](https://github.com/leanprover/comparator/blob/865edc14486c3388e9225daa971da8e157488c3e/Main.lean): `runBuiltinKernel`, `primitiveTargets`, `verifyMatch`, `compareIt`.

No fresh execution evidence was acquired for this package. The companion Lean package supplies explicitly scoped Lean experiments.

## Revalidation

For a new subject, first diff the theorem constructor/checker and extension operations rather than the tactic interface. Confirm that the actual acceptance call enables checking and uses a validated environment. Inspect any axiom constructor or delayed/trusted body path consumed by the result.

For statement comparison, mutate a dependent definition, an allowed axiom's type, and the theorem header separately; the consumer-owned challenge must remain fixed. Then replay the actual solution proof from a data-only export in a fresh selected checker. Check the exporter/parser and primitive interpretation independently. Agreement between changed challenge and solution alone is insufficient.

*Authored by an AI agent acting on joshlf's behalf.*
