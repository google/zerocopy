# Minimal proof interchange and the obligations of richer encodings

## Summary

Metamath/MM0 make proof application and substitution explicit, while MM0 additionally separates a readable specification from a binary proof artifact. Dedukti checks terms modulo supplied rewrite rules, so conversion and rewrite-system properties become part of the logic's boundary. A smaller checker can reduce implementation complexity without reducing the semantic work needed to encode a richer program logic.

The consumer must select the source specification and intended theorem. A certificate's internal statement or a producer-selected rewrite theory does not become the desired Anneal claim merely by passing its checker.

## Applicability

The four repositories are examined at the exact pins in REPORT.json. This is a source/format comparison, not a compatible export/import pipeline. No checker executable was built, installed, fuzzed, or run. MM0's MMB document describes format version 1 and explicitly warns it is not stabilized. The pinned Metamath implementation is metamath-exe, not an assurance claim about every independent Metamath verifier.

The report addresses T006/T007 and contributes to T012/P054. It gives concrete substitution/specification/conversion endpoints and qualitative encoding obligations. Numerical performance, full Rust/Iris encodings, and verified translations from Lean/Rocq remain open.

## Findings

### Explicit substitution makes local proof obligations visible

Basis: **source**.

Metamath's verifyProof processes the parsed proof stack and applies referenced assertion schemes through assignVar. Substitution must match the required hypothesis instances. The code explicitly handles unknown proof steps as incomplete; they are not ordinary complete proofs. It also checks $d obligations: substituted expressions for disjoint scheme variables may not share a variable, and required disjointness must be available in the theorem's own context.

At the end, the computed expression must equal the statement being proved. A mismatch reports a source error and increments errorCount. Therefore callers must inspect the full verification/error state, not only a comment or a scalar return value taken out of context. This audit did not follow the complete command caller and file-loader chain or establish a specific CLI exit contract.

Source: [mmveri.c](https://github.com/metamath/metamath-exe/blob/9898f5d1bb27045d764dd01672862a1c2a3b4f5e/src/mmveri.c), verifyProof (22–205), unknown-step handling (46 onward), assignVar and substitution matching (207 onward), $d checks (532–710), final statement comparison (180–199).

This style does not automatically decide the truth of axioms or identify a “standard” logic. The declarations and axiom database carry the chosen formal theory; the proof checker validates derivability within it. The consumer still needs a trusted policy for that specification and its interpretation.

### MM0 separates the consumer's specification from the binary witness

Basis: **normative** + **source**.

The pinned MMB specification describes little-endian tables for sorts, terms, and theorems plus proof/unification streams. The binary header identifies MM0B and version 1. Sort modifiers and binder dependency bitsets control permitted expression dependencies. Proof commands explicitly distinguish expressions and proofs, theorem application, hypotheses, conversion, and dummy-variable operations.

The specification requires public sorts/terms/axioms/theorems/definitions to match the next declaration in the separate MM0 specification. Local helpers need not appear in that file, but still undergo proof/definition checking. Forward references are prohibited. A definition's value appears in both proof and unify streams and must agree; this redundancy rules out cyclic expression encodings. The concluding unify stream consumes hypotheses and END requires none remain.

Source/specification: [mm0-c/mmb.md](https://github.com/digama0/mm0/blob/0d414c0bfdaaeb7fea571895127abc1fa5a3d956/mm0-c/mmb.md), header/tables (34 onward), streams (128–211), operational rules and final checks (268–462). The formal grammar endpoints are more precise than saying “a short checker checks the proof.”

The inspected C implementation enforces stack/unification constraints, checks dummy dependencies, checks header/table ranges, and calls parse_until for public statement alignment. Its final checks require all declared sorts/terms/theorems to have been processed and then parse the end of the MM0 specification. Source: [verifier.c](https://github.com/digama0/mm0/blob/0d414c0bfdaaeb7fea571895127abc1fa5a3d956/mm0-c/verifier.c), run_unify (213–324), proof operations (364 onward), verify (670–809).

These are actual implementation mechanisms, not a completed proof that this C parser/verifier is correct or memory-safe. Resource limits, fixed dependency masks, C compilation, and input-reading modules need separate assurance if deploying this exact executable. No such assurance was established here.

The specification/proof separation is directly useful to Anneal: the consumer can pin the MM0 file it means to accept while permitting proof producers to vary binary proofs and local checked helpers. That interface still requires a verified translation from the richer source statement to the selected specification if semantic interchange is claimed.

### Dedukti's conversion uses supplied rewriting as part of typechecking

Basis: **source** + **documentation**.

Dedukti's typing checker compares the inferred type with the expected type through SR.convertible; lambda checking weak-head-normalizes an expected product. check_rule infers the left-hand side pattern's type and constraints, constructs a typing substitution/context, checks the right-hand side against the same type under those constraints, and checks annotations. These are the inspected subject-reduction-related obligations for a rule, not a proof that arbitrary added equations are conservative relative to the source logic.

Source: [typing.ml](https://github.com/Deducteam/Dedukti/blob/f3c0eba869ddd46f2e75c123a59f2b612076dba0/kernel/typing.ml), check' (105–130), inference/checking (143–150), check_rule (360–410).

The pinned tutorial states that strong normalization and confluence are needed for decidable typechecking and are not generally checked by Dedukti itself; it describes the optional external confluence checker. The inspected Confluence.check returns immediately when no output file is configured; otherwise it invokes an external command and accepts a first output line YES, rejecting NO/MAYBE/failure. This implementation path does not internally prove the external answer. Sources: [TUTORIAL.md](https://github.com/Deducteam/Dedukti/blob/f3c0eba869ddd46f2e75c123a59f2b612076dba0/TUTORIAL.md), Confluence (388–397); [confluence.ml](https://github.com/Deducteam/Dedukti/blob/f3c0eba869ddd46f2e75c123a59f2b612076dba0/kernel/confluence.ml), configuration/init (23–46), check (193–213).

A logical encoding into the lambda-Pi calculus modulo therefore needs more than an accepted proof term: the signature and rewrite rules must encode the intended source logic, typing/convertibility must meet the relevant metatheory conditions, and the export must preserve the source theorem. Confluence and normalization can support decidability and stable conversion; they alone do not establish that a novel axiom or encoded primitive is true in the intended model.

### Lambdapi checks typing separately from general rewrite-system properties

Basis: **source** + **documentation**.

At `Deducteam/lambdapi@72cc2f10d391932fe078ba5a401765e29a1d4cb7`, the [rule documentation](https://github.com/Deducteam/lambdapi/blob/72cc2f10d391932fe078ba5a401765e29a1d4cb7/doc/commands.rst#L318) places general confluence and termination verification with the user, with external prover options. Its local critical-pair checking omits AC symbols and non-nullary pattern variables and reports non-joinability as a warning. Thus local checks do not establish general confluence.

The [command handler](https://github.com/Deducteam/lambdapi/blob/72cc2f10d391932fe078ba5a401765e29a1d4cb7/src/handle/command.ml#L228) initializes `sr_check` to true. Rule handling conditionally invokes `Tool.Sr.check_rule`, performs local confluence checking, then adds rules to the signature (254–284). This is a source-observed default, not an audit of every CLI configuration or the subject-reduction algorithm's metatheory. The same handler supports admitted proof termination (544–560); acceptance policy must independently exclude unwanted admitted assumptions.

For Anneal, Dedukti and Lambdapi both require a consumer-selected logical encoding and a policy for conversion, rule properties and assumptions. Lambdapi's additional local checks are useful evidence gates, but do not remove the encoding-correctness obligation. Exported Coq or Lean syntax also needs its own theorem-meaning comparison; merely having an exporter is insufficient. No exporter was executed here.

### Interchange transfers a formal derivation only after the encoding is justified

Basis: **derived**.

A richer program logic contains connectives, state/resource models, recursive predicates, invariants, and adequacy theorems. Encoding it into a minimal checker introduces obligations to represent binding/substitution safely, preserve inference rules, reflect the intended theorem, and account for source definitions or conversions. The translation may expand high-level proof steps into many low-level applications; code simplicity can move work and proof volume into the encoding layer.

No performance or proof-size number is claimed. The qualitative cost is an explicit proof/translation burden plus potentially larger witnesses; its magnitude requires a real representative encoding and measurement. A minimal checker cannot remove those semantic obligations merely by being easier to inspect.

For comparison, the prior proof-kernel wave distinguishes LCF/HOL abstract theorem construction from Lean/Rocq proof objects. The companion SMT report inspects Isabelle's separate replay/oracle selection. Those are authority interfaces in existing assistants, while MM0/Metamath/Dedukti supply alternate proof representations whose correspondence still needs proof. This report does not add a fresh HOL4/PVS kernel audit.

### Proposed Anneal acceptance contract

Basis: **derived**, not an implemented interchange tool.

The consumer should fix the theorem and theory specification before reading the candidate proof. An interchange adapter should produce checked evidence that the exported target statement expresses that source theorem, including any axiom/definition/rewrite assumptions. Keep the proof artifact's local helpers and export search untrusted where the target checker independently validates them.

Extensions should register through proved target rule interpretations or host proof terms. Accepting a new rewrite equation, signature constant, or axiom merely because the checker can parse it changes the theory and is a separate authority decision. The simplest useful pilot is one small theorem with binders and an explicit substitution side condition, followed by a round-trip statement comparison; a whole Rust/Iris logic encoding is a later project.

## Boundaries

**Answered subquestions:** explicit substitutions and disjointness; MM0 public-specification alignment and checked local helpers; Dedukti typing/conversion/rewrite conditions; why semantic encoding is an additional proof obligation.

**Research still open:** checker implementation correctness for these exact pins, complete loader/import assumptions, measured richer-logic encoding costs, cross-assistant exporters, and a concrete Rust resource-logic encoding. These gaps constrain implementation selection, not the stated source/grammar comparison.

**Future implementation obligations:** consumer-selected specification packaging, source-to-target correspondence evidence, extension policy, and binary/runtime validation. No deployed Anneal checker is claimed.

## Evidence

support/evidence.json records the original primary units and retrieved-content hashes. The parent additionally inspected Lambdapi's pinned `doc/commands.rst:318–346` and `src/handle/command.ml:228–284,544–560` on 2026-10-14; immutable links accompany the findings. MMB is a normative upstream format document for this pin; the Dedukti tutorial and Lambdapi manual are descriptive upstream documentation; the OCaml/C mechanisms are direct source evidence. Source mirrors are excluded from the package. No fresh execution or complete implementation soundness theorem is claimed.

## Revalidation

Reinspect the exact MMB version, public declaration matching, substitution/free-variable rules, and END checks. Follow Metamath's full caller/loader error handling before using an exit status as an acceptance contract. Reinspect Dedukti conversion and rule typing together with the configured confluence path; record all supplied rewrite rules. For interchange, compare the consumer's source theorem and the target specification under the proved translation before accepting any proof result.


*Authored by an AI agent acting on joshlf's behalf.*
