# Source-safety reflection: kernel-checked counterexample and Rust optimization probe

## Summary

A relation that preserves every already-defined source execution does not imply that a safe target model represents a safe source. The retained Lean experiment proves that implication false for an explicit finite outcome model. It also proves that exposing each source UB outcome as a model UB outcome transfers model safety to source safety and composes across passes.

The separate Rust compilation probe exhibits the practical erasure boundary: an ordinary safe function containing a reachable `unreachable_unchecked` branch and an always-returning function compile to the same instruction bodies at the observed optimized AArch64 target. This is permitted optimization of undefined source behavior, not a compiler-correctness defect. The Rust function containing UB was never executed.

These are discriminating experiments and abstract theorems. They are not a verified Rust interpreter, an Anneal extraction certificate, or an end-to-end safety proof for the emitted code.

## Applicability

The Lean subject is version 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, using `Std`, kernel checking, and ordinary tactics. It is distinct from Anneal's pinned Lean 4.31. The Rust subject is 1.99.0, commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, host `aarch64-apple-darwin`, LLVM 23.1.1. Compilation uses edition 2024, a library crate, `debug-assertions=no`, and optimization levels 0 and 3. The emitted target triple is `arm64-apple-macosx11.0.0` with the observed Apple M1 target CPU attribute.

`support/Reflection.lean` defines programs as functions from Boolean inputs to three outcomes: return a natural number, UB, or divergence. These are stipulated mathematical outcomes; they are not an import or mechanization of Rust semantics. The source-program example has UB on one input and returns seven on the other. The model always returns seven.

Agenda scope: P032, P034, P037, P038, P094, P133, T073, T101, T107, and R004 receive narrow formal or experimental evidence. The result illustrates source-safety transfer, pass composition, erased failure, and narrowed domain coverage. It does not close their real-Rust semantic, frontend, or general nondeterministic obligations.

## Findings

### Ordinary preservation can accept an unsafe source and a safe model

The experiment's `DefinedPreservation source model` requires equal outcomes only when the source outcome is not UB. Its `Safe` predicate excludes UB on every input. Lean checks all three facts:

1. `constantModel` is safe.
2. `brokenSource` is unsafe.
3. Defined-execution preservation holds from the broken source to the constant model.

`ordinary_preservation_does_not_reflect_safety` combines them into a proof that the universal safety-transfer implication is false. This is a logical counterexample under the displayed definitions, not an empirical claim about an optimizer's correctness theorem.

The useful discrimination is the relation's premise: excluding source UB from the executions to compare removes the very case needed to infer that UB cannot occur. A valid target-property proof and a valid ordinary-preservation proof can therefore coexist with an invalid source-safety conclusion.

Basis: **execution**, checked `Reflection.lean`; **derived**, implication for selecting Anneal correspondence relations.

### Source-failure exposure supplies a safety-transfer theorem

`FailureReflection source model` requires that each UB source outcome at an input has a UB model outcome at the same input. The checked theorem `failure_reflection_transfers_safety` establishes:

```text
FailureReflection(source, model) ∧ Safe(model) ⇒ Safe(source).
```

Its proof uses the forbidden model outcome to contradict universal model safety. `failure_reflection_composes` shows transitivity of this relation. The erased-failure example is rejected by `erased_failure_rejected`.

This provides a minimal, explicit theorem shape for P032 and P038. A real translation may change states, argument representation, and nondeterminism. It then needs entry-state coverage, step/outcome simulation under a representation relation, and success-state preservation enabling sequential composition. This finite theorem does not justify those additional premises. In particular, direct outcome transitivity is not a proof of a state-changing compiler pipeline.

Basis: **execution**, kernel-checked general theorems; **derived**, relationship to richer translation certificates.

### A narrowed decoder domain can turn the source theorem conditional

`narrowed_domain_is_safe` proves the same broken source safe on the domain containing only its non-UB input. This theorem is true. It does not contradict the checked theorem that the source is unsafe on all inputs.

The experiment distinguishes proof validity from claim adequacy: changing the domain changes the claim. For an unsafe function, an explicit caller obligation may justify a restricted entry domain; for a safe API advertised over all valid inputs, silently introducing that restriction would omit a permitted caller.

The Boolean witness is intentionally small. It does not validate a concrete Rust decoder, ghost domain, or semantic typing interface. A future real-API certificate must justify the relation between public inputs and model inputs independently of the producer's chosen domain.

Basis: **execution**, `narrowed_domain_is_safe`; **derived**, safe-caller coverage requirement.

### The Rust optimization probe erases the source branch

The owned Rust input defines `broken_safe_api(input: u8)` with a zero-input branch calling `std::hint::unreachable_unchecked`, then returns seven. `always_seven` returns seven directly. The Rust 1.99.0 documentation states that reaching the intrinsic is UB and that branches leading invariably to it can be removed. Zero is an ordinary valid `u8` input, and the function's signature is safe.

At optimization level 3, both emitted AArch64 bodies consist of setting the return register to seven and returning. The optimized LLVM bodies also return seven directly, but their function attributes differ; this report does not infer LLVM semantic equivalence from matching body text alone. At level 0, the original input comparison and intrinsic/precondition-related paths remain visible in the LLVM output.

The observed transformation is consistent with the documented intrinsic contract. It demonstrates why an analysis beginning only from the optimized target can lose a source obligation even when the target computes a simple total result. The probe does not run the unsafe source path or demonstrate a compiler bug.

Basis: **normative/documentation**, Rust 1.99.0 intrinsic safety contract; **execution**, retained compiler outputs; **derived**, extraction-boundary consequence.

### Checking and assumptions remain explicit

Seven commands succeeded: tool identities, Lean checking, and four Rust emission commands. `#print axioms` reports no axioms for the failure-transfer and composition theorems. The counterexample, rejection, and narrowed-domain theorems use Lean's `propext`; this report does not label all proofs axiom-free. No `sorry`, admitted source semantics, or native-decision procedure occurs in the owned Lean input.

Checking the Lean propositions does not check Rust import, compilation, or correspondence to machine execution. The Rust observation and mathematical theorem are related by the report's argument, not by a machine-checked Rust-to-Lean import theorem. That remaining connection is the subject of future certificates, not an assumption silently discharged by this experiment.

Basis: **execution**, command statuses, retained axiom output, and source; **derived**, separation of assurance layers.

## Boundaries

- **Not examined:** other targets, Rust or Lean versions, compiler settings, or an actual Anneal/Charon/Aeneas run.
- **Not established:** concrete Rust semantics adequacy, multi-step first-bad-prefix correspondence, nondeterministic execution coverage, provenance, typed storage, cleanup, concurrency, or a verified checker binary.
- **Known distinction:** the Lean outcome model allows divergence without UB; the simple counterexample still shows why replacing prior UB with an accepted divergence marker would need separate justification.
- No inference that all compiler refinement relations are inadequate: stronger relations can preserve/reflect source failures, and source safety can also be proved separately before a weaker preservation leg is used.
- The source function containing UB was compiled but not executed. Emitted instruction text is an observation rather than a formal ISA safety proof.
- `propext` is a reported logical assumption, not a Rust memory or compiler premise.

## Evidence

Observed 2026-10-14 on the tool identities recorded in `support/lean-version.stdout.txt` and `support/rust-version.stdout.txt`.

- **execution/source:** `support/Reflection.lean`, checked with `lean -DwarningAsError=true Reflection.lean`; theorem names and axiom output are in `support/lean-check.stdout.txt`.
- **execution/source:** `support/erased_ub.rs`, `support/erased-ub-o0.ll`, `support/erased-ub-o3.ll`, and emitted assembly at both optimization levels.
- **execution:** `support/results.json` preserves exact command argv, return codes, stream paths, and SHA-256 hashes of owned source and captured output. Empty stderr is a recorded stream, not evidence that a command succeeded without its status.
- **normative/documentation:** [Rust 1.99.0 `unreachable_unchecked` documentation](https://doc.rust-lang.org/std/hint/fn.unreachable_unchecked.html), displayed compiler `b940084d7`, safety contract and optimization explanation; corresponding installed toolchain documentation was also located. The moving web URL must be checked for version before reusing it.
- **source/documentation:** [Anneal PR-stack admission design](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/ADMISSION_DESIGN.md), original MIR and source-UB obligations; this experiment does not instantiate its proposed Rust correspondence.

## Revalidation

Run `python3 support/run_probes.py` using the exact named toolchains when reproducing this report. It uses existing Lean and Rust executables, retains separate output streams and command statuses, and never invokes the Rust functions. Inspect the resulting version files before comparing outputs. Running it with a changed toolchain is a new observation, not automatic extension of this report's applicability.

For another correspondence relation, attempt the same unsafe-source/safe-model pair and a deliberately narrowed public domain. A required source-safety certificate should reject the former and require independent caller-domain coverage for the latter. Add multi-step, divergent, nondeterministic, cleanup, and representation-changing controls before claiming general Rust support.

*Authored by an AI agent acting on joshlf's behalf.*
