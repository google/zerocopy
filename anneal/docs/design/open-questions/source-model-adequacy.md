<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Source/model adequacy

**Status:** Open design discussion.

Anneal's intended verification pipeline uses Aeneas and Lean to prove that
unsafe operations satisfy their preconditions, yet the correspondence between
Rust and the generated model is only promised for sound Rust programs. An
unsound Rust program may be lowered to a Lean definition that bears no useful
relationship to its source. V2 must close this apparent circularity rather
than merely assume that successful Lean proofs describe the original program.

## Settled constraints

- Soundness is non-negotiable. A Lean theorem about an inadequate model is not
  a soundness result about Rust.
- The soundness preconditions of primitive or otherwise trusted unsafe leaves
  must conservatively reflect Rust's normative guarantees. Anneal's authors are
  responsible for their adequacy, and any remaining assumptions belong in the
  trusted computing base.
- Every applicable callee precondition must be discharged or explicitly
  recorded as a trust gap. Missing a call site cannot count as verification.
- Encoding precondition proofs as Lean function arguments and proving separate
  call-site theorems are both candidate spellings. Neither representation by
  itself resolves semantic adequacy; either can work only with complete
  enforcement.
- The initial unit of a claim is one concrete Cargo compilation artifact with a
  fixed target, features, `cfg`s, panic strategy, dependencies, and relevant
  environment—not a promise over every possible build matrix.
- Proc-macro output and code generated through the compilation process are
  analyzed input, not trusted source generators. The expanded artifact that
  reaches Charon must be covered.
- Rust, Charon, Aeneas, and Anneal changes are all in scope when needed to
  establish a defensible result.
- Model and tool failures must not be mistaken for successful source
  verification.

## The required semantic connection

We need a precise theorem connecting source executions, extracted semantics,
and generated proof obligations. Its exact statement is open. Candidate proof
families include:

- an execution-prefix argument showing correspondence while validity
  conditions hold and ruling out a first invalid operation by proving every
  required guard;
- a forward or backward simulation maintained under an explicit source
  validity invariant; and
- per-artifact translation validation that checks the extracted operations and
  obligations against a separately justified semantic relation.

These are sketches, may overlap, and are neither exhaustive nor accepted. Any
formulation must account for nondeterminism, concurrency, unwind and abort
behavior, infinite executions, provenance, external effects, compiler
transformations, and whatever relation Aeneas actually proves between LLBC and
Lean.

The important distinction is between the semantic argument and the Lean API
used to present an obligation. Proposition-valued parameters make unguarded
model calls ill-typed; sidecar WP theorems may reuse Aeneas machinery more
directly. Either presentation still requires a theorem explaining why proving
the obligations rules out undefined source behavior.

## Questions to resolve

### Where is the authoritative program captured?

- At which rustc phase must Charon extract the program so operations are still
  present and their semantics have not already been changed by optimizations
  that assume away undefined behavior?
- Are MIR and LLBC sufficiently expressive to identify every relevant unsafe
  primitive and path, including drop glue, compiler-generated shims, intrinsics,
  unwinding, and monomorphized calls?
- What compiler transformations occur before extraction, and what assumptions
  do they make?
- Which source annotations survive expansion and lowering, and how are they
  reconciled with compiler-resolved items?

[Issue #3041](https://github.com/google/zerocopy/issues/3041) raises the risk
that extraction after UB-exploiting optimization could erase exactly the
operation Anneal needs to guard. This remains an investigation; V2 must not
assume the current extraction point is adequate without evidence.

### What counts as complete coverage?

- How are direct calls, trait dispatch, function pointers, closures, virtual
  calls, recursion, drop glue, statics, and compiler intrinsics enumerated?
- Is proof coverage stated over syntactic call sites, semantic operations,
  reachable monomorphized instances, or another unit?
- How are unreachable code and dead branches justified?
- What happens when Charon or Aeneas omits an unsupported construct?
- How does separate compilation carry verified contracts without assuming that
  dependency code was built with different features or targets?
- How does Anneal prove that its annotation index and the LLBC artifact describe
  the same items?

Coverage should be machine-checkable and appear in the audit artifact where it
depends on assumptions. See
[Aeneas and Charon integration](aeneas-charon-integration.md) and
[trust and incremental adoption](trust-and-incremental-adoption.md).

### What semantics do leaf guards express?

Raw pointer dereference, pointer arithmetic, reads and writes, allocation,
deallocation, intrinsics, inline assembly, and FFI have different semantic
foundations. For each leaf V2 must determine:

- the Rust operation being modeled;
- the precondition sufficient to rule out its undefined behaviors;
- the result and effects available to subsequent proofs;
- resource ownership or provenance consumed and produced;
- panic, unwind, abort, and divergence behavior where applicable; and
- which facts are proven, derived from Rust's specification, or trusted.

An explicit set of assumptions is not automatically a conservative model of
normative Rust guarantees. The relationship must itself be documented and,
where possible, mechanized. Resource-bearing guards are discussed in
[memory, resources, and effects](memory-resources-and-effects.md).

### What must be proved about the toolchain?

- Is the adequacy theorem end-to-end, or a composition of rustc-to-LLBC,
  LLBC-to-Lean, Anneal instrumentation, Lean kernel, and code-generation claims?
- Which translations are formally verified, validated per artifact, tested, or
  trusted?
- Can Anneal independently validate that generated Lean contains all expected
  obligations without brittle text rewriting?
- Which host compiler, LLVM, linker, and target hardware assumptions affect the
  final claim rather than only tool availability?

These questions do not require V2 to verify its entire toolchain immediately.
They do require an honest boundary and a path to shrink it.

## Candidate approaches

Candidate work can be combined:

- extend Charon with compiler-resolved annotations and an operation index;
- validate LLBC against an independently generated obligation manifest;
- extend Aeneas's WP semantics with guarded unsafe leaves;
- make guards proposition-valued inputs to selected generated Lean functions;
- generate sidecar theorems and have Anneal verify one theorem per indexed
  operation;
- prove an adequacy or trace-simulation theorem connecting complete guards to
  source validity; and
- add fail-closed coverage checks for every unsupported or unmatched item.

Textual patches to generated Lean are less desirable than programmatic
interfaces, but the criterion is robustness and semantic auditability, not a
categorical ban on any implementation technique.

## Evaluation criteria

A successful approach must state exactly which source artifact it covers,
identify every operation that can invalidate the source/model relationship,
make missing obligations detectable, preserve outcome and resource semantics,
and expose its trusted assumptions. It should also let V2 reuse Aeneas's WP
machinery rather than rebuilding it without need.

The result should survive adversarial examples: an invalid operation optimized
away, an unsafe action in generated drop glue, a trait call resolved only after
monomorphization, and a panic path that runs unsafe cleanup.
