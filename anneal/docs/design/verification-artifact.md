<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Verification subject and result identity

Anneal's initial verification subject is one concrete Cargo compilation
artifact. A result does not automatically apply to every feature combination,
target, build profile, dependency resolution, or environment in which the same
source files might compile.

In this canon, “compilation artifact” names the compiler-resolved Rust program
and semantic configuration selected as the subject of a claim. It does **not**
mean the native executable, library archive, or other file emitted by Cargo;
those belong to the later binary-execution layer. “Compilation subject” is the
preferred phrase when that distinction matters.

A verification result is the evidence and claim produced about that subject
under selected properties, models, proof inputs, and trust assumptions. Those
two identities must not be conflated: changing Aeneas or a Lean proof may
produce a different verification result without changing the Rust compilation
artifact being checked.

The single-subject scope is a settled starting point. The exact compilation-
subject manifest, verification-result identity, and audit ledger are not yet
implemented and remain design work.

## What fixes the compilation subject

At minimum, the compilation subject must distinguish every input that can
change the Rust program presented to Charon or its source-level semantics:

| Dimension | Examples |
| --- | --- |
| Cargo selection | workspace, package, library/binary/example/test target, target kind |
| dependency resolution | lockfile, exact source and version, enabled dependency features |
| Rust configuration | crate features, `--cfg` values, target triple and target specification |
| compilation behavior | profile, overflow checks, panic strategy, relevant codegen options |
| source generation | proc-macro expansion, build-script outputs, generated files included by the crate |
| compilation environment | environment variables and build-script directives which affect the selected Rust program |
| Rust frontend | rustc and standard-library version, and compiler options which affect the selected program |

Changing a claim-relevant compilation input produces a different subject. It
may be cheap to verify a related subject, but the prior result must not be
silently generalized to it.

## What fixes the verification result

In addition to identifying its compilation subject, a result must identify the
evidence and assumptions used for its claim. These include:

- selected properties, policies, and dependencies;
- the Charon version and extraction options, and the LLBC actually consumed;
- the Aeneas and Anneal versions, models, generated obligations, and options;
- the Lean, Lake, Mathlib, and other proof-library versions and checked proof
  artifacts;
- proof and coverage status, trusted leaves, axioms, and other assumptions;
  and
- the claim layer being reported and the trust needed to reach it.

Changing one of these inputs may leave the compilation subject unchanged while
producing different evidence or a different claim. Results are not
interchangeable unless Anneal has a sound equivalence argument for the changed
input.

An end-to-end execution claim needs further provenance even when it does not
change the source-level compilation subject: LLVM and other compiler
components, linking, host and target operating assumptions, and the host and
target hardware implementations. See [the trust model](trust-model.md).

## How to classify an input

Classify an input by what it can change:

- If it can change the compiler-resolved Rust program or its source-level
  semantics, it participates in compilation-subject identity.
- If it can change extraction, the model, obligations, checked evidence,
  selected properties, assumptions, or the claim reported, it participates in
  verification-result identity.
- If it changes only the relation between that Rust program and an emitted
  binary or concrete execution, it qualifies the execution claim rather than
  the source-level compilation subject.

One component can have more than one role. A rustc revision may change the
selected program and also remain part of the trusted toolchain. An environment
variable may change generated Rust, a proof invocation, or neither. Classify
the actual dependency rather than assigning a component permanently to one
bucket.

A verification result may report any of the
[claim layers](verification-model.md#layers-of-a-claim). It must name the layer
it reports. If it does not reach binary execution, the ledger must say that no
target-hardware execution claim is being made rather than imply that such a
claim was proved. Host hardware running the proof checker may still be part of
the practical TCB.

The exact normalization of these identities and the treatment of edge cases
remain open. Not every provenance field recorded in a ledger must become part
of a future canonical result identifier; recording a field and defining when
two results are semantically interchangeable are different design questions.

## Generated Rust is input, not an axiom

Build scripts and procedural macros execute before or during compilation and
may determine the code that rustc sees. Anneal verifies the resulting,
compiler-resolved Rust artifact just as it verifies checked-in Rust source.
The generated code is not trusted merely because its generator ran outside
Anneal's proof language.

This gives the right semantic boundary but does not erase provenance concerns:

- the proof applies to the generated artifact, not to every possible output
  of the generator;
- a changed host environment or generator version may produce a different
  compilation subject and therefore requires a new result; and
- executing a build script or proc macro is itself a build-system and host
  security concern, even though its output receives no semantic exemption.

Where source mapping permits, diagnostics should identify both generated code
and its originating invocation. The audit ledger should record enough build
provenance to reproduce the compilation subject.

## Source, model, binary, and hardware

Several related objects must not be conflated:

1. The Cargo/rustc artifact is the Rust program selected for verification.
2. Charon's LLBC is the extracted representation of that artifact.
3. Aeneas and Anneal produce a Lean model and proof obligations.
4. rustc and LLVM produce a binary for a target.
5. Target hardware executes that binary.
6. The verification result records the subject, checked evidence, claim, and
   assumptions connecting the relevant layers.

Anneal's direct proof is over the Lean model. A user-facing end-to-end claim
therefore depends on correspondence between these layers. In the near term,
some correspondences and implementations will be trusted rather than proved.
They must be visible in the trust ledger; a green result must not imply that
Anneal has formally verified rustc, LLVM, an ISA implementation, or physical
hardware when it has not.

The same applies on the host side. The compiler, proof checker, operating
environment, and hardware which execute Anneal are part of the practical TCB
unless independently checked. Recording them is not proof of correctness, but
it makes the residual trust explicit and auditable.

## Local and global claims

For one compilation subject, the intended local shape is:

- each function's preconditions imply its postconditions for the applicable
  outcomes; and
- each function satisfies all required preconditions and property
  dependencies of its callees.

Assuming correct specifications for the trusted primitive leaves and adequate
source/model correspondence, these local facts compose into artifact-level
properties such as Rust soundness. User-defined property domains compose in
the same general way, although their axiomatic specifications express user
intent rather than a Rust-defined ground truth.

The exact treatment of return, panic and unwind, abort, divergence, and model
failure is still open. Do not interpret "one compilation artifact" as "one
normally terminating execution." Servers may run indefinitely without
violating invariants, and panic paths and panic recovery must remain sound.
See [property kinds and outcomes](open-questions/property-kinds-and-outcomes.md).

## Not a build matrix

A library author may eventually request verification across a matrix of
targets, features, panic strategies, or dependency versions. That request is a
set of compilation-subject claims, not one magically polymorphic claim.
Tooling may group and deduplicate them, but reporting must identify which cells
were actually checked and which were skipped or assumed.

Similarly, verifying one monomorphization or one reachable subgraph does not
establish a theorem about omitted code. Coverage boundaries belong in the
result and audit ledger. In particular, a whole-artifact result over concrete
call sites is not automatically a reusable contextual-refinement theorem for
every downstream client. See [the claim layers](verification-model.md#layers-of-a-claim).

## Required result information

The result must expose the information required by
[ANNEAL-REQ-021](settled-requirements.md#anneal-req-021-results-carry-an-audit-ledger)
and the [trust model](trust-model.md): the exact compilation subject, selected
properties and dependencies, proof and coverage status, trusted leaves and
assumptions, relevant toolchain identity, and host/target execution
assumptions.

## Candidate representation details

How the required categories are represented is open. Candidate details
include:

- recording both a source revision and dirty-tree or content-digest state;
- storing a normalized Cargo invocation and resolved dependency graph;
- content-addressing generated source, LLBC, and generated Lean;
- assigning stable identifiers to checked proofs and obligations;
- recording timestamps, signatures, provenance, or reproducibility evidence;
  and
- choosing which values are embedded directly versus referenced from another
  manifest.

None of those representation choices is ratified by this page. The
serialization format, command modes, exit-status policy, and distinction
between “verified” and “conditionally checked” remain open in
[trust and incremental adoption](open-questions/trust-and-incremental-adoption.md).
