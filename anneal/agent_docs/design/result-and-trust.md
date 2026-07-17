<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Result and trust

This document defines what identifies an Anneal result, which dimensions its
claim must state, how checked evidence differs from residual dependencies, and
what users must be able to audit. The
[verification model](verification-model.md) explains how local obligations
compose to produce the result.

Anneal does not eliminate trust by translating Rust into Lean. It must instead
report exactly which claim its evidence supports and expose every dependency
needed to connect that evidence to the claim. The exact serialization, command
profiles, and exit-status policy remain open; see
[trust and incremental adoption](open-questions/trust-and-incremental-adoption.md).

## What trust means

A dependency is trusted for a reported claim when that claim relies on the
dependency's correctness but the result's included checked evidence does not
establish it at the claimed semantic endpoint. Trust is therefore relative to
a particular result and claim, not an intrinsic label on a component. A
compiler may be irrelevant to a theorem stated only about a Lean model but
essential to a claim about the binary it produces.

Different trusted dependencies play different roles. A semantic assumption
says what an operation or environment means. Tool trust says that a component
handled its inputs and semantics correctly. Integration or correspondence
trust says that the components, identities, and artifacts are connected to the
same compilation subject correctly. Execution-substrate trust connects a Rust
or binary claim to the platform and hardware on which it runs.

An incomplete proof and an unchecked admission have distinct statuses, but
neither includes checked evidence for the required argument. An incomplete
proof records unresolved proof work; an unchecked admission is an escape hatch.
Neither becomes an intentional semantic boundary merely because Lean can
represent both using axiom-like declarations. Likewise, a coverage gap or tool
failure may narrow or block a claim instead of becoming an assumption the claim
is permitted to rely on. **Residual dependency** is therefore broader than
**trusted dependency**.

## Compilation-subject and result identity

Anneal's initial subject is one concrete Cargo compilation artifact. Here,
“compilation artifact” means the compiler-resolved Rust program and semantic
configuration selected for verification, not the native executable, library
archive, or other file emitted by Cargo. “Compilation subject” is the preferred
phrase when that distinction matters.

The compilation subject changes whenever an input can change the Rust program
presented to Charon or its source-level semantics. Rust emitted by procedural
macros or build machinery and then ingested by Charon is part of that subject.
It is analyzed like checked-in Rust rather than trusted merely because a
generator produced it. This does not make execution of the generator itself
part of the proved Rust program, nor does it verify every output that the
generator could produce.

A verification result has a separate identity. It combines the compilation
subject with a precise claim, checked evidence, residual dependencies, and the
models and tools that produced or checked them. Changing a proof, property
selection, translator, semantics, or trusted specification can therefore
produce a different result about the same compilation subject.

Classify an input by what it can change:

- an input that changes the compiler-resolved Rust program or its source
  semantics participates in compilation-subject identity;
- an input that changes extraction, modeling, obligations, evidence, selected
  claim, or assumptions participates in verification-result identity; and
- an input that changes only the relationship between the Rust subject and a
  binary execution qualifies that execution claim.

One component may have several roles. A rustc revision, for example, can
change the compilation subject and also remain part of the end-to-end TCB.
Classify the actual dependency rather than permanently assigning each tool to
one bucket.

Verification across targets, features, panic strategies, dependency versions,
or other build-matrix cells initially produces multiple subject-specific
results. Tooling may group and deduplicate them, but must identify which cells
were checked, omitted, or assumed. A prior result must not be silently
generalized to a related subject.

## Claim dimensions

“Verified” is incomplete unless the result states independent dimensions of
the claim:

### Property and guarantee

The result identifies each asserted property, the guarantee established for
it, and every dependency on another property or assumption. Rust soundness is
foundational; selecting another property does not silently remove the
soundness basis needed to interpret the model as Rust.

### Behavior

The result identifies which source behaviors the guarantee covers. Normal
return, panic and unwind, abort, and divergence can support different
obligations. A soundness result does not imply panic freedom or termination
unless those guarantees are also stated and proved.

### Client and coverage envelope

The result identifies the items, paths, call sites, generic instances, and
clients covered. Proving all concrete uses in one compilation subject is
different from proving contextual refinement for every type-correct safe use
admitted by an API within a stated envelope. Omitted or unsupported coverage
may not be inferred to have been checked.

### Semantic endpoint

The result identifies the semantic object about which it makes a claim. A
Lean-kernel theorem concerns declarations in a Lean environment. A claim about
the Rust compilation subject additionally depends on adequate extraction,
translation, obligation generation, and Rust semantics. A claim about a
compiled binary executing on target hardware additionally depends on the
compiler, linker, ABI, platform, and hardware connection.

These endpoints and the other dimensions are not one linear hierarchy. A
result can strengthen its client quantification without extending to target
hardware, or add panic freedom without changing its semantic endpoint. Every
reported result must state the actual combination rather than present one
ambiguous assurance grade.

### Conditions

The claim is relative to every explicit semantic, environmental, and trusted
dependency that remains after proof checking. A condition can make a result
useful without making it unconditional. Its type and consequences must remain
visible.

## Evidence and residual dependencies

Every evidence-graph leaf, proof obligation, and coverage boundary needs enough
classification for users and tools to distinguish its evidence, its role in
the claim, and its coverage or modeling disposition. These dimensions are
independent even if the eventual report schema represents them differently.

### Evidence classification

The following distinctions must remain observable. They need not become
mutually exclusive values in one status enum: the eventual schema may use
statuses, subtypes, provenance fields, or several of these.

- **Checked evidence:** Lean or another accepted checker established the
  obligation relative to that checker's environment and assumptions.
- **Approved assumption:** an explicit premise is permitted to condition the
  reported claim without evidence establishing it in this result. Its role,
  origin, owner, and effect on the claim must be recorded. A specialized form,
  such as a prose justification, retains that more specific provenance.
- **Incomplete proof:** a formal obligation is intentionally recorded as work
  whose checked evidence has not yet been completed.
- **Unchecked admission or escape hatch:** an admitted theorem, unclassified
  axiom, or equivalent bypass supplies no ordinary checked evidence. It must be
  detected and reported separately from intentional incompleteness and approved
  semantic boundaries.
- **Prose justification:** a human safety argument is relied upon for
  incremental adoption in place of a machine-checked proof. Whether the schema
  represents it as a specialized admission, a distinct status, or another form
  remains open, but the result must preserve the distinction.
- **Tool or model failure:** verification could not establish the requested
  result. This is not a source-program outcome and supplies no evidence that
  the source property holds or fails.

### Coverage and modeling disposition

- **Body or path selected for analysis:** the named implementation body or path
  participates in the evidence graph. Its operations still require supported
  semantics and adequate obligations.
- **Specification-only or opaque body:** clients use a specification without
  analyzing the implementation body at this endpoint. This can be a legitimate
  trusted semantic leaf rather than a coverage gap; the specification still
  needs its own evidence classification and role in the claim.
- **Outside the selected adoption or coverage scope:** a named item, path, or
  generated input is deliberately excluded from the claimed envelope.
- **In scope but uncovered or unreconciled:** an item, path, call, or operation
  belongs to the claimed envelope but is absent from or not connected to the
  evidence graph despite having supported semantics. This is a coverage
  adequacy failure, not an intentional scope boundary.
- **Semantics represented:** the checked model assigns semantics and generates
  obligations for the operations relevant to the claim. Whether that
  representation and those obligations are adequate is classified separately
  as a claim-relevant dependency.
- **Unsupported or unmodeled:** a relevant construct or semantics is not
  represented by the checked model. The result must identify the claim this
  prevents, narrows, or conditions.

Coverage and modeling are themselves distinct: selecting a body does not prove
that every operation in it is modeled. A result may therefore need more than
one of these classifications.

### Role in the claim

- **Program-proof obligation:** the result must establish a primitive guard,
  callee precondition, invariant, contract guarantee, or property-dependency
  edge for the analyzed program. Incompleteness, prose, or an admission changes
  its evidence treatment, not this role.
- **Program-semantic dependency:** the result relies on the specified meaning
  of a primitive Rust or standard-library operation, FFI, assembly, an ISA, a
  platform interface, or another part of the modeled program. Its origin and
  owner must be recorded. Anneal is responsible for the adequacy of
  specifications it provides and for exposing the adequacy dependency of any
  specification it imports.
- **User-property dependency:** a user-authored proposition is used without
  proof. Merely defining the intended meaning of a user property is part of the
  claim, not a residual dependency; assuming that the program satisfies it is.
  Anneal cannot infer whether the definition captures the user's intent.
- **Correspondence or integration dependency:** the result relies on source
  extraction, translation, obligation coverage, identity reconciliation, or
  composition connecting the same compilation subject correctly across stages.
- **Tool-implementation dependency:** the result relies on Anneal, Charon,
  Aeneas, Lean, rustc, LLVM, a linker, or another tool behaving correctly.
- **Execution-substrate dependency:** the result relies on an ABI, allocator,
  operating system, firmware, external service, foreign library, hardware
  behavior, or another condition not established by the program proof.

The final names and machine representation are open. Their semantic
distinctions are not. In particular, an approved semantic assumption, an
unfinished proof, an unchecked admission, a prose argument, an opaque body, a
coverage gap, and a tool failure support different conclusions. One item can
carry classifications in several dimensions, and its role alone does not
determine whether it allows, conditions, narrows, or blocks a result.

An undischarged obligation means that Anneal has not established the requested
claim. It is a useful diagnostic about missing evidence, not by itself a proof
that the Rust source violates the property.

## Two trust boundaries

Evidence classification and role do not replace the need to distinguish the
scope of a trust boundary. Anneal must distinguish:

- the **trusted semantic leaf boundary**: program operations whose behavior or
  soundness requirements are specified axiomatically instead of proved from a
  deeper model; and
- the **end-to-end TCB**: every implementation and assumption needed to connect
  checked evidence to the claimed Rust or target execution.

The initial semantic leaf boundary may include raw-pointer operations, unsafe
standard-library functions, intrinsics, assembly, FFI, and platform operations
whose behavior is exposed through axiomatic specifications rather than derived
from a deeper implementation model. Anneal's standard library will likely use
the same axiom facility to specify some of these leaves. Anneal's authors are
responsible for the adequacy of Anneal-provided soundness specifications.

The end-to-end TCB is much broader. Depending on the semantic endpoint, it can
include Anneal's obligation generation, Charon's extraction, Aeneas's
translation and semantics, Lean's kernel and proof environment, rustc, LLVM,
linking, the interpretation of Rust and target specifications, operating
systems or firmware, foreign libraries, and host and target hardware.

A small program-semantic leaf boundary does not make this broader TCB small.
The audit ledger must make clear which boundary a change actually shrinks.

## Audit ledger

Every result must expose enough information to reproduce its subject, interpret
its claim, inspect its evidence, and audit its residual dependencies. At
minimum, the ledger records:

### Claim and scope

- the property guarantees asserted and their dependencies;
- covered behaviors and exceptional outcomes;
- the client, item, path, call-site, generic-instance, and other coverage
  boundaries; and
- the semantic endpoint and every condition needed to reach it.

### Evidence and gaps

- each obligation and dependency, with its evidence classification, role, and
  any applicable coverage or modeling disposition;
- every trusted semantic leaf and axiom, including origin, owner, and affected
  properties;
- every incomplete or admitted proof and every prose justification, with a
  source location where applicable;
- every specification-only or opaque body, with the corresponding
  specification and evidence classification;
- every skipped, unsupported, or unmodeled item or operation;
- coverage gaps and the claims they prevent or condition; and
- dependencies among proofs, properties, specifications, and assumptions.

### Compilation subject

- workspace, package, Cargo target, target kind, profile, source revision or
  other source identity;
- dependency resolution and enabled features;
- target triple or specification, `cfg` values, panic strategy, overflow
  behavior, and other source-semantics-relevant compiler options;
- generated Rust, proc-macro expansion, build outputs, and included files that
  form the compiler-resolved subject; and
- relevant environment variables, build-script directives, ABI, and other
  inputs or assumptions affecting that subject.

### Verification evidence and toolchain

- Anneal, Aeneas, and Charon versions or revisions, options, models,
  obligations, and downstream semantic patches;
- rustc, the Rust standard library, LLVM, linking tools, and relevant compiler
  options;
- the LLBC, Lean declarations, checked proof artifacts, Lean, Lake, Mathlib,
  and other proof-library versions needed to identify or reproduce the
  evidence; and
- proof, extraction, translation, and reporting configuration not already
  captured by the compilation subject.

### Execution substrate

- operating-system, firmware, external-service, foreign-library, and platform
  assumptions relevant to the claim;
- the host hardware or trusted execution environment on which verification ran
  to the degree needed to reproduce or assess the result; and
- the target hardware model or concrete implementation assumed by any binary
  execution claim.

If a result stops at a model or Rust-subject claim, the ledger states that
binary and target-hardware execution are outside the claim rather than implying
they were verified. Host hardware running the checker may nevertheless remain
in the practical TCB.

Recording a field does not necessarily make it part of a future canonical
content identifier. Defining normalization, semantic equivalence, provenance,
signatures, storage formats, and the useful granularity of hardware identity
remains open. The ledger may not omit a claim-relevant dependency merely
because its canonical encoding is unsettled.

## Fail-closed reporting

“Fail closed” means Anneal must never silently report a claim stronger than its
evidence supports. It does not predetermine one command name or exit-code
policy.

An approved external axiom may be compatible with a successful result whose
claim is explicitly relative to that axiom. An explicitly named incremental
mode may report a weaker conditional result with incomplete proofs or prose
justifications. Whatever policy is chosen:

- every successful exit has a documented meaning;
- conditional or incomplete evidence is not labeled as an unconditional
  verification result;
- omitted coverage remains visible and qualifies the claim;
- property dependencies cannot be disabled without being discharged or
  reported as conditions;
- model and tool failures are not treated as source behaviors; and
- users can compare results and ledgers as evidence or trust changes.

The distinction between a strictly verified mode and conditionally checked
profiles remains open. Anneal must settle that user-facing policy explicitly
rather than allowing implementation accidents to define it.

## Reducing trust over time

Stable abstraction contracts should be separable from the current depth of
their implementation model. This permits, for example:

- a primitive-operation axiom to be replaced by a proved Rust operational
  model;
- an assembly axiom to be replaced by an ISA-level proof;
- an FFI specification to be connected to a verified foreign implementation;
- a compiler assumption to be replaced by translation validation or verified
  compilation; or
- a hardware assumption to be connected to a formal hardware model.

The replacement reduces trust only if it supports the same or a stronger
end-to-end claim and removes the old dependency from the ledger. Moving an
assumption into generated code, a helper whose body is not modeled, or another
project without proving it does not shrink the TCB.
