# Configuration Closure and Generated Unsafe Code

## Contents

- [Define the supported set](#define-the-supported-set)
- [Discover configuration axes](#discover-configuration-axes)
- [Prove every supported combination](#prove-every-supported-combination)
- [Audit generated and expanded code](#audit-generated-and-expanded-code)
- [Audit targets, SIMD, and concurrency](#audit-targets-simd-and-concurrency)
- [Audit allocators, panic modes, and assertions](#audit-allocators-panic-modes-and-assertions)
- [Audit FFI, assembly, linking, and global symbols](#audit-ffi-assembly-linking-and-global-symbols)
- [Record configuration coverage](#record-configuration-coverage)

## Define the Supported Set

Write a precise predicate `Supported(configuration)` before claiming full
soundness. Derive it from published package metadata, documentation, target
policy, feature declarations, build tooling, compiler support, downstream
integration agreements, and the artifacts that can actually be shipped.

Include every compilation option combination that downstream users are allowed
to produce, not merely CI jobs or maintainer-preferred builds. If a compilable
combination is exposed without a clear exclusion, conservatively treat it as
supported until the project owner establishes otherwise.

Record:

- source revision and workspace/package selection;
- Rust toolchain range, edition, standard-library identity, and relevant compiler
  flags;
- target triples, target specifications, CPUs, features, ABIs, data layouts, and
  linkers;
- Cargo features, dependency feature unification, optional dependencies, and
  resolver behavior;
- profiles and code-affecting environment or build inputs;
- generated artifacts and their generators;
- explicit exclusions and how compilation or distribution enforces them.

An exclusion written only in an audit report does not constrain downstream
users. If soundness requires rejecting a combination, enforce and document the
rejection in the build or API.

## Discover Configuration Axes

Search both handwritten and generated source for all code-selection and
semantic axes. At minimum, investigate when applicable:

- `cfg` and `cfg_attr`, Cargo features, optional dependencies, and feature
  unification;
- target architecture, OS, environment, vendor, family, ABI, endianness, pointer
  width, alignment, atomic widths, and target capabilities;
- conditional type definitions, representation/layout attributes, constants,
  const evaluation, static initialization, and build-time execution;
- compile-time and runtime SIMD or other target features;
- debug assertions, overflow checks, optimization, LTO, codegen backend, panic
  strategy, unwinding, sanitizers, and instrumentation;
- global and per-operation allocator choices, allocation failure behavior, and
  custom allocator implementations;
- thread availability, atomics, permitted interleavings, weak memory behavior,
  signals, cancellation, and runtime/executor choices;
- build scripts, procedural and declarative macros, derives, code generators,
  bindgen output, included files, environment variables, and external tools;
- FFI implementation, ABI, library version, symbol resolution, static/dynamic
  linking, linker scripts, link arguments, dynamic loading or plugins, and
  load-time substitution;
- inline assembly dialect, registers, options, calling convention, instruction
  availability, and surrounding compiler assumptions;
- compiler version, edition, unstable features, bootstrap flags, custom target
  specifications, and standard-library build;
- tests/examples/binaries versus library code, `no_std`, host versus target
  builds, and build-dependency versus runtime-dependency configurations.

This list is intentionally advisory and may be incomplete or become outdated.
Discover the actual axes from the audited project and authoritative toolchain
contracts. Add newly discovered axes to the audit and report gaps in this
reference.

## Prove Every Supported Combination

Every supported combination must be sound. A CI matrix, sample of targets, or
pairwise feature test does not establish this universal claim.

Avoid Cartesian-product enumeration when an abstract proof is clearer. Valid
coverage arguments include:

- prove one implementation is parametric over an axis;
- partition configurations into equivalence classes and prove the partition is
  exhaustive and each class representative shares the relevant semantics;
- prove mutually exclusive `cfg` predicates form a total partition over the
  supported set;
- prove a generator emits only members of a finite audited family;
- prove independent lemmas for axes, then prove their assumptions remain
  independent under composition;
- prove unsupported combinations fail before producing a shippable artifact.

For every abstraction, check interactions between axes. A proof of each feature
alone does not prove their combination; target facts can change layout, atomic
availability, calling convention, or macro expansion on which another feature
depends.

Attach a configuration-domain predicate to every obligation, premise, and
coverage lemma. A premise proved for one target, toolchain, feature set, or
generated artifact cannot discharge another case merely because the source
looks similar. If separate lemmas cover separate regions, prove that their
union contains the entire supported set and that their assumptions remain true
where regions interact.

Do not infer semantic coverage from successful compilation. Compilation may
establish syntax, typing, and selected compiler-enforced conditions; unsafe
contracts remain separate obligations.

## Audit Generated and Expanded Code

Treat generated code as shipped source. Capture enough information to reproduce
or identify:

- generator/proc-macro/build-script package and exact version or digest;
- host toolchain and host configuration;
- target configuration and all relevant environment inputs;
- input tokens/files/schema and invocation options;
- output source, expansion, metadata, or object identity;
- diagnostics, suppressed checks, and unsupported paths.

Do not stop at the generator's handwritten source. Soundness can depend on the
mapping from every accepted input and configuration to output, hygiene and name
resolution in the destination crate, compiler expansion behavior, or external
tool output.

Use one of these proof strategies:

1. Inspect each member of a proven finite output set.
2. Prove a property of the generator that entails safety for every supported
   output.
3. Record the exact generated artifact in the audited snapshot and enforce that
   exact output identity or digest. Pinning only the generator does not fix its
   inputs, environment, compiler interaction, or output.

For macro-generated APIs, audit the expanded visibility and caller obligations.
A safe-looking invocation is not automatically a safe API if rustc enforces an
unsafe-context obligation in the expansion; conversely, generated internal
unsafe code behind an invocation usable from safe context must be sound for
every accepted safe invocation.

Build scripts may emit `cfg` values, link directives, environment values, or
generated source. Include both their output and every supported path that can
produce different output. Include proc-macro and build dependencies in the TCB
or recursive audit as appropriate.

## Audit Targets, SIMD, and Concurrency

For target-dependent code:

- derive layout, validity, alignment, ABI, instruction, atomic, and pointer-width
  facts from exact applicable authoritative contracts or TCB entries;
- distinguish compile-time target features from runtime CPU availability;
- prove every call edge satisfies target-feature and calling-convention
  requirements;
- prove runtime feature detection dominates every specialized instruction path
  and cannot be invalidated between detection and use;
- audit fallback paths and combinations of enabled features;
- include cross-language or dynamic-dispatch edges that may bypass a Rust
  wrapper.

For concurrency:

- quantify over every permitted interleaving and memory-model behavior within
  scope;
- prove synchronization, atomic ordering, initialization publication, lifetime,
  ownership, and destruction properties from applicable contracts;
- treat caller-provided safe callbacks and safe trait implementations as
  adversarial, including reentrancy, blocking, panic, and unexpected timing;
- distinguish thread-safety properties promised by types and unsafe trait impls
  from behavior merely observed on one runtime.

Do not use one scheduler run, stress test, or architecture as proof of all
executions.

## Audit Allocators, Panic Modes, and Assertions

For allocation-sensitive unsafe code, identify the allocator contract actually
required:

- size and alignment accepted;
- allocation, reallocation, and deallocation pairing;
- zero-size behavior;
- maximum sizes and arithmetic bounds;
- allocation failure, overcommit, and address reuse;
- thread safety and reentrancy;
- allocator identity across FFI, dynamic-library, and configuration boundaries.

A library generic over a valid allocator implementation must be sound for every
implementation satisfying the applicable unsafe allocator contract. A binary
that selects a particular allocator may record that exact implementation as a
TCB dependency when appropriate.

Prove invariant restoration and resource behavior under every supported panic
strategy. Distinguish:

- normal return;
- error return;
- panic with unwind;
- panic with abort;
- foreign exceptions or unwinding across boundaries;
- cancellation or destruction suppression where supported.

Never rely on `debug_assert!` to establish a release-build safety precondition.
If a check is part of the proof, ensure it executes in every supported
configuration or prove the proposition independently. Treat differences in
overflow checks, debug assertions, and optimization as configuration branches
until shown irrelevant.

## Audit FFI, Assembly, Linking, and Global Symbols

For FFI, prove or explicitly trust:

- exact function and data ABI, types, layout, calling convention, and symbol
  identity on both sides;
- validity and ownership of arguments and return values;
- lifetime, aliasing, allocation, deallocation, callback, thread, and unwinding
  rules;
- versioning and configuration of the foreign implementation;
- behavior of foreign code that Rust unsafe code relies upon.

Declaring an extern item asserts that the declaration matches reality; calling
it consumes both the declaration contract and call-specific preconditions. Keep
those obligations distinct.

For inline assembly, derive Rust-side requirements from exact applicable
Reference or standard-library text. Record ISA manuals, target specifications,
ABI documents, linker manuals, and other non-Rust sources as versioned
`EXTERNAL-SPEC` TCB entries unless the exact consumed proposition appears in
Reference or standard-library text. Audit operands, register classes, clobbers,
flags, stack, control flow, memory effects, options, instruction availability,
privilege/environment, and interaction with compiler optimization. This is a
discovery list, not an authoritative specification.

Audit whole-program/link obligations when relevant, including:

- uniqueness and type/ABI agreement of exported or unmangled symbols;
- global allocator and panic-runtime selection;
- link-section placement, alignment, initialization order, and linker-script
  assumptions;
- dynamic symbol interposition and library substitution;
- consistency of declarations across crates and languages;
- linker flags or custom target settings that alter assumptions used by source
  proofs.

A compilation or linker option that still emits a binary belongs to the
supported configuration set if users may ship it. Do not label a flag itself
“Rust undefined behavior” without authoritative text. Instead, trace any
resulting execution to the exact violated Rust or external contract, or state
that the artifact lies outside the proved source-level claim.

## Record Configuration Coverage

For each audit, report:

- the formal or operational definition of the supported set;
- every discovered axis and its possible supported values/classes;
- the proof method establishing coverage;
- the obligation and premise applicability domains used by that proof;
- generated artifact identities or generator theorem;
- excluded combinations and their enforcement;
- untested but abstractly proved combinations;
- tested combinations and the limited propositions those tests establish;
- remaining assumptions, unknowns, and unsupported tool features;
- triggers requiring re-audit.

Mark the audit `UNPROVED` if a shippable supported combination is neither
individually audited nor covered by a valid universal argument.
