# Configuration Closure and Generated Unsafe Code

## Contents

- [Recover the required supported set](#recover-the-required-supported-set)
- [Discover configuration axes](#discover-configuration-axes)
- [Prove coverage of the recovered set](#prove-coverage-of-the-recovered-set)
- [Prove build and generation pipelines](#prove-build-and-generation-pipelines)
- [Audit targets, SIMD, and concurrency](#audit-targets-simd-and-concurrency)
- [Audit allocators, panic modes, and assertions](#audit-allocators-panic-modes-and-assertions)
- [Audit FFI, assembly, linking, and global symbols](#audit-ffi-assembly-linking-and-global-symbols)
- [Record configuration coverage](#record-configuration-coverage)

## Recover the Required Supported Set

This reference helps recover the configuration projection of the full
`Required(case)` domain defined in `SKILL.md`. Define
`Required_cfg(configuration)` to hold when at least one full required case has
that configuration. This projection organizes support-policy and case proofs;
it does not replace inputs, states, executions, or other dimensions of
claim-level `Required` and `Covered`.

Preserve each controlling support expression as a precise symbolic predicate
before claiming full soundness. Fix the exact source or packaged artifact and
audit cutoff. Let each predicate range over every relevant toolchain component,
host/target fact, and build option rather than reducing it to a `rustc` version
string.

Classify support evidence before using it:

- applicable package metadata, published policy, release documentation,
  feature/target policy, and authorized downstream agreements may define the
  project's support contract;
- manifest checks, build scripts, `compile_error!`, wrappers, packaging rules,
  and distribution controls may admit or enforce configurations; and
- CI jobs, lockfiles, successful builds, `rust-toolchain.toml`, and maintainer
  defaults observe or select particular configurations but do not by themselves
  define or prove downstream support.

Resolve inherited fields in the exact workspace and inspect the effective
packaged metadata when it can differ. Interpret every mechanism through its
applicable contract; do not hard-code a universal precedence among metadata,
documentation, and agreements. A documented exclusion may delimit a support
promise, but if soundness depends on preventing that configuration from
shipping, require effective rejection before claiming closure.

If applicable support declarations conflict or materially underdetermine the
predicate, do not silently select the narrowest interpretation. Apply the
domain-recovery choices in `SKILL.md` to the full case domain: obtain an
authorized project decision, construct an explicit conservative `Required`
domain containing every materially supported candidate domain, or report
regional results and leave the combined claim `UNPROVED`. Then project that
chosen full domain to `Required_cfg`. Do not call a conservative audit domain a
newly inferred project promise. If a shippable configuration is exposed and no
applicable contract clearly excludes it, include its possible shippable full
cases in the unresolved conservative domain until project authority resolves
its status; successful compilation alone still does not define the support
promise.

Every transformation from controlling expressions to the full `Required`
domain and its `Required_cfg` projection is a proof obligation. Record the
transformation and the relation it must establish:

- an exact normalization requires equality in both directions;
- a conservative audit domain requires
  `Candidate_i(case) ⊆ Required(case)` for every materially supported candidate
  full-case domain; the projected containment follows but cannot substitute for
  this full-case proof;
- an exclusion requires an applicable support contract and, when soundness
  depends on preventing shipment, effective enforcement; and
- a configuration partition used for proof requires `Required_cfg` to be
  contained in the union of the proved configuration predicates. Cases need
  not be disjoint unless the proof relies on uniqueness.

Do not replace a range or conditional predicate with a finite inventory until
both membership and completeness are established from applicable evidence. A
list of endpoints, sampled toolchains, one apparent representative per minor
series, or successfully observed releases is not an inventory proof. When
exact membership is unavailable or large, retain the symbolic predicate and
prove it parametrically; if neither parametric proof nor justified exhaustive
partition closes, leave the remainder `UNPROVED`.

Preserve conditional and nonlinear structure across every discovered axis
rather than collapsing `Required_cfg` to a single MSRV. It may be finite,
nonlinear, or moving and need not have a globally earliest toolchain. Resolve
dynamic policies at the audit cutoff. A cutoff identifies when a dynamic
predicate was recovered; it neither enumerates the toolchains before that date
nor supplies semantic continuity between sampled versions.

Record:

- source revision and workspace/package selection;
- Rust toolchain range, edition, standard-library identity, and relevant compiler
  flags;
- controlling support-policy sources, conflicts, authorized resolutions, and
  the audit cutoff;
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

## Prove Coverage of the Recovered Set

Every full required case must reach its exact audited artifact, selected source,
or other in-scope build outcome and satisfy the applicable semantic obligations.
A proved enforced exclusion may establish that a candidate combination has no
shippable full case; it does not cover any full case that remains in `Required`.
A CI matrix, sample of targets, or pairwise feature test establishes neither
domain recovery nor universal semantic coverage.

Avoid Cartesian-product enumeration when an abstract proof is clearer. Valid
coverage arguments include:

- prove one implementation is parametric over an axis;
- partition configurations into equivalence classes and prove the partition is
  exhaustive and each class representative shares the relevant semantics;
- prove mutually exclusive `cfg` predicates form a total partition over
  `Required_cfg`;
- prove a generator emits only members of a finite audited family;
- prove independent lemmas for axes, then prove their assumptions remain
  independent under composition;
- prove unsupported combinations fail before producing a shippable artifact.

For every abstraction, check interactions between axes. A proof of each feature
alone does not prove their combination; target facts can change layout, atomic
availability, calling convention, or macro expansion on which another feature
depends.

Use `Required_cfg` only as an index into full-case proofs. Attach a
configuration-domain predicate to every obligation, premise, and coverage
lemma. For each required configuration, prove the relevant build, artifact,
source-selection, and semantic lemmas for every full required case in its
omitted-dimension fiber, parametrically or by an exhaustive partition. A unary
configuration lemma may assert one exact artifact or source only after proving
uniqueness or independence from the omitted dimensions. A premise proved for
one target, toolchain, feature set, or generated artifact cannot discharge
another case merely because the source looks similar. If separate lemmas cover
separate regions, prove that their union contains `Required_cfg`, reattach every
other relevant case dimension, and prove their assumptions remain true where
regions interact. Use the resulting full-case lemmas in claim-level `Covered`;
do not substitute the configuration projection for it.

Before accepting closure, try to exhibit a required boundary, interior,
conditional, or cross-axis full case absent from `Covered`. This is a
falsification check, not a substitute for the containment proof.

Do not infer semantic coverage from successful compilation. Compilation may
establish syntax, typing, and selected compiler-enforced conditions; unsafe
contracts remain separate obligations.

## Prove Build and Generation Pipelines

Model claim-relevant build and generation machinery as a staged relation, not
merely an endpoint mapping:

```text
policy and build inputs
  -> ordered local operations, effects, and exits
  -> emitted directives, metadata, source, or objects
  -> build-tool/compiler interpretation
  -> selected shipped artifact and source
```

Close every arrow with the [evidence-bearing proof
kernel](proof-obligations.md#build-the-evidence-bearing-proof-kernel). Inspection
can establish that a source operation, attribute, directive, or output occurs;
its execution or interpretation is a semantic proposition requiring applicable
Rust/stdlib authority, a verified tool theorem, or an explicit TCB premise.

Include an operation, exit, or effect when it can change the theorem domain, an
applicable or consumed premise, the selected or shipped artifact/source,
semantic reachability, or an in-scope postcondition. Group paths only after
proving them equivalent for every such proposition. Audit additional build
behavior when the requested theorem includes it.

Derive the material stages from the artifact. For each stage, prove:

- the exhaustive input/state partition on which it is reached;
- the order of operations whenever failure, partial progress, caching, or
  invalidation can affect later stages;
- every claim-relevant fallible operation and alternative exit, including
  which later operations are not reached and which earlier effects remain;
- a complete successful-output/effect relation sufficient for every downstream
  proposition: exact value, cardinality, identity, or ordering when consumed or
  asserted, otherwise a proved property covering every possible output;
- the distinction between local source behavior, build-tool or compiler
  behavior, and any admitted environmental behavior; and
- that each output consumed by a later stage was actually established on that
  path and within the premise's applicability.

Classify outcomes according to the controlling contract. A policy rejection,
an infrastructure or tool failure, and successful production of an excluded or
supported artifact can all produce “no library was compiled” or another common
endpoint without being the same proof case. Do not say later selector,
generator, or compiler handling occurred on a path that exited earlier.

Account for freshness when a changing input can reuse prior build state. Prove
the exact invalidation, rerun, cache-key, or identity relation consumed by the
claim rather than assuming the generator is re-executed with current inputs.

When conditional source is selected, evaluate each material predicate from its
proved leaf options through every composite operator to the attribute or other
selection effect. Cite the applicable Rust semantics for those operators and
effects; a TCB entry mapping an external input to a leaf option does not also
supply Rust predicate semantics unless it explicitly says so.

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
generated source. Prove their complete claim-relevant staged relation as above.
Include proc-macro and build dependencies in the TCB or recursive audit as
appropriate.

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

A compilation or linker option belongs to `Required_cfg` only when the
controlling support predicate includes it; the technical ability to emit or
ship a binary does not itself define project support. For an included option
that emits a binary, do not label the flag itself “Rust undefined behavior”
without authoritative text. Trace any resulting execution to the exact
violated Rust or external contract, or state that the artifact lies outside the
proved source-level claim.

## Record Configuration Coverage

For each audit, report:

- every controlling support predicate and its exact source;
- the symbolic `Required_cfg` projection, its relationship to the full
  `Required(case)` domain, the audit cutoff, and any unresolved policy
  ambiguity;
- every asserted set relationship, normalization, enumeration, partition,
  merge, or exclusion used to derive the full `Required` domain and its
  `Required_cfg` projection, with its relation-appropriate certificate;
- every discovered axis and its possible supported values/classes;
- the staged build/generation relation, including ordered effects, alternative
  exits, tool interpretation, and freshness where applicable;
- the proof method for every required configuration fiber and its composition
  into the full-case `Required ⊆ Covered` claim argument;
- the obligation and premise applicability domains used by that proof;
- generated artifact identities or generator theorem;
- excluded combinations and their enforcement;
- untested but abstractly proved combinations;
- tested combinations and the limited propositions those tests establish;
- remaining assumptions, unknowns, and unsupported tool features;
- triggers requiring re-audit.

Mark the configuration-closure obligation and every dependent affirmative claim
`UNPROVED` if `Required_cfg` is not justified, a required configuration fiber
lacks a complete full-case argument, or any required full case remains outside
`Covered`. Apply final verdict certificates separately: a complete independent
existential certificate may still establish `UNSOUND` or `CONTRACT-BROKEN` for
its proved scope.
