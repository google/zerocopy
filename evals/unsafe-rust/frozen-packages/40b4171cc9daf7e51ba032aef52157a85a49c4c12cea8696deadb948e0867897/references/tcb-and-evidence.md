# Trusted Computing Base and Evidence

## Contents

- [Maintain an explicit trust boundary](#maintain-an-explicit-trust-boundary)
- [Classify TCB entries](#classify-tcb-entries)
- [Record dependency contracts](#record-dependency-contracts)
- [Record external and deployment assumptions](#record-external-and-deployment-assumptions)
- [Handle probabilistic claims](#handle-probabilistic-claims)
- [Judge tools by their theorem](#judge-tools-by-their-theorem)
- [Audit a tool-derived proof](#audit-a-tool-derived-proof)
- [Review and evolve the TCB](#review-and-evolve-the-tcb)

## Maintain an Explicit Trust Boundary

A TCB audit log lists every proposition the audit accepts as authoritative or
correct without proving it from more primitive in-scope premises. Its purpose is
not to make assumptions respectable; it makes the exact conditional theorem
visible and reviewable.

For every entry, record:

- stable identifier and category;
- exact proposition admitted;
- exact source, artifact, implementation, version, revision, or digest;
- contract text or other evidence;
- scope, configurations, and consumers;
- why admission is permitted;
- validation or audit already performed;
- compatibility/update channel;
- owner and review trigger;
- status and unresolved limitations.

Do not use entries such as “the platform works,” “dependencies are correct,”
“normal allocator,” “valid environment,” or “the compiler is sound.” Split them
into the smallest propositions actually consumed by proofs.

Minimize the TCB where practical, but never hide an assumption to make the list
look small. Every unproved premise must become either another proof obligation
or an explicit entry.

Do not make the theorem vacuous by adding an entry that merely assumes the
in-scope conclusion or trusts the implementation that the declared audit scope
purports to prove. Either prove that code, or narrow the theorem and expose the
code as a precisely identified excluded dependency/TCB component.

When a proof applies an older documented Rust guarantee to a later version via
Rust's backwards-compatibility commitment, record the exact compatibility
proposition as a TCB entry unless it is itself entailed by applicable Reference
or standard-library text. Neither an API stability badge nor a general
expectation of stability silently expands the older guarantee's semantic or
configuration domain.

The default source-level theorem is relative to the documented Rust abstract
semantics. It does not require trusting one compiler backend to emit a correct
binary. A binary-level theorem additionally requires a compiler/toolchain,
target, linker, loader, platform, and external-runtime story appropriate to the
claim.

## Classify TCB Entries

Use categories that expose why a proposition is admitted. Suitable categories
include:

- **AXIOM:** Exact versioned Rust Reference or standard-library proposition.
- **SAFE-DEP:** Documented behavior of a deliberately selected safe dependency
  API.
- **UNSAFE-DEP:** Correctness of a specific unsafe dependency implementation and
  contract not recursively proved by this audit.
- **EXTERNAL-SPEC:** ABI, ISA, OS, hardware, foreign-language, allocator, linker,
  or other non-Rust contract.
- **IMPLEMENTATION:** Exact compiler, standard-library build, foreign library,
  runtime, generator, proc macro, build tool, or other implementation assumed
  correct for a non-source-level claim.
- **TOOL:** Residual trusted components or model correspondence supporting a
  tool-derived proof.
- **ENVIRONMENT/DEPLOYMENT:** Restriction on entry inputs, load environment,
  symbols, CPU, privileges, resources, or other execution context.
- **CRYPTO/PROBABILISTIC:** Explicit computational or probabilistic premise for
  a separately labeled conditional claim.
- **OUT-OF-BAND:** A bilateral or project-specific promise beyond the published
  default contract.

Projects may use different names. Preserve the semantic distinctions.

A proof result produced by a tool is not automatically a TCB assumption. It can
derive a fact when its theorem and premises are verified. Record only the
remaining unproved tool correctness, translation, model, solver, certificate
checker, harness, or environmental premises as TCB entries.

Only a consumed entry explicitly accepted by the authorized human reviewer may
support `PROVED`. A pending entry makes every consuming claim `UNPROVED`. A
rejected or superseded entry may not be consumed; replace it with a proof or an
accepted entry, or narrow the claim and expose the exclusion.

## Record Dependency Contracts

For every dependency proposition, identify whether code is deliberately
selected or caller-controlled.

The project may trust a deliberately selected safe dependency API to behave as
documented. Record:

- package/source identity and exact resolved version;
- safe API and exact behavior consumed;
- documentation version;
- enabled features and relevant target/configuration scope;
- contract channel: SemVer range, exact pin, in-tree fork, out-of-band
  agreement, consumer-specific promise, or another explicit arrangement;
- compatibility and re-audit trigger.

An exact pin freezes identity; it does not establish an undocumented semantic
fact. Prove such a fact by auditing the pinned implementation, obtain an
applicable additional contract, or admit the exact implementation proposition
explicitly.

Do not apply this exception to behavior supplied by a caller merely because it
uses a dependency-defined type or trait. Values, callbacks, closures, plugins,
generic parameters, trait objects, and safe trait implementations selected by
the caller remain adversarial safe code.

For a third-party unsafe API:

1. Obtain its exact caller safety contract and prove the local call satisfies
   it.
2. Separately establish that the dependency implementation upholds its promise
   for every valid call.
3. Discharge step 2 by recursively auditing the implementation or recording a
   precise `UNSAFE-DEP` assumption.

Do not silently include unsafe dependencies in the safe-dependency exception.

When depending on a fork or out-of-band agreement, record the actual authority
for the additional promise, parties, exact covered uses, duration, notification
mechanism, and update process. Do not generalize a consumer-specific guarantee
to other uses.

## Record External and Deployment Assumptions

External specifications are not Rust axioms. Admit only the exact propositions
needed, with version and scope, for example:

- a foreign function has a stated ABI and obeys stated ownership/lifetime rules;
- a CPU instruction has stated effects when a named feature and privilege level
  are present;
- a linker binds a symbol to a specific definition with a specific layout;
- a custom allocator satisfies a named contract;
- a loader, OS, embedded runtime, kernel, or device maintains specified memory
  or concurrency behavior;
- a binary entrypoint receives inputs restricted by a deployment boundary.

Distinguish three claims:

1. **Safe library soundness:** every well-typed safe use is sound; deployment
   restrictions cannot be hidden premises.
2. **Unsafe API soundness:** every use satisfying documented safety obligations
   is sound; external conditions may be explicit obligations.
3. **Binary/application soundness:** executions satisfying stated entry and
   deployment assumptions are sound.

A cryptographic signature check, authenticated input channel, kernel policy, or
restricted device state may narrow a binary theorem. It may not make an
otherwise safe library API conditionally sound without exposing an unsafe
boundary or enforcing the restriction in safe code.

If a compilation or linker flag still emits an artifact, record it as part of
the configuration or toolchain scope. Do not call the flag itself undefined
behavior unless an authoritative contract uses that classification. Identify
the exact execution contract that the resulting artifact satisfies or violates.

## Handle Probabilistic Claims

Rust soundness is universal over valid uses and permitted executions. A
non-zero, negligible, computationally infeasible, or empirically unobserved
chance of undefined behavior is not unconditional soundness.

A user may explicitly admit a cryptographic or probabilistic premise in the TCB,
such as collision resistance or unforgeability. Then:

- state the exact security experiment or probability bound;
- identify the primitive, parameters, implementation, threat model, and time
  horizon;
- state how the premise restricts executions or inputs;
- label the result as a conditional computational/application theorem;
- keep the ordinary unconditional Rust soundness verdict separate.

Do not write `PROVED` without qualification when the result depends on such an
entry. Use wording such as `PROVED relative to CRYPTO-...` and explain that this
is not unconditional Rust soundness.

## Judge Tools by Their Theorem

Classify evidence by what the exact result proves:

- A concrete failing execution can refute a universal claim when the execution
  is in scope and valid.
- A clean sampled test, fuzzing run, sanitizer run, interpreter execution, or
  stress run usually establishes only that the explored executions did not
  trigger the modeled failure.
- An alarm-free sound over-approximation can prove absence of its modeled bad
  states over its stated domain.
- Exhaustive model checking can prove a property over the exhaustively covered
  state space.
- Bounded model checking proves only the bounded proposition unless a
  completeness bound is established.
- Deductive or interactive verification can prove the encoded theorem relative
  to its logic, axioms, models, specifications, and trusted components.
- Successful compilation establishes only the exact properties the applicable
  compiler contract and checks are relied upon to enforce.

These are examples, not rules attached permanently to tool categories. One tool
can provide different guarantees in different modes or results. Read its exact
documentation and output.

Apply this rule:

> A tool result discharges an obligation only if the documented guarantee of
> that exact result, together with all explicit premises and trusted components,
> logically implies the obligation for the exact audited artifact and supported
> configuration set.

Never infer more than the theorem. A tool model is not an additional Rust
authority; prove its correspondence to exact applicable Reference and
standard-library contracts or admit the missing correspondence explicitly.

## Audit a Tool-Derived Proof

Before accepting a tool result, verify:

1. **Proposition:** State the exact property proved and why it entails the Rust
   soundness obligation or documented postcondition.
2. **Artifact identity:** Record exact source, expansion/generated output, IR,
   harness, specifications, compiler, target, tool, solver/backend, versions,
   options, and configuration.
3. **Quantification:** Check coverage of inputs, states, executions, call
   contexts, nondeterminism, thread interleavings, and supported configurations.
4. **Bounds:** Identify loop, recursion, allocation, object-count, integer,
   search-depth, thread, time, and other bounds. Establish completeness or limit
   the conclusion.
5. **Non-vacuity:** Check that the property, assertion, or unsafe operation is
   reachable under permitted inputs and that assumptions do not make the
   harness inconsistent or empty.
6. **Semantic fidelity:** Check validity, layout, provenance, aliasing,
   initialization, concurrency, panic/unwind, FFI, assembly, allocation, target,
   and environment modeling whenever relevant.
7. **Trust and stubs:** List trusted functions, contracts, abstractions,
   dependency models, unsupported features, suppressions, skipped checks, and
   manual lemmas.
8. **Terminal result:** Require the documented successful proof result. Timeout,
   unknown, incomplete, unsupported, disabled checks, or ignored alarms do not
   prove the target.
9. **TCB:** Identify verifier/analyzer correctness, source-to-model translation,
   semantic models, solver/backend, proof checker, and specification adequacy
   that remain trusted.

An independently checked certificate may remove the producer or solver from the
TCB, depending on its guarantee. It does not by itself prove that the encoded
specification matches the needed Rust theorem or that source-to-model
translation is faithful.

Suppressing a sound analyzer alarm creates a new proof obligation. A false
positive does not invalidate the analyzer's soundness guarantee; an unjustified
suppression invalidates the claimed conclusion.

Tests and dynamic tools remain valuable for finding counterexamples, exercising
configuration paths, and checking that proof assumptions match reality. Report
their actual contribution without treating a clean run as a universal proof.

## Review and Evolve the TCB

Reuse the project's canonical TCB log when present. For every audit:

- open and verify every consumed entry;
- remove unused, expired, superseded, or duplicate entries;
- add newly discovered assumptions before relying on them;
- map entries to proof consumers;
- check versions, feature/configuration scope, and contract channels;
- distinguish reviewed facts from proposed or unresolved assumptions;
- identify entries the human reviewer may reject.

Trigger re-audit when:

- a consumed authoritative document changes materially;
- supported Rust, target, feature, allocator, tool, or environment scope changes;
- a dependency resolves to a new version or changes contract channel;
- a fork or out-of-band agreement changes;
- generated output or its inputs/generator change;
- a tool, model, harness, bound, suppression, or proof specification changes;
- a TCB proposition is weakened, invalidated, or replaced;
- new code consumes an existing entry in a stronger way.

Record the TCB revision or digest in every audit verdict. A `PROVED` result is
always relative to that stated trust boundary even when it contains only
authoritative Rust axioms and deliberately permitted safe-dependency trust.
