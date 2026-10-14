# Prefix safety, outcomes and property transfer

## Summary

A certificate can reflect source safety without assuming complete source safety: cover initial states, match every relevant source prefix step, and reflect a reachable source bad state into a reachable model bad state. A generic Lean specimen checks this implication and heterogeneous composition. It also checks that finite-prefix safety correspondence permits infinite stuttering and therefore establishes no termination or liveness theorem.

The propositions are abstract. Rust source meaning, the first representation's adequacy, outcome classifications and individual pass relations remain independent premises. This separation prevents a theorem about successful translated values from silently becoming a theorem about all source executions.

## Applicability

The original [PrefixCertificate.lean](PrefixCertificate.lean) was checked directly with the existing Lean 4.31.0 binary, revision `68218e876d2a38b1985b8590fff244a83c321783`. No packages were installed or toolchains built. The source and executable hashes are in REPORT.json; [lean-check.json](lean-check.json) records invocation, stdout, empty stderr and exit zero, plus Init.olean and shared-library hashes.

The Aeneas and Rust Reference sources are separately pinned primary subjects. They motivate interface boundaries, but are not instantiated in the specimen. The cce consumer documentation supplies a concrete policy that rejects forbidden execution while allowing explicitly chosen defined outcomes; its source-to-model correspondence remains trusted.

## Findings

### Exact checked finite-prefix interface

Basis: derived original definitions + execution of Lean's kernel checker.

Let Reach(step,a,b) be finite reflexive-transitive reachability. Safe(step,bad,a) means every reachable state avoids bad. A certificate between source S and model M with relation R has these fields:

```text
stepMatch:
  ∀ s m s', R(s,m) ∧ sourceStep(s,s')
       ⇒ ∃ m', Reach(modelStep,m,m') ∧ R(s',m')
badReflect:
  ∀ s m, R(s,m) ∧ sourceBad(s)
       ⇒ ∃ m', Reach(modelStep,m,m') ∧ modelBad(m')
```

The actual Lean fields curry the conjuncts; their propositions are otherwise exactly those displayed. Certificate.mapReach lifts stepMatch to every finite source prefix. Certificate.reflectSafety proves:

```text
Certificate(sourceStep,modelStep,sourceBad,modelBad,R)
∧ R(sourceInitial,modelInitial)
∧ Safe(modelStep,modelBad,modelInitial)
⇒ Safe(sourceStep,sourceBad,sourceInitial).
```

No source-safety premise occurs. The certificate is stronger than a relation restricted to good prefixes: it universally covers steps from every related state. A concrete implementation may truncate its source semantics at the first bad boundary, so no meaning after UB is required. Mark an enabled invalid operation as bad at its pre-state or give it a terminal bad transition; the source adequacy theorem must justify that choice. An invalid production cannot wait until a later observation: [Rust's validity rule](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md#L115) treats producing an invalid value as immediate UB.

The relation direction is property-dependent. This comparison is derived from the quantifiers, not an attribution to a specific compiler paper:

| Relation form | Condition for source safety from model safety |
| --- | --- |
| Source-to-model simulation | Covers all source choices and reflects bad prefixes, as in this specimen. A successful-execution-only version is insufficient. |
| Model-to-source simulation | Alone can omit a bad source choice; add source coverage/bad reflection or another theorem establishing the required direction. |
| Bisimulation | Both directions still need compatible bad/outcome observations and input coverage; matching only successful observations is insufficient. |
| Logical relation | Its interpretation must entail the same source bad-prefix exclusion; safe-fragment typing or successful-value membership alone does not do so. |
| Contextual refinement | Depends on the observation and UB convention. Treating source UB as unrestricted behavior does not itself allow inferring source safety from a safe refinement. |

A weaker good-prefix interface is possible, but requires a separate proof that matching all preceding good steps reaches the first bad operation. A premise saying the entire source execution is safe would defeat the intended argument. Neither agreement on successful returns nor a simulation proved only for already-safe source programs supplies badReflect.

### Input coverage, nondeterminism and composition

Basis: derived + checked generic theorem.

Certificate.coverAllInputs separately requires:

```text
∀ s, sourceInitial(s) ⇒ ∃ m, modelInitial(m) ∧ R(s,m)
∀ m, modelInitial(m) ⇒ Safe(modelStep,modelBad,m).
```

It concludes source safety for every declared sourceInitial. This makes coverage visible: the model's carrier/decoder cannot silently discard source states required by the client theorem. Incoming valid references may be a justified language/interface precondition; an invented stronger decoder domain requires its own coverage argument. A theorem about zero admitted states is mathematically valid and operationally useless.

stepMatch quantifies over **every** source transition. Its existential model match is sufficient because model safety is universal over all reachable model choices. Thus overapproximation is compatible with this safety proof. Selecting only a favorable source scheduler, input, callback result or environment behavior breaks coverage. Extra model behaviors may make proofs harder but do not by themselves make this implication unsound.

Certificate.compose uses R_ST(s,t) = ∃ m, R_SM(s,m) ∧ R_MT(m,t). It constructs a new certificate by lifting the second certificate over each intermediate prefix, including the bad-reflection prefix. Heterogeneous states and step granularities are permitted. The intermediate bad predicate and meaning must coincide at the interface; changing monitors, representations or premises needs an explicit adapter theorem. A checksum, relation name or common Lean carrier is not that theorem.

The kernel reports that reflectSafety, compose and coverAllInputs depend on no axioms. This is evidence about these exact abstract terms; Lean's executable/kernel/runtime and imported initialization environment remain trusted checking machinery.

### Outcomes and the first failing boundary

Basis: primary source + derived interface design.

Aeneas [Primitives.lean 65–110](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Primitives.lean#L65) models Result with return, failure effects and divergence, with multiple failure tags including panic and undef. The effect's failure continuation has no inhabitants. In contrast, [InterpStatements.ml 783–807](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/InterpStatements.ml#L783) defaults drop statements to no-ops, maps Abort uniformly to panic and rejects unwind resume. The two levels do not independently prove the source meanings of all these tags.

Derived outcome interface should retain at least ordinary return, panic initiation, unwinding cleanup/handler continuation, process abort, UB/invalid operation, divergence, and environment/interference transitions. Translation rejection and unsupported syntax belong to admission status, not to a defined source execution outcome. A model undef marker may conservatively deny all claims without asserting that the actual Rust operation is UB. This matches the cce [forbidden-execution policy](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/SEMANTICS.md#L142).

For UB freedom with allowed panics, the accepted model set may contain panic but must still reject UB. Collapsing both into a failure accepted by that contract loses the needed distinction. Rejecting both can be conservative for a restricted claim if every source bad prefix reflects into the rejected union. Permitting divergence similarly requires a proof that a preceding bad operation cannot disappear into divergence. Guards must be checked before entering invalid typed values, even if the result is discarded.

Short-circuiting and evaluation order are step/trace obligations. Destructor and unwind calls are executable dependencies. A callback may invalidate a borrow or global invariant before re-entry; a source run spawning a detached child has relevant prefixes after the parent returns. A parent return alone supplies no safety guarantee for that child.

### Progress, resources and security

Basis: original checked counterexamples + derived property-specific interfaces.

The specimen's stutteringCertificate relates the source step n→n+1 to a Unit model with no steps. Every finite source step matches zero model steps; both bad predicates are false. sourceHasInfiniteChain and targetHasNoStep check the mismatch. This is a discriminating theorem specimen, not a finite Rust test. It demonstrates that the certificate's safety conclusion intentionally omits termination.

To transfer termination, add a well-founded rank decreasing on unmatched source steps, with source steps causing target progress or decreasing rank. To transfer liveness under scheduling, also state fairness and match observable events; fair target executions do not automatically represent all fair source executions. A bounded model fuel failure cannot be classified as real source divergence without an adequacy theorem for the chosen bound or an unbounded semantics.

| Desired property | Additional derived interface |
| --- | --- |
| Finite-prefix memory/type safety | Source bad-operation monitor and universal prefix coverage; state relation includes validity and resource authority. |
| Outcome-sensitive partial correctness | Match return values and accepted failures for every defined relevant outcome; forbidden prefixes remain rejected before divergence. |
| Total correctness / liveness | Progress/rank or divergence-sensitive correspondence plus explicit scheduling/fairness assumptions. |
| Resource bounds / allocation failure | Resource state and charging relation; account for erased steps, allocation/deallocation and environment failure, with initial budgets. |
| Concurrency / atomics | Thread and memory-event relations under a selected memory model; race/ordering/interference choices and detached execution coverage. |
| Confidentiality / noninterference | A trace-pair or relational property and coupled initial/environment observations; single-run safety is insufficient for a hyperproperty. |

A monitor can encode ordinary trace safety into bad states, but not arbitrary liveness or hyperproperties without changing the theorem domain. A two-run product certificate may be suitable for some security policies; it must couple nondeterministic choices as the policy requires. No source atomics/weak-memory, resource-cost or security theorem was checked here.

One concrete source boundary is [Aeneas Core/Atomic.lean 7–13](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Core/Atomic.lean#L7): this file introduces AtomicBool and AtomicU32 as axiomatic types with TODO markers. This narrow observation establishes no atomic operation or weak-memory correspondence theorem and is not a whole-library support verdict.

### Anneal interfaces and proof-generation responsibilities

Basis: derived.

Use separate artifacts for input admissibility, per-pass witnesses, model safety and consumer-property meaning. A verified obligation generator needs a theorem that every accepted witness entails stepMatch/badReflect and that all required inputs/dependencies are covered. The untrusted producer may discover relations, invariants and proofs; the checker must verify the exact propositions, not trust producer-selected requirements. A closed Lean property proof about generated scaffolding does not establish that the scaffold denotes Rust or that the independently required property was included.

Pass premises may depend on local invariants established by preceding certificates. Record their domains and preservation rules. Incoming resource validity can be an interface premise; complete implementation safety cannot be smuggled into a pass's relation. This distinction also prevents cyclic module contracts from proving one another without a common operational induction.

## Boundaries

Answered here: the generic mechanism, direction, quantifiers, noncircular safety premise and composition proposition. Unexamined here: concrete Rust/source adequacy, a complete outcome-aware Charon/Aeneas correspondence, source fairness/cost/security semantics and a real obligation-generator soundness theorem. Those are research gaps with named endpoints, not consequences of failing to implement future Anneal.

The specimen neither asserts arbitrary Rust safety nor checks an actual pass. It has no executable Rust definitions, model primitive axioms or borrowed-memory semantics. No performance measurement or full upstream proof replay was performed.

## Evidence

Lean source SHA-256 `70953b0168c85d511a8481f37576a89807a6a84a075cba5c7d1e71e0f748d03c`; binary SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`. Exact checked propositions are readable in PrefixCertificate.lean. Raw stdout/stderr and execution metadata are report-owned artifacts.

Aeneas primary blobs: Primitives `b5cb07e5f19b9a5e1b39d373ca157ce5ae3627b3`; InterpStatements `e921d3e1411ead14784c1136d104f9aadab18d25`. Rust validity source blob `ff34d0af28ca3ec42f548abf6cd3bce5840a6798`. The linked revisions and cce source documentation are separate from the original derived theorem.

## Revalidation

Run the specified Lean binary directly on PrefixCertificate.lean from the package directory, without lake or external packages. Confirm exit zero, empty stderr and five no-axioms lines. Check source, binary and initialization/runtime hashes before reusing the recorded result. A different compatible checker may check the source anew; that is a new observation. Package validation and this generic theorem check do not discharge Rust adequacy.

*Authored by an AI agent acting on joshlf's behalf.*
