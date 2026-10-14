# Functions, generics and environment certificate closure

## Summary

A function certificate needs the exact function/instantiation/environment and a relation on call state, returns, failures and resource effects. Linking certificates requires both semantic interface compatibility and complete execution closure. A producer's list of callees or a collection of successful root proofs establishes neither.

Generic/dictionary and recursive dependencies require explicit rules: quantify over admissible instantiations or bind a concrete instance; relate actual dictionaries and method targets; and discharge cycles through a simultaneous finite-prefix induction. Unknown foreign code can be summarized conditionally, but its identity, permitted effects and residual assumptions remain visible.

## Applicability

Charon and Aeneas source are pinned as in REPORT.json. Primary source inspection concerns the named generic/dispatch transformations and dependency/effect-analysis entry points, not every rustc resolution rule or every backend primitive. The cce documents supply the actual downstream restricted admission policy; the interfaces below are original derived proposals for a stronger certificate architecture.

The generic composition proof referred to here is an original Lean theorem checked in the companion prefix package. It composes relations on complete transition systems; it does not instantiate this report's module, FFI, trait or recursion rules. No complete module-linking proof or full toolchain build was performed.

## Findings

### Exact callable-certificate interface

Basis: derived original interface, grounded by the inspected call/definition seams.

A callable identity should bind original declaration, compilation configuration, source/generic arguments, lifetime/const substitutions where semantically relevant, selected implementation/dictionary, ABI, body origin and dependency environment. Source/target semantic objects must be bound to exact artifacts, not names alone.

A sufficient local interface separates:

```text
Domain_f(σ,args,instance,env)         -- admissible call states
StateRel_f(σ,μ,instance,env)         -- source/model state relation
StepMatch_f                         -- every source call/body prefix is matched
BadReflect_f                        -- every forbidden source prefix is exposed
ReturnRel_f / OutcomeRel_f          -- returned values and accepted defined outcomes
Frame_f / Effects_f                 -- permitted changes and preserved resources
Dependencies_f / EnvironmentRel_f  -- all possible executable dependencies
SpecMeaning_f                       -- independently required consumer property
```

A local proof may require incoming valid resources and a callee contract. It must not require the whole implementation already safe. Each precondition needs a caller-establishment or public-interface validity argument. A body summary that only says successful return preserves a value cannot replace StepMatch/BadReflect when proving unsafe-body safety.

The independently checked proposition should quantify over Domain_f and the relevant environment choices. The producer can generate candidate domains, dependencies and proof terms; checker acceptance needs completeness/coverage theorems for those generated objects. Renaming a producer requirement as a theorem assumption does not make a required source guarantee follow.

### Complete execution closure and source seams

Basis: source + normative; closure rule is derived.

Aeneas [Interp.ml 52–167](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/Interp.ml#L52) computes a use graph, follows declaration groups for extraction and analyzes type/function information; mixed recursive groups record errors. Aeneas [FunsAnalysis.ml 69–73](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/llbc/FunsAnalysis.ml#L69) registers trait-method analysis information with can_fail true, stateful false and can_diverge false. Derived: these implementation flags are not certified statements about arbitrary Rust implementations or unknown code.

The [cce traversal policy](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/ADMISSION_DESIGN.md#L386) follows roots to a fixed point, checks generic bodies, nested branches/loops/projections/cleanup and concrete external instantiations, and rejects unresolved dispatch/opaque calls unless registered. It distinguishes mathematical RustModel dictionaries from arbitrary Rust trait methods and destructor guarantees.

Derived independent closure algorithm starts from selected executable roots and public entry interfaces, traverses actual source/IR constructs according to a pinned semantic grammar, resolves referenced declarations and implicit effects, and repeats to a fixed point. Every reached executable item must have a checked body certificate or an exact semantic summary/residual assumption. Unknown syntax/ID/body/target rejects closure. Cycles are visited once for inventory but handled simultaneously for semantics.

Include direct calls; trait/vtable methods at every possible invocation; function pointers and callback closures; builtin/intrinsic/helper bodies; globals/TLS/initializers; promoted/const calculations; allocation/foreign/assembly operations; and destructor/drop/unwind/cleanup calls. Dictionary construction itself may have effects, but referencing a dictionary does not execute every method. Public escapes or callbacks can open the closure to environment transitions rather than a finite callee roster.

[Reference destructors](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/destructors.md#L5) execute on initialized values leaving scope and on overwriting assignment; Drop and field destruction participate, with scope-dependent order. Derived: a generic value's cleanup can be a real executable dependency even when its mathematical carrier is identical to a destructor-free type.

### Functions, callers and open-world contexts

Basis: derived.

For a safe public function, require its interface invariant to cover every language-permitted client call. A separately justified fundamental/client theorem must show admissible safe clients establish that invariant and preserve it across arbitrary allowed call sequences. Proving one selected harness or one model input is insufficient. Unsafe function certificates can expose explicit caller obligations, but safe wrappers must discharge them, including re-entry, failure cleanup and resource recovery.

An open-module theorem may be conditional on an EnvironmentRel that limits external effects and establishes contracts for imports. Quantify universally over every environment satisfying that relation. If a callback can mutate shared state or retain a pointer, the rely relation includes those possibilities and the module invariant must survive them. If detached threads exist, the relevant configuration includes their remaining execution after the entry function returns.

FFI requires an exact ABI/memory/ownership and outcome summary, with return, callback, re-entry, allocation and unwind/abort behavior. A verified foreign body supplies a checked summary; a reviewed contract leaves a named assumption. An unknown function cannot be treated as total/pure because its name is familiar or a backend returns a successful placeholder. Rejecting the boundary is a valid restricted admission decision and differs from proving it.

### Generics, dictionaries, substitution and specialization

Basis: source + derived closure laws.

Charon [duplicate_defaulted_methods.rs 31–39, 82–84](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/simplify_output/duplicate_defaulted_methods.rs#L31) substitutes a flattened impl/method binder into copied default bodies under an option gate. [remove_adt_clauses.rs 1–7, 159–162](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/simplify_output/remove_adt_clauses.rs#L1) preserves needed associated-type information and marks removed clauses; [partial_monomorphization.rs 531–556](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/normalize/partial_monomorphization.rs#L531) creates/updates pending instantiations when enabled. Derived: substitutions and removed clause identifiers need semantic evidence, not merely well-typed output.

| Obligation | Sufficient derived closure rule |
| --- | --- |
| Parametric generic certificate | ∀ admissible source types/lifetimes/consts/dictionaries, instantiate the same state/prefix/outcome theorem with a proved substitution lemma and semantic trait laws. |
| Per-instance certificate | Bind exact Rust arguments, selected impl/methods, target layout and body/configuration; do not reuse solely because erasure yields the same Lean type. |
| Unsafe trait law | Check the law for the actual selected implementation/dictionary, or identify it as an explicit residual premise; connect that law to each method and resource representation it constrains. |
| Default method / associated type | Relate the substituted body and dictionary environment to original resolution; copied bodies retain recursive calls, cleanup and implied obligations. |
| Specialization / linking | Prove that selected concrete targets implement the universally assumed interface and preserve instantiation/layout/ABI. A later link cannot silently choose a different unsafe body. |
| Dictionary/closure capture | Bind the captured values/resources and actual method/callback targets; construction and invocation effects are distinct. |
| Dynamic dispatch | Cover every permitted vtable/target and exact slot/signature/receiver relation, or restrict the domain with an independently justified public invariant. |

Charon [transform_dyn_trait_calls.rs 1–18](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/normalize/transform_dyn_trait_calls.rs#L1) lowers trait-object calls through vtable function pointers. Aeneas [PrePasses.remove_vtables 1749–1805](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/PrePasses.ml#L1749) filters vtable-generated declarations from groups. These source operations do not establish full dynamic-dispatch correspondence; the cce policy rejects unresolved function-pointer/dynamic calls.

### Recursion and simultaneous certificate composition

Basis: derived; generic relation composition checked separately.

For acyclic dependencies, compose callable certificates in dependency order, checking state/outcome/resource interfaces and callee preconditions at call sites. For a recursive strongly connected group G, assuming every final function in G already safe and then proving each from that assumption is circular.

A sufficient safety rule uses a common small-step configuration semantics, including stack/call/cleanup state. Establish the entry relation and a **local** transition-preservation/bad-reflection lemma for every constructor, including calls to group members. Then induct on finite source prefix length to obtain the simultaneous relation invariant for every reachable configuration. Recursive call transitions are ordinary steps; no termination premise is needed. Alternatively, big-step/body proofs can induct on a fuel or finite derivation, invoking recursive contracts only at strictly smaller derivations and exposing the first bad prefix at every depth. The fuel index is a proof index, not an undocumented execution cutoff.

This gives a route to close cycles without assuming complete source safety. It still requires a proved local call/interface lemma, compatible group state relations, substitution and environment invariants. Divergence-sensitive or total correctness needs an additional progress/termination argument. A cyclic producer dependency graph alone supplies none of these proofs.

The checked companion theorem composes R_ST(s,t)=∃m,R_SM(s,m)∧R_MT(m,t) with matching intermediate bad predicates. To cross logics, prove an interpretation theorem mapping each logic's state, property, resource assertions, outcomes and imported assumptions to a common semantic interface. Combining certificates with the same English label or identical carrier is insufficient.

### Specification meaning and independent obligation closure

Basis: derived + cce consumer policy.

Bind the independently required property to the original specification and source interface. If annotations/macros/generator stages produce a transformed contract, require a separate SpecMeaning relation preserving domain, preconditions, accepted outcomes and postconditions. A theorem about an implementation-derived generated specification can be vacuous even when its proof is closed.

A sound certificate consumer should have the conditional endpoint:

```text
AdmissibleInputs ∧ CompleteExecutionClosure ∧
CheckedPassCertificates ∧ CompatibleFunction/EnvironmentCertificates ∧
CheckedRequiredProperty ∧ SpecificationMeaning
⇒ declared source property, under exactly the listed residual assumptions.
```

Every conjunct needs an independently fixed meaning. The obligation generator's completeness theorem must show that its accepted result entails all required conjuncts, including implicit calls, unsafe trait laws, decoder-domain coverage and complete forbidden-execution checks. This report identifies that theorem endpoint but does not prove the generator theorem.

The [cce external-model policy](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/ADMISSION_DESIGN.md#L522) registers exact declaration, instantiation, signature and correspondence premises. Its Lean proofs can validate the model's behavior while correspondence to omitted Rust remains separately reviewed. Derived: primitive proof summaries should record both facts independently, with source/body identity and exact supported arguments.

## Boundaries

Answered here: sufficient function/generic/environment/cycle composition interfaces, their semantic premises, and the relevant concrete source transformations. No full unsafe-trait fundamental theorem, arbitrary safe-client contextual theorem, complete dynamic-target resolution or cross-logic linking proof was checked. The current generator's completeness and all implicit source-resolution obligations remain genuine unexamined research questions.

Future implementation of the proposed closure checker and certificate producers is separate engineering. There is no claim that these rules are already enforced by upstream Charon/Aeneas, nor that current restricted cce value proofs establish every open-world Rust guarantee. No source mirrors, toolchain installs or compiler executions were added.

## Evidence

Exact source blobs: Aeneas Interp `6b6f110c9d38f892fe77685bb2c2fb4c9ab60e3d`; FunsAnalysis `7bf693caa8eb8c4dd58cf37b678f792a79dfe3e2`; PrePasses `55e8bc208029e6194b038b77d407244447c97557`. Charon duplicate defaults `f06bd22f00bd7e735ce7df2f2099e9b7e1948bd1`; remove clauses `3cb85042107304e4513d41a550fd558e05f532ae`; partial monomorphization `08e2c56382579af48ac2db33c808bc3885fc784b`; dynamic lowering `818e87a0ecce4b01ca9056f684dc2a203702bbf5`. Rust destructors `0103093cf98bb69825cf840fa04878f6ad545805`.

Primary links name the complete revisions and narrow sections. cce consumer documentation was inspected at the exact commit. All proposed semantic rules and closure algorithms are labelled derived and must be checked if instantiated.

## Revalidation

Reacquire the named source seams and verify substitution/default/dispatch behavior. Re-evaluate exact dependency closure and residual assumptions after changes to compiler flags, source instantiations, dictionaries, external bodies, ABI or cleanup. Validate any concrete linked certificate against the actual semantic object, not its producer roster. Generic Lean composition replay belongs to the companion specimen; it does not establish these Rust-specific closure rules.

*Authored by an AI agent acting on joshlf's behalf.*
