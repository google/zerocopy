# JVM and eBPF admission, typed assembly, and execution preservation

## Summary

Bytecode acceptance establishes a property of the admitted bytecode under its type, memory and environment model. It does not by itself establish that source compilation, helper implementations, loading or native execution preserve that property. JVM stack-map checking, Jinja's proved verifier, Linux/PREvail analysis, refinement-type certificates, and typed assembly put different work on each side of this boundary.

## Applicability

The normative JVM subject is Java SE 25, particularly JVMS §4.7.4 and §4.10. The formal JVM subject is Jinja at AFP mirror revision `352a4e06c2e2c1dc358200e2a87bd930e458ca90`, not the complete industrial JVM. Linux `0fcb05b72344f40806cbe810de8872f1698bf053` and PREVAIL `cefe6a799f8b8f37aa2560e196f223802717c1e7` are inspected source implementations, not newly verified binaries. No kernel loading, JIT execution or verifier build was performed.

## Findings

### A JVM stack map is checked typing evidence

Basis: **normative**.

[JVMS SE 25 §4.10](https://docs.oracle.com/javase/specs/jvms/se25/html/jvms-4.html#jvms-4.10) assigns version-dependent verification strategies: type checking for class versions at least 50.0, with a specifically constrained fallback at exactly 50.0, and type inference for older versions under the stated profiles. [§4.7.4](https://docs.oracle.com/javase/specs/jvms/se25/html/jvms-4.html#jvms-4.7.4) defines offset-indexed local/operand-stack frames; a missing attribute means an implicit empty table, not permission to skip checking.

The instruction rules check applicability and successor type compatibility, including exception edges and initialization-sensitive values. Producer maps do not become authoritative merely because they are present. These static constraints remove certain per-instruction checks; dynamic array bounds, null checks, runtime linking, native methods and execution-engine behavior retain their own obligations. A source compiler can be untrusted for bytecode type safety when the emitted bytecode is checked, but a source-specific functional specification still needs source/bytecode correspondence.

### Jinja separates verifier correctness from execution type safety

Basis: **source**.

In `thys/Jinja/BV/BVExec.thy`, the Kildall analysis produces method typings. `wt_kil_correct` and `wt_kil_complete` relate its result to the specified welltyping; `jvm_kildall_correct` equates the executable program-verifier predicate with the declarative one.

`BVSpecTypeSafe.thy` supplies the next link: `BV_correct_1` preserves conforming states for a JVM step, `BV_correct` lifts this over execution, and `BV_correct_initial` establishes conformance for a permitted entry method. These premises include a well-formed typed program and the modeled initial state. `LBVJVM.thy` additionally instantiates lightweight bytecode verification, illustrating the producer-analysis/consumer-checking split. Its existence does not make the industrial Java verifier, class loader, garbage collector or JIT instances of this theorem.

The useful Anneal pattern is a declared typing/resource judgment plus a theorem from accepted judgments and entry-state conformance to the required safety result. A successful type inference run and a checked type certificate are distinct endpoints.

### Linux admission includes analysis, environment checks and later rewrites

Basis: **source**.

The inspected `kernel/bpf/verifier.c:bpf_check` prepares BTF, applies CO-RE relocation, discovers/checks subprograms, resolves resources, checks CFG and attachment information, then invokes main/subprogram analysis. After successful analysis it still performs instruction rewrites: loop optimization, privileged dead-code cleanup or sanitization, context-access conversion and miscellaneous fixups. Thus a certificate tied only to the pre-rewrite instruction array does not automatically cover the executable that leaves the verifier.

Helper and kfunc checking depends on the selected prototypes and runtime environment. Alignment and privilege flags change admission behavior. An independent certificate must identify those definitions and configurations, and either cover the later rewrites or bind and check the resulting program. A kernel return code is an implementation result, not a standalone formal soundness theorem.

### PREVAIL and refinement certificates expose separate checking opportunities

Basis: **source**, primary theorem.

PREVAIL `src/crab/ebpf_checker.cpp:89–153` visits explicit assertions against an abstract domain. Failed numeric entailment raises a verification-failure signal; an unreachable abstract state needs no assertion check. Separate handlers check accesses, stores, divisors, loop counts and callback targets. Its abstract state, transformer, entailment implementation, parser and runtime contracts remain part of that analyzer's assurance path; the inspected checker function does not itself constitute an independently verified certificate consumer.

[Hamza et al., OOPSLA 2025](https://jorgenavas.github.io/papers/types-ebpf-oopsla-2025.pdf), §5.6 Theorems 1–2, prove progress and preservation for a flow-sensitive refinement-type model and its runtime/type-environment relation. §6 separates inferred annotations from checking the type rules. The property scope is region safety and information-flow safety; the paper does not establish a mechanized correctness theorem for the complete present Linux or PREVAIL implementation. Arithmetic implications used by a type checker must themselves have a trusted or checked decision path.

### Admission and native preservation compose through explicit subjects

Basis: **derived**, narrow reused primary comparisons.

Typed assembly/PCC binds an assembly program to a typing or safety-policy derivation; JIT preservation starts from a source already satisfying its source-side conditions. The existing [PCC/TAL report](../pcc-tal-foundational-policy-certificates/REPORT.md) and [Jitterbug theorem-direction comparison](../refinement-policy-and-safety-direction-comparison/REPORT.md) explain those local theorem roles. A Jitterbug-style result does not prove the admission verifier sound, and a bytecode verifier does not prove the JIT correct.

For Anneal, choose whether the consumer's safety claim concerns original Rust, captured IR, bytecode or native code. A checked target policy can justify target safety directly; transferring a Rust contract additionally requires its specified correspondence direction, environment/primitive interpretation and entry premises. This is a completed bounded mechanism comparison, with deployment instantiation left explicit.

## Boundaries

**Not examined:** executing JVM/eBPF fixtures, complete Java class loading/JMM/native libraries, full Linux verifier soundness, every PREVAIL domain rule, or a newly verified JIT. **Known scope limit:** Jinja and the refinement type system describe their modeled languages and environments. No arbitrary-Rust frontend theorem is required to understand or compare these admission mechanisms.

## Evidence

support/evidence.json records exact source paths, normalized-text hashes and theorem/checker endpoints. Normative and primary-paper links appear beside claims. The two reused report sections were read for their property/preservation boundaries; they are not treated as source-level acceptance guarantees.

## Revalidation

Recheck the JVM version rules and successor/exception/initialization checks; follow Jinja's executable verifier through welltyping to state conformance. For eBPF, inspect the complete `bpf_check` ordering and post-analysis rewrites together with helper/BTF/target configuration, rather than checking only the central state-exploration routine.

*Authored by an AI agent acting on joshlf's behalf.*
