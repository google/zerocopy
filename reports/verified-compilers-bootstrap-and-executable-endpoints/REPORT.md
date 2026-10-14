# Verified compilers, bootstrap, and executable endpoints

## Summary

An abstract compiler-correctness theorem, a proved validator, and a verified compiler binary solve different trust problems. CompCert's selected theorem exports a backward simulation after successful compilation. CakeML's selected theorem reaches installed machine code and retains configuration, FFI, and resource-limit premises; its bootstrap scripts connect a compiler implementation to that path. Current CertiRocq selected source shows substantial local refinement obligations but does not establish a complete installed compiler or runtime theorem in this investigation.

## Applicability

This report compares exact inspected CompCert3.18 and current selected CakeML and CertiRocq source files with Tristan/Leroy's POPL2008 validator construction. It does not rerun their proofs. Historical CakeML bootstrap documentation supplies context; the current source statements, rather than a presumed historical theorem, support the concrete endpoint observations. P020–P021 and T021/T043–T048 receive partial coverage. Runtime isolation and diverse double compilation remain design considerations, not experiments performed here.

## Findings

### CompCert: accepted compilation exports a simulation

**Basis: source.** At `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, `driver/Compiler.v:446–452` states:

```text
transf_c_program p = OK tp ->
backward_simulation (Csem.semantics p) (Asm.semantics tp).
```

The operands identify a formal C program and formal assembly program. The theorem does not by itself identify a parsed source file, an assembled object, linked executable bytes, or the running OCaml compiler binary. The nearby separate-compilation theorem adds conditions about successful component compilation and formal linking. In `common/Smallstep.v:1298–1312`, the backward-simulation final-state, progress, and step-matching obligations each require `safe L1 s1` for the related source state. This exposes a decisive premise: the theorem constrains target behavior through already-safe source execution; it is not a theorem that an arbitrary source program has no undefined behavior.

This pin and these statements are direct source observations. Correct extraction, preprocessing, parser-to-formal-AST binding, assembler, linker, loader, hardware, and actual external-function behavior require their own evidence. The report does not claim these are all unverified in every CompCert configuration; it says the selected theorem alone does not discharge them.

### A validator can export the required pass theorem

**Basis: documentation from primary POPL2008 §2.1–2.2, PDF pp.2–3.** Theorem1 proves that an arbitrary compiler wrapped by a sound validator is verified: successful accepted output satisfies the selected relation, while rejection returns an error. The concrete relation preserves well-defined terminating source behavior and result. Symbolic scheduling validation tracks definedness constraints as well as final expressions, so a target cannot introduce a new failing operation. This is a proof about validator acceptance; it need not produce a separate derivation for every accepted pair. [Author paper](https://xavierleroy.org/publi/validation-scheduling.pdf).

**Basis: derived.** A certifying pass with a proof object and a verified boolean validator can occupy the same composition boundary if both export exactly the required semantic relation. Their checking paths differ. A proof term checked by the kernel can exclude the producer from trust; a once-proved validator also needs its computation faithfully executed. Neither permits accepting unsupported input or a timeout as ordinary verified success.

### CakeML: the installed-code theorem keeps its premises

**Basis: source.** At `CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`, `compiler/proofs/compilerProofScript.sml:269–295` gives `compile_correct`. Under `config_ok cc mc`, successful compilation supplies source behaviors and states that every appropriately installed machine state satisfies:

```text
machine_sem mc ffi ms ⊆ extend_with_resource_limit behaviours.
```

`installed` includes code, code-buffer space, data, data space, FFI names, heap-register choices, machine configuration, and shared-memory information. Parse and type errors have source-semantic conclusions; assemble/config/static error branches make no correctness claim (`T`). The nearby `compile_correct_safe_for_space` variant explicitly addresses the resource extension. This is a modeled installed-machine endpoint with visible assumptions, rather than an unqualified equality of all behaviors.

The x64 bootstrap proof at `compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml:56–86` derives `cake_compiled_thm` by composing the compiled-program result, source nonfailure, machine configuration, and initialization proofs. Its `compile_correct_applied:169–182` requires `Fail` absent from the compiler program's source semantics and `repl_ready_to_run`; the conclusion again includes the resource-limit extension. This is materially closer to an executable compiler theorem than proof of an abstract compilation function alone. It remains relative to the modeled basis FFI and machine semantics.

**Basis: documentation.** The primary CakeML project description explains its in-logic bootstrap: synthesize the compiler's CakeML implementation, then apply the compiler to itself inside HOL to obtain a verified binary. This observation does not identify or validate a downloaded release archive in this investigation. [Project description](https://cakeml.org/).

### CertiRocq: retain the exact local scope

**Basis: source.** At `CertiRocq/certirocq@906241771e0ac0088403dec12a0027213f114dd1`, `theories/Compiler/correctness.v:124–150` explicitly identifies a remaining bridging mismatch involving primitives and axiom-free environments. `metarocq_to_anf_correct` requires the MetaRocq pipeline postcondition, stronger well-formedness flags excluding axioms and primitives, and successful ANF conversion, then concludes existence of `M` and `refines_toplevel`.

The separate `theories/LambdaBox_to_LambdaANF/anf_toplevel.v:143–149` defines `refines`: every successful source fuel evaluation yields a successful target fuel evaluation, a cost bound `c_tgt ≤ t_src + M`, and `value_ref`. Lines569–580 define `refines_top` and give a conversion theorem under additional surrounding context. This report does not silently identify `refines_toplevel` with `refines_top`; the selected current files use different names, and no fresh build established the linkage. A draft lemma with `Admitted` at correctness.v:218–262 is inside a comment, so it is not evidence of an active admitted theorem.

The project README says substantial parts are verified and others remain in progress; its current targets include Clight and WebAssembly. That statement and a local ANF theorem are insufficient to infer that every plugin, quoting path, runtime, garbage collector, FFI bridge, parser, or bootstrapped checker binary is verified. [Project source](https://github.com/CertiRocq/certirocq/tree/906241771e0ac0088403dec12a0027213f114dd1).

### Derived Anneal trust decomposition

**Basis: derived.** Keep separate theorem endpoints for: source bytes to admitted AST; AST to logical semantics; logical checker soundness; checker source to installed checker bytes; runtime/FFI assumptions; acceptance to the artifact eventually used. An abstract proof about the checker function removes algorithmic doubt without proving that the host executes it faithfully. Bootstrap can reduce that implementation gap, but only for the compiled program and its actual configuration.

Producer isolation protects the checker process and its inputs. It is orthogonal to relation correctness: an isolated producer can still submit a proof of the wrong property. Diverse double compilation can test reproducible compiler behavior under its own assumptions, but should not be counted as a semantics theorem without the matching formal argument. Hardware/OS containment and ISA fidelity remain distinct from logical validity.

For Anneal, publish acceptance only when the required source-failure proposition, representation relation, and artifact identity all hold. The producer's changing heuristics need not be in the logical TCB if a checked certificate supplies those obligations. The checker binary, admission/serialization wrapper, and actual invocation still deserve explicit identities and boundary analysis.

## Boundaries

No compiler or prover build, self-compilation, binary hash comparison, runtime execution, FFI test, or diverse double-compilation experiment was performed. Selected files do not establish complete dependency closure, absence of axioms/oracles/admissions, or release provenance. The CertiRocq predicate linkage remains unresolved; no complete current executable-path verdict is made. CompCert's backward simulation must not be interpreted as source-safety reflection.

## Evidence

- CompCert compiler blob `60fc74fec1411216425004f6d63567354e146e9c`; Smallstep blob `cefab134fdce4f3ea2f970db49a99d987c05d3a1`; source coordinates above.
- CakeML compiler-proof blob `c3184fe7a19850c9b8a9a73abe7090c2b9342948`; x64-bootstrap-proof blob `2f7eb486f51fb998d5a81efe1cf5c097446ee41e`.
- CertiRocq compiler-correctness blob `070c3f8ece907b856ca08cc001f55d9d79506691`; ANF-top-level blob `707c73e57af2eedadb6b54fcb852da6169eb6e60`; repository metadata retrieved at the exact pin.
- Tristan/Leroy, POPL2008, DOI `10.1145/1328897.1328444` as recorded on the author's bibliography; 11-page author PDF, §2.1 Theorem1 and §2.2. The prior corpus uses a proceedings-series DOI prefix; this report retains the directly inspected author coordinate.
- Read-only reference baseline `a0ff759e7d2d9a953f0ac40b326dd23197bd9188`; observations acquired2026-10-14 through pinned GitHub source and primary web documentation.

## Revalidation

Retrieve the exact files and compare blob identities, then rebuild the selected theorem with pinned dependencies before calling it checked. Resolve CertiRocq's exported predicate names against the actual build. To justify an installed checker, identify its compiler program, bootstrap theorem, configuration, FFI, resulting bytes, loader/invocation, and admission wrapper. Rerun a certificate rejection case through that complete executable path.

*Authored by an AI agent acting on joshlf's behalf.*
