# Verified compiler-pass composition: CompCert 3.18 and verified validators

## Summary

Verified compiler correctness is compositional only when every stage exports a semantic relation that the next proof can actually compose. CompCert 3.18 makes this concrete. It proves forward simulations for individual passes, composes those simulations into a source-to-assembly forward simulation, and then obtains the whole-compiler backward simulation through additional semantic side conditions: source receptiveness, target determinacy, event factoring, and a separate strategy-to-language simulation. The final theorem is conditional on successful compilation. A failed or disabled pass does not silently inherit correctness; it either contributes an identity simulation or produces no successful compiler result.

This matters because “each pass is verified” is not, by itself, an end-to-end proof rule. The relation direction, treatment of stuttering, trace model, failure semantics, and auxiliary hypotheses have to line up. CompCert's generic `compose_forward_simulations` theorem explicitly constructs the intermediate-state witness and combines the well-founded measures needed when a source step can correspond to zero target steps. Its backward-simulation composition theorem carries an additional `single_events` premise. Its forward-to-backward conversion requires a receptive source semantics and determinate target semantics.

Tristan and Leroy's POPL 2008 verified-validator construction shows a complementary way to satisfy the same interface. An optimization implementation may remain unverified if a formally proved validator checks each concrete source/target pair and the wrapper rejects outputs the validator cannot establish as related. The wrapper then exports the same kind of pass-level semantic-preservation fact that a directly verified transformation would export. The unverified optimizer is therefore removable from the correctness proof, but the validator, its semantic relation, and the reject-on-failure wrapper are not.

The reusable rule for Anneal is to model translation boundaries by explicit proof obligations that compose. A Charon, Aeneas, normalization, or proof-generation stage can be directly verified, validated after the fact, or trusted under an explicit assumption. What cannot be done soundly is to let a stage return ordinary success when its required relation is unknown. Composition preserves the weakest semantic contract actually established at every boundary; it does not recover behaviors, effects, definedness conditions, or source correspondence that an earlier stage omitted.

No compiler or prover was executed for this report. CompCert claims were checked against exact 3.18 source at `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` and the corresponding 3.18 documentation. Verified-validator claims were checked against Tristan and Leroy's POPL 2008 paper, DOI `10.1145/1328438.1328444`.

## Applicability

This report addresses the #3720 subject **Verified compiler-pass composition techniques**. It focuses on vertical composition across a sequence of compiler transformations and on the verified-validator pattern for making an otherwise unverified transformation fit such a sequence.

The concrete compiler is CompCert 3.18. Its `VERSION` file identifies the examined revision as 3.18. The relevant implementation is principally:

- `common/Smallstep.v`, which defines forward and backward simulation machinery and their composition/conversion theorems; and
- `driver/Compiler.v`, which chains pass-level theorems into whole-compiler semantic preservation.

The second subject is the POPL 2008 paper by Jean-Baptiste Tristan and Xavier Leroy. Its generic construction is not tied to the current CompCert implementation revision, but it explains how a verified validator can turn an unverified pass into a pass with a proved semantic-preservation interface.

This report does not establish that CompCert's simulation relation is the right semantic relation for Rust or Anneal. CompCert's event model, undefined-behavior treatment, memory model, and language boundaries are system-specific. The useful result is structural: proof-producing passes and validated passes can compose when they establish compatible relations, and the whole-pipeline theorem must preserve all side conditions needed by those relations.

The report also distinguishes vertical pass composition from separate compilation and linking. CompCert 3.18 proves a separate-compilation theorem as well, but that proof has additional linking premises. Passing from “each compilation unit was compiled correctly” to “the linked program is correct” is a different composition problem from chaining compiler passes.

## Findings

### Pass proofs compose through a shared semantic interface, not through their implementation structure

CompCert 3.18 represents pass correctness using simulations between formal small-step semantics. In `common/Smallstep.v`, `compose_forward_simulations` has the abstract shape:

```text
forward_simulation L1 L2
→ forward_simulation L2 L3
→ forward_simulation L1 L3
```

The theorem does not inspect either compiler pass. It composes the semantic witnesses exported by their proofs. This is the central modularity property: once a transformation establishes the required relation between its input and output languages, later composition depends on that relation rather than on the transformation's algorithm.

The proof is more substantial than relation transitivity on final values. A forward simulation can match one source transition with one or more target transitions, or with no target transition when an internal step is stuttered. To compose two such simulations, CompCert pairs their simulation indices, existentially retains an intermediate `L2` state, and uses a lexicographic well-founded order. The first component closes one simulation's order transitively; the second component carries the other order. This is what keeps repeated zero-step matches from turning the composed simulation into an unsound infinite stutter.

This detail generalizes. A pipeline stage may be semantically “transparent” for some steps without being syntactically the identity. If a proof system allows zero-step correspondence, its composition theorem needs a progress argument or well-founded measure strong enough to rule out bogus preservation by infinite stuttering.

Basis: **source** — `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, `common/Smallstep.v`, `compose_forward_simulations`.

### The whole CompCert proof is an explicit chain of pass-level simulations

`driver/Compiler.v` constructs `cstrategy_semantic_preservation` by repeatedly applying `compose_forward_simulations` to the correctness theorem for each transformation. The chain includes expression simplification, local simplification, Csharpminor and Cminor generation, instruction selection, RTL generation, inlining, register-related transformations, dead-code-related transformations, allocation, linearization, label cleanup, stacking, and assembly generation.

This construction provides a useful audit property: the top-level theorem visibly depends on a preservation theorem for each transformation that participates in the successful pipeline. There is no final theorem that simply assumes “all passes are correct” as an opaque aggregate premise.

Optional passes are handled by `match_if_simulation`. If the pass is enabled, the caller must supply its forward-simulation theorem. If it is disabled, source and target are equal and the proof uses `forward_simulation_identity`. In other words, skipping a pass and validating a pass are both explicit proof cases. Neither is represented by silently dropping a proof obligation.

The 3.18 manual describes the proof at the same architectural level: it splits semantic preservation into separate per-pass proofs and derives the final theorem by composition.

Basis: **source** — `driver/Compiler.v`, `cstrategy_semantic_preservation`, `match_if_simulation`; **documentation** — CompCert 3.18 manual, chapter 1.

### Simulation direction and semantic side conditions matter at the pipeline boundary

CompCert's final whole-compiler theorem is stated as a backward simulation from C semantics to assembly semantics, but most of the pass chain in `cstrategy_semantic_preservation` is first assembled as a forward simulation.

The conversion is explicit. `forward_to_backward_simulation` in `common/Smallstep.v` requires:

```text
forward_simulation L1 L2
receptive L1
determinate L2
```

and produces a `backward_simulation L1 L2`.

`driver/Compiler.v` applies that theorem only after also factoring the source semantics so the target's event structure is suitable. It supplies strong receptiveness for the source strategy semantics and determinacy for assembly.

The source-language connection is another proof step. `c_semantic_preservation` composes a backward simulation from ordinary C semantics to the atomic strategy semantics with the already established strategy-to-assembly backward simulation. `compose_backward_simulation` itself requires `single_events L3`.

Thus, even in a mature verified compiler, “compose the pass proofs” expands into several distinct obligations:

1. establish a compatible relation for each transformation;
2. compose those relations in the direction their generic theorem supports;
3. discharge trace/progress side conditions needed to change proof direction or semantic presentation; and
4. connect the user-facing source semantics to the internal semantics used by the pass chain.

A pipeline cannot safely replace one of these steps with “the intermediate representations look equivalent.” The omitted side condition may be exactly what rules out an invalid behavior.

Basis: **source** — `common/Smallstep.v`, `forward_to_backward_simulation`, `compose_backward_simulation`, `factor_forward_simulation`; `driver/Compiler.v`, `cstrategy_semantic_preservation`, `c_semantic_preservation`.

### Successful compilation is a premise, so pass failure composes by failing closed

The top-level CompCert theorem is conditional:

```text
transf_c_program p = OK tp
→ backward_simulation (Csem.semantics p) (Asm.semantics tp)
```

This shape is important. A compiler transformation is not required to produce output for every input. If a pass returns an error, there is no target program to which the semantic-preservation theorem must attach.

The same principle appears in Tristan and Leroy's validator wrapper. They model a compiler or pass as `C : L1 → L2 + Error` and a validator as `V : L1 × L2 → boolean`. If the compiler produces `c2` and the validator accepts it, the wrapper returns `c2`. If the compiler fails or the validator rejects, the wrapper returns `Error`. Their Theorem 1 says that if validator acceptance implies the desired relation `c1 ≤ c2`, then this wrapper compiler is formally verified even if `C` itself is not.

This gives a clean composition boundary for difficult or heuristic stages: the stage may be arbitrarily complex, but ordinary success is gated by an independently proved acceptance condition. Validator incompleteness is therefore a usability or compilation-success issue, not a soundness issue. A correct transformation that the validator cannot prove is rejected rather than smuggled through as verified.

For Anneal, the analogous requirement follows directly from its fail-closed promise. If a translation boundary lacks the evidence required for the result's Rust-level claim, that boundary must prevent ordinary verification success or surface an explicit assumption/trust classification whose semantics changes the final claim. “Could not validate, continue anyway with an ordinary success result” does not compose.

Basis: **source** — `driver/Compiler.v`, `transf_c_program_correct`; **published result** — Tristan and Leroy, POPL 2008, §2.1 and Theorem 1; **derived** — application to Anneal's fail-closed result semantics.

### A verified validator replaces the pass proof only when it exports the same required relation

Tristan and Leroy define formal verification of a pass through a relation `≤` between source and target programs. A validator is verified by proving that every accepted pair satisfies that relation. The wrapper theorem works because accepted output is indistinguishable, at the semantic interface, from output of a directly verified pass: both establish `c1 ≤ c2`.

This is the key reason validators compose with other verified passes. The composition boundary is not “this tool has a proof.” It is “this tool establishes the relation required by the surrounding proof.”

That distinction becomes critical when stages use different notions of preservation. For example, equality of normally terminating return values does not automatically compose with a later theorem whose premise requires preservation of traces, memory effects, definedness, or divergence. A validator that proves a weaker relation may be entirely sound and still be insufficient for the end-to-end theorem.

The POPL 2008 paper illustrates this problem inside a single optimization. Its symbolic validator does not compare only final symbolic values. It also tracks operations whose definedness matters and requires the transformed block not to introduce stronger failure conditions. Otherwise, a transformed block could compute the same final value on successful runs while adding a division-by-zero or invalid memory access. The validator relation therefore includes more than successful-result equality.

For Anneal, relation compatibility should be a first-class review question at every translation boundary. The relevant contract must include the observations needed by the reported promise: undefined behavior, ownership/resource effects, panics or divergence when material, source correspondence, and any trusted assumptions. Composition cannot reconstruct a dimension that one stage chose not to model.

Basis: **published result** — Tristan and Leroy, POPL 2008, §2.1–2.2; **derived** — compatibility requirement for heterogeneous proof/validation stages.

### Composition preserves the weakest established end-to-end contract

Suppose three stages establish relations `R12`, `R23`, and `R34`. An end-to-end theorem needs either a generic theorem showing those relations compose, or explicit bridges that convert them into a common relation with all necessary premises discharged.

This sounds elementary, but it prevents a common verification error: treating individually meaningful theorems as if their conjunction implied a pipeline theorem. If `R12` excludes unsupported source operations, `R23` assumes termination, and `R34` talks only about successful pure values, the chain has not proved preservation of arbitrary source executions merely because every stage has a local theorem.

CompCert avoids this by making the simulation relations and their generic composition theorems part of the shared semantic infrastructure. When it changes semantic presentation, it invokes named conversion theorems with named premises. Tristan and Leroy avoid the problem by making their verified wrapper export the same preservation relation expected from a verified pass.

For Anneal, a useful result record should therefore make each boundary leg explicit:

```text
Rust semantics
  --R1--> Charon/LLBC
  --R2--> Aeneas model / generated Lean
  --R3--> Anneal proof obligations
  --R4--> kernel-checked theorem
```

For each arrow, later architecture work should be able to answer: what relation is established, by what evidence, under which assumptions, and what happens when establishment fails? A trusted leg can still appear in the chain, but trust should be named rather than confused with a proof.

Basis: **derived** from the two composition patterns above and Anneal's explicit TCB/result contract.

### Separate compilation shows that vertical pass composition is not the only composition boundary

CompCert 3.18 also proves `separate_transf_c_program_correct`. It assumes each source compilation unit successfully compiles and that the source units link. It then establishes that the assembly units can be linked and that the resulting assembly program backward-simulates the linked source program.

The proof first obtains a `match_prog` relation for each compiled unit, then uses `link_list_compose_passes` to transport that relation through linking, and finally applies whole-program semantic preservation.

This is a useful boundary marker. Per-pass vertical composition, per-module horizontal composition, and final linking are separate proof obligations even when one verified compiler owns all of them. An Anneal design that verifies functions or crates independently will need both kinds of composition: translation-stage correctness and abstraction/linking correctness. Solving one does not imply the other.

Basis: **source** — `driver/Compiler.v`, `separate_transf_c_program_correct`; **derived** — distinction between vertical translation composition and program/module composition.

## Boundaries

This report does not prove any current Anneal translation stage correct. It extracts composition techniques and proof obligations from CompCert 3.18 and the verified-validator construction.

No Rocq/Coq build was run. The exact source was inspected, but theorem checking is inherited from the published CompCert development rather than re-executed here.

CompCert's `forward_simulation`, `backward_simulation`, event traces, receptiveness, determinacy, and undefined-behavior treatment are specific formal definitions. This report does not claim that Anneal should adopt them verbatim.

The report does not survey proof-producing compilation, proof-carrying code, equality saturation validators, Alive2, or every verified compiler. Those techniques may instantiate the same high-level interface but have different trust and completeness boundaries.

The POPL 2008 validator relation is tailored to instruction scheduling and its Mach semantics. Its Theorem 1 is generic in the validator relation, but the paper's concrete proof does not establish that a similar validator is feasible for Charon or Aeneas.

CompCert's current semantic-preservation theorem covers its formal C-to-Asm compiler core. The project documentation separately identifies assembling/linking and other external pieces that are outside that core proof. This report does not turn compiler-core composition into a claim of fully verified execution from source text to hardware.

The separate-compilation theorem is mentioned only to distinguish composition dimensions. This report does not analyze CompCert's linking model in depth.

## Evidence

### CompCert 3.18 source

Repository: `AbsInt/CompCert`  
Revision: `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`

- `VERSION`, blob `5fd2882f6f042e89ce617586ce5041f5762c1766`
  - identifies `version=3.18`.
- `common/Smallstep.v`, blob `cefab134fdce4f3ea2f970db49a99d987c05d3a1`
  - `compose_forward_simulations` around lines 1003–1043;
  - backward-simulation machinery around lines 1319 onward;
  - `compose_backward_simulation` around lines 1566 onward;
  - `forward_to_backward_simulation` around lines 1863 onward;
  - `factor_forward_simulation` around lines 2004 onward.
- `driver/Compiler.v`, blob `60fc74fec1411216425004f6d63567354e146e9c`
  - whole-pass match construction before the semantic-preservation section;
  - `cstrategy_semantic_preservation` around lines 344–416;
  - `c_semantic_preservation` around lines 419–434;
  - `transf_c_program_correct` around lines 446–453;
  - `separate_transf_c_program_correct` around lines 466 onward.

Evidence role: **source**.

### CompCert 3.18 documentation

- CompCert commented development, version 3.18, dated 2026-08-31: `https://compcert.org/doc/`.
- CompCert manual chapter “CompCert C: a trustworthy compiler”: `https://compcert.org/man/manual001.html`.
- Commented `Compiler` module: `https://compcert.org/doc/html/compcert.driver.Compiler.html`.

The manual states the top-level semantic-preservation theorem, explains that compile-time failure is permitted, and describes whole-compiler correctness as composition of separate pass proofs. The commented module documents the same forward-simulation, forward-to-backward, and source-semantics composition structure visible in source.

Evidence role: **documentation**.

### Verified-validator paper

Jean-Baptiste Tristan and Xavier Leroy, “Formal Verification of Translation Validators: A Case Study on Instruction Scheduling Optimizations,” POPL 2008, pp. 17–27, DOI `10.1145/1328438.1328444`.

Author-hosted copy: `https://xavierleroy.org/publi/validation-scheduling.pdf`.

The relevant material is §2.1, especially equations (1) and (2) and Theorem 1. The paper models a pass as `L1 → L2 + Error`, defines validator soundness by acceptance implying the desired source/target relation, and proves that wrapping an arbitrary transformer with such a validator yields a formally verified pass. §2.2 shows why the concrete scheduling validator tracks definedness constraints in addition to final symbolic state.

Evidence role: **published result**.

### Derived synthesis

The Anneal-specific conclusions are derived from the composition structures above and current Anneal principles: ordinary verification success cannot erase missing evidence, and the TCB/result must make trusted assumptions visible. No source above states an Anneal architecture.

Evidence role: **derived**.

## Revalidation

For another CompCert revision, first diff `common/Smallstep.v` at the simulation composition/conversion theorems and `driver/Compiler.v` at the whole-compiler semantic-preservation section. Recheck:

1. the type and side conditions of `compose_forward_simulations`;
2. the type and side conditions of `compose_backward_simulation`;
3. the premises of `forward_to_backward_simulation`;
4. the structure of `cstrategy_semantic_preservation`;
5. the source-semantics bridge in `c_semantic_preservation`; and
6. the success premise of `transf_c_program_correct`.

If those interfaces are unchanged, most of this report can be revalidated without rereading every individual pass proof. If the simulation framework, event semantics, or proof direction changes, repeat the composition analysis rather than assuming equivalence from similar theorem names.

For the verified-validator pattern, reread §2.1 of Tristan and Leroy 2008. The discriminating check is that validator acceptance still implies exactly the relation required by the surrounding compiler proof and that rejection prevents ordinary successful output. A new validator with a different relation needs a fresh compatibility argument even if it uses the same wrapper pattern.

For Anneal architecture work, maintain a table of translation boundaries with four columns: source semantics, target semantics, established relation, and failure/trust disposition. A proposed end-to-end theorem should be derivable by composing those rows with named bridge theorems or explicit trusted assumptions. Any row whose relation or failure behavior is “unknown” is a precise indication that ordinary end-to-end verification success is not yet justified.