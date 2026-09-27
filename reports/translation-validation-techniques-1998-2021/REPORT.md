# Translation-validation techniques: per-run refinement checking and validator trust

## Summary

Translation validation changes **what is proved** about a translator. Instead of proving once that every execution of a compiler or translator is semantics-preserving, it checks a concrete source/target pair after one translation run and accepts the result only when a validator establishes the chosen correctness relation. Pnueli, Siegel, and Singerman's original formulation already identifies three essential ingredients: a semantic framework shared by source and target, a formal correctness relation such as refinement, and an automated proof method for establishing that relation on the generated pair.

The resulting assurance depends on two independent dimensions. The first is the **semantic contract**: equivalence, refinement, simulation, preservation of defined behavior, or another relation must say precisely which source observations the target is allowed to change. The second is the **validator trust model**. An ordinary validator can itself contain bugs. A formally verified validator can instead support a theorem of the form `V(source, target) = true -> source <= target`; wrapping an unverified compiler with such a validator yields a compiler that either rejects the translation or returns a result satisfying the proved relation. Translation validation therefore does not inherently mean weaker assurance than compiler verification, but only when the validator and its semantic model have themselves received the necessary justification.

Practical validators recover enough correspondence between the two programs to make the semantic check tractable. The literature includes pass-local symbolic execution, syntactic or semantic simulation relations, invariant and value-correspondence recovery, equality-based reasoning, and SMT encodings. The validator need not reconstruct the translator's exact internal derivation. Necula's GCC work, for example, compared IR before and after optimization passes and used heuristics to infer transformations rather than requiring the optimizer to emit a proof witness.

Automation introduces an important completeness boundary. General semantic equivalence is undecidable, so a sound validator may reject a correct transformation when it cannot establish the relation. Modern bounded systems can choose the opposite practical emphasis: Alive2 aims to avoid false alarms and bounds loops, time, or memory, which means some real miscompilations fall outside the checked search space. A successful bounded check therefore establishes only the property encoded within the bound and supported semantic fragment; failure to find a bug is not an unbounded compiler-correctness theorem.

The most durable lesson is that translation validation is not one algorithm. It is an architecture consisting of a concrete translated pair, a semantics and refinement relation, a correspondence/proof method, an automation strategy, and an explicit trust/completeness boundary.

## Applicability

This report describes external translation-validation techniques and results. It is not an architecture recommendation for Anneal and does not claim that any cited validator can directly validate Rust-to-LLBC, LLBC-to-Lean, or any other Anneal translation.

The historical spine is:

- Pnueli, Siegel, and Singerman, TACAS 1998, which introduced translation validation as per-run validation and formulated correctness through a common semantic framework and refinement/simulation;
- Necula, PLDI 2000, which demonstrated pass-local validation for a realistic optimizing C compiler using symbolic execution and inferred transformation correspondence;
- Tristan and Leroy, POPL 2008, which formalized the distinction between an unverified translator and a **verified validator** and mechanized validator-correctness proofs in Coq for instruction scheduling;
- Lopes, Lee, Hur, Liu, and Regehr, PLDI 2021, which demonstrated a large-scale SMT-based, bounded refinement validator for LLVM IR; and
- Lee, Kim, Hur, and Lopes, CAV 2021, which develops the memory-model encoding needed for bounded validation of LLVM memory optimizations.

The papers use different source/target languages, observables, assumptions, and completeness strategies. Their individual correctness results are not interchangeable. The report extracts techniques and trust boundaries that recur across them.

## Findings

### Translation validation proves a property of one produced pair, not of all translator executions

The defining move in the TACAS 1998 formulation is to place a validation phase after each compiler run. The validator receives the source and the produced target and attempts to establish that this target correctly implements this source. That differs from a compiler-correctness theorem quantified over every source program and every successful translator result.

This distinction permits the translator to remain a complex, evolving, or heuristic implementation. Correctness is enforced at the acceptance boundary: an output for which the validator cannot establish the desired relation is not accepted as validated output.

Basis: **source** — Pnueli, Siegel, and Singerman, TACAS 1998; Necula, PLDI 2000.

### The semantic relation is the real specification of what “validated” means

Translation validation requires more than comparing syntax or outputs on tests. The original framework requires a common semantic basis for source and target plus a formal notion of correct implementation, expressed as refinement. Its proof method then establishes that the concrete target model refines the source model, using a simulation/refinement mapping between their states.

Later work makes the same point with different relations. Tristan and Leroy parameterize their verified compiler wrapper by a relation `<=` between source and target programs. In their scheduling case, the relation requires that whenever the source has well-defined semantics and terminates with an observable result, the target is also well-defined, terminates, and produces the same result. Alive2 uses LLVM-specific refinement rather than simple equality: the target may be **more defined** than the source but may not introduce behaviors forbidden by the source.

Consequently, a validator can be perfectly implemented and still prove the wrong engineering property if the chosen semantics or refinement relation omits a relevant observation. Undefined behavior, divergence, nondeterminism, memory, calls, I/O, panics, or other effects must be included or deliberately excluded by the relation rather than assumed away by the word “validation.”

Basis: **source** — TACAS 1998 refinement/simulation formulation; POPL 2008 §2.1; Alive2 §§5.1–5.3. **Derived** for the general requirement that omitted observations are outside the theorem.

### Whole-program validation is not required; pass-local validation can make the proof problem tractable

Necula's PLDI 2000 infrastructure compares the intermediate program immediately before and after compiler optimization passes. The validator therefore checks smaller transformations in the representation where the optimizer acts, rather than trying to rediscover the relationship only between source language and final machine code.

This decomposition has two advantages. First, it exposes a smaller correspondence problem. Second, a failure can be localized near the pass that introduced the discrepancy. It does not, by itself, eliminate the need for trustworthy semantics or composition: the accepted pass relation must be strong enough that validated steps compose into the desired end-to-end property.

Tristan and Leroy likewise validate individual scheduling transformations inside a verified compiler pipeline. Their formal result shows how a verified validator can be composed with an otherwise unverified pass: if the pass output is accepted by the validator, the wrapper inherits the proved preservation relation; otherwise it reports an error.

Basis: **source** — Necula, PLDI 2000; Tristan and Leroy, POPL 2008 §2.1. **Derived** for the composition precondition.

### Validators can infer correspondence instead of trusting translator-generated certificates

A validator needs some way to relate source state, target state, and transformed computations. One option is for the translator to emit witnesses. Translation validation does not require that design.

Necula describes an interface through which an optimizer could explain transformations, but the demonstrated GCC validator instead uses heuristics to recover the transformations. Tristan and Leroy use symbolic execution specialized to the transformation family. Equality-based validators have used equality saturation to expose equivalent source/target expressions. Alive2 lowers the comparison into SMT formulas over the source and target semantics.

This separation is important to the trust model: correspondence hints can improve automation without necessarily being trusted. If the validator independently checks the semantic consequence, a wrong hint should lead to rejection rather than to acceptance of an invalid translation. Whether that property actually holds is specific to the validator's implementation and proof.

Basis: **source** — Necula, PLDI 2000; Tristan and Leroy, POPL 2008; Stepp, Tate, and Lerner, CAV 2011 as contextual corroboration; Alive2, PLDI 2021. **Derived** for the witness-trust distinction.

### Symbolic execution is useful only when definedness and effects are part of the comparison

The POPL 2008 scheduling validators make a subtle point that generalizes beyond scheduling. Merely showing equal final symbolic expressions is insufficient: a transformed block might execute a new failing operation and still appear to compute the same final register mapping when both executions complete. Their validator therefore tracks both symbolic state and constraints representing operations whose semantics must be defined. For the scheduling case, the target's final symbolic state must match and its definedness obligations must not be stronger than the source's.

This is a concrete example of a broader translation-validation rule: equivalence of successful results does not establish preservation when one side can introduce new stuckness, undefined behavior, exceptional control flow, or other effects. Those outcomes belong in the semantic relation or in side conditions checked with it.

Basis: **source** — Tristan and Leroy, POPL 2008 §2.2. **Derived** for the broader statement.

### A verified validator can move the proof burden away from the translator

Tristan and Leroy model a translator `C : L1 -> L2 + Error` and a validator `V : L1 x L2 -> boolean`. They prove validator correctness in the form:

`V(c1, c2) = true -> c1 <= c2`.

A wrapper runs the original translator, then returns the target only if validation succeeds. From the validator theorem, the wrapper satisfies the compiler-correctness property even though the underlying translator implementation is not verified. The paper's instruction-scheduling validators and their correctness proofs are mechanized in Coq.

This pattern narrows, rather than eliminates, the trusted or proved base. The semantic definitions, validator implementation or extracted checker path, theorem-prover/kernel assumptions, and any unverified boundary between the proved validator and deployed executable still matter. But the complex translator can be excluded from the proof obligation when every accepted output passes the verified checker.

Basis: **source** — Tristan and Leroy, POPL 2008 §§1–2. **Derived** for the explicit trusted-base enumeration.

### Sound validators need not be complete

For general programs, deciding the desired semantic relation is undecidable. Tristan and Leroy state the resulting asymmetry directly: a validator may be proved **sound** in the acceptance direction while still rejecting a correct transformation that lies outside the validator's recognizable class. Specialization to a transformation family can recover completeness for that family, but the claim is then only as broad as the family and assumptions.

This creates a three-way operational distinction that is easy to lose in tooling:

1. **accepted** — the validator established its stated relation;
2. **rejected with a semantic counterexample/discrepancy** — evidence may show the translation violates the relation; and
3. **unknown/unsupported/resource-limited** — the validator failed to establish the relation, without establishing incorrectness.

A tool may collapse the latter two into one user-facing failure, but the technical meanings remain different.

Basis: **source** — Tristan and Leroy, POPL 2008 §2.1; Alive2, PLDI 2021. **Derived** for the three-way taxonomy.

### Bounded translation validation exchanges coverage for predictable automation

Alive2 checks LLVM source/target functions for refinement using SMT. Its design explicitly bounds resource use. Loops are unrolled only to a configured bound, and verification is also constrained by time and memory. The authors state the consequence precisely: a refinement failure triggered within the bound can be found, while one requiring more loop iterations can be missed.

Alive2 therefore demonstrates a useful but narrower claim than unbounded semantic validation. “No counterexample found” is conditional on the encoded semantics, supported feature set, solver/result handling, and bounds. This can still be highly effective in practice: the PLDI 2021 paper reports dozens of LLVM bugs found through deployment. Empirical bug-finding effectiveness and formal coverage are separate properties.

Basis: **source** — Alive2, PLDI 2021 §§1, 7, and evaluation. **Derived** for the separation between practical effectiveness and formal coverage.

### Refinement must represent language-specific undefinedness and nondeterminism

Alive2's relation is intentionally not ordinary extensional equality. LLVM optimizations may exploit undefined behavior and may make an `undef`/poison-influenced result more defined. Alive2 therefore checks a refinement relation in which target behavior is constrained relative to source behavior, models undefined behavior explicitly, and extends the relation to nondeterministic values.

This language-specific work is not peripheral. The paper notes that an LLVM validator that failed to model UB would produce impractical false alarms. The companion CAV 2021 work builds an SMT memory model specifically to make memory-optimization validation precise enough for realistic LLVM.

The general technique is to put semantic asymmetries in the validator's relation instead of forcing them into equality. The limitation is equally important: if the semantic model over-approximates, omits, or does not support a feature, the validation theorem or bounded check covers only the represented fragment.

Basis: **source** — Alive2 §§1, 5; Lee et al., CAV 2021. **Derived** for the generalization to semantic asymmetry.

### A validation result is only as strong as its checker and evidence path

The literature distinguishes several assurance levels that are often conflated:

- an unverified validator adds independent checking but can contain matching or independent bugs;
- a formally verified validator proves that **acceptance** implies the semantic relation, subject to the proof system and deployment path;
- a validator that emits a proof or certificate checked by a smaller trusted checker can move trust from the search procedure to the checker and proof format;
- a bounded validator can be sound about reported counterexamples or accepted bounded obligations while remaining intentionally incomplete outside its bound.

These dimensions are orthogonal to how sophisticated the translator is. Translation validation reduces trust in the translator only to the extent that every accepted translation is forced through a checker whose semantics and acceptance theorem cover the intended property.

Basis: **source** — TACAS 1998 (automated proof/proof-script framing); Tristan and Leroy, POPL 2008 (verified-validator theorem); Alive2, PLDI 2021 (bounded SMT validation). **Derived** for the assurance taxonomy.

## Boundaries

This report does not prove any current compiler, Charon, Aeneas, Lean, or Anneal translation correct. It does not establish that the cited techniques transfer directly to Rust, LLBC, generated Lean, or proof artifacts.

The report is not an exhaustive survey of translation validation. Important families such as proof-carrying code, proof-producing compilation, relational symbolic execution beyond the cited work, verified lifting/decompilation, translation validation for concurrent programs, and domain-specific validators have additional techniques not characterized here.

The report deliberately does not collapse translation validation into compiler testing. Differential testing and equivalence-modulo-inputs can discover compiler defects without establishing a semantic refinement theorem for each accepted output. They are adjacent validation/testing techniques, not interchangeable with the per-translation proof obligation described here.

The report also does not claim that a solver returning `unsat` is independently trustworthy. In an SMT-backed validator, assurance depends on the encoding, solver trust strategy, and treatment of `unknown`, timeouts, unsupported features, and solver bugs. A proof-producing or proof-checked SMT path changes this boundary; the cited Alive2 paper does not by itself turn the whole deployed stack into a verified validator in the POPL 2008 sense.

Finally, a pass-local validator establishes only its declared pass relation. End-to-end correctness requires that the intermediate-language semantics and per-pass relations compose with the surrounding translation stages. That composition subject is adjacent to, but distinct from, this report's inventory item.

## Evidence

**Pnueli, Siegel, Singerman — “Translation Validation.”** TACAS 1998, LNCS 1384, pp. 151–166, DOI `10.1007/BFb0054170`. The paper defines the per-run validation idea, requires a common semantic framework and refinement relation, and develops simulation/refinement mappings plus automated proof generation.

**George C. Necula — “Translation Validation for an Optimizing Compiler.”** PLDI 2000, pp. 83–94, DOI `10.1145/349299.349314`. The paper describes validation around individual GCC optimization passes, symbolic execution, and heuristic inference of transformations without requiring optimizer-produced witnesses.

**Jean-Baptiste Tristan and Xavier Leroy — “Formal Verification of Translation Validators: A Case Study on Instruction Scheduling Optimizations.”** POPL 2008, pp. 17–27, DOI `10.1145/1328438.1328444`. The report used the authors' PDF and especially §§1–2, which define verified validators, acceptance implication, incompleteness, symbolic evaluation, and definedness constraints; the validator proofs are mechanized in Coq.

**Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr — “Alive2: Bounded Translation Validation for LLVM.”** PLDI 2021, pp. 65–79, DOI `10.1145/3453483.3454030`. The report used the author preprint, especially §§1, 5, and 7 for LLVM refinement, nondeterminism/UB treatment, SMT checking, and bounded loop unrolling.

**Juneyoung Lee, Dongjoo Kim, Chung-Kil Hur, Nuno P. Lopes — “An SMT Encoding of LLVM's Memory Model for Bounded Translation Validation.”** CAV 2021, DOI `10.1007/978-3-030-81688-9_35`. The paper supplies the memory-model side of Alive2's realistic bounded validation and reports that memory semantics must be modeled precisely enough to validate LLVM memory optimizations.

`source-map.json` records stable bibliographic identifiers and the web-accessed primary or institutional sources used on 2026-09-27. `technique-matrix.json` preserves the report's cross-paper comparison in machine-readable form.

## Revalidation

The cheapest revalidation is bibliographic rather than executable because the report describes published techniques. Recheck the DOI records and primary papers if a citation, theorem statement, or scope boundary is disputed.

For a future validator design being compared with this report, answer six questions explicitly:

1. What exact source and target semantics are compared?
2. Is correctness equality, refinement, simulation, preservation of defined behavior, or another relation?
3. What correspondence evidence does the validator infer, receive, or check?
4. Is the acceptance checker unverified, formally verified, or proof/certificate checked?
5. Which features, loops, resources, or behaviors are bounded, unsupported, or over-approximated?
6. What does each outcome—accept, counterexample, reject, unsupported, timeout, unknown—logically establish?

If those answers change, the relevant comparison row in `technique-matrix.json` should be revised rather than inferring equivalence from the shared label “translation validation.”
