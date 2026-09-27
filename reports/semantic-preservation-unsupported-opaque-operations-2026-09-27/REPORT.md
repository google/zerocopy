# Semantic preservation with unsupported and opaque operations

## Summary

A semantic-preservation theorem cannot make an unsupported operation disappear. It must either exclude the operation from the accepted source program, give the operation semantics that the proof carries through the translation, or state an assumption that connects the formal operation to the external implementation that will execute.

CompCert 3.18 shows the second pattern clearly. Its semantics does not define the implementation of an ordinary external function. Instead, `external_functions_sem` is an abstract relation over arguments, pre-state, observable trace, result, and post-state. The compiler proof is parametric in that relation, subject to explicit properties about result types, memory permissions, memory extensions and injections, traces, receptiveness, and determinacy. The same `external_call` interface is used across CompCert languages. This lets compiler passes preserve calls whose implementation is outside the compiler without pretending that the implementation has been verified.

CakeML makes a similar boundary explicit in a different form. FFI behavior is supplied by an oracle carried in the semantic state. The compiler can be proved correct relative to that oracle, while an end-to-end theorem additionally requires the concrete external code to obey the modeled FFI behavior and calling convention. The 2019 verified-processor result calls that external-code condition out as an assumption rather than silently absorbing it into compiler correctness.

These examples imply a useful rule for Anneal. An operation that Charon or Aeneas cannot model faithfully should not become a semantically inert placeholder merely so translation can continue. A sound pipeline can reject it; preserve it as an explicit opaque operation with a sufficiently strong relational specification; or expose an assumption whose connection to the real implementation is separately justified. Each choice changes the theorem that can honestly be claimed.

"Opaque" is therefore not synonymous with "arbitrary" or "uninterpreted." A relational external-call model may still constrain memory effects, observable events, nondeterminism, and calling behavior. Conversely, an uninterpreted pure function silently asserts far more than opacity if the real operation can mutate memory, perform I/O, diverge, or depend on the environment.

No fresh CompCert, CakeML, Rocq/Coq, or HOL execution was performed. The report uses exact source at the revisions above plus published correctness documentation.

## Applicability

This report is a technique reference for the #3720 subject "Semantic preservation with unsupported/opaque operations." It examines how two verified-compilation systems keep effects outside the verified translator visible in the semantics and theorem boundary.

The primary concrete instances are:

- CompCert 3.18 at `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`;
- CakeML source at `CakeML/cakeml@31b72d0003620a2ee8c4374caa00a483e1e450ec`;
- Lööw et al., *Verified Compilation on a Verified Processor*, PLDI 2019, DOI `10.1145/3314221.3314622`.

The report does not claim that CompCert's external-call axioms or CakeML's FFI oracle can be transplanted directly into Anneal. Their value here is structural: both systems make the boundary between verified translation and unverified environment explicit enough that later users can see what the theorem assumes.

"Unsupported" means that the translation pipeline lacks the semantic treatment needed for the intended theorem. A parser or IR may still be able to represent the syntax. "Opaque" means that the operation is intentionally not reduced to an implementation in the verified model. Opaque operations can still have precise relational specifications.

The relevant correctness direction is refinement. To use a proof about a formal opaque operation as evidence about a real operation, the real operation's behaviors must be included in the behaviors permitted by the formal model, or an equivalent simulation/refinement argument must connect them. A model that permits fewer behaviors than the real operation can make downstream proofs unsound even when the compiler proof itself is internally correct.

## Findings

### Semantic preservation is always relative to the source semantics

CompCert's whole-program theorem relates behaviors of generated assembly to behaviors admitted by the formal C semantics. At 3.18, `transf_c_program_preservation` says that every generated assembly behavior corresponds to a source behavior, modulo CompCert's `behavior_improves` relation. The stronger refinement corollary requires that the source program cannot go wrong.

This theorem shape exposes the first boundary for unsupported operations: if an operation has no faithful source semantics, a proof about the rest of the compiler cannot by itself establish the missing correspondence. The translator must reject the source, extend the semantics, or make the missing behavior an explicit premise.

This point is easy to obscure in proof pipelines whose final theorem is checked by a strong target prover. A target theorem can be completely valid while the source-to-target correspondence is incomplete. The proof assistant checks the theorem over the model it receives; it does not reconstruct source behavior that the translator omitted.

Basis: CompCert **source** and **documentation** + **derived** consequence for source-to-model pipelines.

### CompCert models external calls as relations, not as verified implementations

CompCert's `common/Events.v` defines an external-call semantics as a predicate over:

- the global symbol environment;
- argument values;
- memory before the call;
- an observable trace;
- the result value; and
- memory after the call.

For ordinary external functions, CompCert deliberately leaves this predicate abstract:

```text
Parameter external_functions_sem: String.string -> signature -> extcall_sem.
```

It assumes that each such relation satisfies `extcall_properties`. This is a useful form of opacity because the compiler proof does not need the external function's implementation, but the operation is not erased. Its arguments, result, memory transition, and observable event remain part of the program semantics.

The abstraction is also shared. `external_call` dispatches ordinary externals, unknown builtins/runtime functions, volatile operations, allocation, deallocation, copies, annotations, inline assembly, and debugging operations through one semantic interface used by all CompCert languages. Compiler passes can therefore prove that they preserve an external interaction without opening the external implementation.

Basis: CompCert **source**.

### Opaque-call axioms carry proof-relevant semantic structure

`extcall_properties` is much stronger than "the call can return anything." Among other obligations, the external-call relation must:

- return a value compatible with the call signature;
- respect equivalent symbol environments;
- not invalidate previously valid memory blocks;
- not increase maximal permissions of existing blocks;
- leave non-writable bytes unchanged;
- commute appropriately with memory extension and memory injection;
- produce a bounded one-step trace;
- be receptive to matching environmental responses; and
- be deterministic up to CompCert's trace-matching relation.

Those conditions are tailored to the simulation arguments used by the compiler. They let passes change memory representations while still relating calls before and after the pass.

The reusable lesson is not the exact list of CompCert conditions. It is that "opaque" operations need the frame and simulation laws required by the transformations around them. If a pipeline represents an unknown call with a placeholder but cannot state how that placeholder interacts with memory, aliasing, observable effects, or nondeterminism, later pass proofs have no stable semantic contract to preserve.

Basis: CompCert **source** + **derived** generalization.

### Parametric compiler correctness does not verify the external implementation

CompCert proves compiler preservation for any external-call semantics satisfying the required properties. That is a strong compiler theorem, but it intentionally leaves another obligation outside the compiler: the concrete environment that eventually implements an external function must correspond to the assumed relation.

This is the crucial distinction between **preserving an opaque operation** and **verifying the operation**. A compiler can preserve calls to `read`, a library routine, or another component while treating their semantics abstractly. The compiler theorem does not thereby prove that the operating system or library implementation meets the abstract relation.

For Anneal, the analogous design would be valid only if the report or final proof makes this boundary visible. A Rust operation may be translated to an opaque Lean relation, but a Rust-level claim then depends on a separate argument that the real operation refines that relation.

Basis: CompCert **source** + **derived** trust-boundary consequence.

### CakeML makes environmental behavior an explicit oracle

CakeML's `semantics/ffi/ffiScript.sml` stores an `oracle` in the FFI state. An FFI call supplies the operation name, oracle state, configuration bytes, and input bytes to that oracle. The result either returns a new oracle state and output bytes or terminates with an FFI outcome. Successful calls are also recorded as I/O events.

This makes external behavior a semantic input rather than hidden host behavior. Compiler correctness can quantify over an oracle or restrict it with additional invariants. The program semantics therefore says what the environment is allowed to do at each FFI boundary.

The basis-library development specializes this mechanism: `basis_ffi_oracle` interprets the standard CakeML basis operations and delegates additional external calls to a supplied extension. The source records the oracle in `basis_ffi`, and later theorems relate FFI-call sequences to the modeled file-system and command-line state.

Basis: CakeML **source**.

### End-to-end CakeML correctness exposes the concrete-FFI assumption

The PLDI 2019 verified-processor result connects CakeML-generated machine code to verified hardware. Its end-to-end theorem still carries a condition for calls to external functions. The paper states that external code must return according to CakeML's calling convention and must behave according to the modeled basis-library FFI. It describes this condition in terms of restricting the interference oracle used by the machine semantics.

That is the appropriate end-to-end treatment of an opaque boundary: the compiler theorem remains useful, but the unverified environment appears as an explicit premise. If the premise is false, the theorem does not silently become a proof about the actual execution.

For Anneal, an assumption such as "external operation `f` obeys specification `S`" is therefore a legitimate boundary when that is the intended theorem. It must remain visible in the theorem, proof package, or trust inventory; hiding it behind successful code generation would change the claimed guarantee.

Basis: published **documentation/research result** + CakeML **source**.

### Rejecting unsupported operations is a sound translation policy

A verified translator does not have to accept every source program. CompCert's public statement of semantic preservation is conditional on the compiler successfully producing target code. A compile-time error is therefore compatible with compiler correctness.

This gives an important fail-closed option for proof-oriented translators: if the translator has no adequate semantics for an operation, rejecting the program can preserve the validity of the theorem for accepted programs. Acceptance coverage and semantic soundness are different goals.

The same principle applies one layer earlier in Anneal. Charon may represent an operation that Aeneas does not model, or Aeneas may preserve enough syntax to emit a target placeholder. That representational success should not be treated as semantic support. If the intended theorem is about Rust behavior and no justified model exists, explicit rejection is safer than accepting the input under a weaker, unstated semantics.

Basis: CompCert **documentation** + **derived** application to staged verification.

### A too-narrow opaque model is more dangerous than an explicit failure

Suppose a real operation may return either `0` or `1`, but the formal model permits only `0`. A target proof may establish a postcondition by relying on the missing `1` behavior. The formal proof can be valid while the claim about the real program is false.

The safe direction is the opposite: every real behavior relevant to the theorem must be represented by the formal model. An over-approximate model may make the proof harder because it permits behaviors the real operation never exhibits, but proving a safety property for all those extra behaviors can still support the real operation once the inclusion relation is justified.

The same point applies to effects. Modeling a stateful or I/O operation as a pure uninterpreted function is not conservative merely because the function body is unknown. Purity, determinism, termination, and dependence only on explicit arguments are semantic claims. If the real operation can mutate memory, observe hidden state, perform I/O, diverge, panic, or exhibit nondeterminism, those possibilities must either appear in the model or be ruled out by a justified premise.

Basis: **derived** refinement reasoning, illustrated by the concrete CompCert and CakeML relational/oracle models.

### "Uninterpreted" and "opaque" are different design choices

An uninterpreted mathematical function usually still denotes a function: equal inputs produce equal outputs, and evaluation has no hidden state unless the state is modeled as an argument and result. That representation can be appropriate for a deterministic pure operation whose mathematical relation is intentionally unspecified.

An opaque external operation is often broader. CompCert gives it a relation over memory and traces. CakeML gives it an oracle that consumes and produces external state and may terminate execution. These representations preserve kinds of behavior that a plain uninterpreted function would erase.

A verification pipeline should therefore choose the semantic shape from the operation's contract, not from implementation convenience. "We do not inspect its body" does not determine whether the correct abstraction is an uninterpreted function, a state transformer, a nondeterministic relation, an event-producing action, a partial operation, or a rejected construct.

Basis: CompCert and CakeML **source** + **derived** distinction.

### Inline assembly is a concrete warning against weakly modeled opacity

CompCert's AST documentation explicitly warns that inline assembly can invalidate the semantic-preservation theorem. In the same source, `EF_inline_asm` is assigned an abstract semantic interface, while the actual assembly text can have machine effects beyond a simple logical annotation or declared clobber model.

This is a useful negative example. A proof can preserve the *formal placeholder* across compiler passes even when that placeholder is not a faithful model of the concrete operation that executes. The gap is not repaired by proving more compiler passes correct.

For Anneal, any use of opaque or assumed semantics needs a separate **adequacy** question: does the chosen model include the behaviors of the Rust operation that will actually execute? If that question is unanswered, the final result is conditional on the model, not an unconditional Rust theorem.

Basis: CompCert **source** + **derived** adequacy consequence.

### Unsupported behavior should remain observable in the proof pipeline

A fail-closed pipeline needs more than an internal error branch. The failure must survive orchestration strongly enough that a downstream success cannot be mistaken for full verification.

For an unsupported or opaque operation, a useful evidence record contains at least:

1. the source operation identity and source location;
2. the representation that crossed each translation boundary;
3. whether the operation was rejected, modeled, or assumed;
4. the exact semantic relation/specification if modeled;
5. the explicit premise if assumed;
6. the diagnostic or coverage evidence that proves no relevant operation was silently dropped; and
7. the proof theorem's dependence on that model or premise.

This is not merely reporting hygiene. If a translator omits a declaration or substitutes an opaque value while returning overall success, later proof checking cannot distinguish "verified complete translation" from "verified remainder after unsupported behavior disappeared."

Basis: **derived** from the theorem boundaries above and the existing Anneal/Aeneas fail-closed requirements recorded elsewhere in this corpus.

### A practical Anneal policy can separate four cases

For future Anneal design, unsupported or opaque operations can be classified into four semantic cases:

1. **Rejected.** Translation stops or the verification result is non-success. No Rust-level theorem is claimed.
2. **Modeled relationally.** The operation remains in the target with an explicit relation that covers results, state/effects, divergence/failure, and observations needed by the theorem. Adequacy of the real operation to that relation is separately justified.
3. **Assumed specification.** The proof is conditional on a named premise or trusted model. The premise appears in the trust/assumption inventory and in any user-facing statement of the result.
4. **Erased or replaced by a weaker placeholder.** This is acceptable only if a proof establishes that the erased behavior is semantically irrelevant to the claimed property. Otherwise it is a soundness gap.

The first three are ordinary verification techniques. The fourth is not automatically wrong, but it needs a theorem; "the tool did not understand the operation" is not such a theorem.

Basis: **derived** synthesis.

## Boundaries

This report is not a survey of every verified compiler, translation validator, or proof assistant. It uses CompCert and CakeML because both expose the external-effect boundary directly in their formal semantics and correctness story.

No theorem prover or compiler was executed. CompCert claims were checked against exact 3.18 source at the revision listed above and the current 3.18 manual/commented development. CakeML implementation claims were checked against exact source at the listed revision. The end-to-end FFI premise is taken from the published PLDI 2019 paper.

The report does not establish that all CompCert external-call axioms are necessary for Anneal. They are tied to CompCert's memory model and simulation proofs.

The report does not establish that CakeML's oracle is the best representation for Rust effects. It demonstrates a theorem architecture in which environmental behavior is explicit and constrained.

The report does not classify every Charon intrinsic, Aeneas builtin, opaque declaration, FFI call, assembly block, or unsupported Rust operation. Dedicated corpus reports own those concrete inventories. This report supplies the semantic-preservation pattern used to reason about them.

An over-approximate model is useful only after establishing that the real operation's relevant behaviors are included. The report does not itself prove such inclusion for any Rust operation.

A target-language axiom or uninterpreted constant can faithfully encode an assumption, but its logical consistency alone does not prove correspondence to Rust. That adequacy obligation remains external unless separately discharged.

## Evidence

**CompCert 3.18.** Repository `AbsInt/CompCert`, revision `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`.

- `VERSION`, blob `5fd2882f6f042e89ce617586ce5041f5762c1766`: identifies version 3.18.
- `common/Events.v`, blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`: event traces; `extcall_sem`; `extcall_properties`; abstract `external_functions_sem`; abstract `inline_assembly_sem`; and the shared `external_call` interface.
- `common/AST.v`, blob `007d44afdb4f3262dc147865ed82721f1494d4a4`: external-function kinds and the explicit warning that inline assembly can invalidate semantic preservation.
- `driver/Complements.v`, blob `d3974c2f7c2e5d04f2a3293fa6cfdb1215e5a217`: whole-program behavior preservation and the refinement corollary for source programs that do not go wrong.
- CompCert 3.18 commented development and manual, observed 2026-09-27: high-level statement of semantic preservation and its successful-compilation precondition.

**CakeML.** Repository `CakeML/cakeml`, revision `31b72d0003620a2ee8c4374caa00a483e1e450ec`.

- `semantics/ffi/ffiScript.sml`, blob `b40698d34360646ffb56e098e15571f99b99d9f4`: FFI oracle, oracle state, I/O events, final outcomes, and `call_FFI`.
- `basis/basis_ffiScript.sml`, blob `4b98525f4f628392a0ec8710a1d4d1394acbffe9`: basis-library FFI oracle, modeled file-system/command-line state, extension FFI boundary, and proofs connecting FFI-call sequences to modeled state.

**Published end-to-end boundary.**

- Andreas Lööw, Ramana Kumar, Yong Kiam Tan, Magnus O. Myreen, Michael Norrish, Oskar Abrahamsson, and Anthony Fox. *Verified Compilation on a Verified Processor*. PLDI 2019, pp. 1041–1053. DOI `10.1145/3314221.3314622`. The paper explicitly states the assumption that external calls obey the modeled FFI behavior and calling convention.

Evidence labeled **derived** above is a direct consequence or reusable design lesson drawn from these concrete semantics and theorem boundaries; it is not attributed to the sources as their terminology.

## Revalidation

For a future Anneal design or toolchain revision, revalidate this topic at two levels.

First, recheck the reference patterns:

1. In CompCert, inspect `common/Events.v` for `extcall_sem`, `extcall_properties`, `external_functions_sem`, `inline_assembly_sem`, and `external_call`; inspect `driver/Complements.v` for the current preservation/refinement theorem shape.
2. In CakeML, inspect `semantics/ffi/ffiScript.sml` for the current oracle and call semantics, and the basis/compiler proof layers for assumptions that connect real FFI execution to the oracle.

Second, apply the pattern to the Anneal pipeline. For every operation that is unsupported, opaque, modeled specially, or supplied by an external specification:

1. identify the Rust operation and the exact Charon representation;
2. identify the Aeneas representation or rejection path;
3. identify the generated Lean representation, if any;
4. record whether the semantics is pure, stateful, nondeterministic, effectful, partial, divergent, or environment-dependent;
5. locate the proof or premise that connects the Rust behavior to that representation;
6. verify that translation failure, warning, or assumption state cannot be dropped by orchestration;
7. confirm that the final Rust-level theorem states every undischarged premise; and
8. reject the verification result if neither a faithful model nor an explicit justified assumption exists.

A useful regression suite should include at least one case for each of the four policy classes above: rejected, relationally modeled, explicitly assumed, and intentionally erased with a proof of irrelevance. Preserve the exact source, intermediate representations, diagnostics, generated Lean, assumptions, and final theorem statement. A successful target proof alone is not the success criterion; the source-to-target semantic link is.