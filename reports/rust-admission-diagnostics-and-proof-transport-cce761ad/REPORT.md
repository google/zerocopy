# Rust admission diagnostics, specification adequacy and proof transport

## Summary

A usable verifier needs separate outcomes for unsupported extraction, an unproved obligation, an inconsistent or narrowed specification, and a concrete model counterexample. The cce761ad admission pipeline contains exact source/dictionary checks, required-contract comparisons and axiom audits, with source maps for selected Lean diagnostics. Ten selected admission/dictionary controls passed in this wave. They establish those rejection checks, not kernel execution or source correspondence. SMTCoq, Carcara and LFSC illustrate different certificate trust boundaries; a solver result cannot be transported to Lean merely by naming its proof format.

## Applicability

The local source subject is google/zerocopy `cce761ad53785973ec2f4a6b13715b770b340c87`, verified against Git blobs. Selected Python controls ran using Python 3 on macOS, with bytecode disabled and temporary files confined to this package's assigned scratch. Exact interpreter, platform, test selection, source hashes and output are retained.

Certificate-source comparison: SMTCoq `7b870140f2ff7e4547a7db614a305d8b2945afa3`, Carcara `20bf49c5ce31089ac83118574c888669355aaae1`, LFSC checker `5a127dbbcf9a0f822768e783dbf892ee90c435d5`. No checker/solver build, proof translation or cost benchmark was run. These are distinct implementations; this report does not equate their kernels or supported logics.

## Findings

### F1. Result categories and concrete diagnostic surface

Basis: **source**, **execution**, **derived**.

`admission.py` rejects unknown constructors, options, effects and unreviewed operation instantiations, and wraps body-audit errors with the function name. `prepare.py` rejects an extraction carrying errors even if the producing command succeeded. These failures are unsupported/invalid admission, not failed safety theorems or discovered UB.

`workspace.py:160–193` streams Lean output and maps selected Specs/ModelShapes/Models generated line numbers back to Rust source locations. It retains the child command's failing status. `inline.py` produces source maps alongside generated modules. This provides a source-oriented obligation pointer; it does not produce an executable Rust counterexample, explain every generated internal symbol or classify all failures automatically.

An implementable diagnostic record should therefore retain source/configuration identity, phase, cause class, raw status, obligation name/location and admitted assumptions. Suggested distinct classes are extraction unsupported, correspondence unavailable, proof incomplete, specification/domain mismatch, forbidden model execution, and operational failure. A solver model must be marked abstract until its path is validated against native behavior. This taxonomy is derived design, not a new implemented diagnostic frontend.

### F2. Executed admission and dictionary controls

Ten selected existing tests passed: declared abstract trait dispatch; executable impl-root coverage; missing external registration; drop/unwind rejection; unknown operations/options/attributes/configuration; UB abort not treated as recoverable unwind; exact native dictionary identity; local impl law selection; retained array usize const application; rejected non-usize/unsupported const expressions.

These controls mutate preserved extraction/metadata fixtures rather than execute invalid Rust. Expected ValueError rejection is part of their oracle. The array test also has a successful baseline, retains the original bound application and checks independent mutations of const parameter identity/type/index/value. Their passing result is evidence that these specific checks discriminate the selected malformed inputs.

The first runner attempt failed before importing tests because its relative source path was one parent too high. It made no test/source changes. That operational error is preserved separately; after correcting the path, the identical selection ran successfully. It is not evidence of an unsupported language feature.

The larger shell/kernel negative suite was read but not run. Its selected families use an expected-failure diagnostic and independent valid baseline, with controls for weakened outcome predicates, missing root coverage, unused proof axioms and impossible domains. A source expectation that these controls fail is not execution evidence that they actually did.

### F3. Required contract strength and vacuity checks

`lean/Check.lean:540–580` requires each canonical theorem to name its exact inline specification and have the expected compiled type. It also requires a separately named required proposition/witness and an arbitrary-outcome adequacy implication from the inline contract to that required proposition. Comparing arbitrary outcomes can expose a weakened postcondition or an admitted divergence/domain case even when a particular current implementation happens to satisfy a weak contract.

This check is only as strong as the independently specified required proposition and admitted source domain. It does not automatically prove that public native entries inhabit a model or that a precondition is satisfiable. Empty/impossible precondition and decoder narrowing remain separate obligations. A useful negative matrix is:

| Changed premise | Discriminating evidence needed | Observed here |
|---|---|---|
| Omitted root or impl body | Independent source/native binding roster versus requested theorem roster | Source check inspected; impl-root selected control executed |
| Wrong trait dictionary/const application | Exact original/final application mismatch | Selected controls executed |
| Weakened postcondition | Arbitrary-outcome required implication plus mutation failure | Compiled checker/shell control source inspected; kernel mutation not run |
| Impossible constructor/domain | Positive native/model entry witness independent of proof | Shell positive/domain controls inspected; broad domain coverage unmeasured |
| Unapproved proof axiom | Whole audited module/dependency graph, including unused helpers | Check.lean inspected; kernel audit execution not run |
| Hidden bad effect | Pre-transformation effect roster and failure preservation | Selected cleanup/UB/options controls executed; full lowering unmeasured |

This matrix answers what adequacy checks mean and what evidence remains; it does not count all listed controls as executed.

### F4. Parameterized model data and logical assumptions

`RustModel.lean` retains the exact provider: model type, partial mathematical decoder and optional bit decoder. Mathematical rejection is distinct from a native Option payload and from execution failure. Successful composition requires both a successful raw execution and accepted decoded value. Language-level representation initialization quantifies over the bit decoder's entire accepted domain; a mathematical decoder that rejects every value cannot shrink that physical initialization obligation.

`FunsExternal.lean:96–111` declares size and alignment inputs as exact functions returning Usize data, with a concrete u8 alignment interpretation and generic fallback. `Check.lean` checks their signatures and reachable definitions and audits allowed logical axioms, module ownership and dependencies, rejecting user proof axioms and sorry. Data parameters force proofs to retain the unknown ABI value; they do not assert arbitrary layout propositions. A global axiom stating the desired property would instead assume that property.

An axiom audit is not a decision procedure for consistency of every allowed foundational theory or every model contract. Satisfiable entry/constructor witnesses, independent domain tests and source-specific semantic interpretations remain needed. The inspected provider/required checks reduce accidental model narrowing; they do not establish arbitrary-safe-client coverage.

### F5. SMT certificate endpoints and transport premises

In [SMTCoq MainChecker.v:1053–1090](https://github.com/smtcoq/smtcoq/blob/7b870140f2ff7e4547a7db614a305d8b2945afa3/theories/checker/MainChecker.v), the checker operates on typed atom/form tables, clause state, trace and conflict index. `checker_correct` requires well-formed form/atom tables and well-typed atom interpretation before successful conflict checking implies invalidity of the starting state. `checker_ext_correct` packages root clauses/certificate: checker true, together with the interpretation well-typing premise, concludes `~ Euf_Checker.valid t_func t_atom t_form d` for every such interpretation. The represented conjunction of roots cannot hold. Its endpoint is a formula semantics theorem, not Rust safety or arbitrary SMT-LIB theory coverage. The README describes certificate import and also abduct generation; a proposed missing hypothesis is not a checked theorem of the original goal.

[Carcara's checker](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/mod.rs) requires a top-level empty clause and returns Valid or Holey. Unknown rules normally error; ignoring them marks holes, and hole/lia_generic rules also mark Holey. Crucially, Config.allowed_rules skips checks without marking a hole. External custom rule checkers add another trust path. Accepting Valid is therefore only meaningful with the exact configuration, empty allowed-rules set or justified assumptions, and external checker inventory. This is a standalone implemented checker; no Rocq/Lean theorem of this current Rust checker was examined.

[LFSC check.cpp:1292–1347](https://github.com/cvc5/LFSC/blob/5a127dbbcf9a0f822768e783dbf892ee90c435d5/src/check.cpp) checks terms under supplied signatures and prints success for a checked command. Check-assuming introduces scoped declarations. The executable accepts multiple signature/proof files, and side-condition code can be interpreted or compiled/run according to flags. Thus signatures, asserted assumptions, side-condition program and checker implementation form part of the certificate identity; the success text alone does not identify the intended unsatisfiability claim.

Transport to Lean needs a proved semantics-preserving translation of formulas, types, assumptions and rules, or a kernel-checked checker with a theorem matching that target. A Rocq theorem cannot become a Lean theorem by serialization alone. Alethe/LFSC are proof representations; independent parsing/checking, supported-theory coverage and exact binding to the original VC are separate obligations. No checking-cost measurements, Lean-native replay or universal cross-system transport theorem were produced. These remain genuine research/measurement gaps.

### F6. Effects and unsafe-source adequacy boundary

The current `forbiddenExecution` produces the undef failure tag. That tag also denotes unsupported model execution; neither total nor partial contracts admits it. Total contracts require success; partial contracts additionally permit divergence, while failures remain rejected. The source documents that Charon/Aeneas collapse source UB and panic into failure; the present fragment forbids unwind recovery, general callbacks/handlers, foreign effects, raw storage and spawned threads. It must not be extended by interpreting every failure as catchable panic.

`ADMISSION_DESIGN.md` requires coverage of every concrete execution, forbids hiding a finite UB prefix in abstract success/divergence, and requires a progress relation for total contracts. These are explicit correspondence requirements/trusted premises, not a checked whole-rustc theorem. The native/module/dictionary identity checks cannot supply them by themselves.

A future effect interface should retain separate normal return, panic unwind, abort, UB, divergence, I/O trace and spawn/detach obligations, including child-thread safety and environment resource assumptions. Compositional safety of a returned parent alone cannot justify an unchecked detached thread. This is derived interface design; no broad async or effect calculus was implemented or surveyed here.

## Boundaries

Execution covers exactly the ten Python controls. Lean kernel negative suites, native source mapping, SMT proof replay and user studies were not executed. Diagnostic source mapping is inspected, not demonstrated end to end. No solver/checker cost figures or usability measurement is claimed.

Research answered with constraints: existing failure categories, required-contract/provider/axiom mechanisms, and concrete certificate endpoint/trust contrasts. Remaining research: complete cross-prover semantic transport, effects with recovery/concurrency, and evaluated ergonomics. Future engineering: implement the suggested diagnostic/effect records and replay VCs on exact source-configurations.

## Evidence

Observed 2026-10-14. `source-evidence.json` binds local files to full revision, Git blob and SHA-256 and external checker files to immutable Git blobs/URLs. `run-admission-controls.py`, `admission-control-results.json` and `control-operational-failure.json` retain selection, interpreter/environment, source hashes, output and the harmless pre-import path failure. No upstream verifier or solver was executed in this wave.

Recorded command paths are normalized to package-relative paths or `<pinned-checkout>`; raw observation hashes and the normalization scope are retained in `observation-path-normalization.json`. Program outputs, statuses and source identities retain their observed meaning.

## Revalidation

Rerun only the retained selection against the same source pin using Python -B and package-local temporary storage. Recheck phase/error distinctions and the exact dictionary/const fixtures when formats change. For a kernel or certificate claim, execute a valid baseline and one discriminating malformed/post-weakened proof under recorded assumptions; read source expectations alone as source evidence. Pin the whole formula/signature/configuration path, including Carcara allowed rules and LFSC side-condition mode, before treating certificate acceptance as a proof.

*Authored by an AI agent acting on joshlf's behalf.*
