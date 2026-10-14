# SMT certificates, reconstruction, and binding to the consumer's goal

## Summary

SMT output earns authority through a particular checking endpoint for particular roots. A Boolean certificate checker with a soundness theorem, proof reconstruction into the host assistant, and LFSC checking against a supplied signature have different obligations. None makes an externally chosen SMT problem the consumer's original theorem automatically.

The examined Carcara configuration can allow named rules without checking them while retaining a non-holey status. The examined Lean SMT reconstruction leaves unreconstructed steps as goals, rather than silently proving them. Isabelle's examined SMT dispatcher distinguishes replay from an explicit oracle option.

## Applicability

This is a comparison of source interfaces at the six immutable revisions in REPORT.json, acquired on 2026-10-14. No combined SMTCoq/Carcara/cvc5/Lean build was run, and their separate revisions do not define a compatible software bundle. LFSC is examined as its own C++ checker and example signature; the inspected current cvc5 Alethe exporter is a separate path. The Lean SMT repository is ufmg-smite/lean-smt, with its actual Smt/Reconstruct.lean, not an assumed upstream Lean standard component.

The report contributes to R084, T011–T014, T020, T094, P051, and P054. The companion coverage.json distinguishes answered research comparisons from open subquestions. Checker/reconstruction interfaces and a critical acceptance configuration are examined; complete theory coverage, measured cost, and cross-assistant proof transport are not. Anneal implementation is a separate future obligation.

## Findings

### Certificate roots and the host theorem are separate interfaces

Basis: **source** + **derived**.

SMTCoq's MainChecker.v defines a generic trace checker that folds a step operation over a clause state and tests a selected conflicting clause. Its _checker__correct theorem assumes that every step preserves semantic validity and that the final false test is sound; acceptance then contradicts validity of the initial state. The concrete Euf_Checker.checker includes form/atom/well-typing checks and checker_correct yields invalidity of the selected root formula under the concrete interpretation.

The extracted-oriented Checker_Ext.checker_ext_correct is narrower than “a true executable result proves any SMT theorem”: it quantifies over a semantic type/function interpretation satisfying Atom.wt. The file explicitly leaves existence of a well-typed evaluation as a TODO in that section. Root formula arrays, used-root selection, atom interpretation, and host quotation must be bound to the consumer's intended hypotheses and negated goal.

The constructors named Hole and ForallInst in the proof-bearing Euf_Checker have proof arguments for their interpretation consequences. Their names do not establish an unchecked escape hatch. Source: [MainChecker.v](https://github.com/SMTCoq/smtcoq/blob/7b870140f2ff7e4547a7db614a305d8b2945afa3/theories/checker/MainChecker.v), _checker__correct (83–102), step constructors (379–396), checker (541 onward), checker_correct (725–729), Checker_Ext commentary and checker_ext_correct (893–900, 1072–1086).

A consumer can accept an independent refutation of its own encoded goal without proving the producer's search algorithm correct. It must still establish that the encoding preserves the intended semantics and that the concrete execution used the checked function.

### Alethe elaboration does not have the same acceptance contract as checking

Basis: **source**.

The inspected cvc5 Alethe printer emits assume commands for root assertions, step commands with rule/premise references, and anchor/discharge structure for subproofs. This is a proof graph with context, not an uninterpreted list of solver conclusions. Source: [alethe_printer.cpp](https://github.com/cvc5/cvc5/blob/f0bc3373ef032a3fc5006f22778aaae7b274f429/src/proof/alethe/alethe_printer.cpp), printStep and printInternal, especially lines95–117, 213–226, 269–290, 332–343.

Carcara's check_with_stats requires an empty clause in the outer context; an empty clause inside a subproof alone is insufficient. It returns Holey if the run marked holes, otherwise Valid. Unknown rules under ignore_unknown_rules and special hole/lia_generic handling can mark a run holey. Crucially, Config.allowed_rules explicitly allows named rules unchecked, and check_step returns Ok immediately for those names before collecting premises or checking discharge; these steps do not mark the proof holey. A Valid status therefore needs an acceptance policy that fixes the allowed-rule bypass set to empty and records any custom checker delegation. Source: [checker/mod.rs](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/mod.rs), Config.allowed_rules (123–130), check_with_stats (160–266), check_step (327–352 and rule dispatch below).

The elaborator's pipeline can fill holes using an external solver, localize coarse steps, uncrowd, and reorder. These are transformations to make later checking practical. Independently check its final artifact against the original consumer-selected roots, with the checking configuration fixed; neither completion of elaboration nor a more detailed proof is itself a soundness theorem. Source: [elaborator/mod.rs](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/elaborator/mod.rs), Elaborator pipeline/default and local elaboration dispatch.

This audit establishes actual Rust code paths, not a machine-checked proof of Carcara's implementation. It did not run a bypass exploit or test theory completeness.

### LFSC signatures and side-condition programs contribute semantic authority

Basis: **source** + **derived**.

LFSC can place a side-condition computation inside the domain of a dependent function argument. In check.cpp, an applied PI whose domain has RUN invokes call_run_code, requires a returned result, and compares it by definitional equality with the expected value; failure is a checking error. The preserved upstream sugar_provided.plf example declares bool_or and checks a provided computation returning tt.

That establishes the concrete interface. The logical meaning of the signature's constants and rules, soundness of side-condition programs relative to that meaning, and correctness of the C++ checking/evaluation implementation remain obligations. A type-correct proof in a producer-supplied signature does not establish that the signature expresses Anneal's goal. Sources: [check.cpp](https://github.com/cvc5/LFSC/blob/5a127dbbcf9a0f822768e783dbf892ee90c435d5/src/check.cpp), call_run_code (71 onward), PI/RUN application (641–660); [sugar_provided.plf](https://github.com/cvc5/LFSC/blob/5a127dbbcf9a0f822768e783dbf892ee90c435d5/tests/tests/sugar_provided.plf).

This does not identify current cvc5 LFSC signatures or claim that the inspected current cvc5 exporter emits LFSC.

### Reconstruction earns authority only after all host goals close

Basis: **source**.

Lean SMT's reconstructProof tries registered reconstructors. Its fallback addTrust creates a metavariable and skipStep abstracts it over the current assumptions, recording the resulting goal in skippedGoals. A trace string calls this “sorry,” but this code does not insert sorryAx; it returns an obligation. The smt tactic replaces the main goal with returned metavariables for unsat, and rejects sat/unknown. Thus “the solver returned unsat” and “the final Lean theorem is closed” are separate outcomes. The final theorem must close every returned goal and meet the consumer's axiom policy.

Reconstruct.Context.native and tactic Config.native default to false; the source documents that native reconstruction components add compiled execution to the trust boundary. Loading registered reconstructor code via evalConst is part of proof search; it need not become theorem authority when the final proof term is independently checked. Sources: [Reconstruct.lean](https://github.com/ufmg-smite/lean-smt/blob/9abdd01c13dc7ac2bac4d68d17ee661c63ed0894/Smt/Reconstruct.lean), context (30–46), reconstructor loading (61–76), skipStep/addTrust/reconstructProof (177–225), solve result interfaces (335 onward); [Tactic/Smt.lean](https://github.com/ufmg-smite/lean-smt/blob/9abdd01c13dc7ac2bac4d68d17ee661c63ed0894/Smt/Tactic/Smt.lean), evalSmtCore (near310–320).

Isabelle's SMT replay dispatcher uses replay when smt_oracle is false and a replay implementation exists; lacking replay is an error that suggests enabling the oracle. With the oracle option true it instead invokes the registered oracle, whose proposition is False for the translated context. This is a material configuration difference, not a claim that Sledgehammer normally trusts an external solver. Source: [smt_solver.ML](https://github.com/isabelle-prover/mirror-isabelle/blob/39c77411f67871f5a8f06140c588e196a9aa9ca8/src/HOL/Tools/SMT/smt_solver.ML), replay (253–263), add_solver oracle registration (273–289). The requested [Hammering towards QED survey](https://isabelle.in.tum.de/~blanchet/h4qed.pdf), §§3–4, explains the division between translation and reconstruction; the specific dispatcher claims here come from pinned source.

### Proposed Anneal interface

Basis: **derived**, not an implemented integration.

Accept a tuple consisting of the consumer's statement identity, its checked encoding, the certificate bytes, the checker identity and options, and checked evidence connecting the checker result to that statement. Reconstruction adapters should return host proof terms plus explicit unresolved obligations. Certificate elaborators may remain untrusted if their output is checked independently against the consumer's own roots. Extension APIs should require a proved rule interpretation rather than merely a new rule-name handler.

## Boundaries

**Not examined:** full SMTCoq quotation/extraction correctness, Rocq-to-Lean logical transport, cvc5 proof-producing correctness, LFSC signature adequacy for an actual Anneal obligation, Lean SMT rule-by-rule soundness, and Isabelle's full ATP/metis replay chain.

**Unknown:** checking time, peak memory, proof-size differences, supported fragment coverage on Anneal workloads, and compatibility of these separate pins. No benchmark result follows from checker size or use of hints.

**Known configuration limitation:** Carcara's allowed_rules acceptance bypass defeats the inference “Valid means every step was checked” if populated. This is an intentional source option, not an observed default exploit or a claim that all Carcara configurations bypass checking.

**Not a native policy audit:** source exposes native options, but compiler/runtime assurance and theorem dependency admission are covered separately by the pinned Lean experiments and prior kernel reports.

## Evidence

Primary endpoints are linked beside the claims. support/evidence.json records full source coordinates and retrieved-content hashes for the inspected units; full upstream source mirrors are excluded from this package. Evidence roles: SMTCoq/Carcara/LFSC/Lean SMT/Isabelle/cvc5 claims are **source**; the survey is **documentation**; the proposed Anneal interface is **derived**. No fresh SMT execution was performed.

## Revalidation

Diff the cited theorem statements, root loading, Carcara early-return/configuration logic, Lean skipped-goal plumbing, and Isabelle oracle dispatch. For a deployment, run separate positive, satisfiable-root negative, unknown-rule, and unclosed-subgoal cases under recorded options. Recheck the final host theorem's statement and dependencies. Those probes test the adapter configuration; they do not replace a quotation or checker soundness proof.


*Authored by an AI agent acting on joshlf's behalf.*
