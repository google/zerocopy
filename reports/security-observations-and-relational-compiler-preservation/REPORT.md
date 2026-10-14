# Security observations and relational compiler preservation

## Summary

Security transfer needs a relation over observations of multiple executions. Returned-value equality can erase secret-dependent leakage even when both programs always return the same value. Primary constant-time product/simulation results and Jasmin cryptographic-security results supply concrete, differently scoped interfaces; they retain source-safety, initialization, resource and adversary premises. The original Lean specimen checks the value/trace distinction under an explicit checker-soundness premise.

## Applicability

This answers P102 through ct-verif’s USENIX2016 paper, CSF2018 constant-time-preserving simulations, Jasmin’s exact `2511.11292v1` security paper and current source `34f15840f10625bbc2cbf59b3d877e94c75bfbd9`. Constant time, observational noninterference and IND-CCA are different properties. The current source and the paper artifact are separate subjects; no upstream security compiler/prover was built or benchmarked.

The original specimen was accepted by Lean4.31.0 with recorded source/runtime identities. This is conditional logical-checking evidence. Official 4.32.2 notes report a soundness fix, and the parent independently inspected the 4.31 missing nested-inductive parameter check. No exploit was executed here. Successful or zero-axiom output alone does not establish arbitrary-producer assurance; that kernel boundary belongs to the parent’s separate report.

## Findings

### F1. Product safety fixes a leakage policy, not ordinary value correctness

Basis: primary paper.

ct-verif defines security by identical observation traces for executions agreeing on public inputs and public outputs. Leakage can include branch decisions, memory indices or variable-time instruction operands. Its output-insensitive product guards paired leakage; for safe programs, product safety implies security, and is equivalent without public-output declassification. The paper mechanizes this core while-language reduction, while the output-sensitive construction’s theorem is presented separately without that mechanization. Its tool uses LLVM/SMACK/Boogie/solver stages. [Definition1 and Theorems1–2, §§3–5, PDF pp6–8](https://www.usenix.org/system/files/conference/usenixsecurity16/sec16_paper_almeida.pdf).

Derived: the declared public/secret input and output policy is part of specification meaning. A proof of noninterference of final values does not necessarily constrain addresses, branch observations or instruction timing; a proof permitting output-sensitive leakage can intentionally reveal more than an output-insensitive policy. The product theorem’s source-safety premise must be independently established when Anneal is proving safety itself.

The inspected ct-verif repository pin `36e166781b0aa7398c12b335c7a4cd118b73568e` identifies a historical implementation/case-study wrapper and dependencies including SMACK, Boogie, Z3 and Bam. No current executable acceptance or mechanized deployment closure was inferred from that source snapshot.

### F2. Compiler preservation uses paired simulations and controlled stuttering

Basis: primary paper.

CSF2018 Theorem1 transfers constant time from safe source to compiled target under ordinary lockstep simulation and a paired constant-time simulation. Theorem4 permits multiple target steps with a strictly positive step-count function, requiring equal counts/leakage for paired source steps. Theorem6 permits stuttering under a decreasing source rank and general paired/final-state conditions. [Theorems1/4/6 and Definitions7–10, PDF pp6–10](https://members.loria.fr/VLaporte/files/CSF2018_ConstantTimePreservation.pdf).

A single-run simulation can preserve values while losing the coupling between two secret-varying runs. Additional erased or expanded instructions affect trace lengths and observations; a mere existence of some matching target prefix does not establish equal paired leakage. These theorems preserve source security toward compiled target. Inferring source security from a simplified Anneal model needs the opposite coverage/observation interface, or a stronger relation supporting both directions.

The source-safety and non-stuttering premises are substantive conditions, not consequences of the security-preservation theorem. This report does not reinterpret them as arbitrary Rust adequacy or hardware timing guarantees.

### F3. Cryptographic security adds probabilistic, interactive and initialization premises

Basis: primary paper.

Jasmin `2511.11292v1` gives an interaction-tree/RHL front-end result and equal IND-CCA advantages for source/compiled KEM experiments under the same adversary. It requires source safety and fully initialized results, sufficient fresh target stack memory and allocated nonoverflowing pairwise-disjoint pointer arguments. The paper covers25/30 passes and excludes its five back-end passes; its artifact is referenced by DOI10.5281/zenodo.17604303. [§§5.2/6.3, Theorem2; introduction limitations](https://arxiv.org/html/2511.11292v1).

Derived: this is preservation of a probabilistic security experiment, not simply a constant-time trace theorem. Adversary/oracle interfaces, randomness distributions, failure/divergence and result initialization determine its meaning. A compiler theorem preserving this experiment does not automatically permit a stronger target adversary or establish implementation safety from a safe abstraction.

The named paper artifact was not acquired here. Its exact source/binary correspondence must therefore remain separate from the current repository observations below.

### F4. Current Jasmin’s actual relation has an error-cutoff boundary

Basis: source.

At the current pin, `it_compile_prog_to_asmP:1718–1730` relates a successful compile and selected entry function to an exported assembly definition under full_pre/full_post. These include memory/stack/argument and result conditions plus print-identity hypotheses. The current source has back-end theorem scripts as well as its front end; this is a distinct scope from the older paper. [it_compiler_proof.v:1688–1730](https://github.com/jasmin-lang/jasmin/blob/34f15840f10625bbc2cbf59b3d877e94c75bfbd9/proofs/compiler/it_compiler_proof.v#L1688).

Its `wkequiv_io` definition quantifies over related inputs, then applies xrutt with **left error cutoff** and **no right cutoff**, related events/answers and the selected result relation. [relational_logic.v:222–226](https://github.com/jasmin-lang/jasmin/blob/34f15840f10625bbc2cbf59b3d877e94c75bfbd9/proofs/lang/relational_logic.v#L222). `is_error` recognizes the error side of the event sum; xrutt explicitly admits a left cutoff alternative. [event definition:71–74](https://github.com/jasmin-lang/jasmin/blob/34f15840f10625bbc2cbf59b3d877e94c75bfbd9/proofs/lang/it_sems_core_defs.v#L71), [xrutt:138–147](https://github.com/jasmin-lang/jasmin/blob/34f15840f10625bbc2cbf59b3d877e94c75bfbd9/proofs/itrees/xrutt.v#L138).

Derived consequence: the compiler endpoint does not reflect all left/source errors into target errors. A proof name containing equivalence or an ITree semantics does not remove that exception. Resource/initialization and safety premises must exclude the relevant cutoffs before applying a stronger security argument. No built assumption closure or current end-to-end IND-CCA theorem was replayed here.

### F5. An original kernel specimen distinguishes value and trace transfer

Basis: original source + execution, conditional on the checking boundary above.

`SecurityWitness.lean` defines a secret Boolean input, no public input and constant returned value zero. The safe model emits an empty leakage trace; the source emits the secret Boolean. `values_agree` holds for every input, `model_constant_time` holds, and `source_not_constant_time` exhibits distinct false/true traces. The universal implication from value equality and model constant time to source constant time is therefore refuted.

Two further endpoints show exact per-input trace equality transfers this deterministic constant-time property in either direction. Their printed axiom lists are empty; the counterexample endpoints use propext. The final process exits zero. Initial ordinary tactic rejection is preserved separately; no admitted recovery declaration is treated as accepted evidence.

The specimen is a logical counterexample with one-bit traces. It performs no timing measurement and does not model a CPU/cache, speculative execution, Rust optimizer or real secret-bearing library. Its mathematical point is the missing observation relation; it does not need a native timing experiment to demonstrate that implication’s failure.

### F6. A property-specific Anneal interface

Basis: derived independently from the quantifiers and specimen.

For source security from model security, cover every relevant pair of source executions from independently low-equivalent inputs. Match them with model executions whose public input/output/declassification conditions correspond. Require each source observation to be the same fixed interpretation of its model observation. Universal security of those model pairs then yields equality of the interpreted source observations. An existential favorable scheduler/input choice cannot omit an insecure source pair.

For preservation toward machine code, reverse the execution coverage and observation map as required. Non-bijective abstractions, nondeterminism and different adversary capabilities require explicit pair/coupling conditions; ordinary may-refinement and successful output equality are insufficient. Keep UB/failure reflection separate so a safe-source assumption does not circularly justify the translation being used to establish safety.

The certificate should bind the leakage/event model, low-equivalence relation, public outputs/declassification, semantic program and entry domain, failure/progress policy, environment/adversary, randomness and assumptions. Hardware timing or speculative/cache security requires an additional model/implementation contract. Adding a security feature is future engineering only after this independently selected property interface is justified.

## Boundaries

Answered: concrete product and compiler-preservation mechanisms, their exact directions/premises, current conditional source relation and an executed logical value/trace discriminator. Unexamined: upstream proof replay/current artifact closure, actual cryptographic implementation, hardware/speculative timing correspondence and a Rust→model two-run adequacy theorem. No numerical proof-cost/security claim is made.

The paper’s source-safety premises and current left error cutoff cannot provide arbitrary unsafe source safety. The 4.31 kernel finding qualifies observed acceptance independently of the abstract mathematical proposition.

## Evidence

`REPORT.json` identifies primary papers/current repositories and the original Lean specimen. `source-identities.json` preserves paths/hashes; `SecurityWitness.lean`, final/initial logs and `lean-check.json` preserve command, version, source, kernel/shared-library/Init identity and statuses. [Official4.32.2 release](https://github.com/leanprover/lean4/releases/tag/v4.32.2) points to the soundness-fix notes; detailed 4.31 source affectedness is parent-reviewed evidence, with no exploit observation here. Acquisition date:2026-10-14.

## Revalidation

Reinspect the selected observation, source-safety, input/adversary and cutoff definitions before changing compiler/property scope. Replay upstream endpoint assumptions and bind its actual artifact when adopting it. Re-run the original specimen with an independently justified checker subject, retaining logs and dependencies; no toolchain upgrade or exploit is required to reproduce the recorded conditional observation. A hardware or Rust assurance claim additionally needs its own two-run source/observation adequacy bridge.

*Authored by an AI agent acting on joshlf's behalf.*
