# SAT, pseudo-Boolean, and bitvector certificate endpoints

## Summary

DRAT/FRAT producers and elaborators can remain outside the trusted search path when a final LRAT/GRAT or pseudo-Boolean artifact is checked against the original input. The logical theorem, parser, evaluator, compiler, and executable each require their own connection. Lean 4.34.1 has proved LRAT and bitvector reflection endpoints, but its examined bv_decide path discharges checking by nativeEqTrue. CakeML source supplies stronger x64 machine-semantics endpoints with explicit installation, filesystem, and resource-limit premises.

A fresh LRAT probe rejects a reused certificate after the formula is changed to a satisfiable one. A shortened hint sequence is legitimately accepted and is not a negative control.

## Applicability

Source comparisons use the separate immutable pins in REPORT.json. This does not claim that the formats, revisions, or toolchains compose without adaptation. Execution applies only to Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, on Darwin 27 arm64; the executable reports an arm64-apple-darwin24.6.0 Release target. Binary and fixture hashes are preserved in support/observations.json. Anneal's selected Lean 4.31 was not tested.

The historical StephanGocht/VeriPB Python source and the current upstream version 3 format overview are different subjects. The current Rust implementation was not acquired or run. The report contributes to T012, T015, T016, T020, T094, P051, and P054. The companion coverage.json separates answered comparisons from open research scope. Semantic/checking endpoints and one discriminating probe are covered; formal replay cost bounds and complete runtime assurance are not.

## Findings

### Hints move work from search into replay without granting the producer authority

Basis: **normative**, **documentation**, **source** + **derived**.

The pinned DRAT README defines an ordered sequence of clause additions/deletions. An added clause must satisfy RAT using the first literal as pivot; reverse unit propagation is the special case used by AT. RAT checks each clause containing the opposite pivot through a corresponding propagation obligation. RAT additions preserve satisfiability under the specification conditions, rather than requiring every added clause to be an ordinary consequence in isolation. Deletion weakens the working formula and preserves existing satisfying assignments, so a final refutation still implies original unsatisfiability; deletion need not preserve unsatisfiability. Deletion handling has documented exceptions for unit clauses in this checker. Source/specification: [DRAT README](https://github.com/marijnheule/drat-trim/blob/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/README.md), Clause Addition Preconditions and Clause Deletion Details. DRAT-trim's C implementation was not audited.

LRAT names clauses and supplies propagation/RAT hints so a checker can replay a proposed route instead of discovering it. The inspected Lean checker distinguishes addEmpty, addRup, addRat, and deletion actions; successful completion means the empty-clause operation passes its RUP check, not merely that the array ended. Source: [CompactLRATChecker.lean](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Tactic/BVDecide/LRAT/Internal/CompactLRATChecker.lean), compactLratChecker.go (27–59).

FRAT's inspected elaborator documentation distinguishes strict checking of provided hints from falling back to no-hint reconstruction, and --full from trimming irrelevant steps. It can therefore produce a valid final LRAT proof even if an irrelevant source step or dispensable hint was defective. That is a property of elaboration, not evidence that the final checker ignored a necessary proof step. Use a fresh independent checker against the original DIMACS problem. Source: [FRAT README](https://github.com/digama0/frat/blob/aa18581497830b49a6ab6cbc9e0dc778c14885b5/README.md), elab/lratchk options. Its Rust implementation was not verified here.

GRAT's Unsat_Check theory checks RUP/RAT records and explicitly requires its RAT candidate set to be exhausted; omitted necessary candidates produce an error. verify_unsat_impl_wrapper_correct gives a separation-logic Hoare result: if the wrapper returns a non-error sum branch, verify_unsat_spec holds for the input database. The same theory exports checking code to SML_imp. The theorem is an endpoint for the modeled implementation and its representation, not a theorem about any downloaded gratchk binary. Source: [Unsat_Check.thy](https://github.com/IsaFoL/IsaFoL/blob/1475076cea603c64d3dfe70c91014a5264e0479b/GRAT/gratchk/Unsat_Check.thy), RAT candidate checks (307–331), export_code (3098 onward), wrapper correctness (3167 onward); [Dimacs_Format.thy](https://github.com/IsaFoL/IsaFoL/blob/1475076cea603c64d3dfe70c91014a5264e0479b/GRAT/gratchk/Dimacs_Format.thy) for formula representation.

No constant-time or asymptotic winner is claimed. More hints can reduce checker discovery while increasing proof volume and elaboration cost; actual Anneal measurements remain open.

### A Lean Boolean checker theorem does not select its execution policy

Basis: **source** + **execution**.

LRAT.check_sound states that success of check on the supplied certificate and CNF implies that very CNF is Unsat. Reflect.verifyCert parses certificate text before invoking LRAT.check; verifyCert_correct connects true to CNF unsatisfiability. unsat_of_verifyBVExpr_eq_true further composes bitblast soundness, AIG relabeling equivalence, and CNF equisatisfiability to the supplied BVLogicalExpr. These are stronger connections than checking an arbitrary solver-selected CNF. Sources: [Checker.lean](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Tactic/BVDecide/LRAT/Checker.lean), check/check_sound (30–47); [Reflect.lean](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Tactic/BVDecide/Reflect.lean), verifyCert and unsat_of_verifyBVExpr_eq_true (173–205).

The examined frontend LratCert.toReflectionProof invokes nativeEqTrue on verifyBVExpr, then applies the theorem above to the resulting auxiliary proof. Consequently, the existence of a proved Boolean checker does not establish that this invocation evaluates it in the logical kernel. Source: [Bitblast.lean](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean), toReflectionProof (26–46).

The package's LratControls.lean uses source clauses x and ¬x with the one-step addEmpty certificate. Native checking accepts both hints [1,2] and the shorter [1]. Root unit assignments are preloaded by DefaultFormula.ofArray, so the remaining hint can conflict with an already-recorded unit assignment; removal of a redundant hint is a legitimate acceptance. Source: [Formula/Implementation.lean](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Tactic/BVDecide/LRAT/Internal/Formula/Implementation.lean), ofArray (78–95), performRupCheck/performRupAdd (208–238).

The material negative changes the formula to x and ¬y, retaining the old certificate. The checker returns false; an independently kernel-reduced theorem proves the assignment x=true, all other variables=false satisfies the changed formula. This tests binding to the input formula and excludes an inconsistent negative case.

Final elaboration exits 0. The checker-equality theorems and sourceUnsat use explicit native_decide and report individual native axioms; changedSatWitness reports only propext. The first attempted ordinary decide fixture exits 1, leaves error-recovery sorryAx dependencies, and is retained with a .first-failed suffix. Those are failed elaborations, not accepted ordinary proofs. No definitive cause of the blocked reduction is claimed.

### Verified compilation can reach an executable model with stated premises

Basis: **source**.

CakeML's LPR array compilation theorem machine_code_sound assumes cake_lpr_run: well-formed command line/filesystem, standard streams/free file descriptor, and installed_x64 checker code. The machine semantics is included in an outcome set extended with possible resource-limit behavior. In the three-argument checking mode, nonempty output is tied to parsing the designated input file, the exact VERIFIED UNSAT output string, and unsatisfiable(interp fml). The theorem relates both the parser-selected original input and the compiled execution model. Source: [lpr_arrayProofScript.sml](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/examples/lpr_checker/array/compilation/proofs/lpr_arrayProofScript.sml), cake_lpr_run and machine_code_sound (86–118), compilation composition (14–35).

The pseudo-Boolean machine_code_sound similarly relates designated parsed formula/objective/preservation variables and printed conclusion to pbc.sem_concl, and in the extra transformation-output mode to pbc.sem_output. A parsing-only invocation is a different branch. Source: [npbc_fullProofScript.sml](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/examples/pseudo_bool/array/compilation/proofs/npbc_fullProofScript.sml), cake_pb_run/machine_code_sound (60–99); [npbcScript.sml](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/examples/pseudo_bool/npbcScript.sml) for checker development.

These source theorems were not freshly rebuilt or evaluated. They do not prove that the local host's processor, operating system, supplied binary, or file transport meets all modeled premises.

### Feasibility, contradiction, and optimality are different claims

Basis: **normative**, **source** + **derived**.

The current [VeriPB overview](https://veripb.org/overview.html), proof format version 3, distinguishes NONE (no semantic conclusion), SAT (a solution of the original input), UNSAT (a contradiction), and BOUNDS (a derived lower bound with a feasible upper-bound witness; equal bounds certify optimality). Checking a feasible assignment alone gives an upper bound for minimization, not optimality. These current-format claims derive from the observed upstream overview, not the historical Python implementation.

The historical pinned Python rules separately distinguish Solution from OriginalSolution: OriginalSolution.compute checks the stored original formula's constraints. The historical verification-result printing can emit a warning for unjustified assumptions or absent contradiction while still printing “Verification succeeded.” Acceptance must inspect semantic outcome and options instead of matching that sentence. Source: [rules.py](https://github.com/StephanGocht/VeriPB/blob/01b7b5088c8a67f1611427174501191bc5f5b365/veripb/rules.py), Solution/OriginalSolution (364–426), ObjectiveBound (437 onward), IsContradiction (486 onward); [verifier.py](https://github.com/StephanGocht/VeriPB/blob/01b7b5088c8a67f1611427174501191bc5f5b365/veripb/verifier.py), VerificationResult (55–71). This observation does not establish current Rust behavior.

### Proposed Anneal use

Basis: **derived**.

For finite bitvector obligations, retain the consumer's expression/width/signedness identity, proved bitblast-to-CNF connection, original CNF, final proof, and exact checking policy. For scheduling or finite optimization, require both feasible witness and lower-bound evidence under the consumer's original objective. Let untrusted preprocessors/elaborators produce candidate final proofs; accept through the proved endpoint and audited execution path.

## Boundaries

**Not examined:** fresh DRAT/FRAT/GRAT/CakeML builds, end-to-end Lean quotation of arbitrary source goals, cross-platform checker binaries, current VeriPB Rust source, or checker performance on Anneal obligations.

**Known limitation of the probe:** the successful checker computations use native evaluation, and their theorem dependency lists explicitly expose that policy. They are not evidence that ordinary imported-kernel reduction succeeded. No successful probe contains sorryAx.

**Unknown:** measured tradeoffs among native execution, kernel reduction, extraction, and verified compiled execution. Source endpoints identify obligations, not benchmark costs.

## Evidence

support/evidence.json records immutable primary coordinates and source hashes. Execution fixtures, outputs, binary identity, and final invocation are retained under support/. LratControls.lean.first-failed and associated output/observation files record the failed original diagnostic. Unretained source mirrors are not needed for the linked source findings. The current VeriPB webpage has an observation date and format version but no acquired immutable source identity; stronger implementation claims remain open.

## Revalidation

Run lean LratControls.lean with the recorded binary revision and compare both Boolean outputs and axiom lists. Require the satisfying-assignment proof to succeed and no sorryAx in the final run. Diff LRAT.check_sound, bitvector reflection theorems, nativeEqTrue use, and compiled CakeML theorem premises. For a real checker executable, bind its bytes to its compilation theorem and verify the original input parser/transport path separately.


*Authored by an AI agent acting on joshlf's behalf.*
