<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Inductive Inference Impossibility, Sound Over-Approximation versus Semantic Completeness, and Crate-Monotonicity Laws in Semantic Verification Models

## Summary

Across the 16-candidate evolution (`Candidate 001`–`016`) of a four-primitive semantic verification framework (`Language`, `Tool`, `BehaviorCodec`, `Spec`) and four adversarial falsification suites (`PENTEST-1`–`10`, `PENTEST-R2-1`–`10`, `PENTEST-R3-1`–`10`, `PENTEST-R4-1`–`10`), candidate adequacy predicates repeatedly oscillated between two dual failure modes:

- **Category A1 Soundness Bypasses:** Certification of defective tools, specifications, or programs, including $N$-entry syntactic allowlist compilers (`PENTEST-3A`, `PENTEST-R2-4A`), Trojan horse compilers that miscompile uninspected programs (`PENTEST-2`), $k$-point rubber-stamp functional specifications (`PENTEST-5`, `PENTEST-R2-5`, `PENTEST-R3-5B`, `PENTEST-R4-9`), inverted compilers that accept only defective spike programs (`PENTEST-R3-8`, `PENTEST-R3-9B`), and intrinsic well-behavedness predicates that certify constant-zero or constant-42 return bugs and impulse spikes (`PENTEST-R4-1A`, `PENTEST-R4-1B`, `PENTEST-R4-7`).
- **Category A2 Honest-Tool Lockouts:** Rejection of legitimate compilers, static analyzers, specifications, or programs, including multi-program compilers (`PENTEST-3B`, `PENTEST-R2-4B`), infinite program families (`PENTEST-R3-2B`), boolean and parity specifications (`PENTEST-R3-5A`), syntactic type and borrow checkers that reject dead-branch ill-typed ASTs (`PENTEST-R3-2A`, `PENTEST-R4-3A`, `PENTEST-R4-3B`), multi-pass compiler pipelines on nondeterministic intermediate languages (`PENTEST-R3-10`), and honest constant initializers in crates whose other functions happen to output `1` and `26` (`PENTEST-R4-1C`).

This report proves and mechanizes in standalone Lean 4 ([support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), 2,016 lines, zero `sorry`, zero custom axioms) that this oscillation is governed by three mathematical impossibility laws and resolved by a single positive characterization theorem:

1. **The Gold–Angluin Finite-Witness and $k$-Point Evasion Impossibility Theorem (`GoldAngluinFiniteWitnessImpossibility_Prog`, `FiniteGoodSpecsLocksOutInfiniteFamily`, `GoldAngluinFiniteWitnessImpossibility_Spec`, `PointSeparatingSpecLocksOutBooleanAndParitySpecs`):** By the inductive inference impossibility principles of Gold (1967), Blum and Blum (1975), Angluin (1980), and Weyuker (1983, 1986), no finite positive program suite $W_+ = \{p_1, \dots, p_N\}$ can force a tool to accept any program $p \notin W_+$ (`allowlistCompiler`), and no finite specification list `goodSpecs` can cover an infinite program family (`L_addK`). Dually, on the query axis, no finite query suite $Q_k = \{q_1, \dots, q_k\}$ can distinguish the true specification $v = f_{\text{true}}(q)$ from the single-valued functional specification `depthKFunctionalSpec Q_k f_true c_bad` ($v = \text{if } q \in Q_k \text{ then } f_{\text{true}}(q) \text{ else } c_{\text{bad}}$). Attempting to block $k$-point evasion by requiring input-injective specifications (`PointSeparatingSpec`) violates the Pigeonhole Principle and locks out `paritySpec` and every boolean-valued specification on $\ge 3$ queries.
2. **The Rice–Cousot Asymmetry Theorem (`DeadBranchSyntacticCheckerLockout`, `SemanticallyClosedNonComposable`, `UnlabeledIntrinsicWellBehavedImpossibility`):** By Rice's Theorem (1953), Morris's thesis that types are syntactic disciplines rather than extensional sets (1973), and Cousot and Cousot's Abstract Interpretation framework (1977), sound static analysis is an *over-approximation* of dynamic safety ($D_{\text{syn}} \subseteq \text{Accepted}(T) \subseteq \text{SemSafe}(L, S)$), never an exact semantic partition. Requiring semantic acceptance closure (`Tool.SemanticallyClosedOn`) or universal acceptance of dynamically well-behaved programs (`Language.WellBehavedProgOn`) locks out every syntactic type or borrow checker that rejects `if false then type_error else e` while accepting `e`. Furthermore, `Tool.SemanticallyClosedOn` is **not closed under vertical pipeline composition** (`Tool.comp`) when an early pass breaks nondeterministic symmetry differently on equivalent ASTs (`.nondet12` vs. `.nondet12_alt`). Finally, correctness is an extrinsic relation between a program and its specification, never an intrinsic property of unlabeled dynamic traces (`L.sem`): any intrinsic predicate that accepts total, deterministic, query-sensitive functions must accept `.buggySpike` ($q \mapsto \text{if } q = 0 \text{ then } 1 \text{ else } 0$).
3. **The Crate-Monotonicity Law (`WellBehavedProgOn_Violates_CrateMonotonicity_BothDirections`, `TotalWellBehavedDomainOn_Typed2_False_Typed3_True`):** A program-level semantic classification $\mathcal{J}(L, \text{pre}, p)$ satisfies *Crate Monotonicity (Local Modularity)* if adding or removing unrelated functions in the crate (`SameDomainCrateExtension L L'`) leaves $\mathcal{J}(L, \text{pre}, p)$ invariant. `Candidate 016`'s `WellBehavedProgOn` and `TotalWellBehavedDomainOn` combine magic-number range filters (`CanonicalConstInit`: $1$ and $26$) with universal quantifiers over all programs $b : L.\text{Prog}$, violating Crate Monotonicity in **both directions**: adding an unrelated function `.add1` ($q + 1$) promotes a buggy constant function `.badConst42` ($42$) from ill-behaved to well-behaved; adding `.add27` and `.add77` promotes `.bad0` ($0$) to well-behaved; adding `.add20` ($q + 20$, which outputs $26$ at $q = 6$) demotes an honest constant initializer `.initZero` ($0$) from well-behaved to ill-behaved; and adding a third well-typed function `.wellTypedAddThree` flips `TotalWellBehavedDomainOn` from `False` to `True`, locking out syntactic type checkers on $\ge 3$-function crates.
4. **The Positive Characterization Theorem (`ExplicitDomainContract_CrateMonotonic`, `ExplicitDomainContract_Admits_SyntacticTypeCheckers`, `ExplicitDomainContract_Separates_ConstInit_From_BuggyConst_And_Spike`, `ExplicitDomainContract_VerticalComposition`):** Pairing an explicit syntactic acceptance domain `AcceptedDom : L.Prog → Prop` with an extrinsic per-program specification family `specOf : (p : L.Prog) → AcceptedDom p → L.Query → SemObs → Prop` (`ExplicitDomainContract` and `Tool.SoundAndCompleteOnExplicitDomain`) is 100% crate-monotonic, admits syntactic type checkers on crates of arbitrary size, certifies honest constant initializers while refuting `.bad0`, `.badConst42`, and `.buggySpike`, and is strictly closed under vertical pipeline composition `Tool.comp` across arbitrary (including nondeterministic) intermediate languages.

## Applicability

The findings in this report apply to the subjects recorded in `REPORT.json`:

1. **Lean 4 theorem prover** at `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), invoked with `-DElab.async=false -Ddebug.skipKernelTC=false` over standalone modules.
2. **Inductive inference and test-data adequacy foundations:**
   - E. Mark Gold (1967), *Language Identification in the Limit*, *Information and Control* 10(5), pp. 447–474 (`doi:10.1016/S0019-9958(67)91165-5`),
   - Dana Angluin (1980), *Inductive Inference of Formal Languages from Positive Data*, *Information and Control* 45(2), pp. 117–135 (`doi:10.1016/S0019-9958(80)90285-5`),
   - Lenore Blum & Manuel Blum (1975), *Toward a Mathematical Theory of Inductive Inference*, *Information and Control* 28(2), pp. 125–155 (`doi:10.1016/S0019-9958(75)90261-2`),
   - Elaine J. Weyuker (1983), *Assessing Test Data Adequacy through Program Inference*, *ACM TOPLAS* 5(4), pp. 641–655 (`doi:10.1145/69575.357231`), and
   - Elaine J. Weyuker (1986), *Axiomatizing Software Test Data Adequacy*, *IEEE TSE* SE-12(12), pp. 1128–1138 (`doi:10.1109/TSE.1986.6313008`).
3. **Computability, abstract interpretation, and modular type-discipline foundations:**
   - Henry Gordon Rice (1953), *Classes of Recursively Enumerable Sets and Their Decision Problems*, *Transactions of the American Mathematical Society* 74(2), pp. 358–366 (`doi:10.2307/1990888`),
   - Patrick Cousot & Radhia Cousot (1977), *Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints*, *POPL 1977*, pp. 238–252 (`doi:10.1145/512950.512973`),
   - Peter J. Landin (1966), *The Next 700 Programming Languages*, *Communications of the ACM* 9(3), pp. 157–166 (`doi:10.1145/365230.365257`), and
   - James H. Morris Jr. (1973), *Types are Not Sets*, *POPL 1973*, pp. 120–124 (`doi:10.1145/512927.512938`).

- **Environments and Formalisms:** Applies to mechanized semantic verification frameworks, compiler correctness contracts, and static-analysis adequacy specifications in dependent type theory (Lean 4.34.1) built over the four-primitive architecture (`Language`, `Tool`, `BehaviorCodec`, `Spec`) using demonic refinement (`Partial.le` / `Behavior.le`) and miracle-free compilation (`ProductiveCompiles`).
- **Assumptions:**
  1. Program execution is modeled as a query-indexed partial relation `Behavior Query Out := Query → Partial (Out → Prop)` where `M ≤ N` (`N.defined → M.defined ∧ M.val ≤ N.val`) captures both undefined-behavior elimination (domain widening) and nondeterminism resolution (output-set narrowing).
  2. Tools (`Tool L_src L_tgt := L_src.Prog → Partial L_tgt.Prog`) are partial compilers or static verifiers whose definedness `(tool p).defined` denotes static acceptance.
  3. Crate extensions (`CrateExtension L L'` / `SameDomainCrateExtension L L'`) embed a sub-crate `L.Prog` injectively into `L'.Prog` while preserving `Query`, `Out`, `obs`, and per-function dynamic semantics `L'.sem (embedProg p) = L.sem p`.
- **Exclusions:**
  1. Does not claim that finite test suites have zero practical bug-finding utility; rather, it proves that within deductive adequacy predicates, finite positive witness lists and finite query suites cannot prevent allowlist or $k$-point piecewise-constant evasion on uninspected inputs.
  2. Does not address probabilistic PAC-learning bounds or complexity-theoretic cryptographic obfuscation; all impossibility constructions are unconditional information-theoretic and recursion-theoretic results constructive in standard Lean 4.

## Findings

### F-01: Program-Axis Gold–Angluin Finite-Witness Evasion and Infinite-Family Lockout

`Basis: normative + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:** For any source and target languages `L_src`, `L_tgt`, codec `c`, base compiler `base`, finite positive program list `W_pos : List L_src.Prog`, and disjoint negative canary list `W_neg : List L_src.Prog`, the syntactic allowlist tool `allowlistCompiler base W_pos` (`defined := p ∈ W_pos ∧ (base p).defined`) accepts all `p ∈ W_pos`, rejects all `b ∈ W_neg`, and satisfies `ProductiveCompiles` on all accepted programs, while rejecting every uninspected valid program `p ∉ W_pos` (`PENTEST-3A/3B`, `PENTEST-R2-4A/B`). Furthermore, on the infinite program family `L_addK` (`Prog := Nat`, where program `k` computes `q + k`), for every finite list `goodSpecs` of tight specifications (`sp.2 0 v → v = sp.1`), the program `p_new = maxSpecProg goodSpecs + 1` is accepted and productively compiled by `honestAddKCompiler`, yet satisfies no specification in `goodSpecs` (`PENTEST-R3-2B`).
- **Mathematical Derivation:** In Gold's (1967) and Angluin's (1980) model of language identification from positive data, any finite sample $W_+ \subset L^*$ is contained in the minimal finite hypothesis $H_{\min} = W_+$. When a verification framework requires universal soundness only over accepted programs ($\forall p,\ \text{Accepted}(T, p) \to \text{Sound}(T, p)$) and existential/finite acceptance only on $W_+$, the indicator restriction $T|_{W_+}$ is a valid sub-partial-function of $T$. Conversely, if the framework restricts `Accepted(T)` to programs covered by a finite specification list `goodSpecs`, any compiler on an infinite language `L_addK` is locked out on $p_{\text{new}} = 1 + \max_{(k, S) \in \text{goodSpecs}} k$.
- **Evidence Location:** [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), lines 397–486 (`allowlistCompiler`, `GoldAngluinFiniteWitnessImpossibility_Prog`, `L_addK`, `honestAddKCompiler`, `maxSpecProg`, `le_maxSpecProg`, `FiniteGoodSpecsLocksOutInfiniteFamily`) and lines 1756–1801 (`trojanAddKCompiler`, `PENTEST_2_3AB_R2_4AB_AllowlistAndTrojanSuite`).
- **Falsification Condition:** Exhibiting a finite positive witness list `W_pos` on a language with `p ∉ W_pos` such that `allowlistCompiler base W_pos` fails positive acceptance on `W_pos`, fails negative rejection on `W_neg` ($W_{\text{neg}} \cap W_{\text{pos}} = \emptyset$), or fails `ProductiveCompiles` on an accepted program.

### F-02: Query-Axis $k$-Point Functional Specification Evasion and Pigeonhole Lockout of `PointSeparatingSpec`

`Basis: normative + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:** Dually on the query axis, for any finite query suite `Q_k : List Query`, true function `f_true : Query → SemObs`, and fallback constant `c_bad : SemObs`, the piecewise functional specification `depthKFunctionalSpec Q_k f_true c_bad` ($v = \text{if } q \in Q_k \text{ then } f_{\text{true}}(q) \text{ else } c_{\text{bad}}$) satisfies `FunctionalSpec`, `PointwiseRefutable`, and $k$-point diagonal `ViolatesAtQuerySuite` (`PENTEST-5`, `PENTEST-R2-5`, `PENTEST-R3-5B`, `PENTEST-R4-9`), yet certifies the defective program in `L_buggyOutsideSuite Q_k f_true c_bad` that outputs `c_bad` on every uninspected query `q ∉ Q_k`. Attempting to outlaw piecewise-constant fallback specifications by requiring `PointSeparatingSpec` (input-injective output fibers: $q_1 \neq q_2 \to \neg (\text{obsPost}(q_1, v) \wedge \text{obsPost}(q_2, v))$) rejects `paritySpec` ($v = q \bmod 2$) and, by the Pigeonhole Principle, rejects **every** boolean-valued specification (`SemObs = Bool`) on any domain with $\ge 3$ distinct valid queries (`PENTEST-R3-5A`).
- **Mathematical Derivation:** As shown by Weyuker (1983, 1986) and Blum and Blum (1975), a finite input-output sample $\{(q_i, f_{\text{true}}(q_i))\}_{i=1}^k$ identifies a function only on $Q_k$; the interpolating function $f_{Q_k, c_{\text{bad}}}$ is total and single-valued (`FunctionalSpec`) everywhere, so functional single-valuedness is orthogonal to off-suite accuracy. Requiring injectivity across queries (`PointSeparatingSpec`) forces $|\text{Query}_{\text{pre}}| \le |\text{SemObs}|$, which is impossible whenever $|\text{SemObs}| < |\text{Query}_{\text{pre}}|$ (e.g., $|\text{Bool}| = 2 < 3$).
- **Evidence Location:** [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), lines 488–594 (`depthKFunctionalSpec`, `L_buggyOutsideSuite`, `GoldAngluinFiniteWitnessImpossibility_Spec`, `PointSeparatingSpecLocksOutBooleanAndParitySpecs`) and lines 1803–1860 (`L_depth3_evasion`, `PENTEST_5_R2_5_R3_5B_R4_9_DepthKSpecSuite`).
- **Falsification Condition:** Constructing a boolean specification `obsPost : L.Query → Bool → Prop` on a domain with 3 distinct valid queries `q₁, q₂, q₃` that both admits a `VerifiedSpine` program and satisfies `PointSeparatingSpec`.

### F-03: Rice–Cousot Asymmetry and Dead-Branch Syntactic Checker Lockout

`Basis: normative + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:** For any language `L` and static verification tool or compiler `tool : Tool L L_tgt`, if `p_good` and `p_deadBranchIllTyped` (`if false then type_error else p_good`) have identical dynamic `Produces` semantics on `pre`, then any syntactic checker that accepts `p_good` and rejects `p_deadBranchIllTyped` violates both `Tool.SemanticallyClosedOn pre tool` (`Candidate 008`, `PENTEST-R3-2A`) and universal acceptance of `Language.WellBehavedProgOn` (`Candidate 012`–`016`, `PENTEST-R4-3A/B`).
- **Mathematical Derivation:** By Rice's Theorem (1953) and Cousot and Cousot's (1977) Galois connection framework for Abstract Interpretation, any computable static type system or borrow checker (Morris 1973; Landin 1966) computes a decidable syntactic sub-domain $D_{\text{syn}} \subsetneq \text{SemSafe}(L, S)$. Because `p_good` and `p_deadBranchIllTyped` lie in the same dynamic equivalence class $[p_{\text{good}}]_{\equiv_{\text{pre}}}$ of `L.Produces` on `pre`, any purely semantic predicate (`SemanticallyClosedOn` or `WellBehavedProgOn`) is invariant across $[p_{\text{good}}]_{\equiv_{\text{pre}}}$ and therefore cannot separate `p_good` from `p_deadBranchIllTyped`.
- **Evidence Location:** [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), lines 609–732 (`Tool.SemanticallyClosedOn`, `Language.WellBehavedProgOn`, `Language.TotalWellBehavedDomainOn`, `DeadBranchSyntacticCheckerLockout`).
- **Falsification Condition:** Exhibiting a tool `tool` that accepts `p_good`, rejects a dynamically equivalent `p_deadBranchIllTyped`, and satisfies `Tool.SemanticallyClosedOn pre tool`.

### F-04: Non-Closure of `SemanticallyClosedOn` Under Vertical Pipeline Composition (`Tool.comp`)

`Basis: normative + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:** `Tool.SemanticallyClosedOn` is **not closed under vertical pipeline composition** (`Tool.comp`). On `L_nondet_pipe` (`PENTEST-R3-10`), `stage1SymBreak` satisfies `Tool.SemanticallyClosedOn` and `ProductiveCompiles` on all accepted programs, and `stage2Filter` satisfies `Tool.SemanticallyClosedOn` and `ProductiveCompiles` on all accepted programs, and `Tool.ChainedSuiteAccepted stage1SymBreak stage2Filter [.det1, .nondet12]` holds, yet `Tool.comp stage1SymBreak stage2Filter` violates `Tool.SemanticallyClosedOn` because it accepts `.nondet12` and rejects the dynamically identical `.nondet12_alt`.
- **Mathematical Derivation:** Demonic refinement (`Compiles`) permits a compiler pass $T_1 : L_1 \to L_2$ to narrow nondeterministic choices differently on syntactically distinct but semantically equivalent source ASTs: $p_1 = (q + 1) \sqcup (q + 2)$ (`nondet12`) is lowered to $p'_1 = q + 1$ (`det1`), while $p_2 = (q + 2) \sqcup (q + 1)$ (`nondet12_alt`) is lowered to $p'_2 = q + 2$ (`det2`). Because $p'_1 \not\equiv p'_2$ in $L_2$, a downstream pass $T_2 : L_2 \to L_3$ can be semantically closed on $L_2$ while accepting $p'_1$ and rejecting $p'_2$. Consequently, $(T_1 \circ T_2)(p_1)$ is defined while $(T_1 \circ T_2)(p_2)$ is undefined, even though $p_1 \equiv p_2$ in $L_1$.
- **Evidence Location:** [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), lines 734–868 (`NondetPipeProg`, `L_nondet_pipe`, `stage1SymBreak`, `stage2Filter`, `SemanticallyClosedNonComposable`).
- **Falsification Condition:** Proving that for all $L_1, L_2, L_3$ and tools $T_1, T_2$ satisfying `SemanticallyClosedOn` and `ProductiveCompiles`, `Tool.comp T_1 T_2` satisfies `SemanticallyClosedOn`.

### F-05: Impossibility of Unlabeled Intrinsic Well-Behavedness (`WellBehavedProgOn` and `.buggySpike`)

`Basis: normative + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:** Correctness is an extrinsic relational property between a program and its specification, never an intrinsic property of unlabeled dynamic traces (`L.sem`). Any intrinsic predicate `WellBehavedProgOn` that accepts productive, deterministic, query-sensitive programs must classify `.buggySpike` ($q \mapsto \text{if } q = 0 \text{ then } 1 \text{ else } 0$) as well-behaved (`PENTEST-R4-7`), even though `.buggySpike` violates both $v = q + 1$ (at $q = 1$) and $v = q + 2$ (at $q = 0$). Moreover, without an extrinsic specification, `SemanticallyClosedOn` and `ProductiveCompiles` certify the inverted compiler `invertedSpikeCompiler` (`PENTEST-R3-8`, `PENTEST-R3-9B`) that accepts only `.buggySpike` and rejects all honest programs `.addOne` and `.addTwo`.
- **Mathematical Derivation:** From an unlabeled semantics $L.\text{sem} : \text{Prog} \to \text{Query} \to \text{Partial}(\text{Out} \to \text{Prop})$, the function $f_{\text{spike}}(q) = \mathbf{1}_{q=0}$ is total, deterministic, and non-constant ($f_{\text{spike}}(0) = 1 \neq 0 = f_{\text{spike}}(1)$). Because no intrinsic property of $f_{\text{spike}}$ distinguishes "intended indicator function $\mathbf{1}_{q=0}$" from "off-by-one/zeroing bug in $q + 1$", any unlabeled intrinsic classifier either accepts `.buggySpike` (Category A1 bypass) or rejects legitimate indicator functions (Category A2 lockout).
- **Evidence Location:** [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), lines 870–936 (`SpikeSuiteProg`, `L_spike_suite`, `UnlabeledIntrinsicWellBehavedImpossibility`) and lines 1862–1909 (`invertedSpikeCompiler`, `PENTEST_R3_8_R3_9B_InvertedBuggyCompiler`).
- **Falsification Condition:** Showing that `.buggySpike` fails `L_spike_suite.WellBehavedProgOn (fun q => q < 100)` or that `L_spike_suite.TotalWellBehavedDomainOn (fun q => q < 100)` fails.

### F-06: Bidirectional Violation of Crate Monotonicity by AST-Global Quantifiers (`PENTEST-R4-1A/B/C`)

`Basis: normative + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:** `Language.WellBehavedProgOn` (`Candidate 016`) violates `CrateMonotonicProgJudgment` in **both directions**:
  1. **Upward Non-Monotonicity (`PENTEST-R4-1B` & `PENTEST-R4-1A`):** In the 2-program sub-crate `L_sub_bad42` (`{.badConst42, .ubCrash}`), `.badConst42` ($q \mapsto 42$) is ill-behaved (`¬ WellBehavedProgOn`). Embedding `L_sub_bad42` into `L_add1_bad42_ub` by adding the unrelated function `.add1` ($q \mapsto q + 1$) flips `.badConst42` from **ill-behaved to well-behaved**! Similarly, in `L_add27_add77_bad0_ub` (`{.add27, .add77, .bad0, .ubCrash}`), the presence of `.add27` ($q + 27$) and `.add77` ($q + 77$) causes `.bad0` ($q \mapsto 0$) to satisfy `WellBehavedProgOn` and `TotalWellBehavedDomainOn`, locking out `honestAdd27Add77Compiler` (`PENTEST-R4-1A`, `PENTEST-R4-3B`).
  2. **Downward Non-Monotonicity (`PENTEST-R4-1C`):** In the 3-program honest crate `L_honest_crate_add1` (`{.add1, .initZero, .oobPanic}`), the honest constant initializer `.initZero` ($q \mapsto 0$) satisfies `WellBehavedProgOn` on `q < 16`. Embedding `L_honest_crate_add1` into `L_honest_crate_add1_add20` by adding the unrelated honest function `.add20` ($q \mapsto q + 20$, which outputs $26$ at $q = 6 < 16$) flips `.initZero` from **well-behaved to ill-behaved**!
- **Mathematical Derivation:** `WellBehavedProgOn` attempts to infer whether a constant function $p$ ($q \mapsto c$) is an intentional constant initializer by quantifying existentially over a reference program $p' : L.\text{Prog}$ and universally over all query-sensitive programs $b : L.\text{Prog}$, guarded by `CanonicalConstInit.validMultiShift` ($\neg \text{range}(p')(1) \wedge \neg \text{range}(p')(26) \wedge \neg \text{range}(b)(1)$). Because $\exists p' \in L.\text{Prog}$ is existential (monotone under crate growth) while $\forall b \in L.\text{Prog}$ is universal (antitone under crate growth), their combination is neither monotone nor antitone under `SameDomainCrateExtension`: adding `.add1` supplies the missing existential witness $p'$ for `.badConst42`, while adding `.add20` introduces a universal counterexample $b$ whose range hits the magic number $26$ when paired with `.add1` (whose range hits $1$).
- **Evidence Location:** [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), lines 975–1301 (`CrateExtension`, `SameDomainCrateExtension`, `CrateMonotonicProgJudgment`, `L_sub_bad42`, `L_add1_bad42_ub`, `L_honest_crate_add1`, `L_honest_crate_add1_add20`, `L_add27_add77_bad0_ub`, `WellBehavedProgOn_Violates_CrateMonotonicity_BothDirections`) and lines 1911–1934 (`honestAdd27Add77Compiler`, `PENTEST_R4_1A_3B_HonestCompilerLockout`).
- **Falsification Condition:** Proving `CrateMonotonicProgJudgment (fun L pre p => L.WellBehavedProgOn pre p)`.

### F-07: Crate-Size Threshold Lockout of Syntactic Type Checkers (`PENTEST-R4-3A`)

`Basis: normative + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:** `Language.TotalWellBehavedDomainOn` (`Candidate 016`) exhibits a phase transition at 3 distinct well-typed functions: on the 2-function typed crate `L_typed2` (`{.wellTypedAddOne, .wellTypedAddTwo, .deadBranchIllTyped, .liveNullDeref}`), `TotalWellBehavedDomainOn (fun q => q < 100)` is `False`; on the 3-function crate extension `L_typed3` (adding `.wellTypedAddThree`), `TotalWellBehavedDomainOn (fun q => q < 100)` becomes `True`, forcing any compliant compiler to accept `.deadBranchIllTyped` and locking out `honestSyntacticTypeCompiler3`.
- **Mathematical Derivation:** The fourth disjunct of `TotalWellBehavedDomainOn` tests whether `L.Prog` contains three pairwise-separable `WellBehavedProgOn` programs $p_1, p_2, p_3$. In `L_typed2`, `.wellTypedAddOne` and `.deadBranchIllTyped` have identical semantics ($q + 1$), so only two distinct dynamic behaviors ($q + 1$ and $q + 2$) exist among well-behaved programs, making `TotalWellBehavedDomainOn` false. Adding a third well-typed function `.wellTypedAddThree` ($q + 3$) activates the 3-program disjunct (`{.wellTypedAddOne, .wellTypedAddTwo, .wellTypedAddThree}`), which globally enables the completeness requirement $\forall p,\ \text{WellBehavedProgOn}(p) \to \text{Accepted}(T, p)$ across the entire crate—including on `.deadBranchIllTyped`.
- **Evidence Location:** [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), lines 1302–1459 (`Typed2Prog`, `L_typed2`, `Typed3Prog`, `L_typed3`, `honestSyntacticTypeCompiler3`, `ext_typed2_to_typed3`, `TotalWellBehavedDomainOn_Typed2_False_Typed3_True`).
- **Falsification Condition:** Showing either that `L_typed2.TotalWellBehavedDomainOn (fun q => q < 100)` holds or that `L_typed3.TotalWellBehavedDomainOn (fun q => q < 100)` fails.

### F-08: Positive Characterization via Explicit Syntactic Sub-Domains and Extrinsic Indexed Specifications

`Basis: normative + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:** Defining an `ExplicitDomainContract L` (`AcceptedDom : L.Prog → Prop` paired with an extrinsic per-program specification `specOf : (p : L.Prog) → AcceptedDom p → L.Query → SemObs → Prop`) and verifying tools via `Tool.SoundAndCompleteOnExplicitDomain` resolves every Category A1 bypass and Category A2 lockout simultaneously:
  1. **Strict Crate Monotonicity (`ExplicitDomainContract_CrateMonotonic`):** For any `SameDomainCrateExtension L L'`, `L.SatisfiesExplicitContractOn dom pre C p` holds if and only if `L'.SatisfiesExplicitContractOn dom' pre' C' (ext.embedProg p)` holds.
  2. **Syntactic Type-Checker Admission (`ExplicitDomainContract_Admits_SyntacticTypeCheckers`):** On the 3-function crate `L_typed3`, `honestSyntacticTypeCompiler3` satisfies `Tool.SoundAndCompleteOnExplicitDomain` with respect to `typed3Contract`, accepting all 3 well-typed functions while rejecting `.deadBranchIllTyped` and `.liveNullDeref`.
  3. **Constant-Initializer Separation (`ExplicitDomainContract_Separates_ConstInit_From_BuggyConst_And_Spike`):** On the 7-program crate `L_unified_crate` (`{.add1, .add20, .initZero, .bad0, .badConst42, .buggySpike, .oobPanic}`), `honestUnifiedCrateCompiler` satisfies `Tool.SoundAndCompleteOnExplicitDomain` on `q < 16` (where `.add1` outputs `1` and `.add20` outputs `26`), certifying `.initZero` against its intended specification $v = 0$ while refuting `.bad0`, `.badConst42`, and `.buggySpike` against $v = q + 1$.
  4. **Vertical Pipeline Composition (`ExplicitDomainContract_VerticalComposition`, `PENTEST_R3_10_ResolvedByExplicitContract`):** Whenever `tool₁ : Tool L₁ L₂` and `tool₂ : Tool L₂ L₃` satisfy `Tool.SoundAndCompleteOnExplicitDomain` for `C₁` and `C₂` and `tool₁` maps `C₁.AcceptedDom` into `C₂.AcceptedDom`, their vertical composition `Tool.comp tool₁ tool₂` satisfies `Tool.SoundAndCompleteOnExplicitDomain` for `C₁`—even on the nondeterministic intermediate language `L_nondet_pipe` of `PENTEST-R3-10`.
- **Mathematical Derivation:** By replacing unlabeled intrinsic trace guessing (`WellBehavedProgOn`) with an explicit syntactic sub-domain predicate $D_{\text{syn}} = \text{AcceptedDom}$ and an extrinsic indexed specification family $\{S_p\}_{p \in D_{\text{syn}}}$, each function's verification obligation $\text{SatisfiesExplicitContractOn}(L, p)$ becomes a purely local predicate on $(L.\text{sem}(p), D_{\text{syn}}(p), S_p)$ with zero quantifiers over $b \in L.\text{Prog}$. Sound over-approximation ($T(p)\text{ defined} \to p \in D_{\text{syn}} \wedge L.\text{sem}(p) \le S_p \wedge \text{ProductiveCompiles}(p, T(p))$) paired with explicit sub-domain completeness ($p \in D_{\text{syn}} \to T(p)\text{ defined}$) is preserved under functorial composition whenever $T_1(D_{\text{syn}, 1}) \subseteq D_{\text{syn}, 2}$.
- **Evidence Location:** [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), lines 1460–1744 (`ExplicitDomainContract`, `Language.SatisfiesExplicitContractOn`, `Tool.SoundAndCompleteOnExplicitDomain`, `ExplicitDomainContract_CrateMonotonic`, `typed3Contract`, `ExplicitDomainContract_Admits_SyntacticTypeCheckers`, `UnifiedCrateProg`, `L_unified_crate`, `intendedUnifiedSpec`, `honestUnifiedCrateCompiler`, `unifiedCrateContract`, `ExplicitDomainContract_Separates_ConstInit_From_BuggyConst_And_Spike`, `ExplicitDomainContract_VerticalComposition`) and lines 1936–1995 (`nondetPipeDet1Contract`, `PENTEST_R3_10_ResolvedByExplicitContract`).
- **Falsification Condition:** Exhibiting a `SameDomainCrateExtension` that violates `ExplicitDomainContract_CrateMonotonic`, or a pair of domain-compatible contracts `(C₁, C₂)` for which `ExplicitDomainContract_VerticalComposition` fails.

## Boundaries

1. **Requirement of Extrinsic Per-Program Intent (`specOf`) and Syntactic Sub-Domain (`AcceptedDom`):** Theorem 2C (`UnlabeledIntrinsicWellBehavedImpossibility`) and Theorem 3A (`WellBehavedProgOn_Violates_CrateMonotonicity_BothDirections`) prove that no framework can infer whether a program is "intended" or "well-typed" from unlabeled input-output traces `L.sem` alone. Consequently, `ExplicitDomainContract` requires the user or language definition to supply `AcceptedDom` (e.g., an inductive typing relation $\Gamma \vdash e : \tau$) and `specOf` (the intended specification per accepted function).
2. **Non-Equivalence of Syntactic Sub-Domain Completeness and Semantic Completeness:** By Rice's Theorem (1953) and Theorem 2A (`DeadBranchSyntacticCheckerLockout`), any decidable `AcceptedDom` for a Turing-complete language is a strict subset of the dynamically safe programs ($D_{\text{syn}} \subsetneq \text{SemSafe}(L, S)$). `Tool.SoundAndCompleteOnExplicitDomain` guarantees completeness with respect to the declared syntactic discipline $D_{\text{syn}}$, not completeness over undecidable dynamic equivalence classes.
3. **Pipeline Domain Compatibility Condition (`h_maps`):** Theorem 4D (`ExplicitDomainContract_VerticalComposition`) requires that the front-end compiler `tool₁` lower every source program $p_1 \in C_1.\text{AcceptedDom}$ to an intermediate program $p_2 \in C_2.\text{AcceptedDom}$. As demonstrated by `SemanticallyClosedNonComposable` (`PENTEST-R3-10`), if `tool₁` lowers a source program outside the syntactic sub-domain supported by `tool₂`, vertical composition can fail to accept $p_1$ unless $C_1.\text{AcceptedDom}$ is restricted to the preimage $T_1^{-1}(C_2.\text{AcceptedDom})$ (`PENTEST_R3_10_ResolvedByExplicitContract`).

## Evidence

All 18 primary theorems and concrete pentest corollaries are mechanized in standalone Lean 4.34.1 in [support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean) (2,016 lines, SHA-256 `dbfb560a0db48931aa3259633de1c433da36be13f756eb8b402e80c08e342c8b`) and verified with `-DElab.async=false -Ddebug.skipKernelTC=false`:

| Theorem / Definition | Pentest / Literature Mapping | Lines in `InductiveInferenceOverapproxAndMonotonicity.lean` | Kernel Axioms |
| :--- | :--- | :--- | :--- |
| `GoldAngluinFiniteWitnessImpossibility_Prog` | Gold (1967); Angluin (1980); `PENTEST-3A/3B`, `PENTEST-R2-4A/B` | 405–438 | `[]` (none) |
| `FiniteGoodSpecsLocksOutInfiniteFamily` | `PENTEST-R3-2B` (infinite `L_addK` vs. finite `goodSpecs`) | 466–489 | `[propext, Quot.sound]` |
| `GoldAngluinFiniteWitnessImpossibility_Spec` | Blum & Blum (1975); Weyuker (1983); `PENTEST-5`, `PENTEST-R2-5`, `PENTEST-R3-5B`, `PENTEST-R4-9` | 509–546 | `[propext]` |
| `PointSeparatingSpecLocksOutBooleanAndParitySpecs` | Pigeonhole Principle; `PENTEST-R3-5A` (`paritySpec` & `Bool` specs) | 548–594 | `[]` (none) |
| `DeadBranchSyntacticCheckerLockout` | Rice (1953); Morris (1973); Cousot & Cousot (1977); `PENTEST-R3-2A`, `PENTEST-R4-3A/B` | 679–732 | `[]` (none) |
| `SemanticallyClosedNonComposable` | `PENTEST-R3-10` (`Tool.comp` symmetry breaking on `L_nondet_pipe`) | 777–868 | `[propext]` |
| `UnlabeledIntrinsicWellBehavedImpossibility` | `PENTEST-R4-7` (`.buggySpike` satisfies `WellBehavedProgOn` & `TotalWellBehavedDomainOn`) | 890–936 | `[propext]` |
| `WellBehavedProgOn_Violates_CrateMonotonicity_BothDirections` | `PENTEST-R4-1A`, `PENTEST-R4-1B`, `PENTEST-R4-1C` (bidirectional non-monotonicity) | 1096–1300 | `[propext, Quot.sound]` |
| `TotalWellBehavedDomainOn_Typed2_False_Typed3_True` | `PENTEST-R4-3A` (2-function vs. 3-function crate lockout of `honestSyntacticTypeCompiler3`) | 1353–1458 | `[propext]` |
| `ExplicitDomainContract_CrateMonotonic` | Positive Characterization: Crate Monotonicity under `SameDomainCrateExtension` | 1519–1542 | `[Quot.sound]` |
| `ExplicitDomainContract_Admits_SyntacticTypeCheckers` | Positive Characterization: Resolves `PENTEST-R3-2A` and `PENTEST-R4-3A/B` on `L_typed3` | 1566–1610 | `[]` (none) |
| `ExplicitDomainContract_Separates_ConstInit_From_BuggyConst_And_Spike` | Positive Characterization: Resolves `PENTEST-R4-1A/B/C` and `PENTEST-R4-7` on `L_unified_crate` | 1679–1718 | `[]` (none) |
| `ExplicitDomainContract_VerticalComposition` | Positive Characterization: Vertical composition of `SoundAndCompleteOnExplicitDomain` | 1720–1744 | `[]` (none) |
| `PENTEST_2_3AB_R2_4AB_AllowlistAndTrojanSuite` | Concrete Round 1–2 `trojanAddKCompiler`, 1-entry, and 2-entry allowlists | 1756–1801 | `[propext, Classical.choice, Quot.sound]` |
| `PENTEST_5_R2_5_R3_5B_R4_9_DepthKSpecSuite` | Concrete Round 1–4 `depth3FunctionalSpec` passing `ViolatesAtQuerySuite` | 1803–1860 | `[propext, Quot.sound]` |
| `PENTEST_R3_8_R3_9B_InvertedBuggyCompiler` | Concrete Round 3 `invertedSpikeCompiler` passing `SemanticallyClosedOn` | 1862–1909 | `[propext]` |
| `PENTEST_R4_1A_3B_HonestCompilerLockout` | Concrete Round 4 lockout of `honestAdd27Add77Compiler` by `.bad0` | 1911–1934 | `[propext, Quot.sound]` |
| `PENTEST_R3_10_ResolvedByExplicitContract` | Concrete Round 3 resolution of `L_nondet_pipe` via `nondetPipeDet1Contract` | 1936–1995 | `[propext]` |

## Revalidation

- **Triggers:**
  1. Upgrading the Lean 4 toolchain version beyond `leanprover/lean4:v4.34.1`.
  2. Modifying any of the four foundational primitives (`Language`, `Tool`, `BehaviorCodec`, `Spec`) or the definition of `ExplicitDomainContract` / `Tool.SoundAndCompleteOnExplicitDomain`.
- **Procedure:**
  Run the standalone Lean 4 kernel checker from the package directory with asynchronous elaboration and kernel type-checking skip disabled:
  ```bash
  lean -DElab.async=false -Ddebug.skipKernelTC=false support/InductiveInferenceOverapproxAndMonotonicity.lean
  ```
  Verify that the command exits with code `0`, emits zero warnings or errors, and prints only standard Lean axioms (`[]`, `[propext]`, `[Quot.sound]`, or `[propext, Classical.choice, Quot.sound]`) for all 18 `#print axioms` declarations.
- **History:**
  - `2026-11-04`: Initial mechanization and full Lean 4.34.1 kernel verification of all 18 theorems ([support/InductiveInferenceOverapproxAndMonotonicity.lean](support/InductiveInferenceOverapproxAndMonotonicity.lean), 2,016 lines).
