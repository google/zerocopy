# Certification evidence against recurring specification-defect classes: formal analysis under DO-178C/DO-333 practice, MC/DC and observable MC/DC fault-finding studies, and Kind 2/CoCoSpec, AGREE and Copilot contract and monitor checks

## Summary

- **Four of the five recurring defect classes are examined here:** (D1) documentation that disagrees with code; (D2) checks that are computed but discarded, commented out or deactivated; (D4) units and conventions at component boundaries; (D5) an n-ary condition implemented as a pairwise fold. The fifth, convergence criteria that do not imply accuracy (D3), is out of scope. The recurring finding is that **every mechanism examined, whether formal analysis, structural coverage or contracts, checks code against a *formalized* statement and cannot see a defect that the formalization shares.** The formalization may be a requirement property, a coverage obligation or a contract. D2 and D5 are caught when the requirement is stated at the output with the full n-ary predicate. D1 is caught only for the formalized part of the documentation. D4 is caught only when the unit error happens to violate a stated range.
- **Industrial formal-analysis evidence (examined sources).** Rockwell Collins model-checked the ADGS-2100 Window Manager against 563 properties and found and corrected 98 errors in early model versions. In an AFRL side-by-side study, 62 requirement properties found 12 errors in redundancy-management logic; an independent testing team spent about 1.5× as much effort and found none. In a third study, 5 design errors were found in a floating-point effector blender, and "several potential errors that were being masked by defensive design practices" were also found (Miller, Whalen, Cofer 2010). For Airbus, the examined sources (an ONERA overview and a 2013 talk) record certification credit for formal methods on A380 software, and proof of functional properties on C source with Frama-C for DO-178 level A, and say model checking of SCADE models had "no certification credit yet". The primary Airbus unit-proof papers (Souyris et al. 2009; Moy et al. 2013) were **not examined**, so no defect counts from them are reported. `Basis: documentation`.
- **MC/DC fault-finding evidence.** Chilenski (FAA 2001) found the unique-cause and masking forms "nearly identical" in error detection on expressions from five level-A units of a single Ada supplier, and recommended masking MC/DC. Whalen et al. (ICSE 2013) report that observable MC/DC finds 2%–88% more faults than MC/DC with an output-only oracle on four Rockwell Collins systems and one teaching model, 1%–14% more (median 4.5%) with an all-state oracle, and that it is much less sensitive to program structure. They cite earlier work in which inlining alone changed MC/DC fault detection by up to 89%. Gay et al. (TSE 2015), across seven case examples, find coverage-directed generation often no better than random suites of equal size; reducing random suites to coverage-providing subsets found up to 13.5% more faults. `Basis: documentation`.
- **Toy model (`Basis: execution (toy model of MC/DC adequacy, not any real program or tool)`).** For `out = (a∧b∧c∧d) ∨ ovr`, every minimum unique-cause or masking MC/DC test set (5 tests) is guaranteed to kill only 10 of 19 semantic mutants when the conjunction is one decision, and 9 of 19 when it is decomposed into nested `if`s or a pairwise fold. The independence pairs may sit where `ovr` masks the output. An observability-constrained variant needs 6 tests and kills all 19. For a three-channel "all distinct" check implemented as `x≠y ∧ y≠z` (omitting `x≠z`), only 50% (values in {0,1,2}) or 33% (values in {0..3}) of minimum MC/DC sets measured on the *implementation* contain a revealing test. 100% of minimum sets measured on the *requirement formula* do.
- **Contract tools on the defect classes** (`Basis: execution` with Kind 2 v3.0.0 + Z3 5.3.3; `source` for AGREE and Copilot):
  - Kind 2 found the pairwise-fold omission (counterexample `x=1, y=0, z=1`) and the discarded range check (`x=101`). Its `--check_reach` flagged an unsatisfiable mode as unreachable, and `CONTRACTCK` flagged contradictory guarantees.
  - It accepted feet wired into a metres input whenever the feet range fits inside the metres envelope, and reported the assumption violation only when it did not.
  - It printed a guarantee *labelled* "output never exceeds 100" as **valid** while the formula was `y <= 1000`. The documentation/formula mismatch is reproduced in the tool's own output.
  - Kind 2 v3.0.0's realizability check reported `guarantee x > 0` (constraining only an uncontrolled input) as realizable, contradicting the definition in its own documentation; a candidate mechanism is visible in its source.
  - Neither Kind 2's lexer nor AGREE's grammar has a unit-of-measure construct.
  - copilot-verifier proves C-versus-spec bisimulation, but by default treats floating-point operations as uninterpreted functions and trusts the C front end and the trigger implementations.

## Applicability

- **Kind 2.** Executed: release `v3.0.0` (pinned commit and artifact hash) with Z3 `z3-5.3.3` on x86_64 Linux. Source quoted from `v3.0.0` where the execution depends on it, and from the development head (pinned) for the contract translator and checker structure. `src/realizability.ml` differs between the two revisions: head adds a function-realizability case. The quoted partitioning lines are present in both. Behaviour of other releases is not established.
- **AGREE and Copilot.** Source and in-repository documentation at the pinned revisions only. Neither tool was built or run (AGREE needs the OSATE/Eclipse environment; copilot-verifier needs GHC, Clang ≤ 16 and an SMT solver), so AGREE- and Copilot-specific claims are `source`/`documentation`.
- **MC/DC.** Literature claims apply to the subject programs of each study: Rockwell Collins Simulink/Lustre models, an automotive case study, and expressions from Ada avionics units. The toy model applies only to its own Boolean programs and semantic mutant set. It illustrates mechanisms and is not a rate for real software.
- **Certification regime.** RTCA DO-178C/DO-333 texts were not examined (not openly available). Statements about DO-333 objectives come from Wiels's 2013 presentation, by an author of both Airbus papers, and are labelled as such.
- **Relationships.** The three contract tools are compared as alternative ways to state component-boundary assumptions. The coverage literature and toy model address what testing-based certification evidence detects. Miller et al. and the ONERA sources supply industrial formal-analysis evidence. Kind 2 is also used as an execution vehicle for small defect specimens written for this report.

## Findings

### 1. The evidence question and the defect classes

`Basis: derived` (a classification used to organize the evidence)

| class | defect | what any detector must have access to |
| :-- | :-- | :-- |
| D1 | documentation/comment/requirement text disagrees with code | an interpretation of the text, i.e. a formal requirement |
| D2 | a check is computed but its result is discarded, commented out or deactivated | an output-level requirement that the check enforces, or a dataflow/observability obligation |
| D4 | units or conventions differ across a boundary (feet vs metres, degrees vs radians, sign conventions) | a typed or ranged interface statement that distinguishes the conventions |
| D5 | an n-ary condition (all distinct, majority, all within tolerance) implemented as a chain of pairwise tests | the full n-ary predicate in the requirement, or tests that probe the omitted pair |

### 2. Certification regime: what formal analysis may replace

`Basis: documentation (Wiels 2013 slides; Wiels et al. 2012, AerospaceLab AL04-10)`

- **DO-333 definitions, as summarized by Wiels.** A formal notation has "precise, unambiguous, mathematically defined syntax and semantics". Formal analysis is "the use of mathematical reasoning to guarantee that properties are always satisfied by a formal model", and "soundness is required for an analysis to be considered formal".
- **Replaceable objectives.** When HLR/LLR are formally expressed, formal analysis may replace review-and-analysis objectives, conformance tests against HLR and LLR, and robustness tests. When LLR are formal *and* property preservation between source and executable object code is shown, it may replace some tests. "Formal Analysis cannot replace HW/SW integration tests. Therefore testing will always be required."
- **Coverage (FM 6.7.1).** Structural coverage objectives may be replaced by: complete coverage of each requirement (6.7.1.2); completeness of the set of requirements (6.7.1.3); detection of unintended dataflow relationships (6.7.1.4); and **detection of extraneous code including dead code and deactivated code (6.7.1.5)**. The last item is the regime's explicit hook for D2.
- **Industrial practice (2012–2013).** Certification credit for formal methods was obtained by Airbus for A380 software. Airbus used AbsInt tools (stack, WCET, absence of run-time errors) and Frama-C for DO-178 level A. Model checking of Simulink/SCADE models gave "better model earlier" but "no certification credit yet". Airbus's five adoption criteria are soundness, cost savings, analysis of unaltered programs, usability by normal software engineers on normal machines, and integrability into the DO-178B process. Verification and validation is stated to be "more than 50% of software development costs".
- **Not examined:** the defect classes and counts in Souyris et al. 2009 (Airbus unit proof) and Moy et al. 2013 (DO-178C alternatives). Their DOIs resolve, but their texts were not retrievable. Woodcock et al. 2009 was likewise not examined.

### 3. Model checking of flight-software models: reported defects

`Basis: documentation (Miller, Whalen, Cofer, CACM 2010, author's version)`

| study | model | properties | errors found | notes |
| :-- | :-- | --: | --: | :-- |
| ADGS-2100 Window Manager | 5 components; 16,117 Simulink blocks in 4,295 subsystem instances; reachable states 9.8×10⁹ to 1.5×10³⁷ | 563 | 98 (early model versions) | checked after every design change by the end |
| CerTA FCS Phase I (UAV redundancy management) | 3 components; 169 blocks in 23 subsystems; 2.1×10⁴ to 6.0×10¹³ states; replicated ×10 | 62 | 12 (4 severity 3, 2 severity 4, 2 requirement changes, 1 redundant, 3 unimplemented requirements) | independent testing team: ≈1.5× the effort, 0 errors |
| CerTA FCS Phase II (effector blender) | > 2,000 blocks in 166 subsystems, 3×6 floating-point matrix | output-limit properties | 5, plus potential errors masked by defensive design | floats converted to fixed point, which made the results *unsound* (debugging aid only); composition proved by hand |

Translator optimizations cut one NuSMV run from "over 29 hours to less than a second". Training was "a single day … and a low level of ongoing mentoring". Mapping onto the defect classes: the sources give no per-class breakdown. The masked-by-defensive-design observation is the only one that bears directly on D2/observability. No examined report gives evidence for D4 or D5 specifically.

### 4. Condition-level structural coverage: definitions and fault-finding evidence

**Definitions** (`Basis: documentation`; Hayhurst et al. 2001; Chilenski 2001):

- MC/DC requires that every condition in a decision has taken all outcomes and "has been shown to independently affect that decision's outcome".
- *Unique-cause* MC/DC (the DO-178B definition) shows independence with test pairs that differ only in that condition.
- *Unique-Cause+Masking* addresses coupled conditions.
- *Masking* MC/DC allows other conditions to change provided they are masked, which is the Boolean-difference criterion. Chilenski calls it "the weakest possible form" and shows it is solvable for more expressions.
- Short-circuit evaluation leaves unevaluated conditions; the tutorial treats them as don't-cares.

**Evidence:**

| study | subjects | method | finding |
| :-- | :-- | :-- | :-- |
| Chilenski 2001 (DOT/FAA/AR-01/18) | Boolean expressions from five level-A LRUs, one supplier, Ada; generated expressions | theoretical error-detection model (counts tests, not kinds of test) and mutation | the three forms are nearly identical in error-detection probability; differences from statement and decision coverage are much larger; masking MC/DC recommended. Validation on real faults "were not available for this study" |
| Kandl & Kirner 2010 (SEUS) | automotive case study | model-checker-generated MC/DC tests; mutations in values, variable names and Boolean operators | abstract notes examples where an MC/DC-adequate set has zero detection probability. **Full results not examined** |
| Whalen et al. 2013 (ICSE) | DWM1, DWM2, Vertmax, Latctl (Rockwell Collins) + Microwave; 250 mutants each | OMC/DC requires each condition's effect to propagate along a non-masking path to an observed output | OMC/DC +2% to +88% fault finding over MC/DC (output-only oracle), +1% to +14%, median +4.5% (all-state oracle); "dramatically less sensitive" to structure |
| Gay et al. 2015 (TSE) | 7 case examples (DWM 1/2, Vertmax, Latctl, NASA docking approach, infusion manager, alarms) | counterexample-based and random generation to coverage vs equal-size random | coverage satisfaction alone can be a poor indicator; random reduced to a coverage subset finds up to 13.5% more faults; OMC/DC can beat random |

**Toy model of decomposition and masking** (`support/mcdc_toy/mcdc_toy.py`, exact enumeration over all 32 input vectors; `Basis: execution (toy model, not a real program)`). The probe enumerates minimum adequate test sets of the correct program and counts semantic mutants of the conjunction that *every* such set kills. There are 19 mutants: 4 negations, 8 stuck-at, 3 `∧→∨` replacements, 3 variable replacements and 1 dropped override, all non-equivalent.

| structure of `t = a∧b∧c∧d; out = t ∨ ovr` | criterion | min tests | # min sets | guaranteed kills | mean kills |
| :-- | :-- | --: | --: | --: | --: |
| single 4-condition decision | decision coverage | 2 | 30 | 0/19 | 5.53 |
| single decision | unique-cause = masking | 5 | 14 | 10/19 | 15.21 |
| single decision | observable masking | 6 | 15 | 19/19 | 19.00 |
| nested `if a: if b: if c: if d` | unique-cause = masking | 5 | 896 | 9/19 | 12.20 |
| nested | observable masking | 6 | 15 | 19/19 | 19.00 |
| pairwise fold `t1=a∧b; t2=t1∧c; t=t2∧d` | unique-cause = masking | 5 | 294 | 9/19 | 12.95 |
| pairwise fold | observable masking | 6 | 15 | 19/19 | 19.00 |

Mutants not guaranteed under the non-observable criteria are the four stuck-at-1 faults, the `∧→∨` replacements and the variable replacements. Their only independence pairs may be taken with `ovr = 1`, where the conjunction cannot reach the output. This is a minimal instance of the masking mechanism that OMC/DC targets.

| D5 specimen: spec `allDistinct(x,y,z)`; code `x≠y ∧ y≠z` | criterion | min tests | sets revealing the omission |
| :-- | :-- | --: | --: |
| values {0,1,2}, coverage measured on code | unique-cause / masking | 3 | 216/432 (50.0%) |
| values {0,1,2}, coverage measured on requirement formula | unique-cause / masking | 4 | 1296/1296 (100%) |
| values {0..3}, coverage measured on code | unique-cause / masking | 3 | 1728/5184 (33.3%) |
| values {0..3}, coverage measured on requirement formula | unique-cause / masking | 4 | 41472/41472 (100%) |

Derived reading: structural coverage of the implementation cannot *require* a test for a condition the implementation omits, so D5 detection by code coverage is incidental. Coverage of the requirement formula (requirements-based coverage) makes it mandatory. Chilenski's executive summary states that structural coverage is a "check and balance on requirements-based verification", which is consistent with this.

### 5. Contract languages: what is stated, checked and trusted

`Basis: source (pinned revisions) + documentation (in-repo docs) + execution (Kind 2 only)`

| aspect | Kind 2 / CoCoSpec | AGREE | Copilot |
| :-- | :-- | :-- | :-- |
| attachment point | Lustre node or function contract (`(*@contract … *)`), importable contract nodes | AADL component annex: `assume`, `guarantee`, `assert`, `lemma`, `reachable` (`Agree.xtext` L91–95) | Haskell-embedded stream DSL: `Stream a` ≅ `ℕ → a`; triggers with guards |
| semantics | `n` respects `(A,G)` iff □A ⇒ □G. Modes `(R,E)` add guarantees `∧R ⇒ ∧E`. Callee assumptions become caller-site properties (`contract-semantics.md`) | compositional assume–guarantee over the architecture; synchrony options (`synchrony`, `calendar`, `latched`, `asynchronous`) | discrete-time streams compiled to constant-space C ring buffers |
| ranges | `subrange [l,u] of int`, `subtype` refinement types, `assume` | `assume`/`guarantee` expressions; `int`/`real`/`bool`, `struct`, `enum` | assertions on streams |
| units | none in the lexer keyword list (L249–346) | none; primitive types `real`, `bool`, `int` (L221) | none in the DSL; the verifier's default `FloatUninterpreted` mode treats float operations as uninterpreted |
| modes | `mode … require … ensure`; one-mode-active check; `--check_reach` non-vacuity | none built in; temporal patterns (`whenever … occurs … during`, `condition … occurs each … with jitter`) | – |
| timing | synchronous steps; `pre`, `->` | `PeriodicStatement`/`SporadicStatement` with jitter and IAT | step function called by the environment; generated C claimed constant-time (2012 report) |
| static checks | k-induction/IC3 property proving; `CONTRACTCK` realizability and satisfiability; `--check_reach` | compositional analysis via Lustre back-ends; `reachable` statements | copilot-verifier: initial-state correspondence, transition preservation, trigger equivalence, discharged by SMT (default Z3) |
| runtime | `contract_monitor` module | – | the generated monitors themselves |
| human text bound to formulas | optional guarantee/assume string; used as the **property name** in output | **mandatory** `str=STRING` on every assume/guarantee/lemma | none |
| trusted | Lustre front end, Kind 2 engines, SMT solver | AADL/Lustre translation, back-end model checker | `clang` → LLVM bitcode, Crucible LLVM semantics, SMT solver, the trigger functions' implementations (assumed not to modify the monitor's memory and to be memory safe) |

Mode semantics in Kind 2's `contractsToProps.ml`: `Assume` becomes an `Assert`, `Guarantee` a property, and each mode `ensure e` the property `(not (r1 and … rn)) or e`. Contract calls and contract node declarations are rejected by that translator with "unsupported". Copilot's 2012 CBMC-based equivalence check was bounded: "CBMC cannot guarantee equivalence beyond the fixed number of iterations". copilot-verifier replaces it with an unbounded bisimulation argument (README; Scott et al., ICFP 2023).

### 6. Kind 2 on defect specimens (real tool runs)

`Basis: execution (Kind 2 v3.0.0 + Z3 5.3.3; files and full outputs in support/kind2_probe/)`

| specimen (node) | class | Kind 2 result | reading |
| :-- | :-- | :-- | :-- |
| `AllDistinct`: guarantee `ok = (x<>y and y<>z and x<>z)`, code `x<>y and y<>z` | D5 | **invalid**, counterexample `x=1, y=0, z=1`, `ok=true` (0.05–0.07 s) | caught because the requirement states the full n-ary predicate |
| `Saturate`: `in_range = x <= 100` computed, `y = x` | D2 | **invalid**, counterexample `x=101` | caught by the output-level guarantee. No warning about the unused local `in_range` appeared in the output |
| `DocDrift`: guarantee `"output never exceeds 100" y <= 1000` | D1 | printed as `output never exceeds 100: valid (k=1)` with `(y <= 1000)` on the next line | the human label is not interpreted; a reader scanning names sees a false claim marked valid |
| `SystemUnitsBug`: feet producer `[0,12000]` → metres consumer assuming `[0,15000]` | D4 | callee assumption **valid** | unit error accepted because ranges nest |
| `SystemUnitsRangeVisible`: feet producer `[0,45000]` → same consumer | D4 | callee assumption **invalid**, counterexample `alt = 15001` | caught only because the unit error violates the range |
| `VacuousMode`: mode `high` requires `x > 10` and `x < 5` | vacuity | `high … unreachable` (non-vacuity check fails) while `high.ensure` is **valid** | without `--check_reach`, the vacuous ensure would be reported valid with no warning |
| `Contradiction`: guarantees `y > x` and `y < x` | inconsistent spec | contract **unrealizable** and **unsatisfiable**, with conflict set listing both guarantees | caught by `CONTRACTCK` |
| `GuarInputOnly`: `guarantee x > 0` (no assumptions) | inconsistent spec | contract **realizable** under `CONTRACTCK`; property **invalid** under normal analysis (`x=0` at k=0) | see below |
| `GuarPastOutput`: `guarantee true -> (pre y = x)` | requires prediction | **realizable** under `CONTRACTCK`; property **invalid** under normal analysis | see below |

**Realizability discrepancy (observed; mechanism not established).** Kind 2's documentation at `v3.0.0` (`doc/usr/source/9_other/12_contract_check.rst`, lines 10–13; the same sentence is in `doc/content/advanced-features/contract-check.md` at the development head) defines a realizable contract as one for which "a component can be constructed such that, for any input satisfying the contract assumptions, there exists some output value that the component can produce to meet the contract guarantees". Under that definition `GuarInputOnly` is unrealizable: input `x = 0` admits no output. `v3.0.0` reports it realizable. The realizability check partitions transition-relation conjuncts by whether they mention a controllable variable at the current step and uses the conjuncts that do not as **premises** (`src/realizability.ml` at `v3.0.0`, lines 187–194 and 222–224):

```ocaml
    (* term_partion assumes constraints over controllable variables contains
       at least a controllable variable in the current state. This is the case
       if the transition system is the direct translation of a Lustre model
       since all constraints are introduced through the definition
       and assertion of a boolean state variable.
       When invariants are included, the partitioning adds them to
       the first part (free_of_controllable_vars_at_1) *)
    term_partition controllable_vars_at_1 (get_conjucts trans)
    …
    let premises = Term.mk_and (fp :: free_of_controllable_vars_at_1) in

    let conclusion = Term.mk_and (fp_at_1 :: contains_controllable_vars_at_1) in
```

A guarantee that mentions no current-step output would be treated as an environment premise *if* it reaches the partition as such a conjunct. That is consistent with both observations. The terms actually produced for these nodes were not traced, so whether this is intended semantics or a defect is **unknown**. The cheap guard is to state every guarantee over at least one current output and to cross-check `CONTRACTCK` verdicts with ordinary property analysis.

### 7. Evidence map: defect class × evidence source

`Basis: derived` from Sections 2–6. "No evidence" means no examined source reports detection or non-detection for that class.

| class | formal analysis in industrial reports | MC/DC literature | OMC/DC | Kind 2/CoCoSpec | AGREE | Copilot (+ verifier) |
| :-- | :-- | :-- | :-- | :-- | :-- | :-- |
| D1 doc ≠ code | no per-class evidence (Miller: errors found against formalized requirements) | none | none | **misses** natural-language drift; label shown as property name (execution) | mandatory description strings, unchecked (source) | verifier checks C against spec, not spec against text |
| D2 discarded/deactivated check | Miller: errors "masked by defensive design practices" found; DO-333 6.7.1.5 targets deactivated code (slides) | MC/DC can be satisfied while the check's effect is masked (toy) | designed for it: requires propagation to output | caught when an output guarantee exists (execution) | same in principle (not run) | monitors observe streams; a deactivated trigger guard would be a spec/C mismatch only if introduced by the compiler |
| D4 units/conventions | no evidence | none | none | only if it violates a range (execution) | no unit types (source) | no unit types; floats uninterpreted by default (source) |
| D5 n-ary as pairwise fold | no evidence | code coverage incidental (toy) | not examined | caught when the requirement has the full predicate (execution) | same in principle (not run) | spec-level only |

### 8. Performance and resource footprint (L1–L6)

| level | quantity | value | basis |
| :-- | :-- | :-- | :-- |
| L1 authoring | model-checking training for Simulink developers | "a single day" + light mentoring | documentation (Miller 2010) |
| L1 | test vs model-checking effort, CerTA Phase I | testing ≈ 1.5× the model-checking effort; 0 vs 12 errors | documentation |
| L1 | unit-proof authoring effort (Airbus) | not measured (primary papers not examined) | – |
| L2 toolchain | Kind 2 v3.0.0 binary / tarball; Z3 archive | 10,166,616 B / 3,646,477 B; 69,671,358 B | execution (`ls`) |
| L2 | building Kind 2, AGREE, Copilot | not measured | – |
| L3 analysis latency | Kind 2 on `defects.lus` (7 analyses, `--check_reach`) | 1.86 s wall; per-property verdicts 0.03–0.08 s | execution |
| L3 | same, compositional + modular | 3.68 s wall | execution |
| L3 | `CONTRACTCK` on `realiz.lus` (3 nodes) | 0.44 s wall | execution |
| L3 | NuSMV on one Window Manager model before/after translator optimization | > 29 h / < 1 s | documentation |
| L4 generated code | Copilot C monitors | constant time and space (claimed); cycles not measured | documentation |
| L5 checking | copilot-verifier proof time | not measured | – |
| L6 memory | Kind 2 max RSS (GNU `time -v`) | 35,448–39,292 kB | execution |
| L6 | state spaces checked (Window Manager; redundancy management) | 9.8×10⁹–1.5×10³⁷; 2.1×10⁴–6.0×10¹³ | documentation |
| L6 | toy MC/DC enumeration | 51.8 s single-thread for all tables | execution (toy) |

### 9. Human comprehensibility (C1) and conceptual simplicity (C2)

- **C1.** Counterexamples from Kind 2 are short concrete traces (`x=1, y=0, z=1`) that a domain engineer can audit; that is the strongest legibility point observed. The weakest is the human-readable label. Kind 2 promotes it to the property *name*, and AGREE makes it mandatory, so readers are invited to trust text that no tool interprets. A reviewer must read the formula, not the label. MC/DC adequacy is legible as a count but not as a guarantee: "100% MC/DC" says nothing about whether a condition's effect was observable (Section 4).
- **C2.** One invariant, *a requirement's condition affects the observed output in every relevant situation*, is enforced by several partial mechanisms: unique-cause, masking and observable MC/DC, requirements-based coverage, DO-333's replacement objectives, and contract non-vacuity checks. Observable coverage and output-level contract properties are the two that make masking an ordinary case instead of an exception. Units are a missing orthogonal dimension in all three contract languages. Encoding them as ranges, the only option available, merges two invariants (magnitude and dimension) into one check, which is exactly why the feet/metres specimen passes.

### 10. Validation (V1–V4)

- **V1, specification adequacy and non-vacuity.** Kind 2 provides three distinct non-vacuity oracles: `--check_reach` for modes, `CONTRACTCK` for satisfiability and realizability, and ordinary property falsification. They disagree on `GuarInputOnly`, so one must not be used as a proxy for another. AGREE has `reachable` statements (source). Mutation-based adequacy appears in the MC/DC studies (250 mutants per system; Chilenski's mutation analysis), not in the contract tools.
- **V2, lowering/checker soundness.** copilot-verifier is a translation-validation step for every generated monitor, with a bisimulation relation `0 ≤ idx < k ∧ s[n+i] = buf[(idx+i) mod k]`. Kind 2's own soundness and the realizability semantics were not fuzzed. Miller et al.'s fixed-point conversion was explicitly unsound and was used for debugging only.
- **V3, concurrency/crash/silicon.** Not examined.
- **V4, plant falsification and field replay.** Copilot's fault-tolerant airspeed monitors were flown on a subscale aircraft with five pitot tubes, in five flights plus two control flights, with one node injecting Byzantine values and tubes physically capped or taped. With only two good tubes out of five, the three non-faulty nodes agreed on "a consistent—but wrong—value". In another scenario a calibration function underflowed on a capped tube. No human-comprehension study of contracts or coverage reports was examined.

## Boundaries

- **Not examined:** RTCA DO-178C and DO-333 texts; Souyris et al. 2009 and Moy et al. 2013 beyond titles and DOI resolution; Woodcock et al. 2009; Cofer et al. 2012 (AGREE case study); Pike et al. 2010; the CoCoSpec (SEFM 2016) and Kind 2 (CAV 2016) papers; and Kandl & Kirner 2010 beyond its abstract. Consequently **no Airbus unit-proof defect counts, no CoCoSpec or AGREE industrial interface-defect reports, and no automotive MC/DC detection rates are reported**.
- **Unknown:** whether the Kind 2 realizability discrepancy is a defect or an intended semantics with undocumented scope. Also unknown: whether any examined industrial study encountered D4 or D5, since none breaks errors down by these classes.
- **Known not to apply:** the toy kill rates do not transfer to real programs, mutant mixes or test generators. Real programs have coupled conditions, temporal state and relational atoms that the toy omits.
- **Unsupported:** that observable MC/DC detects D5 or D4 (the cited study measured mutants of existing code, which cannot include an omitted condition unless the mutant set models omissions); that a passing Kind 2 analysis implies unit correctness; that copilot-verifier validates monitor *requirements*.
- **Not run:** AGREE, copilot-verifier, Kind 2's `contract_monitor`, and any DO-333-style unit proof tool (Frama-C WP or similar).

## Evidence

- **Kind 2.** Execution: release `v3.0.0`, commit `1a05ebc42c5161b72030e69496b48e3483139ce4`, artifact `kind2-v3.0.0-linux-x86_64.tar.gz`, sha256 `a8d08130a1ae8039ff42474fccee955880491061fc7b97d3954d3e66e6faa19d`. Source at development head `c080a232181bf571f090f58cc5b70a23e3a5fa24`:
  - `src/lustre/contractsToProps.ml` (`collect_contracts`: `Ast.Assume` → `Ast.Assert`; `Ast.Guarantee` → property; `Ast.Mode` → `(not (reqs)) or ens`; `ContractCall` → `failwith "… contract calls are unsupported"`);
  - `src/lustre/contractChecker.ml` (`check_contract_realizability`, `check_contract_satisfiability`);
  - `src/realizability.ml`;
  - `src/lustre/lustreLexer.mll` (keyword table, lines 240–346);
  - `doc/content/advanced-features/contract-semantics.md` and `contract-check.md`.
  The quoted realizability lines (`src/realizability.ml` lines 187–194, 222–224) and the realizability definition (`doc/usr/source/9_other/12_contract_check.rst` lines 10–13) are from `v3.0.0`. Probe files and outputs: `support/kind2_probe/`.
- **Z3.** Release `z3-5.3.3`, commit `430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e`, artifact `z3-5.3.3-x64-glibc-2.39.zip`, sha256 `d56f60b06f432f33de5810f7f1a384a339131f361e2d54d08ea83eea14326880`.
- **AGREE.** Commit `c7848ff79871e1382ef0aafc762ee4d8bb0e362c`, `com.rockwellcollins.atc.agree/src/com/rockwellcollins/atc/agree/Agree.xtext`:
  - L91–95: `AssumeStatement 'assume' (name=ID)? str=STRING ':' (expr=Expr | pattern=PatternStatement) ';'`, and likewise `guarantee`, `assert`, `lemma`, `reachable`;
  - L108–127: temporal patterns;
  - L138–142: synchrony;
  - L221: `'real' | 'bool' | 'int'`;
  - L343–344: `floor`, `real` casts.
- **Copilot.** Commit `ee1ff1994214554910d36d321817ca013748a32e`:
  - `copilot-verifier/README.md` (correspondence relation, trigger overrides and assumptions, partial-operation modes);
  - `copilot-verifier/src/Copilot/Verifier.hs` lines 171–252 (`VerifierOptions`; `defaultVerifierOptions` sets `assumePartialSideConds = False`, `smtSolver = Solver.Z3`, `smtFloatMode = FloatMode.FloatUninterpreted`).
- **MC/DC toy.** `support/mcdc_toy/mcdc_toy.py` and `mcdc_toy_output.txt`. Run with `python3 mcdc_toy.py`: deterministic, Python 3 standard library, 51.8 s.
- **Literature.** Identifiers were verified 2026-11-20 by DOI handle resolution and Semantic Scholar metadata; direct Crossref API access was unavailable. Content examined in full text unless stated:
  - Whalen et al., doi:10.1109/ICSE.2013.6606556 (author copy);
  - Gay et al., doi:10.1109/TSE.2015.2421011 (author copy);
  - Miller, Whalen, Cofer, doi:10.1145/1646353.1646372 (author's version);
  - Chilenski, DOT/FAA/AR-01/18 (FAA PDF);
  - Hayhurst et al., NASA/TM-2001-210876 (mirror PDF);
  - Pike et al., NASA/CR-2012-217329 (technical-report version of doi:10.1007/s11334-013-0223-x);
  - Wiels et al., AerospaceLab AL04-10 (2012);
  - Wiels, 2013 presentation slides;
  - Scott, Dodds, Perez, Goodloe, Dockins, *Trustworthy Runtime Verification via Bisimulation*, doi:10.1145/3607841 (abstract; content via the repository README).
  - DOIs verified only (content not examined): Souyris et al. doi:10.1007/978-3-642-05089-3_34; Moy et al. doi:10.1109/MS.2013.43; Woodcock et al. doi:10.1145/1592434.1592436; Kandl & Kirner doi:10.1007/978-3-642-16256-5_14 (abstract read); Cofer et al. doi:10.1007/978-3-642-28891-3_13; Pike et al. 2010 doi:10.1007/978-3-642-16612-9_26; Champion et al. CoCoSpec doi:10.1007/978-3-319-41591-8_24; Champion et al. Kind 2 doi:10.1007/978-3-319-41540-6_29.

## Revalidation

1. **Kind 2 specimens.** Download the target Kind 2 release and a Z3 release and rerun the four commands in `support/kind2_probe/README.txt` (under 5 s total). Expected discriminators: `AllDistinct` and `Saturate` invalid; `SystemUnitsBug` assumption valid; `SystemUnitsRangeVisible` invalid; `high` unreachable; `Contradiction` unrealizable. Check whether `GuarInputOnly` is still realizable under `CONTRACTCK`. If it flips to unrealizable, the discrepancy is resolved; diff `src/realizability.ml` around `term_partition` to see why.
2. **Unit constructs.** Grep the target Kind 2 `src/lustre/lustreLexer.mll` keyword table and AGREE `Agree.xtext` `PrimType`/type rules for any unit-of-measure construct. Their absence is the basis for the D4 rows.
3. **Copilot assumptions.** Re-read `defaultVerifierOptions` in `copilot-verifier/src/Copilot/Verifier.hs` (float mode and solver) and the trigger-assumption paragraph of `copilot-verifier/README.md`.
4. **Toy model.** `python3 support/mcdc_toy/mcdc_toy.py` must reproduce `mcdc_toy_output.txt` byte-for-byte. A change means the script changed, not a fact about any real system.
5. **Literature gaps.** The cheapest way to close the largest gap is to obtain Souyris et al. 2009 and Moy et al. 2013 and add their reported objectives, defects and effort to Sections 2 and 7.
