# Human review of Alloy, Forge, TLA+ and proof-assistant specifications: novice error corpora, audit-escaped specification defects, and a protocol for measuring review rates

## Summary

- **No measured human review rate exists for Alloy, TLA+ or proof-assistant specifications in any source examined.** No source gives statements or lines reviewed per hour, defect-detection recall, or false-alarm rate for reviewers reading these notations, with or without tools. What does exist falls into four kinds:
  - authoring-error corpora from teaching platforms (Alloy4Fun, ARepair, a 93,283-submission Alloy novice study);
  - comprehension and misconception studies (LTL);
  - user studies of model-finder output, with headline results only;
  - post-hoc audits of verified systems.

  The review rate is therefore **unknown**. Section 8 specifies the experiment needed to measure it.
- **Specification defects that escaped review in verified systems were mostly omissions, not wrong statements.** Fonseca et al. (EuroSys 2017) found 16 bugs in IronFleet, Verdi and Chapar.
  - Only 2 of the 16 were specification bugs: IronFleet's 85-SLOC high-level specification never required exactly-once semantics, and a Chapar test assertion was a tautology. Both "would allow … implementations that return incorrect results to pass verification".
  - A 7-line patch disabling deduplication still verified.
  - In seL4, writing the first refinement proof caused about 300 changes to the abstract specification, about half of them algorithm or design bugs (SOSP 2009).
  - Reading a specification does not find an absent clause. Mutating the implementation, proving extra properties, or demanding non-vacuity witnesses does.
- **Recount of the public Alloy4Fun 2019/20 dataset** (17 students, 9 exercises, 93 challenges):
  - 10,949 entries; 3,081 of 10,781 executions (28.6%) raised errors; 4,000 of 7,682 oracle checks (52.1%) were wrong.
  - Our count of correct checks (3,682) equals the published figure exactly.
  - 70.8% of first-correct events had no earlier failed check on their derivation path. Where at least one check had failed, the median time from that first failure to the first correct answer was 1.5 minutes (90th percentile 15.6 minutes).
  - The pattern `some x | A implies B` (an existential that scopes over an implication) appears in 373 of 4,000 wrong submissions but only 6 of 3,682 correct ones.
- **Classes in ARepair's 38 real faulty Alloy models.** The fix annotations (71 across 37 models), classified by explicit rules:
  - relational-expression errors (closure, transpose, navigation): 19;
  - a missing emptiness guard before navigating a partial relation: 18;
  - a missing constraint: 12;
  - a quantifier or multiplicity keyword: 9;
  - connective confusion (implies vs iff, and vs or): 8.
- **Real analyzers catch every seeded misconception class quickly, but only when asked the right question.** Alloy 6.2.0 and TLC 1.7.4 were run on hand-written toy specifications.
  - Each seeded defect — vacuity, quantifier order, missing frame condition, missing fairness — produced a counterexample, or an unsatisfiable non-vacuity witness. Solver times were 53–65 ms; wall times were 0.5–2.4 s including JVM start.
  - The vacuous assertion passed its own `check`. Only a separate `run` of its antecedent exposed it.
  - In a mutant screen, 22 of 24 single-operator mutants were killed at scope 1 and the other 2 at scope 2. Two intended-equivalent rewrites were correctly left unkilled.

## Applicability

This report is about **how well humans can review formal specification statements**, and about the corpora, tools and audit evidence that bear on it. Subjects relate as follows:

- **Alloy4Fun** (`haslab/Alloy4Fun` at `c97f9b2041c7b8ba947122bfc8ae276a2c0d492f`) is the platform. Its 2019/20 dataset lives in the project's GitHub wiki repository (`em1920/`).
  - The files were last changed in wiki commit `886eba28b854` (2020-03-05). They are byte-identical at the observed wiki head `1478014567d9` (2026-11-10).
  - SHA-256 hashes for all nine files are in **Evidence**.
  - The wiki page that documented the dataset was deleted on 2026-11-10. Its text is recovered from wiki history. Statistics are about this dataset only: 17 graduate students, self-study use, not graded.
- **ARepair** (`kaiyuanw/ARepair` at `dacd87d1fa3de4017f6c415f72ab6466211e6150`) supplies the 38 faulty models and their fix annotations. **MuAlloy** (`kaiyuanw/MuAlloy` at `1083004d6968e92ada75e52f21dcf8bf61a80b26`) supplies the mutation-operator vocabulary.
- **Forge** (`tnelson/Forge` at `326400a735540d25f697336c7efbacd215b1800e`) and **Sterling** (`alloy-js/sterling` at `78cb1500ebe0e2f85b3bd4faddc19753dbd4d01b`) were inspected for their specification-testing and visualization mechanisms only. Their classroom outcome data are not public and were **not examined**.
- **Alloy Analyzer**:
  - The probes executed release jar 6.2.0 (SHA-256 in REPORT.json), built from tag `v6.2.0`, commit `59ba2033993449d483d54acad0e11a7bbf20354f`.
  - The warning source was inspected at that tag and at default-branch head `ed89fdb16c58aea17a55e312c44f99e31aa63ee1`. Both carry the same warning text, at lines 604 and 605 respectively.
- **TLC**: release jar 1.7.4. The jar reports `TLC2 Version 2.19 of 08 August 2024 (rev: 5a47802)`, which matches tag commit `5a47802b5c391f59ecdd44117981f4ff8c0656ba`.
- **TLA+ Examples** (`tlaplus/Examples` at `334c3983a2f44ac78fce89d1d20aa79ceb3e6987`) and **seL4 l4v** (`seL4/l4v` at `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`, `spec/abstract/`) are profiled as real specifications that a reviewer would face.
- **Literature**: the papers in REPORT.json, and those cited in **Evidence**, supply audit and study data. Where full text could not be read, only abstract-level claims are used, and the case is marked in **Boundaries**.

**Exact observation vs. extension.** Every probe result is a property of a toy specification run on a real analyzer (labelled `toy model`). It shows what the tool can detect, not how often real specifications contain the defect. The dataset statistics are about novices writing predicates against a hidden oracle, which is an authoring task. They are not a measurement of review. Applying them to expert review of proof-assistant statements is a hypothesis (see **Boundaries**).

Probe host: x86-64 Linux, Intel Xeon at 2.60 GHz, 96 logical CPUs, shared with other workloads (timings vary up to 2× between runs, see §9), OpenJDK 27.0.1, Python 3.13.

## Findings

### 1. Evidence map: what is measured and what is not

| Question | Best available evidence | Status |
|---|---|---|
| Human review rate (statements or lines per hour) for Alloy/TLA+/proof-assistant specs | None found | **unknown** |
| Reviewer recall and false-alarm rate on seeded spec defects | None found. The nearest are Jdoctor-style comment-translation precision/recall and mutation scores, which measure tools, not people | **unknown** |
| Novice authoring error rates in Alloy | Alloy4Fun ABZ 2020; recount in §2; Jovanovic & Sullivan (arXiv:2402.06624): 93,283 submissions, 25.4% correct, 45.3% semantically faulty, 29.28% invalid | measured (novices) |
| LTL comprehension and authoring errors | Greenman et al. 2023: English→LTL wrong 47%/28%/47% (rounds 2/3/4); LTL→English wrong 23%/15%/24% | measured (students; R3 = 29 researchers) |
| Effect of scenario-explorer output on users | Danas et al. SEFM 2017: "most of the output forms fail to be effective, and in some cases even actively mislead users" (abstract) | headline only; numbers **not examined** |
| Effect of provenance (Amalgam) on users | FSE 2017 user study exists | numbers **not examined** |
| Spec defects that survived review in verified systems | Fonseca et al. 2017; seL4 SOSP 2009 / TOCS 2014; AWS preprint 2014 | measured (case counts) |
| Size of real specifications a reviewer must read | §7 measurements of seL4 `spec/abstract/` and tlaplus/Examples; published sizes for IronFleet, Verdi, AWS and MongoRaftReconfig | measured |

Basis: documentation + execution + derived.

### 2. Alloy4Fun 2019/20 dataset recount

Dataset semantics, from the deleted wiki page as recovered from history: each entry is an execution or a permalink share.

- `sat = 1`: the command was satisfiable. For a check, this means a counterexample was found.
- `sat = 0`: unsatisfiable.
- `sat = -1`: an error was thrown.
- `derivationOf`: the parent entry. `original`: the exercise root.

Challenge commands are secret checks comparing the student predicate with an oracle predicate. `sat = 0` on a challenge check means the two are equivalent within the command scope.

| Exercise (predicates) | Entries | Executions | Errors | Oracle checks | Wrong | Wrong share | Median attempts to first correct |
|---|---|---|---|---|---|---|---|
| Trash FOL (10) | 1730 | 1693 | 466 | 1218 | 287 | 23.6% | 1 |
| Classroom FOL (15) | 2426 | 2385 | 573 | 1810 | 940 | 51.9% | 1 |
| Trash RL (10) | 852 | 833 | 292 | 538 | 162 | 30.1% | 1 |
| Classroom RL (15) | 1575 | 1556 | 603 | 951 | 533 | 56.0% | 1 |
| Graphs (8) | 964 | 946 | 232 | 714 | 376 | 52.7% | 1 |
| LTS (7) | 1005 | 997 | 348 | 647 | 518 | 80.1% | 1 |
| Production (4) | 199 | 197 | 61 | 136 | 87 | 64.0% | 2 |
| CV (4) | 368 | 366 | 101 | 265 | 238 | 89.8% | 2 |
| Trash LTL (20) | 1830 | 1808 | 405 | 1403 | 859 | 61.2% | 2 |
| **All** | **10949** | **10781** | **3081 (28.6%)** | **7682** | **4000** | **52.1%** | **1** |

Basis: execution (`a4f_stats.py`, §Evidence) on the real dataset.

- **Reconciliation with the paper.** ABZ 2020 §3.3 says: "Of all the 7689 executions without errors, 3682 were correct (48%)".
  - Our 3,682 unsatisfiable challenge checks equal that figure exactly.
  - Of the 7,700 non-error executions, 11 are executions of non-challenge check commands (`check$1` ×9, `bla` ×2), and removing them leaves 7,689. Those 7,689 are the 7,682 challenge checks plus 7 `run`/`test` commands.
  - Basis: derived.
- **Attempts and elapsed time.** We walked each first-correct challenge check up its `derivationOf` chain to the previous correct check of the same command, counting failed checks on the way.
  - There are 2,638 first-correct events. 70.8% had no earlier failed check. Attempt quartiles are 1/1/2, with 3 at the 90th percentile.
  - Among the 770 events preceded by at least one failure, minutes from first failure to first correct were 0.5 (q25), 1.5 (median), 6.5 (q75) and 15.6 (q90).
  - These times exclude reading and writing before the first check. They are an authoring-latency proxy, not a review rate.
  - Basis: execution + derived.
- **Hardest predicates** (at least 20 checks): CV `Inv4` 100% wrong (95 checks); LTS `inv7` "reversible" 99% (98); Classroom FOL `inv14` 95% (178); Trash LTL `prop12` 92% (120); Graphs `weaklyConnected` 85% (212).
  - A 100% failure rate could mean an unusually hard task or an ambiguous oracle. Which one it is was **not examined**.
- **Published concept-level success rates** (ABZ 2020 §3.3, correct ÷ non-error executions):
  - transitive closure over expressions 8%; ordering module 16%; more than 10 operators 18%; ternary relations 19%;
  - nested quantifiers 33%; nested temporal operators 32%; a single temporal operator 58%; simple multiplicity 52%.
  - Errors: "around 44%" parsing, 28% applying logic operators to relational expressions or vice versa, 26% arity typing. Basis: documentation.
- **Pre-declared misconception signatures.** Each was evaluated on the predicate body of every oracle check (§Evidence gives the code).

| Signature | In correct (n = 3682) | In wrong (n = 4000) |
|---|---|---|
| S1: empty predicate body | 0 | 165 |
| S2: `some <decls> \| … implies/=> …` on one line, with the implication inside the existential's scope (no unmatched `)` before it) | 6 | 373 |
| S3 (Trash LTL only): no temporal operator or prime, where most correct answers for that predicate use one | 0 | 35 |

- All 20 S2 matches drawn at random from the wrong bin were confirmed by hand. Each scopes an existential over an implication where a universal, or an implication outside the existential, was intended. For example: `all c:Class, g:Group | some t:Teacher | some c.Groups.g implies …`.
- The 6 matches in the correct bin are semantically harmless:
  - five instances of `eventually some f:File | f not in Trash implies f in Trash`, which is equivalent to `eventually some f | f in Trash`;
  - one with a trivially true antecedent.
- S2 is a heuristic: the scope test is textual. Basis: execution + manual inspection.
- **Analyzer warnings.** 235 non-error executions carried a relevance warning ("always yields an empty set" or "irrelevant"). The join warning is emitted by `ExprBinary.java` in Alloy 6.2.0:

```java
// AlloyTools/org.alloytools.alloy @ 59ba2033993449d483d54acad0e11a7bbf20354f
// org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/ast/ExprBinary.java:602-604
            case JOIN : {
                if (warns != null && type.hasNoTuple())
                    w = warn("The join operation here always yields an empty set.");
```

At default-branch head `ed89fdb16c58aea17a55e312c44f99e31aa63ee1` the same statement is at line 605. Basis: source.

### 3. Real faulty Alloy models (ARepair benchmark)

- The ARepair README states: "38 real faulty Alloy models with labeled faults from Amalgam and graduate students. These models are derived from 12 models". Nineteen of the 38 are `student1`–`student19`, all variants of one sorted-linked-list assignment.
- Each faulty file carries `// Fix:` comments. An explicit ordered rule list (`arepair_classify.py`, §Evidence) classified all 71 annotations, found in 37 of the 38 files (`student5.als` has none).

| Defect class (first matching rule) | Count | Typical fix text |
|---|---|---|
| Relational expression: closure, transpose or navigation path | 19 | `replace "c.^ext" with "c.^~ext"`; `replace "^~(left + right)" with "*~(left + right)"` |
| Missing emptiness guard before navigating a partial relation | 18 | `replace "n.elem <= n.link.elem" with "some n.link => n.elem <= n.link.elem"` |
| Missing constraint (adds a conjunct, fact or field restriction) | 12 | `add "no iden & neighbors"`; `add "nxt = ~pre"` |
| Quantifier, multiplicity or comparison keyword | 9 | `replace "one" with "lone"`; `replace "lone" with "some"` |
| Connective confusion | 8 | `replace "=>" with "<=>"`; `replace "\|\|" with "&&"` |
| Other multi-part rewrite | 3 | `replace "result = #x" with "result = #{n: … \| n.elem = x}"` |
| Over-constraint (deletes or weakens) | 2 | `replace "Array.length = #Element" with "Array.length >= 0"` |

- The guard class appears in 15 of the 19 student files and in 3 of 4 `dll` files.
- It is the same root mechanism the analyzer's empty-join warning targets. Navigating a lone field yields the empty set, and an arithmetic comparison over the empty set does not fail. Reviewers therefore see a plausible formula with a silent edge case.
- The rules are approximate. For example, `farmerFaulty`'s two state-update fixes, which are frame-condition-like, fall into "relational expression".
- Basis: source (annotations) + derived (classification).

### 4. Misconception classes, detection mechanisms, and probe results

| Class | Field evidence | Mechanism that exposes it | Probe on a real analyzer (toy spec) |
|---|---|---|---|
| Vacuous implication or over-constrained context | S1 (165) and S2 (373) in Alloy4Fun; ARepair guard class (18) | A non-vacuity witness: `run` the antecedent or the facts | `check MarkedNodesAcyclic for 5` found **no counterexample**; `run AntecedentSatisfiable { some Marked } for 5` was **unsatisfiable**, exposing the vacuity. 0.54 s wall, 112 MB peak RSS |
| Quantifier-order slip (∀∃ vs ∃∀) | Temporal analogue: Greenman `BadStateQuantification`, misuse or swap of F/G/U (Eng→LTL counts 22/1/2) | An equivalence check against the intended reading | `check SwapIsEquivalent for 3` gave a counterexample in **53 ms** solver time; the valid direction `SwapOneWay` had none |
| Missing frame condition | ARepair `farmerFaulty` state-update fixes; field prevalence not measured | Safety check over traces | `deleteUnframed` gave a counterexample in **65 ms** (3-state trace); `deleteFramed` had none in 1..10 steps. 1.26 s wall, 145 MB |
| Missing G / implicit F (LTL) | Greenman: `ImplicitG` was the most common authoring error (47/7/10); `WeakU` in half of Round 2 | Trace-satisfaction examples; model checking against intended traces | S3 found 35 temporal-operator-free wrong answers in Trash LTL |
| Missing fairness | AWS: "Failed to find a liveness bug as we did not check liveness" | Liveness property plus explicit `WF`/`SF` | TLC: `SpecNoFair` violates `<>(x = 3)`, with the trace stuttering at x = 2 (4 distinct states); `SpecFair` with `WF_vars(Next)` passes. 2.1–2.4 s wall |
| Omitted guarantee (spec too weak) | IronFleet exactly-once (Fonseca I1) | Implementation mutation that still verifies; proving extra properties | Not probed (needs the full system) |
| Tautological check | Chapar C4: "The check simply asserted the condition of the conditional branch" | Mutation of the checked code; vacuity linting | Not probed |

Basis: execution (probes) + documentation.

**What the probes establish.** Each seeded defect is caught in well under a second, but only by a query the reviewer must choose to write.

- The vacuous assertion passed its own check. The missing-fairness specification passes every safety check.
- Tools turn review into question-asking, and the question set becomes the new thing a reviewer must review.

Basis: derived from the probe outcomes.

### 5. Scenario exploration, provenance and specification testing

- **Amalgam** answers "why/why not" questions about an instance with proofs. The tool page says: "if an element of an instance cannot be consistently removed, Amalgam will say so and provide a justification in the form of a proof". Its stated limits: "does not currently support higher-order quantification … or arithmetic".
- **Minimal models, unsat cores, provenance.** Danas et al. found "most of the output forms fail to be effective, and in some cases even actively mislead users". This is evidence against assuming that tool output automatically raises review recall.
- **Sterling** (Dyer & Baugh, ABZ 2021, DOI 10.1007/978-3-030-77543-8_7) is a web visualizer with custom D3/Cytoscape views. It reports no user study: "being leveraged to develop user studies". The `alloy-js/sterling` README describes it as "Alloy extended to include visualizations generated using the alloy-js library".
- **Forge** builds specification testing into the language. From `forge/examples/oopsla24/f8_testing.frg` at `326400a735540d25f697336c7efbacd215b1800e`:

```text
example moveMiddleFirst is { wellformed } for wellformed_instance

test expect {
	{ someMoveTaken } for wellformed_instance is sat
}
test suite for winning {
	assert fullFirstRow is sufficient for winning for 1 Board
	assert someMoveTaken is necessary for winning for 1 Board
}
```

  (Excerpt; trailing whitespace trimmed and one blank line removed.)

  `is sufficient` and `is necessary` are directional implication tests, and `example` is a positive instance. Together they encode both the non-vacuity check and the over/under-constraint check from §4 as first-class, rerunnable artifacts. Basis: source.
- **Students cannot tell over- from under-specification.** The ABZ 2020 paper reports that students "found it hard to distinguish whether the provided counter-example represents a scenario where their solution was over-specified or under-specified". Ten of 13 respondents found counterexamples frequently useful. Four of those ten only found them useful when the atoms signalled whether the instance should have been accepted or rejected.

### 6. Specification defects in audited verified systems

| System or source | Spec size reviewers faced | Spec defects reported | Why they escaped |
|---|---|---|---|
| IronFleet (SOSP 2015; Fonseca 2017) | IronRSL high-level spec "only 85 SLOC" (IronKV 34), called "easy to inspect for correctness" | I1: no exactly-once requirement, so a 7-line patch disabling deduplication still verified | Omission. The developers' notion of linearizability excluded exactly-once, and they knew of the absence |
| Chapar (POPL 2016; Fonseca 2017) | Not reported | C4: client assertion "always evaluated to true" | Tautology in a test-level specification |
| Verdi (PLDI 2015) | Raft (linearizability) spec 170 lines, implementation 520, proof 4,144 | None in Fonseca's study; Verdi's bugs V1–V8 were all shim-layer bugs | Not applicable |
| seL4 (SOSP 2009) | Abstract spec 4,900 Isabelle lines vs 8,700 lines of C | First refinement: "some 300 changes in the abstract spec and 200 in the executable spec. About 50% of these changes relate to bugs" | Found by proving refinement, not by reading |
| seL4 (TOCS 2014) | 480,000 lines of proofs and specs | The information-flow proof required "making the abstract specification deterministic" (part of ≈18.5 pm) | Properties were proved rather than read: "it is not enough to simply read the abstract specification" |
| AWS (2014 preprint of the CACM 2015 paper) | 6 tabulated specs, 102–939 lines, 3,031 in total (derived) | A DynamoDB bug with a 35-step trace "passed unnoticed through extensive design reviews, code reviews, and testing"; a reviewed fix was still wrong | Behavior depth; unchecked liveness |
| MongoRaftReconfig (CPP 2022) | Spec 359 lines; invariant 140 lines, 20 conjuncts; 3,189-line proof | "we did not discover any errors in our inductive invariant during the TLAPS proof process" | Not applicable. TLC was used beforehand to probabilistically find counterexamples to induction |
| TLA+ Examples `CheckpointCoordination` | Not applicable | "a 12-step error trace for a very subtle bug introduced by an attempted optimization" | Reproduced by `MCCheckpointCoordinationFailure.cfg` (manifest result `safety failure`) |

Basis: documentation (each row's paper) + source (Examples README and manifest).

**Synthesis (derived).** Every reported spec defect that survived human reading fits one of three shapes:
- something missing (I1, liveness not checked);
- something trivially true (C4, vacuity);
- something reachable only by a long behavior (35 steps, 12 steps).

None of these produces a visibly wrong line. The mechanisms that found them were all adversarial:
- implementation mutation (Fonseca's tool needed 377, 18 and 8,015 iterations on average to generate patches);
- proof obligations that forced changes to the specification (seL4);
- model checking (AWS, CheckpointCoordination).

Fonseca et al. recommend tests for specifications "built by developers that did not write the specification".

### 7. Size and structure of real specifications

**seL4 abstract specification** (`spec/abstract/` at `b0fe7693…`, measured with the script in §Evidence; comments `(* … *)` and `text ‹…›` blocks stripped for the non-comment count):

| Slice | Files | Lines | Non-comment non-blank lines | `definition`/`fun`/`primrec`/`function`/`abbreviation` | `record`+`datatype` |
|---|---|---|---|---|---|
| Generic part | 24 | 7,798 | 4,919 | 460 | 35 |
| Generic + AARCH64 | 43 | 10,903 | 7,173 | 717 | 59 |
| Generic + ARM | 40 | 10,314 | 6,737 | 639 | 56 |
| Generic + RISCV64 | 40 | 9,752 | 6,254 | 633 | 52 |
| Generic + X64 | 41 | 10,940 | 7,042 | 687 | 68 |

- The 2009 paper reports 4,900 lines for the abstract spec. The counting rule behind that figure is not stated, so the roughly 2× growth is indicative only.
- The kernel entry point is a single dispatch function. `spec/abstract/Syscall_A.thy:325` declares `handle_event :: "event \<Rightarrow> (unit,'z::state_ext) p_monad"`, followed by one equation per event kind (lines 327–361).
- Basis: execution (counting) + source.

**TLA+ Examples** (all 83 `manifest.json` files and 433 modules at `334c3983…`):
- 66,510 module lines: median 59 per module, 90th percentile 316, maximum 5,661 (`tcp/tcp_proof.tla`). 75 modules have TLAPS proof entries.
- 243 models: 210 success, 19 safety failure, 3 liveness failure, 11 unknown.
- Recorded runtimes (230 models): median 1 s, 90th percentile 60 s, maximum 26,160 s.
- `distinctStates` is recorded for 128 models: median 1,363, 90th percentile 54,944, maximum 1,321,761.
- Many failing models are deliberate puzzle encodings (DieHard, Einstein). Design-flaw ones include `CheckpointCoordination`, `acp/ACP_NB_WRONG_TLC.cfg` and `SDP_Verification`.
- Basis: execution (counting) + source.

**Review-load arithmetic (derived).** For a review rate R in non-comment non-blank lines per hour, reading takes L/R hours. R is **not measured** for any of these notations. Relative loads can still be computed:
- one seL4 architecture slice (7,173 lines) is about 84× IronRSL's 85-line spec and about 20× MongoRaftReconfig's 359-line spec;
- the largest AWS spec (939 lines) is about 11× IronRSL.

Any rate measured on 100-line Alloy predicates must be validated before it is extrapolated across two orders of magnitude.

### 8. Protocol for measuring human review rates of formal specifications

The design elements below are derived from §§2–7. They are what a study must fix to produce a review rate and recall/false-alarm figures that are interpretable.

1. **Unit of measure.** Report both non-comment non-blank lines and formalism-native statements:
   - Alloy: `fact`/`pred`/`assert`/`fun` paragraphs and field declarations;
   - TLA+: top-level definitions and top-level conjuncts of `Init`, `Next` and invariants;
   - Isabelle: definitions and their equations.

   Rates in different units are not interconvertible without a measured ratio (§7: about 1 definition-like item per 10 non-comment non-blank lines in seL4's abstract specification).
2. **Seeded-defect taxonomy.** Stratify by the field classes observed above:
   - (D1) missing guard on a partial navigation;
   - (D2) quantifier order or scope, including S2;
   - (D3) vacuity or an over-constraining fact;
   - (D4) missing frame condition;
   - (D5) temporal: missing `G`, weak vs strong until, missing fairness;
   - (D6) omitted guarantee (spec too weak, I1-style);
   - (D7) tautological check (C4-style);
   - (D8) closure or transpose direction;
   - (D9) connective (implies vs iff).

   D6 and D7 cannot be seeded as single-token mutants. They need hand-written deletions, so MuAlloy's 9 operators (MOR, QOR, UOR, BOR, LOR, UOI, UOD, BOE, IEOE) cover D2, D8 and D9 but not D6.
3. **Equivalence screening.** A seeded change that is semantically equivalent is not a defect. Screen every seed with a bounded equivalence check and, where possible, an unbounded proof.
   - Toy-model evidence: the probe generated 26 variants of 4 predicates. 24 were killed, 22 at scope 1 and 2 at scope 2. The two intended-equivalent rewrites (contrapositive; `no Trash & Protected`) survived scope 4.
   - MuAlloy's published evaluation found 151 equivalent among 1,034 mutants across 13 models (derived from its Table 2). Unscreened seeding would plant about 15% non-defects.
4. **Control specifications.** Include defect-free versions so the false-alarm rate per hour, and per 100 lines, is defined. Adjudicate reported issues blind against the seed list plus independently confirmed pre-existing defects.
5. **Reviewer strata.**
   - Novices: one course, comparable to Alloy4Fun participants.
   - Practitioners: at least one year of production use.
   - Authors of comparable specifications.

   The LTL study shows that expertise lowers but does not remove errors (English→LTL wrong 28% for researchers vs 47% for students).
6. **Conditions, in a crossover with counterbalanced specification and order (Latin square):**
   - (a) unaided reading;
   - (b) scenario explorer: visualizer and instance enumeration;
   - (c) counterexample-assisted: the reviewer may write `check`/`run` and TLC properties;
   - (d) test-assisted: a Forge-style `example`/`is necessary`/`is sufficient` suite is supplied.

   Condition (c) must log every query. §4 shows that detection depends on which query is asked, so the query log is the mechanism variable.
7. **Metrics.** Lines and statements reviewed per hour; per-class recall; false alarms per hour; time to first detection; confidence calibration.
   - Alloy4Fun-style derivation-tree logging, with every analysis timestamped, is a ready instrument. Its `em1920` schema is reusable as is.
8. **Sample size (derived arithmetic).** Under the normal approximation, estimating one recall p to within ±0.10 at 95% confidence needs about 1.96² · p(1−p) / 0.10² ≈ 96 reviewer–defect observations at p = 0.5, per stratum × condition × class cell of interest. That is impractical for nine classes. Pool classes, or pre-register a few primary contrasts.
9. **Ecological-validity guards.** Greenman et al. note that subjects "had to answer questions about abstract formulas, absent a concrete use-case, without access to a solver". Alloy4Fun was "only used for self-study and not for student grading". A review study must state both properties.

### 9. Performance and resource footprint across levels

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | Time for AWS engineers to learn TLA+ to useful results | "2 to 3 weeks" | documentation (2014 preprint) |
| L1 | seL4 abstract-spec authoring | 4 person-months for 4,900 lines, about 1,225 lines per person-month (derived) | documentation + derived |
| L1 | MongoRaftReconfig TLAPS proof | about 4 person-months for the proof plus 1–2 for the invariant; 3,189 lines in total | documentation |
| L1 | IronFleet total effort; proof-to-code ratio | about 3.7 person-years; 3.6:1 | documentation |
| L1 | Alloy4Fun first failure → first correct (novices) | median 1.5 min, 90th percentile 15.6 min | execution |
| L1 | LLM token or turn budgets for spec review | not measured | — |
| L2 toolchain build | Alloy and TLC built from source | not measured (prebuilt release jars used) | — |
| L3 analysis latency | Alloy solver time, toy counterexamples | 53 ms and 65 ms (receipt `duration`) | execution |
| L3 | Alloy CLI wall time per file, including JVM | 0.54–1.26 s; mutant screen of 104 checks: 1.97 s | execution |
| L3 | MuAlloy mutant generation and mutation testing per model | 1.0–8.2 s and 1.8–39.0 s | documentation |
| L3 | TLC toy fairness check, wall time | 2.10 s (violation), 2.42 s (pass) | execution |
| L3 | Editor/LSP responsiveness under 50 ms | not measured | — |
| L4 generated code | Not applicable: specifications here are not compiled to run-time code | known not to apply | — |
| L5 checking | TLC on `lamport_mutex/MCLamportMutex.cfg`, 1 worker | 2,729,079 states, 724,274 distinct, depth 61 (matches manifest exactly); 18 s and 36 s in two runs (about 152k and 76k states/s, derived) | execution |
| L5 | TLAPS check of MongoRaftReconfig | "approximately 38 minutes" on 8 Apple M1 cores | documentation |
| L5 | tlaplus/Examples recorded model runtimes | median 1 s; 90th percentile 60 s; maximum 7.3 h | source + derived |
| L6 footprint | Peak RSS: Alloy CLI | 111–145 MB | execution |
| L6 | Peak RSS: TLC | 75–272 MB toy; 1.78 GB for `MCLamportMutex` | execution |
| L6 | Tool artifacts | Alloy jar 21,062,377 B; `tla2tools.jar` 2,274,532 B | execution |
| L6 | Energy | not measured | — |

### 10. Comprehensibility and conceptual simplicity

- **C1, human vs. machine.**
  - Alloy's relational semantics make partial navigation total: an empty join instead of an error. That removes a whole error channel for the solver but adds a hidden case for the human. It accounts for 18 of 71 ARepair fixes and for the analyzer's dedicated warning.
  - LTL's implicit-`G` failure (most common authoring error) is the temporal analogue: the reader supplies an "always" that the formula lacks.
  - Both are nonlocal. Seeing the defect requires knowing what is absent.
- **C1, counterexample legibility.** Students could not classify a counterexample as over- or under-specification without accept/reject annotations. Forge's `example`, `is necessary` and `is sufficient` attach exactly that label to each instance. Danas et al. show that richer output alone can mislead.
- **C2, one invariant with several mechanisms.** "The specification is not vacuous" is enforced in at least five places:
  - Alloy relevance warnings;
  - ad-hoc `run` witnesses;
  - Forge `test expect … is sat`;
  - TLC deadlock checking;
  - seL4's "prove further properties".

  The minimal universal abstraction is a **witness obligation**. Every assertion or theorem ships with at least one satisfying and one falsifying instance of its antecedent context, checked by the same engine. This makes vacuity, over-constraint and the C4 tautology ordinary failures of one rule rather than three special cases.
  - Exception: I1-style omissions are not caught by witnesses. They need an independent property (here, exactly-once) that someone must think to state.

### 11. Validation of specifications and of review claims

- **V1, adequacy and non-vacuity.**
  - Implementation-mutation survival (Fonseca's 7-line patch) is the strongest observed discriminator for omitted guarantees.
  - Spec-mutation scores need equivalence screening (§8.3).
  - Bounded checking at scope 1–2 killed 24 of 24 non-equivalent toy mutants.
  - Seeds must also survive an unbounded check, because a bounded check cannot prove non-equivalence.
- **V2, checker soundness.**
  - Fonseca found 3 verifier bugs (Fig. 3; §6's text says four). One "caused the verifier to falsely report that any program passed verification checks". A review protocol that relies on a checker must include a known-false canary.
  - The TLC run in §9 reproduced the manifest's state counts exactly. This is a cheap differential check between the archived and current tool behavior.
- **V3, concurrency, crash and physical leakage.** Not examined. The cited audits found shim-layer crashes (9 of 11 shim bugs caused crashes or hangs) outside any specification.
- **V4, human mental models.** The LTL misconception catalog (11 tags, Cohen κ = 0.91 between coders) is the only coded instrument found. Alloy4Fun logs plus S1–S3 give a behavioral litmus test for Alloy. Neither has been applied to review.

## Boundaries

- **unknown**: human review rate, recall and false-alarm rate for Alloy, TLA+ or proof-assistant specifications. Not found in any source examined. A search-engine summary asserted a "30–60%" seeded-defect detection range with no source, and it is not used.
- **not examined**: full texts of the following. Only their abstracts, tool pages or blog posts were read, and no numbers from their bodies are used:
  - Danas et al. SEFM 2017;
  - Amalgam FSE 2017;
  - Forge OOPSLA 2024;
  - ARepair ASE 2018 (a search summary claiming "28 of 38 repaired" was not verified and is not used);
  - the Alloy4Fun journal version (SCP 2021, DOI 10.1016/j.scico.2021.102690);
  - Zimmerman et al. ICSE 2002.
- **not examined**: CACM 2015 print version of the AWS paper; its numbers are quoted from the authors' 29 September 2014 preprint and may differ in wording.
- **not examined**: TOCS 2014 §7.2.2 onward (effort and bug-count analysis), and QED at Large (Ringer et al. 2019) from §7.2 onward. The accessible part of QED at Large has no passage on specification bugs.
- **unknown**: why the CV `Inv4` and LTS `inv7` failure rates are 100% and 99%: task difficulty or oracle ambiguity.
- **unsupported extrapolation**: the dataset statistics describe novices *writing* predicates against a hidden oracle. They are not review data, and they do not transfer to experts reading Isabelle or TLA+ without a study.
- **heuristic**: S2/S3 and the ARepair rule classes are textual heuristics. S2's precision was checked on a random sample of 20, not exhaustively.
- **toy model**: all probe specifications (vacuity, quantifier order, frame, fairness, mutants) were written for this report. Their timings are properties of those toy specifications on the stated host, not of real specifications.
- **not measured**: L2 build times of Alloy, TLC, Isabelle or l4v; LSP latency; energy; LLM-assisted review cost.
- **known not to apply**: L4 generated-code performance (specifications are not executed as compiled code here).
- **not examined**: whether Sterling's or Forge's visualizations change review recall. No study was found. Sterling's paper explicitly defers user studies.

## Evidence

Observation date for all execution and source evidence: 2026-11-20 (UTC). The dataset files were last changed 2020-03-05; the wiki page describing them was deleted 2026-11-10.

**Dataset files** (wiki repository `https://github.com/haslab/Alloy4Fun.wiki.git`, `em1920/`; last changed by commit `886eba28b854`; identical at observed head `1478014567d9`). SHA-256:

```text
57d81ebe004d4ed1cc4340f35036cf4e14ecb2462ea69b5b9eaa8d39e30905ad  9jPK8KBWzjFmBx4Hb.json  (Trash LTL)
61e77b81244a8f9dc0f27c9e6305d10ecdf54a78432ace79924bcc4643967f3d  gAeD3MTGCCv8YNTaK.json  (Graphs)
f345123a4a582167b392e475de9279600c844c1c86358a0b8c52f9af88171273  JC8Tij8o8GZb99gEJ.json  (CV)
cfafffaeb965132eb704bd8ddc86aa830b8091752250ad4a3fce574a9a6bb36e  jyS8Bmceejj9pLbTW.json  (Production)
172f19423a55b2b19fb7617965a6ee5549f51591dd8dd19b406cc8726ac28852  PQAJE67kz8w5NWJuM.json  (Trash RL)
19b1537b5337f8faaf4720358c0f83b0ad5be6c2388b54a187916f74ddc345f4  sDLK7uBCbgZon3znd.json  (Trash FOL)
f690ca92e113da35e40f203f31c54d0bf12e89c1175f8ff21cdc41add313c21a  YH3ANm7Y5Qe5dSYem.json  (Classroom FOL)
8b5f2b0d5389017c617e5ca0f85fc2e01f6b43f7a67e0a68ec8ba37c615fc81e  zoEADeCW2b2suJB2k.json  (LTS)
708a7156a686db8900b59d6d609e6e08dbb2f903628caa63eda5864a11c5e07b  zRAn69AocpkmxXZnW.json  (Classroom RL)
```

**Recount script, core logic** (`a4f_stats.py`, run as `python3 a4f_stats.py em1920/`; 0.46 s):

```python
# predicate under test: strip "Ok"/"OK" from cmd_n; body = text between the braces of `pred <name> {`
# per entry: no 'sat' -> share; sat == -1 -> error; cmd_c true -> challenge check (sat 0 correct, 1 wrong)
TEMPORAL = re.compile(r"\b(always|eventually|after|until|releases|historically|once|before|since|triggered)\b|'")
class _SomeImplies:  # S2: `some ... |` then, on the same line and before any unmatched ')', `implies` or `=>`
    _q = re.compile(r"\bsome\b[^|\n]*\|"); _imp = re.compile(r"\bimplies\b|=>")
    def search(self, body):
        for m in self._q.finditer(body):
            depth, rest = 0, body[m.end():].split('\n', 1)[0]
            for i, ch in enumerate(rest):
                if ch == '(': depth += 1
                elif ch == ')':
                    depth -= 1
                    if depth < 0: break
                elif self._imp.match(rest, i): return True
        return False
# attempts: for each sat==0 challenge check, walk derivationOf ancestors with the same cmd_n,
# counting sat==1 until an earlier sat==0; skip re-checks (earlier correct, zero failures);
# elapsed = time(correct) - time(earliest counted failure)
```

**ARepair classifier** (`arepair_classify.py`). Rules, first match wins, over `// Fix:` text:
1. a `some n.<f> =>` or `no n.<f> ||` guard is introduced → guard;
2. the text starts with `add`/`move field`/`restrict` → missing constraint;
3. `delete`, or `= #Element` weakened → over-constraint;
4. the original is exactly one of `=> <=> || &&` → connective;
5. the original is one keyword among `lone some one all no in = != !in > <` → keyword;
6. the original contains `^ * ~ + .field` → relational;
7. otherwise → other.

Input: `experiments/realbugs/*.als` at `dacd87d1fa3de4017f6c415f72ab6466211e6150`.

**Alloy probes** (`java -jar alloy-6.2.0.dist.jar exec -q -f -c '*' -o out <file>.als`; outcome read from `out/receipt.json`, where a command with a `solution` key is satisfiable):

```alloy
sig Node { next: lone Node }
sig Marked in Node {}
fact Housekeeping { no Marked }
assert MarkedNodesAcyclic { all n: Marked | n not in n.^next }
check MarkedNodesAcyclic for 5                          -- result: no counterexample
run AntecedentSatisfiable { some Marked } for 5         -- result: no instance (vacuity exposed)

sig Person { loves: set Person }
pred everyoneLovesSomeone { all p: Person | some q: Person | q in p.loves }
pred someoneLovedByAll   { some q: Person | all p: Person | q in p.loves }
assert SwapIsEquivalent { everyoneLovesSomeone iff someoneLovedByAll }
check SwapIsEquivalent for 3                            -- counterexample, duration 53 ms

sig File {}
var sig Trash in File {}
var sig Protected in File {}
pred deleteUnframed[f: File] { f not in Protected and Trash' = Trash + f }
pred deleteFramed[f: File]   { f not in Protected and Trash' = Trash + f and Protected' = Protected }
pred init { no Trash }
assert UnframedSafe { (init and always (some f: File | deleteUnframed[f])) implies always (no Trash & Protected) }
check UnframedSafe for 3 but 1..10 steps                -- counterexample, duration 65 ms
```

Writing `(init and always some f: File | …)` without parentheses around the quantifier is a syntax error in Alloy 6.2.0: "There are 35 possible tokens that can appear here".

**Mutant screen** (`mutants.py`):
- Model: `sig File { link: set File }`, with `Trash` and `Protected` as subsets of `File`.
- References:
  - `all f: File | f in Trash implies f not in Protected`;
  - `all f: File | lone f.link`;
  - `all f, g: File | (f in Trash and f->g in link) implies g in Trash`;
  - `some g: File | all f: File - g | f->g in link`.
- Operators applied one occurrence at a time: all↔some, implies→and/iff/or, in↔not in, and→or, lone→one/some, dropping `- g`, and the converse of the top-level implication.
- Extras: the contrapositive, `no Trash & Protected`, and a quantifier-order swap.
- Each variant is checked with `check { m iff ref } for N`, N ∈ {1, 2, 3, 4}.
- Output: `mutants=26 killed=24 equivalent_within_scope4=2 min_killing_scope_hist={1: 22, 2: 2} checks=104 wall_s=1.97`.

**TLC probes** (`java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -workers 1 -metadir <dir> -config <cfg> <module>`):

```tla
---- MODULE Fair ----
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x < 3 /\ x' = x + 1
SpecNoFair == Init /\ [][Next]_vars
SpecFair   == Init /\ [][Next]_vars /\ WF_vars(Next)
Done == <>(x = 3)
====
```

- Configurations: `SPECIFICATION SpecNoFair` (respectively `SpecFair`), `PROPERTY Done`, `CHECK_DEADLOCK FALSE`.
- NoFair output: "Error: Temporal properties were violated." The trace is x = 0, 1, 2, then "State 4: Stuttering".
- `MCLamportMutex` run: printed "2729079 states generated, 724274 distinct states found … depth … 61"; first run "Finished in 18s", second run "Finished in 36s" with `maxrss=1784308KB`.
- Input SHA-256: `MCLamportMutex.tla` `2ebf6f863f504f76cfcb4a3bc8228aae1c5a896e7f2f8d046f8ab763656ccca8`; `MCLamportMutex.cfg` `b91d46fb0a2f3af22fa65147c4c971d5cb9e42d141f63ad9035aa30cad51d118`.
- Two earlier invocations (one per model) printed "TLC threw an unexpected exception" and nothing else. Reruns of the same commands succeeded. The cause was not investigated, and those runs are excluded.

**Profiles.**
- seL4: `spec/abstract/**/*.thy` downloaded at `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e` (109 theory files listed by the git tree API). Lines were counted after stripping nested `(* *)` comments and `text \<open>…\<close>` blocks. Keywords were counted with the regex `^\s*<keyword>\b`.
- tlaplus/Examples: the git tree at `334c3983a2f44ac78fce89d1d20aa79ceb3e6987` (not truncated); all `manifest.json`, `.tla` and `.cfg` files were fetched and aggregated in Python.

**Literature (DOIs checked against Crossref metadata on the observation date).**
- **Corrected identifiers.** Some commonly circulated identifiers for these works are wrong:
  - Amalgam is DOI 10.1145/3106237.3106272.
  - MuAlloy is 10.1145/3183440.3183488.
  - Sterling is 10.1007/978-3-030-77543-8_7.
  - The CPP 2022 paper by Schultz, Dardik and Tripakis is titled "Formal Verification of a Distributed Dynamic Reconfiguration Protocol" (DOI 10.1145/3497775.3503688, arXiv:2109.11987).
  - ARepair's title is "Automated model repair for Alloy" (DOI 10.1145/3238147.3238162).
- Klein et al., TOCS 32(1), DOI 10.1145/2560537; Klein et al., SOSP 2009, DOI 10.1145/1629575.1629596.
- Newcombe et al., CACM 58(4):66–73, DOI 10.1145/2699417. Quotes are from the authors' 2014 preprint "Use of Formal Methods at Amazon Web Services".
- Fonseca et al., EuroSys 2017, DOI 10.1145/3064176.3064183. Revised version of 7/24/2017; key sentences cross-checked against the proceedings copy.
- Hawblitzel et al., IronFleet, SOSP 2015, DOI 10.1145/2815400.2815428; Wilcox et al., Verdi, PLDI 2015, DOI 10.1145/2737924.2737958; Lesani et al., Chapar, POPL 2016, DOI 10.1145/2837614.2837622.
- Ringer et al., QED at Large, DOI 10.1561/2500000045, arXiv:2003.06458.
- Macedo et al., ABZ 2020, DOI 10.1007/978-3-030-48077-6_5 (open access; tables 2–3 are images and were not read); the SCP 2021 journal version, DOI 10.1016/j.scico.2021.102690; precursor arXiv:1907.02275.
- Greenman et al., DOI 10.22152/programming-journal.org/2023/7/7, arXiv:2211.01677.
- Danas et al., SEFM 2017, DOI 10.1007/978-3-319-66197-1_11.
- Nelson et al., Forge, PACMPL 8(OOPSLA1), DOI 10.1145/3649833.
- Jovanovic & Sullivan, arXiv:2402.06624.

## Revalidation

- **Dataset**:
  1. Clone `https://github.com/haslab/Alloy4Fun.wiki.git`.
  2. Verify the nine SHA-256 values.
  3. Rerun the recount logic.

  Expected: `10949 / 10781 / 3081 / 7682 / 4000` and S2 `6 / 373`. Any change to the files invalidates §2. Note that the wiki's description page is already gone.
- **Alloy behavior**: rerun the three probe files on a new Alloy release. The discriminating outcomes are:
  - `MarkedNodesAcyclic` has no counterexample while `AntecedentSatisfiable` has no instance;
  - `SwapIsEquivalent` and `UnframedSafe` each have a counterexample.

  Also grep `ExprBinary.java` for `always yields an empty set` to confirm the warning still exists.
- **TLC**: run `Fair.tla` with both configurations, and `lamport_mutex/MCLamportMutex.cfg` from the pinned Examples revision. Distinct states must equal 724,274; compare the manifest's `distinctStates` for any other revision.
- **Spec profiles**: re-run the line and keyword counts on a newer l4v or Examples revision. Diffing `manifest.json` results (`safety failure`/`liveness failure`) shows new documented failing models.
- **Review-rate evidence**: search for new studies by searching for "seeded defects" with "Alloy", "TLA+", "Isabelle" or "specification review". Any such study supersedes the **unknown** entries in §1. Check it against the §8 design elements.
