# Empirical cost of Rust ownership and lifetimes: learning studies, a garbage-collection trial, the Ownership Inventory, Aquascope, lifetime-annotation density, and C-to-Rust pointer-kind recovery

## Summary

- **Lifetimes, not moves, are the best-measured source of difficulty.** On 100 Stack Overflow questions about Rust's safety rules (118 violations), 77 violations stem from lifetime computation and 41 from ownership rules. In a 101-respondent survey, 85.1% were at least "sometimes" confused by lifetime rules, against 52.4% for ownership rules, and 10.0% against 39.6% could "always" understand the corresponding compiler errors. Of 30 inter-procedural lifetime violations, 14 involve an *elided* annotation (Zhu et al. 2022). In the Ownership Inventory's formative study, readers who had finished the official book predicted the compiler error correctly in 10% and 38% of cases for the two lifetime-parameter programs, against 78% on the other six programs (Crichton, Gray and Krishnamurthi 2023). `Basis: documentation (peer-reviewed papers, full text read)`.
- **Onboarding time is self-reported, and only from enthusiast samples.** In a Rust-community survey (n = 178), the time to write a compilable program without frequently resorting to `unsafe` was under one week for 27%, one week to one month for 41%, and one to six months for 25%. Six respondents could not yet do it; 59% found Rust harder to learn than other languages, and 92% rated its error messages good or very good (Fulton et al. 2021). No study measured onboarding time with a stopwatch on a representative population.
- **The randomized trial of an optional garbage collector does not isolate the borrow checker.** On a 633-student course (333 analysed), the authors found no completion or time difference on the *ownership* task, and no difference in total time. The *aliasing* task took a median of 4 h with the collector against 12 h without; times are self-reported. The authors attribute much of that gain to "architectural simplification", and 40 of the 41 withdrawals were from the collector arm (Coblenz, Mazurek and Hicks 2022).
- **Teaching changes are measurable, but only through temporal, non-randomized designs.** A rewritten ownership chapter raised the Ownership Inventory score from 48% to 57% (N = 177 before, 165 after; d = 0.56). Quiz telemetry from 62,526 book readers drove 12 local text interventions, which gained 20 points on average (d = 0.45); "rules of lifetime inference" went from 0.26 to 0.40 (Crichton and Krishnamurthi 2024).
- **Aquascope shows permissions, not lifetime parameters.** At `cognitive-engineering-lab/aquascope@f2d0a06…`, the tool shows Read, Write and Own ("drop" in the source) permissions per place, the loan or move that removed each one, and per-step permission diffs. These are computed from Polonius facts. Its region-flow analysis for lifetime-parameter errors exists, but is off by default (`ENABLE_FLOW_DEFAULT: bool = false`). This matches the paper's admission that its model "does not soundly approximate lifetime parameter errors". `Basis: source + documentation`.
- **Hand-written annotation density (measured; syntactic; 14 library crates; 15,156 signatures).**
  - 6.3% of function signatures write a named lifetime, and 2.6% declare a function-level lifetime parameter.
  - 91.9% of reference positions in signatures are elided.
  - 1.1% of signatures (164) carry an output lifetime that the elision rules cannot determine, so they would hit `E0106` if their lifetimes were stripped. The per-crate share ranges from 0% to 8.5%.
  - `Basis: execution (syn-based counter over pinned sources)`.
- **Automatic ownership recovery from C converts a minority of raw pointers, measured in incompatible ways.**
  - Laertes (Emre et al. 2021) targets only raw pointers whose sole cause of unsafety is lifetimes, which are 8.1% of raw-pointer declarations. It fixed 1,630 of 2,144 of them (76%), plus 87% of their dereferences.
  - Crown (Zhang et al. 2023) reports median reductions of 37.3% of mutable non-array raw-pointer declarations and 62.1% of their uses. It synthesizes **no** lifetimes.
  - Once all pointers are made eligible, the same Laertes-style inference makes only 12% of declarations safe (21% with inserted casts; Emre et al. 2023).
  - These rates are not comparable with each other, or with the hand-written density above.

## Applicability

This report concerns the *field* cost of Rust's ownership and lifetime discipline, and how much ownership structure tools recover from code written without it. It does not concern the formal design of inference or elision algorithms.

Subjects and their relation:

- **Peer-reviewed studies** (Crichton 2020; Fulton et al. 2021; Zhu et al. 2022; Coblenz et al. 2022; Crichton et al. 2023; Crichton and Krishnamurthi 2024; Emre et al. 2021; Zhang et al. 2023; Emre et al. 2023). These are the primary evidence. Every number attributed to them was read from the full text; locators are in **Evidence**. Their populations are fixed: Stack Overflow askers, Rust forum users, one university course, and readers of a fork of *The Rust Programming Language*. Nothing here extends their findings to other populations.
- **`cognitive-engineering-lab/aquascope` at `f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`**: the visualizer described (unnamed) in Crichton et al. 2023. It is examined as source only and was not built or run. Its `rust-toolchain.toml` pins `nightly-2026-05-01`.
- **`cognitive-engineering-lab/rust-book` at `88250e0392cef0622f318e35469108d68694c1f7`**: the book fork whose `quizzes/` directory holds the instruments used by the two Crichton papers. The instrument counts below are of this revision. The papers' deployments ran earlier (2022–2023), and the counts differ (see Findings §5).
- **`KomaEc/crown` at `621904cd356b433215d5f55db39ffd71714f44ff`** and **`immunant/c2rust` at `a4837814f1ae7650fae0c7eccb9bdbbf2b1aef20`** (`c2rust-analyze/`): pointer-kind analyses, examined as source. Neither was run. Crown's README says the refactoring functionality lives on a separate `artifact` branch, which was not examined.
- **`rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`**: the normative-in-practice text of `E0106` (`compiler/rustc_error_codes/src/error_codes/E0106.md`). **rustc 1.100.0** (commit `0ef1bc386059596dada8fb65b50425aab2ea637a`) was executed for the `E0106` diagnostic probe.
- **Fourteen library repositories**, pinned in `REPORT.json`: the input to the annotation-density pilot. This is a *convenience sample* of widely depended-upon library crates, not a random or representative sample. Application code, `unsafe`-heavy systems code, async-heavy services, and generated code are not represented in proportion. Only each crate's library source directory was counted (see Findings §8).

Exact observation versus broader claims:

- The density numbers are exact for the pinned sources and the stated syntactic definitions.
- The book-quiz counts are exact for the pinned fork.
- All study results are as reported by their authors, for their populations.
- No claim here says how a different language design would fare. The studies do not measure that.

## Findings

### 1. Study designs and what each can attribute to ownership

| Study | Population (n) | Instrument | Can attribute to borrow checking? |
|---|---|---|---|
| Crichton 2020, *The Usability of Ownership* (HATRA workshop) | none (position paper) | experience and examples; cites the 2018 Rust survey only qualitatively | No primary data. The paper contains no percentages. |
| Fulton et al. 2021 (SOUPS) | 16 interviews (Feb–Jun 2020); survey of 178 complete responses out of 203 (Jul–Sep 2020), recruited from Rust forums | semi-structured interviews; descriptive survey statistics with no hypothesis tests | Partly. Seven interviewees named "the borrow checker and the overall shift in programming paradigm" as the biggest challenges. There are no per-concept percentages, and the recruitment "likely … overrepresent[s] Rust enthusiasts". |
| Zhu et al. 2022 (ICSE) | 15,509 Stack Overflow questions (large set); 100 safety questions reproduced offline (118 violations); survey of 101 valid responses out of 502 | Latent Dirichlet allocation (LDA) topic modelling; manual root-cause and fix coding; cognitive task analysis of error messages against rustc 1.50.0; survey with program variants | Yes, for compile-time rule violations, which are classified by rule. Stack Overflow questions "may be more difficult than programming errors in daily practice". |
| Coblenz et al. 2022 (ICSE) | 633-student course; 385 enrolled, 333 analysed (139 with the collector, 194 without) | Randomized at consent; 3 tasks graded by unit tests; self-reported times; Fisher and Wilcoxon tests with Holm–Bonferroni correction | Only for the aliasing-heavy task, and the authors attribute the gain to architecture (GC references vs `Rc<RefCell<…>>`) as much as to borrow checking. |
| Crichton et al. 2023 (OOPSLA) | formative N = 36; evaluation N = 177 before / 165 after | 8-program Ownership Inventory (prediction, counterexample, and fix questions); temporal A/B test of a rewritten chapter | Yes for conceptual understanding, but not randomized: "temporal correlations in readership could have affected our results". |
| Crichton and Krishnamurthi 2024 (OOPSLA) | 62,526 readers, 1,140,202 answers, Sep 2022–Oct 2023 | Embedded quizzes; classical test theory (CTT) plus a 3-parameter logistic (3PL) item response theory model; 12 interventions | Intervention effects per question; no per-concept ranking for ownership or lifetimes. |

`Basis: documentation (full text of each paper)`.

### 2. Which concepts are hardest: the quantitative evidence

| Measure | Lifetimes | Ownership, moves and borrows | Source |
|---|---|---|---|
| Safety-rule violations in 100 Stack Overflow programs | 77 of 118 (44 intra-procedural, 30 inter-procedural, 3 syntax) | 41 of 118 (18 move, 23 borrowing) | Zhu et al. §3.2, Table 2 |
| LDA question groups in the 15,509-question set | 790 lifetime-related | 28 move, 848 borrowing | Zhu et al. §3.3.1 |
| Survey: at least "sometimes" confused | 85.1% | 52.4% (χ²(1) = 23.6, p < 0.001) | Zhu et al. §4.2.1 |
| Survey: "always" understand the compiler error | 10.0% | 39.6% (χ²(1) = 22.4, p < 0.001) | Zhu et al. §4.2.1 |
| Elision involved | 14 of 30 inter-procedural lifetime violations happen at an elided annotation | — | Zhu et al. §3.2.1 |
| Error messages missing key information | 51 of 110 violations; 32 fail to explain "key steps in computing a lifetime or a borrowing relationship", 10 fail to relate two lifetime annotations | (9 fail to explain how a rule applies to a construct) | Zhu et al. §3.4 |
| Inventory error prediction (Q1) | `concat_all` 10%, `add_displayable` 38% | 78% averaged over the other six programs | Crichton et al. §2.5, Table 1 |
| Inventory fix (Q3a) | 43% and 6% | 12%–80% | Crichton et al. Table 1 |
| Wrong "fix" adopted | 12 of 16 added `+ 'static` to `T`, the fix that the compiler error itself suggests; one gave the idiomatic fix | 2 of 16 cloned the input vector, which silently broke `reverse` | Crichton et al. §2.4.2 |
| Self-reported challenge comments in the course | 204 of 340 reference-related comments concern lifetimes | 199 participants said ownership was challenging (76 about borrowing) | Coblenz et al. §6 |

Error codes: Zhu et al. map 103 of 110 violations to 20 distinct codes. Only `E0382` (use after move, 19 occurrences) is counted individually. Per-code counts for `E0499`, `E0502`, `E0505`, `E0597`, `E0106` and `E0373` are **not reported**. `Basis: documentation`.

Derived observation: the elision share (14 of 30) and the Inventory lifetime-parameter scores both point at function signatures. Signatures are where a signature-only interface forces the programmer to state an origin relation that local defaults cannot infer. `Basis: derived` from the two rows above. Neither study tested this causal reading.

### 3. Onboarding time and error-message usefulness

Fulton et al. 2021, §6.2 and §6.3 (survey n = 178, self-selected):

| Item | Result |
|---|---|
| Time to "quickly and easily write a program that compiled and ran (without frequently resorting to the use of unsafe blocks)" | < 1 week 27%; 1 week–1 month 41%; 1–6 months 25%; 6 respondents not yet |
| Found Rust harder to learn than other languages | 59% (7 interviewees) |
| Rust code takes longer to get to compile | 55% |
| Error messages good or very good relative to the respondent's reference language | 92% (87% of the 47 beginners) |
| Descriptive errors are a major problem-solving benefit | 97% |
| Dislike long build times | 55% |
| Learning difficulty is a top organizational concern | 50% |

The survey also asked how long it took to feel comfortable writing small, large, library and application code. The paper reports **no results** for that item. One interviewee reported being comfortable at about three months and "really solid" at about six. `Basis: documentation`.

The positive message ratings and the 10.0% "always understand lifetime errors" figure coexist. The likely reading is that messages are rated well overall, while lifetime-specific errors remain opaque. Zhu et al.'s enhanced message for array borrowing improved an objective score from 0.56 to 0.78 (p = 0.015), but did not improve the inter-procedural lifetime variant. `Basis: documentation + derived`.

Executed illustration (rustc 1.100.0): for `fn longest(x: &str, y: &str) -> &str`, the compiler emits `E0106`. Its explanation reads "this function's return type contains a borrowed value, but the signature does not say whether it is borrowed from `x` or `y`". It suggests `longest<'a>(x: &'a str, y: &'a str) -> &'a str`, which unifies *both* inputs. That is the over-constraining direction, analogous to the `+ 'static` suggestion that misled Inventory participants. `Basis: execution` (`support/probes/e0106_two_inputs.rs` and its `.stderr`).

### 4. The Bronze randomized controlled trial

Coblenz, Mazurek and Hicks 2022:

- Bronze is a precise mark-and-sweep collector that finds roots through LLVM stack maps emitted by a modified rustc. The experiment used "a version of Bronze that never collects", so there are **no runtime or memory measurements**.
- Design: randomized to the Bronze or Traditional condition at consent. The tasks were Basics, Ownership (references, iterators, options, mutable vectors), and Aliasing (a turtle graph with children, mutable parents and a name cache). Bronze participants then repeated Aliasing without the collector.
- Completion (Fisher's exact test on the 90% confirmatory split, 301 participants):
  - Ownership: p ≈ 1.00.
  - Aliasing with GC vs Traditional: p ≈ .006, odds ratio ≈ 0.41 for finishing without Bronze.
  - All parts: p ≈ .51.
- Times (149 finishers, Wilcoxon tests; **self-reported**):
  - Ownership: no difference (p ≈ 1).
  - Aliasing: median 4 h with Bronze vs 12 h Traditional (W = 561, p < .001).
  - Total: no difference, because the Bronze group's repeat of Aliasing without GC took a median of 8 h.
- Attribution in the authors' own words: "Even with GC, Rust learners need to understand ownership, borrowing, and lifetimes"; "a significant part of the benefit of GC in Rust programs is the architectural simplifications it enables and promotes".
- Threats:
  - 40 of the 41 withdrawals came from the Bronze arm, which may leave a stronger Bronze group.
  - Course grade predicted enrolment.
  - A co-author taught the course.
  - A soundness bug in `GcRef` (`Deref` could create multiple `&mut`) was found during review. The fix was re-applied to 43 submissions.

`Basis: documentation`. The trial cannot be read as "the borrow checker costs 8 hours". It compares a collector-backed reference type with an `Rc<RefCell<…>>` design on an aliasing-heavy task.

### 5. The Ownership Inventory, quiz profiling, and the instruments at the pinned book revision

Inventory construction (Crichton et al. 2023, §2.2–2.3):

- The top 50 "Most Frequent" `[rust]` Stack Overflow questions were filtered to 27 about ownership, which yielded 8 programs in 4 categories: dangling pointers, overlapping borrows, illegal borrow promotion, and lifetime parameters.
- Each program carries three questions: predict the error (Q1), write a counterexample assuming the compiler accepted the program (Q2a/b), and fix it while preserving intent and performance (Q3a/b).
- Coding agreement was 91% raw, κ = 0.81. Participants had up to 15 minutes per program.
- The evaluation used 24 multiple-choice versions placed at the ends of Chapters 6, 8, 10 and 17. Pre-intervention data ran 45 days from Dec 2022; post-intervention data ran 45 days from 15 Jun 2023.
- Results: 48% → 57%, p < 0.001, d = 0.56, with significant effects on 10 of 18 questions.
- The permissions model the chapter teaches: paths have R/W/O permissions, borrows remove and grant them, and the model soundly approximates Polonius access errors ("access-error G ⊢ permission-error G", Appendix A.2). Lifetime-parameter errors are explicitly outside the sound fragment.

Profiling (Crichton and Krishnamurthi 2024):

- 62,526 readers and 1,140,202 answers over 13 months; median 6 answers per reader.
- "even for triers, most did not make it past Chapter 4", the ownership chapter.
- Question authoring took about 50 person-hours. Readers spent a median of 29 s per question.
- CTT reader ability had mean 0.70 (σ 0.16), and question difficulty mean 0.63 (σ 0.24).
- Tracing questions whose answer is "does not compile" discriminated poorly: 6 of the 20 low-discrimination items, against 0 of the 20 high-discrimination items.
- Ten of the 12 interventions were significant after Benjamini–Hochberg correction. Ownership-related rows:
  - "Match expressions and ownership": 0.39 → 0.74.
  - "Rules of lifetime inference": 0.26 → 0.40.
  - "String slice diagram": 0.23 → 0.43.
  - "Dereferencing vector elements": 0.15 → 0.18, not significant.
- The paper reports no per-concept ranking for moves, borrows, lifetimes, or elision.

Instrument counts at `rust-book@88250e0…` (`Basis: execution`; parsed with Python `tomllib` by `support/count_quizzes.py`):

| Quiz group | Files | Questions | Types |
|---|---:|---:|---|
| All `quizzes/*.toml` | 93 | 222 | 141 multiple choice, 64 tracing, 17 short answer |
| Chapter 4 (ownership, references, fixing ownership errors, slices, recap) | 9 | 31 | 23 multiple choice, 6 tracing, 2 short answer |
| `ch10-03-lifetimes-sec1/2` | 2 | 5 | 4 multiple choice, 1 tracing |
| Ownership Inventory files (`ch06-04`, `ch08-04`, `ch10-04`, `ch17-04-inventory.toml`) | 4 | 21 (6 + 6 + 6 + 3) | all multiple choice |

The pinned revision holds 21 Inventory questions, whereas the 2023 paper deployed 24. The paper's question totals (221 in §1, 213 in §2.3.1) also differ from the 222 counted here. The difference is not explained in the sources examined. Revisions after the deployments probably edited the quizzes, so treat the counts as describing the current instrument, not the one analysed.

### 6. What Aquascope exposes (source at `f2d0a06…`)

| Concept | Shown? | Mechanism (file) |
|---|---|---|
| R/W/O permissions per place, at each use ("boundaries": expected vs actual) | yes | `PermissionsData` with fields `type_droppable`, `type_writeable`, `type_copyable`, `is_live`, `path_uninitialized`, `path_moved`, `loan_refined`, `loan_drop_refined`; read = initialized ∧ ¬read-refined; write = declared-writeable ∧ read ∧ ¬write-refined; own/drop = declared-droppable ∧ read ∧ ¬drop-refined (`crates/aquascope/src/analysis/permissions/mod.rs`) |
| Which loan or move removed a permission | yes | `enum Refiner { Loan(LoanKey), Move(MoveKey) }`, with a `RefinementRegion` over source character ranges (same file) |
| Permission changes between control-flow points | yes | stepper analysis (`analysis/stepper/`), shown as tables |
| Liveness (the non-lexical lifetime of a loan) | yes | loans are live per Polonius `loan_live_at`; Datalog rules restated in `permissions/output.rs` (`cannot_read`, `cannot_write`, `cannot_drop`) |
| Runtime memory (stack, heap, pointers) | yes | Miri-based interpreter (`crates/aquascope/src/interpreter/`); the paper runs Miri "regardless" of borrow errors |
| Lifetime parameters and outlives errors at signatures | **off by default** | region-flow analysis in `permissions/flow.rs` (taint environment over abstract origins; error kinds such as missing universal constraint and local-outlives-universal); `pub const ENABLE_FLOW_DEFAULT: bool = false;` in `permissions/mod.rs` |
| Elision | no explicit visualization found | — |

`Basis: source`. The concept with the worst measured comprehension, lifetime parameters, is the one the tool does not show by default. The tool consumes Polonius facts through rustc's consumer API, so it is tied to a pinned nightly (`nightly-2026-05-01`).

### 7. The elision rule that sets the annotation burden

`E0106.md` at `rust-lang/rust@c7d5ba5…`: "any function signature with an elided output lifetime must either have: exactly one input lifetime; or, multiple input lifetimes, but the function must also be a method with a `&self` or `&mut self` receiver". `Basis: documentation`. The explanation names this a "special, limited kind of inference". Everything outside these two cases must be written out.

### 8. Lifetime-annotation density in published crates: design and pilot measurement

Design:

1. Choose a stated sample: crate list, repository, pinned commit, and library source directory.
2. Parse every `.rs` file with a real Rust parser (syn 2, `full` features), with no macro expansion and no `cfg` evaluation.
3. For each function signature, classify as follows. The signatures are free fns, impl methods, trait methods, and foreign fns.
   - **Reference positions** are `&`/`&mut` types and `&self` receivers in inputs and output. Nested `fn(..)` pointer types and `Fn(..)` sugar are skipped, because they open their own elision scope.
   - **Written lifetimes** are named, `'static`, or `'_`.
   - **Input lifetimes** = elided input references + `'_` + distinct written lifetimes.
   - **Elision determines output** when there is a reference-to-`Self` receiver (including typed receivers such as `self: Pin<&mut Self>`), or exactly one input lifetime.
   - **Must annotate** = the output carries a non-`'static` lifetime and elision does not determine it.
4. Report counts per crate and pooled.
5. To measure how often the `E0106` situation arises *during development*, replay each repository's history. At each commit that touches a signature in the "must annotate" class, record whether the parent commit had the same signature with fewer written lifetimes. This history replay is designed but **not run** (see **Boundaries**).

Pilot results (`Basis: execution`; tool and raw output in `support/lifetime-density/`). The counter was checked against a 9-signature canary with hand-derived expected values; all 14 checked fields matched.

| crate (dir) | non-blank lines | fn signatures | write a named lifetime | declare fn lifetime params | output carries a lifetime | must annotate | of which write a named output lifetime | elided share of ref positions | ADTs with lifetime params | impls with lifetime params |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| serde (`serde_core/src`, `serde/src`) | 26398 | 1430 | 66 (4.6%) | 11 (0.8%) | 29 (2.0%) | 11 (0.8%) | 11 | 74.6% | 58/203 | 384/560 |
| syn (`src`) | 49524 | 3038 | 407 (13.4%) | 199 (6.6%) | 69 (2.3%) | 19 (0.6%) | 19 | 91.2% | 33/74 | 74/1707 |
| regex (`src`) | 10385 | 325 | 70 (21.5%) | 41 (12.6%) | 154 (47.4%) | 0 (0.0%) | 0 | 85.5% | 29/45 | 73/122 |
| rand (`src`) | 9528 | 361 | 3 (0.8%) | 1 (0.3%) | 19 (5.3%) | 0 (0.0%) | 0 | 99.3% | 4/43 | 5/110 |
| clap_builder (`clap_builder/src`) | 26787 | 1357 | 29 (2.1%) | 7 (0.5%) | 204 (15.0%) | 4 (0.3%) | 4 | 94.2% | 21/101 | 32/428 |
| tokio (`tokio/src`) | 98817 | 3971 | 65 (1.6%) | 31 (0.8%) | 422 (10.6%) | 21 (0.5%) | 21 | 97.8% | 60/580 | 71/1308 |
| anyhow (`src`) | 3465 | 142 | 20 (14.1%) | 12 (8.5%) | 28 (19.7%) | 12 (8.5%) | 7 | 82.1% | 6/21 | 9/75 |
| itertools (`src`) | 14455 | 668 | 3 (0.4%) | 3 (0.4%) | 31 (4.6%) | 0 (0.0%) | 0 | 100.0% | 11/98 | 14/273 |
| hashbrown (`src`) | 21988 | 1008 | 120 (11.9%) | 31 (3.1%) | 239 (23.7%) | 80 (7.9%) | 80 | 82.8% | 65/127 | 72/439 |
| bytes (`src`) | 9076 | 474 | 13 (2.7%) | 5 (1.1%) | 48 (10.1%) | 1 (0.2%) | 1 | 96.4% | 1/16 | 12/146 |
| memchr (`src`) | 14658 | 683 | 40 (5.9%) | 28 (4.1%) | 62 (9.1%) | 6 (0.9%) | 6 | 90.0% | 27/86 | 68/136 |
| nom (`src`) | 19712 | 1068 | 17 (1.6%) | 3 (0.3%) | 189 (17.7%) | 0 (0.0%) | 0 | 97.6% | 1/79 | 31/174 |
| log (`src`) | 5137 | 390 | 97 (24.9%) | 25 (6.4%) | 76 (19.5%) | 8 (2.1%) | 8 | 76.0% | 12/30 | 74/133 |
| smallvec (`src`) | 4073 | 241 | 4 (1.7%) | 1 (0.4%) | 23 (9.5%) | 2 (0.8%) | 2 | 99.6% | 8/15 | 12/147 |
| **pooled** | **314003** | **15156** | **954 (6.3%)** | **398 (2.6%)** | **1593 (10.5%)** | **164 (1.1%)** | **159** | **91.9%** | **336/1518** | **931/5758** |

Readings and caveats (`Basis: derived` from the table and from inspecting flagged cases):

- The 5 "must annotate" signatures without a named output lifetime are all in anyhow, and are measurement artefacts. An input such as `Ref<ErrorImpl>` hides a lifetime parameter inside a path, which a syntactic counter cannot see. A first version of the counter also mis-flagged 11 tokio `poll_fill_buf(self: Pin<&mut Self>, …)` methods. The typed-receiver rule fixed this, so the table excludes them.
- "Write a named lifetime" (6.3%) exceeds "must annotate" (1.1%) because many named lifetimes come from enclosing `impl<'a>` blocks, and are used where elision would also have produced *a* lifetime, possibly a different one. Examples are serde's `'de` and syn's parse-buffer lifetimes. 232 signatures have an elidable shape but name their output lifetime. The counter cannot decide whether elision would have chosen the same lifetime.
- The per-crate spread is wide: regex has 47.4% of signatures with output lifetimes and 0 must-annotate; hashbrown has 7.9% must-annotate. API style, not just domain, drives density. Any population estimate needs a designed sample.
- Throughput of the counter: 790 files and 314,003 non-blank lines in 1.07 s wall time, with a 27.5 MiB peak resident set size (RSS). This is single-threaded on an Intel Xeon @ 2.60 GHz cloud VM. `Basis: execution`.

### 9. Automatic ownership classification from C

| Tool or paper | Target pointer class | Benchmarks | Rate reported | Lifetimes synthesized? | Safety evidence |
|---|---|---|---|---|---|
| Laertes (Emre et al. 2021, "Translating C to Safer Rust") | raw pointers whose *only* cause of unsafety is lifetimes; these are 8.1% of raw-pointer declarations and 9.7% of dereferences | 17 c2rust-translated programs (413,428 C lines → 851,674 Rust lines) | 1,630 of 2,144 such declarations (76%) and 9,631 of 11,029 dereferences (87%; the text says 89%); functions unsafe solely from such pointers: 236 → 40 remaining (83% by the table; the text says 76%) | Yes, heuristically: one lifetime per type for struct fields, a unique lifetime per parameter, then outlives constraints taken from compiler errors (`E0308`, `E0495`, `E0623` → add `'a: 'b`; `E0759` → `'a: 'static`; `E0515`/`E0716` → owned; `E0499`/`E0502` → raw) | rustc acceptance ("we essentially use the Rust compiler as an oracle"); no test-suite runs reported |
| Crown (Zhang et al. 2023, "Ownership Guided C to Rust Translation") | mutable, non-array raw pointers | 20 programs (8 from Laertes' artifact, 8 real-world, 4 data structures) | median reduction 37.3% of declarations and 62.1% of uses; 100% for avl, bst, buffer and ht; brotli 21.4% / 20.9%; Laertes' figures on the same metric were re-derived from its artifact | **No**: "we chose not to do this and instead leave it as a future work"; output parameters become `&mut` | rustc acceptance; tests pass for the 6 benchmarks that have suites |
| Emre et al. 2023, "Aliasing Limits on Translating C to Safe Rust" | all raw pointers, after a "pseudo-safety" transform that removes other causes | 14 of the 17 Laertes programs | before pseudo-safety: 464 of 641 eligible pointers (72% in Table 1; the text says 93%); after: 987 of 8,537 (12%); with inserted reference-to-pointer casts: 1,789 (21%) | Laertes-style | equality-based typing groups pointers into classes; in tmux, 4 pointers marked unsafe force 85% of 4,635 to be unsafe |
| `c2rust-analyze` (source at `a483781…`) | all pointers in translated code | none in-tree | not reported | Not a lifetime synthesizer. It infers a `PermissionSet` lattice (`READ`, `WRITE`, `UNIQUE`, `LINEAR`, `OFFSET_ADD`, `OFFSET_SUB`, `FREE`, `NON_NULL`, `HEAP`, `STACK`) plus `FlagSet` (`CELL`, `FIXED`) | rewrites only "a small subset of unsafe Rust code"; skips a function on unsupported code (README) |

The `c2rust-analyze` pointer-kind mapping (`c2rust-analyze/src/type_desc.rs`, `perms_to_ptr_desc`, lines 105–127):

- `FREE` → `Box`.
- `UNIQUE|WRITE` → `&mut`.
- `CELL` → `&Cell`.
- Anything else → `&`.
- Quantity: `OFFSET_SUB` → offset pointer; `OFFSET_ADD` → slice; otherwise a single object.

Reasons a function is left unrewritten are enumerated in `DontRewriteFnReason` (`context.rs`): `INT_TO_PTR_CAST`, `EXTERN_CALL`, `NON_REWRITTEN_CALLEE`, `COMPLEX_CELL`, `PTR_TO_PTR_CAST`, `RAW_PTR_DEREF`, `SHIM_GENERATION_FAILED`, and analysis-invalid bits including `BORROWCK_INVALID`. Crown counts user-variable raw pointers by thinness and mutability, and counts owning ones (`CrateStatistics` in `crates/analysis/src/statistics.rs`). Its constraint system assumes *ownership monotonicity* along access paths, which "is stricter than the Rust semantics". The authors prove solving it NP-complete (Zhang et al. Thm 3). `Basis: source + documentation`.

Comparison with hand-written code: the translation rates count *pointer declarations converted*. The density table counts *signatures that write lifetimes*. The two have no common denominator. The one structural parallel is that both Laertes (one lifetime variable per parameter) and the `E0106` suggestion start from a maximal or uniform lifetime assignment and then need constraints to repair it. `Basis: derived`.

### 10. Performance and resource footprint across the six levels

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | human time on an aliasing-heavy task | median 4 h (GC) vs 12 h (Traditional); Ownership task no difference | cited, Coblenz et al. (self-reported) |
| L1 authoring | time to a compilable program without frequent `unsafe` | 27% < 1 week; 41% 1 week–1 month; 25% 1–6 months | cited, Fulton et al. (self-selected survey) |
| L1 authoring | signatures that must name a lifetime | 1.1% pooled (0%–8.5% per crate) | measured (this report) |
| L1 authoring | quiz authoring effort; reader time per question | ≈50 person-hours; median 29 s | cited, Crichton and Krishnamurthi |
| L1 authoring | manual patch needed by Laertes on tinycc | 38 lines, 10 min | cited, Emre et al. 2021 |
| L1 authoring | LLM token or turn budgets for ownership repair | not measured | — |
| L2 toolchain build | density counter release build (syn 2.0.119, offline) | 7.65 s | measured (cargo, same VM) |
| L2 toolchain build | Aquascope, Crown, `c2rust-analyze` builds | not measured | — |
| L3 analysis latency | Laertes per program | < 1 min except libxml2 and optipng; libxml2 125 min (81 iterations, 78 for lifetime constraints) on an i7-4790 | cited |
| L3 analysis latency | Crown whole suite; half a million lines | < 60 s; < 10 s (Apple M1) | cited |
| L3 analysis latency | context-sensitive aliasing analysis | tmux 25 h; tinycc 10 min; libxml2 > 48 h timeout | cited, Emre et al. 2023 |
| L3 analysis latency | `c2rust-analyze` Polonius on very large functions | "several minutes" | documentation (README) |
| L3 analysis latency | density counter | 1.07 s for 314,003 non-blank lines | measured |
| L4 generated code | runtime cost of GC references or translated code | not measured; Bronze never collected in the trial; Laertes and Crown report none | — |
| L5 checking | cost of rustc re-checking translated code | not measured | — |
| L6 memory | aliasing analysis peak memory | tmux 27 GiB; tinycc 2.8 GiB; others < 2 GiB | cited, Emre et al. 2023 |
| L6 memory | density counter peak RSS | 27.5 MiB | measured |
| L6 memory | Laertes, Crown, Aquascope memory | not measured | — |

### 11. Human comprehensibility and conceptual simplicity

- **C1, working-memory load.** The Inventory data separate two loads. *Local* access errors are predicted at 78%, because the R/W/O model needs only the current point. *Lifetime-parameter* errors are predicted at 10% and 38%, because they need a non-local relation between a signature and every caller. The `'static` and unify-all-inputs suggestions show diagnostics steering users toward over-constraint. Students also reported cyclic advice ("remove & then after removing try adding &"; Coblenz et al. §6). `Basis: documentation + execution (§3 probe)`.
- **C1, human vs. machine.** The tools that recover ownership (Laertes, Crown) treat the compiler as an oracle. That mechanizes repair but does not explain it. No study measured whether the tool output is readable to humans. `Basis: derived`.
- **C2, one invariant, several mechanisms.** The R/W/O permissions abstraction (Crichton et al.) unifies moves, borrows and drops into one per-place permission state, refined by loans and moves. This is a smaller concept set than the raw rule list. Lifetime parameters remain a separate mechanism, the outlives relation, which the abstraction does not cover (an experimental fourth "flow" permission is sketched in the paper). Pointer-kind lattices in `c2rust-analyze` and Crown similarly reduce many pointer kinds to a few permission bits plus a deterministic type mapping. `Basis: source + documentation`.

### 12. How implementations and claims are validated

- **V1, adequacy of instruments.** Inventory items came from real Stack Overflow questions, with κ = 0.81 coding reliability. Validity against real-world performance is explicitly untested ("future work should validate"). Book quizzes use telemetry, a bug-report button (2,026 reports), and schema checks that compare tracing answers with the real compiler. The density counter's definitions were checked by a canary with expected values; no mutation testing was run.
- **V2, checker as oracle.** Laertes and Crown both delegate safety to rustc acceptance; Crown says its translation "is in theory neither sound nor complete". Aquascope's permission model has a paper soundness argument against Polonius access errors, which is not mechanized. Only Crown ran test suites, on 6 benchmarks.
- **V3, concurrency, crashes and hardware.** Not applicable to these studies; not examined.
- **V4, human mental-model validation.** This is the dominant validation mode here: an RCT (Coblenz), temporal A/B tests (Crichton et al. 2023; Crichton and Krishnamurthi 2024), and surveys with program variants (Zhu). Only Coblenz et al. randomized.

## Boundaries

- **Not examined.**
  - Aquascope, Crown and `c2rust-analyze` were not built or run; their latency and memory numbers come only from papers or READMEs.
  - The Crown `artifact` branch, the Laertes evaluation artifact, and the Bronze artifact were not examined.
  - The 2018 and 2020 Rust community surveys, cited by several papers, were not read; their numbers are not reproduced here.
  - Zeng and Crichton 2019 and Coblenz et al. 2019 are cited by the papers but were not read.
- **Not measured.**
  - The development-time `E0106` frequency from version histories.
  - Density of lifetimes hidden in paths (`Formatter<'_>` written as `Formatter`).
  - Density in application, embedded or async-service code.
  - Generated-code runtime cost (L4) and re-check cost (L5) for any tool.
  - LLM-agent repair budgets.
- **Unknown.** Whether better lifetime diagnostics would close the 10.0% vs 39.6% "always understand" gap. Zhu et al.'s enhanced message helped only the array case. Whether the Inventory score predicts practical skill is also unknown; the authors list this as untested.
- **Known not to apply.**
  - The 4 h vs 12 h Bronze result is not a measurement of borrow-checker cost on ordinary code. The Ownership task showed no difference, and the authors attribute the gain to architecture.
  - Laertes' 76% and Crown's 37.3% are not rates of "ownership recovered from C" in general. They are restricted to the stated pointer classes and differ by metric.
  - Emre et al. 2023 show that on all pointers, the Laertes-style approach makes 12% safe.
- **Source inconsistencies preserved, not resolved.**
  - Emre et al. 2021: the text says 76% vs the table's 83% for functions, and 89% vs 87% for dereferences.
  - Emre et al. 2023: the text says 93% vs the table's 72%.
  - Crichton and Krishnamurthi 2024 give 221 vs 213 questions, and 33,013 vs 32,159 triers.
  - The pinned book fork has 222 questions and 21 Inventory questions, against the 24 deployed.
  - Emre et al. 2023 describe Laertes as using one lifetime per struct field, whereas Emre et al. 2021 say one per type.
- **Attractive stronger conclusions not established.**
  - That annotation burden is "small" because only 1.1% of library signatures must annotate. The sample is not representative, and the studies locate difficulty at exactly those signatures.
  - That garbage collection removes the need to learn ownership. Its own authors say the opposite.

## Evidence

Observation dates: all source pins, executions and paper readings happened on 2026-11-20 (UTC).

Papers (DOIs verified through the doi.org handle API plus OpenAlex metadata, because Crossref was unreachable through the available fetcher; arXiv identifiers verified on arXiv abstract pages):

- Will Crichton, "The Usability of Ownership", HATRA 2020, arXiv:2011.06171 v2 (read as arXiv HTML; section locators §2–§4).
- Kelsey R. Fulton, Anna Chan, Daniel Votipka, Michael Hicks, Michelle L. Mazurek, "Benefits and Drawbacks of Adopting a Secure Programming Language: Rust as a Case Study", SOUPS 2021, pp. 597–616, USENIX open access (no DOI). Cited sections: §3.1, §4, §6.2–6.4, §7.2, §8.
- Shuofei Zhu, Ziyi Zhang, Boqin Qin, Aiping Xiong, Linhai Song, "Learning and Programming Challenges of Rust: A Mixed-Methods Study", ICSE 2022, DOI 10.1145/3510003.3510164. Cited: §3.1–3.4, Table 2, §4.2.
- Michael Coblenz, Michelle L. Mazurek, Michael Hicks, "Garbage Collection Makes Rust Easier to Use: A Randomized Controlled Trial of the Bronze Garbage Collector", ICSE 2022, DOI 10.1145/3510003.3510107; arXiv:2110.01098 v2. Cited: §3, §5.1–5.10, §6, §7. The arXiv HTML prints a template placeholder DOI; the DOI above is correct.
- Will Crichton, Gavin Gray, Shriram Krishnamurthi, "A Grounded Conceptual Model for Ownership Types in Rust", PACMPL 7(OOPSLA2), Article 265, 2023, DOI 10.1145/3622841; arXiv:2309.04134. Cited: §2.2–2.5, Table 1, §3.2, §5, Table 3.
- Will Crichton, Shriram Krishnamurthi, "Profiling Programming Language Learning", PACMPL 8(OOPSLA1), 2024, DOI 10.1145/3649812; arXiv:2401.01257. Cited: §2.3–2.4, §3, §4, Table 1, §6, §8.
- Mehmet Emre, Ryan Schroeder, Kyle Dewey, Ben Hardekopf, "Translating C to Safer Rust", PACMPL 5(OOPSLA), Article 121, 2021, DOI 10.1145/3485498. Cited: Table 1, §2.2–2.4, §3, §4.2–4.3, Tables 7–8.
- Hanliang Zhang, Cristina David, Yijun Yu, Meng Wang, "Ownership Guided C to Rust Translation", CAV 2023, LNCS, pp. 459–482, DOI 10.1007/978-3-031-37709-9_22; arXiv:2303.10515 (preprint read). Cited: §5, §6.1, §7, §8, Tables 1–2.
- Mehmet Emre, Peter Boyland, Aesha Parekh, Ryan Schroeder, Kyle Dewey, Ben Hardekopf, "Aliasing Limits on Translating C to Safe Rust", PACMPL 7(OOPSLA1), Article 94, 2023, DOI 10.1145/3586046. Cited: §1, §4, Table 1, §5, §6, §9, Table 4.

Source (full commits in `REPORT.json`):

- `cognitive-engineering-lab/aquascope@f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`:
  - `ARCHITECTURE.md` (static visualization pipeline: front end, permissions analysis, boundaries and stepper).
  - `crates/aquascope/src/analysis/permissions/mod.rs` (`ENABLE_FLOW_DEFAULT`, `Permissions`, `PermissionsData::permissions_ignore_liveness`, `Refiner`).
  - `permissions/output.rs` (Datalog rule comments).
  - `permissions/flow.rs` (region-flow module docs).
  - `rust-toolchain.toml`.
- `cognitive-engineering-lab/rust-book@88250e0392cef0622f318e35469108d68694c1f7`: all 93 `quizzes/*.toml` files.
- `KomaEc/crown@621904cd356b433215d5f55db39ffd71714f44ff`: `README.md`, `benchmark/` (20 directories), `crates/analysis/src/statistics.rs`, `crates/analysis/src/flow/ownership/inference/{monotonicity,preservation}.rs`.
- `immunant/c2rust@a4837814f1ae7650fae0c7eccb9bdbbf2b1aef20`: `c2rust-analyze/README.md` ("Known limitations"), `c2rust-analyze/src/context.rs` (`PermissionSet`, `FlagSet`, `DontRewriteFnReason`), `c2rust-analyze/src/type_desc.rs` (`Ownership`, `Quantity`, `perms_to_ptr_desc`).
- `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`: `compiler/rustc_error_codes/src/error_codes/E0106.md`.
- Density sample: the 14 repositories and commits listed in `REPORT.json` and `support/lifetime-density/pins.tsv`.

Execution (host: x86_64 Linux cloud VM, Intel Xeon @ 2.60 GHz, 96 vCPUs, shared with unrelated workloads):

- `support/probes/e0106_two_inputs.rs` compiled with `rustc +1.100.0 --edition 2021 --crate-type lib --emit=metadata`; output in `support/probes/e0106_two_inputs.stable-1.100.0.stderr`.
- `support/lifetime-density/` contains:
  - `Cargo.toml` and `src/main.rs` (syn 2.0.119; built offline with cargo 1.100.0);
  - `canary.rs` and `expected.txt`;
  - `run.sh`, which reproduces every row;
  - `raw_stats.txt` and `density_table.tsv`.
- `support/count_quizzes.py` and `support/quiz_counts.txt`: the quiz-count table.

## Revalidation

- **Density.**
  1. Check out each pinned repository.
  2. Build `support/lifetime-density` (`cargo build --release`).
  3. Run `support/lifetime-density/run.sh <checkout-root>`.
  4. Diff against `raw_stats.txt`.

  To extend to newer revisions or another sample, first rerun the canary; it must print every `expected.txt` field unchanged. A change in syn's AST, such as new receiver forms, is the main risk.
- **Elision rule.** Re-read `E0106.md` at a new rustc revision, and rerun `e0106_two_inputs.rs`. A change in the suggested fix (currently unifying both inputs) is directly observable.
- **Aquascope default.** Grep `ENABLE_FLOW_DEFAULT` in `crates/aquascope/src/analysis/permissions/mod.rs`. If it becomes `true`, the "off by default" finding no longer holds.
- **Quiz instrument.** Rerun `support/count_quizzes.py` on a new book revision; the Inventory file count and question count are the discriminating values.
- **Translation tools.** Grep `perms_to_ptr_desc` and `DontRewriteFnReason` in `c2rust-analyze`, and `CrateStatistics` in Crown. For conversion rates, there is no cheap check: the published numbers require rerunning each artifact on its benchmark suite.
- **Study findings.** These are fixed publications and do not drift. Newer studies should be added as separate rows, not used to overwrite these numbers.
