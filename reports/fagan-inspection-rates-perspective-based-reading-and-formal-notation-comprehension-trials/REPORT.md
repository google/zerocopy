# Human review capacity for specifications: inspection rates, team and reading-technique effects, formal-notation comprehension trials, and what is (not) known about reviewing machine-checked specifications

## Summary

- **No study measures how fast, or how accurately, humans review machine-checked specifications.** No controlled study was found of people reviewing proof-assistant theorem statements (Coq/Rocq, Isabelle, Lean), TLA+ or Alloy specifications for defects, and no measured review rate (lines or pages per hour) exists for any formal specification. Every review-budget figure for such audit surfaces is an **extrapolation** from code and requirements inspection. Basis: documentation (literature search; negative result).
- **Code inspection rates converge on roughly 90–200 lines per reviewer-hour, in sessions of at most 2 h.**
  - Fagan 1986 gives 90 NCSS/h as the meeting rate, 125 NCSS/h for preparation, and 125 NCSS/h as the maximum.
  - IEEE Std 1028-2008's informative note gives 100–200 LOC/h.
  - In Kemerer & Paulk 2009 (PSP self-review), reviewing at or below 200 LOC/h found 56–66 % of defects present, against 45–51 % when faster. Going slower than 200 LOC/h showed no further gain.
  - The vendor rule of "under 500 LOC/h, 70–90 % yield" is **not supported by its own case study**.
  - Basis: documentation.
- **Rates for natural-language requirements and design documents vary about tenfold between sources:**
  - Gilb: ≈ 1 logical page of 300 words per hour.
  - IEEE 1028-2008: 2–3 pages/h.
  - Doolan 1992: 5–6 pages/h for individual checking.
  - Regnell et al. 2000: ≈ 6 pages/h, computed from their per-subject times.
  - In the requirements-reading experiments (16–31-page documents, 1.5–4 h per reader), individuals found only ~21–32 % of known defects. Simulated or real 3-person teams found ~24–79 %.
  - Basis: documentation + derived.
- **Who reviews matters more than how the review is structured.**
  - Porter et al. 1998: reviewer identity, code size and functionality explained ≈ 50 % of defect variance. Team size, sessions and repair were non-significant (p = 0.61, 0.51, 0.22).
  - Hatton 2008: faults found per hour varied tenfold between individual reviewers.
  - Perspective-based reading (PBR) gains reproduced in the originators' studies but mostly failed independent replication. Ciolkowski's 2009 aggregation found PBR teams *less* effective than checklist teams and reported "strong indicators of researcher bias".
  - Basis: documentation.
- **Formal notations are neither uniformly hard nor easy to read.**
  - Finney 1996: 19 of 62 trained students could not answer any of three questions on a Z fragment of fewer than 20 lines.
  - Snook & Harrison 2004 (36 students): a Z specification was at least 75 % as comprehensible as its Java implementation (95 % bound).
  - Greenman et al. 2023: 15 % of LTL→English reading responses and 28 % of English→LTL writing responses by researchers with prior LTL exposure were wrong. Misreading U as weak-until W was the dominant error.
  - Notation and structure measurably matter: pattern languages beat raw LTL (Czepa & Zdun), and meaningful names and ~20-line schemas help (Finney et al.).
  - Basis: documentation.
- **Small trusted specifications still contain defects that review missed.**
  - IronFleet called its 85-line IronRSL specification "easy to inspect for correctness". Fonseca et al. 2017 later found it did not require exactly-once semantics, so it failed to ensure linearizability.
  - CompCert's trusted PowerPC semantics omitted an immediate-width constraint (found by Csmith).
  - Mechanising the WebAssembly specification exposed errors in the official text, including type-system unsoundness.
  - Basis: documentation.
- **Derived extrapolation, not a measurement.** At Fagan's 90 lines/h, preparing the 4,900-line seL4 abstract specification (2009) costs one reviewer ≈ 54 h (28 two-hour sessions). A 4-person team at the same rate spends ≈ 436 person-hours. At the ≈ 20 lines/h rate Gilb cites as Raytheon's measured optimum, preparation takes ≈ 245 h per reviewer. Whether formal lines behave like code lines here is **unknown**. Basis: derived (executed arithmetic; see Finding 8).

## Applicability

This report synthesises three bodies of evidence and two durable repository subjects:

| Subject | Identity | Role |
|---|---|---|
| Software inspection and code review literature | DOIs in **Evidence** | Measured rates, effectiveness, team and technique effects. Results are kept separate for code versus requirements/design. |
| Formal/semi-formal notation comprehension experiments | DOIs / arXiv IDs in **Evidence** | Tasks, participants, error rates and times. |
| Verified-system papers reporting trusted-specification sizes and specification defects | DOIs in **Evidence** | Audit-surface sizes and observed specification defects. |
| NASA FRET | `NASA-SW-VnV/fret` @ `cf0f913cc15c41705e803593297e89cd6056b839` | Structured-English requirements tool with explanation aids (repository read). |
| Google engineering-practices guide | `google/eng-practices` @ `3bb3ec25b3b0199f4940b1aa75f0ac5c5753301c` | Published change-size and review-latency norms. |
| IEEE Std 1028-2008; NASA-STD-8739.9 (2013) | standard identifiers | Normative/informative rate and team-size guidance. 8739.9 text was **not** retrievable. |

How the subjects relate:
- The literature supplies rates and effectiveness. The verified-system papers supply audit-surface sizes.
- FRET and the guide are examples of tool-assisted and practice-level guidance.
- Section 8 **combines** literature rates with published sizes by explicit arithmetic. That combination is a hypothesis-generating extrapolation, not an applicability claim.

Scope qualifications:
1. Most quantitative inspection results concern **code**. Requirements results come from a small set of 16–31-page natural-language or SCR documents, read mostly by students.
2. Several classic numbers were read in tech-report, preprint or workshop versions rather than the version of record: Porter et al. 1995/1997/1998, Basili et al. 1996 and Kemerer & Paulk 2009. These are flagged per finding.
3. Fagan 1976's rate table was available only via a secondary reproduction.
4. Effectiveness is measured inconsistently across studies: defects/KLOC, % of seeded defects, % of defects found by end of testing, or defects/hour. Values are not interchangeable.

## Findings

### 1. Inspection rates and session limits, separated by artifact type

| Source | Artifact | Rate (per reviewer) | Session / team | Provenance |
|---|---|---|---|---|
| Fagan 1976, Table 3 | design (I1) / code (I2) | preparation 100 / 125 loc/h; inspection 130 / 150 loc/h; overview 500 loc/h (design) | ≤ 2 h sessions | rates **secondary** (thesis reproduction of Table 3); 2 h limit from search-index text of the original |
| Fagan 1986, citing Buck 1981 | code | preparation 125, inspection 90, **maximum 125 NCSS/h**: "defect detection efficiency diminishes at rates above 125 NCSS/h" | ≤ 2 h, ≤ two sessions/day | full text (reprint) |
| IEEE Std 1028-2008 §6.5.2 NOTE (informative) | requirements; architecture | 2–3 pages/h | 2–6 participants (§6.1) | full text (reproduction of the standard's text) |
| same | preliminary / detailed design | 3–4 pages/h | — | same |
| same | source code; fixes and changes | 100–200 LOC/h; 50–75 LOC/h (units printed inconsistently as "PPH to LPH") | — | same |
| same | test plan; user docs | 5–7; 8–20 pages/h | — | same |
| Gilb (practitioner texts) | any specification text | "one logical page of 300 noncommentary words checked per hour plus or minus 0.9"; Raytheon "about 20 plus or minus 10 lines per hour" | 4–6 people for effectiveness, 2–4 for efficiency | Gilb's own later texts; 1993 book not read |
| Doolan 1992 (Shell) | **requirements specs** (11 SRSs, ≈ 500 pp) | individual checking 5–6 pages/h; logging meeting 7–8 pages/h | teams 4–6; meetings < 2 h | full text |
| Weller 1993 (Bull, > 6,000 meetings) | code, design | preparation-rate split at 200 lines/h; lower rate finds more | "four-person teams were twice as effective … as three-person teams" | full text |
| NASA-GB-A302 (1993) | all | rate table missing from all electronic copies | team 4–7 (minimum 3); meeting "limited to 2 hours" | full text |
| NASA-STD-8739.9 (2013) | all | **not verified** | **not verified** | PDF not retrievable |
| Russell 1991 (BNR, 2.5 MLOC) | code | ≤ 150 LOC/h | — | secondary |
| `google/eng-practices` | code changes | — (size and latency only): "100 lines is usually a reasonable size for a CL, and 1000 lines is usually too large" (`review/developer/small-cls.md:65-66`); "**One business day is the maximum time it should take to respond**" (`review/reviewer/speed.md:36`) | — | source (line-cited) |
| Sadowski et al. 2018 (≈ 9 M changes) | code changes | median change 24 lines; median 1 reviewer; median review latency < 4 h; 3.2 h/week mean reviewing per developer | — | full text |

Basis: documentation (per row provenance).

Reading of the table:
- For code, the planning rates recommended in 1976–2009 sit in a narrow 90–200 lines/h band.
- For requirements and design text, recommended rates span 1 to ~8 pages/h depending on the source.
- **No source in the table defines a rate for formal-specification text.** Fagan 1986 states that for requirements, test plans and user documentation "inspection rates are not as clear for them and are probably more product and project dependent".

### 2. Rate versus effectiveness: what is measured and what is folklore

- **Kemerer & Paulk 2009** (*IEEE TSE* 35(4)): PSP data, 371 C programs from 153 developers and 246 C++ programs from 90 developers. Reviews are individual, checklist-based self-reviews of ≈ 120-LOC programs.
  - Review rate was significant in all 16 models.
  - At ≤ 200 LOC/h reviewers found "66 and 57 percent" of design defects and "56 and 57 percent" of code defects. Faster reviewers found "49 and 51 percent" of design defects and "47 and 45 percent" of code defects.
  - "No statistically significant difference" separated 0–100 from 100–200 LOC/h.
  - The authors note the reverse-causal possibility that finding defects slows reviewers.
  - Their summary "8–15 / 10–11 percent" improvement matches the quoted percentages only if the fast-rate values are paired in reverse order. Table 14 is an image and was not checked (derived).
  - Basis: documentation (preprint full text).
- **Porter et al. 1998** (*ACM TOSEM* 7(1); tech-report version):
  - The correlation between preparation time and defects found in preparation is 0.26; between meeting duration and meeting gains it is 0.57.
  - Preparation time was **deliberately excluded** from the models as endogenous ("a consequence, as well as a cause"). Time-versus-yield correlations therefore do not establish that slowing down causes more defects to be found.
  - Basis: documentation.
- **McIntosh et al. 2016** (Qt, VTK, ITK): reviews approved faster than 200 lines per elapsed hour ("hastily-reviewed") were significant where they survived correlation analysis, but **with inconsistent sign** across systems. A 100 lines/h threshold "had little impact". Basis: documentation.
- **SmartBear/Cisco** (vendor, not peer-reviewed): a 10-month case study of 2,500 reviews of 3.2 MLOC with 50 developers.
  - It measured defect *density* from a 300-review sample: 32 defects/kLOC on average, and 61 % of reviews found none.
  - The widely repeated "70–90 % yield" appears only in later white papers and web pages, **not in the case study**, which measured no yield.
  - Its rate threshold drifts between 300, 400, 450 and 500 LOC/h across the vendor's own documents.
  - Basis: documentation.

Derived consequence: the only controlled evidence for a rate ceiling is about individual code self-review. It supports "≤ 200 LOC/h" and gives no information about rates for dense formal text.

### 3. Team size, meetings and sources of variation

| Study | Setting | Result |
|---|---|---|
| Porter, Siy, Toman, Votta 1997 (*TSE* 23(6); tech report) | 88 code inspections over 18 months, 11 experienced developers, 1/2/4 reviewers × 1/2 sessions | TR: "no difference between 2- and 4-person inspections, but both performed better than 1-person inspections". TSE abstract: treatments "did not significantly influence the defect detection effectiveness". Median 12 defects/KNCSL; median effort ≈ 22 person-h/KNCSL; 30 % of defects were meeting gains. Organisational preparation limit ≈ 300 LOC per ≤ 2 h. |
| Porter, Siy, Mockus, Votta 1998 | same data | Inputs dominate. Final model `Defects ~ Func + log(Size) + RB + RF` explains ≈ 50 % of variance, where RB and RF are two specific reviewers. Team size p = 0.6062, sessions p = 0.5146, repair p = 0.2207. |
| Votta 1993 (FSE) | 13 low-level design inspections | Meeting "synergy" ≈ 4–5 % of defects (secondary); recommends depositions over meetings. A later AT&T dataset reports an average 33 % meeting gain (secondary), so the sources disagree. |
| Johnson & Tjahjono 1998 (*EMSE* 3(1)) | 24 three-person groups | Meetings significantly more costly, no more defects, fewer false positives. |
| Porter, Votta, Basili 1995 (students) | SCR requirements | Meeting gain 4.7 % / 3.1 %, loss 6.8 % / 7.7 %, net ≈ −1 % (not significantly different from 0). |
| Weller 1993 | > 400 defect-finding inspections | 4-person teams "twice as effective" as 3-person teams. |
| Hatton 2008 (*IEEE Software*) | 308 industrial inspections | Checklists gave no significant improvement. Individuals found ≈ 53 % of faults, pairs ≈ 76 %. Tenfold spread in faults/hour between individuals (abstract). |
| Boodoo et al. 2000 (NRC Canada TR) | 16 professional designers, UML, simulation | "No single optimal team size". Optimum 8–11 under assumed cost ratios. A 2-vs-4-person comparison with 5 teams per arm has only 58 % power. |
| Biffl & Halling 2003 (*TSE* 29(5)) | nominal teams, experiment | Mixing reading techniques beats adding inspectors. The marginal cost per additional defect rises "more than linearly" (abstract only). |

Basis: documentation.

Derived consequence: "2 reviewers are as good as 4" rests on small, underpowered arms. "4 beat 3" (Weller) and "pairs ≈ 76 %" (Hatton) point the other way. The defensible statement is that reviewer identity and artifact dominate, and that structural changes move outcomes less than the person reviewing.

### 4. Reading techniques for requirements: scenarios, perspectives and replication

- **Porter, Votta, Basili 1995** (*TSE* 21(6); TR-3327 version). 48 graduate students formed 16 three-person teams. Documents were SCR requirements (WLMS 24 pp/42 natural defects; CRUISE 31 pp/26 defects). Individual detection and team collection were each limited to 2 h.
  - Team detection rates were scenario .57/.45, ad hoc .43/.31 and checklist .41/.24 (method F = 8.064, p < .01).
  - Pooled (derived): scenario .515, ad hoc .368, checklist .325.
  - Several later papers cite "ad hoc 32.5 %, checklist 36.5 %, PBR 51.5 %". That quote swaps ad hoc and checklist and mislabels defect-based scenarios as PBR (derived from the TR's Table 3; the final TSE table was not seen).
- **Basili et al. 1996** (*EMSE* 1(2); SEW-20 version). NASA SEL professionals (12 + 13 per document type) read generic documents (ATM 17 pp/29 seeded defects; PG 16 pp/27) and NASA documents, with a 3 h limit in 1994 and 2 h in 1995. There were no real meetings: nominal 3-person teams were formed post hoc.
  - Team permutation p-values: generic 1995 **0.0007**, generic 1994 0.0660, NASA 1995 0.0390, NASA 1994 **0.4340**.
  - Simulated team means on generic documents: usual 48.2 % → PBR 79.3 % in the 1995 run, and 44.3 % → 52.9 % in the pilot (secondary).
  - Individual means: 24.64 % → 32.14 % (secondary, corroborated).
  - PBR review time was "almost the same … to 30 percent more" (Shull, Rus, Basili 2000).
- **Independent replications:**
  - Bari 1997 (30 undergraduates): no scenario advantage.
  - Linköping 1998 (24): scenario ≈ checklist.
  - Strathclyde 1998 (50): significant on CRUISE only.
  - Lucent 1998 (18 professionals): corroborated.
  - Bari 2000 (ISERN-00-08; 114/109 students, real teams): individual PBR **.220 vs ad hoc .285 (F = 8.69, p = .0039)**; teams .423 vs .419 (p = .891). Only 20 % of PBR reviewers followed the technique.
  - Regnell et al. 2000 (30 MSc students): perspectives not different (p = .49 defects/hour, p = .46 detection rate).
- **Ciolkowski 2009** (ESEM) aggregation (abstract only): "no clear positive effect of PBR … more effective when compared to ad-hoc approaches, but … less effective when compared to checklists … strong indicators of researcher bias".

Basis: documentation (versions as noted) + derived.

Measured reading time (Regnell et al. 2000, Appendix A, recomputed). The mean was 178.2 min per 16–17-page document (median 175, range 88–306). That is ≈ 6.0 pages/h (range 3.3–10.9), 2.71 defects/h, and an individual detection rate of 0.252. Basis: derived from the paper's per-subject table.

### 5. Comprehension of formal and semi-formal notations

| Study | Participants | Task / material | Measured outcome |
|---|---|---|---|
| Finney 1996 (*TSE* 22(2), correspondence) | 62 UG/PG students with Z training | 3 questions on < 20 lines of Z | "19 students, nearly a third of the group, could not answer a single question". No significance tests; the author urges caution. |
| Finney, Rennolls, Fedorec 1998 (*JSS* 42(1)) | UG/PG students (N not in abstract) | 5 Z specifications × comments/naming/structure | Whole group: "only meaningful naming significantly enhances comprehension". Top scorers: only commenting significant. |
| Finney, Fenton, Fedorec 1999 (*IEE Proc. Software*) | students | structure | "schemas of about 20 lines long significantly improved comprehensibility over a monolithic specification" |
| Snook & Harrison 2004 (*IST* 46(14)) | 36 second-year CS students, randomised 18/18 | Z specification vs its Java implementation, 22-point open-question test, 50-min slot | Mean difference 0.56 marks; 95 % bound: Z score "no worse than 75 %" of Java; scoring rate ≥ 82 %; Z rate varied more between subjects. |
| Zimmerman, Lundqvist, Leveson 2002 (ICSE) | computer scientists and aerospace engineers ("preliminary exploration") | 6 state-machine notation factors (macros, hierarchy, transition perspective, …) | Abstract only. No error rates or times verified. |
| Czepa & Zdun 2020 (*TSE* 46(1)) | 216 participants, 2 experiments | judge truth value of existing LTL / PSP / EPL specifications on traces | PSP > EPL > LTL in understandability, "statistically significant and reproducible" (abstract; per-notation numbers not verified). |
| Czepa, Amiri, Ntentos, Zdun 2019 (*SoSyM* 18(6)) | 215 students | *writing* compliance specifications | Bachelor semantic correctness LTL 28.49 %, PSP 50.19 %, EPL 38.20 %; mean times 43–49 min. |
| Greenman, Saarinen, Nelson, Krishnamurthi 2023 (*Programming* 7(2)) | 90 + 57 students; 29 researchers; 11 think-aloud | LTL↔English, trace satisfaction | Reading incorrect 23 % / **15 % (researchers)** / 24 %; writing incorrect 47 % / **28 %** / 47 %; median 93 min for 19 questions. WeakU (U read as W) caught half the Round-2 students and 2 researchers. |
| Greenman et al. 2024 (FM) | incl. expert attendees of an LTLf symposium | write / describe / match | Experts: 33.68 % of written formulas incorrect, 19.79 % of descriptions, 8.33 % of trace matches. |
| Vinter, Loomes, Kornbrot 1998 (METRICS) | trained Z users | reasoning tasks | Z admits "non-logical reasoning errors and biases in trained users" on disjunction, conjunction and quantification (abstract + secondary). No verified rates. |
| Snook & Harrison 2001 (*IST* 43(4)) | 5 organisations (FM users) | interviews | Practitioners saw no significant understanding problems, with a recruitment-selection caveat. |
| Hall 1990 (*IEEE Software*) | experience report | — | "the mathematics for specification is easy" (claim, not measured). Finney 1996 is a direct rebuttal. |

Basis: documentation (abstract-only items flagged).

Synthesis (derived):
1. Error rates on small formal fragments are non-trivial even for experienced readers: ≈ 15 % misreading and ≈ 28–34 % miswriting of short LTL formulas by researchers or experts.
2. Measured interventions that help are naming, comments, ~20-line structuring and pattern-based notations. Reading technique has inconsistent effects.
3. Measured durations are per task or per questionnaire (e.g., ≈ 4.9 min per LTL question including idle time, derived). **None is a lines-per-hour review rate.**

### 6. Tool support: FRET's explanation aids and what has been evaluated

Repository facts (`NASA-SW-VnV/fret` @ `cf0f913c…`):
- **Restricted-English grammar** (`fret-electron/app/parser/Requirement.g4:15-20`):
  ```text
  nasa
          : (scope)? (reqt_condition)?
            (component SHALL | SHALL component)
            (probability)?
            (timing)? response
          ;
  ```
  Line 8 is `reqt_body : (nasa | freeform) ('.')?`.
- **Semantics templates:** `fret-electron/app/parser/semantics.json` has 288 template keys at this revision (counted by loading the JSON). Each key carries a `description`, a `diagram`, future/past-time formulas (`ft`, `pt`, expansions) and export code (`CoCoSpecCode`, `R2U2Code`).
- **Natural-language explanation:** `fret-electron/support/formalization-descriptions.js`, `exports.getDescription` (line 93). For example, line 33 reads `'-,-,immediately,-', 'REQUIRED BEHAVIOR: for every trigger, if trigger holds then RES also holds at the same time point.'`.
- **Timing diagrams:** `fret-electron/support/semanticDiagramsLib.js`.
- **LTL simulator:** `tools/LTLSIM/`, with the UI in `fret-electron/app/components/LTLSimDialog.js`. The documentation (`fret-electron/docs/_media/UsingTheSimulator/ltlsim.md:5-13`) motivates it: "The temporal structure of one or more requirements and their temporal interactions can be rather complicated and hard to understand." The simulator requires NuSMV (`:34-36`).
- **Case studies:** `caseStudies/` holds `FiniteStateMachine`, `LMCPS`, `LiftPlusCruise` and `LiquidMixer`, with 13, 97, 57/19 and 12 requirement entries respectively (counts from the JSON files).

Basis: source.

Evaluations:
- **Giannakopoulou et al. 2021** (*IST* 137): formalization correctness is established by automated testing of generated formulas against template semantics and by past/future equivalence proofs (abstract). Conrad et al. (CPP 2022) prove FRETish semantics equivalent to the generated temporal logic in PVS (arXiv:2201.03641 abstract).
- **Mavridou et al. 2020** (RE): the FRET developers captured 69 of 74 Lockheed Martin challenge requirements. Two requirements "were unclear: we were not able to interpret their meaning even with the help of the domain expert". Only 7 of 112 template keys were used, with `[null, null, always]` in 75 % of formalizations. One requirement went through 4 revisions after semantics, simulation and model-checking feedback.
- The FRET publication list contains **no controlled human-comprehension study** of FRETish, its generated English, or its diagrams. Searches found none elsewhere.

Basis: documentation.

Derived consequence: FRET moves the human review obligation from the temporal-logic formula to the restricted-English sentence plus the template semantics, which is mechanically checked. It offers redundant views for that review. Whether those views improve reviewer accuracy or speed is **unmeasured**.

### 7. Evidence that concerns machine-checked specifications and reference semantics

Published trusted-specification sizes, the "audit surface" a human must validate:

| System | Trusted specification | Size | Other figures | Source |
|---|---|---|---|---|
| IronFleet (Dafny) | high-level specs | IronRSL 85 SLOC, IronKV 34 SLOC; total spec 1,400 SLOC | implementation 5,114; proof 39,253; ≈ 3.7 person-years | Hawblitzel et al. SOSP 2015 |
| WebAssembly (Isabelle) | mechanised spec | ≈ 700 lines | ≈ 11,000 lines total | Watt CPP 2018 |
| CompCert (Coq) | language semantics | 10 % of 42,000 lines (≈ 4,200, derived); Clight 1,100 lines; each intermediate language 300–600 lines | ≈ 3 person-years | Leroy CACM 2009 |
| seL4 (Isabelle) | abstract specification | 4,900 lines, ~75 invariants; ≈ 4 person-months to write | executable spec 13,000 Isabelle lines; C 8,700 + 600 asm; proof ≈ 200,000 lines (2009), 480,000 lines of proofs and specs (2014) | Klein et al. SOSP 2009; TOCS 2014 |
| AWS TLA+ models | design specs | 102–939 lines | engineers learned TLA+ "in 2 to 3 weeks" | Newcombe et al. CACM 2015 (preprint read) |

Specification defects that escaped human review (all documented, none measured as a rate):
- **Fonseca et al. 2017** (EuroSys) found 16 bugs in IronFleet, Verdi and Chapar. Two were specification bugs, including IronRSL not specifying exactly-once semantics, and 11 were shim-layer bugs. They describe the high-level specification as something "which is often manually reviewed and trusted to be correct".
- **seL4 2009:** the first refinement step "lead to some 300 changes in the abstract spec and 200 in the executable spec", about half of them algorithm or design bugs. The paper concedes the proof does not show that "the specification describes the behaviour the user expects".
- **Csmith (Yang et al. PLDI 2011):** "CompCert's PPC semantics failed to specify a constraint on the width of this immediate value".
- **Watt 2018:** errors in the official WebAssembly specification "meant that the type system was originally unsound".
- **Statement-faithfulness audits of Lean benchmark datasets** (an upper-bound proxy for what a reviewer must catch, not a reviewer detection rate):
  - miniF2F: discrepancies "for more than half" of 488 problems (arXiv:2511.03108).
  - LLM-judged autoformalization accuracy of 97 % fell to 66 % after human review.
  - Static checkers over ~10,000 problems produced 4,833 findings, 398 mechanically certified (arXiv:2606.29493).

Basis: documentation.

Answer to "is there direct evidence about reviewing machine-checked specifications?": **only indirect evidence.** Specification defects exist and survive "manual review". Sizes range from tens to thousands of lines. No study reports reviewer time, coverage, or detection probability for such specifications. Basis: documentation (negative result) + derived.

### 8. Derived: what the code-inspection numbers would imply (executed arithmetic)

`Basis: derived (executed arithmetic on literature numbers; the inputs are code-inspection rates, and their transfer to formal text is an unverified assumption).`

The script is `review_budget_derived.py`. Session cap 2 h, ≤ 2 sessions/day, preparation and meeting both at the stated rate:

| Audit surface (lines) | 20 lines/h (Raytheon optimum, via Gilb) | 90/h (Fagan 1986) | 200/h (Kemerer–Paulk ceiling) |
|---|---|---|---|
| IronRSL spec (85) | 4.2 h/reviewer; 3 sessions | 0.9 h; 1 session | 0.4 h; 1 session |
| WebAssembly spec (700) | 35 h; 18 sessions | 7.8 h; 4 sessions | 3.5 h; 2 sessions |
| IronFleet total spec (1,400) | 70 h; 35 sessions | 15.6 h; 8 sessions | 7.0 h; 4 sessions |
| CompCert semantics (≈ 4,200) | 210 h; 105 sessions | 46.7 h; 24 sessions | 21 h; 11 sessions |
| seL4 abstract spec (4,900) | 245 h; 123 sessions | 54.4 h; 28 sessions | 24.5 h; 13 sessions |

At 90 lines/h, total person-hours for a 4-person team are 7.6 (IronRSL), 62 (Wasm), 124 (IronFleet), 373 (CompCert) and 436 (seL4).

Independence check (`1 − (1 − p)^k` against reported team detection):

| Case | individual p | k | predicted | observed | ratio |
|---|---|---|---|---|---|
| Hatton 2008 (code) | 0.53 | 2 | 0.779 | 0.760 | 0.98 |
| Basili 1995 run, usual technique (secondary) | 0.246 | 3 | 0.572 | 0.482 | 0.84 |
| Basili 1995 run, PBR (secondary) | 0.321 | 3 | 0.688 | 0.793 | 1.15 |
| Lanubile & Visaggio 2000, ad hoc, real teams | 0.285 | 3 | 0.634 | 0.419 | 0.66 |
| Lanubile & Visaggio 2000, PBR, real teams | 0.220 | 3 | 0.525 | 0.423 | 0.81 |
| Lanubile & Visaggio 2000, checklist, real teams | 0.288 | 3 | 0.639 | 0.381 | 0.60 |

The independent-reviewer model errs in **both directions**, from 0.60× to 1.15× of the observed team yield. Reviewer overlap (correlated misses) and meeting losses typically make it optimistic. A team-yield budget therefore cannot be computed from individual detection rates alone; it must be measured for the artifact class.

### 9. What would have to be measured to size a human review budget for formal audit surfaces

A minimal protocol that the literature has not executed. This is a derived design, built from the gaps above:

1. **Artifact and defect ground truth.** Use real trusted specifications from proof-assistant developments (statement cones of 10²–10⁴ lines). Seed them with *specification-level* mutants whose vacuity or semantic deviation is mechanically certified, e.g., by a counterexample or by a proof of the mutant's non-equivalence. Keep natural defects with known provenance, such as published specification bugs like those above.
2. **Reviewer strata.** Domain experts versus proof-assistant experts versus general engineers. Record prior exposure; Greenman et al. show experience lowers but does not remove error.
3. **Rate as a controlled variable.** Assign target rates (e.g., 25/50/100/200 lines/h) rather than observing them. This breaks the reverse-causality confound that Porter et al. 1998 and Kemerer & Paulk name.
4. **Outcome per reviewer and per nominal team:**
   - detection probability per defect class (vacuity, missing frame condition, wrong quantifier scope, until/weak-until, unit or width omissions);
   - false-positive rate;
   - time;
   - overlap between reviewers, to fit capture–recapture rather than the independence model.
5. **Form and aid factors.** Names and comments, schema size (≈ 20-line chunks), pattern versus raw temporal logic, and generated-English or diagram aids of the FRET kind, each as a factor.
6. **Power.** At 2-vs-4-reviewer granularity, ≥ 10 teams per arm (Boodoo et al.: 96 % power at 10 teams per arm versus 58 % at 5).

The budget for a surface of L lines is then L/r* reviewer-hours per reviewer. Here r* is the measured rate at which the team detection curve for the riskiest defect class plateaus, and the team size k is the one at which the marginal cost per defect exceeds the downstream cost of an escaped specification defect. Basis: derived.

### 10. Cross-cutting resource, comprehension and validation profile

| Level | What the evidence says |
|---|---|
| L1, human/agent authoring and review velocity | Code review ≈ 90–200 lines/h; requirements ≈ 1–8 pages/h; Google median change 24 lines with ≈ 3.2 h/week per developer reviewing; seL4 abstract spec took ≈ 4 person-months to write. **No formal-spec review rate exists.** LLM-judged faithfulness of autoformalized statements is inflated (97 % → 66 % after human review). |
| L2, toolchain build time | Not applicable to the literature. FRET was not built or run here. |
| L3, interactive latency | FRET's simulator requires NuSMV (docs). Latency not measured. |
| L4, generated-code performance | Not applicable. |
| L5, checking cost | Mechanical checks substitute for human review of derived artifacts: FRET formula testing, PVS equivalence, and certified benchmark findings. Human review remains for the endpoint statements. |
| L6, footprint | Audit-surface sizes: 34 to 4,900 lines (Section 7). FRET `semantics.json` is ≈ 2.2 MB of template data (repository listing). |

C1, human comprehensibility:
- Working-memory load shows up as structure effects: ~20-line schemas beat monolithic specifications, and naming matters.
- Specific operator semantics produce systematic misreadings: U versus W, and implicit G/F.
- Reviewers spend most of their time understanding. Defect comments are only 14 % of review comments (Bacchelli & Bird 2013).
- Human comprehension evidence is about humans only. LLM-judge agreement is not a proxy (miniF2F audit).

C2, simplicity and model refinement:
- The invariant that matters is that **the endpoint statement means what the stakeholder intends**.
- The literature attacks it with several overlapping mechanisms: rate limits, team size, reading techniques, notation choice and explanation aids. None has been shown to transfer to formal statements.
- The one mechanism that removes review load without shifting it elsewhere is mechanically checking derived artifacts against a smaller reviewed core (FRET templates, PVS equivalence). Even then the core remains a review obligation.

V1–V4, validation:
- V1, specification adequacy: specification mutants and non-vacuity witnesses are the only mechanical way to estimate reviewer detection probability (Section 9). The audits in Section 7 show statement faithfulness errors are common in practice.
- V2, differential and metamorphic testing: Csmith found a defect in CompCert's trusted semantics. Differential testing of a semantics against implementations is complementary to human review.
- V3, concurrency, crash and silicon: not examined.
- V4, human mental-model litmus tests: Greenman et al.'s misconception instruments and Finney's question sets are reusable as reviewer-qualification probes. No study links reviewer scores on such probes to defect detection in real specifications.

## Boundaries

- **Unknown (searched, not found):**
  - any controlled measurement of human review rate, coverage or detection probability for proof-assistant statements, TLA+ or Alloy specifications;
  - any human study of FRET's explanation aids;
  - any quantitative pooling of inspection rate versus effectiveness across studies.
- **Not verified:**
  - NASA-STD-8739.9 (2013) rate, team-size and meeting values (PDF not retrievable);
  - the NASA-GB-A302 (1993) rate table (absent from electronic copies);
  - Fagan 1976 Table 3, which comes only from a secondary reproduction;
  - Russell 1991's 150 LOC/h and 0.8–1 defect/staff-hour, which are secondary.
- **Abstract-only:**
  - Zimmerman et al. 2002, which reports no error rates or times;
  - Czepa & Zdun 2020's per-notation correctness and times;
  - Ciolkowski 2009's number of studies and effect sizes;
  - Biffl & Halling 2003's participants and effect curves;
  - Hatton 2008's denominators.
- **Version caveat:** the Porter 1995/1997/1998 and Basili 1996 figures come from tech-report or workshop versions. Porter 1997's TR and TSE abstract disagree on team-size significance.
- **Known not to transfer directly:**
  - Kemerer & Paulk's ≤ 200 LOC/h ceiling concerns individual self-review of ≈ 120-LOC programs, not team review of specifications.
  - Modern code-review statistics describe latency and change size, not defect yield.
- **Attractive but unsupported:**
  1. "Small trusted specs are easy to inspect": contradicted by the IronRSL incompleteness.
  2. "Formal specs are easier to read than code": Snook & Harrison find rough parity in one student study; Finney finds failure on tiny fragments.
  3. "PBR raises team yield": not supported by independent replications or aggregation.
  4. "200–400 LOC, < 500 LOC/h gives 70–90 % yield": the vendor's own study measured no yield.
- **Not examined:** IEC 60880 and other domain standards' review requirements; tool-assisted review of Lean/Coq statements (e.g., statement-diffing tools); eye-tracking studies.
- **The extrapolations in Finding 8 are arithmetic, not evidence.** Whether a line of Isabelle or Dafny specification costs the same review time as a line of code is **unknown**.

## Evidence

Observation date: all retrieval and verification on 2026-11-20 (UTC). DOIs were verified against Crossref metadata (title, authors, venue, volume, issue, pages, year) on that date. arXiv IDs were verified on arxiv.org.

**Repositories:**
- `NASA-SW-VnV/fret@cf0f913cc15c41705e803593297e89cd6056b839`: `fret-electron/app/parser/Requirement.g4` (lines 8, 15–20), `fret-electron/app/parser/semantics.json` (288 keys), `fret-electron/support/formalization-descriptions.js` (lines 33, 93), `fret-electron/support/semanticDiagramsLib.js`, `fret-electron/docs/_media/UsingTheSimulator/ltlsim.md` (lines 5–13, 34–36), `caseStudies/*`, `PUBLICATIONS.md`.
- `google/eng-practices@3bb3ec25b3b0199f4940b1aa75f0ac5c5753301c`: `review/developer/small-cls.md:65-69`, `review/reviewer/speed.md:36-40`.

**Inspection and review literature (DOI):**
- Fagan 1976 `10.1147/sj.153.0182`
- Fagan 1986 `10.1109/TSE.1986.6312976`
- Porter, Siy, Toman, Votta 1997 `10.1109/32.601071` (tech report CS-TR-3760 read)
- Porter, Siy, Mockus, Votta 1998 `10.1145/268411.268421` (CS-TR-3762 read)
- Votta 1993 `10.1145/167049.167070`
- Johnson & Tjahjono 1998 `10.1023/A:1009787822215`
- Kemerer & Paulk 2009 `10.1109/TSE.2009.27`
- Russell 1991 `10.1109/52.62929`
- Weller 1993 `10.1109/52.232397`
- Doolan 1992 `10.1002/spe.4380220205`
- Hatton 2008 `10.1109/MS.2008.100`
- Biffl & Halling 2003 `10.1109/TSE.2003.1199069`
- Aurum, Petersson, Wohlin 2002 `10.1002/stvr.243`
- Shull et al. 2012 `10.1007/s11334-010-0132-1`
- Sadowski et al. 2018 `10.1145/3183519.3183525`
- McIntosh et al. 2016 `10.1007/s10664-015-9381-9`
- Bacchelli & Bird 2013 `10.1109/ICSE.2013.6606617`
- Rigby & Bird 2013 `10.1145/2491411.2491444`
- IEEE Std 1028-2008 `10.1109/IEEESTD.2008.4601584` (Crossref type "standard", ISBN 9780738157689; clause text read from a reproduction of the standard)
- Boodoo et al. 2000, NRC Canada ERB-1081 (no DOI)
- SmartBear/Cisco: *Best Kept Secrets of Peer Code Review* (2006), ISBN 978-1-59916-067-2 (vendor publication, no DOI)

**Reading techniques:**
- Basili et al. 1996 `10.1007/BF00368702`
- Porter, Votta, Basili 1995 `10.1109/32.391380`
- Fusaro et al. 1997 `10.1023/A:1009742216007`
- Sandahl et al. 1998 `10.1023/A:1009724120285`
- Porter & Votta 1998 `10.1023/A:1009776104355`
- Regnell, Runeson, Thelin 2000 `10.1023/A:1009848320066`
- Shull, Rus, Basili 2000 `10.1109/2.869376`
- Laitenberger, El Emam, Harbich 2001 `10.1109/32.922713`
- Ciolkowski 2009 `10.1109/ESEM.2009.5316026`
- Lanubile & Visaggio 2000, ISERN-00-08 (no DOI)

**Notation comprehension:**
- Finney 1996 `10.1109/32.485225`
- Finney, Rennolls, Fedorec 1998 `10.1016/S0164-1212(98)00003-X`
- Finney, Fenton, Fedorec 1999 `10.1049/ip-sen:19990600`
- Zimmerman, Lundqvist, Leveson 2002 `10.1145/581344.581347` (alias `10.1145/581339.581347`)
- Snook & Harrison 2001 `10.1016/S0950-5849(00)00166-X`
- Snook & Harrison 2004 `10.1016/j.infsof.2004.04.003`
- Vinter, Loomes, Kornbrot 1998 `10.1109/METRIC.1998.731248`
- Czepa & Zdun 2020 `10.1109/TSE.2018.2859926`
- Czepa et al. 2019 `10.1007/s10270-019-00721-4`
- Czepa & Zdun 2019 `10.1145/3306608`
- Greenman et al. 2023 `10.22152/programming-journal.org/2023/7/7` (arXiv:2211.01677)
- Greenman et al. 2024 `10.1007/978-3-031-71162-6_30`
- Hall 1990 `10.1109/52.57887`

**FRET papers:**
- Giannakopoulou et al. 2021 `10.1016/j.infsof.2021.106590`
- Mavridou et al. 2020 `10.1109/RE48521.2020.00040`
- Conrad et al. 2022 `10.1145/3497775.3503685` (arXiv:2201.03641)

**Verified systems and specification defects:**
- Klein et al. 2009 `10.1145/1629575.1629596`
- Klein et al. 2014 `10.1145/2560537`
- Leroy 2009 `10.1145/1538788.1538814`
- Yang et al. 2011 `10.1145/1993498.1993532`
- Watt 2018 `10.1145/3167082`
- Hawblitzel et al. 2015 `10.1145/2815400.2815428`
- Fonseca et al. 2017 `10.1145/3064176.3064183`
- Newcombe et al. 2015 `10.1145/2699417`
- Aitken & Melham 2000 `10.1016/S0953-5438(99)00023-5`
- Jovanovic & Sullivan 2025 `10.1007/978-3-031-77382-2_18`
- Ospanov, Farnia, Yousefzadeh arXiv:2511.03108
- Ammanamanchi, Bhat, Biderman arXiv:2606.29493
- Azerbayev et al. arXiv:2302.12433

**Standards without retrievable text:** NASA-STD-8739.9 (document date 2013-06-17; Change 1 2016-10-07; status inactive per the NASA standards page). NASA-GB-A302 (1993) was read in full, except its missing Table 2.

**Derived computation:** `review_budget_derived.py` (Python 3.13, standard library only) is a local script name, not a published artifact. Its full input lists appear in the tables of Finding 8, so its results can be reproduced from the following core lines:

```python
h = L / r; sessions = ceil(h / 2.0); days = ceil(sessions / 2); team_ph = k * 2 * h
pred = 1 - (1 - p) ** k      # compared with reported team detection
```

## Revalidation

1. **Has anyone measured formal-spec review?** Re-run literature searches combining "specification review" or "inspection" with "theorem statement", "Isabelle", "Coq", "Lean", "TLA+" or "Alloy", together with "controlled experiment", "detection rate" or "time". Check new statement-faithfulness audits of formal benchmark datasets. A single controlled study would supersede Finding 8.
2. **FRET aids:** at a newer revision, check that `Requirement.g4`'s `nasa` rule, `formalization-descriptions.js` `getDescription`, `semanticDiagramsLib.js` and `tools/LTLSIM/` still exist. Recount `semantics.json` keys, and search `PUBLICATIONS.md` for "user study" or "comprehension".
3. **Practice guidance:** diff `review/developer/small-cls.md` and `review/reviewer/speed.md` in `google/eng-practices`.
4. **NASA-STD-8739.9:** obtain the PDF from the NASA standards site and read its inspection-rate and team-size tables. These are the main unverified normative numbers here.
5. **Derived budget:** rerun `review_budget_derived.py` with updated sizes or measured rates. The independence check needs only individual and team detection rates from any new study.
