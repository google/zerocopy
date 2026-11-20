# Structure and cost of completeness proofs for algorithmic checkers: mechanized Algorithm W principality, Harper–Pfenning LF equivalence and its Nominal Isabelle mechanization, worklist higher-rank inference in Abella, and the POPLMark Reloaded logical-relation benchmark

## Summary

- **Every examined completeness proof has the same skeleton.** It inducts on the *declarative* derivation with a strengthened statement that quantifies over an instantiation and a fresh-name supply. The concluding "witness" says that the algorithm's output is at least as general as any declarative solution. In the 1998 Isabelle MiniML development the statement is `∀S' A t' n. $S' A |- e :: t' --> new_tv n A --> (∃S t m. W e A n = Some (S,t,m) ∧ ∃R. $S' A = $R ($S A) ∧ t' = $R t)`. Garrigue's `typinf_principal` and Zhao–Oliveira–Schrijvers' Abella `completeness` (`wfj E -> tex E Jo -> dcl Jo -> judge E`) follow the same pattern. Fresh-variable and binder bookkeeping, not the central inductive argument, is where the examined authors report most of the extra effort (§5). Basis: source + documentation.
- **Neither 1999 Algorithm W mechanization verifies unification.**
  - The Isabelle MiniML theory states `mgu` as four unproved rules (`mgu_eq`, `mgu_mg`, `mgu_Some`, `mgu_free`). This was true in 1998, in the 2004 Isar version, and still at the current Archive of Formal Proofs revision (`axiomatization mgu`, `Type.thy` lines 170–175).
  - Dubois and Ménissier-Morain introduce unification's correctness, completeness and free-variable property "as axioms".
  - Garrigue's Coq development `certint` proves unification sound and complete (`ML_SP_Unify.v`, 1,830 lines), and proves type inference sound and principal for ML with structural polymorphism and recursive types. A token scan found no `Axiom`, `Admitted` or `admit`.

  Basis: source + documentation.
- **Harper–Pfenning's completeness argument for LF algorithmic equality survived mechanization; their soundness argument did not.**
  - The algorithm and its Kripke logical relation are indexed by *erased simple types* ("shapes of types, ignoring dependencies on terms").
  - Urban, Cheney and Berghofer mechanized the development in Isabelle/HOL with the Nominal Datatype Package: 14,585 lines, 575 lemmas.
  - They found "a gap in the proof of soundness": the omitted type-extensionality case. They also found a few lacunae: a missing erasure-preservation lemma, missing algorithmic validity rules, one omitted corollary part, and a typo.
  - They validated three repairs. One of them took 2 hours once the gap was confirmed. Formalizing up to soundness took "approximately six person-weeks".

  Basis: documentation.
- **Worklist judgments made higher-rank inference mechanizable, by replacing Dunfield–Krishnaswami's algorithm rather than mechanizing it.** Zhao, Oliveira and Schrijvers prove soundness, completeness and decidability of a new worklist algorithm against DK's declarative system in 7,977 lines of Abella. They report that DK 2013's Lemma 29 (Parallel Admissibility) "simply does not hold" and that DK 2019's Lemma 26 "appears to have the same issue". DK's 2020 arXiv revision still states Lemma 29 unchanged; its note mentions only name and URL updates. Basis: documentation.
- **Measured: the Abella development checks in 22.95 s wall time (21.40 s user) with a 30,092 KB peak RSS under Abella v2.0.7.** It produces 586 completed proofs and 568,940 bytes of `.thc` output. It does *not* check under Abella v2.0.8.3: the run stops in `decl.thm` at a `backchain ... with` step with `Error: Found logic variable at toplevel`. Basis: execution.
- **POPLMark Reloaded benchmarks strong normalization, not completeness.** It proves strong normalization of STLC (and of STLC with sums) by Kripke logical relations. Completeness of algorithmic equality (Crary's simply-typed version) is named as "a logical extension", not a challenge.
  - Binder infrastructure, not the logical relation, drives the size differences. The Beluga (HOAS) solution totals 446/918 lines; Coq well-typed 446/715; Agda 378/684 on top of a roughly 1,600-line library.
  - At the pinned repository revision, the F* solution contains two `admit ()`.
  - At the same revision, the Agda solution transitively depends on a `postulate` that was added because "With-abstraction failing under 2.6.2".

  Basis: documentation + source + derived.

## Applicability

The report compares independent proof developments and papers; it does not study their combination. Each subject's examined form is:

- **Naraschewski–Nipkow (JAR 1999)**: abstract page only. The examined source is the corresponding Isabelle theory `src/HOL/MiniML` in `isabelle-prover/mirror-isabelle` at `ffe95c3ab95d4b9903849cf9e0596e13e5309b8f` (1998-07-24, "Adapted to new datatype package"). Its `README.html` links that theory to the paper. Two later forms were also examined: the 2004 Isar conversion at `d4d27ad162365f9f3b5c125a6a69cfbfb3cdf9f4`, and the current Archive of Formal Proofs entry `thys/MiniML` in `isabelle-prover/mirror-afp-devel` at `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`. Claims about the axiomatized `mgu` hold for all three revisions. Line counts are per revision.
- **Dubois–Ménissier-Morain (JAR 1999)**: the authors' final PDF (dated 6/11/1998, Coq 6.1). No source was available.
- **Garrigue (APLAS 2010; MSCS 2014, volume 25 issue 4)**: extended-version text and `garrigue/certint` at `2c7fdb1e4b12a097e1e55e3899adb39d675ce3b6`. The README says the files are ported to Coq 8.20.1 and that porting "is the only change wrt. the version of september 2010". That claim was not independently checked. Per-file sizes at this revision are within 1.2% of the paper's Table 1, the largest difference being `ML_SP_Inference_wf.v` (3,481 vs 3,443).
- **Harper–Pfenning (TOCL 2005)**: examined through the arXiv abstract of the 2001 preprint (cs/0110028, 41 pages) and through the Urban–Cheney–Berghofer account. The full text was not read.
- **Urban–Cheney–Berghofer (TOCL 2011)**: arXiv 0804.1667v3 (2010-05-03). The Isabelle development is distributed from a URL, not a pinned repository, so its identity is the paper only.
- **Dunfield–Krishnaswami 2013 / 2019**: arXiv 1306.6032v2 (2020) and 1601.05106v4 (2020) metadata, and the Lemma 29 statement in the 2013 appendix.
- **Zhao–Oliveira–Schrijvers (ICFP 2019)**: paper text plus `JimmyZJX/TypingFormalization` at `7f0596031be9ee08b5f7b5a7678a284240e95805` (2019-06-26).
- **POPLMark Reloaded (JFP 2019)**: paper text (version dated 14 December 2019) plus `poplmark-reloaded/poplmark-reloaded` at `6d69fb3f9f4c135671330c8f34ed62b71494ba2d` (2021-07-26). That revision postdates the paper, so source observations apply to it, not to the paper's snapshot.
- **Executed checkers**: `abella-prover/abella` v2.0.7 (`5f6a6122e990f32a3718e1f7efaf29469fd22606`) and v2.0.8.3 (`e59565233045865942882271a34236c257edc8e1`), built from source with OCaml 5.4.0 on a 96-core Intel Xeon @ 2.60 GHz Linux host. Coq, Agda, Beluga, F* and Isabelle were not run.

## Findings

### 1. The common shape of an inference-completeness proof

| Development | Completeness statement (paraphrased; exact text in Evidence) | Induction on | Generalization over | Fresh names | Unification |
|---|---|---|---|---|---|
| Isabelle MiniML 1998 (`W.ML` lines 386–391) | If `$S' A ⊢ e :: t'` and `new_tv n A`, then `W e A n = Some (S,t,m)` and `∃R. $S' A = $R ($S A) ∧ t' = $R t` | expression `e` | arbitrary `S'`, `A`, `t'`, `n` | natural-number counter `n`; `new_tv n X` means "all type variables in X are below n" | axiomatized `mgu` (`Type.thy` lines 148–157) |
| Dubois–Ménissier-Morain | "if a type τ′ can be associated to e … where some free variables have been instantiated (via a substitution φ), then … W will succeed and yield the most general solution" | (paper) induction on expressions | substitution φ | "stamp" counter; a "new type variable" is greater than any free variable | `unify` assumed; "properties relative to the correctness and the completeness of the unify function as axioms" |
| Garrigue `certint` (`typinf_principal`, `ML_SP_Inference.v` line 3117) | If `K; θ(Γ) ⊢ e : θ(τ)` with a well-kinded θ extending the input θ₁, then `typinf` succeeds with `⟨K′, θ′, L′⟩` and some θ″ satisfying `K′ ⊢ θθ″ : K ∧ θθ″ ⊒ θ′ ∧ dom(θ″) ⊂ L′ \ L` | a fuel argument `h`, then the typing derivation | kinding environment K, substitution θ, used-name set L | explicit finite set L of used names; locally nameless binders with cofinite quantification | proved (`ML_SP_Unify.v`); a second variant uses a dependent termination measure (`*_wf.v`) |
| Zhao–Oliveira–Schrijvers (`completeness.thm` line 599) | `forall E Jo, wfj E -> tex E Jo -> dcl Jo -> judge E` | the declarative worklist derivation `dcl` | worklist instantiation `tex` | Abella ∇-quantified nominal variables (λ-tree syntax / HOAS) | none: existential variables are solved in place inside the worklist |

The corollary for closed programs in each development drops the generalization. For example, the 1998 `W_complete` reads `[] |- e :: t' ==> (? S t. (? m. W e [] n = Some(S,t,m)) & (? R. t' = $ R t))`. The current AFP `W_complete` (line 384) is discharged by `metis` from `W_complete_lemma`. Basis: source.

**1.1 Isabelle MiniML.**
- Substitutions are total functions `nat => typ`. Dubois and Ménissier-Morain remark that "Amazingly their proof requires no restriction to finite functions".
- Type schemes use the bound-variable instantiation `bound_typ_inst (%b. TVar (b+n))`.
- The 1998 split separates definitions (`.thy`) from proof scripts (`.ML`). That gives a direct specification-vs-proof measurement: 334 `.thy` lines vs 2,022 `.ML` lines, excluding `ROOT.ML`. The ratio is 6.05 on raw lines and 7.44 on non-blank lines (1,777 / 239).
- `W.ML` alone is 567 lines against a 38-line `W.thy`. The current Isar version totals 1,522 lines.

Basis: source (measured, `support/loc/miniml_loc.txt`) + derived.

**1.2 Dubois–Ménissier-Morain.**
- Type schemes encode bound variables positionally (`Gen_var n` is "the n-th generic variable discovered when σ is read from left to right") "in order to avoid to deal with alpha-conversion".
- Their correctness theorem drops Naraschewski–Nipkow's freshness hypothesis on W's input stamp.
- The new-variable lemmas alone "require a lot of supplementary properties (around 500 lines)".
- Totals: "7371 lines … 322 lemmas", described as "a very large piece of work with much backtracking". The count of definitions is illegible in the text extraction examined.
- The paper extends the system to value polymorphism with references.

Basis: documentation.

**1.3 Garrigue `certint`.**
- The type system is parameterized by a *constraint domain* (functors) for structural polymorphism. Equi-recursive types use a graph of kinds.
- Generalization must close free variables transitively through the kinding environment and split it into generalizable and non-generalizable parts. The paper calls proving soundness and principality "rather painful".
- Extending core-ML soundness to structural polymorphism doubled the proof "from 1000 lines to more than 2000". A single renaming lemma "required about 1000 lines".
- Building unification as a hand-written dependently typed function left its proof size unchanged and grew inference by "about 10%".
- The README credits the library files (`Lib_*`, `Metatheory*`) to Charguéraud's core-ML proof that accompanied "Engineering formal metatheory".
- `Lib_FinSet.v` declares `Parameter eq_ext` / `eq_if_Equal` inside `Module Type FinSet`; `Lib_FinSetImpl.v` (lines 311–326) proves them as theorems. They are interface parameters, not axioms.

Basis: documentation + source.

### 2. Algorithmic equality for LF: Harper–Pfenning vs. Urban–Cheney–Berghofer

**2.1 Argument structure (HP05, as stated in its abstract and restated by UCB).**
- The algorithm is type-directed. It interleaves weak-head reduction with structural comparison, and it runs at *erased* simple types τ = A⁻ ("shapes").
- Completeness (UCB Corollary 1) reads: "If Γ ⊢Σ M = N : A then Γ⁻ ⊢Σ⁻ M ⇔ N : A⁻" (plus the type and kind analogues). It goes through a Kripke logical relation `Γ⁻ ⊢Σ⁻ M = N ∈ [[A⁻]]` and its fundamental theorem.
- Soundness (UCB Theorem 2(1)) reads: "If Γ⁻ ⊢Σ⁻ M ⇔ N : A⁻ and Γ ⊢Σ M : A and Γ ⊢Σ N : A then Γ ⊢Σ M = N : A". It needs subject reduction for weak-head reduction.
- The abstract highlights that "both the algorithm itself and the logical relations rely only on the shapes of types, ignoring dependencies on terms". Because the relation is indexed by simple types, it can be defined by structural recursion on those types without first establishing normalization of dependent types (derived).

Basis: documentation + derived.

**2.2 What mechanization changed** (from UCB §3; each item is quoted or paraphrased from the paper):

| Kind of change | Item | Effect |
|---|---|---|
| Gap (corrected argument) | Soundness of algorithmic *type* equivalence: the omitted type-extensionality case "did not go through" | Three validated repairs: (1) add a type-extensionality rule to the definitional system, checked "within 2 hours"; (2) Harper's suggestion of weaker syntax-directed type-equivalence rules, which suffice without type-level λ, with the logical relation's type level redefined; (3) prove the original results as stated, using applied-variable lemmas (Lemmas 30–33) and extensionality of weak type equivalence |
| Added lemma | Algorithmic erasure preservation (Lemma 15), "omitted from HP05, but straightforward by induction", needed for symmetry and transitivity | New lemma |
| Added lemma | Corollary 1 part 3 (completeness for kinds) "was omitted from HP05" | New statement |
| Changed definition | Algorithmic signature and context validity rules were omitted in HP05 and added (Fig. 7) | New rules |
| Changed definition | "a trivial typographical error in the rule for type constants" | Fixed |
| Proof engineering | Interdependent definitional judgments: "each inductive proof must consider all 35 cases" | Large but routine |
| Sketched in HP05, formalized | Admissibility of strengthening and strong extensionality; quasicanonical forms; an adequacy example | Formalized |
| Partially formalized | Decidability: classical Isabelle/HOL; "inductive definitions of the complements" (quasidecidability) | Not a constructive decision procedure |

Basis: documentation.

**2.3 Binder infrastructure and cost.**
- The development uses nominal datatypes, which give α-equivalence classes and strong induction principles with the variable convention built in. Where nominal induction "could not be applied", binder cases became "much more labor-intensive" (for example, transitivity of algorithmic equivalence).
- A translation to locally nameless syntax (`LocallyN`) takes 4,674 of the 14,585 lines, or 32.0% by lines (derived). The paper's "about 25%" matches its bytes figure (179,148 of 668,105, or 26.8%, derived).
- The `Completeness` theory, which holds the logical relation, is 778 lines and 22 lemmas. That is less than the `Decidability` theory (2,087 lines) and the core `LF` theory (2,631 lines).
- The authors also generate executable code for the type checker from Isabelle/HOL.

Basis: documentation + derived.

### 3. Worklist higher-rank inference vs. Dunfield–Krishnaswami

**3.1 What DK prove, and what broke.** DK 2013 gives a declarative and an algorithmic bidirectional system for predicative higher-rank polymorphism, proved sound, complete and decidable on paper: "13 pages + 78-page appendix" (arXiv v2). DK 2019 adds existentials and indexed types: "28 pages, plus lemmas and proofs (191 pages)" (arXiv v4). ZOS describe the algorithmic contexts as follows:
- the contexts contain solved and unsolved existential variables `α̂ = τ`;
- they are threaded as input and output;
- context extension `Γ −→ Δ` relates them.

ZOS report "missing details as well as a few incorrect proofs and lemmas". Lemma 29 (Parallel Admissibility) "simply does not hold": it is required by instantiation soundness and typing completeness, and by Lemma 54, which is "used 13 times". Ningning Xie found the issue in 2016, and DK acknowledged it. In DK's 2020 arXiv v2 appendix, Lemma 29 is still stated as "If ΓL −→ ΔL and ΓL,ΓR −→ ΔL,ΔR then: (i) …, (ii) …, (iii) …", and the stated revision note covers only the author name and URLs. Basis: documentation.

**3.2 What the worklist reformulation changes.**
- ZOS unify the ordered context with the list of pending judgments ("worklist judgments"). This removes output contexts and solution records: a solved existential is substituted into the rest of the worklist immediately.
- Synthesis returns its result in continuation-passing style (`inferC X (r\ …)`).
- The algorithm is proved against DK's *declarative* system via a non-overlapping declarative variant (`declTyping.thm`) and a step-by-step declarative worklist `dcl` (`dcl.thm`).
- Main theorems, in Abella syntax:
  - `soundness : forall E, wfj E -> judge E -> exists Jo, tex E Jo /\ dc Jo` (`soundness.thm` line 755);
  - `completeness` (above);
  - `decidable : forall E, wfj E -> judge E \/ (judge E -> false)` (`decidability.thm` line 964);
  - `decidable_decl` (line 973).
- Decidability uses a lexicographic measure over several worklist sizes (`decidable_thm`, with arguments `NT NJ NO NV ND`).

Basis: source + documentation.

**3.3 Size, measured and reported.** The paper's Table 1 reports "7,977 lines of Abella code with a total of 60 definitions and 596 theorems". At the pinned revision, `wc -l` over `src/*.thm` gives 7,977 lines. `support/loc/abella_loc.py` counts 586 `Theorem` commands and zero `skip` tactics. Abella v2.0.7 printed 586 `Proof completed` messages. The 10-theorem gap from the paper's 596 is unexplained. Classifying non-blank, non-comment lines, 1,920 are specification (declarations and theorem statements) and 4,941 are tactic lines, a proof/spec ratio of 2.57. The heaviest files are:
- `completeness.thm`: 723 proof lines;
- `decidability.thm`: 703;
- `soundness.thm`: 671;
- `declTyping.thm`: 589;
- `inst_decidable.thm`: 586.

The README describes `soundness.thm` and `completeness.thm` as containing "a lot of uninteresting lemmas on the shape invariance during worklist instantiation". Basis: execution + source + derived.

**3.4 Checker-version sensitivity.**
- The paper says the scripts need an Abella development version, because "the developers just fixed a serious bug that accepts a simple proof of false, which also affects our proof". It names commit `92829a`; the README names `21ef1d` "or above". Both short SHAs resolve to January 2019 commits on `abella-prover/abella`, and release v2.0.7 is 10 commits ahead of `92829a` (GitHub compare).
- With v2.0.7, a clean batch check of `smallStep.thm`, which imports every other file, exits 0.
- With v2.0.8.3, the check stops at `decl.thm` line 92 (`backchain wft_weaken with E = E3, F = tyvar n1 :: nil, G = nil.`) with "Error: Found logic variable at toplevel. This usually means that the `search` tactic could not fully solve a goal."

The artifact's validity is therefore pinned to a checker version. Basis: execution.

### 4. POPLMark Reloaded

**4.1 The challenge.** The challenge is to prove strong normalization of STLC by a Kripke-style logical relation: soundness of the inductive SN characterization with respect to accessibility, plus the SN proof itself. Challenge 2 extends this to disjoint sums. Crary's completeness of algorithmic equality for STLC is mentioned as "a logical extension", not set as a challenge. Dependent types are not covered. The paper's solutions are Beluga (HOAS, first-class contexts and renamings), Coq (well-typed de Bruijn, and a scoped variant using Autosubst), and Agda (well-typed de Bruijn over the `generic-syntax` library). An F* solution from a 2018 master's thesis is mentioned in a footnote and is present in the repository. Basis: documentation.

**4.2 Reported lines of code (paper Fig. 15, columns STLC / STLC+; Coq scoped variant in parentheses):**

| Section | Beluga | Coq well-typed (scoped) | Agda |
|---|---|---|---|
| Library (`generic-syntax`) | – | – | 1600 / 1600 |
| Generated code | – | 0 (167) / 0 (218) | – |
| 3.1 Typed terms & reduction | 75 / 174 | 202 (74) / 265 (132) | 85 / 144 |
| 3.2 Defining strong normalization | 30 / 48 | 22 (22) / 30 (30) | 34 / 47 |
| Evaluation contexts (Agda only) | – | – | 38 / 57 |
| 3.3 Properties of sn | 163 / 355 | 97 (97) / 214 (212) | 97 / 219 |
| 3.4 Soundness of SN | 29 / 50 | 17 (17) / 24 (24) | 12 / 18 |
| 3.5 Properties of SN | 69 / 136 | 43 (47) / 67 (71) | 42 / 65 |
| 3.6 SN via logical predicate | 80 / 155 | 55 (72) / 115 (136) | 70 / 134 |
| Total | 446 / 918 | 446 (329) / 715 (605) | 378 / 684 |

Arithmetic check (derived):
- The Beluga, Agda, Coq-scoped and Coq-STLC+ columns sum to their printed totals. The Agda column includes the evaluation-contexts row.
- The Coq well-typed STLC column sums to 436, against a printed total of 446.

The paper attributes the size differences to binder support: Beluga needs "no additional lemmas w.r.t. syntax representation", Coq's set-up is "up to three times larger", and the generic library is "2 to 4 times the size of the code necessary to solve the actual challenge problem(s)". Basis: documentation + derived.

**4.3 Measured at the pinned revision** (non-blank, non-comment lines; `support/loc/poplmark_reloaded_loc.txt`):

| Development | LoC | Inside / outside `Proof…Qed` |
|---|---|---|
| Coq well-typed | 560 | 334 / 226 |
| Coq well-scoped | 732 | 445 / 287 |
| Coq well-typed + sums | 768 | 500 / 268 |
| Coq well-scoped + sums | 1,039 | 694 / 345 |
| Agda `STLC.agda` / `STLC+.agda` | 423 / 779 | n/a |
| Agda `generic-syntax` (vendored) | 2,196 | n/a |
| Beluga `stlc` / `stlc_sums` | 506 / 954 | n/a |
| F* | 1,863 | n/a |

The Agda counts agree with the paper's 425 and 784 to within 5 lines. The Coq and Beluga directory totals include files the paper's table distributes differently. Basis: source (measured) + derived.

**4.4 Trusted assumptions at the pinned revision.**
- **Coq.** The well-typed developments contain no `Axiom` token. The scoped developments' `axioms.v` declares `Axiom pext : forall P Q : Prop, (P <-> Q) -> (P = Q).` and imports functional extensionality from the Coq standard library.
- **F\*.** The F* files contain `admit ()` at `Sound.fst` line 95 (`admit () // adjust derivation hight`) and at `PropSN.fst` line 271.
- **Agda.** `agda/generic-syntax/Generic/Fusion.agda` line 180 opens a `postulate` for the binder case of the `SubRen` fusion (`aux : ...`). Line 186 carries the comment `-- Andreas, 2021-07-26: With-abstraction failing under 2.6.2`. `renβ` (line 277) uses `subren`, which is built from `SubRen`. `STLC.agda` uses `renβ` at lines 75, 136, 411 and 435, and `STLC.agda` imports `Generic`, which publicly opens `Generic.Fusion`. `Generic/Fusion-Specialised.agda` line 86 also postulates function extensionality.

The STLC SN development as checked at this revision therefore depends on at least one postulate. This is source inspection only: Agda was not run. Basis: source.

### 5. Coverage of features by each completeness or normalization proof

| Proof | Let-polymorphism | Unification proved | Recursive / structural types | Higher rank | Existentials / indexed types | Dependent types | Decidability | Executable algorithm |
|---|---|---|---|---|---|---|---|---|
| Isabelle MiniML | yes | no (axioms) | no | no | no | no | n/a (W total) | HOL function (code generation not examined) |
| Dubois–Ménissier-Morain | yes | no (axioms) | no | no | no | no | n/a | Coq function (extraction "not used") |
| Garrigue `certint` | yes | yes | yes / yes | no | no | no | via fuel / measure | extracted OCaml (`typinf.ml`) |
| HP05 / UCB | n/a | n/a | n/a | n/a | n/a | LF (λΠ) | partial (UCB) | Isabelle code generation (UCB) |
| ZOS worklist | n/a | no unification: in-place solving | no | yes (predicative) | no | no | yes | relational (Abella) |
| DK 2013 / 2019 (paper) | n/a | n/a | no | yes | no / yes (2019) | no | yes (paper) | paper algorithm |
| POPLMark Reloaded | n/a | n/a | no | no | no | no | n/a (SN) | n/a |

In each source the stated main cost driver is:
- fresh names and substitution algebra (Dubois–Ménissier-Morain: "the management of the new type variables is always ignored in a mathematical proof but it cannot be ignored in any formal proof");
- kinds and generalization (Garrigue);
- 35-case mutual inductions and the locally nameless translation (UCB);
- scoping and output contexts (ZOS);
- binder representation (POPLMark Reloaded).

Basis: documentation + source.

### 6. Performance and resource footprint (L1–L6)

Every cell is measured, cited, derived, or marked `not measured`.

| Subject | L1 size / effort | L2 checker build | L3 elaboration | L4 generated code | L5 proof check | L6 artifacts / RSS |
|---|---|---|---|---|---|---|
| Isabelle MiniML 1998 | 334 spec + 2,022 proof-script lines (measured); ratio 6.05 (derived); effort not reported in material examined | not measured | not measured | not measured | not measured | not measured |
| AFP MiniML (current) | 1,522 lines (measured) | not measured | not measured | not measured | not measured | not measured |
| Dubois–Ménissier-Morain | 7,371 lines, 322 lemmas (cited) | not measured | not measured | n/a | not measured | not measured |
| Garrigue `certint` | paper Table 1 component lines sum to 21,895 (derived); revision: 24,700 `wc -l` lines, 21,298 non-blank non-comment, 14,313 inside / 6,985 outside proofs, ratio 2.05 (measured) | not measured | not measured | extracted `typinf.ml` 80,744 bytes and `typinf.mli` 107,926 bytes at the revision (measured from tree metadata) | `times.txt`: 628 s (Core solo 1.2 GHz), 390 s (Core duo 2 GHz), 310 s (Core duo 2.53 GHz) with Coq 8.2; 346 s with Coq 8.2pl1 (cited) | not measured |
| UCB LF | 14,585 lines, 575 lemmas, 668,105 bytes; about 6 person-weeks to soundness; 2 h to validate a repair (cited) | not measured | not measured | Isabelle code generation (not measured) | not measured | not measured |
| DK 2013 / 2019 | 78-page and 191-page proof appendices (cited, arXiv) | n/a | n/a | n/a | n/a (paper) | n/a |
| ZOS Abella | 7,977 lines (measured and cited); 1,920 spec / 4,941 proof lines, ratio 2.57 (measured, derived); 586 theorems (measured) vs 596 (cited) | Abella v2.0.8.3 `dune build` 1 min 14 s wall including example checks (measured); v2.0.7 build not timed | n/a | n/a | full check 22.95 s wall, 21.40 s user, Abella v2.0.7 (measured) | 30,092 KB max RSS; 14 `.thc` files, 568,940 bytes (measured) |
| POPLMark Reloaded | Fig. 15 (cited); revision counts in §4.3 (measured) | not measured | not measured | n/a | not measured | not measured |

The ZOS row's Abella build includes example checks because the build ran the repository's dune rules, which invoke `abella.exe` on the examples.

### 7. Human comprehensibility and conceptual simplicity (C1–C2)

- **Statement legibility (C1).**
  - Garrigue's simplified principality statement (paper Fig. 10) has five hypotheses, and the paper states that the inductive versions "become very long". The Coq predicate `principality` (`ML_SP_Inference.v` lines 2020–2032) has eleven premises, from `is_subst S0` to `trm_depth t < h`, and a conclusion that existentially quantifies `K'`, `S'` and `L'`, then `S''`, followed by four conjuncts. The closed-program corollaries are two lines each.
  - The Isabelle MiniML statement fits in three lines.
  - ZOS's top-level `completeness` statement is one line, but only because `tex` and `dcl` hide the instantiation relation. Reading it requires `trans.thm` (616 SLOC per the paper's table) and `dcl.thm`.

  A human auditor must read the definitions of the auxiliary relations, not only the theorem. Basis: source + documentation.
- **Diagnostic legibility.** Checker version drift (§3.4) surfaces as an error far from its cause ("Found logic variable at toplevel" inside a `backchain`), with a hint that blames `search`. Basis: execution.
- **One invariant, three mechanisms (C2).** "The algorithm's answer is more general than any declarative answer" is implemented in three ways:
  - as an explicit substitution witness R (W);
  - as substitution with kinding-environment entailment (`certint`);
  - as a worklist-instantiation relation `tex` (ZOS).

  The common abstraction is a *refinement relation* between algorithmic and declarative states, preserved backward along declarative derivations. The worklist formulation makes this uniform for checking and synthesis by turning synthesis into a continuation judgment. That removes a special case (output contexts) rather than moving it into an adapter. Unification disappears as a separate component in ZOS because existential solving is a worklist step. In W it is a component and, in two of the three W developments, an axiom. Basis: derived.

### 8. Validation of the proofs and their checkers (V1–V4)

- **V1 (specification adequacy).**
  - All developments state completeness against their own declarative system. None examined includes mutation testing of the declarative rules.
  - UCB includes an adequacy example (first-order logic syntax, Theorem 17) and a translation to locally nameless syntax to address "correctness of the representation".
  - ZOS prove equivalence of their declarative variant with DK's declarative rules (`declTyping.thm`) and of small-step with big-step forms (`smallStep.thm`).
- **V2 (checker soundness).**
  - The ZOS artifact required an Abella fix for "a simple proof of false" (cited).
  - The measured v2.0.8.3 failure shows that the artifact depends on checker behavior (measured).
  - Cross-checking with an independent checker is not available for Abella developments examined here.
  - `certint`'s README records successive Coq ports (8.2 to 8.20.1).
- **V3** (concurrency, crash, physical) does not apply to these proof developments.
- **V4** (human comprehension): no empirical study of how readers understand the statements was examined.

## Boundaries

- **Not examined:**
  - the full texts of Naraschewski–Nipkow (JAR 1999) and Harper–Pfenning (TOCL 2005; only the arXiv abstract and UCB's restatement were read);
  - Isabelle checking of any MiniML revision;
  - Coq checking of `certint` or the POPLMark Reloaded Coq solutions;
  - Agda, Beluga and F* checking;
  - the UCB Isabelle sources, which are not available at a pinned revision;
  - DK's 2019 Lemma 26 argument itself (only ZOS's report of it);
  - Garrigue's APLAS 2010 version in detail;
  - Twelf/Beluga mechanizations of LF metatheory;
  - completeness proofs for bidirectional dependent type checkers.
- **Unknown:**
  - why the paper reports 596 theorems while the pinned scripts contain 586 `Theorem` commands;
  - whether `certint` at the pinned revision checks under its stated Coq version, since it was not built;
  - whether the Agda postulate in `Generic/Fusion.agda` is still present at later revisions;
  - the cause of the 10-line discrepancy in the Coq well-typed STLC column of POPLMark Reloaded Fig. 15.
- **Not measured:** every `not measured` cell in Finding 6, notably all Coq, Isabelle, Agda, Beluga and F* checking times and memory, and all elaboration latencies.
- **Known not to apply:** POPLMark Reloaded does not contain a completeness-of-algorithmic-equality proof, and none of its solutions treats dependent types. ZOS do not mechanize DK's own algorithm, and do not cover existentials or indexed types.
- **Unsupported:** the ZOS artifact does not check under Abella v2.0.8.3 (measured).
- **Stronger conclusions not supported:**
  - That the 1999 Algorithm W mechanizations establish completeness unconditionally: both assume unification.
  - That HP05's completeness proof needed repair: UCB's gap is in soundness.
  - That DK's results are false: ZOS state that they "believe that these problems do not invalidate their work".
  - That the POPLMark Reloaded Agda and F* solutions are axiom-free at the pinned revision.

## Evidence

Evidence was gathered on 2026-11-20 (UTC).

**Repositories:**
- `isabelle-prover/mirror-isabelle` @ `ffe95c3ab95d4b9903849cf9e0596e13e5309b8f`, `src/HOL/MiniML/`:
  - `W.thy` (algorithm `W`, lines 9–38);
  - `W.ML` (header line 6 "Correctness and completeness of type inference algorithm W"; `W_correct_lemma` ends line 384; `W_complete_lemma` statement lines 386–391, ends line 559; `W_complete` lines 561–566);
  - `Type.thy` (`mgu` and its `rules`, lines 148–157);
  - `README.html`.
- `isabelle-prover/mirror-isabelle` @ `d4d27ad162365f9f3b5c125a6a69cfbfb3cdf9f4`, `src/HOL/MiniML/Type.thy`: lines 146–153, `axioms mgu_eq ... mgu_free`.
- `isabelle-prover/mirror-afp-devel` @ `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`, `thys/MiniML/`:
  - `Type.thy` lines 170–175 (`axiomatization mgu`);
  - `W.thy` lines 189 (`W_correct_lemma`), 243 (`W_complete_lemma`), 384–386 (`W_complete`, proved `by (metis W_complete_lemma app_subst_Nil new_tv_Nil)`).
- `garrigue/certint` @ `2c7fdb1e4b12a097e1e55e3899adb39d675ce3b6`:
  - `README.md`; `times.txt`; `CHANGES.md`;
  - `ML_SP_Inference.v` (`principality` definition lines 2020–2032, `typinf_sound` line 1602, `typinf_principal` line 3117, `typinf_principal'` lines 3132–3136);
  - `ML_SP_Unify.v`;
  - `Lib_FinSet.v` lines 15–36; `Lib_FinSetImpl.v` lines 293–326.
- `JimmyZJX/TypingFormalization` @ `7f0596031be9ee08b5f7b5a7678a284240e95805`:
  - `src/readme.md`; `src/typing.thm` (`wfj` line 83, `judge` line 138);
  - `src/trans.thm` (`tex` line 21, `dc` line 528); `src/dcl.thm` (`dcl` line 3, `dcl_complete` line 359);
  - `src/soundness.thm` line 755; `src/completeness.thm` lines 599 and 1081–1121;
  - `src/decidability.thm` lines 533, 964 and 973; `src/decl.thm` line 92.
- `poplmark-reloaded/poplmark-reloaded` @ `6d69fb3f9f4c135671330c8f34ed62b71494ba2d`:
  - `coq/well-scoped/axioms.v` line 30; `f-star/Sound.fst` line 95; `f-star/PropSN.fst` line 271; `f-star/loc.txt`;
  - `agda/generic-syntax/Generic.agda` (imports and `open module fus = Generic.Fusion public`);
  - `agda/generic-syntax/Generic/Fusion.agda` lines 169–221 and 277–282;
  - `agda/generic-syntax/Generic/Fusion-Specialised.agda` line 86;
  - `agda/STLC.agda` lines 75, 136, 411 and 435; `agda/README`.
- `abella-prover/abella` @ `5f6a6122e990f32a3718e1f7efaf29469fd22606` (v2.0.7) and @ `e59565233045865942882271a34236c257edc8e1` (v2.0.8.3): built from source and executed.

**Literature (DOIs verified against Crossref; arXiv identifiers verified on arXiv):**
- W. Naraschewski, T. Nipkow, "Type Inference Verified: Algorithm W in Isabelle/HOL", JAR 23(3):299–318, 1999, `10.1023/A:1006277616879`.
- C. Dubois, V. Ménissier-Morain, "Certification of a Type Inference Tool for ML: Damas–Milner within Coq", JAR 23(3):319–346, 1999, `10.1023/A:1006285817788`.
- J. Garrigue, "A Certified Implementation of ML with Structural Polymorphism", APLAS 2010, LNCS pp. 360–375, `10.1007/978-3-642-17164-2_25`.
- J. Garrigue, "A certified implementation of ML with structural polymorphism and recursive types", MSCS 25(4):867–891 (published online 2014-11-11), `10.1017/S0960129513000066`.
- R. Harper, F. Pfenning, "On equivalence and canonical forms in the LF type theory", ACM TOCL 6(1):61–101, 2005, `10.1145/1042038.1042041`. Preprint arXiv:cs/0110028.
- C. Urban, J. Cheney, S. Berghofer, "Mechanizing the metatheory of LF", ACM TOCL 12(2):1–42, 2011, `10.1145/1877714.1877721`. Preprint arXiv:0804.1667v3.
- J. Dunfield, N. R. Krishnaswami, "Complete and easy bidirectional typechecking for higher-rank polymorphism", ICFP 2013, pp. 429–442, `10.1145/2500365.2500582`. Preprint arXiv:1306.6032v2.
- J. Dunfield, N. R. Krishnaswami, "Sound and complete bidirectional typechecking for higher-rank polymorphism with existentials and indexed types", PACMPL 3(POPL):1–28, 2019, `10.1145/3290322`. Preprint arXiv:1601.05106v4.
- J. Zhao, B. C. d. S. Oliveira, T. Schrijvers, "A mechanical formalization of higher-ranked polymorphic type inference", PACMPL 3(ICFP):1–29, 2019, `10.1145/3341716`.
- A. Abel, G. Allais, A. Hameer, B. Pientka, A. Momigliano, S. Schäfer, K. Stark, "POPLMark reloaded: Mechanizing proofs by logical relations", JFP 29, 2019, `10.1017/S0956796819000170`.

**Execution** (2026-11-20; Linux; Intel Xeon @ 2.60 GHz, 96 cores; OCaml 5.4.0; commands and outputs in `support/`):
- Abella v2.0.7 built with `OCAMLPARAM="_,warn-error=-a,w=-a" make all`. A clean check, `/usr/bin/time -v abella smallStep.thm -o smallStep.out`, exited 0 (`support/abella/v2.0.7_full_check_time.txt`).
- Abella v2.0.8.3 built with `dune build`. Checking the same inputs stops in `decl.thm` (`support/abella/v2.0.8.3_decl_failure_excerpt.txt`). Input hashes are in `support/abella/inputs.sha256`.
- Line counts come from `support/loc/*.py`, with outputs in `support/loc/*.txt`.

## Revalidation

- **Abella artifact:** rebuild Abella at the tag under test, rerun the clean `smallStep.thm` check, and compare the exit status, the 586 `Proof completed` count and the time against `support/abella/`. A pass on a newer Abella would retire the v2.0.8.3 incompatibility finding. A failure at a different line would locate a new incompatibility.
- **Unification assumptions:** grep `thys/MiniML/Type.thy` in the AFP mirror for `axiomatization mgu`. In `certint`, grep all `.v` files for `Axiom|Admitted|admit`. A Coq `Print Assumptions typinf_principal'` after building would turn the token scan into a kernel-level check.
- **POPLMark Reloaded trust:** grep `f-star/*.fst` for `admit ()` and `agda/generic-syntax/Generic/Fusion.agda` for `postulate`, then rerun `count_loc.py` on the target revision. Running `agda STLC.agda` without `--safe` and then with `--safe` would confirm whether the postulate is reachable.
- **DK Lemma 29:** check the latest arXiv version of 1306.6032 for a changed statement of Lemma 29 or an erratum.
- **Literature-only claims** about UCB, Dubois–Ménissier-Morain and Garrigue's paper do not change. Extending them requires obtaining and checking the UCB Isabelle sources, for which no immutable revision was available.
