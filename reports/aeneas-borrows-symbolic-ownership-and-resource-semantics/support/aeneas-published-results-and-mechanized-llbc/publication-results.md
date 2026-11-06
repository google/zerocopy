# Aeneas publication theorem and result inventory

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

The 2024 long paper contains **37 numbered results: 10 theorems and 27 lemmas**, plus three numbered definitions. The thesis's Aeneas soundness material contains **38 numbered results: 11 theorems and 27 lemmas**. The extra thesis theorem is the composed LLBC-to-HLPL statement. Neither set is a proof that the full production Rust → Charon → Aeneas → Lean implementation preserves semantics.

The essential premises are not cosmetic: all functions must satisfy borrow_checks for the borrow-checker theorem; initial states must be related, and the backward theorem additionally connects the concrete state to the signature-derived symbolic initialization. Panic and divergence are admitted safe outcomes. Join correctness assumes successful join/collapse and removal of all side markers. Several printed formulas have binding/label defects, including a visually confirmed missing initial-state relation in thesis Theorem 5. The inventory preserves these rather than silently replacing publication syntax by a stronger or corrected statement.

The 2022 paper, Charon tool paper and 2026 publications have no numbered semantic metatheorem blocks in the examined editions. They do contain application proofs, model contracts, axioms and illustrative backend lemmas; those are inventoried separately with their assumptions and proof status.

## Applicability

This is the A03.2 supplement to the G01 publication/mechanization report for google/zerocopy#3886. It examines:

- arXiv:2206.07185v2, all 43 PDF pages and its complete HTML, including appendices;
- arXiv:2404.02680v2, all 86 PDF pages and complete HTML, including appendices A–F;
- Son Ho's thesis PDF at the recorded SHA-256, Chapter 11, its soundness appendices C–G and the relevant backend results of Chapter 14;
- arXiv:2410.18042v2, complete Charon tool-paper HTML, Sections 1–5 and references;
- arXiv:2609.15648v1, complete main text/appendices A–C;
- arXiv:2605.30106v1, complete main text, plus the cited Hax proof PR head for exact downstream theorem signatures;
- selected current mechanized-llbc source analogues at 2762a26a3c0792017fa7a731aab1683d9a4cf23a.

Basis: **documentation** for publications, **source** for mathematical expressions and current proof scripts, and **derived** for comparisons and identified literal-statement ambiguities. There is no new **execution** evidence: no build, extraction, proof-assistant replay or Print Assumptions occurred. Rendering publication pages and parsing source documents are reading operations, not execution of the upstream toolchain.

The enumeration is complete for the numbered theorem/lemma declarations in those specified semantic sections and for displayed/named application/backend statements recorded below. It is not an inventory of every theorem in every linked application repository, imported mathematical library or the thesis's unrelated protocol/metaprogramming work. A case-study algorithm name or aggregate theorem count does not identify thousands of individual theorem statements in the publication.

## Findings

### Machine inventory and notation

[publication-results-inventory.json](publication-results-inventory.json) records each numbered result separately: identifier, exact source locator/PDF page, quantified domain, premises, conclusion, exclusion profile, the publication's mathematical-expression strings and current-source analogue/status where established. Its 2024 mathematical_source field preserves MathML alttext in source order, including inline symbols and displayed rows; it does not normalize defects into executable proof-assistant syntax. The thesis rows give exact PDF locators and corresponding paper-result IDs, without asserting identical typography. Three definitions are explicitly marked definitions, not additional proved theorems.

[publication-application-inventory.json](publication-application-inventory.json) separately records four 2022 application/assumption contracts, 13 thesis backend/example statements, seven displayed SymCrypt theorem/axiom/predicate declarations, and nine named declarations in the pipeline paper's referenced proof source. It retains exact signatures where printed or directly acquired; statements omitted by the publication are identified as such.

In the table, Omega denotes an environment/state; <= is the paper's reflexive-transitive relation, whose meaning differs across language boundaries. A statement evaluation returns a control outcome and state, or divergence. Rvalue evaluations return a value and state. framable, sloans_incl, compatibility, concretization, initialization and projection predicates are substantive premises, not generic logical truths. Their displayed formulas remain in the machine inventory or the exact linked definitions.

### Complete 2024 numbered-result ledger

All entries concern the paper's formal languages and rules. They exclude production compiler/frontend refinement, arbitrary unsafe/concurrent Rust and completeness of the implemented heuristic search. Additional exclusions are recorded per result through the profile in inventory.json. The current-source column reports related declarations only; it never means the entire paper statement was mechanically checked.

| Result | Quantified domain | Premises and conclusion | Current source analogue/status |
|---|---|---|---|
| [Theorem 2.2](https://arxiv.org/html/2404.02680v2#S2.Thmtheorem2) | L+ states Omega1,Omega2,Omega2prime; expressions e,eprime | Related hybrid states; right hybrid evaluation ⇒ Exists left hybrid evaluation with the same expression result and related final state | No exact mapping established |
| [Theorem 3.1](https://arxiv.org/html/2404.02680v2#S3.Thmtheorem1) | HLPL+ states Omega_l,Omega_r; all s,r,Omega_rprime | Initial state relation; right statement evaluation ⇒ Left evaluation with the same control outcome and related final state | stmt_preserves_HLPL_plus_rel (Qed source) |
| [Theorem 3.2](https://arxiv.org/html/2404.02680v2#S3.Thmtheorem2) | Omega_l in HLPL; Omega_r in HLPL+; all s,r,Omega_rprime | Initial relation and right HLPL+ evaluation; HLPL stability is used in proof ⇒ Left HLPL evaluation and final relation | No exact mapping established |
| [Theorem 3.3](https://arxiv.org/html/2404.02680v2#S3.Thmtheorem3) | Omega in LLBC; all s,r,Omega_r | LLBC statement evaluation ⇒ HLPL+ evaluation from the same initial state and related final state | No exact mapping established |
| [Theorem 3.4](https://arxiv.org/html/2404.02680v2#S3.Thmtheorem4) | Omega_l in PL; Omega_h in LLBC; all statements s | Initial PL/LLBC relation; LLBC diverges at every step index ⇒ PL diverges | No exact mapping established |
| [Theorem 4.1](https://arxiv.org/html/2404.02680v2#S4.Thmtheorem1) | Concrete Omega, symbolic Omega#; every s and symbolic outcome set S# | All functions in program P borrow_check; concrete/symbolic relation; successful symbolic evaluation ⇒ Concrete execution diverges, panics, or has a related nonpanic outcome in S# | No exact mapping established |
| [Theorem 4.2](https://arxiv.org/html/2404.02680v2#S4.Thmtheorem2) | PL/LLBC initial states; every g<regions,types>; every PL result res | init determines symbolic input abstractions/state; every P function borrow_checks; PL<=LLBC<=initial symbolic state; PL evaluation of g.body ⇒ Exists LLBC evaluation; both diverge or yield the same outcome with related final states | No exact mapping established |
| [Theorem 5.1](https://arxiv.org/html/2404.02680v2#S5.Thmtheorem1) | All left/right/joined/collapsed states | Successful join then collapse; collapsed state contains no side markers ⇒ Each original side is related to the collapsed result | No exact mapping established |
| [Lemma A.1](https://arxiv.org/html/2404.02680v2#A1.Thmtheorem1) | HLPL+ states; all rvalues and right values/final states | Initial relation and right rvalue evaluation ⇒ Left rvalue evaluation; related (value,state) pairs, defined using an anonymous binding | rvalue_preserves_HLPL_plus_rel (Qed source) |
| [Lemma A.2](https://arxiv.org/html/2404.02680v2#A1.Thmtheorem2) | All places p,read values; contextual Omega1 and location ell from enclosing case | Immutable read; left/right differ at one pointer/shared-borrow hole ⇒ Same read or a value context exposing corresponding ptr/borrow at that hole | No exact mapping established |
| [Lemma A.3](https://arxiv.org/html/2404.02680v2#A1.Thmtheorem3) | Context Omega1; ell0,ell1,v; all p,read values | Nested locations shape; no other loc ell1 in stated context; substituted left state; immutable read ⇒ Substituted equal read or corresponding value context with collapsed nested locations | No exact mapping established |
| [Lemma A.4](https://arxiv.org/html/2404.02680v2#A1.Thmtheorem4) | All p,read values; contextual states,ell,v | Immutable read; pointer plus anonymous location on left versus Box on right ⇒ Same read or value context relating ptr ell and Box v | No exact mapping established |
| [Lemma A.5](https://arxiv.org/html/2404.02680v2#A1.Thmtheorem5) | All p,read values; context Omega1,ell from enclosing case | Move-capability read; pointer versus shared/reserved-borrow hole ⇒ Exists decomposition separating moved component or a value context; read/write facts hold for every replacement value | No exact mapping established |
| [Lemma A.6](https://arxiv.org/html/2404.02680v2#A1.Thmtheorem6) | All p,read values; two-hole context from Le-MutBorrow-To-Ptr proof case | Move-capability read under the enclosing mutable borrow/loan-to-location case ⇒ Three-hole or two-hole/value-context decomposition; universal read/write replacement facts | No exact mapping established |
| [Lemma A.7](https://arxiv.org/html/2404.02680v2#A1.Thmtheorem7) | HLPL+ states; rvalue rv,place p; every right final state | Initial relation; successful right assignment with unit outcome ⇒ Successful left assignment and related final states | store_preserves_HLPL_plus_rel (Qed source) |
| [Lemma A.8](https://arxiv.org/html/2404.02680v2#A1.Thmtheorem8) | HLPL+ states; every right reorganized state | Initial relation; right reorganization ⇒ Exists related left reorganization | reorg_preserves_HLPL_plus_rel (Qed source) |
| [Theorem B.2](https://arxiv.org/html/2404.02680v2#A2.Thmtheorem2) | PL/HLPL states; all s,r,HLPL final states | PL<=HLPL; HLPL evaluation ⇒ PL evaluation with identical outcome and related final states | No exact mapping established |
| [Lemma B.3](https://arxiv.org/html/2404.02680v2#A2.Thmtheorem3) | HLPL state,rvalue,value,final state | HLPL rvalue evaluates to that value and final state ⇒ Returned value contains no loc wrapper | No exact mapping established |
| [Lemma B.4](https://arxiv.org/html/2404.02680v2#A2.Thmtheorem4) | PL/HLPL states,blockof,addrof; all places p,capabilities k,values v,types tau | Compatibility and state concretization relation; typed HLPL read ⇒ Exists PL byte/cell vector read, related to concretized HLPL value | HLPL_PL_Read (Qed source) |
| [Lemma B.5](https://arxiv.org/html/2404.02680v2#A2.Thmtheorem5) | PL/HLPL states,blockof,addrof; all rvalues,values,HLPL final states | Compatibility; state concretization relation; HLPL rvalue evaluation ⇒ Exists updated address maps and byte vector; PL evaluation and compatible related states/values (printed binding anomaly noted) | Rvalue_Preserves_PL_HLPL_Rel (Qed source) |
| [Lemma B.6](https://arxiv.org/html/2404.02680v2#A2.Thmtheorem6) | PL/HLPL states; all p,rv,HLPL final states | Initial relation; successful HLPL assignment ⇒ Successful PL assignment and related final states | Assign_Preserves_PL_HLPL_Rel (Abort source) |
| [Lemma B.7](https://arxiv.org/html/2404.02680v2#A2.Thmtheorem7) | PL/HLPL states and quantified HLPL final state | Printed reorganization formula has inconsistent state labels; retain literal source ⇒ Intended role is preservation under HLPL reorganization with compatible PL state; exact printed formula is not silently repaired | Reorg_Preserves_PL_HLPL_Rel (Qed source) |
| [Lemma C.1](https://arxiv.org/html/2404.02680v2#A3.Thmtheorem1) | LLBC+ states; all rvalues and right values/final states | Initial symbolic-abstraction relation and right rvalue evaluation ⇒ Left rvalue evaluation with related (value,state) pairs | rvalue_preserves_LLBC_plus_rel (Qed source) |
| [Lemma C.2](https://arxiv.org/html/2404.02680v2#A3.Thmtheorem2) | LLBC+ states; rv,p; every right final state | Initial relation; successful right assignment ⇒ Successful left assignment with related final state | store_preserves_LLBC_plus_rel (Qed source) |
| [Lemma C.3](https://arxiv.org/html/2404.02680v2#A3.Thmtheorem3) | Printed domain says HLPL+; title/context concern LLBC+; all right final states | Initial relation; right reorganization ⇒ Left reorganization and final relation; domain discrepancy retained | reorg_preservation (Qed source) |
| [Theorem C.4](https://arxiv.org/html/2404.02680v2#A3.Thmtheorem4) | LLBC+ states; all s,v_r,Omega_rprime as printed | Initial relation and right evaluation; printed formula uses unbound r instead of quantified v_r ⇒ Exists related left evaluation; differing arrow glyph also retained | stmt_preserves_LLBC_plus_rel (Qed source) |
| [Lemma D.1](https://arxiv.org/html/2404.02680v2#A4.Thmtheorem1) | LLBC+ states and identifier substitution subst | Initial abstraction relation ⇒ Pointwise substitution preserves relation | No exact mapping established |
| [Lemma D.2](https://arxiv.org/html/2404.02680v2#A4.Thmtheorem2) | LLBC+ states Omega,Omega_prime; statement s,outcome r,identifier subst | Printed Omega<=Omega_prime plus evaluation premise ⇒ Evaluation commutes with substitution | No exact mapping established |
| [Lemma D.3](https://arxiv.org/html/2404.02680v2#A4.Thmtheorem3) | LLBC+ states; every frame Omega_f | State relation and explicit framable predicate controlling fresh/shared IDs, symbolic values and abstractions ⇒ Relation preserved after adding same frame | No exact mapping established |
| [Lemma D.4](https://arxiv.org/html/2404.02680v2#A4.Thmtheorem4) | LLBC+ states; statement/outcome; every frame Omega_f | Evaluation and framable predicate from D.3 ⇒ Evaluation preserved after adding same frame | No exact mapping established |
| [Lemma D.5](https://arxiv.org/html/2404.02680v2#A4.Thmtheorem5) | Printed Omega and Omega# domain says LLBC#; step n,statement s,outcome set S# | All functions borrow_check; initial relation; symbolic evaluation ⇒ At index n concrete diverges/panics, or has a related successful outcome in S#; successful branch is unindexed as printed | simulation_LLBC_sharp_LLBC_plus (Qed source) |
| [Lemma D.6](https://arxiv.org/html/2404.02680v2#A4.Thmtheorem6) | Single argument value/type/context,regions; existential reborrow abstractions | init_extern and proj_output equations; unions defining initial/final/signature abstractions; shared input borrows have matching initial shared loans ⇒ Exist reborrowing frame and initial/final relations plus framable predicate; exact binding conventions in source formula | No exact mapping established |
| [Lemma D.7](https://arxiv.org/html/2404.02680v2#A4.Thmtheorem7) | Families of argument types/values indexed by i,regions; existential reborrow abstractions | Multiargument versions of init_extern/proj_output and abstraction-union equations; shared-loan premise ⇒ Exist reborrowing frame, initial/final relations and framable predicate for function body | No exact mapping established |
| [Lemma E.1](https://arxiv.org/html/2404.02680v2#A5.Thmtheorem1) | Original states; state-with-hole contexts; input/joined values; fresh abstraction family | Each original is related to current hole-filled state; sloans_incl; wf_join_hole; successful value join ⇒ Both projections of joined value/new abstractions stay above originals and preserve shared-loan inclusion | No exact mapping established |
| [Lemma E.2](https://arxiv.org/html/2404.02680v2#A5.Thmtheorem2) | Original states,current left/right states,accumulated/joined states | Projected accumulator plus current sides bound originals; sloans_incl; successful state join ⇒ Both projections of final accumulated join bound originals | No exact mapping established |
| [Lemma E.3](https://arxiv.org/html/2404.02680v2#A5.Thmtheorem3) | Region abstractions A0,A1,A; both marker sides m | Successful abstraction merge ⇒ Marker projection commutes with abstraction merge | No exact mapping established |
| [Lemma E.4](https://arxiv.org/html/2404.02680v2#A5.Thmtheorem4) | All states Omega,Omega_prime and both marker sides | Successful collapse ⇒ Each projected initial state is related to projected collapsed state | No exact mapping established |

Definition 2.1 defines forward simulation; it is referenced as “Theorem 2.1” in surrounding text but is not another proved theorem. Definition 2.3 is stability of a lower language within the hybrid language. Definition B.1 defines the PL/HLPL relation using existence of compatible blockof/addrof maps and concretization. Omitting those definitions can make the theorem statements appear stronger than they are.

Theorem 2.2 is a proof template instantiated for the paper languages. It is not a universal statement that any two languages sharing syntax automatically simulate each other. The hybrid union must use the necessary administrative rules and exclude rules that would break stability.

Theorem 3.4 concerns divergence quantified over every step index; the zero-fuel result alone is not divergence. Theorem 4.1 allows a concrete execution to panic or diverge. It establishes the modeled safety/borrow-checking property rather than termination or panic-freedom. Theorem 4.2 uses all-function borrow-checking, signature initialization and the two initial-state relations; its proof additionally relies on PL determinism to relate any PL behavior to the exhibited LLBC behavior. Theorem 5.1 gives soundness conditional on a successful derivation and an unmarked final state, not existence of a successful join/fixed-point computation.

### Thesis numbered-result crosswalk

Each row is a separate machine record with the same premise/conclusion responsibilities as the paper ledger, an exact thesis PDF locator, and its own mechanization qualification. This is not a claim that numbering or every displayed character is shared between editions.

| Thesis result | Exact PDF / printed page | Corresponding 2024 result |
|---|---|---|
| Theorem 1 | PDF 199 / printed 187 | 2.2 |
| Theorem 2 | PDF 209 / printed 197 | 3.1 |
| Theorem 3 | PDF 209 / printed 197 | 3.2 |
| Theorem 4 | PDF 210 / printed 198 | 3.3 |
| Theorem 5 | PDF 210 / printed 198 | Additional composed theorem; missing initial relation as printed |
| Theorem 6 | PDF 213 / printed 201 | 3.4 |
| Theorem 7 | PDF 214 / printed 202 | 4.1 |
| Theorem 8 | PDF 224 / printed 212 | 4.2 |
| Theorem 9 | PDF 230 / printed 218 | 5.1 |
| Lemma 1 | PDF 352 / printed 340 | A.1 |
| Lemma 2 | PDF 353 / printed 341 | A.2 |
| Lemma 3 | PDF 354 / printed 342 | A.3 |
| Lemma 4 | PDF 355 / printed 343 | A.4 |
| Lemma 5 | PDF 355 / printed 343 | A.5 |
| Lemma 6 | PDF 356 / printed 344 | A.6 |
| Lemma 7 | PDF 359 / printed 347 | A.7 |
| Lemma 8 | PDF 360 / printed 348 | A.8 |
| Theorem 10 | PDF 372 / printed 360 | B.2 |
| Lemma 9 | PDF 373 / printed 361 | B.3 |
| Lemma 10 | PDF 373 / printed 361 | B.4 |
| Lemma 11 | PDF 373 / printed 361 | B.5 |
| Lemma 12 | PDF 375 / printed 363 | B.6 |
| Lemma 13 | PDF 375 / printed 363 | B.7 |
| Lemma 14 | PDF 379 / printed 367 | C.1 |
| Lemma 15 | PDF 382 / printed 370 | C.2 |
| Lemma 16 | PDF 383 / printed 371 | C.3 |
| Theorem 11 | PDF 388 / printed 376 | C.4 |
| Lemma 17 | PDF 389 / printed 377 | D.1 |
| Lemma 18 | PDF 390 / printed 378 | D.2 |
| Lemma 19 | PDF 391 / printed 379 | D.3 |
| Lemma 20 | PDF 393 / printed 381 | D.4 |
| Lemma 21 | PDF 393 / printed 381 | D.5 |
| Lemma 22 | PDF 397 / printed 385 | D.6 |
| Lemma 23 | PDF 398 / printed 386 | D.7 |
| Lemma 24 | PDF 400 / printed 388 | E.1 |
| Lemma 25 | PDF 401 / printed 389 | E.2 |
| Lemma 26 | PDF 402 / printed 390 | E.3 |
| Lemma 27 | PDF 402 / printed 390 | E.4 |

Thesis Theorem 5 (PDF page 210, printed page 198) explicitly states the composed LLBC-to-HLPL result. The displayed formula omits Omega_l<=Omega_r, although the surrounding composition argument needs an initial relation. The page was rendered and visually inspected to distinguish this from a PDF extraction artifact. The inventory records the literal statement and separately describes the expected premise-bearing reading; it does not certify the unqualified printed formula. Paper Section 3.2 describes the composed result in prose rather than adding another numbered theorem.

Chapter 13 gives functional synthesis rules, but the thesis explicitly describes that translation as trusted. The conclusion (PDF page 291, printed page 279) describes the borrow-checker proof as pen-and-paper, mechanization as ongoing, and translation correctness as remaining work. Thus numbered semantic proofs and a formal translation definition are different evidence roles.

### Literal-source anomalies and interpretation boundaries

The exact locators/formulas are retained to permit correction without rediscovering the publication. These are defects or ambiguities of the displayed statements, not counterexamples to every intended semantic argument:

- Thesis Theorem 5 lacks its initial relation, as above.
- Paper Lemma A.2 has a dangling implication inside the immutable-read display.
- Paper Lemma B.5 uses a PL final-state symbol not bound by the displayed existential list, and its PL rvalue display omits a final-state component.
- Paper Lemma B.7's display uses inconsistent PL/HLPL state labels and an arbitrary final-state variable. Its proof text instead analyzes an HLPL reorganization. The corresponding thesis Lemma 13 has the same displayed label problem.
- Paper Lemma C.3 quantifies HLPL+ states despite its LLBC+ title/context. Theorem C.4 quantifies v_r but uses r, and changes the evaluation-arrow glyph in its conclusion.
- Paper Lemma D.5's prose calls both initial states LLBC# states; its successful branch is unindexed although its divergence/panic branches carry n.

No missing condition has been silently inserted into mathematical_source. A caller requiring a literal well-scoped theorem must resolve the relevant publication erratum or supply its own explicitly corrected statement and proof. This supplement does not turn an editorial repair into a checked result.

### Current mechanization is related source, not one-to-one publication certification

The inspected source contains Qed-ending analogues for several rvalue, assignment/store, reorganization and statement simulations, and an LLBC_sharp-to-LLBC_plus simulation. Signatures and endings are preserved per mapped record. The current HLPL+ statement analogue requires well_formed and uses a step index; this differs from merely copying the unindexed publication statement. The current shared grammar omits calls, return, traits and destructors, so it cannot directly instantiate all function-environment and initialization premises of paper Theorems 4.1/4.2.

In PL.v, HLPL_PL_Read, Rvalue_Preserves_PL_HLPL_Rel and Reorg_Preserves_PL_HLPL_Rel have completed source scripts. Assign_Preserves_PL_HLPL_Rel ends with Abort, so that attempt is not a proved declaration. Other current files contain explicit admissions; in particular the HLPL+ rvalue/statement proofs use operand infrastructure with admitted obligations. A Qed ending is therefore neither an axiom-free claim nor proof that the file currently compiles. No compiled dependency closure was measured.

For entries without an established exact correspondence, the status is explicitly “no exact mapping established,” rather than “unmechanized.” This investigation did not prove absence of any related theorem in all revisions. Nor did it identify the current tree as the immutable artifact accompanying the paper. The current artifact's narrower syntax and source markers qualify this inspected development, not the truth of every published mathematical argument.

### 2022 application contracts and absence of a compiler metatheorem

No numbered semantic theorem/lemma block occurs in the complete 2022 edition. Its operational/symbolic/translation rules are definitions. Its four displayed named proof/assumption contracts are:

| Identifier | Premises and result role |
|---|---|
| hash_map_insert_fwd_lem | Any value type, invariant-valid table, key and value. Failure implies a previously absent key and saturated count; success preserves the invariant, changes the requested binding, preserves other keys and updates size according to key freshness. F* application proof over a trusted translation. |
| serialize_lem | Assumed external-state contract: failure unconstrained; success stores the projected table. |
| deserialize_lem | Assumed external-state contract: successful load returns the projected table and preserves that projection. |
| insert_on_disk_fwd | Derived application contract under the two external assumptions; failure unconstrained. Its printed code uses the post-state for both state_v occurrences; inventory preserves that detail rather than replacing it with a stronger intended disk theorem. |

These application properties do not establish a metatheorem for the OCaml translator. The publication's static-ownership scope excludes unsafe code and interior mutability. It treats the generated translation as trusted and leaves semantic/translation soundness as further work. Exact displayed F* signatures and section anchors are in publication-application-inventory.json; no old F* artifact was replayed.

### Charon tool-paper disposition

The complete [Charon paper, arXiv:2410.18042v2](https://arxiv.org/html/2410.18042v2), contains no formal theorem blocks and no named or numbered theorem, lemma, corollary or proposition declarations. Its introduction describes the intended semantic preservation of MIR/ULLBC and ULLBC/LLBC; it does not supply a quantified preservation statement or proof. Section 4.3 points to the separately inventoried Aeneas paper. The client case studies and taint-analysis validation are empirical evidence; they do not establish a mechanized frontend correctness theorem. This is a publication-level disposition, not a claim that no related result exists outside the inspected edition.

### Additional thesis backend/model results

The following named statements supplement the 38 numbered semantic results. Exact source locators and normalized code transcriptions are retained. Ellipses, omitted bodies and illustrative inconsistencies are not counted as successful fresh proofs.

| Identifier | Scope, premises and conclusion |
|---|---|
| [sum_eq](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=264) | Illustrative total-correctness equation; proof omitted; historical partial-function discussion. |
| [id_unfold](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=265) | Unfolding equation for the fixed-point-defined example; not definitional equality. |
| [id_is_id (total)](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=266) | Example total correctness; proof omitted. Premise visually confirmed from PDF. |
| [id_is_id (partial)](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=266) | Alternative partial-correctness statement; same printed name, not another simultaneous declaration. |
| [fix_eq](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=268) | Generic fixed-point equation requires monotonicity/continuity via is_valid; proof uses excluded middle. Historical inductive Result, not current ITree representation. |
| [expr_is_valid_bind](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=269) | Compositional validity of bind; displayed is_valid_p differs from nearby exp_is_valid naming, and d is not explicitly listed in opening implicit binders. Preserve as illustrative source syntax. |
| [map_is_valid](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=271) | Simplified validity rule for handwritten map; higher-order recursion requires stored validity lemmas. Printed type notation is illustrative, not claimed fresh-elaborated syntax. |
| [length_append](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=272) | Automation example; List parameter omitted in display; proof elided. |
| [Scalar.bounds](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=273) | Historical scalar-model bounds lemma; proof omitted. |
| [pos_mul_pos_is_pos](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=273) | Disjunctive arithmetic rule used to demonstrate local automation; not a Rust semantic result. |
| [U32.add_spec](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=274) | Historical checked-add model contract under no-overflow bound; not ordinary Rust release wrapping arithmetic. |
| [insert_spec](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=275) | Illustrative sketch spans PDFpages275–276; displayed ord/ordInst and t/tprime differ from intended prose, so this is not cited as a checked complete theorem. |
| [inv_scalar_facts](https://www.sonho.fr/papers/thesis-manuscript.pdf#page=278) | Only first conjunct printed; full theorem cannot be reconstructed from publication. Example of exposing selected invariant facts. |

The historical backend section uses an inductive Result with ok/fail/div. Its fix_eq and validity lemmas must not be imported as representation facts for the current ITree-based Result. They are backend metatheory for the particular historical encoding, not source-to-target simulation theorems. The printed insert_spec is explicitly illustrative and uses t rather than the returned tprime in its final isSet expression; the prose describes the intended returned-tree property. inv_scalar_facts prints only its first conjunct, so a complete signature is unavailable from this publication.

### 2026 SymCrypt: displayed application/model contracts

The complete v1 has no numbered theorem/lemma metatheorem blocks. Its named displayed contracts are these four theorem statements, two contract axioms and one feature-model predicate axiom:

| Identifier | Status/role | Premises and conclusion |
|---|---|---|
| [reduce.spec](https://arxiv.org/html/2609.15648v1#S5.SS2.p2.1) | application theorem; displayed proof | Range premise and reduction model ⇒ Normal output equals x.val modulo Q.val |
| [featurePresent](https://arxiv.org/html/2609.15648v1#S6.p5.2) | axiom/model predicate, not a correctness theorem | None; uninterpreted feature predicate ⇒ Boolean feature availability |
| [cpu_features_present.spec](https://arxiv.org/html/2609.15648v1#S6.p5.2) | axiomatized contract | Assumed external feature-detection contract ⇒ Returned Boolean agrees with featurePresent feat |
| [ct_equal_u16.spec](https://arxiv.org/html/2609.15648v1#S7.SS4.p3.4) | application theorem; body omitted | Length equality ⇒ Returned byte is 0xFF exactly when slices equal; otherwise 0 |
| [set1_epi16.spec](https://arxiv.org/html/2609.15648v1#A2.p1.4) | model theorem; proof ellipsis | AVX2 featurePresent=true ⇒ Every output lane equals a |
| [mm_aesenc_si128.spec](https://arxiv.org/html/2609.15648v1#A2.p2.2) | axiomatized intrinsic contract | Assumed intrinsic semantics ⇒ Output bytes equal Spec.AES.round of input/key bytes |
| [mlkem.decapsulate.spec](https://arxiv.org/html/2609.15648v1#A3.p3.1) | application API theorem; body omitted | wfDecapKey key params ⇒ Success matches MLKEM.Decaps; InvalidArgument implies bad length; MemoryAllocationFailure implies out_of_memory; other error cases impossible |

The displayed `#decompose compute compute_eq` command separately names the generated equality theorem **[compute_eq](https://arxiv.org/html/2609.15648v1#S5.SS3.p4)**. The paper says it equates the main function body before and after folding repeated reduction code, and uses `rw [compute_eq]` in the simplified proof. This is an illustrative program-specific target equality, separate from the seven explicit theorem/axiom declarations above. Its full signature and formal premises are unavailable because the `compute` example is ellipsized; the inventory records that limit and the paper-reported proof generation without claiming fresh replay.

The declarations labeled axiom remain assumptions. A displayed theorem with an omitted body is a publication claim, not proof replay in this investigation. Application-model correctness retains the paper's compiler/translator, external-model, specification, platform and proof-checker assumptions; it does not establish leakage resistance or a translation-soundness metatheorem. Aggregate counts of thousands of application theorems do not supply their individual identifiers in the paper; this inventory makes no claim to enumerate that separate repository development.

### 2026 pipeline report: identify Hax results and remaining goals

The complete paper has no numbered source-semantics metatheorem block. Its detailed running example is Hax RustM code. Four theorem code listings show the bind inversion, two conditional bounds and target-distance result. The paper also names the maximum-bound theorem and unfinished application goals. To avoid leaving their exact types as an unspecified future query, the cited PR head at 4fab6ff08a8e515321675ca121f9ad36c38268ab was read; signatures and source statuses of all nine named declarations in its FoldingCorrectness.lean are recorded:

| Referenced source theorem | Source status at the cited head |
|---|---|
| [compute_log_arity_gives_folding_degree](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L50) | completed source script/term; not replayed |
| [RustM_ok_ite_decide_lt_le_left](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L68) | completed source script/term; not replayed |
| [arity_respects_target_distance](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L83) | completed source script/term; not replayed |
| [RustM_bind_eq_ok](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L121) | completed source script/term; not replayed |
| [RustM_ok_ite_decide_lt_le_right](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L136) | completed source script/term; not replayed |
| [arity_respects_max_bound](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L151) | completed source script/term; not replayed |
| [arity_respects_next_input](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L197) | sorry in inspected source |
| [folding_respects_final_height](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L215) | sorry in inspected source |
| [round_consistency_preserved](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline/blob/4fab6ff08a8e515321675ca121f9ad36c38268ab/lean/P3FriProofs/Proofs/FoldingCorrectness.lean#L233) | sorry in inspected source |

The maximum-bound theorem retains an explicit current-height > final-height premise in that source even though its proof does not need the arithmetic of the preliminary subtraction. The target-distance theorem is limited to the None next-input case and requires that strict height inequality. The three unfinished named theorems respectively concern Some-case next-input distance, preservation of the final target height and a two-round sum bound; their complete premises are in their acquired signatures.

The paper says four goals remain sorry. The inspected cited head has three named sorry theorem declarations plus an unnamed concrete sorry example; its sixth named application declaration, compute_log_arity_gives_folding_degree, is already a trivial existential witness over Nat. Therefore “all six FRI correctness theorems proved” would be unsupported. The artifact observation is attached to that immutable head, not a claim about current default branch state.

The separate Aeneas fold_step/ArkLib result is stated in prose: bounded prime/inputs, 13 checked u64 operations, no overflow and equality to the arity-two fold evaluation. The paper does not provide an exact theorem identifier/signature for that claim. This is a genuine publication-detail limit, not a nonexistent result or an invitation to substitute a theorem from an unrelated revision. The inventory does not treat that Aeneas application claim or the Hax examples as a proof of either translator.

## Boundaries

- The exhaustive enumeration claim is limited to numbered declarations in the specified publication sections and the displayed/named auxiliary/application declarations identified above. It does not cover every imported library lemma or every theorem in an application artifact.
- A source declaration ending in sorry, Admitted or Abort has a different status from a completed source proof script. None was compiled or checked for transitive assumptions here.
- Exact printed formula defects are preserved. Concise conclusion summaries explain the proof's intended role where necessary; they are not certified replacements for defective syntax.
- A complete statement is unavailable when the publication prints an ellipsis or only a prose result without a theorem identifier. Such cases are marked explicitly, including inv_scalar_facts and the pipeline fold_step claim.
- No result here establishes a mechanically checked rustc/Charon-to-current-Lean preservation theorem, correctness of current backend model registration or a theorem for general unsafe/concurrent Rust.

## Evidence

Evidence acquired on 2026-10-15. [publication-source-identities.json](publication-source-identities.json) records exact edition URLs, PDF/HTML hashes, page counts, scan criteria and current-source coordinates. The complete PDF/HTML extraction remains only in the investigation's reading cache and is **not** part of this report package. The package preserves mathematical expression data, concise summaries, identifiers, exact locators and small source signatures, not copied publication proof prose.

The 2024 HTML formal blocks were enumerated structurally and cross-checked against PDF headings. Thesis declarations were enumerated independently from the relevant PDF ranges; counts cover Theorems 1–11 and Lemmas 1–27 without gaps. All 37 paper result IDs have individual premise/conclusion/domain records; each of the 38 thesis results has its own locator and crosswalk. The application scan separately distinguishes theorem, axiom, illustrative statement and unfinished goal.

## Revalidation

Re-run the structural heading enumeration against the exact edition/hash, then compare identifiers and statement locations before changing counts. For each changed theorem, preserve its quantified domain and all initialization, relation, frame, projection and failure/divergence premises. Do not normalize a typo into a proof claim without recording both versions.

For mechanization, an exact artifact identity and a checked assumption closure are needed in addition to matching names. A later source build and Print Assumptions could strengthen the source-only observations, but this report performs neither. For application claims, use exact theorem signatures and distinguish assumptions, elided sketches, sorry goals and completed proof artifacts before treating aggregate paper descriptions as full correctness coverage.
