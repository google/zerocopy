# Binding human-read statements to kernel declarations at library scale: Pollack-consistent printing, proof audits, rendered-code and blueprint links, a print/re-elaborate/compare measurement over Lean 4 core, and benchmark misformalization corrections

## Summary

- **Two different properties are routinely conflated.** *Pollack-consistency* (Wiedijk 2012) is a property of a prover's printer/parser pair: printed terms must parse back to the term printed (`parse(print t) = t`, "well-behaved"), and no two distinct well-typed terms may print identically in a way that lets a reader derive a contradiction. *Statement adequacy* is whether a correctly printed formal statement says what its author or the informal source meant. A print/re-elaborate/compare pass checks only the first; every documented benchmark correction examined here (wrong hypotheses, wrong library notion, missing quantifier, off-by-one, optional-parameter binders read as definitions) is a failure of the second and would survive such a check unchanged.
- **Measured on a real library** (Lean 4 v4.35.0, all 46,041 non-generated theorems of the shipped `Init` and `Std` modules, Lean's default heartbeat budget): with default `pp.*` options, 77.80% of statements re-elaborate to the identical kernel type, 2.78% to a definitionally equal one, **0.89% (412) silently re-elaborate to a different closed, well-typed statement**, and 18.52% do not re-elaborate (unassigned metavariables 12.58%, elaboration errors 4.30%, parse errors 1.63%). In 150 of the 412 the re-elaborated term prints to the *same string*: these are concrete Pollack-axiom candidates in Wiedijk's sense. The cost is 4.90 ms per declaration mean (3.02 ms median, 48.7 ms p99), about 226 s of single-thread time for the whole library at 2.26 GB peak RSS. `Basis: execution`.
- **What the silent mismatches are.** Numeric literals whose type the text does not fix (`0 ≤ 1` over `Int` re-reads over `Nat`), coercion arrows whose target the text does not fix (`Fin.ext_iff`'s `a = b ↔ ↑a = ↑b` re-reads as the tautology `a = b ↔ a = b`), hidden instance arguments, generalized field notation on a head whose type is not printed, and omitted binder types. Enabling `pp.numericTypes` and `pp.coercions.types` removes 246 of the 412 at +1.6% printed length; `pp.explicit` removes all 412 at 2.88× length; `pp.all` removes all of them and makes 99.85% of statements round-trip exactly, at 3.90× length. `Basis: execution`.
- **Tools bind rendered text to different objects, and none of the Lean tools examined checks rendering fidelity by default.** doc-gen4 renders the *kernel type* through the delaborator and keeps only constant-link tags. Mathlib's `ppRoundtrip` linter compares *source syntax* with the *reformatted source syntax*: it never consults the elaborated declaration, and it is off by default. leanblueprint's `\lean{…}` plus `checkdecls` checks only that a declaration *name exists*. PutnamBench's docstring check compares informal text with a docstring *string*. The Liquid Tensor Experiment's `examples/` are abductive "specs" that exercise definitions. HOL Zero instead classifies printer flaws that can make a theorem look unsound as bounty-eligible soundness bugs: 6 of the 7 entries on its unsoundness list are printer flaws. `Basis: source + documentation`.
- **How benchmark misformalizations are found.** In PutnamBench's history of commits touching `lean4/src`, 102 of the 219 non-merge commits are statement fixes (message heuristic). They name 97 distinct problems and were written by 14 authors over 2024-07 to 2026-09; 37 of the fix messages state that the old statement was *disprovable*. One commit removed default-valued binders from 212 Lean files. miniF2F records statement fixes across Lean, Isabelle, Metamath and HOL Light in three repositories, including corrections credited to prover-based analysis. Lean Workbook reports 93.5% sampled accuracy after compile, back-translation and NLI filtering. `Basis: source (repository history) + documentation`.

## Applicability

- **Round-trip measurement.** Applies to the Lean 4 toolchain `v4.35.0` (`leanprover/lean4` at the pinned commit; `lean --version` reports that commit) and to the theorems of its bundled `Init.*` and `Std.*` modules. It does **not** cover Mathlib or any other downstream library: Mathlib was not built or downloaded. The probe ran the delaborator and elaborator in the root namespace with nothing opened, at the per-declaration heartbeat budget equal to Lean's default `maxHeartbeats` (200000). Results for other namespaces/`open` contexts, other options, or other library versions are not established. A rerun at 1/1000 of the default budget turned 1.87% of declarations into timeouts and changed the silent-mismatch count only from 412 to 405. Budget therefore matters for the failure classes and much less for the silent class.
- **Tool binding analysis.** Applies to the pinned revisions of `mathlib4` (`PPRoundtrip.lean`), `doc-gen4`, `leanblueprint`, `checkdecls`, `lean-liquid`, `mirror-isabelle` (PIDE files only) and `PutnamBench` (`lean4/check_docstrings.lean`). It rests on source reading. None of these tools was executed except where stated, and doc-gen4's HTML output was not generated.
- **Benchmark corrections.** Apply to the commit histories reachable from the pinned revisions of `PutnamBench`, `openai/miniF2F`, `facebookresearch/miniF2F` and `yangky11/miniF2F-lean4`, and to the cited papers. Counts are message-text heuristics over commit metadata and are not semantic diff reviews. Individual examples were checked against their diffs.
- **HOL Zero and audits.** HOL Zero claims come from the project's own pages (version 0.6.3) and the abstract of Adams's ITP 2016 paper. The HOL Zero source tarball and the full texts of Adams 2010/2016 were not examined; see Boundaries. Flyspeck facts come from the arXiv version of Hales et al.
- **Relationship among subjects.** The Lean toolchain is the measured system. Mathlib's linter, doc-gen4, leanblueprint/checkdecls, PutnamBench's checker, LTE and Isabelle PIDE are compared as alternative binding mechanisms. The benchmark repositories are sources of field evidence about misformalization. HOL Zero, Wiedijk and Adams supply the design criteria.

## Findings

### 1. Vocabulary: what "printing cannot mislead" means

`Basis: documentation (Wiedijk, ENTCS 285, 2012, Defs. 1.1–1.6, §8.1)`

| Notion | Definition (Wiedijk) | Lean-probe analogue used below |
| :-- | :-- | :-- |
| compatible | `parse(print t)` defined for all `t` | not `parse_fail` / `elab_fail` / `elab_mvars` |
| well-behaved | `∀t. parse(print t) = t` | `exact` (or `defeq_*` if definitional equality is accepted) |
| input-complete | every term has some input string | not measured |
| Pollack-axiom | `t1 = t2` well-typed with `print t1 = print t2` | `MISMATCH` whose re-elaborated term prints identically (150 cases) |
| (weakly/strongly) Pollack-inconsistent | contradiction derivable from finitely many Pollack-axioms (with/without extra definitions) | not tested (no attempt to derive `False`) |
| Pollack-super-inconsistent | a provable `φ` with `print φ = print ⊥` | not tested |

Wiedijk's concrete failures: HOL Light prints both `?!x:1. T` (true) and `?!x:bool. T` (false) as `?!x. T`. HOL Light accepts variables named `0` and `1`, so it proves something that prints as `0 = 1`. Isabelle omits quantifier types the same way. Coq allows a weak super-inconsistency through a user-declared coercion. The Mizar HTML printer drops `qua`. Metamath is trivially consistent because parse and print are the identity. His remedy is a *failsafe* printer `print'(t) = let s = print t in if parse'(s) = t then s else print_failsafe(t)`. It is Pollack-consistent by construction, and he argues that printing is not a bottleneck. Section 5 measures exactly the `parse'(print t) = t` test that this remedy needs on every print.

### 2. HOL Zero: printer flaws treated as soundness flaws

`Basis: documentation (HOL Zero home and unsoundness pages; ITP 2016 abstract)`

- **Stated design.** HOL Zero is a basic HOL prover "designed with trustworthiness as its top priority". It is intended for checking or consolidating proofs from other provers rather than developing proofs. The ITP 2016 paper adapts Hindley–Milner inference to *variable–variable overloading* and computes *minimal type annotations* so that printing is unambiguous, with the goal of "well-behaved parsing/printing and Pollack-consistency" (abstract).
- **Bounty record since 0.3.0 (2010-09-14).** The list covers logical unsoundnesses and "printer unsoundnesses that can be exploited to make it appear that there is a logical unsoundness". It has 7 entries. One is logical: OCaml `Obj.magic` could convert a sequent into a theorem. Six are printer flaws: look-alike UTF-8 characters; OCaml string mutability used to change a fixity or enumeration brackets silently (2 entries); missing parentheses around `let` subexpressions; `|-` not reserved as a token; and preterm destructors mishandling variables overloaded with the top-level constant. Each was fixed in the next point release. Two $100 awards are recorded, for the UTF-8 entry and the `Obj.magic` entry.
- **Design consequence.** For a checker whose role is to let a human trust a statement, the printer is inside the trusted path. Classifying printer flaws as soundness bugs puts them under the same review process as kernel bugs.

### 3. Independent checking of a very large formalization (Flyspeck)

`Basis: documentation (Hales et al., arXiv:1501.02155, §§1–2, 4.3, 4.5)`

- The Kepler-conjecture main statement was verified in HOL Light (and Isabelle for the tame-graph enumeration), "with a second verification of the main statement in HOL Zero". Recorded proof objects were exported, then imported and replayed in a bare HOL Light core and in HOL Zero. A weaker form of the main statement was used for the replay, with the graph archive as a universally quantified variable: `|- !a. tame_classification a /\ good_linear_programming_results a /\ the_nonlinear_inequalities ==> the_kepler_conjecture`.
- **Reported costs:** about 5 h on a 2 GHz CPU to verify the main statement from proof scripts, and about 40 min to replay the recorded proof. The nonlinear-inequality subclaim takes about 5000 CPU hours.
- "Hundreds of small errors in the proof of the Kepler conjecture were corrected during formalization." These are errors in the *informal* proof found by formalizing, not printer errors.
- Adams's JFR 2016 abstract argues that "formalisation itself can be subject to error" and proposes an "effective and efficient auditing process" illustrated on Flyspeck. The audit procedure, findings and effort figures are in the full paper, which was **not examined**. No audit-effort number is therefore reported here.

### 4. What each binding mechanism binds and checks

`Basis: source (pinned revisions) unless marked`

| Mechanism | Rendered/human text is bound to | Check performed | Mismatch classes it can see | Classes it cannot see |
| :-- | :-- | :-- | :-- | :-- |
| doc-gen4 signatures (`Process/NameInfo.lean` `Info.ofTypedName`) | kernel type of the constant, delaborated with `delabForallParamsWithSignature`, with `currNamespace := n.getPrefix` and options `pp.tagAppFns`, `pp.funBinderTypes` (`Load.lean`) | none. `RenderedCode.renderTagged` keeps `.const n` tags (links), sort tags, keyword/string tags and an information-free `otherExpr` tag, and drops all other `SubexprInfo` (types, elaboration state) | none automatically. A reader can follow constant links | everything the delaborator hides (Section 5 classes). Coercion and instance applications are not constants, so they are not linked |
| Mathlib `ppRoundtrip` linter | the command's *source syntax* | `polishSource(source) ≠ polishPP(ppCategory command stx)` after whitespace normalization. Registered with `defValue := false` | layout and notation differences between written syntax and the formatter's re-rendering of that *same syntax tree* | anything semantic. The linter runs after elaboration but compares only syntax trees and strings; the elaborated declaration is never consulted |
| leanblueprint `\lean{decls}` + `\leanok` + `checkdecls` | a list of declaration *names* | `env.contains line.toName` for each name in `blueprint/lean_decls` | missing/renamed declarations | whether the declaration's statement matches the informal statement it is attached to |
| PutnamBench `lean4/check_docstrings.lean` | docstring of `putnam_YYYY_xN` | trimmed docstring `=` escaped informal statement in `informal/putnam.json` | drift between two copies of the *informal* text | formal–informal disagreement |
| LTE `src/challenge.lean` + `src/examples/` | the headline theorem, isolated with its notations (`challenge_notations.lean`) | a human reads `examples/` (`real.lean`, `pBanach.lean`, `Ext.lean`, …), which are compiled `example`s showing, e.g., `ℝ≥0 = {r : ℝ // r ≥ 0}` and the `‖λv‖ = |λ|^p‖v‖` rule for a chosen p-norm | definitions that do not behave like the textbook objects, to the extent the examples probe them | properties no example exercises. Commelin–Topaz call this *abductive* evidence, not proof |
| Isabelle PIDE (`markup.ML` `entity`/`def`/`ref`/`typing`; `rendering.scala` hyperlinks/tooltips) | text ranges of source or prover output, annotated with entity kind, name and definition position | none. Markup supports navigation and tooltips | a reader can inspect the entity behind each token and its type | anything the reader does not hover over. No automatic comparison |

The pattern across the table is that every mechanism binds *names* or *text*, not elaborated statements. Elaborated statements are bound to readable text only by the delaborator, and only Section 5's style of check tests that binding.

### 5. Measurement: print → parse → elaborate → compare over Lean 4 core

`Basis: execution (real system: Lean 4 v4.35.0 binary and its bundled Init/Std .olean files)`

**Procedure** (probe `support/roundtrip/RoundTrip.lean`; one `lean --run` process per option variant). The probe imports `Std` and selects every `thmInfo` constant whose module begins with `Init` or `Std`. It excludes internal-detail and private names, auxiliary recursors, `noConfusion`, and names ending in `eq_def`, `eq_<n>`, `sizeOf_spec`, `injEq` or `inj`, leaving **46,041** theorems. For each theorem `n : T` it then:

```text
s  := (ppExpr T with options O).pretty 100
stx := runParserCategory env `term s                       -- parse_fail
T' := withLevelNames n.levelParams (elabType stx; synthesizeSyntheticMVarsNoPostponing; instantiateMVars)
      with errToSorry := false                              -- elab_fail / elab_mvars
status := exact      if stripMData T' == stripMData T       (alpha-equivalence; binder info ignored)
        | defeq_red  if isDefEq T' T at reducible transparency
        | defeq_def  if isDefEq T' T at default transparency
        | MISMATCH   otherwise (T' closed, well-typed, not defeq)
```

Each declaration runs under `withCurrHeartbeats` with `maxHeartbeats = 200000` (Lean's default) and in the root namespace with nothing open. Host: x86_64 Linux, 96 vCPUs, 236 GiB RAM. Up to four probe processes ran concurrently, so per-variant timing differences under about 15% are noise.

**Default options:**

| status | count | share |
| :-- | --: | --: |
| exact | 35,822 | 77.80% |
| defeq at reducible | 1,100 | 2.39% |
| defeq at default only | 181 | 0.39% |
| **MISMATCH (different closed well-typed statement)** | **412** | **0.89%** |
| unassigned metavariables after elaboration | 5,793 | 12.58% |
| elaboration error | 1,981 | 4.30% |
| parse error | 752 | 1.63% |

**Silent mismatches, classified by the smallest option set that removes them** (`support/roundtrip/compare_variants.py`):

| class | count | representative (default print → what the print re-elaborates to) |
| :-- | --: | :-- |
| numeric literal type not determined by text | 110 | `Int.one_nonneg`: `0 ≤ 1` (over `Int`) → `0 ≤ 1` over `Nat`; `Lean.Grind.Field.zero_ne_one`: `0 ≠ 1` (over `α`) → over `Nat` |
| coercion target not determined by text | 92 | `Fin.ext_iff`: `a = b ↔ ↑a = ↑b` (`↑` = `Fin.val`) → `a = b ↔ a = b` |
| either of the two options suffices | 44 | `Fin.val_add_one` family |
| needs `pp.explicit` | 153 | `ISize.toInt16_ofNat`: `(OfNat.ofNat n).toInt16` resolves to `Nat.toInt16`; `ite_eq_ite` with `{h h' : Decidable p}`: two `if`s using different instances print identically; `Int.NonNeg.elim`: `∃ n, a = ↑n` with `n : Nat` re-reads with `n : Int` |
| needs `pp.all` | 13 | `Array.mapFinIdx_*`, `Array.mapIdx_*` |

`Fin.ext_iff` is the instructive case. The kernel statement is the extensionality lemma `a = b ↔ a.val = b.val`. Its default rendering, if copied and re-checked, states a tautology. The coercion delaborator's own docstring (`Builtins.lean`, `coeDelaborator`) says that when re-parsing `↑n` "we can (usually) recover the specific coercion being used". The 92 + 44 coercion cases measure the exceptions to "usually" in this library.

**The non-silent failures** are compatibility failures in Wiedijk's sense: the printed text is not accepted back. The dominant sources are `⋯` for omitted proofs (`pp.proofs` is false by default), which elaborates to metavariables; anonymous instance binders that leave typeclass problems stuck; and notations the printer emits that the parser in the same context rejects. For example, 416 of 634 `Std.Do` theorems fail to parse, with Hoare-triple brackets `⦃P⦄ x ⦃Q⦄`, and `BitVec`'s `n#'hn` fails too. Turning on `pp.proofs` cuts unassigned-metavariable results from 5,793 to 1,913 and leaves the silent count essentially unchanged (414, two of them new).

**Option trade-off** (same 46,041 theorems; length is the printed string length in characters):

| options | exact | exact or defeq | silent MISMATCH | mvars | elab err | parse err | mean length (× default) | mean ms/decl | default MISMATCH resolved |
| :-- | --: | --: | --: | --: | --: | --: | --: | --: | --: |
| default | 77.80% | 80.59% | 412 | 5,793 | 1,981 | 752 | 175.8 (1.00) | 4.90 | – |
| doc-gen4's option set (`pp.tagAppFns` + `pp.funBinderTypes`) | 79.24% | 81.82% | 372 | 5,700 | 1,549 | 750 | 178.9 (1.02) | 5.37 | 39 |
| `pp.numericTypes` | 78.30% | 81.04% | 223 | 5,782 | 1,973 | 752 | 178.3 (1.01) | 5.28 | 154 |
| `pp.coercions false` | 64.43% | 80.64% | 262 | 5,815 | 2,084 | 752 | 179.4 (1.02) | 5.62 | 38 |
| `pp.coercions.types` | 78.26% | 81.05% | 244 | 5,643 | 2,086 | 752 | 176.1 (1.00) | 5.33 | 136 |
| `pp.numericTypes` + `pp.coercions.types` | 78.65% | 81.38% | **115** | 5,608 | 2,098 | 752 | 178.6 (1.02) | 5.35 | 246 |
| `pp.proofs` | 84.89% | 88.93% | 414 | 1,913 | 2,016 | 755 | 182.5 (1.04) | 5.81 | 0 |
| `pp.explicit` | 69.12% | 88.15% | **0** | 5,435 | 20 | 2 | 505.5 (2.88) | 4.57 | 394 (18 become mvars) |
| `pp.all` | **99.85%** | 99.98% | **0** | 0 | 2 | 5 | 686.2 (3.90) | 4.23 | 412 |

The doc-gen4 row applies doc-gen4's option set to `ppExpr` of the whole type. doc-gen4 itself prints binders and conclusion separately through `delabForallParamsWithSignature`, so this row approximates its text and does not reproduce it. With those options, 372 statements still re-read silently as different statements (`Basis: execution` for the row; `derived` for its relevance to doc-gen4 pages).

A trap appears when options are combined. `pp.coercions false` together with `pp.numericTypes` prints literals as raw `OfNat.ofNat (nat_lit 1)` *without* the type. The reason is that `delabOfNat` runs only `whenPPOption getPPCoercions` (`Builtins.lean` lines 1166–1169 at the pinned toolchain), so turning coercions off also disables the literal delaborator that honors `pp.numericTypes`. The combined "explicit-looking" variant (`pp.proofs`, `pp.numericTypes`, `pp.coercions false`, `pp.funBinderTypes`, `pp.letVarTypes`) still had 234 silent mismatches. `Basis: source + execution`.

**Cost of Wiedijk's failsafe printer on this library** (`Basis: derived` from the default and `pp.all` rows). A check on every print costs the default round trip, 4.90 ms mean. Falling back to `pp.all` for the 19.41% of statements that are not exact-or-defeq adds about 0.194 × 4.23 ≈ 0.82 ms on average, for ≈ 5.7 ms per printed statement. The fallback's own residue is 7 statements, 2 elaboration errors and 5 parse errors under `pp.all`. On those the failsafe guarantee itself fails, so a production printer would need a still more explicit form. Re-checking all 46,041 statements costs ≈ 226 s of single-thread CPU time, which parallelizes per declaration.

### 6. How benchmark misformalizations were discovered and corrected

`Basis: documentation (papers) + source (commit histories at pinned revisions)`

**Reviewer procedures and effort reported by maintainers:**

| benchmark | size | review procedure | effort reported |
| :-- | :-- | :-- | :-- |
| miniF2F (ICLR 2022) | v1: 244 test + 244 valid statements, Lean/Metamath/Isabelle (HOL Light added later) | manual formalization; "reviewing a formalized statement" is a separate step; versions frozen, "only allowing fixes in case errors are later discovered" | formalizing ≈ 15 min average; reviewing ≈ half of that |
| PutnamBench (arXiv v2) | 1,692 formalizations of 640 problems (Lean 4 640, Isabelle 640, Coq 412); README at the pinned revision: 1,724 (Lean 672) | team of two doctoral and five undergraduate students; "each formalization was verified by a second person at least once"; public issues invited | ≈ 25 min to formalize one problem in one language; verification about 10 min on average (the sentence is garbled in the extracted PDF text: "took between 10 minutes, on average") |
| Lean Workbook (arXiv v3) | 1,088,678 forum questions → 458,692 well-defined → 327,870 selected → 205,079 compile → 57,231 pass back-translation NLI | compile check, back-translation + NLI by an LLM, then three human experts diagnose failing patterns; accuracy measured on 5–10 samples per common tag | 2–5 min per problem; 93.5% sampled accuracy (abstract) |

No project reports inter-reviewer agreement statistics. Not one of the three papers gives a measured *false-statement rate found by review* separately from errors found later.

**PutnamBench history** (`support/benchmarks/putnambench_history.py`, output preserved). Of 219 non-merge commits touching `lean4/src` (2024-07-09 to 2026-09-21), 102 are statement fixes by message heuristic, naming 97 distinct problems. 76 have an explanatory body. 37 state the old statement was **disprovable**, 4 that it was trivially provable or vacuous, and 13 reference an issue or suggestion. The commits come from 14 authors, one of whom wrote 71. Diff-checked examples, by class:

| class | example (short commit in PutnamBench) | what changed | discovery cue in message |
| :-- | :-- | :-- | :-- |
| default-valued binder read as a definition | `6ab737ca26ed` "Fix optParam issue." (212 Lean files); `fe8a301c96e7` | `(S : Set ℕ := {n \| p n = 0})` → `(S : Set ℕ) (S_def : S = …)`. An `optParam` binder in a theorem quantifies over *every* `S`; the default constrains only call sites | reviewer |
| wrong library notion | `14b744ddcebd`, `a65cf48fb109` | `Fin 2 → ℝ` with `Euclidean.dist`/`dist` → `EuclideanSpace ℝ (Fin 2)`. On `Fin n → ℝ` Mathlib's norm is the sup norm | external suggestion |
| vacuous hypothesis | `2c2ee36ba5e4` | `(n : ℕ) (hn : n < 0)` → `(hn : 0 < n)` | – |
| inconsistent hypotheses | `1ce0f8851d4e` (1996 A4) | `hS2` at `a, b, a` simplifies to `False` | "trivially provable" |
| precedence | `9f8cf2b0d615` (2023 B3) | `i + 2 < k → P ↔ Q` parsed as `(… → P) ↔ Q`; parentheses added | "disprovable" with a witness lemma |
| off-by-one / wrong quantity | `534c83185bce` (2021 A1) | list length counted locations, not hops | "disprovable" |
| goal too strong | `c6be8d3a8f65` (2012 A4) | `n > 2` in the goal | counterexample given |
| wrong encoding of an analytic notion | `a41463651cd8` (2010 A3) | `fderiv ℝ h (1,0) x` → `fderiv ℝ h x (1,0)` plus a missing coefficient | – |
| error inherited from the informal solution | `68e16f8aa83c` (2022 A1) | typos in the published solution PDF propagated | comparison with the derivation |

**miniF2F histories.** `openai/miniF2F` has 161 non-merge commits from 2021-05 to 2022-06, 57 with fix keywords. `facebookresearch/miniF2F` has 215 from 2021-05 to 2025-01, 98 with fix keywords, many per-problem fixes applied across Lean, Metamath, Isabelle and HOL Light. `yangky11/miniF2F-lean4` has 77 from 2023-08 to 2026-02, 22 with fix keywords. Diff-checked Lean 4 examples:

- `1be24b76c89e` fixed 7 test-split statements, "based on analysis by NuminaMath (DeepSeek-Prover-V1.5) and independent verification of counterexamples". Among them, `aime_1994_p3` was missing `∀ x` in hypothesis `h0`. The commit message explains that `x` "becomes an implicit argument", so the hypothesis constrained `f` at one point. Others gained a missing positivity hypothesis or a strengthened bound.
- `1646bd5843b7` changed `n!` to `n !`. Derived explanation, not stated in the commit: in Lean 4, `!` may end an identifier, so `n!` can elaborate as a fresh, automatically bound variable rather than `Nat.factorial n`.
- `1f8e11a35044` changed `(∑ k ∈ range n, 2 * k) + 1` to `∑ k ∈ range n, (2 * k + 1)` (big-operator scope), and `∀ n ∈ S, n ∣ …` to `∀ n, n ∈ S ↔ n ∣ …` (a one-directional characterization).
- `9505034a2aef` renamed a duplicated hypothesis name `h₀` (shadowing).

**Lean Workbook error patterns** (paper §5.2). Integer division written without a type annotation elaborates to floor division over `ℕ`/`ℤ`. Even after human-labelled examples were added, the model emitted the `: ℝ` fix only "about half the times". In minimum/maximum problems the formalization states one inequality but omits attainment.

### 7. Coverage matrix: misformalization class × detection mechanism

`Basis: derived` from Sections 4–6. ✓ = detects by construction; ~ = may detect; ✗ = cannot detect.

| class | print/re-elab/compare | `ppRoundtrip` | name-existence check | docstring sync | example files / abductive specs | proof attempt (disprovable / too easy) | human statement review |
| :-- | :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| hidden literal type / coercion / instance in rendering | ✓ | ✗ | ✗ | ✗ | ~ | ~ | ~ (if reading rendered text) |
| default-valued binder read as definition | ✗ | ✗ | ✗ | ✗ | ~ | ~ (often trivial or false) | ✓ |
| wrong library notion (sup-norm `dist`) | ✗ | ✗ | ✗ | ✗ | ✓ if exercised | ~ | ~ (needs library knowledge) |
| vacuous / inconsistent hypotheses | ✗ | ✗ | ✗ | ✗ | ✗ | ✓ (trivial proof) | ~ |
| goal too strong / off-by-one | ✗ | ✗ | ✗ | ✗ | ✗ | ✓ (counterexample) | ~ |
| precedence or binder scope in the *source* | ✗ (round trip is faithful) | ~ (only if reformatting adds parentheses) | ✗ | ✗ | ✗ | ✓ (37 "disprovable" fixes) | ~ |
| automatically bound variable (`n!`, missing `∀`) | ✗ | ✗ | ✗ | ✗ | ✗ | ✓ | ~ |
| renamed / missing declaration | ✗ | ✗ | ✓ | ✓ | ✗ | ✗ | ✓ |
| informal text drift | ✗ | ✗ | ✗ | ✓ | ✗ | ✗ | ✓ |

The rendering classes that a Pollack check detects did not appear as the cause of any benchmark correction examined. Conversely, every benchmark correction class examined is invisible to a Pollack check. The two kinds of check are complementary, not substitutes.

### 8. Performance and resource footprint (L1–L6)

| level | quantity | value | basis |
| :-- | :-- | :-- | :-- |
| L1 authoring | formalize / review one olympiad statement (miniF2F) | ≈ 15 min / ≈ 7.5 min | documentation |
| L1 | formalize / verify one Putnam statement in one language | ≈ 25 min / ≈ 10 min | documentation |
| L1 | human diagnosis per autoformalized problem (Lean Workbook) | 2–5 min | documentation |
| L1 | audit effort for a large formalization (Adams) | not measured (full paper not examined) | – |
| L2 toolchain build | building Lean or Mathlib | not measured (prebuilt `v4.35.0` used) | – |
| L3 elaboration | round trip per theorem, default options | mean 4.90 ms; p50 3.02; p90 6.93; p99 48.74; max 291.9 | execution |
| L3 | phases (default): delab+format / parse / elaborate / compare | 1.31 / 0.29 / 3.24 / 0.06 ms mean | execution |
| L3 | import `Std` environment | 0.82–0.91 s per process | execution |
| L4 generated code | – | not applicable | – |
| L5 checking | Flyspeck main statement from scripts / recorded replay / nonlinear inequalities | ≈ 5 h / ≈ 40 min (2 GHz) / ≈ 5000 CPU h | documentation |
| L5 | full library re-check of Init+Std renderings | ≈ 226 s single-thread (sum of per-theorem times) | execution |
| L6 memory | peak RSS of one probe process | 2,257,404–2,326,244 kB across variants | execution (`VmHWM`) |
| L6 artifacts | Init + Std `.olean` bytes (1,145 modules) | 96,295,496 + 106,993,336 = 203,288,832 B | execution (`find -printf %s`) |
| L6 readability proxy | mean printed statement length default / `pp.explicit` / `pp.all` | 175.8 / 505.5 / 686.2 characters | execution |

### 9. Human comprehensibility (C1) and conceptual simplicity (C2)

- **C1.** The failures that matter to a human reader are local and silent: one `↑` or one literal whose type is not printed. Nothing in the rendered text signals that information is missing. Unlike the compatibility failures, these produce no error when the statement is copied back. Making the text Pollack-safe by brute force (`pp.all`, 3.9× longer) trades this hazard for a working-memory hazard: readers must scan universe levels and instance terms. The two-option setting (`pp.numericTypes` + `pp.coercions.types`) is the measured sweet spot here, removing 60% of silent mismatches for 1.6% more text. It leaves hidden-instance and dot-notation cases, which need `pp.explicit`-level detail. For agents the trade-off differs: length is cheap, so `pp.all` or direct kernel-term comparison is the natural interface.
- **C2.** One invariant is enforced today by six unrelated mechanisms (Section 4), none of which states it: *the text a reviewer approves denotes the kernel statement that was checked*. The minimal universal abstraction is Wiedijk's: a printer is admissible only together with a parser for which `parse ∘ print = id` on the printed domain, with a failsafe form for the remainder. HOL Zero's "minimal annotation" is a smarter printer satisfying the same law. The other mechanisms then become ordinary layers above it: names (checkdecls), informal-text sync (docstring checks) and behavioural specs (LTE examples). This does not absorb statement adequacy (Section 7), which remains a separate, irreducible human-or-prover obligation.

### 10. Validation (V1–V4)

- **V1, specification adequacy and non-vacuity.** Benchmark histories show proof attempts acting as a mutation oracle for statements. "Disprovable" (37 PutnamBench fixes) is a killed mutant of the intended statement, and "trivially provable" is a vacuity signal. LTE's examples are behavioural tests of definitions. No benchmark examined reports systematic statement mutation or vacuity checking as part of review.
- **V2, checker/lowering soundness.** The round-trip probe is a differential test of delaborator against elaborator. Its oracle is the kernel-term equality check (`==` after stripping metadata, then `isDefEq`). Both sides share the elaborator, so a bug that is symmetric in print and parse would be invisible. HOL Zero's replay of Flyspeck is an independent-checker differential.
- **V3, concurrency/crash/silicon.** Not applicable to this topic.
- **V4, human comprehension.** No study examined measures whether human reviewers misread the 412 silent cases or how often reviewers of benchmark statements detect planted errors.

## Boundaries

- **Not examined:** Mathlib (no build); any measurement of `ppRoundtrip` findings on a real library; doc-gen4 HTML output (rendering consequences are derived from source); the HOL Zero source tarball and the full texts of Adams 2010, Adams ITP 2016 and Adams JFR 2016 (the publisher PDFs were not retrievable through the available fetcher). Audit procedure details and audit effort from Adams 2016 are therefore **not reported**, and no claim is made about specific misleading renderings his audit found in Flyspeck. Also not examined: the Wenzel 2012 paper text (PIDE claims rest on source files); Lean Workbook's repository and per-tag accuracy table; miniF2F reviewer counts.
- **Unknown:** why 416 `Std.Do` and 79 `Std.Tactic` statements print with notation that the root-context parser rejects. Whether it is scoped notation leaking into the printer or a parser/printer asymmetry was not investigated. Also unknown: whether any of the 412 silent mismatches can be combined into a derivation of `False` (strong Pollack-inconsistency of Lean core). No such derivation was attempted, and the examples found are all true statements re-reading as other true statements.
- **Known not to apply:** the measured rates do not transfer to Mathlib. Mathlib uses far more coercions and numeric literals over non-`ℕ` types, so its silent rate could differ in either direction; no number is claimed. The rates also do not apply to doc-gen4's exact output, which splits signatures with a different delaborator entry point and uses `pp.funBinderTypes`.
- **Unsupported by the evidence:** that 0.89% is "the" misrendering rate of Lean; that any benchmark correction was caused by a rendering defect; that HOL Zero is Pollack-consistent (only its design goal and bug record were examined); that `pp.all` output is human-auditable.
- **Probe limitations:** `defeq_*` counts as success, but a definitional-equality pass at default transparency is not what a reader sees. Binder names and binder info are ignored by the comparison (`Expr.eqv` semantics). Elaboration happens in an empty local context in the root namespace, with no `open` and no `set_option`, so statements that rely on scoped notation are penalized as compatibility failures.

## Evidence

- **Lean toolchain:** `leanprover/lean4` at `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (tag `v4.35.0`). Delaborator options are in `src/Lean/PrettyPrinter/Delaborator/Options.lean` (`pp.coercions` default true; `pp.coercions.types`, `pp.numericTypes`, `pp.explicit`, `pp.proofs` default false; `getPPCoercions o := o.get pp.coercions.name (!getPPAll o)`). In `src/Lean/PrettyPrinter/Delaborator/Builtins.lean`, `delabOfNat` (lines 1166–1169) reads `whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions <| withOverApp 3 do delabOfNatCore …`, and `coeDelaborator` (around line 1230) wraps the coercee in `withTypeAscription (cond := ← getPPOption getPPCoercionsTypes)`.
- **Round-trip probe and outputs:** `support/roundtrip/RoundTrip.lean`, `summarize.py`, `compare_variants.py`, `results_summary.txt` (all per-variant tables and run logs: wall time, `VmHWM`) and `default_mismatches.tsv` (all 412 silent mismatches with printed and re-printed forms). The full per-declaration JSONL outputs (about 20 MB per variant) are not preserved. They are regenerated by the command in Revalidation. Observed 2026-11-20.
- **mathlib4** `5fc503cdd50c2c198f54ccc97121ec82919e2930`, `Mathlib/Tactic/Linter/PPRoundtrip.lean`: `register_option linter.ppRoundtrip … defValue := false`. `ppRoundtrip` computes `polishSource origSubstring.toString`, formats `PrettyPrinter.ppCategory `command stx`, applies `polishPP`, and warns `if st != real`.
- **doc-gen4** `43c98922de00e9f215d2f3fe027cd2f99873212f`: `DocGen4/RenderedCode.lean` defines `RenderedCode.Tag` (`keyword | string | const | sort | otherExpr`), and `renderTagged` links only when `termInfo.expr.consumeMData` is `.const n _`. In `DocGen4/Process/NameInfo.lean`, `Info.ofTypedName` uses `delabCore … delabForallParamsWithSignature`. In `DocGen4/Process/Base.lean`, `prettyPrintTerm` uses `ppExprWithInfos`. `DocGen4/Load.lean` sets options `pp.tagAppFns true`, `pp.funBinderTypes true`.
- **leanblueprint** `56e066d30fb7b608a63f4241fee80982d7eae3ef`: `leanblueprint/Packages/blueprint.py` (`class lean`, `leanok`, `mathlibok`, `notready`, `make_lean_data` writes `lean_decls`); `leanblueprint/client.py` (`do_checkdecls` runs `lake exe checkdecls blueprint/lean_decls`). **checkdecls** `3d425859e73fcfbef85b9638c2a91708ef4a22d4`, `Main.lean`: `unless env.contains line.toName do println! "{line} is missing."`.
- **lean-liquid** `ee4795874a99ea5f9d85bd0b364425f07b932377`: `src/challenge.lean` (theorem `liquid_tensor_experiment`), `src/challenge_notations.lean` (localized `ℳ_{p'} S` notation), `src/examples/{real,pBanach,radon_measures,Ext,cond}.lean`.
- **mirror-isabelle** `20d6a3f7ffbaaa82e77f341d90db5070b3428fbe`: `src/Pure/PIDE/markup.ML` (`entityN = "entity"`, `defN = "def"`, `refN = "ref"`, `typing`), `src/Pure/PIDE/rendering.scala` (hyperlinks from `Markup.Entity.Def/Ref`, tooltips for `ENTITY`, `TYPING`), `src/Pure/PIDE/markup_tree.scala`.
- **PutnamBench** `a635813f5edf297d928f9bd5ef8324a26bdde09c`: `lean4/check_docstrings.lean` (`checkEntry` compares `findDocString?` with `escapeDocstring entry.informal_statement.trim`); `README.md` statistics. Commit history was read via the GitHub REST API on 2026-11-20. Script and output are in `support/benchmarks/`. Example commits are cited by 12-hex prefix within this repository.
- **miniF2F:** `openai/miniF2F` `4e433ff5cadff23f9911a2bb5bbab2d351ce5554`; `facebookresearch/miniF2F` `e4f113090ad82d64f8ce064d2f55b613a9b6bded`; `yangky11/miniF2F-lean4` `5746b7d6c47855ce1294bed87329618ff7f1bc31`. Commit lists and example diffs were read via the GitHub API on 2026-11-20.
- **HOL Zero:** project home page (version 0.6.3, released 2016-04-25) and `unsoundnesses.html` (7 entries), read 2026-11-20. The publication page gives the ITP 2016 abstract and the reference "LNCS 9807, pages 20-35".
- **Literature.** Identifiers were verified on 2026-11-20 via the DOI handle registry (resolution target) and Semantic Scholar metadata. Direct Crossref API access was not available from the fetcher. arXiv identifiers were verified by retrieving the arXiv PDFs.
  - Wiedijk, *Pollack-inconsistency*, ENTCS 285 (2012), doi:10.1016/j.entcs.2012.06.008. Full text read from the author's copy.
  - Adams, *Introducing HOL Zero*, ICMS 2010, doi:10.1007/978-3-642-15582-6_25. Metadata only.
  - Adams, *HOL Zero's Solutions for Pollack-Inconsistency*, ITP 2016, doi:10.1007/978-3-319-43144-4_2. Abstract.
  - Adams, *Proof Auditing Formalised Mathematics*, JFR 9(1):3–32 (2016), doi:10.6092/issn.1972-5787/4576. Abstract and reference list.
  - Hales et al., *A Formal Proof of the Kepler Conjecture*, Forum Math. Pi (2017), doi:10.1017/fmp.2017.1, arXiv:1501.02155. Full text.
  - Wenzel, CICM 2012, doi:10.1007/978-3-642-31374-5_38. Metadata only.
  - Commelin & Topaz, Bull. AMS (2024), doi:10.1090/bull/1831, arXiv:2309.14870. Full text, §5.
  - Zheng, Han, Polu, arXiv:2109.00110. Full text.
  - Tsoukalas et al., arXiv:2407.11214 (v2). Full text.
  - Ying et al., arXiv:2406.03847 (v3). Full text.

## Revalidation

1. **Round-trip rates on a new toolchain.** With the target toolchain's `lean` first on `PATH`, run `RT_HEARTBEATS=200000 lean --run support/roundtrip/RoundTrip.lean default 0 /tmp/rt_default.jsonl` (about 4 min, 2.3 GB). Repeat with `all` and `numcoetypes`, then run `python3 support/roundtrip/compare_variants.py /tmp`. A cheap smoke test: `Fin.ext_iff` should be `MISMATCH` under `default` and `exact` under `coetypes`; `Int.one_nonneg` should be `MISMATCH` under `default` and resolved under `numerals`. If either flips, the delaborator changed and the class table must be regenerated.
2. **Option interaction.** Diff `delabOfNat` and `coeDelaborator` in `src/Lean/PrettyPrinter/Delaborator/Builtins.lean`. If `delabOfNat` no longer requires `getPPCoercions`, the `pp.coercions false` + `pp.numericTypes` trap is gone.
3. **Tool binding claims.** Re-read four regions. `PPRoundtrip.lean`: does it still call `ppCategory` on unelaborated syntax, with `defValue := false`? `RenderedCode.lean` `renderTagged`: is it still const-only linking? checkdecls `Main.lean`: is it still `env.contains`? PutnamBench `check_docstrings.lean`: is it still string equality? Any change there is a change in what is bound.
4. **Benchmark history counts.** Run `python3 support/benchmarks/putnambench_history.py <new revision>`. The counts are message heuristics, so diff-check any new "disprovable" fixes before citing classes.
5. **HOL Zero record.** Re-read `unsoundnesses.html`; the counts of 7 entries / 6 printer entries hold for the page as read on 2026-11-20.
