# Term-anchored statement rendering: MMT/OMDoc whole-library exports, BEq term-level equivalence, a Lean 4 re-elaboration census, and human faithfulness-grading protocols

## Summary

- **Three binding levels.** A rendered statement can be bound to (a) source text, (b) the elaborated term (after disambiguation, coercion insertion, implicit-argument and type inference), or (c) the kernel term. The MMT/OMDoc exports differ in level. The Isabelle export takes theory content from Isabelle's `Export_Theory` data, i.e. post-elaboration Pure-logic terms. The 2011/2013 Mizar export took the verifier's constructor-level XML. The 2021 Mizar export takes the ESM/EMSM XML, which is statically analysed and identifier-resolved and keeps a `spelling` attribute for the original token. PVS supplies kernel-generated XML that keeps nearly all user-level structure. The HOL Light and Lean 3 importers read kernel-level data plus a separate notation table.
- **Identifiers survive; notation mostly does not.** In MMT every symbol reference is a global MMT name (URI); the Isabelle paper states that all symbol occurrences are exported with unique URIs. For Isabelle the scheme is `https://isabelle.in.tum.de?<session.theory>?<entity>|<kind>`, and MathML output tags each operator with `data-mmt-symref`. Rendering information is reduced, though. The Isabelle importer maps only `No_Syntax`, `Prefix` and `Infix` syntax. The Lean importer maps only prefix, postfix and infix notations. Implicit arguments are emitted but hidden by default with the CSS class `mmt-implicit-arg-hidden`. Overloading is resolved, because each occurrence carries its URI. Mixfix templates, binder notation and syntax translations are not carried over.
- **Reported export costs are large.** Isabelle2020 plus AFP needed 80 GB RAM, 8 cores and 22 h 30 min. It produced 65 GB of OMDoc/XML (310 MB XZ) for 7,027 theories, 5,291 locales and 2,116,638 individuals (types, constants, axioms, theorems). The 2011 Mizar export of 1,129 MML files took 41 min 40 s on a 4 GB laptop, with 8.6 GB of Mizar XML as input. The 2021 Mizar export took 15 min for XML, 2 h for zipped OMDoc and 30 h for MMT text syntax; the authors attribute the 30 h to an MMT scalability issue unrelated to Mizar.
- **Term-level equivalence.** BEq treats two statements as equivalent when each is provable from the other under restricted tactics. Each direction first tries `exact?` and then up to K LLM-generated proofs. On 200 human-labelled ProofNet pairs (70 equivalent, 130 not), BEq reached precision 100%, recall 72.86% and accuracy 90.50%. Definitional equality alone reached precision 100% but recall 11.43%. The reference implementation's `all` level drops the banned-token filter and accepts any proof that produces no error-severity message. In Lean, `sorry` produces a warning, not an error, so by inspection a `sorry` proof would be accepted at that level (not executed against the harness).
- **New measurement: a text round trip misses many term changes.** A probe ran Lean 4 v4.35.0 over all 28,644 theorems of its `Init` library. For each theorem it printed the type with default options, re-parsed and re-elaborated it, and compared terms. Only 78.38% came back syntactically identical (up to alpha-equivalence and metadata). For 2,652 theorems (9.26%), the print, re-parse, print round trip was textually identical while the term was not. In 178 of those, `isDefEq` at default transparency returned false, so these changes are invisible to text checks. Example: `UInt64.neg_one_eq` prints as `-1 = 18446744073709551615`, which re-elaborates as a false statement about `Int`. `pp.numericTypes` + `pp.proofs` + `pp.funBinderTypes` cut the invisible non-defeq cases to 62, with an 8% increase in median length. `pp.explicit` cut them to 0, but at 2.8× the median length. The single-threaded run took about 151 s, a median of 3.2 ms per theorem.
- **Human grading protocols are thin.** ProofNet relied on "a human expert". Wu et al. inspected 150 items, with the number of graders unstated. BEq used 4 experts who labelled independently and then reached consensus at a roundtable, with no agreement statistic reported. FormalAlign used synthetic labels and reported Fleiss' κ = 0.49 among Lean experts. FormalMATH used 12 olympiad-medalist-level experts at \$6.89 per statement. No protocol specifies which rendering (pretty-printed, fully explicit, or hover) graders must see.

## Applicability

The subjects relate as follows:

- MMT at the pinned revision contains the importers and presenters whose source was read.
- The Mizar system source shows which XML files the open-source processors write.
- The four papers on the exports report the historical runs. They are for Isabelle2020 + AFP (April 2020), MML 4.166.1132 (2011 export) and an unstated MML version (2021 export).
- The BEq repository supplies the equivalence procedure and the 200 labelled pairs. The ICLR 2025 paper reports results obtained with Lean 4.7.0-rc2 and a pinned Mathlib commit listed in its appendix.
- ProofNet, Wu et al., FormalAlign and FormalMATH supply the grading protocols.
- The Lean 4 v4.35.0 toolchain was executed for this report. It is the only subject whose behaviour is measured here rather than reported.

Scope limits:

- Export claims describe the pinned MMT importer source and the cited papers. The historical export runs were not reproduced, and costs are quoted from the papers.
- The re-elaboration census covers only theorems, not definitions, in modules whose names start with `Init` in Lean 4 v4.35.0.
  - Internal names (`Name.isInternal`) and private names are excluded.
  - Printing uses default `pp` options in the root namespace with no `open`.
  - Elaboration uses `Term.elabType` with error-to-`sorry` recovery disabled and the theorem's universe parameter names in scope.
  - `differ` means `Meta.isDefEq` at default transparency returned false, not that the statements are logically inequivalent.
  - Results for Mathlib or other libraries, other `open` contexts, or other toolchain versions are **not examined**.
- BEq behaviour is described from the source at the pinned revision and from the paper. The harness was **not executed**, because it needs a GPU-served LLM, the Lean REPL and a 2024 Mathlib build.

## Findings

### 1. What each whole-library export binds a rendering to

| Export (input artefact) | Level of content | How identifiers are formed | Proofs | Basis |
|---|---|---|---|---|
| Mizar 2011/2013 (Mizar verifier XML) | Constructor (semantic) level, chosen over the pattern (presentation) level | Mizar's `(aid, kind, absnr)` pointer to a constructor; for example `set` becomes `<OMS module="HIDDEN" name="M1"/>`. This disambiguates overloaded user-visible names. | Not translated in that export | documentation (2011 manuscript of the JAR paper) |
| Mizar 2021 (ESM/EMSM XML) | Statically analysed and identifier-resolved, *without* proof verification. Each node keeps a `spelling` attribute with the original token plus `absolutepatternMMLId`/`absoluteconstrMMLId`. | Article-scoped names built from a declaration-kind character plus pattern/constructor counters (e.g. `tarski:R1R1`) | Partial only | documentation (2021 preprint) + source (importer) |
| Isabelle + AFP (PIDE session; `isabelle.Export_Theory`) | Post-elaboration Pure-logic terms (`Const`/`Free`/`Bound`/`Abs`/`App`) with explicit type instantiations of polymorphic constants. Locales get a structure-preserving representation; other high-level specification elements are exported only through their elaboration. | `https://isabelle.in.tum.de?<long-theory-name>?<entity-name>\|<entity-kind>`, e.g. `https://isabelle.in.tum.de?HOL.Nat?Nat.nat\|type` | Off by default (`mmt_proof_terms = false`, "not scalable") | source + documentation |
| PVS Prelude + NASA library (PVS kernel XML) | Kernel output that keeps "virtually the entire original source structure, down to source references and redundant brackets". Includes kernel-inferred information and optional type-correctness conditions (TCCs). | MMT URIs per PVS theory and declaration. Theory-parameter instances are carried as implicit arguments, and parametric includes are mimicked with a special include declaration. | High-level proof objects are not complete: decision-procedure steps are not recorded | documentation (survey) + source (`inExts = List("xml")`) |
| HOL Light (kernel instrumentation) | Kernel level. The export also reads HOL Light's internal notation table. | One OMDoc theory per source file | Dependency-only, no proof terms | documentation (survey) |
| Lean 3 (`lean --export` low-level text) via `mmt-lean` | Kernel declarations, re-read with the `trepplein` checker | MMT names from Lean names | Definitions keep values | source |

Basis for the Isabelle row: `src/mmt-isabelle/.../Importer.scala` `import_term` (line 591 onward) matches only on `isabelle.Term.{Const,Free,Var,Bound,Abs,App}`. A `Var` (schematic) raises "Illegal schematic variable". The paper states that the export "is foundational ... relative to the Pure logic in Isabelle's kernel, which arises from the original user input through a series of highly non-trivial transformations (elaboration)". It also states that trusting the conservativity of elaboration "may be a bigger leap than trusting the correctness of the proofs".

### 2. Which reader-relevant information survives into the rendering

**Isabelle notation.** Pinned MMT source `Importer.scala`, lines 297–331:

```scala
syntax match {
  case isabelle.Export_Theory.No_Syntax => xname_notation
  case isabelle.Export_Theory.Prefix(delim) => List(prefix_notation(delim, implicit_args))
  case infix : isabelle.Export_Theory.Infix => ... Infix(delim, implicit_args, 2, assoc) ... Precedence.integer(infix.pri)
}
```

Consequences:

- Infix priority and associativity are preserved.
- Every other Isabelle syntax form arrives as `No_Syntax` or `Prefix` and renders as a prefix application of the entity name. This covers general mixfix templates, binders, set-builder notation and parse/print translations.
- `implicit_args` equals the number of type arguments, so type instantiations are present in the term but not displayed.

Basis: source.

**Lean 3 notation.** `LeanImporter.scala`, lines 171–189, maps only `lean.Prefix`/`Postfix`/`Infix`. Line 180 defines the implicit arguments as "universe params and leading Lean-implicit (= non-default) arguments":

```scala
val impl = params.length + args.takeWhile(_.of.info != BinderInfo.Default).length
```

Basis: source.

**Presentation.** In `MathMLPresenter.scala`, `doDelimiter` (line 81) emits each operator with `data-mmt-symref -> p.toPath`, the symbol's URI. `doImplicit` (line 144) wraps implicit arguments with `doOptional(implicitarg, …)`, which outputs `<mrow class="mmt-implicit-arg mmt-implicit-arg-hidden">` (lines 139–143). Inferred bound-variable types get the same treatment with `mmt-reconstructed-type`. Implicit information is therefore present in the DOM, hidden by default and toggleable. Basis: source.

**Detectability of rendering-fidelity failure classes by a reader of each export's default rendering.** These are derived from the rows above. "Data" means the information is in the exported term even if not displayed.

| Failure class | Mizar 2013 (constructor level) | Mizar 2021 (ESM) | Isabelle | PVS | Lean 3 (`mmt-lean`) |
|---|---|---|---|---|---|
| Hidden coercion | Not examined | Not examined | Coercions are explicit constants in Pure terms, so they render as named prefix applications: detectable | Kernel XML includes inferred information: data, presentation not examined | Coercion functions are ordinary constants: detectable |
| Implicit arguments | Constructor arguments are explicit in the data; presentation not examined | `spelling` plus visible-argument positions are in the XML | In data; hidden by default (`mmt-implicit-arg-hidden`) | Theory-parameter instances in data | In data; hidden by default |
| Overloaded notation | Resolved to constructor ids: detectable | Resolved (`absolute…MMLId`) | Resolved per occurrence (URI) | Resolved per occurrence | Resolved (URI) |
| Precedence/associativity | Not examined | Not examined | Preserved for `Infix` only | Redundant brackets preserved | Priority preserved for prefix/postfix/infix |
| Redefined constants (Mizar `redefine`) | Not examined | The 2021 paper lists redefinitions without definiens as needing extra static analysis | n/a | n/a | n/a |

**Open-source Mizar artefacts versus the importer's input extension.** The pinned `MizarProject/system` file `base/esmprocessor.dpr` (program `Even_More_Strict_Mizar_Processor`) reads `MizFileName+'.wsx'` at line 23 and writes `Write_MSMizArticle(lWSTextProper,MizFileName+'.msx')` at line 30. That is the same extension that `base/msmprocessor.dpr` writes at line 85. The pinned MMT importer declares `def inExts = List("esx")` (`translator/Translator.scala`, line 66). The 2021 paper also names the EMSM files ".msx". How `.esx` files are produced from the open-source processors at these revisions is therefore **unknown** (renaming, a binary-distribution tool, or another producer). Basis: source; no upstream defect is claimed.

### 3. Reported whole-library export costs

| Export | Input size | Output size | Time | Hardware | Basis |
|---|---|---|---|---|---|
| Mizar 2011 (MML 4.166.1132, 1,129 files) | Source 77.5 MB (13.5 MB zipped); Mizar XML 8.6 GB (425.0 MB zipped) | Pragmatic OMDoc 894.8 MB (22.7 MB); core OMDoc 1015.3 MB (25.3 MB) | 29 min 46 s + 11 min 54 s = 41 min 40 s for pipeline steps 2–4 | Intel Core i5-2410M, 4 GB RAM | documentation (2011 manuscript); sum derived |
| Mizar 2021 (whole MML; proofs partial) | MML 100 MB; XML 4.7 GB (15 min, parallel; "Mizar only needs to resolve identifiers, which does not require verifying the proofs") | 18 MB zipped OMDoc (2 h); 200 MB MMT text syntax (30 h, attributed to an MMT scalability issue) | as listed | "simple hardware" | documentation (2021 preprint) |
| Isabelle2020 + AFP | 680 sessions, 7,027 files, 160 MB theory text (30 MB XZ) | 65 GB OMDoc/XML (310 MB XZ). Contents: 7,027 theories, 5,291 locales (incl. 1,236 type classes), 2,116,638 individuals (11,724 type, 204,404 const, 236,186 axiom, 1,497,689 thm), and 400,996,957 relations including 386,325,246 `ulo:uses` | 22 h 30 min elapsed | 80 GB RAM and 8 cores used (40-core/128 GB server available) | documentation (arXiv version) |
| Isabelle batch build, for comparison | Same | Heap images | ≈46 h CPU, 13 h elapsed | 8 cores, 16 GB RAM | documentation |
| PVS, HOL Light | Not examined (ITP 2017 and CICM 2014 full texts not obtained) | | | | |

Derived from these figures:

- The Isabelle export uses about 5× the build's memory (80 GB vs 16 GB) and about 1.7× its elapsed time (22.5 h vs 13 h). The paper itself says "around 2 times the memory and 2–5 times the elapsed time" relative to an elementary batch build, so the two configurations it compares are evidently not identical; that disagreement is preserved here.
- The four listed Isabelle individual kinds sum to 1,950,003, leaving 166,635 of the 2,116,638 unitemized in the text examined.
- XZ-compressed output is 310/30 ≈ 10.3× the XZ-compressed source, matching the paper's "about factor 10". The paper attributes the growth to "all occurrences of symbols are disambiguated and exported with their unique URIs", source references on every element, and explicit type arguments and bound-variable types.
- The 2011 Mizar XML is 8.6 GB / 77.5 MB ≈ 111× the source; the 2021 XML is 4.7 GB / 100 MB = 47×.

The survey reports that a two-week research visit was "the minimal investment necessary to synchronize understanding of the schema and to specify (not implement) the export". It also says developer effort for system-side exporters could often not be quantified. The 2011 translator comprised 88 Scala classes and 47 Scala objects. Basis: documentation.

### 4. Term-level equivalence: definitional equality and BEq

**Definitional-equality stage.** In `equivalence/def_eq.py`, line 84, the harness submits:

```python
code_P + '\n\n' + code_Q + '\n' + 'example : thm_P = thm_Q := by rfl'
```

`thm_P` and `thm_Q` are `sorry`-proved theorems. `Eq` is homogeneous, so `thm_P = thm_Q` typechecks only if the two statement types are definitionally equal. Proof irrelevance then closes it by `rfl`. Success means no error-severity message (line 87). Basis: source.

The same input shape was reproduced in Lean 4 v4.35.0 (`support/DefEqStage.lean`, `support/DefEqStage.out.txt`):

| Case | Result |
|---|---|
| `(2 : Nat) + 2 = 4` vs `Nat.add 2 2 = 4` | Accepted |
| Swapped hypothesis order `(hp : p) (hq : q)` vs `(hq : q) (hp : p)` | Rejected: "Type mismatch … has type `∀ (p q : Prop), q → p → p ∧ q` but is expected to have type `∀ (p q : Prop), p → q → p ∧ q`" |
| Same swapped pair, proved in both directions by a single `exact thm_P p q hp hq` | Accepted |
| `sorry` proof | Reported as `warning: declaration uses 'sorry'` |

Basis: execution (Lean 4 v4.35.0, not the BEq harness or its Lean 4.7.0-rc2).

**BEq.** From the paper, Eqs. (1)–(3):

```text
T(sP | sQ, R)  = some sP' ∈ U(sP, R) with sQ ≡_D sP'   (else ⊥)
sP ←U sQ       ⇔ sP ≡_D T(sQ | sP, R)
sP ~B sQ       ⇔ sP ←U sQ ∧ sQ ←U sP
```

R is a tactic set, and T is approximated by sampling tactic sequences from an LLM and executing them in Lean.

Implementation at the pinned revision (`equivalence/beq_basic.py`, `check_equivalence_PQ`, lines 275–350):

1. **Heuristic.** Run `exact?` as the body of `theorem thm_Q … := by` with `thm_P` (a `sorry` axiom) in scope. Succeed iff there is no error message and the last info message contains `Try this: exact` and `thm_P` (lines 286–292).
2. **LLM.** Otherwise sample `try_num` proofs (default 8; temperature 0.7 if `try_num > 1`, else beam search at 0.0; `max_tokens` 512; lines 236–242). Reject a proof if it contains any `BANNED_TOKENS = ['sorry','admit','by_contra']` by substring (lines 50–54, 325).
   - At the basic level, every line must start with `have` or `exact`. A `have … by` line must contain `exact`, and the `exact` line must be last (lines 327–335).
   - Accept iff the text contains `thm_P` (or `exact?` suggested it) and the REPL reports no error-severity message (lines 337–343).
3. Repeat with the roles swapped (lines 406–412). Equivalence is the intersection of the two directions' successes (line 436).

Differences between the levels at the same revision:

- `beq_normal.py` and `beq_advanced.py` replace the line-shape rule with a **substring** test, `any([tac in line for tac in ALLOWED_TACTICS])` (normal, line 342). Any line containing `rw`, `ext`, `use`, `intro` or `apply` as a substring passes, e.g. `simp_rw`, `erw`, `apply_fun`, or a line containing the word "because" (which contains `use`). Basis: source; whether such proofs occurred in the reported runs is **unknown**.
- `beq_all.py` has no `BANNED_TOKENS` filter and no line rule. Its LLM path accepts when (lines 320–326):

```python
assert ('thm_P' in equiv_proof) or any([...'Try this: exact' in m.data and 'thm_P' in m.data ...])
...
assert len([m for m in run_result.messages if m.severity == 'error']) == 0, str(run_result.messages)
is_success = True
```

Lean reports `sorry` as a warning (execution above), and a comment satisfies the `'thm_P' in equiv_proof` substring test. So a candidate proof `sorry -- thm_P` would satisfy both assertions. Basis: source + derived; not executed against the harness. The paper's Table 4 reports false positives only for the Advanced and All levels (All, bidirectional, K=16, T=0.7: 3 false positives, precision 94.44%) and states that "Advanced and All may lead to false positives". The cause of those particular false positives is **unknown**.

**What each check counts as equivalent.** Definitional equality is reflexive, symmetric and transitive, but misses reorderings, currying and `Set` versus subtype encodings. BEq is reflexive and symmetric by construction, but its transitivity depends on the LLM. The paper's table marks it ✓ for R, S and T as a relation. As implemented, success depends on sampling, so the relation computed is not guaranteed transitive. Basis: derived.

### 5. Automatic judges versus human labels

Human Equivalence Benchmark (repository `data/human_equivalence/`):

- `o1-generated/labels.json`: 100 pairs, 39 `true` and 61 `false`.
- `rautoformalizer-generated/labels.json`: 100 pairs, 31 `true` and 69 `false`.
- Total: 70 equivalent and 130 inequivalent (counted from the files; basis: source). This matches the paper's Typecheck precision of 35.00% (70/200).

ICLR 2025 Table 1 (precision / recall / accuracy on the 200 pairs; basis: documentation):

| Metric | Precision | Recall | Accuracy | Derived counts |
|---|---|---|---|---|
| Identity match | 0/0 | 0.00% | 65.00% | |
| Typecheck | 35.00% | 100.00% | 35.00% | |
| BLEU threshold (best over thresholds) | 62.96% | 24.29% | 68.50% | |
| LLM majority vote, InternLM2-Math-Plus-20B, 16 samples | 40.00% | 94.29% | 48.50% | |
| LLM majority vote, DeepSeek-V2.5, 16 samples | 70.59% | 85.71% | 82.50% | ≈60 TP, ≈25 FP |
| Definitional equality | 100.00% | 11.43% | 69.00% | 8 TP |
| BEq | 100.00% | 72.86% | 90.50% | 51 TP, 0 FP, 19 FN |

The paper attributes its 19 false negatives to "semantic gaps" (9) and "transformation function failure" (10). Examples:

- `Infinite {p : Nat.Primes // p ≡ -1 [ZMOD 6]}` versus `Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 6 = 5}`.
- An instance-path mismatch, `NonUnitalNonAssocSemiring.toMul` versus `NonUnitalNonAssocRing.toMul`, invisible in the pretty-printed goal.

In Table 4, `exact?` alone (K=0, bidirectional) already gives precision 100%, recall 67.14% (47/70) and accuracy 88.50%. The LLM adds 4 true positives. Unidirectional checking with K=0 has 16 false positives (precision 75.00%).

**FormalAlign** scores a pair with `V_align = (V_cer + V_sim)/2`. `V_cer` is the exponentiated mean token log-probability of the formal statement given the informal one; `V_sim` is the cosine similarity of final hidden states. The score is thresholded. Its labels are synthetic: aligned pairs plus mutated formal statements (variable added, type changed, constant or exponent changed, …). FormalAlign versus GPT-4 on (alignment-selection score, precision, recall):

| Dataset | FormalAlign | GPT-4 |
|---|---|---|
| FormL4-Basic | 99.21 / 93.65 / 86.43 | 88.91 / 26.33 / 88.69 |
| MiniF2F-Test | 64.61 / 66.70 / 63.37 | 68.31 / 51.11 / 94.65 |

FormalAlign agrees with human judgments only on these synthetic labels; it was not compared with human equivalence labels for model outputs. Basis: documentation.

### 6. Library-scale re-elaboration census (Lean 4 v4.35.0, `Init`)

**Method.** `support/ReelabProbe.lean` handles each of the 28,644 candidate theorems as follows:

1. `ppExpr` the stored type with the mode's options (width 10⁶, so a statement prints on one line).
2. `Parser.runParserCategory env `term`.
3. Elaborate in one metavariable context, with `withoutErrToSorry` and `withLevelNames ci.levelParams`, and then call `synthesizeSyntheticMVarsNoPostponing` and `instantiateMVars`.
4. Classify the result:
   - `exact` if `stripMData e2 == stripMData t1` (`Expr.eqv`: alpha-equivalence ignoring binder names and annotations);
   - `defeq` if not exact but `isDefEq` succeeds at default transparency;
   - `differ` if `isDefEq` returns false;
   - `mvar` if metavariables remain;
   - `elabfail` or `parsefail` otherwise.
5. Re-print the re-elaborated term and record whether the text is identical (`same`), which is what a text-only round trip checks.
6. For `defeq` and `differ`, record the first differing subterm pair.

The run was single-threaded on an x86-64 Linux workstation under a cgroup memory-limit wrapper.

**Results (execution; full summaries in `support/summary_all_modes.txt`):**

| Mode (pp options) | exact | defeq | differ | mvar | elabfail | parsefail | text same & term not exact | text same & `differ` | median chars |
|---|---|---|---|---|---|---|---|---|---|
| default | 22,451 (78.38%) | 809 | 474 | 3,371 | 1,477 | 62 | 2,652 (9.26%) | 178 | 83 |
| `pp.proofs` | 23,683 (82.68%) | 1,075 | 480 | 1,840 | 1,500 | 66 | 1,663 | 184 | 84 |
| targeted (`pp.proofs`, `pp.numericTypes`, `pp.funBinderTypes`) | 24,451 (85.36%) | 1,099 | 264 | 1,717 | 1,047 | 66 | 1,529 | 62 | 90 |
| explicit (`pp.explicit`, `pp.proofs`) | 27,903 (97.41%) | 615 | 0 | 102 | 18 | 6 | 565 | 0 | 234 |

"Text same & term not exact" is the sum of `defeq/same`, `differ/same` and `mvar/same` (derived). The opposite error, where the text changed but the term was exact (a text false alarm), occurred in 10 theorems in each of the first three modes, all binder regrouping (`{k : Nat} {m n : Nat}` re-prints as `{k m n : Nat}`), and in 351 theorems in explicit mode.

**Change classes invisible to a text round trip** (default mode, the 178 `differ/same` theorems; heuristic classification by `support/classify_differ.py`):

| Class | Count | Example (printed text is identical before and after) |
|---|---|---|
| Numeral/literal type defaulting | 90 | `UInt64.neg_one_eq : -1 = 18446744073709551615` re-elaborates at `Int`, where it is false (`support/SpotCheck.out.txt`). `Int.one_ne_zero : 1 ≠ 0` re-elaborates at `Nat`; `USize.zero_lt_one : 0 < 1` at `Nat`. |
| Universe instantiation / element type defaulted | 39 | `List.sum_nil : [].sum = 0` re-elaborates with the element type fixed by numeral defaulting (`Eq.{1}` vs `Eq.{succ u}`). The quantified `α` is no longer used. |
| Hidden binder type or argument dependency | 21 | `Array.mem_extract_iff_getElem`: `∃ k hm, as[i + k] = a`. The omitted type of `hm` is re-inferred differently. |
| Instance-binder identity | 16 | `ite_decide_self_left`: `[h : Decidable p] {w : Decidable p}`. The rendering does not show which of two same-typed instances is used. |
| Auxiliary matcher identity / other | 12 | `match_1` versus `List.dropLast.match_1` |

With the targeted options, numeral defaulting among `differ/same` falls from 90 to 2, and the remaining 62 are mostly binder-dependency (25) and instance-identity (21) cases. The `defeq/same` class (734 in default mode) is dominated by:

- auxiliary-matcher renaming (332);
- universe-level normal-form differences such as `Eq.{max (succ u_2) (succ u_3)}` versus `Eq.{max (succ u_3) (succ u_2)}`;
- `optParam` wrappers absent after re-elaboration;
- proof-term differences such as `Decidable.byContradiction …` versus an `_proof_2` auxiliary lemma.

**Failures that a text round trip does catch** (`differ/changed`, 296 in default mode): coercion arrows re-elaborate with the wrong target. For example, `Int.ofNat_add_ofNat`, `↑m + ↑n = ↑(m + n)`, re-elaborates to `m + n = m + n`, a different and trivially true statement. In 60 of the 62 `parsefail` cases, the printed text uses the `n#'h` (`BitVec.ofNatLT`) notation, which the root-namespace parser rejects ("expected end of input"). The notation is declared as `scoped syntax:max term:max noWs "#'" noWs term:max : term` (`src/lean/Init/Data/BitVec/Basic.lean`, line 189, in the v4.35.0 toolchain sources), yet the default printer emits it outside its namespace. Basis: source + execution. Of the 1,477 `elabfail` cases, the leading causes are stuck type-class problems after binder types are omitted (e.g. `Std.Associative fun x1 x2 => x1 ^^^ x2`) and "failed to prove index is valid" for `xs[i]` whose bound proof is not reconstructible.

**Cost (execution).**

| Measure | Default mode |
|---|---|
| Per-theorem total | median 3.21 ms, p90 7.71 ms, p99 44.8 ms, max 705 ms |
| Phase sums | printing 29.4 s, parsing 5.7 s, elaboration 83.7 s, comparison incl. re-print 27.4 s |
| Loop wall time | 150.8 s ≈ 190 theorems/s (derived) |
| `Init` import | 0.64 s |
| Peak RSS (GNU `time`) | 2,016,688 KB |

Explicit mode has a similar total (149.3 s): elaboration is cheaper (40.7 s) but printing and parsing are more expensive (47.1 s and 10.7 s). Printed length grows 2.8× at the median (234 vs 83 characters, derived), 3.0× at the mean (362.4 vs 121.6), and reaches 68,530 characters at the maximum.

### 7. Design: a library-scale "re-elaborate, then compare terms" measurement

Derived from §§4–6:

1. **Unit.** One row per declaration `c` whose type is the statement shown to readers (theorems, plus definitions' types if desired). Record the module, the options used and the `open`/namespace context. Re-elaborate in the declaration's *own* context, re-establishing namespaces and `open`s. The census above used the root context, so its `parsefail` count includes the scoped `#'` notation (60 of 62 cases).
2. **Tiers.**
   - Tier 0: text equality after re-print, to report the text check's verdict.
   - Tier 1: `Expr.eqv` after metadata stripping.
   - Tier 2: `isDefEq` at default transparency, then at `.all`, with a heartbeat cap. The census used 200,000×1000 heartbeats per call and no wall-clock cap.
   - Tier 3, only for tier-2 failures: BEq-style bidirectional proof with a restricted, *line-shape-checked* tactic set (the basic level, not substring matching), `sorry`/`admit`/`native_decide` rejected, and the axioms of both proofs inspected (`#print axioms` must not show `sorryAx`).
3. **Accounting.** Per tier, record wall time and heartbeats per declaration, and the p50/p99/max per library. Report the four-way cross-tabulation `{text same, text changed} × {exact, defeq, proved-equivalent, differ/failed}`.
4. **What it detects that text cannot.** Numeral and element-type defaulting, hidden binder types, instance-binder identity, and incomplete terms from elided proofs (`⋯`), whenever re-printing reproduces the same text.
5. **What it cannot detect.** A rendering that is wrong in the *reader's* model but re-elaborates to the same term (for example a misleading notation definition). Mismatches between informal intent and the formal statement. And any fault in the elaborator itself, because the check reuses the elaborator. These need human grading (§8) or an independent checker.

### 8. Published human grading protocols for statement faithfulness

| Study | Items graded | Graders | Material shown | Agreement / disagreement handling | Rendering prescribed? | Basis |
|---|---|---|---|---|---|---|
| Wu et al. 2022 (Isabelle) | 150 random MATH problems (50 algebra, 50 number theory, 50 intermediate algebra), Codex outputs | Not stated | Informal problem and Isabelle statement | None reported. Multi-label failure taxonomy (per-subject column sums 59/76/80 exceed 50, so derived as multi-label); 38/150 = 25.3% "perfect" | No | documentation |
| ProofNet 2023 (Lean 3) | Model formalizations of 371 statements (186 test + 185 valid lines) | "a human expert" | Not stated | None reported. Codex 12-shot accuracy 13.4%, typecheck 23.7%, BLEU 25.1; retrieval 16.1% | No | documentation + source |
| BEq / Human Equivalence Benchmark 2025 (Lean 4) | 200 typechecked predictions paired with ProofNet ground truth | 4 experts (1 formal verification, 3 computer science) | Formal statement pairs | Independent labelling, then roundtable consensus per item; no κ located | No | documentation + source |
| FormalAlign 2024 | 80 MiniF2F-test items, balanced, with synthetic misalignment labels | Text says four Lean 4 experts, but Table 11 lists three (83.75%, 77.50%, 77.50%; their mean is 79.58%, derived) | Same informal and formal statements | Fleiss' κ = 0.49. About 3 h per expert for 80 items, ≈2.25 min/item (derived). GPT-4o 47.50%, FormalAlign 65.00% | No | documentation |
| FormalMATH 2025 | Statements surviving compiler, multi-LLM semantic and negation-disproof filters; 5,560 retained | 12 IMO-medalist-level experts | Natural-language statement and Lean 4 statement | Per-item grader count not located. 72.09% preserved; \$6.89/statement; 22 days. LLM unanimity ≈30% on high-school competition items, 4.63% on HardMath | No | documentation |

No protocol examined requires graders to see a fully explicit form, hover information or the elaborated term. §6 shows that the default rendering can hide numeric types, element types and instance choices that change meaning.

### 9. Performance and resource coverage (L1–L6)

| Level | Measured / cited / derived values | Not measured |
|---|---|---|
| L1 Authoring and grading effort | Export specification: ≥ 2 weeks of joint expert time (survey). 2011 Mizar translator: 88 classes + 47 objects. FormalMATH \$6.89 per statement and 22 days with 12 graders. FormalAlign ≈3 h per 80 items per expert. BEq LLM budget per direction: `try_num` 8 (code default; the paper used 16), 512 tokens per sample | LLM token totals per BEq decision; person-hours for the BEq labels |
| L2 Toolchain build | Isabelle + AFP batch build ≈46 h CPU / 13 h elapsed, 8 cores, 16 GB | MMT build time; Lean toolchain build (release binaries used) |
| L3 Elaboration and translation latency | Census: 3.21 ms median, 44.8 ms p99 per theorem. Mizar 2011: 41 min 40 s; Mizar 2021: 15 min, 2 h and 30 h; Isabelle: 22 h 30 min | BEq per-pair latency; LSP-interactive latency of re-elaboration |
| L4 Generated-code execution | Known not to apply: no executable artefacts are produced | — |
| L5 Checking | Census `isDefEq` plus re-print: median 0.79 ms. Isabelle proof terms off by default; footnote: parts of Isabelle/HOL Main produce "hundreds of megabytes of proof terms". Mizar 2021 XML generation skips proof verification | Re-checking speed of any exported library in an independent checker |
| L6 Memory and disk | Census peak RSS ≈ 2.0 GB. Isabelle export: 80 GB RAM, 65 GB XML / 310 MB XZ. Mizar 2011: 8.6 GB XML and 1.0 GB core OMDoc. Mizar 2021: 4.7 GB XML, 18 MB zipped OMDoc, 200 MB MMT text | Peak RSS of the Mizar and PVS exports; energy |

### 10. Comprehensibility and conceptual model (C1–C2)

**C1.** A URI on every symbol (`data-mmt-symref`) lets a reader resolve *which* constant is meant, which settles overloading. It does not show *which instantiation*: implicit arguments and inferred types are hidden by default. The census quantifies the trade-off:

- Fully explicit printing removes every non-defeq round trip in `Init` but makes statements 2.8× longer at the median. That is an extra working-memory cost for every reader.
- Three targeted options remove most text-invisible meaning changes at an 8% median length cost.
- The remaining hazard, which instance of two same-typed binders is used, has no targeted option among those tested.

In the graders' setting, Fleiss' κ = 0.49 among Lean experts on synthetic misalignments suggests that formal statements are not reliably human-auditable from their printed form alone. The κ is from one 80-item study.

**C2.** Three mechanisms appear in the sources, each enforcing a different invariant:

- URI binding: a name resolves to a declaration.
- Re-elaboration with term comparison: the rendering denotes the stored term, a Pollack-style consistency of the printer at term level.
- Bidirectional proof: two different terms are logically interchangeable.

A text round trip is the special case of the second mechanism that compares strings after a second print, and §6 shows it is strictly weaker on this corpus. A smaller model is "parse ∘ print = id up to `isDefEq` on stored terms", checked per declaration. URI binding is then a corollary for constants, and BEq is needed only where two *distinct* source statements are compared.

### 11. Validation coverage (V1–V4)

| Kind | What the sources provide | Gap |
|---|---|---|
| V1 Specification adequacy and non-vacuity | BEq is validated against 200 human labels. FormalAlign is validated against synthetic mutants (variable, type and constant changes), a mutation-analysis analogue; mutant "kill" rates are its precision and recall | No study validates the human labels themselves against a second independent panel |
| V2 Checker soundness | Lean's kernel checks the BEq proofs. The `trepplein` re-check is used in the Lean 3 importer | No adversarial testing of BEq's acceptance predicate (§4); no independent re-check of the Isabelle or Mizar exports reported in the texts examined |
| V3 Concurrency, crash, silicon | Known not to apply to these subjects | — |
| V4 Human comprehension | Grading studies (§8) | No behavioural test of what graders believe a rendering means; κ is reported only by FormalAlign |

## Boundaries

- **Not examined.**
  - Full texts of Kaliszyk–Rabe (CICM 2014, HOL Light), Kohlhase–Müller–Owre–Rabe (ITP 2017, PVS), Bancerek et al. (JAR 2018) and Rabe–Kohlhase (Inf. Comput. 2013). Their DOIs resolve, but the publisher full texts were not obtained, so HOL Light and PVS cost figures are absent and their rows rest on the survey (arXiv:2005.03089).
  - The 2011 Mizar figures come from the 2011 manuscript of the JAR paper, not the published version.
  - The Isabelle figures come from the arXiv version (2005.08884v1) of the LIPIcs paper.
  - MathHub-hosted export outputs were not opened.
  - The `src/mmt-mizar` handling of Mizar redefinitions and hidden arguments was not traced end to end.
- **Not executed.** The BEq harness, FormalAlign and every historical export. The `sorry` acceptance risk in `beq_all.py` is derived from source and from Lean 4.35 warning severity, not from a harness run; it may also be moot if `all` is never used for headline results.
- **Unknown.**
  - How `.esx` input is produced from the pinned open-source Mizar processors (§2).
  - Whether BEq's 0 false positives at the normal level would persist on a larger or adversarial pair set.
  - Whether the paper's All-level false positives involved banned tokens.
- **Scope of the census.**
  - One library (`Init`), one toolchain (v4.35.0), the root namespace, and theorems only.
  - `differ` is `isDefEq` failure at default transparency, not proven inequivalence.
  - Classes come from a heuristic first-difference classifier.
  - Rates for Mathlib, whose statements use far more notation, coercions and instance-heavy structures, are **not examined** and should not be extrapolated from these numbers.
- **Attractive stronger conclusions not established.**
  - That URI-anchored exports make statements faithful to the source author's notation (they preserve identity, not form).
  - That BEq is sound in general (100% precision on 200 pairs is an empirical result).
  - That human graders are an adequate oracle (only one agreement statistic exists).

## Evidence

Evidence was observed on 2026-11-20 (UTC). GitHub revisions were resolved through the GitHub API, and files were read from `raw.githubusercontent.com` at the following commits.

- `UniFormal/MMT` @ `71814b0fec9c1f2dbe7d677ab65bb433bc90ec08`:
  - `src/mmt-isabelle/src/info/kwarc/mmt/isabelle/Importer.scala`: line 69 (`narration-base: https://isabelle.in.tum.de`), lines 297–331 (`notation`), 591–614 (`import_term`), 619–627 (`import_prop`), 729 (`mmt_proof_terms`), 761–768 and 966 (RDF timing).
  - `src/mmt-isabelle/etc/options`: lines 21 and 24 (`mmt_type_checking`, `mmt_proof_terms` both `false`).
  - `src/mmt-isabelle/README.md`: big-example heap advice, 16 GB Poly/ML and 32 GB Java pointer-width thresholds.
  - `src/mmt-mizar/src/info/kwarc/mmt/mizar/translator/Translator.scala`: lines 64–66 (`inExts = List("esx")`), 95–99 (parse timing).
  - `src/mmt-pvs/src/info/kwarc/mmt/pvs/Importer.scala`: line 23 (`inExts = List("xml")`); `Translator.scala`: line 65 (`doSourceRef` from the PVS `place` attribute).
  - `src/mmt-lean/src/info/kwarc/mmt/lean/LeanImporter.scala`: lines 14–24 (low-level export and `trepplein`), 171–189 (notation; line 180 implicit-argument count).
  - `src/mmt-api/src/main/info/kwarc/mmt/api/presentation/MathMLPresenter.scala`: lines 81–96, 139–146; `HTMLAttributes.scala`: lines 18, 60, 67, 69.
- `MizarProject/system` @ `e04ee5d40cd3ffc4c6027f41c003bc8de0a784a6`: `base/esmprocessor.dpr` lines 10, 21–30; `base/msmprocessor.dpr` lines 78, 85; `base/wsmparser.dpr` line 90 (`.wsx`).
- `Purewhite2019/rethinking_autoformalization` @ `5ce3b814a5d0213429cc92244e5467425b22297a`:
  - `equivalence/def_eq.py` lines 75–93.
  - `equivalence/beq_basic.py` lines 50–54, 236–242, 275–350, 406–412, 436.
  - `equivalence/beq_normal.py` lines 50–63, 338–351.
  - `equivalence/beq_advanced.py` (ALLOWED_TACTICS list).
  - `equivalence/beq_all.py` lines 268–331.
  - `data/human_equivalence/*/labels.json` (label counts).
- `zhangir-azerbayev/ProofNet` @ `509ad79710ed4f46ff5c282ed5640c1aa9ac3f30`: `README.md` (371 examples; Lean 3, deprecated in favour of Lean 4 ports); `benchmark/test.jsonl` (186 lines) and `valid.jsonl` (185 lines); `eval/results/*/metrics.json` (BLEU only).
- `leanprover/lean4` v4.35.0 @ `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (the `lean --version` commit equals the tag commit).
  - Toolchain source read: `src/lean/Init/Data/BitVec/Basic.lean` line 189 (the `scoped syntax` for `#'`).
  - The probe was run as `lean --run ReelabProbe.lean Init 0 <mode>` for each mode, under GNU `time -v`.
  - Outputs, scripts and the 474 default-mode `differ` rows are in `support/`. `SpotCheck.lean` and `DefEqStage.lean` were run with `lean <file>`.
- Papers:
  - Kohlhase–Rabe–Wenzel, DOI 10.4230/LIPIcs.TYPES.2019.1, read as arXiv:2005.08884v1 (§5.3 statistics; naming scheme; adequacy paragraph).
  - Iancu–Kohlhase–Rabe–Urban, DOI 10.1007/s10817-012-9271-4, read as the 2011 manuscript (pipeline and size table).
  - Rothgang–Korniłowicz–Rabe, DOI 10.1007/978-3-030-81097-9_17, read as the author preprint (WSM/MSM/EMSM; conclusion table).
  - Kohlhase–Rabe, arXiv:2005.03089 (§§2.4, 4, 8).
  - Liu et al., ICLR 2025, OpenReview `hUb2At2DsQ` (§3.2, Table 1, Table 4, A.4, labelling paragraph, toolchain appendix).
  - Wu et al., arXiv:2205.12615 (§4.4, Table 2).
  - Azerbayev et al., arXiv:2302.12433 (§4.1.1, Table 3).
  - Lu et al., arXiv:2410.10135 (Eqs. 3–5, Table 3, Appendix G Table 11).
  - Yu et al., arXiv:2505.02735 (Table 2, §3).
- Identifier verification: each DOI above, plus 10.1007/978-3-319-08434-3_26, 10.1007/978-3-319-66107-0_21, 10.1007/s10817-017-9440-6 and 10.1016/j.ic.2013.06.001, was resolved through the doi.org handle API (response code 1). Title, authors, venue and year were matched against OpenAlex metadata; Crossref was unreachable from the observation host. arXiv identifiers were verified by fetching the arXiv listing or PDF and matching titles and authors.

## Revalidation

- **Census (cheapest, most discriminating).** With a Lean 4 toolchain on `PATH`, run `lean --run support/ReelabProbe.lean Init 0 default`. Then run `python3 support/summarize.py out.tsv` and `python3 support/classify_differ.py out.tsv`, and compare the status counts with §6. For a quick check, run only `lean support/SpotCheck.lean`: if `(-1 = 18446744073709551615)` still elaborates at `Int` while `UInt64.neg_one_eq` prints without type ascriptions, the headline numeral-defaulting class persists. Changing toolchain, library or namespace context requires rerunning the census; do not reuse the rates.
- **Export claims.** Re-read the `notation` function in `src/mmt-isabelle/.../Importer.scala` and `LeanImporter.constant`. Any new `case` beyond `No_Syntax`/`Prefix`/`Infix` (or `Prefix`/`Postfix`/`Infix`) changes §2. Diff `inExts` in the Mizar importer against the extensions written by `base/esmprocessor.dpr`.
- **BEq acceptance.** Diff `check_equivalence_PQ` across `equivalence/beq_*.py`. The `all`-level risk is gone if a `BANNED_TOKENS` check or an axiom check (`#print axioms` without `sorryAx`) is added before `is_success = True`.
- **Grading protocols.** These are fixed publications; revalidate only by reading newer versions of the cited papers.
