# Keeping prose, formal definitions and code in agreement: comment-drift detectors, single-source checked documents (Ott, Verso, Isabelle antiquotations, Alectryon, hax), and inline contracts (SPARK, OpenJML, Frama-C, CrossHair) on default-value, constant-convention and tie-break mismatches

## Summary

- **Published drift detectors each cover one narrow comment class. None treats default values, unit or constant conventions, or tie-break order as a category.**
  - iComment covers lock and call rules: 1,832 rules, 60 inconsistencies (33 bugs, 27 bad comments).
  - @tComment covers null behavior: 24 inconsistencies; 27 true vs 29 false-alarm tests.
  - DocRef covers code names in API docs: 3,564 mismatches, 46.4% errors, 40.9% false alarms.
  - Fraco covers identifier renames: precision 100% for fields in 5 of 6 systems.
  - Jdoctor covers `@param`/`@return`/`@throws`: precision 92%, recall 83%. It cannot translate "the sorted array", which needs a loop.
  - Wen et al.'s 25-type inconsistency taxonomy (1.3 billion AST changes, 1,500 systems) contains a "Literal" change class and one replaced-magic-number case. A keyword search found no default-value, precondition or ordering category.
- **Single-source document systems each bind a different pair of artifacts, and all leave free prose unchecked.**
  - Ott generates LaTeX and prover definitions from one grammar and rule source. Its per-target "homs" are copied verbatim, never compared across targets. In our probe, Ott 0.34 accepted a premise rendered as `≤` in LaTeX and Isabelle but as `<` in Coq, reporting "1 good 0 bad".
  - Isabelle antiquotations type-check quoted terms in the theory context, but plain cartouche text is "quasi-formal text (unchecked)".
  - Verso elaborates every `lean` code block at build time. A `leanOutput` block fails the build with "Didn't match" when the recorded message differs from the actual one.
  - Alectryon records prover output. Its caches serve as regression tests, but the author documents a rename that changes output "silently … with no error or warning".
  - hax extracts specifications from Rust, trusting its own frontend and engine (or Charon/Aeneas for Lean). Its documentation states: "The specification is the source of truth and is therefore unverifiable."
- **Inline contracts on the three mismatch classes.** Toy specimens were run on real CrossHair 0.0.113 and 0.0.114, GNATprove 16.1.0 and GNAT run-time assertion checking:
  - **Default value**: invisible to any contract on the function itself. It is caught only by a *caller* contract that states the documented value. CrossHair found a 6-element counterexample; GNATprove found `Len = 11`, result 5; run-time checking failed.
  - **Tie-break order**: caught by both static tools. CrossHair found `[('\x00', 3), ('', 3)]`; GNATprove found `A = ('SOH', 0)`, `B = ('NUL', 0)` and proved the fixed version. CrossHair reported a counterexample against the *fixed* version that does not reproduce when executed: a false alarm, root cause not located.
  - **Half-life written where a decay constant is expected**: CrossHair found `(1.0, 1.0, 1.0)` in 0.25–1.05 s. GNATprove could prove neither the buggy nor the fixed version, because GNAT's `Exp` contract only states `Exp (0.0) = 1.0`. Run-time checking caught the bug on the chosen input.
  - Writing the contracts surfaced two unstated preconditions, `k = -1` and `n0 = +inf`. Doctest examples written in the usual style passed on all three buggy functions.

## Applicability

This report concerns mechanisms that keep **documentation, specifications and executable code in agreement**, and their measured or documented effectiveness. Subjects relate as follows.

- **Comment-drift studies** (iComment, @tComment, DocRef, Fraco, Jdoctor/Toradocu, Wen et al.) supply prevalence, taxonomy and precision/recall. `albertogoffi/toradocu` at `d76899fc65bf0c8912479606d61998d91f30e5bd` was inspected for its output form.
- **Single-source document and extraction tools**:
  - `ott-lang/ott` at `0639ce49892252e0b53e84aa5b0c35b02785913e` was built from source and executed. It reports itself as version 0.34.
  - Inspected only: `leanprover/verso` at `0b8baf4248c351aa5a38929badde9b22ac8cc8af`; `cpitclaudel/alectryon` at `a6f19454a4a8756c51c6c4413544ad09d188e006`; `pereq-dev/hax` at `0d2f66ed697c46d7c0f5038150b7c9679e4d954b` (the former `cryspen/hax` name redirects here); and the Isabelle/Isar Reference Manual dated October 24, 2026.
- **Inline contract checkers**:
  - CrossHair: PyPI `crosshair-tool` 0.0.113, plus the source at `pschanely/CrossHair` `0b39c5bc3b02478f49cbe046df0d09f15101dcf4`, tagged `v0.0.114`, built and executed. All probe outcomes were identical on both versions.
  - GNATprove and GNAT FSF 16.1.0 binary releases (hashes in REPORT.json) were executed. `AdaCore/spark2014` at `80a91869007be9be5a7d5ead3ffccd121faab893` was inspected for documented limitations.
  - OpenJML and Frama-C: documentation and papers only. They were **not executed**.
- **Specimens.** The three mismatch classes are toy specimens written for this report, labelled `toy model` below. Results show what each tool can or cannot detect on that class. They are not prevalence data for real code.

Probe host: x86-64 Linux, Intel Xeon at 2.60 GHz, 96 logical CPUs, shared with other workloads (repeat timings varied up to 3×); Python 3.13; OCaml 5.4.0.

## Findings

### 1. What comment–code drift studies measure

| Study | Comment class | Corpus | Result | Precision / false alarms |
|---|---|---|---|---|
| iComment (SOSP 2007) | Lock and call rules in C comments | Linux, Mozilla, Wine, Apache | 1,832 rules at 90.8–100% extraction accuracy; 60 inconsistencies = 33 bugs + 27 bad comments; 19 confirmed | 38 false positives (talk slides, not the paper body) |
| @tComment (ICST 2012) | Null-related Javadoc | 6 Java projects | 24 inconsistencies (4 fixed: 1 code, 3 comments); 4,672 properties inferred at 94–100% | 27 true vs 29 false-alarm tests (about 48% precision, derived) |
| DocRef (OOPSLA 2013) | Code names and samples in API docs | Lucene, Batik, Hadoop, Uimaj, J2SE | 3,564 mismatches: 882 typos + 773 broken code names = 46.4% errors; 48 fixed within 2 weeks | 40.9% false alarms |
| Fraco (ASE 2017) | Comments made stale by identifier renames | 600 identifiers, 6 systems | "more than half of the total number of identifiers … had fragile comments after renaming" | Fields: precision 100% in 5 of 6 systems, recall above 90%; Eclipse's built-in rename 20–100% / 15–100% |
| Toradocu (ISSTA 2016) | `@throws` only | 9 Guava classes | 34 tags: 25 correct, 4 incomplete, 5 untranslated; "never produced an incorrect oracle" | — |
| Jdoctor (ISSTA 2018) | `@param`, `@return`, `@throws` | 829 comments, 118 classes, 6 projects | P/R 0.96/0.97 (pre), 0.71/0.69 (`@return`), 0.97/0.79 (`@throws`); overall 0.92/0.83 | Baselines: @tComment 0.90/0.24, Toradocu 0.61/0.23 |
| Wen et al. (ICPC 2019) | Any comment change co-occurring with code | 1.3 billion AST changes, 1,500 systems; 500 commits labelled (362 relevant) | 69 change types, 25 relevant; 13–20% of code changes trigger comment updates | — |

Basis: documentation (each paper; iComment from abstract and talk slides only).

**Output forms.** Toradocu/Jdoctor emit "a JSON file containing executable Java expressions" (Jdoctor §6.2). The README at `d76899fc…` says: "All the generated specifications are **executable** and guaranteed to **compile**."

**What these detectors cannot express** (documentation + derived):
- Jdoctor cannot translate "@return the sorted array" ("involves a loop … not supported"), nor multi-element comparisons.
- @tComment handles only null.
- iComment works "topic by topic".

A documented tie-break such as "ties broken by name ascending" is a quantified ordering property over adjacent output pairs. It is therefore outside all three. A documented default ("k defaults to 10") is a property of the signature, not of a method contract, so none of the translators targets it.

### 2. Why the three mismatch classes escape manual maintenance

| Class | Where the truth lives | Why reviewers miss it | Field signal |
|---|---|---|---|
| Default value (doc says 10, signature says 5) | Function signature (a literal) | The doc and the code are in different syntactic places. Callers that omit the argument rely on the doc | Wen et al.: "Literal" changes are among those "less frequently triggering comment updates"; one example left an "old, wrong parameter value" in a comment example after the code was fixed |
| Constant convention (half-life h vs decay constant λ = ln 2 / h) | A formula inside the body | Both are `float`. The wrong formula is plausible and dimensionally identical, since both are 1/time inverses up to ln 2 | One replaced-magic-number refactoring in Wen et al.'s labelled sample (count 1) |
| Tie-break order | Comparator or sort key | Visible only on inputs with equal primary keys. Typical examples use distinct keys, as the doctests here do | No category in the taxonomies examined |

Basis: derived from §1 sources and the §6 specimens.

### 3. Single-source checked documents and extraction: what each binds

| System | Single source binds | Checked mechanically | Residual trust | Escapes |
|---|---|---|---|---|
| Ott | Grammar + inductive rules → LaTeX, Coq, Isabelle, HOL, Lem, OCaml types | Parsing and sort-checking of symbolic terms; naming conventions (JFP §2, §8) | Homs are uninterpreted strings; Ott's generator (about 24,000 lines of OCaml, JFP §6: "one should not treat the tool as part of a trusted chain"); generated prover code must be checked by the prover | Cross-target meaning of homs (probe §4); everything outside the rules |
| Isabelle document antiquotations | Prose ↔ theory context | `@{term t}` "prints a well-typed term"; `@{value t}` "evaluates a term t and prints its result"; `@{lemma φ by m}` proves φ | The prose around antiquotations | "‹foo_bar + baz ≤ bazar› prints literal quasi-formal text (unchecked)" |
| Verso (Lean) | Manual prose ↔ Lean code and messages ↔ docstrings | `lean` code blocks are elaborated in the module context; `leanOutput` compares recorded vs actual messages; missing docstrings error unless `allowMissing` | Free prose; HTML rendering | Prose claims about code that is not embedded |
| Alectryon | Prose ↔ recorded Rocq/Lean goals and messages | Code in blocks "is executed at compilation time"; `massert` checks that references resolve; caches diff output | Cached output when caches are reused; the VsRocq/SerAPI server | The author's own example: renaming `plus` to `Nat.add` plus a compatibility notation changes output "silently … with no error or warning" |
| hax | Rust code ↔ F*/Lean/Rocq/ProVerif model and specifications | Backend prover checks the extracted model | rustc front end; hax frontend and engine (F*), or modified Aeneas (Lean); `hax-lib` macro expansion; models of `core` | The specification itself: "the source of truth and is therefore unverifiable" (hax TCB documentation) |

**Source facts** (basis: source):
- **Ott copies homs verbatim.** `src/grammar_pp.ml` at `0639ce49…` lines 1464–1472:

```ocaml
  | Tex xo ->
      ( match hse with
      | Hom_string s -> s
      ...
  | Coq _ | Twf _ | Caml _ | Lex _ | Menhir _ ->
      ( match hse with
      | Hom_string s -> s
```

- **Verso elaborates `lean` blocks.** `src/verso-manual/VersoManual/InlineLean.lean` at `0b8baf42…` lines 501–506 define `@[code_block] meta def lean`, which calls `elabCommands config str toHighlightedLeanBlock`.
- **Verso fails on mismatched messages.** Line 756 of the same file fails the build when an expected-output block disagrees:
  `throwErrorAt str (m!"Didn't match{…} - got: {…}\nbut expected:{…}" ++ hint)`.
- **Alectryon's output assertions.** `README.rst` at `a6f19454…` line 640: "Alectryon's marker-placement mini-language can serve as a poor lad's unit test. The ``massert`` directive … checks that each line of its body is a valid reference to part of a previous goal."
- **hax backends.** `README.md` at `0d2f66ed…` lines 121–124: the Lean backend "Uses Charon + Aeneas" and is "Recommended for Lean". F* is "Stable"; Rocq/Coq is "Experimental".

### 4. Ott probe: one source, divergent meanings, accepted

`toy model` on the real tool. Input `decay.ott` (SHA-256 `1cf960ddbfde1b7ba8a86da5db9f5c8186b391f6666055998f38c2b16ccc8c77`):

```text
metavar k ::= {{ com natural number }} {{ coq nat }} {{ isa nat }} {{ ocaml int }} {{ lex numeral }} {{ tex [[k]] }}
grammar
formula :: 'formula_' ::=
  | judgement :: :: judgement
  | k1 <= k2 :: M :: le {{ tex [[k1]] \le [[k2]] }} {{ coq ([[k1]] < [[k2]]) }} {{ isa [[k1]] \<le> [[k2]] }}
terminals :: 'terminals_' ::=
  | <= :: :: le {{ tex \le }}
defns
Jdecay :: '' ::=
defn
k1 decays_before k2 :: :: decays :: D_ {{ com decay ordering }} by
  k1 <= k2
  ------------------- :: before
  k1 decays_before k2
```

Command: `ott -i decay.ott -o decay.tex -o decay.v -o decay.thy`. Output: "Definition rules: 1 good 0 bad". 0.00 s wall, 18 MB peak RSS. Generated artifacts:

```text
decay.v   : | D_before : forall (k1 k2:k), ( k1  <  k2 )  -> decays k1 k2.
decay.thy : D_beforeI: "\<lbrakk> k1  \<le>  k2 \<rbrakk> \<Longrightarrow> decays k1 k2"   (as printed, modulo spacing)
decay.tex : \ottpremise{ k_{{\mathrm{1}}}  \le  k_{{\mathrm{2}}} }%
```

- The typeset rule and the Isabelle relation say ≤; the Coq relation says <. A reader of the PDF has no signal.
- **Ill-formed generated code is also accepted.** An earlier variant that used an `indexvar` in the judgement produced Coq with free variables, `Inductive decays : Prop := | D_before : ( n1 < n2 ) -> decays`, and Ott still reported success. Ott's checks do not include well-formedness of generated prover code.
- No Coq or Isabelle installation was available to confirm the prover-side errors (see **Boundaries**).

Basis: execution + source.

### 5. Inline contracts and symbolic checkers on the three classes

`toy model` specimens (abridged; full text in **Evidence**). Results:

| Specimen | CrossHair 0.0.113 and 0.0.114 (PEP 316, `--per_condition_timeout=20`) | GNATprove 16.1.0 (`--level=2 --counterexamples=on`, `-j1`) | GNAT run-time checks (`-gnata`) | Doctest |
|---|---|---|---|---|
| Default: `top_k(xs, k=5)` documented "default k = 10"; caller contract `len(result) == min(len(xs), 10)` | **Counterexample**: `summarize_buggy([28962, 28963, -47926, -47925, -47926, -47926])` returned 5 items | **"high: postcondition might fail … e.g. when Len = 11 and Summarize'Result = 5"** | Postcondition failed (`Summarize (12)`) | Passed (example passes `k` explicitly) |
| Default, function-local contract only: `post: len(__return__) == min(len(xs), k)` | Did not flag the default. Flagged `top_k([], k=-1)` (unstated `k ≥ 0`) | Not applicable (the default is not visible to the contract) | — | — |
| Constant convention: `n0 * exp(-half_life * t)`; post: at `t == half_life` the result is `n0/2` | **Counterexample** `remaining_buggy(1.0, 1.0, 1.0)` → 0.3679 | **Unproved** ("medium: … cannot prove"), and equally unproved for the **fixed** formula | Postcondition failed at `(1.0, 2.0, 2.0)`; the fixed version returned 0.5 | Passed (example uses t = 0) |
| Constant convention, fixed formula | Counterexample `n0 = float("inf")`: an unstated finiteness precondition, not a formula error | Unproved | Passed | — |
| Tie-break: documented "score desc, name asc"; buggy sorts by score only | **Counterexample** `rank_buggy([('\x00', 3), ('', 3)])` | **"high: postcondition might fail … e.g. when A = (N => 'SOH', S => 0) and B = (N => 'NUL', S => 0)"** | Postcondition failed (`('b',3)`, `('a',3)`) | Passed (example scores distinct) |
| Tie-break, fixed | **Reported counterexample that does not reproduce** (§6) | **Proved** | — | — |

Basis: execution.

**Why GNATprove cannot discriminate the constant-convention pair.**
- GNAT's elementary-function contract gives the provers almost nothing to work with. From `a-ngelfu.ads` in the GNAT 16.1.0 release (`lib/gcc/x86_64-pc-linux-gnu/16.1.0/adainclude/a-ngelfu.ads`, lines 87–89):

```ada
   function Exp (X : Float_Type'Base) return Float_Type'Base with
     Global => null,
     Post   => (if X = 0.0 then Exp'Result = 1.0);
```

- The SPARK User's Guide at `80a91869…` (`docs/ug/en/source/how_to_investigate_unproved_checks.rst`, lines 83–89) lists "Floating point elementary operations, such as square root or trigonometric functions" among features that "may yield checks that should be true, but cannot be proved".
- Static proof is therefore **complete for the integer and enumeration classes** (default and tie-break), but **silent on transcendental constant conventions**. Those need run-time checking or a test at a pinned input.

Basis: source + execution.

**GNATprove summary** (`obj/gnatprove/gnatprove.out`, identical in both runs): 26 checks; 5 discharged by flow analysis (termination); 13 proved by provers (12 run-time checks, split CVC5 58% / trivial 42%, plus 1 functional contract by CVC5); 8 unproved. The unproved checks are 4 functional contracts and 4 float/overflow run-time checks. "max steps used for successful proof: 7012".

### 6. Observed CrossHair false alarm on string ordering

- Both CrossHair 0.0.113 (PyPI) and the pinned source revision 0b39c5bc (v0.0.114) report:

```text
str_min.py:14: error: false when calling le_sorted_names(['\x00\x00\x00', '\x00\x00\x00', '\x00\x00\x00\x00\x00\x00'])
  (which returns ['\x00\x00\x00', '\x00\x00\x00', '\x00\x00\x00\x00\x00\x00'])
```

  The specimen is `def le_sorted_names(xs: List[str]) -> List[str]`, with docstring `post: all(x <= y for x, y in zip(__return__, __return__[1:]))` and body `return sorted(xs)`.
- Executing the printed input in CPython returns a sorted list, and the postcondition evaluates to `True`. The same happens for `rank_fixed([('\x02\x00', 3), ('\x02\x00\x00\x00', 3)])`, reported 3 of 3 times.
- Two related checks report nothing:
  - `a <= b` with `a` a strict prefix of `b`;
  - `sorted(xs, key=lambda p: p[1])` with a post on `x[1] <= y[1]`.
- We only observed that the reported counterexample does not reproduce. The defect location in CrossHair was **not identified**, so this is not a claim about any specific source line.
- The documentation says "the absence of a counterexample does not guarantee that the property holds". This observation is the converse case: a reported counterexample that is not one.

Basis: execution.

### 7. Trusted base, annotation overhead, and completeness limits

| Tool | What the user writes | Trusted base (documented) | Completeness / soundness statement |
|---|---|---|---|
| SPARK / GNATprove | `Pre`/`Post` aspects. Here 1 line per subprogram (2 for `Remaining`), plus a 2-line expression function `Before` | GNAT front end (gnat2why), Why3, provers (Alt-Ergo 2.6.1, CVC5 1.3.2, Z3 4.15.4 in this release), and runtime-library contracts such as `Exp` | Counterexamples "do not always correspond to a feasible execution" (UG `how_to_view_gnatprove_output.rst` line 400); elementary float functions are imprecisely modelled |
| OpenJML | JML in comments: ESC plus a RAC compiler | SMT solver and the JDK specs; unspecified library methods "are by necessity (for soundness) presumed to be …" | "manual review that the formally stated specifications are complete and match informal or natural language requirements is also necessary" (User Guide §1.2) |
| Frama-C / ACSL | ACSL annotations; WP or Value; E-ACSL for run-time checks | Kernel and plug-ins | Value is sound by over-approximation, with "false alarms"; E-ACSL "only excludes parts of ACSL which are not computable in finite time" |
| CrossHair | PEP 316 docstring lines, `assert`s, icontract or deal | CPython plus proxy patches, Z3 | "cannot generally prove that properties hold"; "the illusion is not complete"; per-path and per-condition CPU timeouts |
| Doctest | Example calls with outputs | CPython | Checks only the written examples |

**CrossHair's docstring-contract parser.** In CrossHair only lines matching one regex become contracts; all other docstring prose is ignored. `crosshair/condition_parser.py` at `0b39c5bc…` lines 353–361:

```python
_HEADER_LINE = re.compile(
    r"""^(\s*)\:?  # whitespace with optional leading colon
         ((?:post)|(?:pre)|(?:raises)|(?:inv))  # noncapturing keywords
         (?:\[([\w\s\,\.]*)\])?  # optional params in square brackets
         \:\:?\s*  # single or double colons
         (.*?)  # The (non-greedy) content
         \s*$""",
    re.VERBOSE,
)
```

The sentence "default k = 10" in the same docstring therefore has no formal effect. Basis: source.

### 8. Performance and resource footprint across levels

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | Contract lines added per specimen | 1–2 PEP 316 lines (CrossHair); 1–2 aspect lines (SPARK) | execution (counted) |
| L1 | Jdoctor translation quality (substitute for writing specs by hand) | P 0.92 / R 0.83 overall | documentation |
| L1 | LLM token or turn budgets for spec writing | not measured | — |
| L2 toolchain build | Ott from source (`make world`) | 5.83 s wall, 81 MB peak RSS; 8,938,384-byte native binary | execution |
| L2 | CrossHair from source (`pip install` of the 0b39c5bc tarball) | not measured (not timed) | — |
| L2 | GNATprove, OpenJML or Frama-C from source | not measured (binary release used, or not executed) | — |
| L3 checking latency | CrossHair per function, wall time | 0.23–1.05 s for found counterexamples; 2.2–11.8 s for the string-ordering cases | execution |
| L3 | GNATprove, 6 subprograms, `--level=2 -j1` | 102.28 s wall | execution |
| L3 | Ott generation for the probe | 0.00 s wall (below timer resolution) | execution |
| L3 | GNAT build of the run-time-check harness (`gnatmake -gnata`) | 0.68 s | execution |
| L3 | Editor/LSP responsiveness under 50 ms (Verso, Isabelle/jEdit) | not measured | — |
| L4 generated code | Run-time cost of `-gnata` or E-ACSL checks | not measured | — |
| L5 proof checking | Rechecking Verso/Alectryon documents; prover replay of Ott output | not measured | — |
| L6 footprint | Peak RSS: CrossHair | 65–76 MB | execution |
| L6 | Peak RSS: GNATprove (largest process in tree) | 134 MB | execution |
| L6 | Release archives | GNATprove 472,919,963 B; GNAT 402,244,219 B | execution (GitHub release metadata) |
| L6 | Alectryon cache size | `List.v.cache` 3.2M → 66K compressed; `Ranalysis3.v.cache` 21M → 25K compressed (README "Typical results") | documentation |

### 9. Comprehensibility and conceptual simplicity

- **C1, local vs nonlocal reasoning.**
  - A default-value mismatch is nonlocal: the doc sentence, the signature literal and every omitting call site.
  - A tie-break is conditional on equal keys.
  - A constant convention is semantic, since the types are identical.

  Human review of any single location sees nothing wrong. Every successful detection in §5 came from writing the documented claim as an executable condition in the place where its consequence is observable: the caller for defaults, adjacent output pairs for tie-breaks, a pinned input for the half-life.
- **C1, diagnostics.** GNATprove's counterexamples for the tie-break and default classes were directly legible (`Len = 11`, result 5; two equal scores with names out of order). CrossHair's non-reproducing counterexample (§6) is the opposite: a diagnostic a human must disprove.
- **C2, one invariant with many mechanisms.** "Rendered claim = checked artifact" is implemented separately as:
  - Ott homs (unchecked);
  - Isabelle antiquotations (checked terms, unchecked prose);
  - Verso blocks (checked code and messages);
  - Alectryon caches (diffable output);
  - hax extraction (trusted translation);
  - Jdoctor JSON (translated prose).

  The minimal universal abstraction is a **quotation obligation**: every rendered formal or numeric claim must be a reference to a checked entity, or an evaluated expression, never free text. Isabelle's `@{value}` and Verso's `leanOutput` already realize it for terms and messages. Extending it to defaults means rendering `inspect.signature(f).parameters['k'].default`, or Ada's default expression, *from* the code rather than restating it. That makes the default-value class unrepresentable instead of detectable.
  - It does not cover hom-style cross-target meaning (Ott), where two targets are each checked but never against each other.

### 10. Validation of the mechanisms themselves

- **V1, adequacy.** Writing contracts surfaced two unstated preconditions (`k ≥ 0`, finite `n0`). A contract is itself a specification that needs non-vacuity and adequacy checks. Jdoctor found "many developer-written specifications were logically inconsistent", for example a `@param … must not be null` alongside `@throws NullPointerException if a is null`.
- **V2, checker soundness.** Two checks are cheap:
  - replay every reported counterexample concretely (that is how §6 was found);
  - run each mechanism on a seeded-buggy and a fixed twin, as in §5.

  GNATprove's UG warns that counterexamples may be infeasible when `--check-counterexamples=off`. That flag was not set here.
- **V3, concurrency, crash and leakage.** Not examined.
- **V4, human comprehension.** No study was found that measures whether readers detect default, constant or tie-break drift faster with single-source documents than with conventional ones (**unknown**).

## Boundaries

- **not examined (full text)**:
  - the iComment paper body (abstract and talk slides only; the false-positive count of 38 is from the slides);
  - the Alectryon SLE 2020 paper (author's blog post and README used instead; no overhead numbers);
  - the hax VSTTE 2024 paper body (ePrint abstract plus current TCB documentation, which may differ from the paper's architecture);
  - the OpenJML NFM 2011 paper (User Guide pages 1–92 only; its §14.1 "Soundness and Completeness" not read).
- **not examined (execution)**: OpenJML, Frama-C/WP/E-ACSL, Isabelle, Verso, Alectryon and hax were not run. Coq/Isabelle compilation of Ott's output was not performed, so the claim that the free-variable variant would be rejected by Coq is **unknown** here.
- **unknown**: the root cause of CrossHair's non-reproducing counterexamples (§6), and whether they occur outside strings containing NUL characters.
- **unknown**: prevalence of default-value, constant-convention and tie-break mismatches in real code. The taxonomies examined have no such categories, and keyword searches of Wen et al. found none.
- **unsupported by the cited detectors**: quantified or ordering properties (Jdoctor), non-null properties (@tComment), and topics other than locks and calls (iComment).
- **toy model**: every specimen (`drift_probe.py`, `str_min.py`, `drift.ads`/`drift.adb`, `decay.ott`). Timings are properties of these specimens on the stated host.
- **not measured**: L4 run-time overhead of assertion checking; L5 document recheck time; LSP latency; energy; LLM-assisted authoring cost.
- **attractive but unestablished**:
  - "single-source documents eliminate drift": they eliminate drift only for quoted formal entities;
  - "static contract proof catches all three classes": it did not for the transcendental case.
- **identifier corrections** (verified against Crossref): DocRef is DOI 10.1145/2509136.2509523; Fraco is 10.1109/ASE.2017.8115624; the SPARK book by McCormick and Chapin is 10.1017/CBO9781139629294; Wenzel's EPTCS 167 paper (10.4204/EPTCS.167.10) is titled "System description: Isabelle/jEdit in 2014".

## Evidence

All execution and source observations were made on 2026-11-20 (UTC).

**CrossHair specimens** (`drift_probe.py`, SHA-256 `b1044aca86476f265276667dddea57573ee7ce095aa6ec7cd5ab58ccc04f0895`; `str_min.py`, SHA-256 `de796c4ae61ca0ae223598bd97ffdc1fca98c6eab8e35f9904ad0620d1f07e6a`), abridged:

```python
def top_k(xs: List[int], k: int = 5) -> List[int]:
    """Return the k largest items, largest first (default k = 10).

    >>> top_k([3, 1, 2], 2)
    [3, 2]

    post: len(__return__) == min(len(xs), k)
    """
    return sorted(xs, reverse=True)[:k]

def summarize_buggy(xs: List[int]) -> List[int]:
    """post: len(__return__) == min(len(xs), 10)"""
    return top_k(xs)

def remaining_buggy(n0: float, t: float, half_life: float) -> float:
    """pre: n0 > 0 and half_life > 0 and t >= 0
    post: t != half_life or abs(__return__ - n0 / 2) <= 1e-9 * n0"""
    return n0 * math.exp(-half_life * t)            # fixed: math.exp(-math.log(2) * t / half_life)

def rank_buggy(players: List[Tuple[str, int]]) -> List[Tuple[str, int]]:
    """post: all(a[1] > b[1] or (a[1] == b[1] and a[0] <= b[0]) for a, b in zip(__return__, __return__[1:]))"""
    return sorted(players, key=lambda p: -p[1])     # fixed: key=lambda p: (-p[1], p[0])
```

- Commands: `crosshair check --analysis_kind=PEP316 --per_condition_timeout=20 drift_probe.<fn>` and `python -m doctest -v drift_probe.py` (result: "3 passed").
- v0.0.114 was installed with `pip install "crosshair-tool @ https://github.com/pschanely/CrossHair/archive/0b39c5bc3b02478f49cbe046df0d09f15101dcf4.tar.gz"`. pip recorded the archive hash `sha256=174c44f5e98c4fef462b590ebdb35872a911fd6a88e85e8110b7bd55d02d3409`.
- Tags: `v0.0.114` is commit 0b39c5bc…; `v0.0.113` is 41 commits behind it.

**SPARK specimen** (`drift.ads`, abridged):

```ada
   function Before (A, B : Player) return Boolean is
     (A.S > B.S or else (A.S = B.S and then A.N <= B.N));
   procedure Order_Pair_Buggy (A, B : in out Player) with Post => Before (A, B);
     --  body: if B.S > A.S then swap
   procedure Order_Pair_Fixed (A, B : in out Player) with Post => Before (A, B);
     --  body: if not Before (A, B) then swap
   function Take (Len : Natural; K : Natural := 5) return Natural is (Natural'Min (Len, K));
   function Summarize (Len : Natural) return Natural with
     Post => Summarize'Result = Natural'Min (Len, 10);            --  body: Take (Len)
   function Remaining_Buggy (N0, T, Half_Life : Float) return Float with
     Pre  => N0 in 1.0 .. 1.0e6 and T in 0.0 .. 1.0e3 and Half_Life in 1.0e-3 .. 1.0e3,
     Post => (if T = Half_Life then abs (Remaining_Buggy'Result - N0 / 2.0) <= 1.0e-3 * N0);
     --  body: N0 * Exp (-Half_Life * T); fixed body: N0 * Exp (-0.693_147_18 * T / Half_Life)
```

- Prover command: `gnatprove -P drift.gpr -j1 --level=2 --counterexamples=on --report=fail` (after `--clean`). Result: "wall=102.28s maxrss=134264KB".
- Version banner: "FSF 16.1.0", "Why3 for gnatprove version 1.8.2+git", "Alt-Ergo version 2.6.1", "cvc5 version 1.3.2", "Z3 version 4.15.4".
- Run-time harness: `gnatmake -q -gnata -gnat2022 -I../src ../src/main.adb`, then `./main`. Output:

```text
fixed half-life ok: 5.00000E-01
buggy half-life: postcondition failed at run time
buggy tie-break: postcondition failed at run time
buggy default: postcondition failed at run time
```

- Release archives were checked against their published `.sha256` files: they matched.

**Ott**:
- Build: `make world` from the tarball of `0639ce49892252e0b53e84aa5b0c35b02785913e`, with the `ocamlfind` and `ocamlgraph` packages from opam, OCaml 5.4.0. Result: `wall=5.83s maxrss=81424KB`.
- Version banner: "Ott version 0.34 distribution of Mon Dec 30 10:12:45 GMT 2024". The banner is the in-tree version string; the build is the pinned commit.

**Verso, Isabelle, Alectryon, hax, SPARK UG, CrossHair parser**: file paths and line numbers are given inline in §§3, 5 and 7. The Isabelle quotes are from §4.2 of the manual dated October 24, 2026.

**Literature** (DOIs verified against Crossref metadata on the observation date):
- Tan et al., iComment, SOSP 2007, DOI 10.1145/1294261.1294276.
- Tan et al., @tComment, ICST 2012, DOI 10.1109/ICST.2012.106.
- Zhong & Su, OOPSLA 2013, DOI 10.1145/2509136.2509523.
- Ratol & Robillard, ASE 2017, DOI 10.1109/ASE.2017.8115624.
- Goffi et al., Toradocu, ISSTA 2016, DOI 10.1145/2931037.2931061.
- Blasi et al., Jdoctor, ISSTA 2018, DOI 10.1145/3213846.3213872.
- Wen et al., ICPC 2019, DOI 10.1109/ICPC.2019.00019.
- Sewell et al., Ott, JFP 20(1):71–122, DOI 10.1017/S0956796809990293.
- Pit-Claudel, SLE 2020, DOI 10.1145/3426425.3426940.
- Bhargavan et al., hax, VSTTE 2024 (LNCS 2025), DOI 10.1007/978-3-031-86695-1_7; IACR ePrint 2025/142.
- Cok, OpenJML, NFM 2011, DOI 10.1007/978-3-642-20398-5_35.
- Kirchner et al., Frama-C, FAC 27(3):573–609, DOI 10.1007/s00165-014-0326-7.
- McCormick & Chapin, *Building High Integrity Applications with SPARK*, DOI 10.1017/CBO9781139629294.

## Revalidation

- **Ott hom divergence**: run `ott -i decay.ott -o decay.v -o decay.tex` with a newer Ott. If Ott ever begins cross-checking homs, the run will stop reporting "1 good 0 bad". Otherwise, grep `src/grammar_pp.ml` for `Hom_string s -> s` in the `Tex` and `Coq` branches.
- **Verso**: confirm that `InlineLean.lean` still defines `@[code_block] meta def lean` with `elabCommands`, and that `leanOutput` still throws "Didn't match".
- **CrossHair false alarm**:
  1. Run `crosshair check --analysis_kind=PEP316 str_min.le_sorted_names`.
  2. If it reports a counterexample, execute the printed input concretely.
  3. A fix shows up as no report, or as a report that reproduces.
- **GNATprove on constant conventions**:
  1. Rerun the SPARK specimen with a newer release.
  2. Check `a-ngelfu.ads` for a stronger `Exp` postcondition.
  3. Discrimination appears only if `Remaining_Fixed` becomes proved while `Remaining_Buggy` stays unproved.
- **Taxonomy gap**: search new code–comment inconsistency studies for "default value", "unit" or "tie" categories. Any such category supersedes the **unknown** prevalence entry.
