# Non-Quorum Kernel Confidence: Proof Export and Down-Translation, Guard Mutation, Normalization Smoke Tests, Finite-Model Rule Checks, and Result Checking

## Summary

Re-checking a proof with a second trusted checker ("quorum") is one way to gain confidence in a proof checker. This report evaluates five other ways against real systems and documented bugs, and keeps published evidence apart from two new experiments run here on a real Metamath verifier and from small toy models.

1. **Export and down-translation** (large checker or solver emits a certificate that a smaller or different checker re-validates) is the only technique with broad deployment: Lean's NDJSON export with 37 registered checkers (the official kernel among them), DRAT→LRAT with verified checkers for SAT, CPC/Alethe certificates for SMT, Metamath and Metamath Zero. It catches implementation bugs of the producer on the exported instances and kernel bypasses. It misses errors in the logic itself, assumptions baked into the format or prelude, and it fails whenever the small checker *trusts a derived field of the certificate* — a documented, recurring bug class.
2. **Guard mutation** (disable each check; does a known-false statement get in?) measures whether a negative test suite is adequate, cheaply. New experiment: of 36 guard-disabling mutants of `mmverify.py`, the upstream negative tests expose 2; ten crafted exploits expose 6, three more turn into uncaught exceptions, and 27 change nothing observable. It cannot see a guard that was never written: the same verifier has an open upstream soundness bug of exactly that kind, reproduced here.
3. **Normalization / canonicity of closed terms** is a real consistency argument on paper (MetaRocq proves canonicity and "Consistency under the assumption of strong normalization") but a weak test in practice: Lean's reduction is known not to terminate, axioms produce stuck terms, and the evaluator is usually the kernel's own. No routine deployment was found.
4. **Finite-model checks of individual rules** find wrong rule instances with tiny, legible countermodels (toy model here: a capturing substitution is refuted on a 2-element domain; published: Alive found incorrect LLVM peephole rules) but are blind to rules valid in every finite model and to all implementation slips.
5. **Result checking** in the Blum–Kannan sense is what a kernel already is for proof search; the kernel's own one-bit verdict has no smaller certificate unless it emits a trace (LRAT hints are exactly such a trace). Against hardware faults, published fleet data (mis-computing "mercurial" cores) says a single run can be silently wrong; the remedy is re-execution on different hardware plus pinning of the *statement*. New experiment: of 10,824 single-bit corruptions of a Metamath database, 55.9% are rejected, 42.4% are comment or whitespace changes, and 1.64% are accepted with changed content — including one flip that turns an axiom into an unsound one while every proof still checks.

## Applicability

The subjects in `REPORT.json` fall into four groups.

- **Certificate pipelines examined at pinned revisions**: Lean's `lean4export` format, the same-kernel replayer `lean4checker`, the statement-pinning judge `comparator`, the independent kernels nanoda, Lean4Lean and con-leche, the Lean Kernel Arena (registry, tests, and its published `results.json`), `lean2dk`; DRAT-trim/`lrat-check` and `cake_lpr`; cvc5's proof documentation with the checkers Carcara and Ethos; Metamath Zero. Lean 4, Rocq and MetaRocq appear for their kernel sources, bug records and metatheory statements.
- **Subjects of the new experiments**: `mmverify.py` and the `metamath-test` suite, both executed unmodified at the pinned revisions with Python 3.13.15 on Linux x86-64. The mutation harness, ten crafted negative databases and the bit-flip driver are this report's own and are reproduced in full under Evidence.
- **Literature**: Blum and Kannan (result checking), Hochschild et al. and Dixit et al. (silent hardware corruption), the LRAT and Boolean-Pythagorean-triples papers, the operator-mutation SMT fuzzing paper, the Metamath Zero and Lean4Lean papers, Alive, and Abel–Coquand.
- **A toy model** (one short Python program) illustrates technique 4 and nothing else; it characterizes no real system.

Findings about Lean, SAT and SMT tooling are from documentation, source and upstream-published measurements; none of those tools was built or run here. Findings about `mmverify.py` are from execution and apply to that revision only: other Metamath verifiers were not run, so no claim is made about them. Issue and pull-request texts are mutable and were read on the observation date.

## Findings

### 1. What each technique substitutes for a second trusted checker

| Technique | Where the confidence comes from | Unit of evidence |
|---|---|---|
| Quorum (baseline) | agreement of independently written peers | one verdict per peer per artifact |
| 1 Export / down-translation | asymmetry: the validator is smaller, simpler, verified, or at least different | a certificate re-derivable without the producer |
| 2 Guard mutation | necessity: each check is shown to be the only thing standing between a known-false statement and acceptance | one witness file per guard |
| 3 Normalization / canonicity | a semantic invariant of the logic that a false theorem would violate | a normal form |
| 4 Finite-model rule check | per-rule semantics | a countermodel, or exhaustion up to a bound |
| 5 Result checking / integrity | redundancy in the computation, not in the reasoning | a trace, a repeat run, a hash |

Basis: derived (classification).

### 2. Technique 1 — proof export and down-translation

**Pattern and its four invariants.**

```text
producer P (large, untrusted)  ──certificate c──▶  validator K (small or different)  ──▶ accept / reject
wanted:    K(c, s) = accept  ⟹  statement s holds
trusted:   K, the semantics of the certificate format, the statement s, and K's compiler/runtime/hardware

(I1) s is fixed independently of P (P cannot restate the theorem).
(I2) K recomputes every datum in c that is derivable; it never believes P's copy.
(I3) the certificate format has one meaning (no producer/validator disagreement about semantics).
(I4) K parses c from scratch in a format it validates (no memory-mapped producer data structures).
```

Each documented failure of the pattern below is a violation of one of I1–I4. Basis: derived, from the cases cited in this section.

**Deployed pipelines.**

| Domain | Producer → certificate → validator | Published evidence of scale | Trusted after the hop |
|---|---|---|---|
| Lean 4 | kernel/elaborator → `lean4export` NDJSON ("Lean 4 export format: version 3.1.0") → `leanchecker --from-export` (official kernel), nanoda (Rust), Lean4Lean, con-leche, and others | Arena: 37 registered checkers; the Mathlib export is 5.9 GB / 112.1 M lines; 20 checkers accept it; official kernel 2,696 s wall and 9.91 GiB, nanoda 442 s wall (1,475 s CPU) and 5.95 GiB, con-leche 206 s wall (801 s CPU) and 4.83 GiB | validator, export tool, prelude assumption, statement |
| Lean 4 → Dedukti | `lean2dk` → Dedukti | README: "still a work-in-progress"; best branch "translates and type-checks `Init.Data.Nat.Lemmas` end-to-end against a patched Dedukti kernel" | translator's encoding, patched Dedukti |
| SAT | solver → DRAT → DRAT-trim → LRAT → verified checker (`cake_lpr`; ACL2; Coq) | Boolean Pythagorean triples: a DRAT proof "almost 200 terabytes in size", "a compressed certificate of 68 gigabytes", "approximately 4 CPU years" of solving; LRAT paper: a Coq-certified checker verified the transformation proof "in 8 minutes and 25 seconds", and the ACL2 checker is "almost as fast as —and in some cases even faster than— non-certified checking by DRAT-trim" | verified LRAT checker and its formula parser |
| SMT | cvc5 → CPC → Ethos; cvc5/veriT → Alethe → Carcara, Isabelle/HOL reconstruction, SMTCoq | cvc5 docs: Alethe output covers "equality with uninterpreted functions, linear arithmetic, bit-vectors and parts of the theory of strings" | the rule signature (`Cpc.eo`) or the Alethe rule semantics in the checker |
| Metamath | any tool → `.mm` → many verifiers | `metamath-test` drives six independent verifiers (C, Haskell, Rust, C++, Java, Python); `mmverify.py` is 708 lines | one verifier, the axioms in the file |
| Metamath Zero | `mm0-rs` → `.mm0` spec + `.mmb` proof → `mm0-c` | Paper: "fastest verification of the `set.mm` Metamath library … at less than 200 ms"; README: `mm0-c` "is under 3,000 lines of C" (1,388 lines in its four `.c` files) | `mm0-c`, the `.mm0` statement file |

Basis: documentation + source (line counts measured on the pinned trees) + execution by upstream (arena `results.json`).

A size comparison corrects a common assumption: Lean's C++ kernel is 7,868 lines in 34 files under `src/kernel`, while nanoda's `src/` holds 9,524 non-blank lines of Rust (tests included). For Lean the export hop buys **independence and format isolation, not a smaller validator**; only Metamath Zero and the LRAT checkers are "much smaller" in the literal sense. Basis: source.

**Why certificates are wanted at all (SMT).** One year of operator-mutation fuzzing of Z3 and CVC4 produced "1,092 bugs … out of which 819 unique bugs were confirmed and 685 of the confirmed bugs were fixed", among them "184 soundness bugs". Basis: documentation (Winterer, Zhang, Su 2020).

**Bug classes it catches (published).**

- *Implementation bugs of the producer's kernel, on exported instances.* Lean pull request 14613 (a type in `Sort (imax 1 0)` not recognized as a proposition): "nanoda rejects it". Lean pull request 14806 (order-dependent definitional-equality cache): "Both exploits are also caught by nanoda, and both are caught by the new lean-inductive-models".
- *Kernel bypass and corrupted environment state.* Lean manual, on the export-based judge: "tricks like injecting theorems without passing them by the kernel are caught"; on same-kernel replay: it protects against "Bugs in Lean's core handling of the kernel's state (e.g. due to parallel proof processing, or import handling)" and "Meta-programs or tactics intentionally bypassing that state".

Basis: documentation.

**Bug classes it misses, each with a documented instance.**

| Violated invariant | Instance | Record |
|---|---|---|
| I2 — validator believes a derived field | The export "contains information that is redundant and would likely be ignored or only validated by a full external checker (such as the types of recursors)"; the kernel "derives the recursors, and informational fields like `isRec`, `isReflexive` or `cidx`. The export format includes the data of these generated declarations for convenience." Arena tests `bugs/ctor-num-fields` ("Proof of False via trusted `numFields` on a constructor") and `bugs/rec-k-lie` ("False theorem via trusted `k` on a recursor"): "Nanoda and its descendants accepted this until it was fixed"; `bugs/nat-rec-rules` and `bugs/nested-rec-rule-nfields` record the same class for recursor rules. Rule from `bugs/rec-rule-wrong-arg`: "A checker must derive the rule itself and reject an export whose rule differs from it, as the official kernel does". | lean4export `format_ndjson.md`; arena `tests/bugs/*.yaml` |
| I4 — validator maps the producer's data structures | Lean manual: `lean4checker` "trusts that the .olean files are structurally correct" and is "prone to an attacker crafting invalid .olean files (e.g. invalid pointers, invalid data in strings)". Lean issue 15100 (a forged `.olean` constructor entry accepted by `leanchecker`) was closed by its reporter because "the supported untrusted-code path … exports via NDJSON and runs leanchecker --from-export. This construction is rejected there"; its sibling 15101 (arbitrary quotient entries) notes that "The `--from-export` path has a separate post-check … but the ordinary `.olean` path does not". Rocq: "deserialization of .vo data not properly checked" (8.10–8.18.1) and "rocqchk trusts the serialized VM bytecode segment" (8.20–9.3). | Lean manual; Lean issues; Rocq `critical-bugs.md` |
| I3 — format semantics differ | "DRAT-trim ignores deletion steps of unit clauses by design. … Notice that ignoring deletion steps of unit clauses can turn a valid DRAT proof into an invalid one --- and the other way around." cvc5: CPC "treats certain operators differently from the SMT-LIB standard." | DRAT-trim `README.md`; cvc5 `docs/proofs/output_cpc.rst` |
| I1 — statement not pinned | The judge exists because of this: it checks that "The theorem statements of the challenge and solution match exactly, including all transitively used definitions." | Lean manual |
| Shared assumption in every validator | An export that redefines `Nat.add` proves `False` in the official kernel (Lean issue 15908, closed as not a kernel bug: the guide says "keep the declarations of the official prelude as they are"); the judge rejects it with "Const does not match between challenge and target 'Nat.add'". | Lean issue 15908 |
| Common-mode bug | Lean pull request 14807: "The bogus proof was also accepted by nanoda, an independent implementation of the Lean kernel." | pull-request text |
| The validator is itself buggy | Arena results: 9 of 37 checkers accept at least one of the 90 must-reject exports (37 wrong acceptances in 9,805 results); 15 of the 90 are accepted by some checker. `mmverify.py` accepts a false proof (Section 3). | arena `results.json`; execution |
| Rules never checked for soundness | Ethos "checks that each step follows the supplied rules; it does not prove that those rules are sound." | Ethos `README.md` |
| Coverage gaps | `lean2dk` (one library file); Alethe theories (above); Lean4Lean at the arena's pinned build rejects 22 of 145 valid tests including Mathlib. | READMEs; arena results |

Basis: documentation + source + execution by upstream.

The first row is the trap specific to *down*-translation: making a certificate convenient for tools (pre-computed recursors, field counts, flags) hands the small validator data it is tempted to believe. A format that omitted derivable data, or marked it as untrusted hints in the way LRAT marks its propagation hints, would make I2 structural rather than a discipline. Basis: derived.

### 3. Technique 2 — mutation testing of the checker's own guards

**Method.** A *guard* is a check whose failure makes the checker reject. For each guard build a mutant in which it can never fire, then run negative inputs (which a sound checker must reject) and positive inputs. A mutant is *exposed* when it accepts a negative input the original rejects; an exposed guard is thereby shown to be load-bearing, and the input is its witness. Guards whose mutants are never exposed are either redundant, crash-masked, or — the interesting case — soundness-critical but untested.

**New experiment (real verifier, real upstream tests, crafted additional inputs).** Subject: `mmverify.py` at the pinned revision, which contains 36 `raise MMError(...)` sites. Operator: if the `raise` is the sole statement of an `if` body the condition is forced to `False`; if it is the sole statement of an `else` branch the condition is forced to `True` (32 and 4 sites respectively). Inputs: the 8 must-fail and 8 small must-pass databases of `metamath-test`, plus 10 crafted must-fail databases and 1 must-pass database over a toy two-sorted axiom system in which `|- F` is underivable (the system has a model, described in the file header). Each crafted negative ends in a theorem `bad $p |- F` whose proof violates exactly one rule. Basis for everything in this subsection: execution (real upstream system; crafted inputs and harness are this report's).

| Guard (upstream line, message) | Kind | Upstream negatives | Crafted negatives | Outcome |
|---|---|---|---|---|
| 507 "Proof stack entry … does not match essential hypothesis" | proof | `demo0-bad1` accepted | `n2` accepted | exposed by both |
| 519 "Disjoint variable violation" | proof | `set-dist-bad1` accepted | `n6` accepted | exposed by both |
| 497 "… does not match floating hypothesis" | proof | — | `n3` accepted | exposed only by crafted input |
| 539 "… label of a nonactive hypothesis" | proof | — | `n7` accepted | exposed only by crafted input |
| 638 "Stack entry … does not match proved assertion" | proof | — | `n1` accepted | exposed only by crafted input |
| 345 "var in $f already typed by an active $f-statement" | declaration | — | `n12` accepted | exposed only by crafted input |
| 488 "Stack underflow" | proof | — | `n4`: uncaught `IndexError` | crash-masked |
| 543 "No statement information found for label" | proof | — | `n9`: uncaught `TypeError` | crash-masked |
| 594 "Not enough saved proof steps" | proof | — | `n11`: uncaught `IndexError` | crash-masked |
| 629 "Empty stack at end of proof", 632 "Stack has more than one entry" | proof | — | — | no observable change |
| 25 other declaration- and parse-level guards (lines 111–468) | declaration | — | — | no observable change; no negative input in either corpus exercises them |

Totals: 36 mutants; **2 exposed by the upstream negative suite (5.6%)**; 6 exposed by the crafted suite (16.7%; the 2 upstream ones are among them); 3 crash-masked; 27 with no observable change. All 36 mutants still accept all 9 positive inputs. Of the 10 proof-level guards, 5 are shown load-bearing for soundness; of the 26 declaration- and parse-level guards, 1 is — and that one (line 345) shows that "merely syntactic" well-formedness checks can be soundness-critical: with it disabled, a variable typed both `wff` and `num` lets a theorem proved about numbers be instantiated at a formula, yielding `|- F`. The whole run (36 mutants × 28 inputs) took 96 s on one core, and a second run from the harness and inputs as printed under Evidence reproduced the results exactly; a single verification of the small databases takes 0.06–0.11 s.

**A guard that was never written.** The unmutated verifier accepts the crafted database `n8`, which proves `|- F` from no axioms by citing, in a *compressed* proof, a hypothesis label whose scope has closed. In normal-format proofs the check exists (lines 530–539 of `mmverify.py` at the pinned revision):

```python
        active_hypotheses = {label for frame in self.fs for labels in (frame.f_labels, frame.e_labels) for label in labels.values()}
        for label in proof:
            stmt_info = self.labels.get(label)
            if stmt_info:
                label_type = stmt_info[0]
                if label_type in {'$e', '$f'}:
                    if label in active_hypotheses:
                        self.treat_step(stmt_info, stack)
                    else:
                        raise MMError(f"The label {label} is the label of a nonactive hypothesis.")
```

In compressed-format proofs the label block is looked up without it (line 592):

```python
                self.treat_step(self.labels[plabels[proof_int] or ''], stack)
```

Reproduction (exit status 1 for the first file, 0 for the second):

```text
$c |- F $.
${
  hyp $e |- F $.
  inner $p |- F $= hyp $.
$}
outer $p |- F $= hyp $.            ← normal format: rejected ("nonactive hypothesis")
outer $p |- F $= ( hyp ) A $.      ← compressed format, same file otherwise: accepted
```

This is the upstream project's open issue 30 ("Inactive hypotheses allowed in label list of compressed proofs", opened 2025-09-17, with an open fix as pull request 32); it was rediscovered here by noticing the asymmetry while enumerating guards. None of the 8 upstream negative tests covers it, and no mutant can: there is no guard to disable. A second robustness defect surfaced the same way: an empty proof (`$= $.`) is rejected only because line 623, `if proof[0] == '(':`, raises an uncaught `IndexError`.

**Practical limits, as the experiment shows them.**

1. *Mutation measures the test suite, not the checker.* A 5.6% exposure rate says the upstream negative suite is thin, not that 94% of guards are unnecessary.
2. *Every guard needs its own known-false witness.* Building the 10 witnesses required a consistent toy theory with a model and one exploit per rule; for a dependent type theory the analogue is an expert-written exploit per check. The Lean Kernel Arena is, in effect, such a witness library: 90 must-reject exports, of which 47 belong to a tutorial series with "one small test per feature of the type theory" and 30 record bugs "actually found in a checker, including the official kernel".
3. *Crash-masking hides criticality.* Three mutants reject only by dying. In a memory-unsafe implementation language the same mutants would be undefined behaviour rather than a clean exit (compare Lean issue 10577, "Kernel accesses uninitialized memory", found by fuzzing).
4. *Redundant guards look dead.* Line 632 is shadowed by line 638 comparing `stack[0]` with the conclusion; defence in depth and equivalent mutants are indistinguishable from untested guards without analysis.
5. *Missing guards are invisible.* The compressed-proof hole above, and the Lean bugs fixed by pull requests 14498 ("kernel to check opaque values for fvars"), 14577 ("missing check at kernel inductive declaration") and 14807 (`is_prop` on a stuck type), are all absences. Guard enumeration helps a reviewer notice asymmetries; mutation execution does not.
6. *Wrong rules are invisible.* A guard that faithfully enforces an unsound rule survives every mutation analysis.

**Published evidence.** The `metamath-test` README states the motivation: the reference distribution had "no tests that are intended to *not* pass. That's not good, because if you replaced a verifier with the program "true" it would produce the same results". The arena README asks for the same thing ("We need more tests with tricky corner cases!"), and its `bugs/large-elim-param` test records a bounty in which an outside participant broke a deliberately small kernel through a wrong large-elimination check, fixed "the same day". No published guard-mutation kill rate for a production kernel was found. Basis: documentation.

### 4. Technique 3 — normalization and canonicity of closed terms as a smoke test

**The argument being borrowed.** If every well-typed closed term normalizes, and normal closed terms of an inductive type are constructor applications (canonicity), then a closed proof of an empty type cannot exist. MetaRocq's README lists both halves for PCUIC: "Canonicity: The weak head normal form of a term of inductive type is a constructor application" and "Consistency under the assumption of strong normalization". As a *test*: normalize closed terms of ground type (in particular any closed proof of `False`) and flag anything that is not canonical. Basis: documentation.

**Where it fails.**

| Failure | Evidence |
|---|---|
| Reduction need not terminate | The Lean4Lean paper: "the Lean type theory is known not to terminate", with an example ending `#reduce Om -- whnf nontermination` and a variant marked `rfl -- isDefEq nontermination`; the cause is "a combination of impredicativity, proof irrelevance, and subsingleton elimination" (Abel and Coquand). The kernel survives through "timeouts and depth limits", but "Not all parts of the kernel have such limits". A timeout is not a verdict. |
| Axioms and open computation produce stuck terms that are not bugs | The `is_prop` bug report describes an inferred type that "did not reduce to a sort but was left as a stuck term", for example "an `Eq.rec` whose major premise is a free variable". Canonicity is a theorem about closed, axiom-free terms; Lean's standard axioms have no computation rules (derived). |
| The normalizer is the kernel's own evaluator | Rocq's list has a whole section of evaluator bugs (bytecode VM, native compilation, lazy machine). A smoke test run through the same engine inherits them; run through a different engine it has become a quorum of evaluators. |
| Algorithmic conversion is incomplete, so "normal form" is not canonical across checkers | The arena keeps a `corner-cases` group (31 tests; 30 tests in the suite have outcome `either`) for inputs "where the correct outcome is debatable (`outcome: either`), typically gaps between algorithmic and declarative conversion". |
| Cost | Not quantified in any source read; normalization of proof terms can be far more expensive than type checking them (derived). |

**What it would catch.** A kernel that accepts an ill-typed closed term whose normalization then gets stuck or changes type. Whether the documented Lean exploits behave that way was not examined. The closest deployed relative re-derives *computational behaviour* per declaration rather than normalizing proofs: the arena's `ind-models` checker "adds an ordinary-declaration model of each supported inductive" and, "by re-deriving each inductive's recursor and reduction behavior from first principles and verifying the result, … can catch a large class of potential implementation bugs in the kernel's handling of inductives"; it rejects all 90 bad exports and checks Mathlib in 1,586 s. Basis: documentation + execution by upstream.

No evidence was found of normalization being used as a routine soundness smoke test on a production kernel.

### 5. Technique 4 — finite-model checks of individual inference rules

**Idea.** Treat each rule (or rewrite, or axiom schema instance) as a formula and search small models for a counterexample: premises true, conclusion false.

**Published evidence.** Alive (Lopes, Menendez, Nagarakatte, Regehr; PLDI 2015) checks LLVM peephole rewrites one rule at a time with an SMT solver over bit-vectors of bounded width and reported incorrect optimizations in LLVM's instruction combiner (eight, by the summary consulted; the paper's text was not fetched). Basis: documentation (bibliographic record verified; bug count from a secondary summary).

**Toy model run here** (not any real checker): rule instances over one binary predicate, all interpretations on domains of at most three elements.

| Rule instance | Result |
|---|---|
| `∀x ∃y P(x,y) ⊢ ∃y P(c,y)` (correct instantiation) | no countermodel with ≤ 3 elements |
| `∀x ∃y P(x,y) ⊢ ∃y P(y,y)` (substitution captured by the binder) | refuted at domain size 2 with `P = {(0,1),(1,0)}` |
| `∀x ∃y P(x,y) ⊢ ∃y ∀x P(x,y)` (quantifier swap) | refuted at domain size 2, same model |
| "every injective `f : D → D` is surjective" | no countermodel for sizes 1–6; false on infinite domains |

Basis: execution (toy model of first-order rule instances, not a model of any examined system).

**What it catches**: wrong side conditions and capture *at the level of the rule as written*, with a countermodel small enough to read. **What it misses**: (i) rules valid in all finite models but unsound in general (last row; any principle equivalent to finiteness); (ii) implementation slips — the historical capture bugs in HOL Light's `inst` and alpha-conversion were in code that implemented a correct rule; (iii) rules whose soundness is not first-order-expressible over a finite carrier (universe levels, impredicativity, inductive families); (iv) interactions between rules (Rocq's guard condition versus propositional extensionality). **Cost**: exponential in domain size and arity; trivial for the sizes that matter. Basis: derived.

### 6. Technique 5 — result checking and integrity against hardware faults

**Blum–Kannan result checking.** A checker for a function `f` is a (possibly randomized) program `C` that, given a program `P` as an oracle and an input `x`, outputs CORRECT with high probability if `P` is correct everywhere and BUGGY with high probability if `P(x) ≠ f(x)`; to be "quantifiably different" from `P` its own running time, not counting calls to `P`, should be asymptotically smaller. It certifies one result, not the program. Basis: normative (Blum and Kannan 1995; definition paraphrased from standard accounts of the paper, whose text was not fetched; bibliographic record verified).

Mapping to proof checking (derived):

- **Proof search → kernel** is already result checking with a deterministic certificate: the proof term. Nothing about the elaborator needs trust.
- **Kernel → ?** The kernel's output is one bit. There is no smaller certificate of "accept" unless the kernel is made to emit a *trace of its own decisions* that a simpler machine can replay. This is precisely what LRAT is to DRAT-trim (the complex backward checker emits unit-propagation hints; "Checking validity of LRAT proofs can be implemented using trusted systems such as the languages supported by theorem provers") and what `lean2dk` attempts for Lean's conversion checker (its `--no-elim` option is documented as "Do not eliminate definitional equalities via Lean4Less translation", i.e. by default the translation makes those equalities explicit). Trace emission turns technique 5 into technique 1 one level down.
- **Self-correction by random self-reduction**, the other half of the Blum–Kannan programme, has no evident analogue: proof validity has no algebraic structure relating one instance to random others.

**Hardware faults.** Two fleet operators report that processors silently mis-compute. Hochschild et al.: "we observe on the order of a few mercurial cores per several thousand machines", with examples including "A deterministic AES mis-computation, which was "self-inverting": encrypting and decrypting on the same core yielded the identity function, but decryption elsewhere yielded gibberish." Dixit et al. trace an application failure to one core on which the computation `Int(1.1^53)` "would always produce a result of 0 on Core 59 of the CPU" while `Int(1.1^52) = 142` was computed correctly. Basis: documentation.

Consequences for a proof checker (derived): (i) a single run's verdict can be wrong in either direction; a wrong *accept* is the dangerous one and needs a data-dependent fault on a branch that should have rejected; (ii) repeating the run on the same core does not help against deterministic faults (the "self-inverting" case); the repeat must be on different hardware, and a different binary also covers compiler and runtime faults; (iii) memory-mapped caches of checked results (`.olean`, `.vo`) extend the exposure from the run to the artifact's lifetime, which is the same I4 issue as in Section 2. No published instance of a hardware fault flipping a proof checker's verdict was found.

**New experiment: does re-checking detect corruption of the input?** Every one of the 8 × 1,353 = 10,824 single-bit flips of `demo0.mm` (from `metamath-test`) was re-checked with unmodified `mmverify.py`. Basis: execution (real upstream verifier and database; driver is this report's).

| Outcome | Flips | Share |
|---|---|---|
| Rejected with a verifier error | 4,694 | 43.37% |
| Rejected through an uncaught exception or other failure | 1,361 | 12.57% |
| Accepted; only comments or whitespace changed | 4,591 | 42.42% |
| Accepted; a label changed | 104 | 0.96% |
| Accepted; token structure changed (e.g. a stray token inside a constant declaration) | 68 | 0.63% |
| Accepted; the text of an axiom changed | 6 | 0.06% |

So 178 corruptions (1.64%) change the database's content and still verify. One of them (bit 7,368) rewrites the axiom

```text
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.      into
a1 $a |- ( t = s -> ( t = s -> r = s ) ) $.
```

which asserts that any `r` equals `s` once `t = s`; the database's only theorem still checks. A verifier's "accept" is integrity evidence for the *proofs relative to the statements it was shown*, and none at all for the statements. The published mitigations are structural: Metamath Zero keeps the statement in a separate `.mm0` file that "is built to be read"; Lean's judge compares the solution against a trusted challenge file; neither relies on the checker noticing. A digest of the axioms and theorem statements, compared out of band, closes the gap for hardware faults as well as for tampering. Basis: execution + documentation.

### 7. Side-by-side: bug classes, misses, cost, deployment

| | Catches | Misses | Cost | Deployment evidence |
|---|---|---|---|---|
| 1 Export / down-translation | producer-kernel implementation bugs on exported instances; kernel bypass; with a verified validator, validator bugs too | errors in the logic; shared prelude/format assumptions; trusted derived fields; common-mode bugs; un-pinned statements | gigabyte certificates; minutes to an hour per large library; a second implementation to maintain | broad: Lean (37 checkers), SAT (verified LRAT), SMT (CPC, Alethe), Metamath, Metamath Zero |
| 2 Guard mutation | inadequate negative tests; soundness-critical guards with no witness | missing guards; wrong rules; anything behind a crash or a redundant check | minutes of machine time; one expert-built witness per guard | negative-test suites exist (arena, `metamath-test`); no published kill rates; new experiment here |
| 3 Normalization / canonicity | ill-typed closed terms that get stuck (in principle) | non-terminating logics; axioms; shared-evaluator bugs; conversion incompleteness | unbounded | none found as a routine check; per-declaration re-derivation (`ind-models`) is the deployed relative |
| 4 Finite-model rule checks | wrong rule statements and side conditions with small countermodels | finite-only validity; implementation slips; rule interactions; higher-order features | negligible at small bounds | compiler rewrite rules (Alive); toy model here |
| 5 Result checking / integrity | single-run faults (by diverse re-execution); corrupted proofs | corrupted *statements* unless pinned; deterministic faults on the same core | a second run on other hardware; a digest | fleet-level fault data; statement pinning in Lean's judge and Metamath Zero; new experiment here |

Basis: derived from Sections 2–6.

### 8. Cost and footprint by level (L1–L6)

| Level | Findings | Basis |
|---|---|---|
| **L1 authoring** | Validator sizes at the pinned revisions: Lean C++ kernel 7,868 lines; nanoda 9,524 non-blank lines; `mm0-c` 1,388 lines in four `.c` files; `mmverify.py` 708 lines; `lrat-check.c` 509 and `drat-trim.c` 1,501 lines; `lean4export` 1,569, `comparator` 875 and `lean4checker` 638 non-blank lines of Lean. Guard-mutation harness: 100 lines of Python; ten witnesses and their toy theory: about 55 lines of Metamath. Person-time and model-token budgets: not published for any subject. | source; execution |
| **L2 toolchain build** | Not examined (nothing was built). | — |
| **L3 producer-side latency** | Certificate generation overhead in solvers and in Lean's export step: not examined. | — |
| **L4 generated-code performance** | Known not to apply: validators emit verdicts. | — |
| **L5 checking speed** | Mathlib export (5.9 GB): official kernel 12.1 T user instructions / 2,696 s; nanoda 5.77 T / 442 s wall on four threads; con-leche 6.13 T / 206 s wall on four threads; `ind-models` 12.94 T / 1,586 s; the 20 accepting checkers span 0.46 T to 19.22 T instructions. Metamath Zero: `set.mm` "at less than 200 ms". LRAT: 8 min 25 s for the Pythagorean transformation proof in a Coq-certified checker. `mmverify.py`: 0.06–0.11 s per small database, 0.63 s to reach the error in the 1.9 MB `set-dist-bad1.mm`. Cold-start and admission latency in the millisecond range: not examined. | execution by upstream; documentation; execution |
| **L6 memory and artifact size** | Peak resident memory on Mathlib: 9.91 GiB (official), 5.95 GiB (nanoda), 4.83 GiB (con-leche), 6.0 GiB (`ind-models`). Certificates: Mathlib NDJSON 5.9 GB (con-leche's `PERF.md` gives 6,069,002,157 bytes for its copy); Pythagorean DRAT ≈ 200 TB, compressed certificate 68 GB. Binary sizes, energy: not examined. | execution by upstream; documentation |

### 9. Human comprehensibility and conceptual simplicity (C1–C2)

**C1.** The techniques differ sharply in how legible their failures are. A finite countermodel is a two-element relation a reader can verify by hand. A guard-mutation finding is a line number plus a ten-line file that proves `False`. A rejected export is a declaration name. A normalization failure is a timeout or a term too large to read, and a hardware fault leaves nothing at all. For auditing *what was proved*, formats matter: NDJSON and `.mm0` can be read; a memory-mapped `.olean` cannot. The hidden footgun in technique 1 is convenience data in the certificate (Section 2, invariant I2): nothing in a JSON object distinguishes a field the validator must recompute from one it may use.

**C2.** All five techniques are one idea: *make the checker's decision re-derivable by something simpler than, or different from, the checker.* The unifying object is a pair (evidence, small validator): a certificate and its replayer; a witness file and the guard it kills; a countermodel and an evaluator; a digest and a comparison. Two regularities then replace ad-hoc practice: (i) **guard/witness duality** — every rejecting check should own at least one input that only it rejects, so the negative test suite is the checker's specification read backwards; (ii) **derived data is either absent from a certificate or labelled as hint** — which turns the "trusted `numFields`" class from a recurring bug into a type error. Neither moves complexity into adapters: both delete trust rather than relocate it. What does *not* unify is statement integrity (Section 6): it is orthogonal to every checker-centred technique and needs its own mechanism.

### 10. Validation of the techniques themselves (V1–V4)

| Axis | Evidence | Gaps |
|---|---|---|
| **V1 specification adequacy, mutation, non-vacuity** | Technique 2 is mutation analysis of the checker; `metamath-test` exists because a verifier replaced by `true` would pass positive-only tests; the arena scores checkers on 90 must-reject and 145 must-accept exports and keeps 30 as "either". | Mutation of the *rules* (does any test notice a weakened side condition in the specification?) was not examined. |
| **V2 fuzzing and differential testing of validators** | Arena entries "Found by a differential run of Pestka against other checkers"; Lean issue 10577 found by fuzzing declarations; the SMT fuzzing campaign (184 soundness bugs) is the producer-side counterpart. Malformed-certificate handling is tested by the arena's hand-written NDJSON exports. | No coverage metrics published for any validator. |
| **V3 concurrency, crash, silicon** | Silent-corruption field data (Section 6); same-kernel replay as a check on parallel elaboration state (Lean manual). | Weak-memory model checking, power-cut injection, side-channel and glitch testing: known not to apply to verdict correctness, or not examined. Fault injection into a running kernel: not done. |
| **V4 intent and human comprehension** | Statement pinning (challenge file; `.mm0`); the Lean manual's warning that a proved statement may not be the intended one. | No empirical study of how reliably humans read exported statements was found; temporal-logic falsification and hardware-in-the-loop replay: known not to apply. |

## Boundaries

- **Not examined**: Dedukti and Lambdapi themselves (only `lean2dk`'s README); LFSC (cvc5's `docs/proofs/output_lfsc.rst` does not exist at the pinned revision; whether cvc5 still emits LFSC was not determined); the internals and proofs of `cake_lpr`; Carcara's and Ethos's rule coverage; SMTCoq and Isabelle reconstruction; other Metamath verifiers (no differential run was made, so the acceptance of `n8` is shown for `mmverify.py` only); build times, binary sizes, energy; whether the documented Lean exploits would be exposed by normalizing their proof terms.
- **Unknown**: guard-mutation kill rates for any production kernel; the rate at which hardware faults flip checker verdicts; whether the 25 untested declaration-level guards of `mmverify.py` are soundness-critical (one of 26 was shown to be; the rest were not attacked).
- **Known not to apply**: the mutation percentages do not transfer to other verifiers or to `metamath-test` as used with other verifiers; the toy finite-model results say nothing about any real checker; the bit-flip shares are specific to one 1,353-byte file in which 42% of the flips land in comments or whitespace.
- **Unsupported**: Lean's same-kernel replayer explicitly does not defend against crafted `.olean` files; Ethos explicitly does not establish soundness of the rules it is given; DRAT-trim explicitly deviates from DRAT on unit deletions.
- **Stronger conclusions the evidence does not establish**: that a small validator is more reliable than a large one (9 of 37 Lean re-checkers accept a known-bad export; `mmverify.py` has an open soundness bug); that exposing 6 of 36 guards means the other 30 are safe to remove; that a clean export-and-recheck implies the statement is the intended one or that the logic is consistent.

## Evidence

Acquired in one session on 2026-11-20 between 00:25 and 02:00 UTC (2026-11-19 in US time zones, the date recorded in the metadata).

**Sources read at pinned revisions.**

- `leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab`: `README.md`, `format_ndjson.md` (version line; redundancy paragraph; "Inductive Declaration" note).
- `leanprover/lean4checker@91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`: `README.md` (deprecation notice; "Recheck a compiled Lean `olean` file using the Lean kernel").
- `leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e`: `README.md` (assumptions 1–6; guarantees; deprecation in favour of the built-in judge).
- `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`: `README.md`; `src/` line count (`find src -name '*.rs' | xargs cat | grep -cve '^\s*$'` → 9524, 22 files).
- `digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`: `README.md`, `divergences.md`; paper arXiv 2403.14064v3 (termination discussion).
- `leanprover/con-leche@cd2eceab2e9b10404c663b468639c8aa99d0d1f2`: `PERF.md`.
- `leanprover/lean-kernel-arena@0ddd55b91d6bc604ae0d14833bad60cc27e51268`: `README.md`, `tests/bugs/*.yaml`, `checkers/*.yaml`; the published `results.json` (meta block names this revision; 37 checkers, 265 tests — 90 reject, 145 accept, 30 either — and 9,805 results, runs dated 2026-11-14) analysed by counting `status`/`correctness` pairs per checker and per test and reading `wall_time`, `cpu_time`, `max_rss`, `instructions` for the `mathlib` test.
- `leanprover/lean4@5a82f1a47fbc2323ad6be6b11a7c0522dd4f3e68`: `src/kernel/*.{cpp,h}` (34 files, 7,868 lines); issues 10577, 14484, 14576, 15100, 15101, 15908 and pull requests 14613, 14806, 14807 read on the web (the titles of fix pull requests 14498 and 14577 are taken from the closing events on issues 14484 and 14576).
- `Deducteam/lean2dk@471208f18c29420e25750503648469fc95d2ac8f`: `README.md`.
- `marijnheule/drat-trim@2e3b2dc0ecf938addbd779d42877b6ed69d9a985`: `README.md` ("Clause Deletion Details"); `wc -l drat-trim.c lrat-check.c`.
- `tanyongkiam/cake_lpr@033aad53d1733bd4b8ca41cf6f1b5fb5d84f8de2`: `README.md`.
- `cvc5/cvc5@4cc4e66310f82f49f2e99e722bc74e0bfee41ffb`: `docs/proofs/proofs.rst`, `docs/proofs/output_alethe.rst`, `docs/proofs/output_cpc.rst`.
- `ufmg-smite/carcara@819f30914665019898cbad7e09d3962053b6f97a` and `cvc5/ethos@b02afbe66a4f796043ed3c5b9790cb6e7f00b9cc`: `README.md`.
- `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`: `README.md`, `mm0-c/*.c`; paper arXiv 1910.10703v3 (abstract).
- `rocq-prover/rocq@25f5b18a320e4796f181f938d3b74bebe7db4dc4`: `dev/doc/critical-bugs.md`.
- `MetaRocq/metarocq@51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`: `README.md` (PCUIC property list).
- Papers: arXiv 1612.02353 (LRAT), 1605.00723 (Pythagorean triples), 2004.08799 (operator mutation), 2102.11245 (silent data corruption), 1911.08174 (Abel–Coquand); Hochschild et al. (HotOS 2021 proceedings PDF); Crossref records for the DOIs in `REPORT.json`. The Lean reference manual page is the rendered "latest" version and is not version-pinned.

**Experiment A — guard mutation of `mmverify.py`** (`david-a-wheeler/mmverify.py@63a2aa3815cd5bf67892dbfc7f2048cbb177524c`, `david-a-wheeler/metamath-test@5758bf781bab662d4b31c7f72ac4dedea74fcb0f`; Python 3.13.15). Command: `python3 mutate_guards.py mmverify.py <metamath-test dir> <crafted dir> mut_results.json`. Harness:

```python
#!/usr/bin/env python3
"""Guard-disabling mutation analysis of mmverify.py (Metamath verifier).

For every `raise MMError(...)` site, build one mutant in which that guard can
never fire, then run each mutant on negative tests (files a sound verifier must
reject) and positive tests (files it must accept).

Mutation operator ("guard never fires"):
  * raise is the only statement of an `if` body      -> test := False
  * raise is the only statement of an `else` branch  -> test := True
  * otherwise                                        -> raise := pass
Outcome per (mutant, test): ACCEPT (exit 0), REJECT (MMError), CRASH (other
uncaught exception), TIMEOUT.
"""
import ast, copy, json, os, subprocess, sys, tempfile

SRC, UPSTREAM_TESTS, CRAFTED, OUT = sys.argv[1:5]
src = open(SRC).read()
tree = ast.parse(src)

def is_mmerror_raise(n):
    return (isinstance(n, ast.Raise) and isinstance(n.exc, ast.Call)
            and isinstance(n.exc.func, ast.Name) and n.exc.func.id == 'MMError')

sites = []  # (lineno, message-prefix)
for n in ast.walk(tree):
    if is_mmerror_raise(n):
        msg = ''
        for c in ast.walk(n.exc):
            if isinstance(c, ast.Constant) and isinstance(c.value, str):
                msg = c.value; break
        sites.append((n.lineno, msg[:48]))
sites.sort()

def mutant_source(lineno):
    t = copy.deepcopy(tree)
    op = None
    for parent in ast.walk(t):
        for field in ('body', 'orelse', 'finalbody'):
            lst = getattr(parent, field, None)
            if not isinstance(lst, list):
                continue
            for i, child in enumerate(lst):
                if is_mmerror_raise(child) and child.lineno == lineno:
                    if isinstance(parent, ast.If) and len(lst) == 1:
                        parent.test = ast.Constant(value=(field != 'body'))
                        op = 'cond:=False' if field == 'body' else 'cond:=True'
                    else:
                        lst[i] = ast.Pass()
                        op = 'raise:=pass'
    assert op, lineno
    ast.fix_missing_locations(t)
    return ast.unparse(t), op

UP_NEG = ['anatomy-bad1', 'anatomy-bad2', 'anatomy-bad3', 'big-unifier-bad1',
          'big-unifier-bad2', 'big-unifier-bad3', 'demo0-bad1', 'set-dist-bad1']
UP_POS = ['anatomy', 'big-unifier', 'demo0', 'demo0-includer', 'emptyline',
          'miu', 'peano-fixed', 'hol']
CR_NEG = ['n1_wrong_conclusion', 'n2_ehyp_mismatch', 'n3_fhyp_typecode',
          'n4_stack_underflow', 'n6_dv_violation', 'n7_scope_normal',
          'n9_unknown_label', 'n10_empty_proof', 'n11_compressed_bad_index',
          'n12_double_typed_var']
CR_KNOWN = ['n8_scope_compressed']   # accepted by the unmutated verifier
CR_POS = ['pos_sanity']

def run(pyfile, path, cwd):
    try:
        with open(path, 'rb') as fh:
            p = subprocess.run([sys.executable, pyfile], stdin=fh, cwd=cwd,
                               capture_output=True, timeout=120)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'
    if p.returncode == 0:
        return 'ACCEPT'
    err = p.stderr.decode('utf-8', 'replace')
    last = err.strip().splitlines()[-1] if err.strip() else ''
    return 'REJECT' if last.startswith('MMError') else 'CRASH:' + last.split(':')[0][:24]

def suite(pyfile):
    r = {}
    for group, names, d in (('up_neg', UP_NEG, UPSTREAM_TESTS), ('up_pos', UP_POS, UPSTREAM_TESTS),
                            ('cr_neg', CR_NEG, CRAFTED), ('cr_known', CR_KNOWN, CRAFTED),
                            ('cr_pos', CR_POS, CRAFTED)):
        r[group] = {n: run(pyfile, os.path.join(d, n + '.mm'), d) for n in names}
    return r

work = tempfile.mkdtemp(prefix='mmmut_')
results = {'sites': len(sites), 'mutants': []}
# Sanity: the pretty-printed but unmutated source must behave like the original.
base_py = os.path.join(work, 'base.py'); open(base_py, 'w').write(ast.unparse(tree))
results['original'] = suite(os.path.abspath(SRC))
results['unparsed_original'] = suite(base_py)
assert results['original'] == results['unparsed_original']
for lineno, msg in sites:
    code, op = mutant_source(lineno)
    f = os.path.join(work, f'm{lineno}.py'); open(f, 'w').write(code)
    r = suite(f)
    results['mutants'].append({'line': lineno, 'msg': msg, 'op': op, 'res': r})
json.dump(results, open(OUT, 'w'), indent=1)
print('sites', len(sites), 'written', OUT)
```

Crafted inputs: every file is the following preamble followed by the lines shown in the table.

```text
$( Toy two-sorted system. Intended model: wffs are truth values (F false, T true,
   -> implication, -. negation); num ranges over {0}; "bot" is an obj, not a num;
   ( n = n ) is true, ( n = bot ) and ( n = T ) are false
   (neither bot nor T is a num); var metavariables range over distinct
   object variables and ( x == y ) is syntactic identity. Every $a |- axiom is true
   in this model and both rules preserve truth, so "|- F" is not derivable. $)
$c wff |- num obj var ( ) -> -. = == F T 0 bot $.
$v p q n x y $.
wp $f wff p $.
wq $f wff q $.
nn $f num n $.
vx $f var x $.
vy $f var y $.
wF $a wff F $.
wT $a wff T $.
wi $a wff ( p -> q ) $.
wn $a wff -. p $.
n0 $a num 0 $.
ob $a obj bot $.
weq $a wff ( n = n ) $.
weqb $a wff ( n = bot ) $.
weqt $a wff ( n = T ) $.
wse $a wff ( x == y ) $.
ax-t $a |- T $.
ax-refl $a |- ( n = n ) $.
ax-nb $a |- -. ( n = bot ) $.
ax-nw $a |- -. ( n = T ) $.
ax-sid $a |- ( x == x ) $.
${ $d x y $. ax-sne $a |- -. ( x == y ) $. $}
${ mp.1 $e |- p $.  mp.2 $e |- ( p -> q ) $.  ax-mp $a |- q $. $}
${ ct.1 $e |- p $.  ct.2 $e |- -. p $.  ax-ct $a |- F $. $}
```

| File | Appended lines | Guard targeted | Unmutated verifier |
|---|---|---|---|
| `pos_sanity` | `ok1 $p \|- ( 0 = 0 ) $= n0 ax-refl $.` / `${ $d x y $. ok2 $p \|- -. ( x == y ) $= vx vy ax-sne $. $}` / `ok3 $p \|- ( x == x ) $= vx ax-sid $.` / `ok4 $p \|- -. ( 0 = T ) $= n0 ax-nw $.` | — | accepts |
| `n1_wrong_conclusion` | `bad $p \|- F $= ax-t $.` | 638 | rejects |
| `n2_ehyp_mismatch` | `bad $p \|- F $= wT wF ax-t ax-t ax-mp $.` | 507 | rejects |
| `n3_fhyp_typecode` | `bad $p \|- F $= ob weq ob ax-refl ob ax-nb ax-ct $.` | 497 | rejects |
| `n4_stack_underflow` | `bad $p \|- F $= ax-t ax-ct $.` | 488 | rejects |
| `n6_dv_violation` | `bad $p \|- F $= vx vx wse vx ax-sid vx vx ax-sne ax-ct $.` | 519 | rejects |
| `n7_scope_normal` | `${ h $e \|- F $. inner $p \|- F $= h $. $}` / `bad $p \|- F $= h $.` | 539 | rejects |
| `n8_scope_compressed` | `${ h $e \|- F $. inner $p \|- F $= h $. $}` / `bad $p \|- F $= ( h ) A $.` | (no guard exists) | **accepts** |
| `n9_unknown_label` | `bad $p \|- F $= nosuch $.` | 543 | rejects |
| `n10_empty_proof` | `bad $p \|- F $= $.` | 629 | exits non-zero via uncaught `IndexError` |
| `n11_compressed_bad_index` | `bad $p \|- F $= ( ) B $.` | 594 | rejects |
| `n12_double_typed_var` | `$v r $.` / `wr $f wff r $.` / `nr $f num r $.` / `t0 $p wff ( r = T ) $= nr weqt $.` / `t1 $p \|- ( r = r ) $= nr ax-refl $.` / `t3 $p \|- -. ( r = T ) $= nr ax-nw $.` / `bad $p \|- F $= wT t0 wT t1 wT t3 ax-ct $.` | 345 | rejects |

Observed summary printed from `mut_results.json`: mutants 36 (32 `cond:=False`, 4 `cond:=True`); exposed by upstream negatives 2 (lines 507, 519); exposed by crafted negatives 6 (lines 345, 497, 507, 519, 539, 638); new uncaught exceptions on lines 488 (`n4`), 543 (`n9`), 594 (`n11`); 27 mutants identical to the original on all 28 inputs; `n8` accepted by the original and by all 36 mutants. The pretty-printed but unmutated source behaves identically to the original on all inputs (asserted by the harness).

**Experiment B — single-bit corruption of `demo0.mm`**. Command: `python3 bitflip_recheck.py mmverify.py demo0.mm 6` (3 min 29 s wall on six processes). Driver:

```python
#!/usr/bin/env python3
"""Exhaustive single-bit corruption of a Metamath database, re-checked by mmverify.py.
For each of the 8*len(file) single-bit flips: run the verifier; if it still exits 0,
classify what changed.  Measures how much integrity 'the checker accepted it' gives."""
import os, re, subprocess, sys, tempfile, multiprocessing as mp, collections

VERIFIER, DB = sys.argv[1], sys.argv[2]
orig = open(DB, 'rb').read()

def tokens(b):
    s = b.decode('latin-1')
    s = re.sub(r'\$\(.*?\$\)', ' ', s, flags=re.S)       # strip comments
    return s.split()

OT = tokens(orig)
KW = {'$c', '$v', '$f', '$e', '$a', '$p', '$d', '${', '$}'}

def region(toks, i):
    """statement kind containing token i, with 'proof' for the part after $=."""
    kind, in_proof = 'label/other', False
    for j in range(i, -1, -1):
        if toks[j] == '$=': in_proof = True
        if toks[j] == '$.' and j != i: break
        if toks[j] in KW:
            kind = toks[j]; break
    return kind + ('-proof' if in_proof and kind == '$p' else '')

def one(k):
    byte, bit = divmod(k, 8)
    m = bytearray(orig); m[byte] ^= (1 << bit)
    with tempfile.NamedTemporaryFile(delete=False, suffix='.mm') as fh:
        fh.write(m); name = fh.name
    try:
        with open(name, 'rb') as inp:
            p = subprocess.run([sys.executable, VERIFIER], stdin=inp, capture_output=True, timeout=60)
        rc = p.returncode
        last = (p.stderr.decode('latin-1').strip().splitlines() or [''])[-1]
    except subprocess.TimeoutExpired:
        rc, last = -1, 'TIMEOUT'
    finally:
        os.unlink(name)
    if rc != 0:
        return ('rejected:MMError' if last.startswith('MMError') else 'rejected:crash/other', None)
    MT = tokens(bytes(m))
    if MT == OT:
        return ('accepted:comment-or-whitespace-only', None)
    i = next((x for x in range(min(len(MT), len(OT))) if MT[x] != OT[x]), min(len(MT), len(OT)))
    if len(MT) != len(OT):
        return ('accepted:token-structure-changed', (k, OT[max(0, i-2):i+3], MT[max(0, i-2):i+3]))
    kind = region(OT, i)
    if kind == 'label/other' or (i + 1 < len(OT) and OT[i + 1] in KW):
        kind = 'label'
    return ('accepted:changed-' + kind, (k, OT[i], MT[i]))

if __name__ == '__main__':
    with mp.Pool(int(sys.argv[3]) if len(sys.argv) > 3 else 6) as pool:
        res = pool.map(one, range(8 * len(orig)), chunksize=64)
    c = collections.Counter(r[0] for r in res)
    n = len(res)
    print(f'file {os.path.basename(DB)}: {len(orig)} bytes, {n} single-bit flips')
    for k, v in sorted(c.items()):
        print(f'  {k:45s} {v:6d}  {100*v/n:6.2f}%')
    ex = collections.defaultdict(list)
    for cat, e in res:
        if e and len(ex[cat]) < 3: ex[cat].append(e)
    for cat, es in sorted(ex.items()):
        print('  e.g.', cat, es)
```

Observed output (counts as in Section 6), with examples `accepted:changed-$a [(6120, 'r', 's'), (6552, 'r', 's'), (7368, 'r', 's')]`; bit 6120 changes `tpl $a term ( t + r ) $.` to `( t + s )`, bit 6552 changes `weq $a wff t = r $.` to `t = s`, bit 7368 changes axiom `a1` as shown in Section 6.

**Toy model C — finite-model rule checks** (standard-library Python; domain sizes ≤ 3 for the predicate rules, ≤ 6 for the function rule):

```python
import itertools
def interps(n):
    cells = list(itertools.product(range(n), repeat=2))
    for bits in itertools.product((False, True), repeat=len(cells)):
        yield dict(zip(cells, bits))
def refute(rule, maxn):
    for n in range(1, maxn + 1):
        for P in interps(n):
            if rule(range(n), P): return n, sorted(k for k, v in P.items() if v)
r1 = lambda D, P: all(any(P[x, y] for y in D) for x in D) and not any(P[0, y] for y in D)
r2 = lambda D, P: all(any(P[x, y] for y in D) for x in D) and not any(P[y, y] for y in D)
r3 = lambda D, P: all(any(P[x, y] for y in D) for x in D) and not any(all(P[x, y] for x in D) for y in D)
print(refute(r1, 3), refute(r2, 3), refute(r3, 3))
print([any(len(set(f)) == n and set(f) != set(range(n)) for f in itertools.product(range(n), repeat=n)) for n in range(1, 7)])
```

Observed: `None (2, [(0, 1), (1, 0)]) (2, [(0, 1), (1, 0)])` and `[False, False, False, False, False, False]`.

## Revalidation

- **Upstream bug still present?** Save the six-line compressed-proof file from Section 3 and run `python3 mmverify.py < file; echo $?`. Exit status 0 means the hole is still open; also check whether upstream issue 30 has been closed.
- **Guard coverage after a change to the verifier or the test suite**: rerun Experiment A. The discriminating numbers are the count of mutants exposed by the upstream negatives alone (2 of 36 here) and the list of crash-masked lines.
- **Export pipeline health**: fetch the arena's `results.json`; for the validators you depend on, count results with `status == "accepted"` and `correctness == "incorrect"` (must be 0) and note any `rejected`/`incorrect` on tests you need (completeness drift). Re-read `tests/bugs/` for new entries mentioning "trusted" fields.
- **Format trust**: `grep -n "redundant" format_ndjson.md` in `lean4export`; if a later format version drops or labels derived fields, the I2 hazard of Section 2 has changed.
- **Semantics drift between certificate producer and checker**: `grep -n "ignores deletion steps of unit clauses" README.md` in DRAT-trim; `grep -n "does not prove that those rules are sound" README.md` in Ethos.
- **Integrity experiment on another database**: rerun Experiment B on any small `.mm` file; the figure to watch is the share of accepted flips whose category is not comment-or-whitespace, and whether any of them alters an `$a` statement.
- **Toy models**: rerun C; its output is fully determined.
- Claims about Lean, SAT and SMT tool performance are upstream measurements; revalidating them means rerunning the arena or the cited benchmarks, which was not done here.
