# Cyclic Verifier Rings, Relativized Self-Verification, and Löb Boundaries for Proof Checkers

## Summary

A proof checker `C` for a logic `L` can be the subject of two different correctness claims, and almost every confusion about "self-verified" or "mutually verified" checkers comes from mixing them:

- **(a) Implementation faithfulness** — `Accept_C(x) ⇒ Deriv_L(x)`: the code accepts only what the rules of `L` derive. This is an ordinary statement about a program and an inductive relation. It can be proved in `L` itself, by `C` itself, or around a ring `C₁ → C₂ → … → C₁`, with no logical obstacle.
- **(b) Semantic soundness / consistency** — `Deriv_L(φ) ⇒ True(φ)`, or at least `¬Deriv_L(⊥)`. Gödel's second incompleteness theorem and Löb's theorem forbid a consistent `L` from proving this about itself, and (derived below) forbid any closed cycle `T₁ ⊢ Con(T₂), …, Tₙ ⊢ Con(T₁)` among consistent, sufficiently strong theories. An inconsistent system proves its own soundness trivially, so an unconditional self-soundness theorem carries no evidence.

Every real project examined therefore **relativizes** claim (b) to a hypothesis that the host logic cannot discharge: MetaRocq assumes strong normalization (`NormalizationIn`) and guard-checker correctness; con-leche proves `model_exists` under `[SetTheory V]` (an ω-chain of Grothendieck universes); Candle proves `hol_consistent` under `is_set_theory mem ∧ ∃inf. is_infinite mem inf`; HOL Light's `Model/` proves consistency only of "pure HOL (no axioms or definitions)"; Milawa is proved sound in the stronger HOL4; Metamath Zero's goal theorem `Verifier_Valid` is pure claim (a) and is unproved at the examined revision; Lean4Lean is a partial claim-(a) proof that explicitly disclaims unconditional soundness.

Tested against documented kernel soundness bugs in Lean, Rocq, Agda, HOL Light, HOL4 and Isabelle: a faithfulness proof (a) catches implementation slips (missing guards, overflow, unsound caches) on **all** inputs and has actually found Lean kernel bugs; independent N-version re-checking catches them only on replayed inputs and only when the implementations fail differently (one Lean bug was accepted by two independent kernels). **Neither** catches an error in the specification of `L` itself (Rocq's guard condition vs. propositional extensionality, Isabelle's overloading with type definitions, Agda's sized types), an assumption all parties share (Lean's official-prelude assumption), or a miscompiled/misbehaving checker binary; those need a semantic model (relativized (b)), explicit boundary checks, and Diverse Double-Compiling or verified compilation respectively.

## Applicability

Scope: kernels and standalone checkers of interactive theorem provers, and the meta-theorems proved about them. The subjects in `REPORT.json` relate as follows.

- **Systems that verify a checker**: MetaRocq (Rocq in Rocq), Lean4Lean and con-leche (Lean in Lean), Candle inside CakeML (HOL Light in HOL4), HOL Light's `Model/` directory (HOL in HOL), the Milawa soundness proof inside HOL4 with Milawa's own sources in the ACL2 community books, and Metamath Zero. Each was read at the pinned revision; quoted identifiers and theorem statements are from those trees.
- **Bug records used as test cases**: Lean 4 issues and pull requests (read on the GitHub web pages on the observation date; numbers given), the Lean Kernel Arena `tests/bugs/*.yaml` catalogue and its published `results.json` (generated from the pinned arena revision), Rocq's `dev/doc/critical-bugs.md`, Agda issues labelled `false`, HOL Light's `CHANGES` file, and HOL4 issues. Issue and pull-request discussions are mutable; the pinned repository revisions fix only the in-tree files.
- **Logic**: Löb (1955) is the normative reference for Löb's theorem; the no-ring corollary is this report's own derivation and is labelled derived.
- **Not a subject**: Isabelle sources (only the cited paper was used), CakeML's compiler proof, and any execution of the provers themselves. No prover, kernel or proof was built or run; the only executed artifact is a small Python model checker for modal formulas, labelled as a toy.

Findings stated for "Lean", "Rocq" etc. apply to the versions named in the cited records. Where a verdict says a technique "would plausibly have caught" a bug, that is a derived judgment with its reason stated, not an observation, unless the row cites an upstream statement that a specific tool did or did not catch it.

## Findings

### 1. Two claims, one composition law

Fix a logic `L` with an inductively defined derivability relation `⊢_L` and a total checker program `C`.

```text
(a)  Faith(C, L)   :  ∀x.  C(x) = accept  →  Deriv_L(x)
(b1) Con(L)        :  ¬ Deriv_L(⊥)
(b2) Sound(L, M)   :  ∀φ.  Deriv_L(φ)  →  M ⊨ φ          (M a model; implies b1 when M ⊭ ⊥)
(b3) Rfn(L)        :  ∀φ.  Prov_L(⌜φ⌝) → φ                (reflection, as a schema)

Composition:   Faith(C, L) ∧ Con(L)        ⟹  C never accepts ⊥
               Faith(C, L) ∧ Sound(L, M)   ⟹  everything C accepts holds in M
```

`Faith` mentions no truth predicate and no model; it is an arithmetical statement about a program and a syntactic relation. Claims (b1)–(b3) are about `L`, not about `C`; proving them needs resources beyond `L` (Section 2). A meta-theorem about a checker is fully described by four coordinates: the host logic `H` in which it is proved (and whose checker checked it), the hypothesis `A` it is conditional on, the property `P ∈ {Deriv_L, has-a-model, true}`, and the residue (driver, parser, compiler, runtime, hardware) outside the theorem: `A ⊢_H Accept_C(x) → P(x)`.

Basis: derived (definitions); the instantiations in Section 3 are source.

### 2. Limits on (b): Gödel II, Löb, and why consistency proofs cannot close a ring

**Löb's theorem** (Löb 1955): for a recursively axiomatized theory `T` satisfying the Hilbert–Bernays–Löb derivability conditions, if `T ⊢ Prov_T(⌜φ⌝) → φ` then `T ⊢ φ`; formalized, `T ⊢ Prov_T(⌜Prov_T(⌜φ⌝) → φ⌝) → Prov_T(⌜φ⌝)`. Gödel's second theorem is the instance `φ = ⊥`: `T ⊢ Con(T)` only if `T` is inconsistent. Basis: normative (Löb 1955).

Three consequences for checkers:

1. **Self-reflection is vacuous.** `T` proves "if I prove φ then φ" only for those φ it proves outright. A system cannot certify its own (b3) even one sentence at a time.
2. **An inconsistent checker passes its own soundness audit.** In provability logic `□⊥ → □(□p → p)` is valid: if `T ⊢ ⊥` then `T` proves every sentence, including `Sound(T)`. Hence `Pr[T ⊢ Sound(T) | T inconsistent] = 1`, and observing such a proof cannot raise confidence in `T`. Evidence can only enter through a channel that an inconsistency would not also open: an independently trusted host, a small audited checker, or a human-inspected model.
3. **No ring of consistency proofs (derived).** Let `T₀,…,Tₙ₋₁` be consistent, recursively axiomatized theories extending `IΣ₁`, with standard Σ₁ provability predicates, each proving that its successor extends Robinson's `Q`. Suppose `Tᵢ ⊢ Con(Tᵢ₊₁)` for all `i` (indices mod `n`). Then for each `i`:
   - (S1) `Tᵢ₊₁ ⊢ Con(Tᵢ₊₂)` is a true Σ₁ fact, so by Σ₁-completeness `Tᵢ ⊢ Prov_{i+1}(⌜Con(Tᵢ₊₂)⌝)`;
   - (S2) `¬Con(Tᵢ₊₂)` is Σ₁, so by formalized Σ₁-completeness of `Tᵢ₊₁`, `Tᵢ ⊢ ¬Con(Tᵢ₊₂) → Prov_{i+1}(⌜¬Con(Tᵢ₊₂)⌝)`;
   - (S3) `Tᵢ ⊢ Prov_{i+1}(⌜ψ⌝) ∧ Prov_{i+1}(⌜¬ψ⌝) → ¬Con(Tᵢ₊₁)`.

   Combining, `Tᵢ ⊢ Con(Tᵢ₊₁) → Con(Tᵢ₊₂)`, and with the hypothesis `Tᵢ ⊢ Con(Tᵢ₊₂)`: "proves the consistency of" is transitive. Going round the ring gives `T₀ ⊢ Con(T₀)`, contradicting Gödel II. Since (b2) and (b3) each imply (b1) provably in a weak base theory, no ring of soundness or model-existence proofs exists either. At least one edge of any ring of (b)-claims must be conditional on a hypothesis its prover cannot establish.

   Basis: derived (steps S1–S3 are the standard derivability conditions) + execution (toy finite Kripke-frame check of the modal skeleton, not arithmetic; Evidence E9). The frame check found the 2-ring formula `(□₁Con₂ ∧ □₂Con₁) → □₁⊥` valid on all 9,982 bimodal frames with at most 4 worlds satisfying the bridge condition for `□ᵢφ → □ⱼ□ᵢφ`, the 3-ring analogue valid on all 1,151 trimodal frames with at most 3 worlds, and a countermodel as soon as the bridge condition (formalized Σ₁-completeness) is dropped, which matches the role of S1–S2 in the derivation.

**What is still possible.**

- **A ring (or self-loop) of (a)-proofs.** `Tᵢ ⊢ Faith(Cᵢ₊₁, Lᵢ₊₁)` has no modal obstruction: `Faith` is not a consistency statement, and `L` can prove `Faith(C, L)` about its own checker. Metamath Zero's goal, Lean4Lean, MetaRocq's "correct and complete w.r.t. the PCUIC specification", and Candle's kernel theorem are all of this kind.
- **Pointwise but not uniform (b).** A theory can prove the consistency of each finite fragment of itself without proving the universal statement. con-leche's README states the Lean instance exactly: the ω-chain of universes it assumes is needed only up to the highest universe a given input uses, and "For every concrete `k` we can prove their existence in lean without further assumptions, just not for all `k`." Basis: documentation (con-leche README).
- **Strictly ascending towers.** A stronger host proves (b) for a weaker object: HOL4 proves Milawa's logic sound; HOL with an infinite set proves HOL consistent (Candle); ZFC with ω inaccessibles models Lean (Carneiro, as cited by the Lean4Lean paper and con-leche). Towers have a top that is trusted, not proved.

**What a ring of (a)-proofs is worth.** If every `Cᵢ` is unfaithful in a way that lets it accept a bogus proof of `Faith(Cᵢ₊₁, Lᵢ₊₁)`, the ring closes with every member wrong; a ring has no base case. Its value is conditional: *if at least one checker in the ring is faithful and its logic is consistent*, then that checker's verdict on its successor's faithfulness is trustworthy, and so on forward. A ring therefore converts "trust all `n` implementations" into "trust any one of them plus the shared specification", which is the same reduction N-version checking gives, but for all inputs rather than for the inputs replayed (Section 4). Basis: derived.

MetaRocq's README records that its `Quotation` development aims to show that the quoting modality `□` is "a lax monoidal semicomonad … which is sufficient for proving Löb's theorem", i.e. the same boundary is being formalized inside Rocq's own type theory. Basis: documentation.

### 3. How real systems relativize their claims

All quotations are from the pinned trees unless marked otherwise. Basis for the whole table: source + documentation.

| System | Host | Claim proved | Hypothesis the host cannot discharge (as written) | Outside the theorem | State at the examined revision |
|---|---|---|---|---|---|
| **MetaRocq** safe checker for PCUIC | Rocq | (a): "The checker is shown to be correct and complete w.r.t. the PCUIC specification." (b), relativized: "Consistency under the assumption of strong normalization". | `pcuic/theories/PCUICSN.v`: "We assume normalization of the reduction. We state is as well-foundedness of the reduction." — `Class NormalizationIn … := normalization_in : forall Γ t, welltyped Σ Γ t -> Acc (cored Σ Γ) t.` Also `PCUICGuardCondition.v`: "AXIOM postulate correctness of the guard condition checker" (`Class GuardCheckerCorrect`). | Specification covers "all of Rocq except eta-expansion and template polymorphism"; extraction and the Rocq kernel that checks the development. | Described upstream as done under those classes; not rebuilt here. |
| **Lean4Lean** | Lean 4 | Partial (a): `Lean4Lean.Verify` "is the proof that the `Lean4Lean` implementation satisfies the `Lean4Lean.Theory` abstract specification." | None for (b): the paper says "We are up against Gödel's incompleteness theorem, so anything that would imply the unconditional soundness of Lean won't be directly provable", and the kernel is given fuel because Lean's reduction is known not to terminate. | README: "derived directly from the C++ kernel implementation, and as such likely shares some implementation bugs with it (it's not really an independent implementation)". `Verify/Axioms.lean` postulates facts about upstream opaques (e.g. `axiom mkData_eq : @mkData = @mkData'`). | Incomplete: `grep -rw sorry` matches 18 lines under `Lean4Lean/Verify` and 9 under `Lean4Lean/Theory`; `Theory/Typing/UniqueTyping.lean` is described as "conjectures about the typing relation". |
| **con-leche** | Lean 4 | (b), relativized, composed with (a) in one theorem: `theorem model_exists (V : Type w) [SetTheory V] … (accepted : checkDecls .verified pins maxNatSize ds = .ok env) : Nonempty (Model V env)` and the corollary `no_False_declaration` (an export containing a theorem of type `False` is rejected). | `class SetTheory (V : Type u)`: "membership, the six ZF⁻ axioms … and an ω-chain of Grothendieck universes" (`univChain`, `univChain_mem`, `univChain_tg`). A separate bridge shows `carneiro_implies_conleche : OmegaInaccessibles.{u} → Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V)`, with axioms `[propext, Classical.choice, Quot.sound]`. | The `IO` driver (modelled, with unenforced assumptions such as "The files accessed are not changing under our nose"); the Lean compiler and runtime ("Bugs in the Lean runtime support for `Nat` can lead to unsoundness here"); the `.olean` format, which "is not well-specified". The checker does extra comparisons purely to make the proof go through (the README's "certification tax"). | Stated complete by upstream ("production ready"); not rebuilt here. |
| **Candle** (in CakeML) | HOL4 | (a) for the whole read-eval-print loop: `events_of_semantics` concludes `∀e. e IN events_of res ⇒ ok_event e`, where `ok_event (IO_event n out y) ⇔ n = ExtCall kernel_ffi ⇒ ∃ctxt th. THM ctxt th ∧ thm2bytes ctxt th = out ∧ ctxt extends init_ctxt`. (b), relativized: `hol_consistent`. | `hol_consistent: is_set_theory ^mem ∧ (∃inf. is_infinite ^mem inf) ⇒ … consistent_theory (thyof ctxt)`; without the axiom of infinity only `is_set_theory ^mem` is needed (`fhol_consistent`). `holAxiomsScript.sml`: "For the axiom of infinity, this requires an additional assumption on the set theory." | HOL4's own kernel; the CakeML compiler proof and machine model (not examined). | Theorems present in the tree; not rebuilt here. |
| **HOL Light `Model/`** | HOL Light | (b) for a fragment: `Model/make.ml` is headed "Consistency proof of "pure HOL" (no axioms or definitions) in itself." | The fragment omits the axioms (including infinity) and the definitional rules; the accompanying paper (Harrison 2006) treats full HOL only relative to a stronger axiom. | OCaml compiler and runtime; everything about definitions. | Present in the tree; not re-run. |
| **Milawa** on the verified Lisp runtime | HOL4 (Milawa's own tower: ACL2-bootstrapped) | (b) by a stronger host: `examples/theorem-prover/README` — "when Milawa is run on top of the verified runtime it will only ever prove statements that are true w.r.t. the semantics of Milawa's formulas -- no matter how reflection or any other feature is used." | None inside Milawa: its self-verification is a "progression of proof checkers" (ACL2 books `milawa/ACL2/README`), each admitted by its predecessor, i.e. a tower of (a)-style extension proofs, not a consistency proof. | HOL4's kernel and the hardware model. | README (dated 2012) describes the proof as finished; not rebuilt here. |
| **Metamath Zero** | MM0 over Peano arithmetic | Goal is pure (a) at machine-code level: `theorem Verifier_Valid (k mm0_file: nat): $ initialConfig Verifier k /\ succeeds k mm0_file 0 -> Valid mm0_file $;` with `Verifier: string` "The actual verifier ELF". | None needed: the conclusion is "the theorems in the input are derivable", not that they are true. | The x86 model (`x86.mm0`), the axioms of whatever logic the user supplies. | Unproved: "`verifier.mm1` will be the proof"; the compiler correctness proof "still admits a `sorry` axiom". |

Three structural observations follow.

1. **The hypothesis is always stronger than the object logic's own resources**: normalization of PCUIC implies its consistency; an ω-chain of universes models all of Lean's universes; an infinite set models HOL's axiom of infinity. This is Section 2 showing through in engineering form.
2. **(a) and (b) are sometimes fused into one theorem** (con-leche's `model_exists` speaks about the checker function directly; Candle composes two theorems). Fusion removes the need for a separately specified `Deriv_L`, at the price that a reader can no longer audit "the rules of Lean" independently of the checker.
3. **Convergence of self-hosting**: an open Lean 4 pull request (number 16353, opened 2026-11-09, titled "feat: replace the C++ kernel with InLean, a verified Lean port (experiment)") proposes replacing the C++ type checker with a Lean port "that con-leche proves sound". If merged, the checker that checks its own soundness proof would be the proved checker itself: a self-loop of (a) plus relativized (b), still resting on `[SetTheory V]`, the Lean compiler, and an unverified inductive-type generator of which the pull request says "nothing it produces is added unless con-leche's verified inductive check accepts it". Basis: documentation (pull-request text; mutable).

### 4. Mutual verification versus independent N-version re-checking

| Failure class | Faithfulness proof (a), incl. rings | Relativized model proof (b) | Independent re-check by `k` other kernels | Same-kernel replay (`lean4checker`, `coqchk`) |
|---|---|---|---|---|
| Missing or wrong guard in one implementation | Caught for **all** inputs (proof cannot be completed) | Caught if fused with (a) | Caught for replayed inputs, if not all `k` share the slip | Not caught |
| Unsound optimization or cache (overflow, hash, union-find) | Caught if the optimization is inside the proved code; missed if modelled away by an axiom | as left | Caught unless the optimization was copied | Not caught |
| Kernel bypass by metaprograms or corrupted environment state | Out of scope (not kernel code) | Out of scope | Caught (export is re-checked from scratch) | Caught — this is its purpose |
| Error in the rules of `L` (spec) | **Not caught**: the proof is relative to those rules | **Caught**: no model exists, the proof fails | **Not caught**: all implement the same rules | Not caught |
| Assumption shared by all parties (trusted prelude, export format, statement meaning) | Not caught unless the assumption is made an explicit check | Not caught | Not caught | Not caught |
| Miscompiled or misexecuted checker binary | Not caught unless the theorem is about the binary (Metamath Zero's goal, con-agua's claim, CakeML's bootstrap) | as left | Caught if the kernels use different compilers/runtimes | Not caught |

Basis: derived, checked against the cases in Section 5.

Evidence that bears on the comparison:

- **Independent kernels are individually far from reliable, and a quorum is much better.** In the arena's published results (37 registered checkers, 265 tests of which 90 must be rejected), 9 of 37 checkers accept at least one known-bad export and 15 of the 90 bad exports are accepted by at least one checker; the official kernel, nanoda, Lean4Lean and the three con-* checkers reject every bad export they do not decline. Basis: execution by upstream (arena `results.json`, analysed here).
- **Common-mode failure is real.** The Lean fix for `is_prop` (pull request 14807) states: "The bogus proof was also accepted by nanoda, an independent implementation of the Lean kernel. We believe the lean4lean external kernel does not have this bug." A two-kernel quorum of the official kernel and nanoda would have passed a proof of `False`. Conversely the union-find cache bug (14806) and the `imax` bug (14613) were rejected by nanoda according to their fix descriptions. Basis: documentation (pull-request texts).
- **Derived implementations inherit bugs.** Lean4Lean's README warns it "likely shares some implementation bugs" with the C++ kernel; the arena catalogue repeatedly notes that "Nanoda and its descendants accepted this until it was fixed" for forks of nanoda. Independence is a property of provenance, not of language. Basis: documentation.
- **Faithfulness proofs find bugs without an exploit.** The Lean4Lean paper reports the `looseBVarRange` overflow as "a nice example of a bug that was found entirely theoretically, by failing to prove a theorem and working backwards to an actual exploitable soundness bug"; Lean issue 10475 ("Kernel bug: collecting fvars in `infer_let`") is described by its reporter as "the second kernel bug discovered by Lean4Lean verification", and no exploit was found for it. N-version checking needs a triggering input; a proof does not. Basis: documentation.

**What mutual verification adds over N-version checking**: universal quantification over inputs, and a machine-readable statement of exactly what was assumed. **What it costs**: a formal `Deriv_L` (or model) that is itself trusted, and proof effort that roughly doubles the code (Section 6). **What N-version adds over mutual verification**: independence from any shared formal specification's *formalization errors* and from the host checker; it is the only one of the two that works today for the whole of Lean, Rocq's `.vo` files, or Metamath. They are complements: the Lean reference manual's highest validation level combines a pinned statement file, sandboxed build, export, and "several independently-written kernels", and lists as remaining assumptions "The soundness of Lean's logic" and "There is no implementation bug affecting all of the used checkers simultaneously." Basis: documentation.

**Binary-level trust.** Diverse Double-Compiling (Wheeler 2009) addresses only the last row: compile the compiler's source with a second, trusted compiler, use the result to compile the compiler under test, and compare bit-for-bit with the shipped binary. In the dissertation's words: "If the DDC result is bit-for-bit identical with the original compiler-under-test's executable, and certain other assumptions hold, then the compiler-under-test's executable corresponds with its putative source code." It establishes source/binary correspondence, never source correctness, and the dissertation demonstrates it on four compilers including GCC. For checkers the alternatives seen in the examined systems are: state the theorem about the binary (Metamath Zero's `Verifier: string` ELF; the arena's description of con-agua: "The code the CPU executes is the code the theorem is about, so neither a compiler nor a language runtime is trusted; what is trusted is Kraken's x86 semantics, the assembler and loader, and the C harness"), or run the same verified algorithm through two toolchains (the arena's description of con-ron: "a proof accepted by both is protected against a bug in Lean's compiler or runtime — the bignum library included"). Basis: documentation (dissertation abstract; arena checker descriptions, not independently examined).

### 5. Test cases: documented kernel soundness bugs against each technique

Legend for the last three columns: **yes** = the technique's success condition is contradicted by the bug, so it must surface; **no** = the bug is invisible to it by construction; **if…** = conditional. Verdicts are derived unless the cited record states the outcome (marked *stated*). "(a)" is a completed faithfulness proof of that kernel against its written rules; "(b)" is a model/soundness proof of the rules; "N-ver" is re-checking the offending artifact with an independently written kernel.

| # | Record | Mechanism (per the record) | Class | (a) | (b) | N-ver |
|---|---|---|---|---|---|---|
| L1 | Lean 4 pull request 8554 "fix: soundness bug in {Expr, Level}.data" (2025-05-30); Lean4Lean paper §4.1 | Cached per-expression bit-field: on overflow `panic!` "does not abort execution, and lean continues with the default value", so `hasLooseBVars`, `hasFVar`, … stop being conservative | Fixed-width cache in implementation | **yes** — *stated*: found "by failing to prove a theorem" | no | if the other kernel does not share Lean's `Expr` data field (not confirmed) |
| L2 | Lean 4 issue 10475 → fix 10476 (2025-09-20) | `infer_let` "does not take into account dependencies in the type of a let binding" | Scoping slip | **yes** — *stated* ("second kernel bug discovered by Lean4Lean verification") | no | unknown: no exploit was constructed |
| L3 | Lean 4 issue 10577 (2025-09-26, "discovered via fuzzing"); arena `bugs/constlevels` | `unfold_definition` fails on a wrong level-parameter count and the caller reads the empty result: "Kernel accesses uninitialized memory" | Memory unsafety of the implementation language | yes, and a memory-safe host removes the class | no | **yes** — arena: all 36 non-declining checkers reject |
| L4 | Lean 4 issue 14484 → fix 14498 (2026-07-22) | "The checked kernel path for `Declaration.opaqueDecl` does not reject free or metavariables in the declaration body"; with the inference cache this yields `False`; "Fresh replay exits successfully" | Missing guard | yes (closedness is a premise of the typing judgment) | no | yes if the other kernel checks closedness; same-kernel replay: **no** — *stated* |
| L5 | Lean 4 issue 14576 → fix 14577 (2026-07-28); arena `bugs/nested-unused-param` | A parameter of a nested inductive application is never type-checked because it "does not occur in the auxiliary declaration"; payload hidden behind an expression-hash collision | Missing guard in inductive-type admission | yes | no | **yes** — arena: 32 reject, 1 accepts, 3 decline, 1 times out |
| L6 | Lean 4 pull request 14613 (merged 2026-07-31); arena `bugs/proj-of-imax-prop` | A type in `Sort (imax 1 0)` "was not recognized as a proposition, so the kernel allowed a non-proof field to be projected out of a proof" | Syntactic test where a semantic one is required | yes | no | **yes** — *stated*: "nanoda rejects it" |
| L7 | Lean 4 pull request 14806 (merged 2026-08-18); arena `bugs/rec-missing-ih`, `bugs/proj-of-stuck-prop` | Successful `is_def_eq` results were cached in a union-find; because the implemented relation is "sound but incomplete, and therefore not transitive", the closure made answers depend on query order; affected "v4.28.0, v4.29.1, v4.33.0 and nightly-2026-08-01" | Optimization relying on a property the algorithm lacks | yes (cache soundness lemma is unprovable) | no | **yes** — *stated*: "Both exploits are also caught by nanoda"; same-kernel replay **no** — *stated*: affected kernels "re-derive the same broken recursor when replaying the export data" |
| L8 | Lean 4 pull request 14807 (merged 2026-08-18); arena `bugs/proj-of-subst-prop`, `bugs/rec-of-subst-prop` | `is_prop` returned `false` for a stuck (non-sort) inferred type "instead of treating the term as ill-formed", skipping the proof-irrelevance guard on projections | Missing error path | yes | no | **no for {official, nanoda}** — *stated*: "also accepted by nanoda"; yes for Lean4Lean per the same text ("We believe…") |
| L9 | Lean 4 issues 15908 (2026-10-24) and 15704 (2026-10-15), both closed as not kernel bugs | Native `Nat.add` reduction and annotation stripping dispatch on constant *names*; an export that redefines them proves `False`. Maintainers: "the C++ kernel assumes the official prelude and makes no guarantees if you replace prelude definitions" | Shared boundary assumption | only if the prelude is inside the theorem (Lean4Lean's `Primitive.checkDef`; con-leche compares `Nat` operations with pinned definitions) | no | no for kernels that copy the assumption; the statement-comparison tool rejects it — *stated*: "Const does not match between challenge and target 'Nat.add'" |
| R1 | Rocq `critical-bugs.md`: "guard condition was unknown to be inconsistent with propositional extensionality in library Sets" (fixed 28 Oct 2014) and its variant fixed in 9.0.1 | "not a bug per se but an incompatibility discovered late"; "technically speaking from V6.1" | **Specification of `L`** (rule × axiom) | **no** (MetaRocq *postulates* guard correctness) | **yes** in principle | **no** |
| R2 | ibid.: "VM conversion of stuck matches shifted the arguments of constructors with extended tags" (issue 22760; V8.5–V9.3.0; fixed V9.4) | Bytecode machine mis-indexes for inductives "with at least 246 non-constant constructors" | Auxiliary reduction engine | yes if that engine is in the proof; the MetaRocq checker does not use it | no | yes for any checker not using the VM (`coqchk` affected "only when using -bytecode-compiler yes") |
| R3 | ibid.: "conversion under contexts is done in the wrong environment" (issue 22378; 8.14–9.2.0) | Core lazy conversion | Core conversion slip | yes | no | not by `coqchk` — *stated*: "impacted coqchk versions: same" |
| R4 | ibid.: "translation of identifiers from Coq to OCaml was not injective" (issue 22364; V8.5–V9.2.0) | Native-compilation name mangling collides | Checker's use of a host compiler | only if compilation is modelled | no | yes — *stated*: `coqchk` "none (no native computation in coqchk)" |
| R5 | ibid.: "buffer overflow on large records and closures" (OCaml issue 6385, Rocq issue 13439; "impacted versions: 8.1-NOW", "fixed in: NONE") | Host-runtime size limit reached from the VM | Runtime of the checker binary | no | no | yes for checkers without that runtime path |
| R6 | ibid.: "deserialization of .vo data not properly checked" (8.10–8.18.1) and "rocqchk trusts the serialized VM bytecode segment" (issue 22352; 8.20–9.3) | The re-checker trusts structure of its input file | Input trust of the re-checker | no | no | yes if the second checker reads a different, validated format |
| R7 | ibid.: "Incorrect specification of PrimFloat.leb" (issue 12483; 8.11.0–8.11.2; "fixed by fixing the spec") | Axiomatized primitive stated wrongly | **Specification** of a primitive | no | yes (model of floats) | no |
| A1 | Agda issue 5706 (2021-12-22; closed by pull request 5707) | `Set₁₈₄₄₆₇₄₄₀₇₃₇₀₉₅₅₁₆₁₅ : Set₀` accepted under `--safe`: universe level `2^64 − 1` wraps, giving Russell's paradox | Fixed-width arithmetic | yes | no | unsupported: no second Agda kernel was identified |
| A2 | Agda issue 4606 (2020-04-19; closed 2020-05-11) | "The combination of Cubical Agda with inductive families is logically inconsistent" | Specification (feature interaction) | no | yes | no |
| A3 | Agda issue 3026 (opened 2018-04-05, still open) | Well-founded induction on `Size` with `∞ < ∞` | Specification | no | yes | no |
| A4 | Agda issue 2169 (2016-09-08) | `0.0 ≡ -0.0` by `refl`, while `1.0 / x < 0.0` distinguishes them | Specification of a primitive vs. host semantics | no | yes | no |
| H1 | HOL Light `CHANGES`, "Thu 28th Mar 96 thm.ml" | Definitions allowed type variables in the body that are not in the constant's type | Missing side condition of a rule | yes if definitions are in the proved kernel (they are in Candle; they are excluded from `Model/`) | yes | yes |
| H2 | ibid., "Fri 19th Jul 03 term.ml" ("the first soundness bug since 1996", found by Tom Hales) | In `inst`, "The "unchanged" short-circuiting was bypassing the test for consistency with the environment" | Variable capture | yes | no | yes |
| H3 | ibid., "Mon 1st Sep 03 term.ml" (found by Bob Solovay) | "an asymmetry in the way alpha-conversion made its tests" | Variable capture | yes | no | yes |
| H4 | HOL4 issue 2024 (2026-07) | `Term.read_raw` builds a term with a dangling bound-variable index; `BETA_CONV` then captures; `⊢ F` | Unchecked constructor reachable through the kernel's interface | yes **only if** the proof covers every exported entry point (Candle's invariant ranges over all values a user program can obtain) | no | yes |
| H5 | HOL4 issues 1870 (2026-03) and 2042 (2026-08) | Redefinition of constants of theory `bool`; a type with variables "marked GRND" so `Term.inst` skips it | Definitional/signature bookkeeping | yes with the same proviso | no | yes |
| H6 | Kunčar and Popescu 2015 (Isabelle/HOL) | Overloaded constant definitions combined with type definitions admitted a cyclic, inconsistent definition | **Specification** (definitional mechanism) | no | yes — the paper's contribution is the consistency argument | no |

Reading the table by column:

- **(a) alone** would have caught every implementation-class row (L1–L8, R2–R3, A1, H1–H5 with the stated provisos) and none of the specification rows (R1, R7, A2–A4, H6) or boundary rows (L9, R4–R6).
- **(b) alone** catches exactly the specification rows, and nothing else.
- **N-version** catches most implementation rows *when a triggering artifact exists and the second kernel is truly independent*; it misses L8 for the pair that was actually deployed, is unavailable for Agda, and for Rocq is weakened because the standard re-checker shares the kernel code (R3).
- The rows nobody catches by default (L9, R5) are the ones where every party trusts the same thing: a prelude, a runtime.

### 6. Cost and footprint (L1–L6)

Measured values are from the pinned trees or from upstream-published measurements; nothing here was benchmarked by this report.

| Level | What was found | Basis |
|---|---|---|
| **L1 authoring** | Lean4Lean: 44,149 non-blank lines under `Lean4Lean/`, of which `Theory` 6,079 and `Verify` 21,649; the remaining 16,421 include the kernel, tests and experiments — the (incomplete) specification-plus-proof is about 1.7× everything else. Lean's C++ kernel: 34 files, 7,868 lines (7,113 non-blank) under `src/kernel`. `mm0-c`: 1,388 lines in its four `.c` files; README: "under 3,000 lines of C". con-leche's README: implemented and proved by an AI model "under heavy supervision" by one engineer; person-hours and token budgets are not published. Latency from defect to fix: Rocq R1 was latent from V6.1 until 2014 and its variant until 9.0; Lean L7 spanned at least v4.28.0–v4.33.0. | source (line counts, Evidence E2/E10); documentation |
| **L2 toolchain build** | Milawa README: building "takes several hours, requires a lot of memory and hard disk space", with a parallelism rule of "No more than (Physical_Memory / 4 GB)". The HOL4 proof's runtime must process Milawa's bootstrap, "a 4-gigabyte input". Build cost of MetaRocq, Candle, con-leche: not examined. | documentation |
| **L3 elaboration / interactive latency** | Not examined; the checkers studied are batch kernels. | — |
| **L4 generated-code performance** | Known not to apply: a checker emits a verdict. (MetaRocq's verified erasure pipeline is out of scope.) | — |
| **L5 checking speed** | Lean4Lean paper, Figure 2 (single-threaded, 12th Gen Intel i7-1255U): Lean core 37.01 s (C++ kernel via `lean4checker`) vs 44.61 s (Lean4Lean), ratio 1.21; Batteries 32.49 s vs 45.74 s, 1.40; Mathlib 44.54 min vs 58.79 min, 1.32. Arena `results.json` (runs dated 2026-11-14) on the Mathlib export (5.9 GB, 112.1 M lines): official kernel 2,696 s wall on one thread; nanoda 442 s wall / 1,475 s CPU; con-leche 206 s wall / 801 s CPU; con-ron 178 s / 551 s; con-agua 167 s / 569 s. con-leche `PERF.md` (measured by upstream at an earlier commit `a0f1865a`): user-mode instructions on Mathlib 10.26 T (official v4.33.0), 6.40 T (`--trusted`), 7.05 T (`--verified`): the proof-driven extra checks cost a factor 1.10; check phase 834.0 s on one worker, 169.2 s on four, 88.5 s on eight. | documentation (upstream measurements) |
| **L6 memory / artifact size** | Same sources: peak resident memory on Mathlib 9.91 GiB (official), 5.95 GiB (nanoda), 4.83 GiB (con-leche), 4.42 GiB (con-ron), 11.63 GiB (con-agua); `PERF.md` records the Mathlib export stream as 6,069,002,157 bytes. Binary sizes, energy: not examined. | documentation |

In these measurements con-leche and its ports are faster than the unverified reference kernel, and the partially verified Lean4Lean is within a factor of 1.4 of it; the cost of verification is paid mainly in L1, not L5.

### 7. Human comprehensibility and conceptual simplicity (C1–C2)

**C1 — what a reader must hold in mind.** Four facts decide what a "verified checker" claim means, and none is visible from the word "verified": the host, the hypothesis, the property, the residue (Section 1). Hazards observed in the records:

- *"No axioms" is not "no bug"*: the exploit reports for L4 and L5 both end with Lean printing "does not depend on any axioms" for a proof of `False`. Axiom audit and kernel faithfulness are orthogonal.
- *The hypothesis can be read only by a specialist*: `NormalizationIn`, `[SetTheory V]` with Tarski-style universes, and `is_set_theory` are each one line, but judging them requires knowing that they are strictly stronger than the object logic. A non-specialist can still check the *shape*: the theorem must have a hypothesis of this kind, and if it does not, either the object is a strict fragment or something is wrong (Section 2).
- *Fusion trades auditability of rules for auditability of one theorem*: con-leche's reader checks `Model V env` ("every constant in the environment denotes a member of its type's denotation"); MetaRocq's reader checks a typing relation of PCUIC. The first is closer to mathematical practice, the second to the implementation.
- *The statement is outside every theorem*: the Lean reference manual says "Lean can establish that a statement has been proven, but not whether it is the intended statement." Metamath Zero answers with a separate specification file "built to be read".

**C2 — one abstraction instead of several.** Rings, towers, self-verification, external verification and N-version checking are all instances of `A ⊢_H Accept_C(x) → P(x)`; they differ only in `H`, `A`, `P`. The distinctions "self vs. external" and "ring vs. chain" carry no information once `A` and `P` are stated; the single rule that matters is: **cycles are admissible only for `P = Deriv`**. The Lean prelude exception (L9) becomes an ordinary case once the prelude is treated as input to be checked rather than as ambient truth, which is what Lean4Lean's `Primitive.checkDef` and the statement-comparison tool do; the complexity does not vanish but moves into an explicit, testable check. con-leche's "certification tax" is the honest form of such a move: extra comparisons that exist only because the proof needs them, with a switch (`--trusted`) to measure their cost.

### 8. How the claims themselves are validated (V1–V4)

| Axis | Applicable evidence | Gaps |
|---|---|---|
| **V1 specification adequacy / non-vacuity** | Only technique (b) validates the rules of `L`; rows R1, R7, A2–A4, H6 are what happens without it. con-leche guards vacuity of its corollary by hard-coding the meaning of `False` ("no tricks involving odd definitions for `False` will confuse the checker"). The arena's 90 must-reject exports act as a kill suite for kernels. | Mutation of a formal `Deriv_L` to see whether the faithfulness proof notices: not examined. Property-based generation of counterexamples to typing rules: not examined. |
| **V2 checker fuzzing / differential testing** | L3 was "discovered via fuzzing"; several arena entries were "Found by a differential run of Pestka against other checkers"; L7 and L8 were reported from an AI-driven exploit search (pull request 14806: "reported by Daniel Selsam (OpenAI) using their internal models"); Rocq's list attributes five entries to "OpenAI". | No coverage or kill-rate figures are published for any kernel. |
| **V3 concurrency, crash, silicon** | The Lean manual says replaying with `lean4checker` protects against "Bugs in Lean's core handling of the kernel's state (e.g. due to parallel proof processing, or import handling)". con-leche's driver theorem assumes files do not change during the run; the arena's con-agua entry says its threaded mode "takes the harness's thread scheduling as hypotheses". | Weak-memory model checking, power-cut fault injection, side-channel and glitch testing: known not to apply to the soundness claims studied, or not examined. Silent hardware faults during checking: not examined in this report. |
| **V4 real-world intent and human comprehension** | Statement fidelity is handled procedurally (trusted challenge file compared with the solution; "attempts at cheating in the solution by changing notation are caught"). | No empirical study of whether users correctly interpret relativized soundness theorems was found. Signal-temporal-logic falsification and hardware-in-the-loop replay: known not to apply. |

## Boundaries

- **Not examined**: Isabelle's sources and changesets (H6 rests on the cited paper only); CakeML's compiler correctness and bootstrap proofs; the internals of con-ron and con-agua (characterized only through the arena's checker descriptions); whether any examined kernel bug was caused by a C++/OCaml compiler miscompilation — none of the records read attributes a bug to one, but the search was not exhaustive; build and proof-checking times of MetaRocq and Candle; theories below Robinson's `Q` or with non-standard provability predicates, to which the no-ring derivation does not apply as stated.
- **Unknown**: which change actually landed for L1 (the page of pull request 8554 shows it closed rather than merged; a same-day pull request 8559, "fix: block adversarial exploit of non-aborting `assert!`", exists and the Lean4Lean paper describes the eventual fix as making the data field opaque and moving the panic into C++); whether L1 and L2 would have been rejected by nanoda or other independent kernels (no exploit artifact was located for L2); whether Lean4Lean was affected by L7; whether con-leche's and MetaRocq's formal hypotheses are the weakest that suffice (con-leche lists weakening the ω-chain as future work).
- **Known not to apply**: the no-ring result does *not* forbid rings of faithfulness proofs, proofs of consistency of proper fragments (HOL without infinity; Lean with boundedly many universes), or a stronger system proving a weaker one sound. A proof of `no_False_declaration` does not show that Lean is consistent: it shows that *if* the assumed set-theoretic universe exists then this checker rejects proofs of `False`.
- **Unsupported**: N-version re-checking for Agda (no independent kernel identified); independent re-checking of Rocq through `coqchk` for core-conversion bugs (it shares the kernel code, R3).
- **Stronger conclusions the evidence does not establish**: that verified checkers are bug-free (their residues — drivers, runtimes, prelude handling — are where L9, R4–R6 live); that a quorum of today's Lean kernels is sound (their own documentation lists a common-mode bug as a remaining assumption, and L8 is an instance); that the verdict columns of Section 5 were observed (only entries marked *stated* were); that the toy frame check proves the no-ring result (it is a bounded sanity check of the modal skeleton).

## Evidence

Evidence was acquired in one session on 2026-11-20 between 00:25 and 02:00 UTC (2026-11-19 in US time zones, the date recorded in the metadata). Issue and pull-request pages are mutable and were read on that date.

- **E1 MetaRocq** `MetaRocq/metarocq@51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`: `README.md` (PCUIC property list; Safe Checker and Quotation sections), `pcuic/theories/PCUICSN.v` (comment and `Class NormalizationIn`, `Class Normalization`), `pcuic/theories/PCUICGuardCondition.v` (`Class GuardCheckerCorrect`), `pcuic/theories/README.md` ("[PCUICSN] | Axiom of normalization", "[PCUICGuardCondition] | Axioms on the stability of the guard condition").
- **E2 Lean4Lean** `digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`: `README.md`, `divergences.md` (`Primitive.checkDef` entry: "Lean does not check that primitives are declared with the correct types and definitional behavior … This is required for soundness, but Lean is able to get away with it because Lean ships its prelude and using an alternative prelude is not supported"), `bugs-found.md` (lists Lean issues 10475 and 10511), `Lean4Lean/Verify/Axioms.lean`. Counts: `find Lean4Lean -name '*.lean' | xargs cat | grep -cve '^\s*$'` → 44149 (and per directory); `grep -rwn sorry Lean4Lean/Verify | wc -l` → 18; same for `Theory` → 9. Paper: arXiv 2403.14064v3 (abstract; §4.1 "Bit tricks and soundness bugs"; termination discussion; Figure 2).
- **E3 con-leche** `leanprover/con-leche@cd2eceab2e9b10404c663b468639c8aa99d0d1f2`: `README.md`, `ConLeche/MainTheorem.lean` (`model_exists` at lines 102–105, `no_False_declaration` at 116–123), `ConLeche/SetTheory/Core.lean` (`IsTGUniverse`, `class SetTheory`), `bridge/lean4lean-model/ConLecheBridge/Carneiro.lean` (`carneiro_implies_conleche`, `#print axioms` guard), `PERF.md`.
- **E4 CakeML** `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`: `candle/README.md`, `candle/prover/candle_prover_semanticsScript.sml` (`events_of_semantics`), `candle/prover/candle_prover_invScript.sml` (`ok_event_def`), `candle/standard/semantics/holConsistencyScript.sml` (`fhol_consistent`, `hol_has_model`, `hol_consistent`), `candle/standard/semantics/README.md`, `candle/set-theory/setSpecScript.sml` (`is_set_theory_def`, `is_infinite_def`).
- **E5 HOL Light** `jrh13/hol-light@1a0c0e6b182cd9e271946ba8d78f7942619f4acb`: `CHANGES` entries dated "Thu 28th Mar 96", "Fri 19th Jul 03", "Mon 1st Sep 03"; `Model/make.ml` header.
- **E6 HOL4** `HOL-Theorem-Prover/HOL@0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`: `examples/theorem-prover/README`; issues 1870, 2024, 2025, 2042.
- **E7 ACL2** `acl2/acl2@08bec1884997560686932229dbfe458c1bba34bf`: `books/projects/milawa/README`, `books/projects/milawa/ACL2/README`.
- **E8 Metamath Zero** `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`: `README.md`, `examples/verifier.mm0` (29 lines), `mm0-c/{main,verifier,types,index}.c` (79 + 819 + 329 + 161 lines).
- **E9 Provability-logic probe** (toy model; standard-library Python 3.13). Formulas are evaluated at every world of every finite frame of the stated class up to the bound; the single-modality class is transitive irreflexive frames (for which the logic GL is sound and complete), the multi-modal class additionally requires `Rⱼ;Rᵢ ⊆ Rᵢ` for `i ≠ j`.

```python
import itertools
def strict_orders(n):
    pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        R = {p for p, b in zip(pairs, bits) if b}
        if all((a, c) in R for (a, b) in R for (b2, c) in R if b == b2) and not any((b, a) in R for (a, b) in R):
            yield frozenset(R)
def ev(f, w, Rs, val):
    t = f[0]
    if t == 'bot': return False
    if t == 'p': return w in val
    if t == 'not': return not ev(f[1], w, Rs, val)
    if t == 'imp': return (not ev(f[1], w, Rs, val)) or ev(f[2], w, Rs, val)
    if t == 'and': return ev(f[1], w, Rs, val) and ev(f[2], w, Rs, val)
    if t == 'box': return all(ev(f[2], v, Rs, val) for (u, v) in Rs[f[1]] if u == w)
bot, p = ('bot',), ('p',)
Not = lambda f: ('not', f); Imp = lambda f, g: ('imp', f, g); And = lambda f, g: ('and', f, g)
Box = lambda i, f: ('box', i, f); Con = lambda i: Not(Box(i, bot))
def valid_mono(f, N):
    for n in range(1, N + 1):
        for R in strict_orders(n):
            for k in range(n + 1):
                for s in itertools.combinations(range(n), k):
                    for w in range(n):
                        if not ev(f, w, {1: R}, frozenset(s)): return (n, sorted(R), s, w)
def bridge_ok(Ri, Rj): return all((u, w) in Ri for (u, v) in Rj for (v2, w) in Ri if v == v2)
def valid_poly(f, N, k, bridged=True):
    count = 0
    for n in range(1, N + 1):
        orders = list(strict_orders(n))
        for Rs in itertools.product(orders, repeat=k):
            if bridged and not all(bridge_ok(Rs[i], Rs[j]) for i in range(k) for j in range(k) if i != j): continue
            count += 1
            for w in range(n):
                if not ev(f, w, {i + 1: Rs[i] for i in range(k)}, frozenset()): return count, (n, [sorted(R) for R in Rs], w)
    return count, None
print('Loeb       ', valid_mono(Imp(Box(1, Imp(Box(1, p), p)), Box(1, p)), 4))
print('G2         ', valid_mono(Imp(Con(1), Not(Box(1, Con(1)))), 4))
print('explosion  ', valid_mono(Imp(Box(1, bot), Box(1, Imp(Box(1, p), p))), 4))
print('reflection ', valid_mono(Imp(Box(1, p), p), 4))
print('consistency', valid_mono(Con(1), 4))
two = Imp(And(Box(1, Con(2)), Box(2, Con(1))), Box(1, bot))
three = Imp(And(And(Box(1, Con(2)), Box(2, Con(3))), Box(3, Con(1))), Box(1, bot))
print('2-ring     ', valid_poly(two, 4, 2)); print('3-ring     ', valid_poly(three, 3, 3))
print('2-ring, no bridge', valid_poly(two, 3, 2, bridged=False))
```

  Observed: `Loeb`, `G2`, `explosion` → `None` (no countermodel up to 4 worlds); `reflection` and `consistency` → countermodel at the one-world frame; `2-ring` → `(9982, None)`; `3-ring` → `(1151, None)`; `2-ring, no bridge` → `(7, (2, [[(1, 0)], [(0, 1)]], 1))`, i.e. a two-world countermodel at world 1. Run time under one second.

- **E10 Lean 4** `leanprover/lean4@5a82f1a47fbc2323ad6be6b11a7c0522dd4f3e68`: `src/kernel` holds 34 `.cpp`/`.h` files, 7,868 lines. The post-fix guard reads, at `src/kernel/type_checker.cpp` lines 371–377: `bool type_checker::is_prop(expr const & e) { expr s = ensure_sort(infer_type(e)); … return normalizes_to_zero(sort_level(s)); }` with the comment "Comparing `s` against `Prop` syntactically instead would let `infer_proj` extract non-proof data out of a proof, contradicting proof irrelevance." Name-based dispatch is visible at line 675: `if (f == *g_nat_add) return reduce_bin_nat_op(nat_add, e, /* check_size */ true);`. Records read: pull requests 8554, 14613, 14806, 14807, 16353; issues 10475 (closed by 10476), 10577, 14484 (closed by 14498), 14576 (closed by 14577), 14875, 15100, 15101, 15704, 15908. Fix pull requests 10476, 14498 and 14577 are known from the closing events and commit titles on those issue pages, not from their own pages.
- **E11 Lean Kernel Arena** `leanprover/lean-kernel-arena@0ddd55b91d6bc604ae0d14833bad60cc27e51268`: `README.md` (meaning of `tests/bugs/`), `tests/bugs/*.yaml` descriptions (30 test definitions, each stating where the bug was found), `checkers/*.yaml` (37 checkers). Published `results.json` (meta: generated from this revision; 37 checkers, 265 tests, 9,805 results) was analysed with a short script counting results with `status == "accepted"` and `correctness == "incorrect"` per checker and per test, and reading `wall_time`, `cpu_time`, `max_rss` for the `mathlib` test.
- **E12 Rocq** `rocq-prover/rocq@25f5b18a320e4796f181f938d3b74bebe7db4dc4`: `dev/doc/critical-bugs.md` (1,421 lines; entries quoted by title in Section 5).
- **E13 Agda** `agda/agda@11f7300c8303608196e620714100a056e8c1ed0f` identifies the tree; issues 2169, 3026, 4606, 5706 were read on the tracker (103 issues carried the label `false` on the observation date).
- **E14 Literature**: Löb 1955 (metadata confirmed through Crossref); Wheeler, arXiv 1004.5534v1 (abstract quoted); Davis and Myreen 2015; Harrison 2006; Kunčar and Popescu 2015 (metadata confirmed through Crossref; contents summarized, not re-derived); Abel and Coquand (cited by the Lean4Lean paper for non-termination); the Lean reference manual page "Validating a Lean Proof" (rendered "latest" page, not version-pinned — its wording may change).

## Revalidation

- **Is a self-verification claim still relativized?** In each tree, search for the hypothesis rather than the conclusion: `grep -n "NormalizationIn" pcuic/theories/PCUICSN.v`; `grep -n "SetTheory V" ConLeche/MainTheorem.lean`; `grep -n "is_infinite" candle/standard/semantics/holConsistencyScript.sml`. If a full-strength consistency theorem ever appears *without* such a hypothesis, Section 2 says to suspect the statement (a fragment, a weakened provability notion) before celebrating.
- **Has a partial proof been completed?** `grep -rwn sorry Lean4Lean/Verify Lean4Lean/Theory | wc -l` in Lean4Lean; in Metamath Zero check whether `examples/verifier.mm1` exists and whether `compiler.mm1` still admits `sorry`.
- **Has the Lean kernel become the proved checker?** Check the state of Lean 4 pull request 16353 and whether `src/kernel/type_checker.cpp` still exists.
- **Is the quorum still clean?** Download the arena's `results.json` and count results with `status == "accepted"` and `correctness == "incorrect"` for the kernels you rely on; any non-zero count for a kernel in your quorum is a live common-mode risk.
- **New test cases**: re-read `dev/doc/critical-bugs.md` (Rocq), the arena's `tests/bugs/` directory (Lean), and Agda's `false` label; classify each new entry with Section 5's three questions — is the written rule wrong, is the code unfaithful to the rule, or is a shared boundary assumption violated?
- **The logic**: rerun the probe in E9; it must print no countermodel for the three valid formulas and the two ring formulas, and countermodels for reflection, consistency and the unbridged ring. It checks only the modal skeleton; the arithmetical derivation in Section 2 must be re-read, not re-run.
