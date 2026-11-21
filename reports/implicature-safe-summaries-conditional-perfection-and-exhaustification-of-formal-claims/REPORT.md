# Implicature-safe summaries: conditional perfection and exhaustification of formal claims

## Summary

This package models, in Lean 4 without Mathlib, when a one-sentence rendering of what a technical report proves (a summary bullet, a headline, a result-card line) is safe to publish. A rendering σ is *literally safe* for a report E exactly when E entails σ over the listed worlds of a finite model space. It is *strengthening-safe* exactly when E also entails every reading that a stated default reader draws from σ. The reader has three rules: conditional perfection (`∀x, A → B` read as `∀x, A ↔ B`), exhaustification by innocent exclusion (stronger alternatives read as false), and qualifier dropping (`∀x, H ⇒ A` read as `∀x, A`). Each rule can be disabled by an out-of-band blocker flag, and a reading inconsistent with σ is cancelled.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

How to read the list below. Each item is a card's plain-language claim, followed by a bracketed note on what it does not say. Unless an item says "iff" or "exactly", it states sufficient conditions, and its converse is neither claimed nor refuted here. An item that exhibits instances ("there are", "in the space S22") does not claim the corresponding "not all" or "in general" reading unless the bracketed note says so. "Reader" without qualification means the one-step reader `readings` with the standard alternatives `stdAlt`. Non-claims are listed first under **Boundaries**; a non-claim reports that a statement is not shown here, and such a statement is not shown, and not refuted, unless a theorem is cited for its failure. Every item is a statement about the toy model; it neither establishes nor refutes the corresponding claim about real readers or real summaries (see **Applicability**).

**Literal safety versus strengthening safety.**

- **1. `literal-safety-does-not-imply-strengthening-safety`.** For the one-step reader `readings` with the standard alternatives `stdAlt` and no blocker flags, there are consistent reports E and renderings σ with E ⊨ σ (literal safety) for which the reader draws a reading that E contradicts: (i) perfection, in the 16-world space S22: E proves ∀x, A→B and refutes ∀x, B→A, and the reading ∀x, A↔B is drawn; (ii) exhaustification, in the 4-world space S12: E proves ∀x, A, and the reading of ∃x, A equivalent to (∃x, A) ∧ ¬(∀x, A) is drawn; (iii) qualifier dropping, in the 64-world space S32: E proves ∀x, H⇒A and refutes ∀x, A, and the reading ∀x, A is drawn. (An existence claim about three instances. The stronger reading "every literally safe rendering is strengthening-unsafe" is false in this model: `blockers_sound`, and the unflagged safe rendering in `blocker_conjunct_drop_breaks_strengthening_safety`.)
- **2. `literal-safety-closed-under-literal-weakening`.** For every finite space S, report E and claims σ, σ': if E ⊨ σ and σ ⊨ σ' over the listed worlds, then E ⊨ σ'. (Sufficient conditions; the converse is neither claimed nor refuted here. Each hypothesis is tight: without it the conclusion can fail, `literal_weakening_tight_hsafe`, `literal_weakening_tight_hweak`.)
- **3. `dropping-a-blocking-conjunct-breaks-strengthening-safety`.** For the one-step reader with the standard alternatives and no blocker flags, in the 16-world space S22: the rendering σ = (∀x, A→B) ∧ ¬(∀x, B→A) is strengthening-safe for the report E = [σ], and its perfected reading (∀x, A↔B) ∧ ¬(∀x, B→A), generated at the first conjunct, is inconsistent with σ and is not drawn (cancellation); while its literal weakening ∀x, A→B (σ ⊨ ∀x, A→B) is not strengthening-safe for the same E. (One instance; no general claim about which conjuncts block which readings.)

**Exhaustification operators.**

- **4. `naive-exhaustification-of-disjunction-inconsistent`.** In the 4-world space S21, for the satisfiable disjunction p ∨ q (p = P0(0), q = P1(0)) with the explicitly supplied alternatives p, q, p ∧ q: naive exhaustification negates all three alternatives and is unsatisfiable, while innocent exclusion negates exactly one alternative, p ∧ q (the computed list `ieList` is [p ∧ q]), and yields the satisfiable exclusive disjunction (p ∨ q) ∧ ¬(p ∧ q). With the alternative list [p, q] (no conjunctive alternative), naive exhaustification is still unsatisfiable, while innocent exclusion negates nothing and is equivalent to the inclusive p ∨ q. (Two instances with explicitly supplied alternatives.)
- **5. `innocent-exclusion-consistent`.** For every finite space S, every finite alternative list A and every claim σ: if σ is satisfiable in S, then exh S A σ is satisfiable in S, where exh S A σ is σ together with the negation of every alternative in the computed list ieList S σ A (which agrees with innocent excludability in Fox's sense by innocent-exclusion-computed-by-maximal-falsified-sets). (Sufficient condition; the converse is neither claimed nor refuted here. Without the hypothesis the conclusion can fail: `innocent_exh_consistent_tight`.)
- **6. `innocent-exclusion-computed-by-maximal-falsified-sets`.** For every finite space S, prejacent σ, alternative list A and claim a: a ∈ ieList S σ A (that is, a ∈ A and a is false at every σ-world of S.worlds whose set of falsified alternatives is inclusion-maximal among the σ-worlds) iff a is innocently excludable in Fox's sense (a ∈ A and a belongs to every maximal subset of A whose negations are jointly consistent with σ). (A characterization: both directions are proved.)
- **7. `naive-exhaustification-entails-innocent`.** For every finite space S, alternative list A and claim σ: naive exhaustification of σ (σ and the negation of every alternative σ does not entail) entails innocent exhaustification of σ over the listed worlds. (One direction; the converse entailment can fail: `innocent_exh_not_entails_naive_exh`.)
- **8. `innocent-equals-naive-iff-naive-consistent`.** For every finite space S, alternative list A and claim σ: if σ is satisfiable in S, then innocent and naive exhaustification of σ are equivalent over the listed worlds iff naive exhaustification of σ is satisfiable. (The equivalence is claimed for satisfiable σ; for an unsatisfiable σ it can fail: `innocent_equiv_naive_tight`.)
- **9. `exhaustification-not-monotone-antitone-or-reflecting`.** With the standard alternatives in the 4-world space S12: ∀x, A entails ∃x, A, but neither exhaustified reading entails the other; and exh(∃x, A) entails exh(¬∀x, A) although ∃x, A does not entail ¬∀x, A. (Instances in one space with one alternative function.)

**Computed blockers.**

- **10. `computed-blockers-sound`.** For every finite space S, alternative function alt, report E and rendering σ: if E ⊨ σ, then flagging the computed blocker set blockers S alt E σ (the rules that contribute an uncancelled reading E does not entail) makes σ strengthening-safe for the one-step reader `readings`. (Sufficient condition; the converse is neither claimed nor refuted here. Without literal safety the conclusion can fail: `blockers_sound_tight`.)
- **11. `computed-blockers-minimal`.** For every finite space S, alternative function alt, report E, rendering σ and flag set F, for the one-step reader `readings`: (a) if σ is strengthening-safe under F, then F contains every rule of the computed blocker set; (b) if E ⊨ σ, then σ is strengthening-safe under F iff F contains every rule of the computed blocker set, so the computed blocker set is the least safe flag set (up to rule membership). (Both statements are for the one-step reader; (b) is claimed for literally safe σ and can fail without that hypothesis: `blockers_iff_tight_hlit`.)
- **12. `composing-reader-minimal-blockers-not-unique`.** With the standard alternatives in the 64-world space S32, for the report E_relCond (∀x, A→B; ∀x, H⇒(B→A); ∃x, B∧¬A) and the literally safe rendering ∀x, H⇒(A→B): the one-step blocker set is {exhaustification} and suffices for the one-step reader `readings`, but for the composing reader `readingsStar` it is insufficient, and among the eight flag sets the safe ones have exactly two minimal elements, {exhaustification, qualifierDrop} and {exhaustification, perfection}. (One instance. It refutes the general existence of a least safe flag set for the composing reader; it makes no claim about other renderings.)

**Compression of normal-form claims.**

- **13. `conclusion-dropping-preserves-literal-safety`.** For every finite space S, report E, hypothesis H and conclusion lists Cs, Cs': if E ⊨ nf H Cs (E proves ∀x, H ⇒ C for every C in Cs) and every member of Cs' is in Cs, then E ⊨ nf H Cs'. (Sufficient conditions; the converse is neither claimed nor refuted here. Each hypothesis is tight: `conclusion_dropping_tight_hE`, `conclusion_dropping_tight_hsub`.)
- **14. `compression-with-recomputed-blockers-safe`.** For every finite space S, alternative function alt, report E, list R of normal-form entries and compression comp, for the one-step reader `readings`: if E proves the normal-form claim of every entry of R, and comp is a conclusion-dropping compression of R (each compressed entry keeps the hypothesis of some entry of R, and each of its conclusions is a conclusion of that entry), then the rendering of comp is strengthening-safe (a) under the blocker set computed for that rendering relative to E, and (b) under the blocker set computed for that rendering relative to the normal-form claims of R alone. (Sufficient conditions for the one-step reader; the converse is neither claimed nor refuted here. Each hypothesis is tight: `compression_tight_hR`, `compression_tight_hcomp`.)
- **15. `inherited-blockers-can-be-insufficient-or-superfluous-after-compression`.** For the one-step reader with the standard alternatives: (i) in the 16-world space S22, for the report E_unc consisting of the normal-form claims ∀x, ⊤⇒(A→B) and ∀x, ⊤⇒(B∧¬A), the full rendering has an empty computed blocker set (its perfected reading is inconsistent with the rendering and is cancelled) and is strengthening-safe with no flags, while the compressed rendering ∀x, ⊤⇒(A→B) obtained by dropping the second conclusion has computed blocker set {perfection}: its perfected reading ∀x, ⊤⇒(A↔B) is drawn and is contradicted by E_unc, and the inherited (empty) flag set leaves it unsafe; (ii) in the 64-world space S32, for the report E_comp (∀x, H⇒A; ∀x, H⇒B; ∀x, A; ¬∀x, B), the full rendering has computed blocker set {qualifierDrop, exhaustification} and the compressed rendering ∀x, H⇒A has computed blocker set {exhaustification}: its exhaustified reading is equivalent to (∀x, H⇒A) ∧ ¬(∀x, A), is contradicted by E_comp, and does not entail "H is needed for A"; the inherited flags make the compressed rendering safe but include the unneeded qualifierDrop. (Two instances; inherited flags are not claimed to be always wrong: in (ii) they are sufficient.)
- **16. `hypothesis-dropping-literally-safe-iff-proved-where-hypothesis-fails`.** For every finite space S, report E, hypothesis H and conclusion list Cs: (a) if E ⊨ nf H Cs (E proves ∀x, H ⇒ C for every C in Cs), then the hypothesis-dropped rendering nf ⊤ Cs is literally safe iff E ⊨ nf (¬H) Cs (E also proves ∀x, ¬H ⇒ C for every C in Cs); (b) nf ⊤ Cs is literally safe iff E ⊨ ∀x, ⋀Cs. (The equivalence (a) is claimed for reports that prove nf H Cs; without that hypothesis it can fail: `hypothesis_dropping_tight_hE`.)

**Necessity words, tightness and disclaimers.**

- **17. `necessity-rendering-contradicted-iff-counterexample-proved`.** For every finite space S, report E and claims X, Y: the rendering "X is needed for Y", read literally as ∀x, Y→X, is contradicted by E iff E proves ∃x, Y ∧ ¬X. (A characterization: both directions are proved, with no further hypothesis.)
- **18. `tight-sufficient-hypothesis-not-needed-instances`.** (i) In a single interpreted world over the parameter values 0..7, with atom 0 read as "divisible by 4" and atom 1 as "even" (a single world, so the empty report already decides every claim): "divisible by 4 gives even" holds, "divisible by 4 is needed for evenness" is false, the hypothesis is tight for "under divisibility by 4, even" (1 is neither), and the exhaustified reading of that claim under the standard alternatives holds. (ii) In the 16-world space S22, the consistent report E_tight (∀x, A⇒B; ∃x, B∧¬A; ∃x, ¬A∧¬B) proves ∀x, A⇒B, proves that A is tight for it (which the empty report does not), and entails its exhaustified reading, yet contradicts "A is needed for B". In both instances the hypothesis is sufficient and tight, and "needed" is false. (Two instances; they show that tightness does not imply "needed", not that "needed" is false for every tight hypothesis.)
- **19. `disclaimer-read-as-refutation`.** For every finite space S, report E and claim c: (a) if the disclaimer "c is not shown" is true (E ⊭ c), then the reader rule "not shown ↦ false" makes it unsafe iff E leaves c open (neither proves nor refutes c); (b) the blocked disclaimer "c is not shown, and not refuted" is safe iff E leaves c open. (Statement (a) is claimed for true disclaimers; for a false disclaimer it can fail: `not_shown_tight_htrue`.)

**Universal conditionals.**

- **20. `nondegenerate-universal-conditional-unsafe-without-blockers`.** For the one-step reader `readings` with the standard alternatives `stdAlt`, every finite space S, report E and claims a, b: (a) if E is consistent, ∀x, a→b is consistent with its perfected reading ∀x, a↔b (PerfectionConsistent S a b), and ∀x, a→b is consistent with ¬∀x, b→a (ConverseExcludable S a b), then the rendering ∀x, a→b is not strengthening-safe for E without blocker flags; (b) if in addition E ⊨ ∀x, a→b, then its computed blocker set is {perfection} if E refutes ∀x, b→a, {exhaustification} if E proves ∀x, b→a, and {perfection, exhaustification} if E does neither; (c) if PerfectionConsistent S a b and E leaves ∀x, b→a open, then its computed blocker set is {perfection, exhaustification}. (Sufficient conditions; the converse of (a) is neither claimed nor refuted here, and each hypothesis is tight (counterexamples in card 20's ledger). For a report that proves ∀x, a→b, flagging the computed blocker set restores safety: `blockers_sound`; instances in `forall_conditional_safe_with_blockers`.)

## Applicability

**Model fidelity.** This is a toy model. Its parts and the real things they stand for:

- A `Claim` stands for a formal statement or its compressed rendering. Claims are built from uninterpreted atoms applied to one parameter argument, the connectives `∧ ∨ → ↔ ¬`, bounded quantifiers over a finite parameter list with a single bound variable (an inner quantifier shadows an outer one), and a hypothesis-relativized form `rel H C` (written `H ⇒ C`). `imp` and `rel` have the same truth conditions (material implication); they differ in which reader rules apply to them.
- A `Space` stands for the epistemic possibilities compatible with the background theory: an explicit finite list of worlds, a finite parameter list and a truth value for every atom at every parameter value in every world. "The report proves σ" is modeled as entailment from the report's list of established claims over the listed worlds.
- The reader stands for a human or automated reader who applies default pragmatic strengthenings to a summary. It is deterministic, has no context, background knowledge or probabilities, and applies three stated rules. Alternatives for exhaustification are generated by stipulated rules (`stdAlt`), not by a structural theory of alternatives.
- Blocker flags stand for explicit non-claims attached to a summary (for example "the converse is not claimed"). In the model they are out-of-band annotations with no truth conditions that disable exactly the rule they name.
- Disclaimers stand for sentences about the report ("X is not shown"); their reader is fixed by definition (`disclaimerReadings`).

**Known gaps.** Natural-language sentences are not parsed; the mapping from a real sentence to a `Claim` is outside the model. Real readers draw implicatures probabilistically and context-dependently; the model's rules always fire unless blocked or cancelled. The alternative set strongly affects exhaustified readings (see the shared non-claims under **Boundaries**). Several bound variables, infinite domains, graded or causal senses of "needed", and spaces given symbolically are not modeled. Single-world spaces (`Space.interp`) collapse entailment to truth in that world and cannot exhibit an open claim or an implicature hazard.

**Scope.** These are statements about the toy model; they neither establish nor refute the corresponding claims about how human or automated readers interpret real summaries of real reports. Each card states its connection to real summaries separately, as a `derived (modeling bridge)` claim with its reasoning.

**Subjects.** The Lean 4 toolchain release `v4.34.1` is the checker of every theorem (no Mathlib; the Lake project in `lean/` has one library, `Implicature`, and no dependencies). The cited papers are prior art for the modeled phenomena (conditional perfection, scalar implicature, exhaustivity operators, cancellability); the package restates or makes precise some of their results in its own finite vocabulary and examines no other software.

All Lean names below live in the namespace `Toy.Implicature`; sources are under `lean/Implicature/` (`Basic.lean`, `Exh.lean`, `Reader.lean`, `Lemmas.lean`, `Examples.lean`, `Results.lean`).

## Findings

### Model definitions

Every definition that a card statement depends on is quoted here from the Lean source, with its documentation comment. The statement hashes under **Evidence** cover these definitions.

#### Claims and spaces (`Basic.lean`)

`Space.evalAt`, `Space.holds`, `Space.full` and `Space.interp` are in the namespace `Toy.Implicature.Space`. `Space.full n m` has the `2^(n*m)` bitmask worlds; atom `a` at value `k` is bit `a*m + k`. `entailsB` and `satB` (quoted below, after `Equiv`) are Boolean decision procedures proved equivalent to `Entails` and `Sat` (`entailsB_iff`, `satB_iff`, also quoted below); they supply the `Decidable` instances used by `decide +kernel`, and they occur in the definitions of `naiveExcl`, `ruleReadings`, `blockers` and `readingsStar`.

```lean
-- lean/Implicature/Basic.lean:21-27
/-- The argument of an atom: a literal parameter value, or the bound variable of the nearest
enclosing quantifier. The syntax has a single variable; an inner quantifier shadows an outer
one. Outside every quantifier, `var` reads parameter value `0` (claims are intended closed). -/
inductive Arg where
  | lit (k : Nat)
  | var
  deriving DecidableEq, Repr
```

```lean
-- lean/Implicature/Basic.lean:29-43
/-- Claim syntax. `imp` is a stated conditional result ("`A` gives `B`"); `rel h c` is a claim
under a stated hypothesis ("under `h`, `c`"). The two have the same truth conditions
(material implication); they differ only in which reader rules and alternatives apply. -/
inductive Claim where
  | top
  | atom (a : Nat) (t : Arg)
  | and (c d : Claim)
  | or (c d : Claim)
  | imp (c d : Claim)
  | iff (c d : Claim)
  | not (c : Claim)
  | all (c : Claim)
  | ex (c : Claim)
  | rel (h c : Claim)
  deriving DecidableEq, Repr
```

```lean
-- lean/Implicature/Basic.lean:63-70
/-- A finite model space: an explicit list of worlds, an explicit finite list of parameter
values (the domain of the bounded quantifiers), and the truth value `val w a k` of atom `a` at
parameter value `k` in world `w`. Only the listed worlds count for entailment. -/
structure Space where
  World : Type
  worlds : List World
  params : List Nat
  val : World → Nat → Nat → Bool
```

```lean
-- lean/Implicature/Basic.lean:74-86
/-- Evaluation of a claim in world `w` with the bound variable set to `x`. -/
def evalAt (S : Space) (w : S.World) (x : Nat) : Claim → Bool
  | .top => true
  | .atom a (.lit k) => S.val w a k
  | .atom a .var => S.val w a x
  | .and c d => S.evalAt w x c && S.evalAt w x d
  | .or c d => S.evalAt w x c || S.evalAt w x d
  | .imp c d => !S.evalAt w x c || S.evalAt w x d
  | .iff c d => S.evalAt w x c == S.evalAt w x d
  | .not c => !S.evalAt w x c
  | .all c => S.params.all fun y => S.evalAt w y c
  | .ex c => S.params.any fun y => S.evalAt w y c
  | .rel h c => !S.evalAt w x h || S.evalAt w x c
```

```lean
-- lean/Implicature/Basic.lean:88-89
/-- Truth of a (closed) claim in a world. -/
def holds (S : Space) (w : S.World) (c : Claim) : Bool := S.evalAt w 0 c
```

```lean
-- lean/Implicature/Basic.lean:91-98
/-- The space of all valuations of `nAtoms` atoms over the parameter values `0 … nParams-1`.
A world is a bitmask `w < 2 ^ (nAtoms * nParams)`; atom `a` holds at value `k` iff bit
`a * nParams + k` of `w` is set. Atoms and values outside the ranges are false. -/
def full (nAtoms nParams : Nat) : Space where
  World := Nat
  worlds := List.range (2 ^ (nAtoms * nParams))
  params := List.range nParams
  val w a k := decide (a < nAtoms) && decide (k < nParams) && w.testBit (a * nParams + k)
```

```lean
-- lean/Implicature/Basic.lean:100-111
/-- A space with a single world in which every atom has a fixed, intended interpretation over
the given parameter values. Used for "natural" instances whose atoms are concrete predicates.
With one world, entailment from any report collapses to truth in that world: every claim is
decided even by the empty report, no claim is left open (`interp_never_open`), and cancellation
discards every false reading, so a literally safe rendering is strengthening-safe with no flags
(`interp_literallySafe_strengtheningSafe_unblocked`). Single-world spaces therefore cannot exhibit
an open claim or an implicature hazard; they only illustrate truth in a fixed structure. -/
def interp (params : List Nat) (val : Nat → Nat → Bool) : Space where
  World := Unit
  worlds := [()]
  params := params
  val _ a k := val a k
```

```lean
-- lean/Implicature/Basic.lean:115-117
/-- `E ⊨ σ`: every listed world in which all claims of `E` hold is a world in which `σ` holds. -/
def Entails (S : Space) (E : List Claim) (σ : Claim) : Prop :=
  ∀ w ∈ S.worlds, (∀ e ∈ E, S.holds w e = true) → S.holds w σ = true
```

```lean
-- lean/Implicature/Basic.lean:119-121
/-- `Γ` is jointly satisfiable in some listed world. -/
def Sat (S : Space) (Γ : List Claim) : Prop :=
  ∃ w ∈ S.worlds, ∀ c ∈ Γ, S.holds w c = true
```

```lean
-- lean/Implicature/Basic.lean:123-125
/-- `E` contradicts `ρ`: `E` entails the negation of `ρ` (refutes it). -/
def Contradicts (S : Space) (E : List Claim) (ρ : Claim) : Prop :=
  Entails S E (.not ρ)
```

```lean
-- lean/Implicature/Basic.lean:127-129
/-- Semantic equivalence of two claims over the listed worlds. -/
def Equiv (S : Space) (c d : Claim) : Prop :=
  Entails S [c] d ∧ Entails S [d] c
```

```lean
-- lean/Implicature/Basic.lean:131-133
/-- Boolean decision procedure for `Entails`. -/
def entailsB (S : Space) (E : List Claim) (σ : Claim) : Bool :=
  S.worlds.all fun w => !(E.all fun e => S.holds w e) || S.holds w σ
```

```lean
-- lean/Implicature/Basic.lean:135-137
/-- Boolean decision procedure for `Sat`. -/
def satB (S : Space) (Γ : List Claim) : Bool :=
  S.worlds.any fun w => Γ.all fun c => S.holds w c
```

```lean
-- lean/Implicature/Basic.lean:139-140
theorem entailsB_iff {S : Space} {E : List Claim} {σ : Claim} :
    entailsB S E σ = true ↔ Entails S E σ := by …
```

```lean
-- lean/Implicature/Basic.lean:154-154
theorem satB_iff {S : Space} {Γ : List Claim} : satB S Γ = true ↔ Sat S Γ := by …
```

```lean
-- lean/Implicature/Basic.lean:171-175
/-- Conjunction of a list of claims (`top` for the empty list). -/
def conjList : List Claim → Claim
  | [] => .top
  | [c] => c
  | c :: cs => .and c (conjList cs)
```

#### Alternatives and exhaustification (`Exh.lean`)

`Claim.lits`, `Claim.quantFree` and `Claim.substLit` are in the namespace `Toy.Implicature.Claim`.

```lean
-- lean/Implicature/Exh.lean:23-29
/-- Literal parameter values mentioned in a claim (with repetitions). -/
def lits : Claim → List Nat
  | .top => []
  | .atom _ (.lit k) => [k]
  | .atom _ .var => []
  | .and c d | .or c d | .imp c d | .iff c d | .rel c d => c.lits ++ d.lits
  | .not c | .all c | .ex c => c.lits
```

```lean
-- lean/Implicature/Exh.lean:31-38
/-- No quantifier and no bound variable: the claim talks about fixed parameter values only. -/
def quantFree : Claim → Bool
  | .top => true
  | .atom _ (.lit _) => true
  | .atom _ .var => false
  | .and c d | .or c d | .imp c d | .iff c d | .rel c d => c.quantFree && d.quantFree
  | .not c => c.quantFree
  | .all _ | .ex _ => false
```

```lean
-- lean/Implicature/Exh.lean:40-52
/-- Replace every literal parameter value `k` by `k'`. -/
def substLit (k k' : Nat) : Claim → Claim
  | .top => .top
  | .atom a (.lit j) => .atom a (.lit (if j = k then k' else j))
  | .atom a .var => .atom a .var
  | .and c d => .and (c.substLit k k') (d.substLit k k')
  | .or c d => .or (c.substLit k k') (d.substLit k k')
  | .imp c d => .imp (c.substLit k k') (d.substLit k k')
  | .iff c d => .iff (c.substLit k k') (d.substLit k k')
  | .not c => .not (c.substLit k k')
  | .all c => .all (c.substLit k k')
  | .ex c => .ex (c.substLit k k')
  | .rel h c => .rel (h.substLit k k') (c.substLit k k')
```

```lean
-- lean/Implicature/Exh.lean:56-68
/-- Rule-generated alternatives of a single site (the "core" alternatives). Conditional:
converse and biconditional. Existential: universal. Relativized `rel h c`: the hypothesis-free
`c`, plus the alternatives of `c` kept under `h`. Universal prefix: alternatives of the body, kept
under the prefix. Everything else (atoms, `∧`, `∨`, `↔`, `¬`, `top`) has no core alternatives.
These are stipulated rules, not structurally defined alternatives in the sense of Katzir (2007):
under that definition a disjunction has its disjuncts as alternatives (by deletion), while the
biconditional, being more complex, is not an alternative of a conditional. -/
def coreAlts : Claim → List Claim
  | .imp a b => [.imp b a, .iff a b]
  | .ex c => [.all c]
  | .rel h c => c :: (coreAlts c).map (.rel h)
  | .all c => (coreAlts c).map .all
  | _ => []
```

```lean
-- lean/Implicature/Exh.lean:70-83
/-- Neighbouring-value alternatives: a quantifier-free claim mentioning exactly one parameter
value `k` has the alternatives obtained by moving `k` to `k - 1` and `k + 1`, when those are
parameter values of the space. The rule ignores the connectives of the claim, so it also applies
under negation, disjunction and biconditional (`stdAlt_value_alternatives_any_connective`). -/
def valueAlts (S : Space) (c : Claim) : List Claim :=
  if c.quantFree then
    match c.lits with
    | k :: rest =>
      if rest.all (· == k) then
        (((if k = 0 then [] else [k - 1]) ++ [k + 1]).filter (fun k' => S.params.contains k')).map
          (fun k' => c.substLit k k')
      else []
    | [] => []
  else []
```

```lean
-- lean/Implicature/Exh.lean:85-86
/-- All alternatives of one site. -/
def siteAlts (S : Space) (c : Claim) : List Claim := coreAlts c ++ valueAlts S c
```

```lean
-- lean/Implicature/Exh.lean:88-92
/-- Apply a site rewriting `f` to one top-level conjunct at a time (the top-level `and` spine
is the list of sites), returning one result per (site, rewrite) pair. -/
def siteSubst (f : Claim → List Claim) : Claim → List Claim
  | .and c d => (siteSubst f c).map (fun c' => .and c' d) ++ (siteSubst f d).map (fun d' => .and c d')
  | c => f c
```

```lean
-- lean/Implicature/Exh.lean:94-95
/-- The standard alternatives of a rendering: replace one site by one of its alternatives. -/
def stdAlt (S : Space) (σ : Claim) : List Claim := siteSubst (siteAlts S) σ
```

```lean
-- lean/Implicature/Exh.lean:99-102
/-- `falsSub S A w v`: every alternative of `A` false at `w` is false at `v`
(the falsified set of `w` is contained in that of `v`). -/
def falsSub (S : Space) (A : List Claim) (w v : S.World) : Bool :=
  A.all fun a => S.holds w a || !S.holds v a
```

```lean
-- lean/Implicature/Exh.lean:104-107
/-- `w` is a `σ`-world whose set of falsified alternatives is maximal (under inclusion) among
the `σ`-worlds of the space. -/
def maxFals (S : Space) (σ : Claim) (A : List Claim) (w : S.World) : Bool :=
  S.holds w σ && S.worlds.all fun v => !(S.holds v σ && falsSub S A w v) || falsSub S A v w
```

```lean
-- lean/Implicature/Exh.lean:109-112
/-- Computable innocent excludability: `a` is false at every `σ`-world with a maximal
falsified set. -/
def ieB (S : Space) (σ : Claim) (A : List Claim) (a : Claim) : Bool :=
  S.worlds.all fun w => !maxFals S σ A w || !S.holds w a
```

```lean
-- lean/Implicature/Exh.lean:114-115
/-- The innocently excludable alternatives, in the order of `A`. -/
def ieList (S : Space) (σ : Claim) (A : List Claim) : List Claim := A.filter (ieB S σ A)
```

```lean
-- lean/Implicature/Exh.lean:117-120
/-- Exhaustification by innocent exclusion: `σ` and the negation of every innocently
excludable alternative. -/
def exh (S : Space) (A : List Claim) (σ : Claim) : Claim :=
  conjList (σ :: (ieList S σ A).map .not)
```

```lean
-- lean/Implicature/Exh.lean:122-124
/-- The alternatives naive exhaustification negates: those not entailed by `σ`. -/
def naiveExcl (S : Space) (σ : Claim) (A : List Claim) : List Claim :=
  A.filter fun a => !entailsB S [σ] a
```

```lean
-- lean/Implicature/Exh.lean:126-128
/-- Naive exhaustification: `σ` and the negation of every alternative `σ` does not entail. -/
def naiveExh (S : Space) (A : List Claim) (σ : Claim) : Claim :=
  conjList (σ :: (naiveExcl S σ A).map .not)
```

```lean
-- lean/Implicature/Exh.lean:130-132
/-- `X` is a set of alternatives (from `A`) whose negations are jointly consistent with `σ`. -/
def ConsistentExclusion (S : Space) (σ : Claim) (A X : List Claim) : Prop :=
  (∀ a ∈ X, a ∈ A) ∧ ∃ w ∈ S.worlds, S.holds w σ = true ∧ ∀ a ∈ X, S.holds w a = false
```

```lean
-- lean/Implicature/Exh.lean:134-137
/-- A consistent exclusion that no consistent exclusion strictly extends (as a set). -/
def MaximalExclusion (S : Space) (σ : Claim) (A X : List Claim) : Prop :=
  ConsistentExclusion S σ A X ∧
    ∀ Y, ConsistentExclusion S σ A Y → (∀ a ∈ X, a ∈ Y) → ∀ a ∈ Y, a ∈ X
```

```lean
-- lean/Implicature/Exh.lean:139-142
/-- Innocent excludability (textbook form): `a ∈ A` belongs to every maximal consistent
exclusion. -/
def InnocentlyExcludable (S : Space) (σ : Claim) (A : List Claim) (a : Claim) : Prop :=
  a ∈ A ∧ ∀ X, MaximalExclusion S σ A X → a ∈ X
```

#### Readers, blockers, compression, necessity words, disclaimers (`Reader.lean`)

```lean
-- lean/Implicature/Reader.lean:19-31
/-- Default strengthening rules. A blocker flag is an out-of-band annotation with no truth
conditions of its own: it disables exactly the rule it names and nothing else. Intended phrasings:
`perfection` ↔ "the converse is not claimed";
`exhaustification` ↔ "stronger alternatives are not claimed to fail";
`qualifierDrop` ↔ "established under `H`; not shown without `H`".
Disabling one rule leaves the others active: for example, flagging only `perfection` on
`∀x, a → b` still lets exhaustification negate the converse whenever the converse is innocently
excludable (`forall_conditional_blockers_by_converse_status`). -/
inductive Rule where
  | qualifierDrop
  | perfection
  | exhaustification
  deriving DecidableEq, Repr
```

```lean
-- lean/Implicature/Reader.lean:33-34
/-- All rules, in the order in which the composing reader applies them. -/
def allRules : List Rule := [.qualifierDrop, .perfection, .exhaustification]
```

```lean
-- lean/Implicature/Reader.lean:36-42
/-- Perfection of the core of a site: `A → B ↦ A ↔ B`, looking through a prefix of universal
quantifiers and hypothesis relativizations. -/
def perfCore : Claim → Option Claim
  | .imp a b => some (.iff a b)
  | .all c => (perfCore c).map .all
  | .rel h c => (perfCore c).map (.rel h)
  | _ => none
```

```lean
-- lean/Implicature/Reader.lean:44-49
/-- Qualifier dropping at the core of a site: `(H ⇒ C) ↦ C`, looking through a prefix of
universal quantifiers. -/
def dropCore : Claim → Option Claim
  | .rel _ c => some c
  | .all c => (dropCore c).map .all
  | _ => none
```

```lean
-- lean/Implicature/Reader.lean:51-56
/-- One application of a rule, before cancellation; one result per applicable site
(exhaustification applies to the whole rendering, with alternatives `alt σ`). -/
def step (S : Space) (alt : Claim → List Claim) : Rule → Claim → List Claim
  | .perfection, σ => siteSubst (fun c => (perfCore c).toList) σ
  | .qualifierDrop, σ => siteSubst (fun c => (dropCore c).toList) σ
  | .exhaustification, σ => [exh S (alt σ) σ]
```

```lean
-- lean/Implicature/Reader.lean:58-60
/-- The readings a rule contributes to `σ`, after cancellation (kept iff consistent with `σ`). -/
def ruleReadings (S : Space) (alt : Claim → List Claim) (r : Rule) (σ : Claim) : List Claim :=
  (step S alt r σ).filter fun ρ => satB S [σ, ρ]
```

```lean
-- lean/Implicature/Reader.lean:62-65
/-- One-step strengthening reader with blocker flags `F`: the literal reading plus every
uncancelled one-rule reading of an unblocked rule. -/
def readings (S : Space) (alt : Claim → List Claim) (F : List Rule) (σ : Claim) : List Claim :=
  σ :: (allRules.filter fun r => decide (r ∉ F)).flatMap fun r => ruleReadings S alt r σ
```

```lean
-- lean/Implicature/Reader.lean:67-68
/-- Literal safety of a rendering: the report entails it. -/
def LiterallySafe (S : Space) (E : List Claim) (σ : Claim) : Prop := Entails S E σ
```

```lean
-- lean/Implicature/Reader.lean:74-77
/-- Strengthening safety (one-step reader): the report entails every reading. -/
def StrengtheningSafe (S : Space) (alt : Claim → List Claim) (F : List Rule) (E : List Claim)
    (σ : Claim) : Prop :=
  ∀ ρ ∈ readings S alt F σ, Entails S E ρ
```

```lean
-- lean/Implicature/Reader.lean:83-85
/-- The computed blocker set: the rules that contribute some reading `E` does not entail. -/
def blockers (S : Space) (alt : Claim → List Claim) (E : List Claim) (σ : Claim) : List Rule :=
  allRules.filter fun r => (ruleReadings S alt r σ).any fun ρ => !entailsB S E ρ
```

```lean
-- lean/Implicature/Reader.lean:89-93
/-- Apply any subset of the rules `rs`, in list order, each at most once and at one site. -/
def composeReadings (S : Space) (alt : Claim → List Claim) : List Rule → Claim → List Claim
  | [], ρ => [ρ]
  | r :: rs, ρ =>
      composeReadings S alt rs ρ ++ (step S alt r ρ).flatMap (composeReadings S alt rs)
```

```lean
-- lean/Implicature/Reader.lean:95-100
/-- Composing strengthening reader with flags `F`: the literal reading plus every composition of
unblocked rules (in the order of `allRules`) that is consistent with `σ`. -/
def readingsStar (S : Space) (alt : Claim → List Claim) (F : List Rule) (σ : Claim) :
    List Claim :=
  σ :: (composeReadings S alt (allRules.filter fun r => decide (r ∉ F)) σ).filter
    fun ρ => satB S [σ, ρ]
```

```lean
-- lean/Implicature/Reader.lean:102-105
/-- Strengthening safety for the composing reader. -/
def StrengtheningSafeStar (S : Space) (alt : Claim → List Claim) (F : List Rule)
    (E : List Claim) (σ : Claim) : Prop :=
  ∀ ρ ∈ readingsStar S alt F σ, Entails S E ρ
```

```lean
-- lean/Implicature/Reader.lean:113-119
/-- A normal-form established claim with one hypothesis `H`, one quantifier domain (the
parameter set) and a list of conclusions `C₁, …, Cₙ`, rendered one conclusion per top-level
conjunct: `(∀x, H x ⇒ C₁ x) ∧ … ∧ (∀x, H x ⇒ Cₙ x)` (`⊤` for `n = 0`). Each conclusion is its own
site, so perfection, qualifier dropping and the structural alternatives apply to each conclusion
separately. (A conjunction nested under `∀` or `⇒` would be a single site to which perfection and
the structural alternatives do not apply.) -/
def nf (H : Claim) (Cs : List Claim) : Claim := conjList (Cs.map fun c => .all (.rel H c))
```

```lean
-- lean/Implicature/Reader.lean:121-122
/-- The claim of a normal-form entry `(H, Cs)`. -/
def nfOf (p : Claim × List Claim) : Claim := nf p.1 p.2
```

```lean
-- lean/Implicature/Reader.lean:124-128
/-- `comp` is a conclusion-dropping compression of the normal-form entries `R`: every
compressed entry keeps the hypothesis (and the quantifier domain) of some entry of `R` and
keeps only conclusions of that entry. -/
def ConclusionDropping (R comp : List (Claim × List Claim)) : Prop :=
  ∀ p ∈ comp, ∃ q ∈ R, q.1 = p.1 ∧ ∀ c ∈ p.2, c ∈ q.2
```

```lean
-- lean/Implicature/Reader.lean:130-131
/-- The rendering of a compression: the conjunction of its normal-form claims. -/
def renderComp (comp : List (Claim × List Claim)) : Claim := conjList (comp.map nfOf)
```

```lean
-- lean/Implicature/Reader.lean:135-136
/-- "`X` is needed for `Y`", read literally: `∀x, Y x → X x`. -/
def needed (X Y : Claim) : Claim := .all (.imp Y X)
```

```lean
-- lean/Implicature/Reader.lean:138-142
/-- The counterexample half of "`H` is tight for `∀x, H x ⇒ C x`": some parameter value
violates `H` and `C` fails there. It does not check that `∀x, H x ⇒ C x` itself holds, and it
models a single hypothesis: for `∀x, (H₁ x ∧ H₂ x) ⇒ C x`, tightness of `H₁` also requires `H₂` to
hold at the witness, which `tightFor H₁ C` does not express. -/
def tightFor (H C : Claim) : Claim := .ex (.and (.not H) (.not C))
```

```lean
-- lean/Implicature/Reader.lean:146-149
/-- `∀x, a → b` is consistent with its perfected reading `∀x, a ↔ b` (so perfection is not
cancelled). -/
def PerfectionConsistent (S : Space) (a b : Claim) : Prop :=
  Sat S [.all (.imp a b), .all (.iff a b)]
```

```lean
-- lean/Implicature/Reader.lean:151-154
/-- `∀x, a → b` is consistent with the failure of its converse `∀x, b → a` (so the converse is
innocently excludable under the standard alternatives). -/
def ConverseExcludable (S : Space) (a b : Claim) : Prop :=
  Sat S [.all (.imp a b), .not (.all (.imp b a))]
```

```lean
-- lean/Implicature/Reader.lean:165-170
/-- A disclaimer about claim `c`: "`c` is not shown", or the blocked form "`c` is not shown,
and not refuted". Disclaimers are statements about the report, not about the worlds. -/
inductive Disclaimer where
  | notShown (c : Claim)
  | notShownNotRefuted (c : Claim)
  deriving DecidableEq, Repr
```

```lean
-- lean/Implicature/Reader.lean:172-174
/-- `E` leaves `c` open: it neither proves nor refutes `c`. -/
def Open (S : Space) (E : List Claim) (c : Claim) : Prop :=
  ¬ Entails S E c ∧ ¬ Entails S E (.not c)
```

```lean
-- lean/Implicature/Reader.lean:176-179
/-- Literal truth of a disclaimer relative to the report `E`. -/
def DisclaimerTrue (S : Space) (E : List Claim) : Disclaimer → Prop
  | .notShown c => ¬ Entails S E c
  | .notShownNotRefuted c => ¬ Entails S E c ∧ ¬ Entails S E (.not c)
```

```lean
-- lean/Implicature/Reader.lean:181-186
/-- Object-level readings of a reader who maps "not shown" to "false". The blocked form
"not shown, and not refuted" disables that rule. Both readings are fixed by this definition; they
are not derived from exhaustification, the alternatives or the cancellation filter. -/
def disclaimerReadings : Disclaimer → List Claim
  | .notShown c => [.not c]
  | .notShownNotRefuted _ => []
```

```lean
-- lean/Implicature/Reader.lean:188-191
/-- A disclaimer rendering is safe iff it is literally true and `E` entails every object-level
reading the reader draws from it. -/
def DisclaimerSafe (S : Space) (E : List Claim) (d : Disclaimer) : Prop :=
  DisclaimerTrue S E d ∧ ∀ ρ ∈ disclaimerReadings d, Entails S E ρ
```

#### Fixtures (`Examples.lean`, `Results.lean`)

```lean
-- lean/Implicature/Examples.lean:15-16
/-- Atom `0` at the bound variable. -/
def xA : Claim := .atom 0 .var
```

```lean
-- lean/Implicature/Examples.lean:17-18
/-- Atom `1` at the bound variable. -/
def xB : Claim := .atom 1 .var
```

```lean
-- lean/Implicature/Examples.lean:19-20
/-- Atom `2` at the bound variable (used as a hypothesis). -/
def xH : Claim := .atom 2 .var
```

```lean
-- lean/Implicature/Examples.lean:21-22
/-- Atom `0` at parameter value `0` (a closed propositional atom). -/
def p0 : Claim := .atom 0 (.lit 0)
```

```lean
-- lean/Implicature/Examples.lean:23-24
/-- Atom `1` at parameter value `0` (a closed propositional atom). -/
def q0 : Claim := .atom 1 (.lit 0)
```

```lean
-- lean/Implicature/Examples.lean:26-27
/-- One atom over two parameter values (4 worlds). -/
def S12 : Space := Space.full 1 2
```

```lean
-- lean/Implicature/Examples.lean:28-29
/-- Two atoms over one parameter value (4 worlds): propositional logic in `p0`, `q0`. -/
def S21 : Space := Space.full 2 1
```

```lean
-- lean/Implicature/Examples.lean:30-31
/-- Two atoms over two parameter values (16 worlds). -/
def S22 : Space := Space.full 2 2
```

```lean
-- lean/Implicature/Examples.lean:32-33
/-- Three atoms over two parameter values (64 worlds). -/
def S32 : Space := Space.full 3 2
```

```lean
-- lean/Implicature/Examples.lean:35-39
/-- A single interpreted world over the parameter values `0 … 7`: atom `0` is
"divisible by 4", atom `1` is "even"; other atoms are false. -/
def natSpace : Space :=
  Space.interp (List.range 8) fun a k =>
    if a = 0 then k % 4 == 0 else if a = 1 then k % 2 == 0 else false
```

```lean
-- lean/Implicature/Examples.lean:41-42
/-- "`x` is divisible by 4" in `natSpace`. -/
def div4 : Claim := .atom 0 .var
```

```lean
-- lean/Implicature/Examples.lean:43-44
/-- "`x` is even" in `natSpace`. -/
def even : Claim := .atom 1 .var
```

```lean
-- lean/Implicature/Examples.lean:46-52
/-- A two-world space over one parameter value in which atoms `0` and `1` always disagree
(world `false`: `P0` false, `P1` true; world `true`: `P0` true, `P1` false). -/
def disagreeSpace : Space where
  World := Bool
  worlds := [false, true]
  params := [0]
  val w a _ := if a = 0 then w else !w
```

```lean
-- lean/Implicature/Examples.lean:146-147
/-- The disjunction `p0 ∨ q0`. -/
def pOrQ : Claim := .or p0 q0
```

```lean
-- lean/Implicature/Examples.lean:148-149
/-- The standard alternatives of a disjunction: the disjuncts and the conjunction. -/
def disjAlts : List Claim := [p0, q0, .and p0 q0]
```

```lean
-- lean/Implicature/Examples.lean:269-270
/-- The report of the running example: `∀x, A → B` and the converse fails. -/
def E_notConv : List Claim := [.all (.imp xA xB), .not (.all (.imp xB xA))]
```

```lean
-- lean/Implicature/Examples.lean:291-292
/-- The rendering "for all x, under H, A gives B". -/
def σ_relCond : Claim := .all (.rel xH (.imp xA xB))
```

```lean
-- lean/Implicature/Results.lean:45-46
/-- The report of the qualifier-dropping countermodel: `∀x, H ⇒ A`, and `∀x, A` fails. -/
def E_qual : List Claim := [.all (.rel xH xA), .not (.all xA)]
```

```lean
-- lean/Implicature/Results.lean:81-82
/-- The rendering "for all x, A gives B, and not conversely". -/
def σ_notConv : Claim := .and (.all (.imp xA xB)) (.not (.all (.imp xB xA)))
```

```lean
-- lean/Implicature/Results.lean:267-270
/-- The report of the composing-reader countermodel: `∀x, A → B`, `∀x, H ⇒ (B → A)`, and
`∃x, B ∧ ¬A`. -/
def E_relCond : List Claim :=
  [.all (.imp xA xB), .all (.rel xH (.imp xB xA)), .ex (.and xB (.not xA))]
```

```lean
-- lean/Implicature/Results.lean:373-374
/-- The normal-form entries of the compression countermodel. -/
def R_comp : List (Claim × List Claim) := [(xH, [xA, xB])]
```

```lean
-- lean/Implicature/Results.lean:376-378
/-- The report of the compression countermodel: `∀x, H ⇒ A`, `∀x, H ⇒ B`, `∀x, A`, and `∀x, B`
fails. -/
def E_comp : List Claim := [nf xH [xA, xB], .all xA, .not (.all xB)]
```

```lean
-- lean/Implicature/Results.lean:399-401
/-- The normal-form entries of the uncancelling countermodel: unconditionally, `A → B` and
`B ∧ ¬A`. -/
def R_unc : List (Claim × List Claim) := [(.top, [.imp xA xB, .and xB (.not xA)])]
```

```lean
-- lean/Implicature/Results.lean:403-404
/-- The report of the uncancelling countermodel: exactly the normal-form claims of `R_unc`. -/
def E_unc : List Claim := R_unc.map nfOf
```

```lean
-- lean/Implicature/Results.lean:544-546
/-- The report of the multi-world instance: `∀x, A ⇒ B`, a counterexample to the converse
`∃x, B ∧ ¬A`, and the tightness witness `∃x, ¬A ∧ ¬B`. -/
def E_tight : List Claim := [.all (.rel xA xB), .ex (.and xB (.not xA)), tightFor xA xB]
```

#### Definition examples

The definitions in the table below have proved intended positive and negative examples, all in `Examples.lean`. All but three are proved by `decide +kernel`; the three `InnocentlyExcludable` examples (`innocentlyExcludable_pos`, `innocentlyExcludable_neg`, `innocentlyExcludable_neg_disjunct`) are short term or tactic proofs whose finite checks use `decide` or `decide +kernel`. Every example named in the table is quoted verbatim, with its documentation comment, in the collapsible list after the table, and its statement and closure hashes are recorded under **Evidence**. The examples are unit tests of the definitions; eight of them are also cited by cards (as non-vacuity witnesses or in non-claims) and are quoted there as well.

| Definition | Positive examples | Negative examples |
| :--- | :--- | :--- |
| `Space.full`, `Space.holds` | `full_world_count`, `holds_pos_all_true_world` | `holds_neg_partial_world`, `full_out_of_range_atom_false` |
| `Entails` | `entails_pos_modus_ponens` | `entails_neg_affirming_consequent` |
| `Sat` | `sat_pos_not_conversely` | `sat_neg_iff_not_converse` |
| `Contradicts` | `contradicts_pos` | `contradicts_neg` |
| `Equiv` | `equiv_pos` | `equiv_neg` |
| `stdAlt` | `stdAlt_pos_conditional`, `stdAlt_pos_existential`, `stdAlt_pos_relativized`, `stdAlt_pos_neighbouring_values`, `stdAlt_pos_sites`, `stdAlt_value_alternatives_any_connective` | `stdAlt_neg_universal`, `stdAlt_neg_under_negation`, `stdAlt_neg_value_outside_params` |
| `ieList`, `exh` | `ieList_pos_some_not_all`, `exh_pos_some_but_not_all`, `ieList_pos_disjunction` | `ieList_neg_entailed` |
| `InnocentlyExcludable` | `innocentlyExcludable_pos` | `innocentlyExcludable_neg`, `innocentlyExcludable_neg_disjunct` |
| `naiveExcl` | `naiveExcl_pos_disjunction` | `naiveExcl_neg_entailed` |
| `step` | `step_perfection_pos`, `step_drop_pos` | `step_perfection_neg`, `step_drop_neg` |
| `readings` | `readings_pos_perfection` | `readings_neg_blocked`, `readings_neg_cancelled`, `readings_neg_no_composition` |
| `readingsStar` | `readingsStar_pos` | `readingsStar_neg_blocked` |
| `StrengtheningSafe` | `strengtheningSafe_pos` | `strengtheningSafe_neg`, `negated_value_claim_exhaustified_reading_not_entailed` |
| `StrengtheningSafeStar` | `strengtheningSafeStar_pos` | `strengtheningSafeStar_neg` |
| `blockers` | `blockers_pos` | `blockers_neg` |
| `ConclusionDropping` | `conclusionDropping_pos` | `conclusionDropping_neg`, `conclusionDropping_neg_added` |
| `needed`, `tightFor` | `needed_pos`, `tightFor_pos` | `needed_neg`, `tightFor_neg`, `tightFor_does_not_check_theorem` |
| `PerfectionConsistent`, `ConverseExcludable` | `perfectionConsistent_pos`, `converseExcludable_pos` | `perfectionConsistent_neg` (b = ¬a), `converseExcludable_neg` (a = b) |
| `Open`, `DisclaimerTrue`, `DisclaimerSafe` | `open_pos`, `disclaimerSafe_pos` | `open_neg`, `disclaimerSafe_neg`, `disclaimerTrue_neg` |

<details>
<summary>Statements of the 64 definition examples (<code>lean/Implicature/Examples.lean:60-383</code>, verbatim, proofs elided)</summary>

**`Space.full` and `Space.holds`.**

```lean
-- lean/Implicature/Examples.lean:60-61
/-- `Space.full 2 2` has the intended 16 worlds. -/
theorem full_world_count : S22.worlds.length = 16 := by …
```

```lean
-- lean/Implicature/Examples.lean:63-64
/-- Positive: world `3` (atom 0 true at values 0 and 1) satisfies `∀x, P0 x`. -/
theorem holds_pos_all_true_world : S12.holds (show S12.World from (3 : Nat)) (.all xA) = true := by …
```

```lean
-- lean/Implicature/Examples.lean:67-68
/-- Negative: world `1` (atom 0 true at value 0 only) does not satisfy `∀x, P0 x`. -/
theorem holds_neg_partial_world : S12.holds (show S12.World from (1 : Nat)) (.all xA) = false := by …
```

```lean
-- lean/Implicature/Examples.lean:71-73
/-- Negative: atoms outside the declared range are false in `Space.full`. -/
theorem full_out_of_range_atom_false :
    S12.holds (show S12.World from (3 : Nat)) (.ex (.atom 1 .var)) = false := by …
```

**`Entails`, `Sat`, `Contradicts`, `Equiv`.**

```lean
-- lean/Implicature/Examples.lean:78-79
/-- Positive: modus ponens is an entailment. -/
theorem entails_pos_modus_ponens : Entails S21 [p0, .imp p0 q0] q0 := by …
```

```lean
-- lean/Implicature/Examples.lean:81-82
/-- Negative: affirming the consequent is not an entailment. -/
theorem entails_neg_affirming_consequent : ¬ Entails S21 [.imp p0 q0, q0] p0 := by …
```

```lean
-- lean/Implicature/Examples.lean:85-87
/-- Positive: "for all x, A gives B, and not conversely" is satisfiable. -/
theorem sat_pos_not_conversely :
    Sat S22 [.all (.imp xA xB), .not (.all (.imp xB xA))] := by …
```

```lean
-- lean/Implicature/Examples.lean:89-91
/-- Negative: the biconditional together with the failure of the converse is unsatisfiable. -/
theorem sat_neg_iff_not_converse :
    ¬ Sat S22 [.all (.iff xA xB), .not (.all (.imp xB xA))] := by …
```

```lean
-- lean/Implicature/Examples.lean:93-95
/-- Positive: a report refuting the converse contradicts the biconditional. -/
theorem contradicts_pos :
    Contradicts S22 [.not (.all (.imp xB xA))] (.all (.iff xA xB)) := by …
```

```lean
-- lean/Implicature/Examples.lean:97-98
/-- Negative: a report that only proves `A → B` does not contradict the biconditional. -/
theorem contradicts_neg : ¬ Contradicts S22 [.all (.imp xA xB)] (.all (.iff xA xB)) := by …
```

```lean
-- lean/Implicature/Examples.lean:101-102
/-- Positive: `¬∀x, B → A` is equivalent to `∃x, B ∧ ¬A`. -/
theorem equiv_pos : Equiv S22 (.not (.all (.imp xB xA))) (.ex (.and xB (.not xA))) := by …
```

```lean
-- lean/Implicature/Examples.lean:105-106
/-- Negative: `∃x, A` is not equivalent to `∀x, A`. -/
theorem equiv_neg : ¬ Equiv S12 (.ex xA) (.all xA) := by …
```

**Alternatives.**

```lean
-- lean/Implicature/Examples.lean:110-113
/-- Positive: the alternatives of a universal conditional are its converse and its
biconditional. -/
theorem stdAlt_pos_conditional :
    stdAlt S22 (.all (.imp xA xB)) = [.all (.imp xB xA), .all (.iff xA xB)] := by …
```

```lean
-- lean/Implicature/Examples.lean:115-116
/-- Positive: the alternative of an existential is the universal. -/
theorem stdAlt_pos_existential : stdAlt S12 (.ex xA) = [.all xA] := by …
```

```lean
-- lean/Implicature/Examples.lean:118-119
/-- Positive: the alternatives of a relativized claim include the hypothesis-free claim. -/
theorem stdAlt_pos_relativized : stdAlt S32 (.all (.rel xH xA)) = [.all xA] := by …
```

```lean
-- lean/Implicature/Examples.lean:121-123
/-- Positive: a claim at value 1 has the neighbouring values 0 and 2 as alternatives. -/
theorem stdAlt_pos_neighbouring_values :
    stdAlt (Space.full 1 3) (.atom 0 (.lit 1)) = [.atom 0 (.lit 0), .atom 0 (.lit 2)] := by …
```

```lean
-- lean/Implicature/Examples.lean:126-128
/-- Positive: alternatives are substituted at one top-level conjunct at a time. -/
theorem stdAlt_pos_sites :
    stdAlt S22 (.and (.ex xA) (.ex xB)) = [.and (.all xA) (.ex xB), .and (.ex xA) (.all xB)] := by …
```

```lean
-- lean/Implicature/Examples.lean:131-132
/-- Negative: a universal claim has no alternatives (nothing stronger on its scale). -/
theorem stdAlt_neg_universal : stdAlt S12 (.all xA) = [] := by …
```

```lean
-- lean/Implicature/Examples.lean:134-138
/-- Negative: a negated quantified claim has no alternatives: the core rules do not look under
negation, and the neighbouring-value rule applies only to quantifier-free claims. (A negated
quantifier-free claim does get neighbouring-value alternatives,
`stdAlt_value_alternatives_any_connective`.) -/
theorem stdAlt_neg_under_negation : stdAlt S12 (.not (.ex xA)) = [] := by …
```

```lean
-- lean/Implicature/Examples.lean:140-141
/-- Negative: the neighbouring-value rule ignores values outside the parameter set. -/
theorem stdAlt_neg_value_outside_params : stdAlt S12 (.atom 0 (.lit 1)) = [.atom 0 (.lit 0)] := by …
```

**Innocent exclusion and exhaustification.**

```lean
-- lean/Implicature/Examples.lean:151-158
/-- Positive: the neighbouring-value rule ignores connectives: a negated, disjunctive or
biconditional quantifier-free claim at value `0` gets the value-`1` alternative when `1` is a
parameter value; with a single parameter value (`S21`) the disjunction has no alternatives. -/
theorem stdAlt_value_alternatives_any_connective :
    stdAlt S12 (.not p0) = [.not (.atom 0 (.lit 1))] ∧
    stdAlt S22 pOrQ = [.or (.atom 0 (.lit 1)) (.atom 1 (.lit 1))] ∧
    stdAlt S22 (.iff p0 q0) = [.iff (.atom 0 (.lit 1)) (.atom 1 (.lit 1))] ∧
    stdAlt S21 pOrQ = [] := by …
```

```lean
-- lean/Implicature/Examples.lean:161-165
/-- Consequence of the value rule under negation: `¬P0(0)` is not strengthening-safe for the
report `[¬P0(0)]` in `S12`, because exhaustification adds `P0(1)`. -/
theorem negated_value_claim_exhaustified_reading_not_entailed :
    LiterallySafe S12 [.not p0] (.not p0) ∧
    ¬ StrengtheningSafe S12 (stdAlt S12) [] [.not p0] (.not p0) := by …
```

```lean
-- lean/Implicature/Examples.lean:168-169
/-- Positive: for "some", innocent exclusion negates "all". -/
theorem ieList_pos_some_not_all : ieList S12 (.ex xA) [.all xA] = [.all xA] := by …
```

```lean
-- lean/Implicature/Examples.lean:171-173
/-- Positive: the exhaustified "some" is "some but not all". -/
theorem exh_pos_some_but_not_all :
    Equiv S12 (exh S12 [.all xA] (.ex xA)) (.and (.ex xA) (.not (.all xA))) := by …
```

```lean
-- lean/Implicature/Examples.lean:175-177
/-- Positive: for a disjunction, innocent exclusion negates only the conjunction
(exclusive "or"). -/
theorem ieList_pos_disjunction : ieList S21 pOrQ disjAlts = [.and p0 q0] := by …
```

```lean
-- lean/Implicature/Examples.lean:179-180
/-- Negative: an alternative entailed by a satisfiable prejacent is not excluded. -/
theorem ieList_neg_entailed : ieList S12 (.all xA) [.ex xA] = [] := by …
```

```lean
-- lean/Implicature/Examples.lean:182-184
/-- Positive (textbook definition): "all" is innocently excludable for "some". -/
theorem innocentlyExcludable_pos :
    InnocentlyExcludable S12 (.ex xA) [.all xA] (.all xA) := …
```

```lean
-- lean/Implicature/Examples.lean:187-190
/-- Negative (textbook definition): "some" is not innocently excludable for "all": the empty
exclusion is maximal. -/
theorem innocentlyExcludable_neg :
    ¬ InnocentlyExcludable S12 (.all xA) [.ex xA] (.ex xA) := by …
```

```lean
-- lean/Implicature/Examples.lean:206-208
/-- Negative (textbook definition): in a disjunction, a disjunct is not innocently excludable
(there is a maximal exclusion that keeps it). -/
theorem innocentlyExcludable_neg_disjunct : ¬ InnocentlyExcludable S21 pOrQ disjAlts p0 := by …
```

```lean
-- lean/Implicature/Examples.lean:227-228
/-- Positive: naive exhaustification of a disjunction negates every alternative. -/
theorem naiveExcl_pos_disjunction : naiveExcl S21 pOrQ disjAlts = disjAlts := by …
```

```lean
-- lean/Implicature/Examples.lean:230-231
/-- Negative: naive exhaustification keeps alternatives the prejacent entails. -/
theorem naiveExcl_neg_entailed : naiveExcl S12 (.all xA) [.ex xA] = [] := by …
```

**Reader rules, readings, blockers.**

```lean
-- lean/Implicature/Examples.lean:235-237
/-- Positive: perfection turns a universal conditional into a universal biconditional. -/
theorem step_perfection_pos :
    step S22 (stdAlt S22) .perfection (.all (.imp xA xB)) = [.all (.iff xA xB)] := by …
```

```lean
-- lean/Implicature/Examples.lean:240-241
/-- Negative: perfection does not apply to an existential. -/
theorem step_perfection_neg : step S12 (stdAlt S12) .perfection (.ex xA) = [] := by …
```

```lean
-- lean/Implicature/Examples.lean:244-245
/-- Positive: qualifier dropping removes the hypothesis of a relativized claim. -/
theorem step_drop_pos : step S32 (stdAlt S32) .qualifierDrop (.all (.rel xH xA)) = [.all xA] := by …
```

```lean
-- lean/Implicature/Examples.lean:248-249
/-- Negative: a stated conditional result is not a qualifier and is not dropped. -/
theorem step_drop_neg : step S22 (stdAlt S22) .qualifierDrop (.all (.imp xA xB)) = [] := by …
```

```lean
-- lean/Implicature/Examples.lean:252-254
/-- Positive: the unblocked reader of "for all x, A gives B" draws the perfected reading. -/
theorem readings_pos_perfection :
    (Claim.all (.iff xA xB)) ∈ readings S22 (stdAlt S22) [] (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Examples.lean:257-259
/-- Negative: the perfection blocker removes the perfected reading. -/
theorem readings_neg_blocked :
    (Claim.all (.iff xA xB)) ∉ readings S22 (stdAlt S22) [.perfection] (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Examples.lean:262-266
/-- Negative (cancellation): with an explicit "and not conversely", the perfected reading
contradicts the literal content and is not drawn. -/
theorem readings_neg_cancelled :
    (Claim.and (.all (.iff xA xB)) (.not (.all (.imp xB xA)))) ∉
      readings S22 (stdAlt S22) [] (.and (.all (.imp xA xB)) (.not (.all (.imp xB xA)))) := by …
```

```lean
-- lean/Implicature/Examples.lean:272-275
/-- Positive: with the perfection blocker, "for all x, A gives B" is strengthening-safe for
`E_notConv`. -/
theorem strengtheningSafe_pos :
    StrengtheningSafe S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Examples.lean:278-280
/-- Negative: without blockers it is not. -/
theorem strengtheningSafe_neg :
    ¬ StrengtheningSafe S22 (stdAlt S22) [] E_notConv (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Examples.lean:283-284
/-- Positive: the computed blocker set of the running example is exactly `[perfection]`. -/
theorem blockers_pos : blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] := by …
```

```lean
-- lean/Implicature/Examples.lean:287-288
/-- Negative: a biconditional rendering of a proved biconditional needs no blocker. -/
theorem blockers_neg : blockers S22 (stdAlt S22) [.all (.iff xA xB)] (.all (.iff xA xB)) = [] := by …
```

```lean
-- lean/Implicature/Examples.lean:294-296
/-- Positive: the composing reader draws "for all x, A iff B" from `σ_relCond` (drop, then
perfect). -/
theorem readingsStar_pos : (Claim.all (.iff xA xB)) ∈ readingsStar S32 (stdAlt S32) [] σ_relCond := by …
```

```lean
-- lean/Implicature/Examples.lean:299-301
/-- Negative: the one-step reader does not draw that reading. -/
theorem readings_neg_no_composition :
    (Claim.all (.iff xA xB)) ∉ readings S32 (stdAlt S32) [] σ_relCond := by …
```

```lean
-- lean/Implicature/Examples.lean:303-305
/-- Negative: with the qualifier-drop flag the composing reader no longer draws that reading. -/
theorem readingsStar_neg_blocked :
    (Claim.all (.iff xA xB)) ∉ readingsStar S32 (stdAlt S32) [.qualifierDrop] σ_relCond := by …
```

```lean
-- lean/Implicature/Examples.lean:308-311
/-- Positive: with the perfection flag, "for all x, A gives B" is strengthening-safe for the
composing reader and `E_notConv`. -/
theorem strengtheningSafeStar_pos :
    StrengtheningSafeStar S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Examples.lean:314-316
/-- Negative: without flags it is not. -/
theorem strengtheningSafeStar_neg :
    ¬ StrengtheningSafeStar S22 (stdAlt S22) [] E_notConv (.all (.imp xA xB)) := by …
```

**Non-degeneracy conditions.**

```lean
-- lean/Implicature/Examples.lean:321-322
/-- Positive: "for all x, A gives B" is consistent with "for all x, A iff B" in `S22`. -/
theorem perfectionConsistent_pos : PerfectionConsistent S22 xA xB := by …
```

```lean
-- lean/Implicature/Examples.lean:324-325
/-- Negative: "for all x, A gives not A" is inconsistent with "for all x, A iff not A". -/
theorem perfectionConsistent_neg : ¬ PerfectionConsistent S12 xA (.not xA) := by …
```

```lean
-- lean/Implicature/Examples.lean:327-328
/-- Positive: "for all x, A gives B" is consistent with the failure of its converse in `S22`. -/
theorem converseExcludable_pos : ConverseExcludable S22 xA xB := by …
```

```lean
-- lean/Implicature/Examples.lean:330-331
/-- Negative: "for all x, A gives A" entails its converse. -/
theorem converseExcludable_neg : ¬ ConverseExcludable S12 xA xA := by …
```

**Normal form and compression.**

```lean
-- lean/Implicature/Examples.lean:335-336
/-- Positive: keeping the hypothesis and a subset of the conclusions is conclusion dropping. -/
theorem conclusionDropping_pos : ConclusionDropping [(xH, [xA, xB])] [(xH, [xA])] := by …
```

```lean
-- lean/Implicature/Examples.lean:339-340
/-- Negative: replacing the hypothesis by `top` (dropping it) is not conclusion dropping. -/
theorem conclusionDropping_neg : ¬ ConclusionDropping [(xH, [xA, xB])] [(.top, [xA])] := by …
```

```lean
-- lean/Implicature/Examples.lean:343-344
/-- Negative: adding a conclusion is not conclusion dropping. -/
theorem conclusionDropping_neg_added : ¬ ConclusionDropping [(xH, [xA])] [(xH, [xA, xB])] := by …
```

**Necessity words, tightness, disclaimers.**

```lean
-- lean/Implicature/Examples.lean:349-350
/-- Positive: "evenness is needed for divisibility by 4" is true in `natSpace`. -/
theorem needed_pos : Entails natSpace [] (needed even div4) := by …
```

```lean
-- lean/Implicature/Examples.lean:352-353
/-- Negative: "divisibility by 4 is needed for evenness" is false in `natSpace`. -/
theorem needed_neg : Contradicts natSpace [] (needed div4 even) := by …
```

```lean
-- lean/Implicature/Examples.lean:355-356
/-- Positive: in `natSpace`, divisibility by 4 is tight for "under div4, even" (1 is neither). -/
theorem tightFor_pos : Entails natSpace [] (tightFor div4 even) := by …
```

```lean
-- lean/Implicature/Examples.lean:358-359
/-- Negative: no hypothesis is tight for a conclusion that holds everywhere. -/
theorem tightFor_neg : Contradicts natSpace [] (tightFor div4 (.or even (.not even))) := by …
```

```lean
-- lean/Implicature/Examples.lean:362-366
/-- `tightFor` does not check the theorem: `tightFor div4 (¬even)` holds in `natSpace` although
`∀x, div4 ⇒ ¬even` is false there. -/
theorem tightFor_does_not_check_theorem :
    Contradicts natSpace [] (.all (.rel div4 (.not even))) ∧
    Entails natSpace [] (tightFor div4 (.not even)) := by …
```

```lean
-- lean/Implicature/Examples.lean:369-370
/-- Positive: the empty report leaves `p0` open. -/
theorem open_pos : Open S21 [] p0 := by …
```

```lean
-- lean/Implicature/Examples.lean:372-373
/-- Negative: a report proving `p0` does not leave it open. -/
theorem open_neg : ¬ Open S21 [p0] p0 := by …
```

```lean
-- lean/Implicature/Examples.lean:375-376
/-- Positive: "`p0` is not shown, and not refuted" is safe for the empty report. -/
theorem disclaimerSafe_pos : DisclaimerSafe S21 [] (.notShownNotRefuted p0) := by …
```

```lean
-- lean/Implicature/Examples.lean:378-379
/-- Negative: "`p0` is not shown", read as "`p0` is false", is unsafe for the empty report. -/
theorem disclaimerSafe_neg : ¬ DisclaimerSafe S21 [] (.notShown p0) := by …
```

```lean
-- lean/Implicature/Examples.lean:381-382
/-- Negative: a false disclaimer is not safe ("not shown" when `E` proves `p0`). -/
theorem disclaimerTrue_neg : ¬ DisclaimerTrue S21 [p0] (.notShown p0) := by …
```

</details>

### Cards

Each card gives: kind, tier and depth; the plain-language claim; the Lean statement of every main theorem, quoted verbatim with its source lines (proofs elided), and for general theorems a checked rendering with the key definitions unfolded; the hypothesis ledger ("tight" means a proved counterexample satisfies all the other hypotheses of that theorem and falsifies its conclusion; the witness class says what kind of instance it is); the non-vacuity witness; the positive control for impossibility-style cards; prior art; the design question; and the basis of each claim. Each card's non-claims are under **Boundaries**.

#### Card 1. `literal-safety-does-not-imply-strengthening-safety`

- **Kind:** counterexample. **Tier:** T1: Each pattern (perfection, scalar implicature, overgeneralization by dropping a restriction) is classical in pragmatics; the precise countermodels in this report-and-rendering setting are new formulations of folklore. **Depth:** shallow.
- **Plain claim.** For the one-step reader `readings` with the standard alternatives `stdAlt` and no blocker flags, there are consistent reports E and renderings σ with E ⊨ σ (literal safety) for which the reader draws a reading that E contradicts: (i) perfection, in the 16-world space S22: E proves ∀x, A→B and refutes ∀x, B→A, and the reading ∀x, A↔B is drawn; (ii) exhaustification, in the 4-world space S12: E proves ∀x, A, and the reading of ∃x, A equivalent to (∃x, A) ∧ ¬(∀x, A) is drawn; (iii) qualifier dropping, in the 64-world space S32: E proves ∀x, H⇒A and refutes ∀x, A, and the reading ∀x, A is drawn.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:21-25
theorem perfection_reading_contradicted_though_literally_safe :
    Sat S22 E_notConv ∧ LiterallySafe S22 E_notConv (.all (.imp xA xB)) ∧
    (Claim.all (.iff xA xB)) ∈ readings S22 (stdAlt S22) [] (.all (.imp xA xB)) ∧
    Contradicts S22 E_notConv (.all (.iff xA xB)) ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [] E_notConv (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Results.lean:37-42
theorem exhaustification_reading_contradicted_though_literally_safe :
    Sat S12 [.all xA] ∧ LiterallySafe S12 [.all xA] (.ex xA) ∧
    exh S12 (stdAlt S12 (.ex xA)) (.ex xA) ∈ readings S12 (stdAlt S12) [] (.ex xA) ∧
    Equiv S12 (exh S12 (stdAlt S12 (.ex xA)) (.ex xA)) (.and (.ex xA) (.not (.all xA))) ∧
    Contradicts S12 [.all xA] (exh S12 (stdAlt S12 (.ex xA)) (.ex xA)) ∧
    ¬ StrengtheningSafe S12 (stdAlt S12) [] [.all xA] (.ex xA) := by …
```

```lean
-- lean/Implicature/Results.lean:50-54
theorem qualifier_drop_reading_contradicted_though_literally_safe :
    Sat S32 E_qual ∧ LiterallySafe S32 E_qual (.all (.rel xH xA)) ∧
    (Claim.all xA) ∈ readings S32 (stdAlt S32) [] (.all (.rel xH xA)) ∧
    Contradicts S32 E_qual (.all xA) ∧
    ¬ StrengtheningSafe S32 (stdAlt S32) [] E_qual (.all (.rel xH xA)) := by …
```

Fixtures used: `E_notConv`, `E_qual` (quoted under **Model definitions → Fixtures**).

**Hypothesis ledger.**

No hypotheses: the theorems on this card are closed statements about concrete instances, proved by kernel evaluation.

**Non-vacuity witness.** Each theorem exhibits its instance and includes Sat S E (the report is consistent): S22 with E_notConv; S12 with E = [∀x, A]; S32 with E_qual. Lean: `perfection_reading_contradicted_though_literally_safe`, `exhaustification_reading_contradicted_though_literally_safe`, `qualifier_drop_reading_contradicted_though_literally_safe`.

**Further theorems cited in this card's non-claims:** `blockers_sound`, `blocker_conjunct_drop_breaks_strengthening_safety`, `perfection_countermodel_exhaustified_reading_entailed`, `blockers_pos`, `stdAlt_pos_conditional`, `stdAlt_pos_relativized`, `stdAlt_pos_neighbouring_values`, `stdAlt_value_alternatives_any_connective` (quoted under **Cited supporting theorems**).

**Prior art.**

- M. L. Geis and A. M. Zwicky, "On invited inferences", Linguistic Inquiry 2(4):561-566, 1971. Names the invited inference of conditional perfection ("If you mow the lawn, I'll give you five dollars" invites "if not, not").
- L. R. Horn, A Natural History of Negation, University of Chicago Press, 1989 (reissued by CSLI Publications, Stanford, 2001, ISBN 1-57586-336-7); chapter 4, "Negation and Quantity", develops quantity scales such as <all, some> and the scalar implicature from "some" to "not all".
- L. R. Horn, "From if to iff: Conditional perfection as pragmatic strengthening", Journal of Pragmatics 32(3):289-326, 2000, doi:10.1016/S0378-2166(99)00053-3. Analyzes conditional perfection as pragmatic strengthening.
- H. P. Grice, "Logic and conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics 3: Speech Acts, Academic Press, 1975, pp. 41-58 (Brill reissue doi:10.1163/9789004368811_003). Introduces conversational implicature and its cancellability; the cancellation filter of the reader model is a toy version of cancellability.
- I. A. Noveck, "When children are more logical than adults: Experimental investigations of scalar implicature", Cognition 78(2):165-188, 2001, doi:10.1016/S0010-0277(00)00114-1. Cited as evidence for the modeling bridge, not for any kernel-checked statement: adults often reject underinformative "some" statements.
- L. Bott and I. A. Noveck, "Some utterances are underinformative: The onset and time course of scalar inferences", Journal of Memory and Language 51(3):437-457, 2004, doi:10.1016/j.jml.2004.05.006. Cited as evidence for the modeling bridge, not for any kernel-checked statement: "some but not all" responses take longer than logical responses.

**Design question.** Is literal entailment of a summary sentence by the proved statement enough to make the summary safe against default strengthenings? (No, for this reader model: for each of the three rules there is a literally entailed summary whose strengthened reading a consistent report refutes.)

Basis: execution (Lean kernel check): `perfection_reading_contradicted_though_literally_safe`, `exhaustification_reading_contradicted_though_literally_safe`, `qualifier_drop_reading_contradicted_though_literally_safe`.

Basis: derived (modeling bridge): If a reader of a real summary perfects conditionals, exhaustifies against stronger alternatives, or drops stated hypotheses as these rules do, then checking that the report entails the summary does not rule out a misleading reading. Reasoning: the three countermodels have the shape of real reports and summaries; whether and when real readers apply the rules is an empirical matter (Noveck 2001; Bott and Noveck 2004, for "some"). This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 1**.

#### Card 2. `literal-safety-closed-under-literal-weakening`

- **Kind:** theorem. **Tier:** T0: Transitivity of entailment. **Depth:** definitional.
- **Plain claim.** For every finite space S, report E and claims σ, σ': if E ⊨ σ and σ ⊨ σ' over the listed worlds, then E ⊨ σ'.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:60-62
theorem literal_safety_closed_under_literal_weakening (S : Space) (E : List Claim)
    (σ σ' : Claim) (hsafe : LiterallySafe S E σ) (hweak : Entails S [σ] σ') :
    LiterallySafe S E σ' := …
```

Unfolded rendering of `literal_safety_closed_under_literal_weakening` (Lean; definitionally equal to the statement after its binders):

```lean
(∀ w ∈ S.worlds, (∀ e ∈ E, S.holds w e = true) → S.holds w σ = true) →
  (∀ w ∈ S.worlds, (∀ e ∈ [σ], S.holds w e = true) → S.holds w σ' = true) →
  ∀ w ∈ S.worlds, (∀ e ∈ E, S.holds w e = true) → S.holds w σ' = true
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hsafe : LiterallySafe S E σ` | the rendering being weakened is entailed by the report | tight | `literal_weakening_tight_hsafe` | the 4-world space S21 with the empty report and σ = σ' = p0 | every theorem on this card |
| `hweak : Entails S [σ] σ'` | σ' is a literal weakening of σ | tight | `literal_weakening_tight_hweak` | the 4-world space S21 with report [p0], σ = p0 and the independent atom σ' = q0 | every theorem on this card |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:67-67
theorem literal_weakening_tight_hsafe : Entails S21 [p0] p0 ∧ ¬ LiterallySafe S21 [] p0 := by …
```

```lean
-- lean/Implicature/Results.lean:72-73
theorem literal_weakening_tight_hweak :
    LiterallySafe S21 [p0] p0 ∧ ¬ LiterallySafe S21 [p0] q0 := by …
```

</details>

**Non-vacuity witness.** S21, E = [p0 ∧ q0], σ = p0 ∧ q0, σ' = p0. Lean: `literal_weakening_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:77-78
theorem literal_weakening_nonvacuous :
    LiterallySafe S21 [.and p0 q0] (.and p0 q0) ∧ Entails S21 [.and p0 q0] p0 := by …
```

</details>

**Further theorems cited in this card's non-claims:** `blocker_conjunct_drop_breaks_strengthening_safety` (quoted under **Cited supporting theorems**).

**Prior art.**

- Standard property of semantic consequence; no specific source is relied on.

**Design question.** Reference point: which kind of safety survives compression by weakening? (Literal safety does; strengthening safety need not: `blocker_conjunct_drop_breaks_strengthening_safety`.)

Basis: execution (Lean kernel check): `literal_safety_closed_under_literal_weakening`, `literal_weakening_tight_hsafe`, `literal_weakening_tight_hweak`, `literal_weakening_nonvacuous`.

Basis: derived (modeling bridge): A summary that the report entails stays literally true under further literal weakening, for any real summary whose meaning is captured by its formal rendering. Reasoning: transitivity of entailment involves no reader assumption. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 2**.

#### Card 3. `dropping-a-blocking-conjunct-breaks-strengthening-safety`

- **Kind:** counterexample. **Tier:** T1: Cancellation of an implicature by an explicit clause is Gricean folklore; the statement that the literal weakening obtained by deleting the cancelling clause loses strengthening safety is a precise formulation of it. **Depth:** shallow.
- **Plain claim.** For the one-step reader with the standard alternatives and no blocker flags, in the 16-world space S22: the rendering σ = (∀x, A→B) ∧ ¬(∀x, B→A) is strengthening-safe for the report E = [σ], and its perfected reading (∀x, A↔B) ∧ ¬(∀x, B→A), generated at the first conjunct, is inconsistent with σ and is not drawn (cancellation); while its literal weakening ∀x, A→B (σ ⊨ ∀x, A→B) is not strengthening-safe for the same E.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:88-95
theorem blocker_conjunct_drop_breaks_strengthening_safety :
    Entails S22 [σ_notConv] (.all (.imp xA xB)) ∧ Sat S22 [σ_notConv] ∧
    (Claim.and (.all (.iff xA xB)) (.not (.all (.imp xB xA)))) ∈
      step S22 (stdAlt S22) .perfection σ_notConv ∧
    (Claim.and (.all (.iff xA xB)) (.not (.all (.imp xB xA)))) ∉
      readings S22 (stdAlt S22) [] σ_notConv ∧
    StrengtheningSafe S22 (stdAlt S22) [] [σ_notConv] σ_notConv ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [] [σ_notConv] (.all (.imp xA xB)) := by …
```

Fixtures used: `σ_notConv` (quoted under **Model definitions → Fixtures**).

**Hypothesis ledger.**

No hypotheses: the theorems on this card are closed statements about concrete instances, proved by kernel evaluation.

**Non-vacuity witness.** The instance itself; Sat S22 [σ] is part of the statement. Lean: `blocker_conjunct_drop_breaks_strengthening_safety`.

**Further theorems cited in this card's non-claims:** `open_converse_rewordings_not_literally_safe`, `forall_conditional_open_converse_safe_iff_both_flags`, `stdAlt_value_alternatives_any_connective`, `composing_reader_minimal_blocker_sets_not_unique` (quoted under **Cited supporting theorems**).

**Prior art.**

- H. P. Grice, "Logic and conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics 3: Speech Acts, Academic Press, 1975, pp. 41-58 (Brill reissue doi:10.1163/9789004368811_003). Introduces conversational implicature and its cancellability; the cancellation filter of the reader model is a toy version of cancellability.
- M. L. Geis and A. M. Zwicky, "On invited inferences", Linguistic Inquiry 2(4):561-566, 1971. Names the invited inference of conditional perfection ("If you mow the lawn, I'll give you five dollars" invites "if not, not").
- L. R. Horn, "From if to iff: Conditional perfection as pragmatic strengthening", Journal of Pragmatics 32(3):289-326, 2000, doi:10.1016/S0378-2166(99)00053-3. Analyzes conditional perfection as pragmatic strengthening.

**Design question.** Does compression by dropping conjuncts (and nothing else) preserve the non-misleadingness of a summary? (No: dropping the clause that cancels a strengthening is a literal weakening that makes the summary misleading for this reader model.)

Basis: execution (Lean kernel check): `blocker_conjunct_drop_breaks_strengthening_safety`.

Basis: derived (modeling bridge): For a reader who cancels a perfected reading when it conflicts with the summary, as the cancellation filter does, deleting a clause such as "and not conversely" from a real summary can make the summary misleading although it stays literally true. Reasoning: the instance has realistic shape; the cancellation behaviour is the modeled assumption. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 3**.

#### Card 4. `naive-exhaustification-of-disjunction-inconsistent`

- **Kind:** counterexample. **Tier:** T0: The standard motivating example for innocent exclusion (Fox 2007), and the disjunction-without-conjunction case of Spector (2016, section 2.2.2). **Depth:** shallow.
- **Plain claim.** In the 4-world space S21, for the satisfiable disjunction p ∨ q (p = P0(0), q = P1(0)) with the explicitly supplied alternatives p, q, p ∧ q: naive exhaustification negates all three alternatives and is unsatisfiable, while innocent exclusion negates exactly one alternative, p ∧ q (the computed list `ieList` is [p ∧ q]), and yields the satisfiable exclusive disjunction (p ∨ q) ∧ ¬(p ∧ q). With the alternative list [p, q] (no conjunctive alternative), naive exhaustification is still unsatisfiable, while innocent exclusion negates nothing and is equivalent to the inclusive p ∨ q.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:102-106
theorem naive_exhaustification_of_disjunction_inconsistent :
    Sat S21 [pOrQ] ∧ naiveExcl S21 pOrQ disjAlts = disjAlts ∧
    ¬ Sat S21 [naiveExh S21 disjAlts pOrQ] ∧
    ieList S21 pOrQ disjAlts = [.and p0 q0] ∧ Sat S21 [exh S21 disjAlts pOrQ] ∧
    Equiv S21 (exh S21 disjAlts pOrQ) (.and pOrQ (.not (.and p0 q0))) := by …
```

```lean
-- lean/Implicature/Results.lean:112-114
theorem disjunction_without_conjunctive_alternative :
    naiveExcl S21 pOrQ [p0, q0] = [p0, q0] ∧ ¬ Sat S21 [naiveExh S21 [p0, q0] pOrQ] ∧
    ieList S21 pOrQ [p0, q0] = [] ∧ Equiv S21 (exh S21 [p0, q0] pOrQ) pOrQ := by …
```

Fixtures used: `pOrQ`, `disjAlts` (quoted under **Model definitions → Fixtures**).

**Hypothesis ledger.**

No hypotheses: the theorems on this card are closed statements about concrete instances, proved by kernel evaluation.

**Non-vacuity witness.** The instances themselves (Sat S21 [p ∨ q] is part of the first statement). Lean: `naive_exhaustification_of_disjunction_inconsistent`, `disjunction_without_conjunctive_alternative`.

**Further theorems cited in this card's non-claims:** `stdAlt_value_alternatives_any_connective` (quoted under **Cited supporting theorems**).

**Prior art.**

- D. Fox, "Free choice and the theory of scalar implicatures", in U. Sauerland and P. Stateva (eds.), Presupposition and Implicature in Compositional Semantics, Palgrave Macmillan, 2007, pp. 71-120, doi:10.1057/9780230210752_4. Defines innocent exclusion: an alternative is innocently excludable iff it belongs to every maximal set of alternatives whose negations are jointly consistent with the prejacent.
- U. Sauerland, "Scalar implicatures in complex sentences", Linguistics and Philosophy 27(3):367-391, 2004, doi:10.1023/B:LING.0000023378.71748.db. Uses the disjuncts and the conjunction as the alternatives of a disjunction (the alternative set used in the disjunction example here).
- M. Krifka, "Focus and presupposition in dynamic interpretation", Journal of Semantics 10(4):269-300, 1993, doi:10.1093/jos/10.4.269. The semantics of "only" that negates every alternative not entailed by the prejacent (the naive operator, called exh_krifka by Spector 2016).
- B. Spector, "Comparing exhaustivity operators", Semantics and Pragmatics 9(11):1-33, 2016, doi:10.3765/sp.9.11. Compares naive exhaustification (exh_krifka), minimal-worlds exhaustification (exh_mw) and innocent exclusion (exh_ie). Section 2.2.2 (pp. 8-9): for A or B with the alternative set {A, B} (no conjunctive alternative), exh_krifka is contradictory, exh_mw gives the exclusive reading, and exh_ie is vacuous.
- G. Chierchia, D. Fox and B. Spector, "Scalar implicature as a grammatical phenomenon", in C. Maienborn, K. von Heusinger and P. Portner (eds.), Semantics: An International Handbook of Natural Language Meaning, vol. 3, De Gruyter, 2012, pp. 2297-2332, doi:10.1515/9783110253382.2297. Survey of the exhaustification-operator approach to scalar implicature.

**Design question.** Can a summary checker model readers by negating every non-entailed alternative? (No: that reader can be inconsistent on satisfiable renderings.)

Basis: execution (Lean kernel check): `naive_exhaustification_of_disjunction_inconsistent`, `disjunction_without_conjunctive_alternative`.

Basis: derived (modeling bridge): A summary checker that models readers by negating every non-entailed alternative can attribute an inconsistent reading to a satisfiable summary. Reasoning: the instance is a plain disjunction with the textbook alternatives. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 4**.

#### Card 5. `innocent-exclusion-consistent`

- **Kind:** theorem. **Tier:** T1: Consistency is the design goal of innocent exclusion in Fox 2007; it is stated and mechanized here for arbitrary finite alternative lists over finite spaces. **Depth:** substantive.
- **Plain claim.** For every finite space S, every finite alternative list A and every claim σ: if σ is satisfiable in S, then exh S A σ is satisfiable in S, where exh S A σ is σ together with the negation of every alternative in the computed list ieList S σ A (which agrees with innocent excludability in Fox's sense by innocent-exclusion-computed-by-maximal-falsified-sets).

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:119-120
theorem innocent_exhaustification_consistent_of_sat (S : Space) (A : List Claim) (σ : Claim)
    (hσ : Sat S [σ]) : Sat S [exh S A σ] := …
```

Unfolded rendering of `innocent_exhaustification_consistent_of_sat` (Lean; definitionally equal to the statement after its binders):

```lean
(∃ w ∈ S.worlds, ∀ c ∈ [σ], S.holds w c = true) →
  ∃ w ∈ S.worlds, ∀ c ∈ [conjList (σ :: (ieList S σ A).map Claim.not)], S.holds w c = true
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hσ : Sat S [σ]` | exh S A σ has σ as a conjunct (definition of exh), so for an unsatisfiable σ it is unsatisfiable; instance in the counterexample | tight | `innocent_exh_consistent_tight` | the 4-world space S21 with the contradictory prejacent p0 ∧ ¬p0 and the empty alternative list | every theorem on this card |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:125-125
theorem innocent_exh_consistent_tight : ¬ Sat S21 [exh S21 [] (.and p0 (.not p0))] := by …
```

</details>

**Non-vacuity witness.** S21, σ = p0 ∨ q0 with the disjunction alternatives. Lean: `innocent_exh_consistent_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:129-130
theorem innocent_exh_consistent_nonvacuous :
    Sat S21 [pOrQ] ∧ Sat S21 [exh S21 disjAlts pOrQ] := by …
```

</details>

**Further theorems cited in this card's non-claims:** `exhaustification_reading_contradicted_though_literally_safe` (quoted under **Cited supporting theorems**).

**Prior art.**

- D. Fox, "Free choice and the theory of scalar implicatures", in U. Sauerland and P. Stateva (eds.), Presupposition and Implicature in Compositional Semantics, Palgrave Macmillan, 2007, pp. 71-120, doi:10.1057/9780230210752_4. Defines innocent exclusion: an alternative is innocently excludable iff it belongs to every maximal set of alternatives whose negations are jointly consistent with the prejacent.
- G. Chierchia, D. Fox and B. Spector, "Scalar implicature as a grammatical phenomenon", in C. Maienborn, K. von Heusinger and P. Portner (eds.), Semantics: An International Handbook of Natural Language Meaning, vol. 3, De Gruyter, 2012, pp. 2297-2332, doi:10.1515/9783110253382.2297. Survey of the exhaustification-operator approach to scalar implicature.

**Design question.** Is innocent exclusion a well-behaved reader model for safety checking, in the sense that it never contradicts a satisfiable rendering? (Yes in this sense: for every finite alternative list, a satisfiable rendering has a satisfiable innocent exhaustification.)

Basis: execution (Lean kernel check): `innocent_exhaustification_consistent_of_sat`, `innocent_exh_consistent_tight`, `innocent_exh_consistent_nonvacuous`.

Basis: derived (modeling bridge): A summary checker using innocent exclusion over a finite encoding of the claim space never attributes an inconsistent exhaustified reading to a satisfiable summary, whatever finite alternative list it is given. Reasoning: the theorem is general over finite spaces and alternative lists. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 5**.

#### Card 6. `innocent-exclusion-computed-by-maximal-falsified-sets`

- **Kind:** characterization. **Tier:** T0: Spector (2016, Proposition 7 and Corollary 8) proves that an alternative is innocently excludable iff minimal-worlds exhaustification entails its negation; over finitely many listed worlds the minimal worlds are the σ-worlds with inclusion-maximal falsified sets, so this is that result restated and mechanized. **Depth:** substantive.
- **Plain claim.** For every finite space S, prejacent σ, alternative list A and claim a: a ∈ ieList S σ A (that is, a ∈ A and a is false at every σ-world of S.worlds whose set of falsified alternatives is inclusion-maximal among the σ-worlds) iff a is innocently excludable in Fox's sense (a ∈ A and a belongs to every maximal subset of A whose negations are jointly consistent with σ).

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:135-136
theorem mem_ieList_iff_innocentlyExcludable (S : Space) (σ : Claim) (A : List Claim)
    (a : Claim) : a ∈ ieList S σ A ↔ InnocentlyExcludable S σ A a := …
```

Unfolded rendering of `mem_ieList_iff_innocentlyExcludable` (Lean; definitionally equal to the statement after its binders):

```lean
a ∈ A.filter (ieB S σ A) ↔ a ∈ A ∧ ∀ X, MaximalExclusion S σ A X → a ∈ X
```

**Hypothesis ledger.**

No hypotheses: the theorem is stated for all values of its parameters.

**Non-vacuity witness.** "All" is in the list and innocently excludable for "some" (S12); the empty maximal exclusion witnesses the case where both sides are false (innocentlyExcludable_neg). Lean: `ieList_characterization_instance`, `innocentlyExcludable_neg`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:140-142
theorem ieList_characterization_instance :
    (Claim.all xA) ∈ ieList S12 (.ex xA) [.all xA] ∧
      InnocentlyExcludable S12 (.ex xA) [.all xA] (.all xA) := …
```

```lean
-- lean/Implicature/Examples.lean:189-190
theorem innocentlyExcludable_neg :
    ¬ InnocentlyExcludable S12 (.all xA) [.ex xA] (.ex xA) := by …
```

</details>

**Further theorems cited in this card's non-claims:** `ieList_characterization_unsat_prejacent`, `exh_weaker_than_maximal_falsified_worlds` (quoted under **Cited supporting theorems**).

**Prior art.**

- D. Fox, "Free choice and the theory of scalar implicatures", in U. Sauerland and P. Stateva (eds.), Presupposition and Implicature in Compositional Semantics, Palgrave Macmillan, 2007, pp. 71-120, doi:10.1057/9780230210752_4. Defines innocent exclusion: an alternative is innocently excludable iff it belongs to every maximal set of alternatives whose negations are jointly consistent with the prejacent.
- B. Spector, "Comparing exhaustivity operators", Semantics and Pragmatics 9(11):1-33, 2016, doi:10.3765/sp.9.11. Compares naive exhaustification (exh_krifka), minimal-worlds exhaustification (exh_mw) and innocent exclusion (exh_ie). Proposition 7 and Corollary 8 (p. 12): an alternative is innocently excludable iff exh_mw entails its negation, so exh_ie conjoins the negations of exactly those alternatives; Theorem 9 (p. 13): exh_mw and exh_ie coincide when the alternatives are closed under conjunction.
- K. Schulz and R. van Rooij, "Pragmatic meaning and non-monotonic reasoning: The case of exhaustive interpretation", Linguistics and Philosophy 29(2):205-250, 2006, doi:10.1007/s10988-005-3760-4. Exhaustive interpretation by minimal models (the minimal-worlds operator).

**Design question.** Can the innocent-exclusion reader be decided efficiently over an explicit finite claim space? (Yes, by comparing falsified-alternative sets of worlds.)

Basis: execution (Lean kernel check): `mem_ieList_iff_innocentlyExcludable`, `ieList_characterization_instance`, `innocentlyExcludable_neg`.

Basis: derived (modeling bridge): A summary checker can compute innocent exclusion over an explicitly enumerated finite claim space by comparing the falsified-alternative sets of worlds. Reasoning: the characterization is general; the cost grows with the number of enumerated worlds. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 6**.

#### Card 7. `naive-exhaustification-entails-innocent`

- **Kind:** theorem. **Tier:** T0: Spector (2016, Corollary 2) proves that exh_krifka entails exh_ie; restated over finite listed worlds and mechanized. **Depth:** shallow.
- **Plain claim.** For every finite space S, alternative list A and claim σ: naive exhaustification of σ (σ and the negation of every alternative σ does not entail) entails innocent exhaustification of σ over the listed worlds.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:162-163
theorem naive_exh_entails_innocent_exh (S : Space) (A : List Claim) (σ : Claim) :
    Entails S [naiveExh S A σ] (exh S A σ) := …
```

Unfolded rendering of `naive_exh_entails_innocent_exh` (Lean; definitionally equal to the statement after its binders):

```lean
Entails S [conjList (σ :: (naiveExcl S σ A).map Claim.not)]
  (conjList (σ :: (ieList S σ A).map Claim.not))
```

**Hypothesis ledger.**

No hypotheses: the theorem is stated for all values of its parameters.

**Non-vacuity witness.** S12, σ = ∃x, A with alternatives [∀x, A], where the naive reading is satisfiable. Lean: `naive_exh_entails_innocent_instance`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:167-169
theorem naive_exh_entails_innocent_instance :
    Sat S12 [naiveExh S12 [.all xA] (.ex xA)] ∧
      Entails S12 [naiveExh S12 [.all xA] (.ex xA)] (exh S12 [.all xA] (.ex xA)) := by …
```

</details>

**Further theorems cited in this card's non-claims:** `innocent_exh_not_entails_naive_exh` (quoted under **Cited supporting theorems**).

**Prior art.**

- M. Krifka, "Focus and presupposition in dynamic interpretation", Journal of Semantics 10(4):269-300, 1993, doi:10.1093/jos/10.4.269. The semantics of "only" that negates every alternative not entailed by the prejacent (the naive operator, called exh_krifka by Spector 2016).
- B. Spector, "Comparing exhaustivity operators", Semantics and Pragmatics 9(11):1-33, 2016, doi:10.3765/sp.9.11. Compares naive exhaustification (exh_krifka), minimal-worlds exhaustification (exh_mw) and innocent exclusion (exh_ie). Corollary 2 (p. 11): exh_krifka entails both exh_mw and exh_ie.
- D. Fox, "Free choice and the theory of scalar implicatures", in U. Sauerland and P. Stateva (eds.), Presupposition and Implicature in Compositional Semantics, Palgrave Macmillan, 2007, pp. 71-120, doi:10.1057/9780230210752_4. Defines innocent exclusion: an alternative is innocently excludable iff it belongs to every maximal set of alternatives whose negations are jointly consistent with the prejacent.

**Design question.** Is the innocent reader ever stronger than the naive one? (No: for the same alternatives, naive exhaustification entails innocent exhaustification over the listed worlds, and the converse entailment fails in `innocent_exh_not_entails_naive_exh`.)

Basis: execution (Lean kernel check): `naive_exh_entails_innocent_exh`, `naive_exh_entails_innocent_instance`.

Basis: derived (modeling bridge): Replacing innocent exclusion by naive exhaustification in a summary checker never yields a weaker modeled reading, for the same alternatives. Reasoning: the entailment is general. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 7**.

#### Card 8. `innocent-equals-naive-iff-naive-consistent`

- **Kind:** characterization. **Tier:** T0: Spector (2016, Proposition 1) proves that a non-contradictory exh_krifka equals exh_ie; together with consistency of innocent exclusion for satisfiable prejacents this gives the equivalence, restated over finite listed worlds and mechanized. **Depth:** shallow.
- **Plain claim.** For every finite space S, alternative list A and claim σ: if σ is satisfiable in S, then innocent and naive exhaustification of σ are equivalent over the listed worlds iff naive exhaustification of σ is satisfiable.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:179-181
theorem innocent_equiv_naive_iff_naive_sat (S : Space) (A : List Claim) (σ : Claim)
    (hσ : Sat S [σ]) :
    Equiv S (exh S A σ) (naiveExh S A σ) ↔ Sat S [naiveExh S A σ] := …
```

Unfolded rendering of `innocent_equiv_naive_iff_naive_sat` (Lean; definitionally equal to the statement after its binders):

```lean
Sat S [σ] →
  ((Entails S [exh S A σ] (naiveExh S A σ) ∧ Entails S [naiveExh S A σ] (exh S A σ)) ↔
    Sat S [naiveExh S A σ])
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hσ : Sat S [σ]` | both readings have σ as a conjunct (definitions of exh and naiveExh), so for an unsatisfiable σ they are equivalent (both unsatisfiable) while the naive reading is not satisfiable; instance in the counterexample | tight | `innocent_equiv_naive_tight` | the 4-world space S21 with the contradictory prejacent p0 ∧ ¬p0 and alternatives [p0] | every theorem on this card |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:187-189
theorem innocent_equiv_naive_tight :
    ¬ (Equiv S21 (exh S21 [p0] (.and p0 (.not p0))) (naiveExh S21 [p0] (.and p0 (.not p0))) ↔
      Sat S21 [naiveExh S21 [p0] (.and p0 (.not p0))]) := by …
```

</details>

**Non-vacuity witness.** S12, ∃x, A with [∀x, A] (both sides true); S21, the disjunction (both sides false). Lean: `innocent_equiv_naive_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:193-195
theorem innocent_equiv_naive_nonvacuous :
    Sat S12 [.ex xA] ∧ Equiv S12 (exh S12 [.all xA] (.ex xA)) (naiveExh S12 [.all xA] (.ex xA)) ∧
    Sat S21 [pOrQ] ∧ ¬ Equiv S21 (exh S21 disjAlts pOrQ) (naiveExh S21 disjAlts pOrQ) := by …
```

</details>

**Prior art.**

- B. Spector, "Comparing exhaustivity operators", Semantics and Pragmatics 9(11):1-33, 2016, doi:10.3765/sp.9.11. Compares naive exhaustification (exh_krifka), minimal-worlds exhaustification (exh_mw) and innocent exclusion (exh_ie). Proposition 1 (p. 11): if exh_krifka is not the contradiction, exh_krifka = exh_mw = exh_ie.
- D. Fox, "Free choice and the theory of scalar implicatures", in U. Sauerland and P. Stateva (eds.), Presupposition and Implicature in Compositional Semantics, Palgrave Macmillan, 2007, pp. 71-120, doi:10.1057/9780230210752_4. Defines innocent exclusion: an alternative is innocently excludable iff it belongs to every maximal set of alternatives whose negations are jointly consistent with the prejacent.
- G. Chierchia, D. Fox and B. Spector, "Scalar implicature as a grammatical phenomenon", in C. Maienborn, K. von Heusinger and P. Portner (eds.), Semantics: An International Handbook of Natural Language Meaning, vol. 3, De Gruyter, 2012, pp. 2297-2332, doi:10.1515/9783110253382.2297. Survey of the exhaustification-operator approach to scalar implicature.

**Design question.** For a satisfiable rendering, when can the simpler naive reader stand in for innocent exclusion? (Exactly when the naive reading is satisfiable, given that the rendering is satisfiable.)

Basis: execution (Lean kernel check): `innocent_equiv_naive_iff_naive_sat`, `innocent_equiv_naive_tight`, `innocent_equiv_naive_nonvacuous`.

Basis: derived (modeling bridge): For a satisfiable summary, a checker may substitute the naive reader for innocent exclusion exactly when the naive reading is satisfiable. Reasoning: the characterization is general. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 8**.

#### Card 9. `exhaustification-not-monotone-antitone-or-reflecting`

- **Kind:** counterexample. **Tier:** T1: Non-monotonicity of exhaustification is well known ("all" entails "some" but contradicts "some but not all"); the precise countermodels are stated here. **Depth:** shallow.
- **Plain claim.** With the standard alternatives in the 4-world space S12: ∀x, A entails ∃x, A, but neither exhaustified reading entails the other; and exh(∃x, A) entails exh(¬∀x, A) although ∃x, A does not entail ¬∀x, A.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:201-206
theorem exh_neither_monotone_nor_antitone :
    Entails S12 [.all xA] (.ex xA) ∧
    ¬ Entails S12 [exh S12 (stdAlt S12 (.all xA)) (.all xA)]
        (exh S12 (stdAlt S12 (.ex xA)) (.ex xA)) ∧
    ¬ Entails S12 [exh S12 (stdAlt S12 (.ex xA)) (.ex xA)]
        (exh S12 (stdAlt S12 (.all xA)) (.all xA)) := by …
```

```lean
-- lean/Implicature/Results.lean:211-214
theorem exh_entailment_does_not_reflect :
    Entails S12 [exh S12 (stdAlt S12 (.ex xA)) (.ex xA)]
      (exh S12 (stdAlt S12 (.not (.all xA))) (.not (.all xA))) ∧
    ¬ Entails S12 [.ex xA] (.not (.all xA)) := by …
```

**Hypothesis ledger.**

No hypotheses: the theorems on this card are closed statements about concrete instances, proved by kernel evaluation.

**Non-vacuity witness.** The instances themselves. Lean: `exh_neither_monotone_nor_antitone`, `exh_entailment_does_not_reflect`.

**Further theorems cited in this card's non-claims:** `stdAlt_value_alternatives_any_connective` (quoted under **Cited supporting theorems**).

**Prior art.**

- L. R. Horn, A Natural History of Negation, University of Chicago Press, 1989 (reissued by CSLI Publications, Stanford, 2001, ISBN 1-57586-336-7); chapter 4, "Negation and Quantity", develops quantity scales such as <all, some> and the scalar implicature from "some" to "not all".
- G. Chierchia, D. Fox and B. Spector, "Scalar implicature as a grammatical phenomenon", in C. Maienborn, K. von Heusinger and P. Portner (eds.), Semantics: An International Handbook of Natural Language Meaning, vol. 3, De Gruyter, 2012, pp. 2297-2332, doi:10.1515/9783110253382.2297. Survey of the exhaustification-operator approach to scalar implicature.
- K. Schulz and R. van Rooij, "Pragmatic meaning and non-monotonic reasoning: The case of exhaustive interpretation", Linguistics and Philosophy 29(2):205-250, 2006, doi:10.1007/s10988-005-3760-4. Exhaustive interpretation by minimal models (the minimal-worlds operator).

**Design question.** Can a summary checker reason about exhaustified readings compositionally by entailment? (Not by monotonicity in either direction.)

Basis: execution (Lean kernel check): `exh_neither_monotone_nor_antitone`, `exh_entailment_does_not_reflect`.

Basis: derived (modeling bridge): A summary checker cannot in general infer the exhaustified reading of one summary from that of a weaker or stronger summary by entailment. Reasoning: the countermodels use "all", "some" and "not all". This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 9**.

#### Card 10. `computed-blockers-sound`

- **Kind:** theorem. **Tier:** T1: Formalizes the practice of adding explicit non-claims; the statement is new in form but conceptually folklore. **Depth:** shallow.
- **Plain claim.** For every finite space S, alternative function alt, report E and rendering σ: if E ⊨ σ, then flagging the computed blocker set blockers S alt E σ (the rules that contribute an uncancelled reading E does not entail) makes σ strengthening-safe for the one-step reader `readings`.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:221-222
theorem blockers_sound (S : Space) (alt : Claim → List Claim) (E : List Claim) (σ : Claim)
    (hlit : LiterallySafe S E σ) : StrengtheningSafe S alt (blockers S alt E σ) E σ := …
```

Unfolded rendering of `blockers_sound` (Lean; definitionally equal to the statement after its binders):

```lean
Entails S E σ → ∀ ρ ∈ readings S alt (blockers S alt E σ) σ, Entails S E ρ
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hlit : LiterallySafe S E σ` | the literal reading is always among the readings; no flag can block it | tight | `blockers_sound_tight` | the 4-world space S21 with the empty report, σ = p0 and the standard alternatives | every theorem on this card |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:227-228
theorem blockers_sound_tight :
    ¬ StrengtheningSafe S21 (stdAlt S21) (blockers S21 (stdAlt S21) [] p0) [] p0 := by …
```

</details>

**Non-vacuity witness.** S22, E_notConv, σ = ∀x, A→B: the computed blocker set is [perfection] and makes σ safe. Lean: `blockers_sound_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:232-235
theorem blockers_sound_nonvacuous :
    LiterallySafe S22 E_notConv (.all (.imp xA xB)) ∧
    blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] ∧
    StrengtheningSafe S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) := by …
```

</details>

**Further theorems cited in this card's non-claims:** `composing_reader_minimal_blocker_sets_not_unique` (quoted under **Cited supporting theorems**).

**Prior art.**

- H. P. Grice, "Logic and conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics 3: Speech Acts, Academic Press, 1975, pp. 41-58 (Brill reissue doi:10.1163/9789004368811_003). Introduces conversational implicature and its cancellability; the cancellation filter of the reader model is a toy version of cancellability.

**Design question.** Can the explicit blockers a summary needs be computed from the report? (Yes, for the one-step reader, by deciding entailment of each rule's uncancelled readings.)

Basis: execution (Lean kernel check): `blockers_sound`, `blockers_sound_tight`, `blockers_sound_nonvacuous`.

Basis: derived (modeling bridge): A real summary that the report entails, carrying one non-claim for each computed blocker (phrased as in the doc comment of `Rule`), is safe against the modeled one-step reader. Reasoning: flags are modeled as out-of-band annotations; whether a real phrase disables a real reader's inference is the modeling assumption. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 10**.

#### Card 11. `computed-blockers-minimal`

- **Kind:** theorem. **Tier:** T1: As for computed-blockers-sound. **Depth:** shallow.
- **Plain claim.** For every finite space S, alternative function alt, report E, rendering σ and flag set F, for the one-step reader `readings`: (a) if σ is strengthening-safe under F, then F contains every rule of the computed blocker set; (b) if E ⊨ σ, then σ is strengthening-safe under F iff F contains every rule of the computed blocker set, so the computed blocker set is the least safe flag set (up to rule membership).

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:240-242
theorem blockers_subset_of_strengtheningSafe (S : Space) (alt : Claim → List Claim)
    (E : List Claim) (σ : Claim) (F : List Rule) (hsafe : StrengtheningSafe S alt F E σ) :
    ∀ r ∈ blockers S alt E σ, r ∈ F := …
```

Unfolded rendering of `blockers_subset_of_strengtheningSafe` (Lean; definitionally equal to the statement after its binders):

```lean
(∀ ρ ∈ readings S alt F σ, Entails S E ρ) → ∀ r ∈ blockers S alt E σ, r ∈ F
```

```lean
-- lean/Implicature/Results.lean:248-250
theorem strengtheningSafe_iff_blockers_subset (S : Space) (alt : Claim → List Claim)
    (E : List Claim) (σ : Claim) (F : List Rule) (hlit : LiterallySafe S E σ) :
    StrengtheningSafe S alt F E σ ↔ ∀ r ∈ blockers S alt E σ, r ∈ F := …
```

Unfolded rendering of `strengtheningSafe_iff_blockers_subset` (Lean; definitionally equal to the statement after its binders):

```lean
Entails S E σ → ((∀ ρ ∈ readings S alt F σ, Entails S E ρ) ↔ ∀ r ∈ blockers S alt E σ, r ∈ F)
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hsafe : StrengtheningSafe S alt F E σ` | statement (a): minimality is relative to flag sets that achieve safety | tight | `blockers_minimal_tight` | the 16-world space S22 with E_notConv, σ = ∀x, A→B and F = [] | `blockers_subset_of_strengtheningSafe` |
| `hlit : LiterallySafe S E σ` | statement (b): the literal reading σ is among the readings under every flag set (definition of readings), so without literal safety no flag set is safe, while the computed blocker set is contained in itself | tight | `blockers_iff_tight_hlit` | the 4-world space S21 with the empty report, σ = p0 and F the computed blocker set | `strengtheningSafe_iff_blockers_subset` |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:255-256
theorem blockers_minimal_tight :
    ¬ (∀ r ∈ blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)), r ∈ ([] : List Rule)) := by …
```

```lean
-- lean/Implicature/Results.lean:261-264
theorem blockers_iff_tight_hlit :
    ¬ LiterallySafe S21 [] p0 ∧
    ¬ (StrengtheningSafe S21 (stdAlt S21) (blockers S21 (stdAlt S21) [] p0) [] p0 ↔
        ∀ r ∈ blockers S21 (stdAlt S21) [] p0, r ∈ blockers S21 (stdAlt S21) [] p0) := by …
```

</details>

**Non-vacuity witness.** (a) S22, E_notConv, σ = ∀x, A→B, F = [perfection]; (b) the same instance, with E ⊨ σ. Lean: `strengtheningSafe_pos`, `blockers_sound_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Examples.lean:274-275
theorem strengtheningSafe_pos :
    StrengtheningSafe S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Results.lean:232-235
theorem blockers_sound_nonvacuous :
    LiterallySafe S22 E_notConv (.all (.imp xA xB)) ∧
    blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] ∧
    StrengtheningSafe S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) := by …
```

</details>

**Further theorems cited in this card's non-claims:** `composing_reader_minimal_blocker_sets_not_unique` (quoted under **Cited supporting theorems**).

**Prior art.**

- H. P. Grice, "Logic and conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics 3: Speech Acts, Academic Press, 1975, pp. 41-58 (Brill reissue doi:10.1163/9789004368811_003). Introduces conversational implicature and its cancellability; the cancellation filter of the reader model is a toy version of cancellability.

**Design question.** Is there a canonical, smallest set of non-claims a summary must carry? (Yes for the one-step reader, for literally safe renderings.)

Basis: execution (Lean kernel check): `blockers_subset_of_strengtheningSafe`, `strengtheningSafe_iff_blockers_subset`, `blockers_minimal_tight`, `blockers_iff_tight_hlit`, `strengtheningSafe_pos`, `blockers_sound_nonvacuous`.

Basis: derived (modeling bridge): For a summary that the report entails, the computed rule-level non-claims form the least set of rule-level non-claims that makes it safe against the modeled one-step reader. Reasoning: the characterization is general over alternative functions. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 11**.

#### Card 12. `composing-reader-minimal-blockers-not-unique`

- **Kind:** counterexample. **Tier:** T1: Not found in the cited literature; a direct consequence of letting strengthening rules compose, recorded as a precise countermodel. **Depth:** shallow.
- **Plain claim.** With the standard alternatives in the 64-world space S32, for the report E_relCond (∀x, A→B; ∀x, H⇒(B→A); ∃x, B∧¬A) and the literally safe rendering ∀x, H⇒(A→B): the one-step blocker set is {exhaustification} and suffices for the one-step reader `readings`, but for the composing reader `readingsStar` it is insufficient, and among the eight flag sets the safe ones have exactly two minimal elements, {exhaustification, qualifierDrop} and {exhaustification, perfection}.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:276-286
theorem composing_reader_minimal_blocker_sets_not_unique :
    LiterallySafe S32 E_relCond σ_relCond ∧
    blockers S32 (stdAlt S32) E_relCond σ_relCond = [.exhaustification] ∧
    StrengtheningSafe S32 (stdAlt S32) [.exhaustification] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [.exhaustification] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [.qualifierDrop] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [.perfection] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [.qualifierDrop, .perfection] E_relCond σ_relCond ∧
    StrengtheningSafeStar S32 (stdAlt S32) [.exhaustification, .qualifierDrop] E_relCond σ_relCond ∧
    StrengtheningSafeStar S32 (stdAlt S32) [.exhaustification, .perfection] E_relCond σ_relCond := by …
```

Fixtures used: `σ_relCond`, `E_relCond` (quoted under **Model definitions → Fixtures**).

**Hypothesis ledger.**

No hypotheses: the theorems on this card are closed statements about concrete instances, proved by kernel evaluation.

**Non-vacuity witness.** The instance itself (LiterallySafe is part of the statement). Lean: `composing_reader_minimal_blocker_sets_not_unique`.

**Further theorems cited in this card's non-claims:** `composing_reader_some_safe_flag_set_iff_literally_safe`, `stdAlt_value_alternatives_any_connective` (quoted under **Cited supporting theorems**).

**Prior art.**

- No prior statement found; the composing reader is defined here.

**Design question.** Does "the minimal set of blockers" remain well defined when readers chain strengthenings (drop the hypothesis, then perfect)? (No: in this instance there are two incomparable minimal safe flag sets.)

Basis: execution (Lean kernel check): `composing_reader_minimal_blocker_sets_not_unique`.

Basis: derived (modeling bridge): For readers that chain strengthenings, a summary checker cannot assume a single least set of rule-level non-claims; in the instance it must choose between two incomparable minimal sets. Reasoning: the countermodel's report and rendering have realistic shape. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 12**.

#### Card 13. `conclusion-dropping-preserves-literal-safety`

- **Kind:** theorem. **Tier:** T0: Conjunction elimination. **Depth:** definitional.
- **Plain claim.** For every finite space S, report E, hypothesis H and conclusion lists Cs, Cs': if E ⊨ nf H Cs (E proves ∀x, H ⇒ C for every C in Cs) and every member of Cs' is in Cs, then E ⊨ nf H Cs'.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:301-303
theorem conclusion_dropping_preserves_literal_safety (S : Space) (E : List Claim) (H : Claim)
    (Cs Cs' : List Claim) (hE : LiterallySafe S E (nf H Cs)) (hsub : ∀ c ∈ Cs', c ∈ Cs) :
    LiterallySafe S E (nf H Cs') := …
```

Unfolded rendering of `conclusion_dropping_preserves_literal_safety` (Lean; definitionally equal to the statement after its binders):

```lean
Entails S E (conjList (Cs.map fun c => Claim.all (Claim.rel H c))) →
  (∀ c ∈ Cs', c ∈ Cs) →
  Entails S E (conjList (Cs'.map fun c => Claim.all (Claim.rel H c)))
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hE : LiterallySafe S E (nf H Cs)` | the report proves the normal-form claim | tight | `conclusion_dropping_tight_hE` | the 64-world space S32 with the empty report, H = xH and Cs = Cs' = [xA] | every theorem on this card |
| `hsub : ∀ c ∈ Cs', c ∈ Cs` | Cs' keeps whole conclusions of Cs (every member of Cs' is a member of Cs) | tight | `conclusion_dropping_tight_hsub` | the 64-world space S32 with report [∀x, H⇒A], Cs = [A] and the added conclusion Cs' = [A, B] | every theorem on this card |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:308-309
theorem conclusion_dropping_tight_hE :
    (∀ c ∈ [xA], c ∈ [xA]) ∧ ¬ LiterallySafe S32 [] (nf xH [xA]) := by …
```

```lean
-- lean/Implicature/Results.lean:314-316
theorem conclusion_dropping_tight_hsub :
    LiterallySafe S32 [nf xH [xA]] (nf xH [xA]) ∧
    ¬ LiterallySafe S32 [nf xH [xA]] (nf xH [xA, xB]) := by …
```

</details>

**Non-vacuity witness.** S32, E = [nf H [A, B]], Cs' = [B]. Lean: `conclusion_dropping_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:320-322
theorem conclusion_dropping_nonvacuous :
    LiterallySafe S32 [nf xH [xA, xB]] (nf xH [xA, xB]) ∧ (∀ c ∈ [xB], c ∈ [xA, xB]) ∧
    LiterallySafe S32 [nf xH [xA, xB]] (nf xH [xB]) := by …
```

</details>

**Further theorems cited in this card's non-claims:** `inherited_blockers_insufficient_after_conclusion_drop` (quoted under **Cited supporting theorems**).

**Prior art.**

- Standard; no specific source is relied on.

**Design question.** Reference point: which compressions of a theorem statement keep it literally true? (Dropping whole conclusions while keeping hypothesis and domain.)

Basis: execution (Lean kernel check): `conclusion_dropping_preserves_literal_safety`, `conclusion_dropping_tight_hE`, `conclusion_dropping_tight_hsub`, `conclusion_dropping_nonvacuous`.

Basis: derived (modeling bridge): Dropping whole conclusions of a real theorem statement, keeping its hypothesis and quantifier domain, keeps the summary literally true. Reasoning: conjunction elimination involves no reader assumption. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 13**.

#### Card 14. `compression-with-recomputed-blockers-safe`

- **Kind:** theorem. **Tier:** T1: Combines conclusion dropping with the computed blockers; folklore made precise. **Depth:** shallow.
- **Plain claim.** For every finite space S, alternative function alt, report E, list R of normal-form entries and compression comp, for the one-step reader `readings`: if E proves the normal-form claim of every entry of R, and comp is a conclusion-dropping compression of R (each compressed entry keeps the hypothesis of some entry of R, and each of its conclusions is a conclusion of that entry), then the rendering of comp is strengthening-safe (a) under the blocker set computed for that rendering relative to E, and (b) under the blocker set computed for that rendering relative to the normal-form claims of R alone.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:328-331
theorem compression_with_recomputed_blockers_strengthening_safe (S : Space)
    (alt : Claim → List Claim) (E : List Claim) (R comp : List (Claim × List Claim))
    (hR : ∀ q ∈ R, LiterallySafe S E (nfOf q)) (hcomp : ConclusionDropping R comp) :
    StrengtheningSafe S alt (blockers S alt E (renderComp comp)) E (renderComp comp) := …
```

Unfolded rendering of `compression_with_recomputed_blockers_strengthening_safe` (Lean; definitionally equal to the statement after its binders):

```lean
(∀ q ∈ R, Entails S E (nf q.1 q.2)) →
  (∀ p ∈ comp, ∃ q ∈ R, q.1 = p.1 ∧ ∀ c ∈ p.2, c ∈ q.2) →
  ∀ ρ ∈ readings S alt (blockers S alt E (renderComp comp)) (renderComp comp), Entails S E ρ
```

```lean
-- lean/Implicature/Results.lean:336-340
theorem compression_with_entry_blockers_strengthening_safe (S : Space)
    (alt : Claim → List Claim) (E : List Claim) (R comp : List (Claim × List Claim))
    (hR : ∀ q ∈ R, LiterallySafe S E (nfOf q)) (hcomp : ConclusionDropping R comp) :
    StrengtheningSafe S alt (blockers S alt (R.map nfOf) (renderComp comp)) E
      (renderComp comp) := by …
```

Fixtures used: `R_comp`, `E_comp` (quoted under **Model definitions → Fixtures**).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hR : ∀ q ∈ R, LiterallySafe S E (nfOf q)` | the report proves the claims being compressed | tight | `compression_tight_hR` | the 64-world space S32 with the empty report and R = comp = [(H, [A])] | every theorem on this card |
| `hcomp : ConclusionDropping R comp` | whole conclusions are dropped; hypotheses and domains are kept | tight | `compression_tight_hcomp` | the 64-world space S32 with report [∀x, H⇒A] and the compressed entry (⊤, [A]), which drops the hypothesis | every theorem on this card |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:351-357
theorem compression_tight_hR :
    ConclusionDropping [(xH, [xA])] [(xH, [xA])] ∧
    ¬ StrengtheningSafe S32 (stdAlt S32) (blockers S32 (stdAlt S32) [] (renderComp [(xH, [xA])])) []
        (renderComp [(xH, [xA])]) ∧
    ¬ StrengtheningSafe S32 (stdAlt S32)
        (blockers S32 (stdAlt S32) ([(xH, [xA])].map nfOf) (renderComp [(xH, [xA])])) []
        (renderComp [(xH, [xA])]) := by …
```

```lean
-- lean/Implicature/Results.lean:363-370
theorem compression_tight_hcomp :
    (∀ q ∈ [(xH, [xA])], LiterallySafe S32 [nf xH [xA]] (nfOf q)) ∧
    ¬ StrengtheningSafe S32 (stdAlt S32)
        (blockers S32 (stdAlt S32) [nf xH [xA]] (renderComp [(.top, [xA])])) [nf xH [xA]]
        (renderComp [(.top, [xA])]) ∧
    ¬ StrengtheningSafe S32 (stdAlt S32)
        (blockers S32 (stdAlt S32) ([(xH, [xA])].map nfOf) (renderComp [(.top, [xA])]))
        [nf xH [xA]] (renderComp [(.top, [xA])]) := by …
```

</details>

**Non-vacuity witness.** S32, R_comp = [(H, [A, B])], E_comp, comp = [(H, [A])]. Lean: `compression_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:381-387
theorem compression_nonvacuous :
    (∀ q ∈ R_comp, LiterallySafe S32 E_comp (nfOf q)) ∧ ConclusionDropping R_comp [(xH, [xA])] ∧
    StrengtheningSafe S32 (stdAlt S32) (blockers S32 (stdAlt S32) E_comp (renderComp [(xH, [xA])]))
      E_comp (renderComp [(xH, [xA])]) ∧
    StrengtheningSafe S32 (stdAlt S32)
      (blockers S32 (stdAlt S32) (R_comp.map nfOf) (renderComp [(xH, [xA])]))
      E_comp (renderComp [(xH, [xA])]) := by …
```

</details>

**Further theorems cited in this card's non-claims:** `inherited_blockers_insufficient_after_conclusion_drop`, `inherited_blockers_superfluous_after_conclusion_drop`, `entry_blockers_strictly_larger_than_report_blockers`, `duplicated_conclusion_keeps_perfection_hazard`, `composing_reader_minimal_blocker_sets_not_unique` (quoted under **Cited supporting theorems**).

**Prior art.**

- H. P. Grice, "Logic and conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics 3: Speech Acts, Academic Press, 1975, pp. 41-58 (Brill reissue doi:10.1163/9789004368811_003). Introduces conversational implicature and its cancellability; the cancellation filter of the reader model is a toy version of cancellability.

**Design question.** What is a safe recipe for compressing a theorem into a headline under this reader model? (Drop whole conclusions, keep hypotheses and domains, and recompute the blockers for what remains, either from the report or from the normal-form entries alone.)

Basis: execution (Lean kernel check): `compression_with_recomputed_blockers_strengthening_safe`, `compression_with_entry_blockers_strengthening_safe`, `compression_tight_hR`, `compression_tight_hcomp`, `compression_nonvacuous`.

Basis: derived (modeling bridge): A headline obtained from proved normal-form claims by dropping whole conclusions, with rule-level non-claims recomputed for the headline, is safe against the modeled one-step reader. Reasoning: the theorem is general over alternative functions. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 14**.

#### Card 15. `inherited-blockers-can-be-insufficient-or-superfluous-after-compression`

- **Kind:** counterexample. **Tier:** T1: Not found in the cited literature; precise countermodels for reusing the blockers of a full statement after compression. **Depth:** shallow.
- **Plain claim.** For the one-step reader with the standard alternatives: (i) in the 16-world space S22, for the report E_unc consisting of the normal-form claims ∀x, ⊤⇒(A→B) and ∀x, ⊤⇒(B∧¬A), the full rendering has an empty computed blocker set (its perfected reading is inconsistent with the rendering and is cancelled) and is strengthening-safe with no flags, while the compressed rendering ∀x, ⊤⇒(A→B) obtained by dropping the second conclusion has computed blocker set {perfection}: its perfected reading ∀x, ⊤⇒(A↔B) is drawn and is contradicted by E_unc, and the inherited (empty) flag set leaves it unsafe; (ii) in the 64-world space S32, for the report E_comp (∀x, H⇒A; ∀x, H⇒B; ∀x, A; ¬∀x, B), the full rendering has computed blocker set {qualifierDrop, exhaustification} and the compressed rendering ∀x, H⇒A has computed blocker set {exhaustification}: its exhaustified reading is equivalent to (∀x, H⇒A) ∧ ¬(∀x, A), is contradicted by E_comp, and does not entail "H is needed for A"; the inherited flags make the compressed rendering safe but include the unneeded qualifierDrop.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:412-425
theorem inherited_blockers_insufficient_after_conclusion_drop :
    Sat S22 E_unc ∧ (∀ q ∈ R_unc, LiterallySafe S22 E_unc (nfOf q)) ∧
    ConclusionDropping R_unc [(.top, [.imp xA xB])] ∧
    (Claim.and (.all (.rel .top (.iff xA xB))) (.all (.rel .top (.and xB (.not xA))))) ∈
      step S22 (stdAlt S22) .perfection (renderComp R_unc) ∧
    ¬ Sat S22 [renderComp R_unc,
      .and (.all (.rel .top (.iff xA xB))) (.all (.rel .top (.and xB (.not xA))))] ∧
    blockers S22 (stdAlt S22) E_unc (renderComp R_unc) = [] ∧
    StrengtheningSafe S22 (stdAlt S22) [] E_unc (renderComp R_unc) ∧
    (Claim.all (.rel .top (.iff xA xB))) ∈
      readings S22 (stdAlt S22) [] (renderComp [(.top, [.imp xA xB])]) ∧
    Contradicts S22 E_unc (.all (.rel .top (.iff xA xB))) ∧
    blockers S22 (stdAlt S22) E_unc (renderComp [(.top, [.imp xA xB])]) = [.perfection] ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [] E_unc (renderComp [(.top, [.imp xA xB])]) := by …
```

```lean
-- lean/Implicature/Results.lean:433-446
theorem inherited_blockers_superfluous_after_conclusion_drop :
    Sat S32 E_comp ∧ (∀ q ∈ R_comp, LiterallySafe S32 E_comp (nfOf q)) ∧
    ConclusionDropping R_comp [(xH, [xA])] ∧
    blockers S32 (stdAlt S32) E_comp (renderComp R_comp) = [.qualifierDrop, .exhaustification] ∧
    blockers S32 (stdAlt S32) E_comp (renderComp [(xH, [xA])]) = [.exhaustification] ∧
    Equiv S32 (exh S32 (stdAlt S32 (renderComp [(xH, [xA])])) (renderComp [(xH, [xA])]))
      (.and (.all (.rel xH xA)) (.not (.all xA))) ∧
    Contradicts S32 E_comp
      (exh S32 (stdAlt S32 (renderComp [(xH, [xA])])) (renderComp [(xH, [xA])])) ∧
    ¬ Entails S32 [exh S32 (stdAlt S32 (renderComp [(xH, [xA])])) (renderComp [(xH, [xA])])]
      (needed xH xA) ∧
    StrengtheningSafe S32 (stdAlt S32) [.qualifierDrop, .exhaustification] E_comp
      (renderComp [(xH, [xA])]) ∧
    StrengtheningSafe S32 (stdAlt S32) [.exhaustification] E_comp (renderComp [(xH, [xA])]) := by …
```

Fixtures used: `R_unc`, `E_unc`, `R_comp`, `E_comp` (quoted under **Model definitions → Fixtures**).

**Hypothesis ledger.**

No hypotheses: the theorems on this card are closed statements about concrete instances, proved by kernel evaluation.

**Non-vacuity witness.** The instances themselves (each includes Sat S E and literal safety of the entries). Lean: `inherited_blockers_insufficient_after_conclusion_drop`, `inherited_blockers_superfluous_after_conclusion_drop`.

**Further theorems cited in this card's non-claims:** `stdAlt_value_alternatives_any_connective`, `composing_reader_minimal_blocker_sets_not_unique` (quoted under **Cited supporting theorems**).

**Prior art.**

- No prior statement found.

**Design question.** Can a compressed headline reuse the blocker flags computed for the full statement? (Not in general: inherited flags can be insufficient (i) or include unneeded flags (ii); recompute them for the compressed rendering.)

Basis: execution (Lean kernel check): `inherited_blockers_insufficient_after_conclusion_drop`, `inherited_blockers_superfluous_after_conclusion_drop`.

Basis: derived (modeling bridge): Rule-level non-claims computed for a full theorem statement can be wrong for a compressed headline: missing (instance (i)) or superfluous (instance (ii)). Reasoning: the instances have realistic shape. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 15**.

#### Card 16. `hypothesis-dropping-literally-safe-iff-proved-where-hypothesis-fails`

- **Kind:** characterization. **Tier:** T0: Case analysis on the hypothesis under a universally quantified conditional. **Depth:** definitional.
- **Plain claim.** For every finite space S, report E, hypothesis H and conclusion list Cs: (a) if E ⊨ nf H Cs (E proves ∀x, H ⇒ C for every C in Cs), then the hypothesis-dropped rendering nf ⊤ Cs is literally safe iff E ⊨ nf (¬H) Cs (E also proves ∀x, ¬H ⇒ C for every C in Cs); (b) nf ⊤ Cs is literally safe iff E ⊨ ∀x, ⋀Cs.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:471-473
theorem hypothesis_dropping_literally_safe_iff_proved_where_hypothesis_fails (S : Space)
    (E : List Claim) (H : Claim) (Cs : List Claim) (hE : LiterallySafe S E (nf H Cs)) :
    LiterallySafe S E (nf .top Cs) ↔ LiterallySafe S E (nf (.not H) Cs) := by …
```

Unfolded rendering of `hypothesis_dropping_literally_safe_iff_proved_where_hypothesis_fails` (Lean; definitionally equal to the statement after its binders):

```lean
Entails S E (nf H Cs) →
  (Entails S E (nf Claim.top Cs) ↔ Entails S E (nf (Claim.not H) Cs))
```

```lean
-- lean/Implicature/Results.lean:451-452
theorem nf_top_literally_safe_iff_unconditional (S : Space) (E : List Claim) (Cs : List Claim) :
    LiterallySafe S E (nf .top Cs) ↔ LiterallySafe S E (.all (conjList Cs)) := by …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hE : LiterallySafe S E (nf H Cs)` | statement (a): without it, a report that proves the conclusions where H fails, but not where H holds, satisfies the right-hand side but not the left; instance in the counterexample | tight | `hypothesis_dropping_tight_hE` | the 64-world space S32 with report [∀x, ¬H⇒A] and Cs = [A] | `hypothesis_dropping_literally_safe_iff_proved_where_hypothesis_fails` |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:501-503
theorem hypothesis_dropping_tight_hE :
    ¬ (LiterallySafe S32 [nf (.not xH) [xA]] (nf .top [xA]) ↔
        LiterallySafe S32 [nf (.not xH) [xA]] (nf (.not xH) [xA])) := by …
```

</details>

**Non-vacuity witness.** Both sides true: E = [∀x, H⇒A, ∀x, ¬H⇒A]; both sides false: E = [∀x, H⇒A] (S32). Lean: `hypothesis_dropping_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:508-514
theorem hypothesis_dropping_nonvacuous :
    LiterallySafe S32 [nf xH [xA], nf (.not xH) [xA]] (nf xH [xA]) ∧
    LiterallySafe S32 [nf xH [xA], nf (.not xH) [xA]] (nf .top [xA]) ∧
    LiterallySafe S32 [nf xH [xA], nf (.not xH) [xA]] (nf (.not xH) [xA]) ∧
    LiterallySafe S32 [nf xH [xA]] (nf xH [xA]) ∧
    ¬ LiterallySafe S32 [nf xH [xA]] (nf .top [xA]) ∧
    ¬ LiterallySafe S32 [nf xH [xA]] (nf (.not xH) [xA]) := by …
```

</details>

**Further theorems cited in this card's non-claims:** `inherited_blockers_insufficient_after_conclusion_drop`, `blockers_sound` (quoted under **Cited supporting theorems**).

**Prior art.**

- Standard; no specific source is relied on.

**Design question.** Reference point: when may a summary omit a hypothesis? (Given that the report proves the claim under the hypothesis: exactly when the report also proves the conclusions where the hypothesis fails.)

Basis: execution (Lean kernel check): `hypothesis_dropping_literally_safe_iff_proved_where_hypothesis_fails`, `nf_top_literally_safe_iff_unconditional`, `hypothesis_dropping_tight_hE`, `hypothesis_dropping_nonvacuous`.

Basis: derived (modeling bridge): A real summary may omit a hypothesis H of a proved claim, and remain literally true, exactly when the report also proves the conclusions where H fails. Reasoning: the characterization is general. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 16**.

#### Card 17. `necessity-rendering-contradicted-iff-counterexample-proved`

- **Kind:** characterization. **Tier:** T0: Duality of ∀ and ∃ over a finite domain. **Depth:** definitional.
- **Plain claim.** For every finite space S, report E and claims X, Y: the rendering "X is needed for Y", read literally as ∀x, Y→X, is contradicted by E iff E proves ∃x, Y ∧ ¬X.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:521-522
theorem necessity_rendering_contradicted_iff_counterexample (S : Space) (E : List Claim)
    (X Y : Claim) : Contradicts S E (needed X Y) ↔ Entails S E (.ex (.and Y (.not X))) := by …
```

Unfolded rendering of `necessity_rendering_contradicted_iff_counterexample` (Lean; definitionally equal to the statement after its binders):

```lean
Entails S E (Claim.not (Claim.all (Claim.imp Y X))) ↔
  Entails S E (Claim.ex (Claim.and Y (Claim.not X)))
```

**Hypothesis ledger.**

No hypotheses: the theorem is stated for all values of its parameters.

**Non-vacuity witness.** S22: the report [∃x, B ∧ ¬A] makes both sides true for X = A, Y = B; the empty report makes both false. Lean: `necessity_rendering_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:527-530
theorem necessity_rendering_nonvacuous :
    Contradicts S22 [.ex (.and xB (.not xA))] (needed xA xB) ∧
    Entails S22 [.ex (.and xB (.not xA))] (.ex (.and xB (.not xA))) ∧
    ¬ Contradicts S22 [] (needed xA xB) ∧ ¬ Entails S22 [] (.ex (.and xB (.not xA))) := by …
```

</details>

**Prior art.**

- Standard quantifier duality; no specific source is relied on.

**Design question.** Reference point: is calling a sufficient condition "needed" merely an implicature hazard? (No: whenever the report proves a counterexample ∃x, Y ∧ ¬X, the rendering "X is needed for Y" is literally contradicted.)

Basis: execution (Lean kernel check): `necessity_rendering_contradicted_iff_counterexample`, `necessity_rendering_nonvacuous`.

Basis: derived (modeling bridge): Calling a condition "needed" in a real summary is a literal falsehood, not merely an implicature hazard, whenever the report proves a counterexample. Reasoning: the characterization is general. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 17**.

#### Card 18. `tight-sufficient-hypothesis-not-needed-instances`

- **Kind:** counterexample. **Tier:** T1: Elementary instances chosen to illustrate the gap between tightness and necessity that von Fintel (2001 ms., pp. 5-8) points out for conditionals. **Depth:** shallow.
- **Plain claim.** (i) In a single interpreted world over the parameter values 0..7, with atom 0 read as "divisible by 4" and atom 1 as "even" (a single world, so the empty report already decides every claim): "divisible by 4 gives even" holds, "divisible by 4 is needed for evenness" is false, the hypothesis is tight for "under divisibility by 4, even" (1 is neither), and the exhaustified reading of that claim under the standard alternatives holds. (ii) In the 16-world space S22, the consistent report E_tight (∀x, A⇒B; ∃x, B∧¬A; ∃x, ¬A∧¬B) proves ∀x, A⇒B, proves that A is tight for it (which the empty report does not), and entails its exhaustified reading, yet contradicts "A is needed for B". In both instances the hypothesis is sufficient and tight, and "needed" is false.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:537-541
theorem natural_instance_tight_sufficient_condition_not_needed :
    Entails natSpace [] (.all (.imp div4 even)) ∧ Contradicts natSpace [] (needed div4 even) ∧
    Entails natSpace [] (tightFor div4 even) ∧
    Entails natSpace []
      (exh natSpace (stdAlt natSpace (.all (.rel div4 even))) (.all (.rel div4 even))) := by …
```

```lean
-- lean/Implicature/Results.lean:551-555
theorem tight_hypothesis_not_needed :
    Sat S22 E_tight ∧ ¬ Entails S22 [] (tightFor xA xB) ∧
    Entails S22 E_tight (.all (.rel xA xB)) ∧ Entails S22 E_tight (tightFor xA xB) ∧
    Entails S22 E_tight (exh S22 (stdAlt S22 (.all (.rel xA xB))) (.all (.rel xA xB))) ∧
    Contradicts S22 E_tight (needed xA xB) := by …
```

Fixtures used: `natSpace`, `div4`, `even`, `E_tight` (quoted under **Model definitions → Fixtures**).

**Hypothesis ledger.**

No hypotheses: the theorems on this card are closed statements about concrete instances, proved by kernel evaluation.

**Non-vacuity witness.** The instances themselves. Lean: `natural_instance_tight_sufficient_condition_not_needed`, `tight_hypothesis_not_needed`.

**Further theorems cited in this card's non-claims:** `interp_never_open`, `interp_literallySafe_strengtheningSafe_unblocked`, `tightFor_does_not_check_theorem` (quoted under **Cited supporting theorems**).

**Prior art.**

- K. von Fintel, "Conditional strengthening: A case study in implicature", unpublished manuscript, MIT, draft version of 13 September 2001, https://web.mit.edu/fintel/fintel-2001-condstrength.pdf (no DOI). Section "Not True No Matter What" (pp. 5-8): the quantity implicature of "if p, q" against the competitor "q no matter what" is that q is not unconditionally true; p. 8 stresses that this is much weaker than the claim that the antecedent is a necessary condition. This is the gap between tightness (an existential counterexample) and necessity modeled here.
- M. L. Geis and A. M. Zwicky, "On invited inferences", Linguistic Inquiry 2(4):561-566, 1971. Names the invited inference of conditional perfection ("If you mow the lawn, I'll give you five dollars" invites "if not, not").
- L. R. Horn, "From if to iff: Conditional perfection as pragmatic strengthening", Journal of Pragmatics 32(3):289-326, 2000, doi:10.1016/S0378-2166(99)00053-3. Analyzes conditional perfection as pragmatic strengthening.

**Design question.** May a report write "H is needed" for a hypothesis it has shown to be tight? (Not in general: in both instances the hypothesis is tight yet "needed" is false; tightness is existential, necessity is universal.)

Basis: execution (Lean kernel check): `natural_instance_tight_sufficient_condition_not_needed`, `tight_hypothesis_not_needed`.

Basis: derived (modeling bridge): A real report should not write "H is needed" on the strength of a tightness counterexample for H. Reasoning: the instances show tightness without necessity; the necessity reading of "needed" is the modeled assumption. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 18**.

#### Card 19. `disclaimer-read-as-refutation`

- **Kind:** characterization. **Tier:** T1: Folklore about reading "not shown" as "false", made precise. **Depth:** definitional.
- **Plain claim.** For every finite space S, report E and claim c: (a) if the disclaimer "c is not shown" is true (E ⊭ c), then the reader rule "not shown ↦ false" makes it unsafe iff E leaves c open (neither proves nor refutes c); (b) the blocked disclaimer "c is not shown, and not refuted" is safe iff E leaves c open.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:562-564
theorem not_shown_read_as_false_unsafe_iff_open (S : Space) (E : List Claim) (c : Claim)
    (htrue : DisclaimerTrue S E (.notShown c)) :
    ¬ DisclaimerSafe S E (.notShown c) ↔ Open S E c := by …
```

Unfolded rendering of `not_shown_read_as_false_unsafe_iff_open` (Lean; definitionally equal to the statement after its binders):

```lean
¬ Entails S E c →
  (¬ (¬ Entails S E c ∧ ∀ ρ ∈ [Claim.not c], Entails S E ρ) ↔
    (¬ Entails S E c ∧ ¬ Entails S E (Claim.not c)))
```

```lean
-- lean/Implicature/Results.lean:571-572
theorem not_shown_not_refuted_safe_iff_open (S : Space) (E : List Claim) (c : Claim) :
    DisclaimerSafe S E (.notShownNotRefuted c) ↔ Open S E c := by …
```

Unfolded rendering of `not_shown_not_refuted_safe_iff_open` (Lean; definitionally equal to the statement after its binders):

```lean
((¬ Entails S E c ∧ ¬ Entails S E (Claim.not c)) ∧ ∀ ρ ∈ ([] : List Claim), Entails S E ρ) ↔
  (¬ Entails S E c ∧ ¬ Entails S E (Claim.not c))
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `htrue : DisclaimerTrue S E (.notShown c)` | statement (a): DisclaimerSafe requires the disclaimer to be true (definition), so a false disclaimer is unsafe even when c is not open | tight | `not_shown_tight_htrue` | the 4-world space S21 with report [p0], which proves c = p0 and makes the disclaimer false | `not_shown_read_as_false_unsafe_iff_open` |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:577-578
theorem not_shown_tight_htrue :
    ¬ (¬ DisclaimerSafe S21 [p0] (.notShown p0) ↔ Open S21 [p0] p0) := by …
```

</details>

**Non-vacuity witness.** S21, E = [], c = p0: the bare disclaimer is true and unsafe, c is open, the blocked disclaimer is safe. Lean: `disclaimer_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:583-585
theorem disclaimer_nonvacuous :
    DisclaimerTrue S21 [] (.notShown p0) ∧ Open S21 [] p0 ∧
    ¬ DisclaimerSafe S21 [] (.notShown p0) ∧ DisclaimerSafe S21 [] (.notShownNotRefuted p0) := by …
```

</details>

**Positive control** (a nearby setting where the conclusion fails): `not_shown_read_as_false_safe_when_refuted`.

```lean
-- lean/Implicature/Results.lean:589-590
theorem not_shown_read_as_false_safe_when_refuted :
    DisclaimerTrue S21 [.not p0] (.notShown p0) ∧ DisclaimerSafe S21 [.not p0] (.notShown p0) := by …
```

**Prior art.**

- H. P. Grice, "Logic and conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics 3: Speech Acts, Academic Press, 1975, pp. 41-58 (Brill reissue doi:10.1163/9789004368811_003). Introduces conversational implicature; the disclaimer model here has no cancellation filter and fixes its readings by definition.

**Design question.** How should a report state that something is not established without being read as refuting it? (Under this model, "not shown, and not refuted" is safe exactly when the matter is open; this requires checking that the report neither proves nor refutes it, not merely that it was not examined.)

Basis: execution (Lean kernel check): `not_shown_read_as_false_unsafe_iff_open`, `not_shown_not_refuted_safe_iff_open`, `not_shown_tight_htrue`, `disclaimer_nonvacuous`, `not_shown_read_as_false_safe_when_refuted`.

Basis: derived (modeling bridge): A real non-claim written "X is not shown" risks being read as "X is false" when X is open; "not shown, and not refuted" is safe for the modeled reader exactly when X is open, which must be checked rather than assumed. Reasoning: the characterization is general; the disclaimer reader is fixed by definition. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 19**.

#### Card 20. `nondegenerate-universal-conditional-unsafe-without-blockers`

- **Kind:** impossibility. **Tier:** T1: The clash between perfection (if ↦ iff) and a scalar reading of if against the stronger iff (if ↦ merely sufficient) is noted in the conditional-perfection literature (von Fintel 2001 ms., pp. 13-14); the impossibility for a consistent report and the blocker characterization are precise formulations of it. **Depth:** shallow.
- **Plain claim.** For the one-step reader `readings` with the standard alternatives `stdAlt`, every finite space S, report E and claims a, b: (a) if E is consistent, ∀x, a→b is consistent with its perfected reading ∀x, a↔b (PerfectionConsistent S a b), and ∀x, a→b is consistent with ¬∀x, b→a (ConverseExcludable S a b), then the rendering ∀x, a→b is not strengthening-safe for E without blocker flags; (b) if in addition E ⊨ ∀x, a→b, then its computed blocker set is {perfection} if E refutes ∀x, b→a, {exhaustification} if E proves ∀x, b→a, and {perfection, exhaustification} if E does neither; (c) if PerfectionConsistent S a b and E leaves ∀x, b→a open, then its computed blocker set is {perfection, exhaustification}.

**Statement** (Lean source, verbatim):

```lean
-- lean/Implicature/Results.lean:600-603
theorem forall_conditional_unblocked_unsafe_of_perfection_consistent_of_converse_excludable
    (S : Space) (E : List Claim) (a b : Claim) (hE : Sat S E)
    (hperf : PerfectionConsistent S a b) (hconv : ConverseExcludable S a b) :
    ¬ StrengtheningSafe S (stdAlt S) [] E (.all (.imp a b)) := …
```

Unfolded rendering of `forall_conditional_unblocked_unsafe_of_perfection_consistent_of_converse_excludable` (Lean; definitionally equal to the statement after its binders):

```lean
Sat S E →
  Sat S [Claim.all (Claim.imp a b), Claim.all (Claim.iff a b)] →
  Sat S [Claim.all (Claim.imp a b), Claim.not (Claim.all (Claim.imp b a))] →
  ¬ ∀ ρ ∈ readings S (stdAlt S) [] (Claim.all (Claim.imp a b)), Entails S E ρ
```

```lean
-- lean/Implicature/Results.lean:610-616
theorem forall_conditional_blockers_by_converse_status (S : Space) (E : List Claim) (a b : Claim)
    (hE : Sat S E) (hlit : LiterallySafe S E (.all (.imp a b)))
    (hperf : PerfectionConsistent S a b) (hconv : ConverseExcludable S a b) :
    blockers S (stdAlt S) E (.all (.imp a b)) =
      if Entails S E (.not (.all (.imp b a))) then [.perfection]
      else if Entails S E (.all (.imp b a)) then [.exhaustification]
      else [.perfection, .exhaustification] := …
```

```lean
-- lean/Implicature/Results.lean:622-624
theorem forall_conditional_blockers_of_open_converse (S : Space) (E : List Claim) (a b : Claim)
    (hperf : PerfectionConsistent S a b) (hopen : Open S E (.all (.imp b a))) :
    blockers S (stdAlt S) E (.all (.imp a b)) = [.perfection, .exhaustification] := …
```

Unfolded rendering of `forall_conditional_blockers_of_open_converse` (Lean; definitionally equal to the statement after its binders):

```lean
Sat S [Claim.all (Claim.imp a b), Claim.all (Claim.iff a b)] →
  (¬ Entails S E (Claim.all (Claim.imp b a)) ∧ ¬ Entails S E (Claim.not (Claim.all (Claim.imp b a)))) →
  blockers S (stdAlt S) E (Claim.all (Claim.imp a b)) = [Rule.perfection, Rule.exhaustification]
```

Fixtures used: `disagreeSpace`, `E_notConv` (quoted under **Model definitions → Fixtures**).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold; the conclusion fails) | Witness class | Applies to |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `hE : Sat S E` | statements (a), (b): an inconsistent report entails every reading | tight | `forall_conditional_tight_hE`, `forall_conditional_blockers_tight_hE` | the 16-world space S22 with a = A, b = B and the inconsistent report [p0, ¬p0] | `forall_conditional_unblocked_unsafe_of_perfection_consistent_of_converse_excludable`, `forall_conditional_blockers_by_converse_status` |
| `hlit : LiterallySafe S E (∀x, a→b)` | statement (b): the exhaustified reading has the rendering as a conjunct (definition of exh), so a report that does not prove the rendering does not entail it, and the blocker set can differ from the one stated; instance in the counterexample | tight | `forall_conditional_blockers_tight_hlit` | the 16-world space S22 with a = A, b = B and the report [¬∀x, B→A] | `forall_conditional_blockers_by_converse_status` |
| `hperf : PerfectionConsistent S a b` | statements (a), (b), (c): without it the perfected reading ∀x, a↔b is inconsistent with the rendering and is cancelled (definition of ruleReadings) | tight | `forall_conditional_tight_hperf`, `forall_conditional_tight_hperf_full`, `forall_conditional_blockers_tight_hperf`, `forall_conditional_open_tight_hperf` | (a) the 2-world space disagreeSpace (atoms 0 and 1 always disagree; not a full valuation space) with report [∀x, A→B], and the full 4-world space S12 with b = ¬a and report [∀x, A→¬A]; (b) disagreeSpace with E_notConv; (c) disagreeSpace with the empty report | `forall_conditional_unblocked_unsafe_of_perfection_consistent_of_converse_excludable`, `forall_conditional_blockers_by_converse_status`, `forall_conditional_blockers_of_open_converse` |
| `hconv : ConverseExcludable S a b` | statements (a), (b): without it ∀x, a→b entails its converse over the listed worlds, so the converse is not available for exclusion; in the counterexample exhaustification adds nothing and the unflagged rendering is safe | tight | `forall_conditional_tight_hconv`, `forall_conditional_blockers_tight_hconv` | the 4-world space S12 with a = b = A and the empty report | `forall_conditional_unblocked_unsafe_of_perfection_consistent_of_converse_excludable`, `forall_conditional_blockers_by_converse_status` |
| `hopen : Open S E (∀x, b→a)` | statement (c): a report that refutes the converse can have a one-flag blocker set (in the counterexample it is {perfection}; compare statement (b)) | tight | `forall_conditional_open_tight_hopen` | the 16-world space S22 with a = A, b = B and E_notConv, which refutes the converse | `forall_conditional_blockers_of_open_converse` |

<details><summary>Counterexample statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:639-641
theorem forall_conditional_tight_hE :
    PerfectionConsistent S22 xA xB ∧ ConverseExcludable S22 xA xB ∧
    StrengtheningSafe S22 (stdAlt S22) [] [p0, .not p0] (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Results.lean:677-681
theorem forall_conditional_blockers_tight_hE :
    LiterallySafe S22 [p0, .not p0] (.all (.imp xA xB)) ∧ PerfectionConsistent S22 xA xB ∧
    ConverseExcludable S22 xA xB ∧
    Entails S22 [p0, .not p0] (.not (.all (.imp xB xA))) ∧
    blockers S22 (stdAlt S22) [p0, .not p0] (.all (.imp xA xB)) = [] := by …
```

```lean
-- lean/Implicature/Results.lean:687-692
theorem forall_conditional_blockers_tight_hlit :
    Sat S22 [.not (.all (.imp xB xA))] ∧ PerfectionConsistent S22 xA xB ∧
    ConverseExcludable S22 xA xB ∧
    Entails S22 [.not (.all (.imp xB xA))] (.not (.all (.imp xB xA))) ∧
    blockers S22 (stdAlt S22) [.not (.all (.imp xB xA))] (.all (.imp xA xB)) =
      [.perfection, .exhaustification] := by …
```

```lean
-- lean/Implicature/Results.lean:647-650
theorem forall_conditional_tight_hperf :
    Sat disagreeSpace [.all (.imp xA xB)] ∧ ConverseExcludable disagreeSpace xA xB ∧
    StrengtheningSafe disagreeSpace (stdAlt disagreeSpace) [] [.all (.imp xA xB)]
      (.all (.imp xA xB)) := by …
```

```lean
-- lean/Implicature/Results.lean:655-659
theorem forall_conditional_tight_hperf_full :
    Sat S12 [.all (.imp xA (.not xA))] ∧ ConverseExcludable S12 xA (.not xA) ∧
    ¬ PerfectionConsistent S12 xA (.not xA) ∧
    StrengtheningSafe S12 (stdAlt S12) [] [.all (.imp xA (.not xA))]
      (.all (.imp xA (.not xA))) := by …
```

```lean
-- lean/Implicature/Results.lean:697-701
theorem forall_conditional_blockers_tight_hperf :
    Sat disagreeSpace E_notConv ∧ LiterallySafe disagreeSpace E_notConv (.all (.imp xA xB)) ∧
    ConverseExcludable disagreeSpace xA xB ∧
    Entails disagreeSpace E_notConv (.not (.all (.imp xB xA))) ∧
    blockers disagreeSpace (stdAlt disagreeSpace) E_notConv (.all (.imp xA xB)) = [] := by …
```

```lean
-- lean/Implicature/Results.lean:731-734
theorem forall_conditional_open_tight_hperf :
    Open disagreeSpace [] (.all (.imp xB xA)) ∧
    blockers disagreeSpace (stdAlt disagreeSpace) [] (.all (.imp xA xB)) =
      [.exhaustification] := by …
```

```lean
-- lean/Implicature/Results.lean:664-666
theorem forall_conditional_tight_hconv :
    Sat S12 [] ∧ PerfectionConsistent S12 xA xA ∧
    StrengtheningSafe S12 (stdAlt S12) [] [] (.all (.imp xA xA)) := by …
```

```lean
-- lean/Implicature/Results.lean:706-709
theorem forall_conditional_blockers_tight_hconv :
    Sat S12 [] ∧ LiterallySafe S12 [] (.all (.imp xA xA)) ∧ PerfectionConsistent S12 xA xA ∧
    ¬ Entails S12 [] (.not (.all (.imp xA xA))) ∧ Entails S12 [] (.all (.imp xA xA)) ∧
    blockers S12 (stdAlt S12) [] (.all (.imp xA xA)) = [] := by …
```

```lean
-- lean/Implicature/Results.lean:739-741
theorem forall_conditional_open_tight_hopen :
    PerfectionConsistent S22 xA xB ∧
    blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] := by …
```

</details>

**Non-vacuity witness.** S22 with a = A, b = B: E_notConv satisfies the hypotheses of (a) and of (b) (refuted branch); [∀x, A↔B] and [∀x, A→B] satisfy those of (b) (proved and open branches); [∀x, A→B] satisfies those of (c). Lean: `forall_conditional_nonvacuous`, `forall_conditional_blockers_nonvacuous`, `forall_conditional_open_nonvacuous`.

<details><summary>Non-vacuity statements (verbatim)</summary>

```lean
-- lean/Implicature/Results.lean:670-671
theorem forall_conditional_nonvacuous :
    Sat S22 E_notConv ∧ PerfectionConsistent S22 xA xB ∧ ConverseExcludable S22 xA xB := by …
```

```lean
-- lean/Implicature/Results.lean:715-726
theorem forall_conditional_blockers_nonvacuous :
    PerfectionConsistent S22 xA xB ∧ ConverseExcludable S22 xA xB ∧
    Sat S22 E_notConv ∧ LiterallySafe S22 E_notConv (.all (.imp xA xB)) ∧
    Entails S22 E_notConv (.not (.all (.imp xB xA))) ∧
    blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] ∧
    Sat S22 [.all (.iff xA xB)] ∧ LiterallySafe S22 [.all (.iff xA xB)] (.all (.imp xA xB)) ∧
    Entails S22 [.all (.iff xA xB)] (.all (.imp xB xA)) ∧
    blockers S22 (stdAlt S22) [.all (.iff xA xB)] (.all (.imp xA xB)) = [.exhaustification] ∧
    Sat S22 [.all (.imp xA xB)] ∧ LiterallySafe S22 [.all (.imp xA xB)] (.all (.imp xA xB)) ∧
    Open S22 [.all (.imp xA xB)] (.all (.imp xB xA)) ∧
    blockers S22 (stdAlt S22) [.all (.imp xA xB)] (.all (.imp xA xB)) =
      [.perfection, .exhaustification] := by …
```

```lean
-- lean/Implicature/Results.lean:746-747
theorem forall_conditional_open_nonvacuous :
    PerfectionConsistent S22 xA xB ∧ Open S22 [.all (.imp xA xB)] (.all (.imp xB xA)) := by …
```

</details>

**Positive control** (a nearby setting where the conclusion fails): `forall_conditional_safe_with_blockers`.

```lean
-- lean/Implicature/Results.lean:753-761
theorem forall_conditional_safe_with_blockers :
    StrengtheningSafe S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) ∧
    StrengtheningSafe S22 (stdAlt S22) [.exhaustification] [.all (.iff xA xB)]
      (.all (.imp xA xB)) ∧
    StrengtheningSafe S22 (stdAlt S22) [.perfection, .exhaustification] [.all (.imp xA xB)]
      (.all (.imp xA xB)) ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [.perfection] [.all (.imp xA xB)] (.all (.imp xA xB)) ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [.exhaustification] [.all (.imp xA xB)]
      (.all (.imp xA xB)) := by …
```

**Further theorems cited in this card's non-claims:** `open_converse_rewordings_not_literally_safe`, `forall_conditional_open_converse_safe_iff_both_flags`, `distinct_atoms_nondegenerate_in_full_spaces`, `single_value_conditional_needs_exhaustification_flag` (quoted under **Cited supporting theorems**).

**Prior art.**

- M. L. Geis and A. M. Zwicky, "On invited inferences", Linguistic Inquiry 2(4):561-566, 1971. Names the invited inference of conditional perfection ("If you mow the lawn, I'll give you five dollars" invites "if not, not").
- J. van der Auwera, "Pragmatics in the last quarter century: The case of conditional perfection", Journal of Pragmatics 27(3):261-274, 1997, doi:10.1016/S0378-2166(96)00058-6. Survey of accounts of conditional perfection.
- L. R. Horn, "From if to iff: Conditional perfection as pragmatic strengthening", Journal of Pragmatics 32(3):289-326, 2000, doi:10.1016/S0378-2166(99)00053-3. Analyzes conditional perfection as pragmatic strengthening.
- K. von Fintel, "Conditional strengthening: A case study in implicature", unpublished manuscript, MIT, draft version of 13 September 2001, https://web.mit.edu/fintel/fintel-2001-condstrength.pdf (no DOI). Treats "if p, q" as restricted universal quantification over relevant situations, with perfection conveying "all and only"; on pp. 13-14 it notes that treating "if and only if p, q" as a stronger scalar alternative of "if p, q" would yield the quantity implicature that p is merely sufficient, against the perfected interpretation (a scale excluded as ill-formed by J. D. Atlas and S. C. Levinson, "It-clefts, informativeness and logical form: Radical pragmatics (revised standard version)", in P. Cole (ed.), Radical Pragmatics, Academic Press, 1981, pp. 1-61 (one library record gives pp. 1-62)), and that exhaustivity accounts instead compare "if p, q" with "if p or r, q".

**Design question.** Can a bare "A gives B" headline be safe against both default readers? (Under this reader model, not without flags when the report is consistent and both PerfectionConsistent and ConverseExcludable hold; which flags suffice depends on whether the report refutes, proves, or leaves open the converse; for a report that proves ∀x, a→b and leaves the converse open, with PerfectionConsistent S a b, a flag set is safe iff it contains both the perfection and the exhaustification flags.)

Basis: execution (Lean kernel check): `forall_conditional_unblocked_unsafe_of_perfection_consistent_of_converse_excludable`, `forall_conditional_blockers_by_converse_status`, `forall_conditional_blockers_of_open_converse`, `forall_conditional_tight_hE`, `forall_conditional_blockers_tight_hE`, `forall_conditional_blockers_tight_hlit`, `forall_conditional_tight_hperf`, `forall_conditional_tight_hperf_full`, `forall_conditional_blockers_tight_hperf`, `forall_conditional_open_tight_hperf`, `forall_conditional_tight_hconv`, `forall_conditional_blockers_tight_hconv`, `forall_conditional_open_tight_hopen`, `forall_conditional_nonvacuous`, `forall_conditional_blockers_nonvacuous`, `forall_conditional_open_nonvacuous`, `forall_conditional_safe_with_blockers`.

Basis: derived (modeling bridge): A bare "A gives B" headline for a consistent report, with A and B non-degenerate in the sense of the two hypotheses, is unsafe against a reader who both perfects and exhaustifies against the converse; which non-claims restore safety depends on what the report says about the converse. Reasoning: the theorem is general over spaces and claims for the standard alternatives. This bridge is not kernel-checked.

**Non-claims:** see **Boundaries → Non-claims → Card 20**.

### Cited supporting theorems

Theorems cited by name in non-claims or design questions, beyond each card's main theorems, witnesses and counterexamples. All are proved; their hashes are under **Evidence**.

```lean
-- lean/Implicature/Results.lean:30-32
theorem perfection_countermodel_exhaustified_reading_entailed :
    Entails S22 E_notConv
      (exh S22 (stdAlt S22 (.all (.imp xA xB))) (.all (.imp xA xB))) := by …
```

```lean
-- lean/Implicature/Examples.lean:284-284
theorem blockers_pos : blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] := by …
```

```lean
-- lean/Implicature/Examples.lean:112-113
theorem stdAlt_pos_conditional :
    stdAlt S22 (.all (.imp xA xB)) = [.all (.imp xB xA), .all (.iff xA xB)] := by …
```

```lean
-- lean/Implicature/Examples.lean:119-119
theorem stdAlt_pos_relativized : stdAlt S32 (.all (.rel xH xA)) = [.all xA] := by …
```

```lean
-- lean/Implicature/Examples.lean:122-123
theorem stdAlt_pos_neighbouring_values :
    stdAlt (Space.full 1 3) (.atom 0 (.lit 1)) = [.atom 0 (.lit 0), .atom 0 (.lit 2)] := by …
```

```lean
-- lean/Implicature/Examples.lean:154-158
theorem stdAlt_value_alternatives_any_connective :
    stdAlt S12 (.not p0) = [.not (.atom 0 (.lit 1))] ∧
    stdAlt S22 pOrQ = [.or (.atom 0 (.lit 1)) (.atom 1 (.lit 1))] ∧
    stdAlt S22 (.iff p0 q0) = [.iff (.atom 0 (.lit 1)) (.atom 1 (.lit 1))] ∧
    stdAlt S21 pOrQ = [] := by …
```

```lean
-- lean/Implicature/Results.lean:773-776
theorem open_converse_rewordings_not_literally_safe (S : Space) (E : List Claim) (a b : Claim)
    (hopen : Open S E (.all (.imp b a))) :
    ¬ LiterallySafe S E (.all (.iff a b)) ∧
    ¬ LiterallySafe S E (.and (.all (.imp a b)) (.not (.all (.imp b a)))) := by …
```

```lean
-- lean/Implicature/Results.lean:630-634
theorem forall_conditional_open_converse_safe_iff_both_flags (S : Space) (E : List Claim)
    (a b : Claim) (F : List Rule) (hlit : LiterallySafe S E (.all (.imp a b)))
    (hperf : PerfectionConsistent S a b) (hopen : Open S E (.all (.imp b a))) :
    StrengtheningSafe S (stdAlt S) F E (.all (.imp a b)) ↔
      Rule.perfection ∈ F ∧ Rule.exhaustification ∈ F := …
```

```lean
-- lean/Implicature/Results.lean:156-158
theorem ieList_characterization_unsat_prejacent (S : Space) (σ : Claim) (A : List Claim)
    (hσ : ¬ Sat S [σ]) :
    ieList S σ A = A ∧ ∀ a ∈ A, InnocentlyExcludable S σ A a := …
```

```lean
-- lean/Implicature/Results.lean:148-151
theorem exh_weaker_than_maximal_falsified_worlds :
    (∀ w ∈ S21.worlds, maxFals S21 pOrQ [p0, q0] w = true → S21.holds w (.and p0 q0) = false) ∧
    (∃ w ∈ S21.worlds, S21.holds w (exh S21 [p0, q0] pOrQ) = true ∧
      S21.holds w (.and p0 q0) = true) := by …
```

```lean
-- lean/Implicature/Results.lean:173-174
theorem innocent_exh_not_entails_naive_exh :
    ¬ Entails S21 [exh S21 disjAlts pOrQ] (naiveExh S21 disjAlts pOrQ) := by …
```

```lean
-- lean/Implicature/Results.lean:291-293
theorem composing_reader_some_safe_flag_set_iff_literally_safe (S : Space)
    (alt : Claim → List Claim) (E : List Claim) (σ : Claim) :
    (∃ F, StrengtheningSafeStar S alt F E σ) ↔ LiterallySafe S E σ := …
```

```lean
-- lean/Implicature/Results.lean:799-804
theorem entry_blockers_strictly_larger_than_report_blockers :
    (∀ q ∈ R_comp, LiterallySafe S32 E_comp (nfOf q)) ∧
    ConclusionDropping R_comp [(xH, [xA])] ∧
    blockers S32 (stdAlt S32) (R_comp.map nfOf) (renderComp [(xH, [xA])]) =
      [.qualifierDrop, .exhaustification] ∧
    blockers S32 (stdAlt S32) E_comp (renderComp [(xH, [xA])]) = [.exhaustification] := by …
```

```lean
-- lean/Implicature/Results.lean:392-396
theorem duplicated_conclusion_keeps_perfection_hazard :
    ConclusionDropping [(.top, [.imp xA xB])] [(.top, [.imp xA xB, .imp xA xB])] ∧
    blockers S22 (stdAlt S22) E_notConv (renderComp [(.top, [.imp xA xB])]) = [.perfection] ∧
    blockers S22 (stdAlt S22) E_notConv (renderComp [(.top, [.imp xA xB, .imp xA xB])]) =
      [.perfection] := by …
```

```lean
-- lean/Implicature/Lemmas.lean:541-542
theorem interp_never_open (ps : List Nat) (val : Nat → Nat → Bool) (E : List Claim) (c : Claim) :
    ¬ Open (Space.interp ps val) E c := by …
```

```lean
-- lean/Implicature/Lemmas.lean:556-559
theorem interp_literallySafe_strengtheningSafe_unblocked (ps : List Nat)
    (val : Nat → Nat → Bool) (alt : Claim → List Claim) (E : List Claim) (σ : Claim)
    (hlit : LiterallySafe (Space.interp ps val) E σ) :
    StrengtheningSafe (Space.interp ps val) alt [] E σ := by …
```

```lean
-- lean/Implicature/Examples.lean:364-366
theorem tightFor_does_not_check_theorem :
    Contradicts natSpace [] (.all (.rel div4 (.not even))) ∧
    Entails natSpace [] (tightFor div4 (.not even)) := by …
```

```lean
-- lean/Implicature/Results.lean:766-768
theorem distinct_atoms_nondegenerate_in_full_spaces :
    PerfectionConsistent S22 xA xB ∧ ConverseExcludable S22 xA xB ∧
    PerfectionConsistent S32 xA xB ∧ ConverseExcludable S32 xA xB := by …
```

```lean
-- lean/Implicature/Results.lean:786-792
theorem single_value_conditional_needs_exhaustification_flag :
    Sat S22 [.imp p0 q0, .not (.imp q0 p0)] ∧
    LiterallySafe S22 [.imp p0 q0, .not (.imp q0 p0)] (.imp p0 q0) ∧
    blockers S22 (stdAlt S22) [.imp p0 q0, .not (.imp q0 p0)] (.imp p0 q0) =
      [.perfection, .exhaustification] ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [.perfection] [.imp p0 q0, .not (.imp q0 p0)]
      (.imp p0 q0) := by …
```

`interp_never_open` and `interp_literallySafe_strengtheningSafe_unblocked` (in `Lemmas.lean`) are the single-world collapse lemmas for `Space.interp`.

## Boundaries

### Non-claims

Each item records something a result does not show. Unless a theorem is cited for its failure, it is not shown, and not refuted. Shared non-claims are listed once and referenced by label.

#### Shared non-claims

- **N1.** These are statements about a toy model: finitely many listed worlds, uninterpreted atoms over a finite parameter list, a single bound variable (inner quantifiers shadow outer ones), material implication for both `→` and `⇒`, and three stated reader rules applied deterministically. They neither establish nor refute the corresponding claims about how actual readers interpret actual summary sentences; any such connection is a separate `derived (modeling bridge)` claim, resting on experimental work such as Noveck (2001; Cognition 78(2):165-188, doi:10.1016/S0010-0277(00)00114-1) and Bott and Noveck (2004; Journal of Memory and Language 51(3):437-457, doi:10.1016/j.jml.2004.05.006), which find that adults often, though not always, read "some" as "some but not all" and that this reading takes extra processing time.
- **N2.** Exhaustified readings depend on the alternative set. Unless a card says otherwise the alternatives are `stdAlt`: converse and biconditional of a conditional, universal of an existential, hypothesis-free version of a relativized claim, and neighbouring parameter values of a quantifier-free claim that mentions exactly one parameter value (whatever its connectives, including negation, disjunction and biconditional; `stdAlt_value_alternatives_any_connective`), substituted at one top-level conjunct. These are stipulated rules, not structurally defined alternatives in the sense of R. Katzir, "Structurally-defined alternatives", Linguistics and Philosophy 30(6):669-690, 2007, doi:10.1007/s10988-008-9029-y. Other alternative sets (for example alternative antecedents, as in exhaustification accounts of perfection) may give different readings (not proved here); nothing is claimed for them, either way.
- **N3.** Cancellation keeps a strengthened reading exactly when it is consistent with the literal rendering over the listed worlds (the filter in `ruleReadings`); the reader model has no context, no background knowledge and no probabilities.
- **N4.** Reference point (baseline): this result is elementary and is included so that other cards can cite it.
- **N5.** The one-step reader applies each unblocked rule once at one site. This card makes no claim, either way, about readers that compose rules; the composing reader `readingsStar` is treated in composing-reader-minimal-blockers-not-unique (`composing_reader_minimal_blocker_sets_not_unique`).
- **N6.** Computing `blockers` decides entailment and satisfiability by scanning the listed worlds: polynomial in the number of listed worlds and alternatives, but exponential in the numbers of atoms and parameter values when the worlds enumerate all valuations (as in `Space.full`).
- **N7.** Normal-form claims are rendered one conclusion per top-level conjunct (`nf H [C₁, …, Cₙ] = (∀x, H ⇒ C₁) ∧ … ∧ (∀x, H ⇒ Cₙ)`, and `⊤` when no conclusion remains); a conjunction written under `∀` or `⇒` would be a single site, to which perfection and the structural alternatives do not apply. No rule perfects a stated hypothesis into a necessary condition (no reading `∀x, C → H` or `∀x, H ↔ C` is generated from `∀x, H ⇒ C`); the qualifier-drop flag's intended phrasing is "established under H; not shown without H"; it does not say that C fails without H.

#### Card 1. `literal-safety-does-not-imply-strengthening-safety`

- Does not say that every literally safe rendering is strengthening-unsafe, and that stronger reading is false in this model: with the computed blocker set flagged every literally safe rendering is strengthening-safe (`blockers_sound`), and some literally safe renderings are strengthening-safe with no flags at all (the full rendering in `blocker_conjunct_drop_breaks_strengthening_safety`).
- In case (i) the contradicted reading is the perfected one: the exhaustified reading of the same rendering is entailed by that report (`perfection_countermodel_exhaustified_reading_entailed`), and the computed blocker set is `[perfection]` (`blockers_pos`).
- Exhaustification is not limited to existentials: the standard alternatives also include the converse and biconditional of a conditional (`stdAlt_pos_conditional`), the hypothesis-free version of a relativized claim (`stdAlt_pos_relativized`) and neighbouring values of a single-value claim (`stdAlt_pos_neighbouring_values`); whether an alternative is negated depends on whether it is innocently excludable.
- Shared: N1, N2, N3.

#### Card 2. `literal-safety-closed-under-literal-weakening`

- Says nothing about strengthening safety, which is not closed under literal weakening (`blocker_conjunct_drop_breaks_strengthening_safety`).
- Shared: N4, N1.

#### Card 3. `dropping-a-blocking-conjunct-breaks-strengthening-safety`

- Relies on the cancellation filter (the generated and cancelled perfected reading is part of the theorem). Under a reader that perfects a conjunct without checking consistency, σ itself would be unsafe; under a reader that never looks inside conjunctions, every added conjunct would block perfection. Neither reader is formalized (not proved here).
- An object-level cancelling conjunct such as ¬(∀x, B→A) is literally safe when the report refutes the converse. When the report leaves the converse open, neither "and not conversely" nor "iff" is literally safe (`open_converse_rewordings_not_literally_safe`), and, for a report proving ∀x, A→B in a space where ∀x, A→B is consistent with ∀x, A↔B (PerfectionConsistent), a flag set is safe iff it contains both the perfection and the exhaustification flags (`forall_conditional_open_converse_safe_iff_both_flags`).
- One instance; does not characterize which conjuncts act as blockers.
- Shared: N1, N2, N3, N5.

#### Card 4. `naive-exhaustification-of-disjunction-inconsistent`

- The alternatives are supplied explicitly. The standard alternatives contain neither the disjuncts nor the conjunction of a disjunction: in S21, `stdAlt` of p ∨ q is empty, and in S22, which has the neighbouring parameter value 1, it is the one-element list [P0(1) ∨ P1(1)] (`stdAlt_value_alternatives_any_connective`).
- In this instance the exclusive reading depends on p ∧ q being among the alternatives: with the alternatives p, q innocent exclusion negates nothing (`disjunction_without_conjunctive_alternative`).
- Shared: N1.

#### Card 5. `innocent-exclusion-consistent`

- Concerns consistency with σ; says nothing about consistency with a report E, and exhaustified readings can be contradicted by a consistent report (`exhaustification_reading_contradicted_though_literally_safe`).
- The theorem holds for every finite alternative list, but the exhaustified reading itself depends on the list.
- Shared: N1.

#### Card 6. `innocent-exclusion-computed-by-maximal-falsified-sets`

- Gives a decision procedure polynomial in the number of listed worlds and alternatives; says nothing about spaces given symbolically, where the number of worlds is exponential.
- When σ is unsatisfiable both sides hold for every a ∈ A (`ieList_characterization_unsat_prejacent`).
- `exh S A σ` is in general weaker than restricting σ to the worlds with inclusion-maximal falsified sets (minimal-worlds exhaustification): for p ∨ q with alternatives p, q, every such world falsifies p ∧ q, yet `exh` holds at a world where p ∧ q holds (`exh_weaker_than_maximal_falsified_worlds`). The two coincide when the alternatives are closed under conjunction (Spector 2016, Theorem 9; not proved here).
- Shared: N1.

#### Card 7. `naive-exhaustification-entails-innocent`

- The converse fails (`innocent_exh_not_entails_naive_exh`: the disjunction in S21).
- When the naive reading is unsatisfiable the entailment holds vacuously.
- Shared: N1.

#### Card 8. `innocent-equals-naive-iff-naive-consistent`

- Equivalence means mutual entailment over the listed worlds of S; nothing is claimed about other spaces.
- Shallow given innocent-exclusion-consistent and naive-exhaustification-entails-innocent.
- Shared: N1.

#### Card 9. `exhaustification-not-monotone-antitone-or-reflecting`

- Shows failure for one alternative function in one space; says nothing about restricted classes of renderings on which exh might be monotone.
- Shared: N1, N2.

#### Card 10. `computed-blockers-sound`

- Concerns the one-step reader; for the composing reader the one-step blocker set can be insufficient (`composing_reader_minimal_blocker_sets_not_unique`).
- Blocking a rule removes all its readings, including safe ones at other sites.
- Blocker flags `F : List Rule` are out-of-band rule-disabling annotations with no truth conditions; unlike an object-language clause such as `¬(∀x, B→A)`, flagging `perfection` does not require the report to refute `∀x, B→A`. Flagging one rule leaves the others active.
- Shared: N6, N1, N3.

#### Card 11. `computed-blockers-minimal`

- Uniqueness of the least safe flag set holds for the one-step reader; it fails for the composing reader (`composing_reader_minimal_blocker_sets_not_unique`).
- "Least safe flag set" means least with respect to rule membership (∀ r ∈ blockers S alt E σ, r ∈ F); the order of F and duplicate flags in F do not matter.
- Least among flag sets of the three fixed rules; finer-grained blockers (per site, per alternative) are not modeled.
- Blocker flags `F : List Rule` are out-of-band rule-disabling annotations with no truth conditions; unlike an object-language clause such as `¬(∀x, B→A)`, flagging `perfection` does not require the report to refute `∀x, B→A`. Flagging one rule leaves the others active.
- Shared: N6, N1.

#### Card 12. `composing-reader-minimal-blockers-not-unique`

- The composing reader applies rules in the fixed order qualifier dropping, perfection, exhaustification; other orders are not examined.
- `readingsStar` applies each unblocked rule at most once and at a single top-level conjunct, and checks consistency with σ for the final composed reading, not after each step; readers that apply a rule at several conjuncts at once or cancel after each step are not modeled.
- For the composing reader some flag set is safe iff the rendering is literally safe (`composing_reader_some_safe_flag_set_iff_literally_safe`); for a literally safe rendering a minimal safe flag set therefore exists among the eight flag sets (by finiteness; not stated as a theorem here).
- Shared: N1, N2, N3.

#### Card 13. `conclusion-dropping-preserves-literal-safety`

- Concerns literal safety; strengthening safety need not be preserved (`inherited_blockers_insufficient_after_conclusion_drop`).
- Shared: N4, N7, N1.

#### Card 14. `compression-with-recomputed-blockers-safe`

- The blockers must be recomputed for the compressed rendering; flags computed for the uncompressed claim can be insufficient or can include unneeded flags (`inherited_blockers_insufficient_after_conclusion_drop`, `inherited_blockers_superfluous_after_conclusion_drop`).
- Strengthening safety of the compressed rendering follows from its literal safety together with blocker soundness; `ConclusionDropping` does not bound or preserve the blocker set. Blockers computed from R alone are sound (statement (b)) but can be strictly larger than those computed from E (`entry_blockers_strictly_larger_than_report_blockers`: {qualifierDrop, exhaustification} versus {exhaustification}).
- Normal form here means one hypothesis and one quantifier domain per claim; hypotheses that are themselves lists, or several quantifier domains, are not modeled. Duplicating a conclusion is allowed and does not hide a hazard (`duplicated_conclusion_keeps_perfection_hazard`).
- Shared: N7, N6, N1, N5.

#### Card 15. `inherited-blockers-can-be-insufficient-or-superfluous-after-compression`

- Two instances; does not bound how often recomputation changes the blocker set, and does not say inherited flags are never sufficient (in instance (ii) they are sufficient).
- The exhaustified reading of ∀x, H⇒A under `stdAlt` says that the hypothesis-free claim ∀x, A fails; it does not entail the necessity reading "H is needed for A", ∀x, A → H (`inherited_blockers_superfluous_after_conclusion_drop`).
- Shared: N7, N1, N2, N5.

#### Card 16. `hypothesis-dropping-literally-safe-iff-proved-where-hypothesis-fails`

- Concerns literal safety: a literally safe hypothesis-free normal-form rendering can still carry strengthening hazards (the compressed rendering nf ⊤ [A→B] in `inherited_blockers_insufficient_after_conclusion_drop` is literally safe and not strengthening-safe without flags); its blockers are computed as for any rendering (`blockers_sound`).
- Does not say a report proving ∀x, H⇒C never proves ∀x, C; it can (`hypothesis_dropping_nonvacuous`).
- Shared: N4, N7, N1.

#### Card 17. `necessity-rendering-contradicted-iff-counterexample-proved`

- The theorem has no hypothesis that E proves ∀x, X→Y.
- "Needed" is modeled as universal necessity; graded or causal senses of "needed" are not modeled.
- Shared: N4, N1.

#### Card 18. `tight-sufficient-hypothesis-not-needed-instances`

- Instance (i) uses a single-world space: entailment collapses to truth in that world (the empty report entails every true claim), no claim is open (`interp_never_open`), every literally safe rendering is strengthening-safe with no flags (`interp_literallySafe_strengtheningSafe_unblocked`), and exhaustification excludes ∀x, even because it is false in that world, not because it is open. Instance (ii) is the multi-world counterpart.
- `tightFor H C` (∃x, ¬H ∧ ¬C) models tightness of a single hypothesis H in ∀x, H ⇒ C; for ∀x, (H₁ ∧ H₂) ⇒ C, tightness of H₁ also requires H₂ at the witness, which is not modeled. `tightFor` does not check that the theorem itself holds (`tightFor_does_not_check_theorem`).
- Shared: N1.

#### Card 19. `disclaimer-read-as-refutation`

- When E refutes c the "false" reading is safe (`not_shown_read_as_false_safe_when_refuted`); the result does not say disclaimers are always misread.
- `Open S E c` is semantic independence of c from E over the listed worlds (a world satisfying E and ¬c, and one satisfying E and c); it does not license writing "not shown, and not refuted" when c was merely not examined and E might entail ¬c.
- `disclaimerReadings` fixes the readings by definition ("not shown" ↦ ¬c; the blocked form ↦ nothing); neither the "not shown ↦ false" inference nor its blocking is derived from exhaustification, the alternatives or the cancellation filter.
- Disclaimers are statements about E; their truth is not a property of worlds.
- Shared: N1.

#### Card 20. `nondegenerate-universal-conditional-unsafe-without-blockers`

- Escape hatches depend on what E proves about the converse (statement (b)): if E refutes ∀x, b→a, the perfection flag alone restores safety, and so does the rendering "(∀x, a→b) ∧ ¬(∀x, b→a)" in the instance of dropping-a-blocking-conjunct-breaks-strengthening-safety; if E proves ∀x, b→a, the exhaustification flag alone restores safety; if E leaves ∀x, b→a open, neither "iff" nor "and not conversely" is literally safe (`open_converse_rewordings_not_literally_safe`), and, for a report proving ∀x, a→b with PerfectionConsistent S a b, a flag set is safe iff it contains both the perfection and the exhaustification flags (`forall_conditional_open_converse_safe_iff_both_flags`; instances in `forall_conditional_safe_with_blockers`).
- The perfection flag alone does not express "the converse is open": with that flag alone, exhaustification still negates the converse whenever the converse is innocently excludable (`forall_conditional_safe_with_blockers`, open-converse instance).
- In the full valuation spaces S22 and S32 the distinct atoms A, B satisfy both PerfectionConsistent and ConverseExcludable (`distinct_atoms_nondegenerate_in_full_spaces`); the counterexamples for hperf and hconv use a restricted space, b = ¬a, or a = b.
- For a quantifier-free single-value conditional such as p0 → q0, neighbouring-value alternatives add further exhaustified content: even when the report refutes q0 → p0 in S22, the perfection flag alone is not enough (`single_value_conditional_needs_exhaustification_flag`).
- Depends on the standard alternatives (converse and biconditional of a conditional): with alternative antecedents instead, exhaustification may agree with perfection (not proved here); nothing is claimed for that reader, either way.
- Shared: N1, N3.

### Escape hatches

For the impossibility-style result (card 20), each hypothesis is tight, so dropping any one of them defeats statement (a): an inconsistent report entails every reading (`forall_conditional_tight_hE`); without `PerfectionConsistent` the perfected reading can be cancelled (`forall_conditional_tight_hperf`, `forall_conditional_tight_hperf_full`); without `ConverseExcludable` the conditional can entail its converse (`forall_conditional_tight_hconv`). Statement (a) is about the unflagged reader: flags restore safety (`forall_conditional_safe_with_blockers`), and the flags needed depend on what the report says about the converse (statement (b)). A rendering that adds an object-level clause is a different rendering: "(∀x, A→B) ∧ ¬(∀x, B→A)" is safe without flags for the report that is that rendering (`blocker_conjunct_drop_breaks_strengthening_safety`), but it is not literally safe when the report leaves the converse open (`open_converse_rewordings_not_literally_safe`). Results stated for the standard alternatives `stdAlt` make no claim, either way, about other alternative sets.

For card 19, a disclaimer "c is not shown" read as "c is false" is safe when the report refutes c (`not_shown_read_as_false_safe_when_refuted`).

### Tightness status

All 18 hypothesis-ledger entries are `tight` (18 of 18); none is `harmless` or `unknown`. Each tight entry names its counterexample theorems and the class of the witness.

### Disproved, dropped or unknown statements

None. Every card's statements are proved without `sorry`; no statement was found false, and no result was dropped or left `unknown`.

### Not examined

- Readers other than the one-step reader `readings` and the composing reader `readingsStar` (rule orders other than qualifier dropping, perfection, exhaustification; cancellation after each step; readers with context or probabilities).
- Alternative sets other than those named in each card (in particular structurally defined alternatives and alternative antecedents).
- Several bound variables, infinite parameter domains, symbolically given spaces, and the mapping from natural-language sentences to `Claim`s.
- Finer-grained blockers (per site or per alternative) and object-language blockers other than the "and not conversely" instance.

## Evidence

**Toolchain.** Lean 4 `leanprover/lean4:v4.34.1` (`lean/lean-toolchain`); the tag `v4.34.1` of `leanprover/lean4` is a lightweight tag pointing at commit `5045d0056413266e57c625dcd7c365b10e377c52` (GitHub API, observed 2026-11-21). No Mathlib; `lean/lakefile.toml` declares one `[[lean_lib]]` (`Implicature`) and no `[[require]]`.

**Kernel check.** Observed 2026-11-21: `lake build` of `lean/` succeeds with no `sorry`; the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe` or `debug.skipKernelTC`; and every one of the 530 declarations of the library depends on no axioms other than `propext`, `Classical.choice` and `Quot.sound` (Lean's `collectAxioms`). Countermodels, counterexamples, witnesses and positive controls are proved by `decide +kernel` (kernel evaluation, no `native_decide`); general theorems by term and tactic proofs from the lemmas in `Lemmas.lean`.

**Statement and closure hashes.** For every Lean name referenced by `results.json`, the statement hash is the SHA-256 of Lean's `repr` of the theorem's type, and the closure hash is the SHA-256 of the sorted lines `name : repr(type) := repr(value)` of every package-local constant reachable from the statement (theorem bodies excluded; closure size in parentheses). The values are recorded in `audit/statements.json`; per-declaration axioms in `audit/axioms.json`. Rows with the role "definition example" are the examples quoted under **Definition examples**, and rows with the role "model definitions" are `entailsB_iff` and `satB_iff`, quoted under **Claims and spaces**; each is listed under the card whose statement is about the exemplified definition, and none of them is a result, non-vacuity witness, counterexample or positive control of that card.

| Lean name | Card (role) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `perfection_reading_contradicted_though_literally_safe` | 1 (result); 1 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `f56101eba0e6e7f95d1fdd5dca2a7b67855bf7777369d1aeeedba2ab6007ecaf` | `cebd01960538b3ebc07c932e7fa3762323ba2d0145d9142ddf44bdae94443f6f` (95) |
| `exhaustification_reading_contradicted_though_literally_safe` | 1 (result); 1 (non-vacuity); 5 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `c9810a06ba5114fa6c85b1ec8ff95810d18f7fea93b90a1ae2a2f1e00158df12` | `15cffeec2df90630ecb499da19be4fbeeb3b199b30ea4437042a64d122541d83` (94) |
| `qualifier_drop_reading_contradicted_though_literally_safe` | 1 (result); 1 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `6f270ef3e6cbfa572f18c0c29deda0303c294c443208951644ca3368c17f5e90` | `2792ee9db5ce9f55e135de44b0e4289158e6d26fedb56de2bc50e59d0556cd7f` (95) |
| `blockers_sound` | 1 (cited); 10 (result); 16 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `5111eb03f8c38bd561d71a6042dea18b4f518c1ce4b6712a7d4c3f034ef19a63` | `da95c80ea4e1764f7445027e0f296526eb7b102fe7b7cacceabf736f106d6b9f` (74) |
| `blocker_conjunct_drop_breaks_strengthening_safety` | 1 (cited); 2 (cited); 3 (result); 3 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `77c8f042d3b5387738ed4d8d0ae18d1751f8a28157c4b8ea24fbac8205c64603` | `9ebfc86abb9e34f3da39ced57e52ccade58ad8b83ea24828cfb821129ddbf5c0` (93) |
| `perfection_countermodel_exhaustified_reading_entailed` | 1 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `164cd8ff30683884da8fcb07d69da424060ffd4c1782e5df322bc60829a17dd4` | `2a1ebb856e2c59682761e3ae04d7ce28e3b77cb965d9029fc65bd73055ed967c` (67) |
| `blockers_pos` | 1 (cited) | `propext` | `83c54c31e3af5d23fc10747032feabd3f518a5db05b38d5062868e49fdf4f769` | `911c953688b36dcb466775ee16a6c2af39cf19385320e99a5b430cf20d6baae2` (87) |
| `stdAlt_pos_conditional` | 1 (cited) | `propext` | `88e9ea9d717c2a63e33875453c7838abfb81055c1713168ebc42756086319237` | `ce10ca238745568375b8756abee62077a3924f2660c614d3219ceac1670196d7` (49) |
| `stdAlt_pos_relativized` | 1 (cited) | `propext` | `18f4b6a0c6a5540e90a4e61dd3ad357c8c020cdc1f332fc933772083c352420e` | `a944d7e4df634898ac757ff13c3c6f925e75b971e4cfa74f966b3942d1372ddc` (49) |
| `stdAlt_pos_neighbouring_values` | 1 (cited) | `propext` | `7a9892fe96674dfc44c1db80bb7199c948f8e1d34d6963cab9482be0ce1a7c94` | `f9a3144cd618b66c39a0f6ea83a3029f2e4582da45b7f12b8eb6ca7950ac9403` (46) |
| `stdAlt_value_alternatives_any_connective` | 1 (cited); 3 (cited); 4 (cited); 9 (cited); 12 (cited); 15 (cited) | `propext` | `1a2912af64e0ed977b074d44bc4ebdd110b26f8a40e088423d051df76670c7d9` | `c7db2554dc00cb7a83ed337e6fbf82eba1ea3c2ac06e9887387f2eda2e69995a` (52) |
| `stdAlt_pos_existential` | 1 (definition example) | `propext` | `9d2002470242481fc370609074618fe54990f5d23e9fe30cc67c390b2731747e` | `6eace23bc053c28eb952498af16e229cc8a85f6a427164b9bb80d23ae62610e7` (48) |
| `stdAlt_pos_sites` | 1 (definition example) | `propext` | `1c7288f955f55c640fc02ef212c49ca0ba22284226e9908f6bef0c71e29504bb` | `ce10ca238745568375b8756abee62077a3924f2660c614d3219ceac1670196d7` (49) |
| `stdAlt_neg_universal` | 1 (definition example) | `propext` | `8cd241c38f7e72d6798987956f306710338319a30ad87b67a8f6978c4af26528` | `6eace23bc053c28eb952498af16e229cc8a85f6a427164b9bb80d23ae62610e7` (48) |
| `stdAlt_neg_under_negation` | 1 (definition example) | `propext` | `2148b59dbfdd14a47ec369b3feadb3523d9465fff41a770c02155251cb51e68f` | `6eace23bc053c28eb952498af16e229cc8a85f6a427164b9bb80d23ae62610e7` (48) |
| `stdAlt_neg_value_outside_params` | 1 (definition example) | `propext` | `fa85dee30704b7b34487ecc42ecc243aeee08e828e473fdddc64cf22cdc93dfe` | `934857c5f035e323befb89a2382a276ea912c89da520f8d94b8bceb1fd2bc7cd` (47) |
| `negated_value_claim_exhaustified_reading_not_entailed` | 1 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `89695a283515f3e6984fe4c8492b140c8bf0119c41437cf44775ab1ee316d385` | `5c365c51fda9fd325b809273a06e39d72100c35f488f2750d0ec326b4cafdb2f` (91) |
| `step_perfection_pos` | 1 (definition example) | `propext` | `def3cb76164a800005a749c10532e4f011738f1a950508cc2e441ceb0e09bc8b` | `989bad04349c9a9615e893ede88835f894c1e803527878c1d6b0651ee89c6b2a` (81) |
| `step_perfection_neg` | 1 (definition example) | `propext` | `0e4d9dd6a792757939f871bb62522b051cc2cd8db295b15e2f6838f3d1be7c35` | `219f5d14706067c597c763c9b49f7ef4c9e152aba937e307a7014817142124a7` (80) |
| `step_drop_pos` | 1 (definition example) | `propext` | `995eb4a8f6618799bc8f18849e45758cfad0a035fa185ea47602451253d0f856` | `b84a1b29a7d1c3dfa6e00aa86daafdbf7f756f644b3d57f06c57288882c3f6fa` (81) |
| `step_drop_neg` | 1 (definition example) | `propext` | `dca1a1d2800c7e7ac02827a6752fca2f3fb26aa476d7a21ef16260dd3ccd0212` | `989bad04349c9a9615e893ede88835f894c1e803527878c1d6b0651ee89c6b2a` (81) |
| `readings_pos_perfection` | 1 (definition example) | `propext` | `cc928308d1c07d109222ef730ea67c98f71fcb0263523ca35fe1401863fc0a52` | `b7e4ff593fcce7d50f94153a55aa27323c82db5b8a26941c6ddf6f4f2873b2ce` (89) |
| `readings_neg_blocked` | 1 (definition example) | `propext` | `6b18a726d2a7ee231c52cf1a86a0701aec9e5b4e8221def59b476ad77644baa7` | `b7e4ff593fcce7d50f94153a55aa27323c82db5b8a26941c6ddf6f4f2873b2ce` (89) |
| `readings_neg_cancelled` | 1 (definition example) | `propext` | `2b6b7f45286e0d8523e4f53c7d07b9b799b2eb1e9b94bc9e5ff8af84a06dbea0` | `b7e4ff593fcce7d50f94153a55aa27323c82db5b8a26941c6ddf6f4f2873b2ce` (89) |
| `strengtheningSafe_neg` | 1 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `cbd10d027c6ddc787ba41d23e2addae45655b6f3bb37d67d25c017cf3ccca959` | `66b06964e06eb6c03f27746e7db159251d86fe39bf74a226706b1fbd665dc824` (92) |
| `literal_safety_closed_under_literal_weakening` | 2 (result) | `Quot.sound`, `propext` | `68d251c52669dca194a4c845f9cb5c348bc30ef8c6ea3f719c961fe17588b7b4` | `086838c183604ffdb71d1e17c9b5caf1ed2361d036425752e9638c0fcec0dcc6` (33) |
| `literal_weakening_tight_hsafe` | 2 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `25938f85f0bdd6beb0a788bda53e06e7ffe67e5b4816adad86bfa3c8025859ef` | `992d921bbbe36b867489b3a68700ae4a8649c4e3a45478a28092928b7e873901` (36) |
| `literal_weakening_tight_hweak` | 2 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `5f3ea758a0d7fd65426384d50ac3d27e9e69baaad4d60a5648918a94d3221477` | `238b1871ede48d036a2cac5d884d8dfaf4bfd23c69554d970ac725592c810ca3` (37) |
| `literal_weakening_nonvacuous` | 2 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `00a88375fbe62fadc82d0c9a0e4483d783244a406d823e19b576bafc4022d972` | `238b1871ede48d036a2cac5d884d8dfaf4bfd23c69554d970ac725592c810ca3` (37) |
| `full_world_count` | 2 (definition example) | `propext` | `13c03c43f40ac01d94f0865569cf6eb0c548ae5a8847215516f8824e00b140bb` | `6cf4c7c49d6a40d7ee6f32fbe20f1cac4bbe96c0552b72d95d89374a6be995b1` (6) |
| `holds_pos_all_true_world` | 2 (definition example) | `propext` | `4616f7b0e650f89a568598d469b8081a04b7c750f87aaa8ea4ab7ab0bd607914` | `bf123a96636e25d01b87d5907e885e009e93d5738ee8568b52016b751dfca41f` (33) |
| `holds_neg_partial_world` | 2 (definition example) | `propext` | `d25e76df95c790d1440295991589e23d10da5a3b88ad13facb8e06c2d636ef93` | `bf123a96636e25d01b87d5907e885e009e93d5738ee8568b52016b751dfca41f` (33) |
| `full_out_of_range_atom_false` | 2 (definition example) | `propext` | `ae11ce5a55fca0bbbc2acca51f78a92ee6f4cdb0cd6bc7c359ff5e9f2379dc18` | `c683127092bda9ee54c127155648cb65e779a874303106970fd432b71b1d2d05` (32) |
| `entails_pos_modus_ponens` | 2 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `d2cb3df5fad4b4b85fa143a267a04eb076d037f157134fdaa8af707538053895` | `a37248b475e659058c062355004135a389777b6008b5a9e42fd55aa90559e770` (36) |
| `entails_neg_affirming_consequent` | 2 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `33d8f24dc356e570f18de937bfc682f841010599ebbb9592aa98769c7b615d85` | `a37248b475e659058c062355004135a389777b6008b5a9e42fd55aa90559e770` (36) |
| `entailsB_iff` | 2 (model definitions) | `Classical.choice`, `Quot.sound`, `propext` | `d289c59f4d33ecf3c9796c72725fdacf8ac930f25ec65209e19765f7e0177b43` | `177e3337a60f5c3562016614fac4ebfe39c19f5e8686047f30aaf0a8797719c2` (33) |
| `open_converse_rewordings_not_literally_safe` | 3 (cited); 20 (cited) | `Quot.sound`, `propext` | `93467928338e94810699edc7adaa33e9257e2a707053492007ec5af138d94999` | `6f9f63baedb2ebf8dd9827318484620e1661c4823aa6d6a5be7239396bd8cfaf` (34) |
| `forall_conditional_open_converse_safe_iff_both_flags` | 3 (cited); 20 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `f37908a112b8e1e8b63d4a1cf8eb39e131db57b1b529d8bf8ae32f4f6a5a6fe0` | `29164ab4168b2736958371d172950ea9bc75d629baef3365605ec8457bb5c3e6` (91) |
| `composing_reader_minimal_blocker_sets_not_unique` | 3 (cited); 10 (cited); 11 (cited); 12 (result); 12 (non-vacuity); 14 (cited); 15 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `d17f2db1365187a8fc290c8f629d669f291776026e6abd836436fd65939ae1d3` | `f244587ebb454e9fa8ff2e8a0fc5ccd7aed79c94ea300ff72dcc98ef0239b682` (102) |
| `naive_exhaustification_of_disjunction_inconsistent` | 4 (result); 4 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `6cde828db76c3b923b13027189c9490eb9ce99f06f7de46da37496feb4e1f6d8` | `fc5d3761ba4000e8361817404f00dc2bd4d64fbc5258182d3ae48bbf98c8aa02` (52) |
| `disjunction_without_conjunctive_alternative` | 4 (result); 4 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `45489a64c7ffbb7becb64c8a24a8eea400c63b57d3f7de4b721e6e524480f0d1` | `c00e9724487824bb1d5f5e03140f816c1049d93477f8ab0c0fb003f9f6e04a31` (51) |
| `innocent_exhaustification_consistent_of_sat` | 5 (result) | `Quot.sound`, `propext` | `8f4a64c102b7975bfb88e9777055c14eb1223cd9b3af271d66aa97cfc02e1a8a` | `9e5f01af070b6a1c50d9614c4e0bdabb82dac70c3360ce77ba5830f79131eaaa` (41) |
| `innocent_exh_consistent_tight` | 5 (counterexample) | `Quot.sound`, `propext` | `84aae395ca8717d7b2581b335f39131bd3632af8483b9f84a9260167a758567e` | `606339dd34860a77c73a9cfcdf233561ebd4f4e95fea3be9a5dea5905d117b96` (44) |
| `innocent_exh_consistent_nonvacuous` | 5 (non-vacuity) | `Quot.sound`, `propext` | `fc8bee8feb85373cfe4ead44c13d9c0ca42dc1a081771fef672d2df2f4d2e6e1` | `d68ea3f4681e69069e2b74a90a8c05fa79f16e62bf30b38e79d100c4193ce1f3` (47) |
| `sat_pos_not_conversely` | 5 (definition example) | `Quot.sound`, `propext` | `708ba318dc5e658a3e18577449251c09851d190af09b31bf5ff642352ef1c522` | `e863f49d7638f4f971a0df1eee99db0a12a7a4613c26a0d8ecb986c362d8de7d` (36) |
| `sat_neg_iff_not_converse` | 5 (definition example) | `Quot.sound`, `propext` | `d5f5e9af5d6bdc8c3c3aca9ad11979c566cb13545ff2abb8159d2de441e1e4f2` | `e863f49d7638f4f971a0df1eee99db0a12a7a4613c26a0d8ecb986c362d8de7d` (36) |
| `satB_iff` | 5 (model definitions) | `Quot.sound`, `propext` | `e6fb636fc85e4920d353fd824949659cecda84fad3d183229cee10941fe1565c` | `c139dd848d32591e258dd26e204daffd450194d96bff0fcde09e833c97ab9276` (33) |
| `mem_ieList_iff_innocentlyExcludable` | 6 (result) | `Quot.sound`, `propext` | `1e94ff693e9deab92e24c9b6406637403ea5d5902cd7a1019f253b6aaa11085e` | `9019c8f154ca862831efc7e9322f8a454f770494e8427f93f17c5fca1e9fe1ea` (38) |
| `ieList_characterization_instance` | 6 (non-vacuity) | `propext` | `5a8c99b4bf686949db4a66a19eaf62a1901371fa17e25550b12efa0b0f80b40b` | `56ec1d88909cfeae645fb58c5930453c4e6ab2836c943d2472180190038b673f` (41) |
| `innocentlyExcludable_neg` | 6 (non-vacuity) | `Quot.sound`, `propext` | `7f5de0d64d11372278821d2550c39c634602224ac9e594f5c255028498ab46a9` | `5a16fcfb2390c314eeed9b48a68483af92bb40cf1450fe328731356cca763aaa` (37) |
| `ieList_characterization_unsat_prejacent` | 6 (cited) | `Quot.sound`, `propext` | `92a51f1e5b9d5de40e4e5319ed089e10ab9f012a086b45196ef320bc0240efcd` | `6ed44fb8b57de6b6553d1c4285ee0f36fe3180231dd13f6071f06a69e9da8f6d` (39) |
| `exh_weaker_than_maximal_falsified_worlds` | 6 (cited) | `propext` | `1a5d42ce009aff035efae74415234a1d1db9f4324a06ca6df0bde275981c2380` | `7f5196daa00c3d0f850d7d06de1f89802a3e8cd04ffa1d78025e992bb17decfe` (45) |
| `ieList_pos_some_not_all` | 6 (definition example) | `propext` | `6535b46d406fab74764e04617bc91625af4092abffa39e85add8c2020877cb5b` | `bccc3343c3228b115b0a9bc876b89655bcb91ba28d34cfa155f5f1d18796f314` (38) |
| `exh_pos_some_but_not_all` | 6 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `c51d21ab1fccc1275b35390e152e87204543cdd1722581967f07bd7ae1b6fc69` | `de5abc9851618ca94d05323f17d963eb77547931eb6ed1a85f0506cbb6701e2e` (45) |
| `ieList_pos_disjunction` | 6 (definition example) | `propext` | `267a77cae02bf6ef6ca982a5b8bfafb28662f3bdc3055082814e0938015e4dd7` | `42366327ef033661d0ca4e745c6ad7741e90e8022ad46ae9f7384bca4fbefe34` (41) |
| `ieList_neg_entailed` | 6 (definition example) | `propext` | `caa3baf7a97959484cb669ac45ee14fe52ee315c0f18c16caa909046072db66d` | `bccc3343c3228b115b0a9bc876b89655bcb91ba28d34cfa155f5f1d18796f314` (38) |
| `innocentlyExcludable_pos` | 6 (definition example) | `propext` | `3b6dac7d8a07f32af951030aa96418137e742eb89304572f82f1d6e831a09632` | `5a16fcfb2390c314eeed9b48a68483af92bb40cf1450fe328731356cca763aaa` (37) |
| `innocentlyExcludable_neg_disjunct` | 6 (definition example) | `Quot.sound`, `propext` | `7efd4fed82a7179ba2aecf41edddf9e247b6bdba2c7e3c80421278819f716d74` | `4cef8eb5e0b4d288f6ddf8d6a3169b661db423c0d34853f5aba39c237f9b2622` (40) |
| `naive_exh_entails_innocent_exh` | 7 (result) | `Classical.choice`, `Quot.sound`, `propext` | `a9f4df92c0ea58a2e445fc12b390b472505103930370b7a1a560edf860516750` | `89c52e1da3505caee1ad355d46ae8f917e2b740a88e36a9c28b28ecf17885586` (44) |
| `naive_exh_entails_innocent_instance` | 7 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `2fdc2058887bf567f4c43503ea9b40437166c733f1c2f087683b83741b487ee5` | `6c341b43f55089709b7d9111d69e8b6b62f0942f939b8ee15d26d48bbedacf1f` (48) |
| `innocent_exh_not_entails_naive_exh` | 7 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `d2363609e993f8845f1be2f40600d484b37de7bedc10680939654883d3b547f1` | `f272c41244277e54f1f052f87931dfcd76cea23ce3d2b916ad59616a82ecf893` (50) |
| `naiveExcl_pos_disjunction` | 7 (definition example) | `propext` | `b212af6f96836f203680e4843da9413a1a503c0e131fa7c1ca3fa2e9fae99c48` | `6f3f7193bde08f8ce22f4b50ef5e99d7aaa0546961929171617aa3b691ea7d35` (39) |
| `naiveExcl_neg_entailed` | 7 (definition example) | `propext` | `a8b14e1bbd9e6fe5b918a8412edb89fd61f793a28583762e7b239442ea964ef2` | `71eb3f977c3bcf9754cf9e120ff284505f38a6928e4c1fa7b90160f2da4f3f62` (36) |
| `innocent_equiv_naive_iff_naive_sat` | 8 (result) | `Classical.choice`, `Quot.sound`, `propext` | `b84fd5b734711d440b1d5dfb6bf7ad8dd4e11699c09025260be3342beb9686b0` | `6cde684eed13db2d98ae20524d1ac3e183af17395f26b2db6b04aebe6c70955c` (46) |
| `innocent_equiv_naive_tight` | 8 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `7936095b86348dac517fe81d29a764c354a0f835f4f28f18a9cdf0a74752e52b` | `957231279240b83dec693cd77af6d8d49ba74cd7de818e2a2fa384b3b9dd34b2` (49) |
| `innocent_equiv_naive_nonvacuous` | 8 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `7e41c6087893d166db09848c9c12dae71a7029f8a7bfe22319c60a37d772f627` | `0394720f0bd23bf8b0f60bfce8ef7dd461d8bc78d63020ef614c36732e8faac9` (54) |
| `equiv_pos` | 8 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `c8d8d9f7595b9b60ad37cbdad6c2d548474717b350616de835bfa86ea92c395b` | `5c55c9170b265e52b7f7ffbdace369e6b291a028e8bb3a5d0a48ca87f113b2c9` (37) |
| `equiv_neg` | 8 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `dcb3a72c8748519bc0fb8f895073e6736c79fec9f0baea019fd11cf8203486bc` | `e83e1acecb8e1cd8691f716c7607d7cd9f78a0cc13d3f2ef5d4a4d6ffdb546fc` (36) |
| `exh_neither_monotone_nor_antitone` | 9 (result); 9 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `c72e1dde58e6a602acfebe111cb4df52abd535546faa3329964ecda00ef73948` | `477470806f26fd1a51a4a4292e487c139a4cf1a89f0f283259a2335e25b9bc68` (65) |
| `exh_entailment_does_not_reflect` | 9 (result); 9 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `3d42a400beb2de8408cde8659fac2017dc321ed0b0af4edcdb8fb7b672111eb7` | `477470806f26fd1a51a4a4292e487c139a4cf1a89f0f283259a2335e25b9bc68` (65) |
| `blockers_sound_tight` | 10 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `afc0baa45ed4be083889d366c36be3d1e80d49cacc84e46cba9e6691cc5de3d4` | `04837d1739796ccfc189882f1693e9f478eaff9afde38c5341f25b22e747ccab` (92) |
| `blockers_sound_nonvacuous` | 10 (non-vacuity); 11 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `25b31fae6b113c8ea21abe6a60b91f918e8dc2f398686a7715223db0fe95acef` | `cb71d3d9498aa8f2ca9a3e5e464f39bc0266335aebaf5962731be21ce7647158` (95) |
| `blockers_neg` | 10 (definition example) | `propext` | `41d41081ab8b124db8e1629c4801e5a628b06101a865fe492e35e881f557ce5d` | `18fe81c7c8b48a92915bcfad87308ef602ce58d53e03ac1a5aa0feca9328e533` (86) |
| `blockers_subset_of_strengtheningSafe` | 11 (result) | `Classical.choice`, `Quot.sound`, `propext` | `0d7d1b5a4fbf620c47afc4a9362767676157863755110aae5452c71061b7c6fe` | `a0c50bd2780386188c1e1baf90251bed308c82089e159971515d9591124fdf14` (73) |
| `strengtheningSafe_iff_blockers_subset` | 11 (result) | `Classical.choice`, `Quot.sound`, `propext` | `c4235f62068357e4805a724403522eaf67d448132118d2add698337dc6af3b3a` | `da95c80ea4e1764f7445027e0f296526eb7b102fe7b7cacceabf736f106d6b9f` (74) |
| `blockers_minimal_tight` | 11 (counterexample) | `propext` | `5139e64fede854626fae67124601a38af75c237fcce37455955c0ab8f4b60b2b` | `911c953688b36dcb466775ee16a6c2af39cf19385320e99a5b430cf20d6baae2` (87) |
| `blockers_iff_tight_hlit` | 11 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `70d4b1150f52b965b4846565a0c23e2f0c8762be72945e7cdba71593635235d6` | `e35e7b8374aa21b0464788adde1001f989888a217ca8a5f6a334d26ebdfcc342` (93) |
| `strengtheningSafe_pos` | 11 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `cb6a1d50aded49cd5133ce757241dbbcdf7c6c42fbfd8f48b0e876d66ed16487` | `66b06964e06eb6c03f27746e7db159251d86fe39bf74a226706b1fbd665dc824` (92) |
| `composing_reader_some_safe_flag_set_iff_literally_safe` | 12 (cited) | `propext` | `c672cff967906a3ef723594a41183e865ecb265fc56e51cab4aa5814b6bb2133` | `3803cddbaab0f6f36a0c2269abd6413cf1c74ec841a4cc400046a3d094b3064c` (74) |
| `readingsStar_pos` | 12 (definition example) | `propext` | `099b8c4b94e30ec8bcc37e2bd7d012b3db2cdad808f7ccfcbf29c960a8aa6bb1` | `51f888ec565697e477662c679bd973bac5e3a3973a54ba73a531b2a3a2fce54e` (93) |
| `readings_neg_no_composition` | 12 (definition example) | `propext` | `26d5f229374ece71190f4f8a7d7ab59cec4ac30a5d893d79dc59d5cbc901d87e` | `58538fd5d8c7da23bb14626e4a8807627220db8725328592e07942dc9ebf2ac8` (91) |
| `readingsStar_neg_blocked` | 12 (definition example) | `propext` | `2d5bbd1a900e2957056f4daad4f9005475e2152eeaf6490bc1724bb6ede2803d` | `51f888ec565697e477662c679bd973bac5e3a3973a54ba73a531b2a3a2fce54e` (93) |
| `strengtheningSafeStar_pos` | 12 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `dcee73036fe75436aca2a3ae36a668def4a060e246c127fe7a777bb96fd8866a` | `7bb1db1f710752cce69694f078d4197463d096207bee83fec5b05f1b7b068fc6` (94) |
| `strengtheningSafeStar_neg` | 12 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `cfa93958744dd169f418a234bef82ca90c2a68c60f7895b3308d5cf5030eb18b` | `7bb1db1f710752cce69694f078d4197463d096207bee83fec5b05f1b7b068fc6` (94) |
| `conclusion_dropping_preserves_literal_safety` | 13 (result) | `Quot.sound`, `propext` | `0cb36573ea505fa51b112f13045a2656e02affb7558c13f448fc15bbe4a9bfdc` | `7dd39395b14ecb4f979bbd0a7fd14f8950d0702951516c007e0b7fc6cae78bba` (38) |
| `conclusion_dropping_tight_hE` | 13 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `f864b0e6ec0deacac19e54e361d82d27d1a8b0128cce177684b37b9c9e928e2d` | `5e301d3f49704db588d825dd94559cfba64fdd5371e5b262db4c2a9ea53bbbfa` (42) |
| `conclusion_dropping_tight_hsub` | 13 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `9a8f9fa00986f9187713fcb98c1bb2915ec2d563f124fbe342a8f25e8c0771da` | `2c0a7d296f4ded0f425285bb49c042f1de3c92a19257b568dabb9136cecc2111` (43) |
| `conclusion_dropping_nonvacuous` | 13 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `4cfcf14303901e1b3d5d0841e572325f68536a5a164d596ea723007c2ea1166b` | `2c0a7d296f4ded0f425285bb49c042f1de3c92a19257b568dabb9136cecc2111` (43) |
| `inherited_blockers_insufficient_after_conclusion_drop` | 13 (cited); 14 (cited); 15 (result); 15 (non-vacuity); 16 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `bed42cec1a155bb7a1ee5b9af72575abdb5edfd0419ef30f15814fbcdbef74bd` | `a1c5df24af5271f30fc03802b8a2fb4b9fe74570a22ed539ffc0f559d8bf610d` (102) |
| `compression_with_recomputed_blockers_strengthening_safe` | 14 (result) | `Classical.choice`, `Quot.sound`, `propext` | `a9b08f540a000bfe61e80f4279be079e48aa0acd4c8ee8c3bc909ab0d595af4c` | `9ff7a2d5d108ec79cdbced0bc3f97abfb0c681e40534e753190167ed3e136d67` (78) |
| `compression_with_entry_blockers_strengthening_safe` | 14 (result) | `Classical.choice`, `Quot.sound`, `propext` | `3b9455ee1301c0877d0c34509be0919f04402d69b1adab97c92344e58aae2498` | `9ff7a2d5d108ec79cdbced0bc3f97abfb0c681e40534e753190167ed3e136d67` (78) |
| `compression_tight_hR` | 14 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `67216471d596299c61a7f45a94788b217f015e4350bf7dbfd1ac25f8f7fc848d` | `dd65303e1157f2fa842f356fa8728e4b7b1ba5bd2a3428e9282ae03a0a65d4a1` (97) |
| `compression_tight_hcomp` | 14 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `eb0c7165c3dbd6286aea043b02077160e4a00256fda739d53948e77fdc0ebba0` | `1ef1ebed2bc85ef925555bb9cd3753c7666f9439625f2df0475ebf8e3bde3bf7` (97) |
| `compression_nonvacuous` | 14 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `ae9a0be86ae2dec08643bc369f215aa7860a34e7951b7969d4520a36abec95db` | `f06f0e056cb79c57be09b26816c6a048a6b4f260f755016b7c95590223d09592` (101) |
| `inherited_blockers_superfluous_after_conclusion_drop` | 14 (cited); 15 (result); 15 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `94631fa066f128e213e88b34758e7e020011289ab2e4717c7984375dcf1cdd67` | `11307d4a21d606c5f2e1d091edc66074def9331c67453e432dee221796c4e39a` (105) |
| `entry_blockers_strictly_larger_than_report_blockers` | 14 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `675384001fd915491b831005772cfb2a13e6860a34b9e9825239a15a5ab23e2e` | `6fe6b442efefea7830e2c9db4c99f1cb6d1bdafd8b8b15a194770c4914d5c3d7` (95) |
| `duplicated_conclusion_keeps_perfection_hazard` | 14 (cited) | `propext` | `292ee437ee9da8cf4579ca9da32081261abfc8c09c76776e8b98063b8f208cfb` | `ff9318c0a9155f55f641345f75bf45df2b3e77b93247ce4fe39487535558eef8` (91) |
| `conclusionDropping_pos` | 14 (definition example) | `propext` | `f9a02bafad32405899f122808d548c53ec376f284534ae7113d8acf90bf77f8f` | `bc39e062f47b65a9d9770f4cd44a25ed8e6c19a3ca1edbeaa00c21906c60a49e` (18) |
| `conclusionDropping_neg` | 14 (definition example) | `propext` | `bbb397d0f9cad14a37f2e29798d2545aa21897b1edbd33f7ab054e4d7f8b442d` | `bc39e062f47b65a9d9770f4cd44a25ed8e6c19a3ca1edbeaa00c21906c60a49e` (18) |
| `conclusionDropping_neg_added` | 14 (definition example) | `propext` | `3182c1b06981057b071217f1c5c0c78197edf9533c13b6a9f1675e3ba30aa885` | `bc39e062f47b65a9d9770f4cd44a25ed8e6c19a3ca1edbeaa00c21906c60a49e` (18) |
| `hypothesis_dropping_literally_safe_iff_proved_where_hypothesis_fails` | 16 (result) | `Quot.sound`, `propext` | `6311da34c702ecb32dedccf180e18e5feb2cbe819bad4e08099b6987390cdb23` | `7dd39395b14ecb4f979bbd0a7fd14f8950d0702951516c007e0b7fc6cae78bba` (38) |
| `nf_top_literally_safe_iff_unconditional` | 16 (result) | `Quot.sound`, `propext` | `61d7f2b1613c4300ed340bf61b515bd4d2e232cf42c1465a7f4679f5acffcff2` | `7dd39395b14ecb4f979bbd0a7fd14f8950d0702951516c007e0b7fc6cae78bba` (38) |
| `hypothesis_dropping_tight_hE` | 16 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `d6dc663c98319d9ec94204bed5b6d8cd7a64ae703a3e3c886682d778735a9db3` | `5e301d3f49704db588d825dd94559cfba64fdd5371e5b262db4c2a9ea53bbbfa` (42) |
| `hypothesis_dropping_nonvacuous` | 16 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `a9bd0dcd84454b01f0fdf375691de57017f257a7435becb3e531a0730a44da7f` | `5e301d3f49704db588d825dd94559cfba64fdd5371e5b262db4c2a9ea53bbbfa` (42) |
| `necessity_rendering_contradicted_iff_counterexample` | 17 (result) | `Classical.choice`, `Quot.sound`, `propext` | `d00992a1e4ef5b96ce3fc508e4c8830bd0750af1fa2f8910fc65bfec71216560` | `c3c89bd2365d1b3c2fc4bc026dd9743f81f22bb8e4add2c3153ec15f5eda9426` (34) |
| `necessity_rendering_nonvacuous` | 17 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `a48a5c1279c84f3139b2fa6f8216e67aa7e6563acefeb4cba2aa1933e1549846` | `d1c7c3b3b7b3d76a66d4c87a926f2c1456c170b2c9c022a0fc27d0327e293a47` (38) |
| `contradicts_pos` | 17 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `08ddcf84104741059ee82606fbf820a654d1717aa4da26b543c815e4350f7290` | `c7bcfa80ae3d746c4580d5fc4af041ab5729a1df5775181131635bba354edbd6` (37) |
| `contradicts_neg` | 17 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `ab49dc175b2ad2b581c520f4a3a0326985c137a7a0d0a2779553ffff8de4e8cf` | `c7bcfa80ae3d746c4580d5fc4af041ab5729a1df5775181131635bba354edbd6` (37) |
| `needed_pos` | 17 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `ba7a7eb7fb9de2d4ddcbfc005d378c1025adf9c368fed892495575006f47e251` | `988fe3ca0ad42c9f0434f93aa6383c8a08487d872b704f73f312b48e02e26afa` (37) |
| `needed_neg` | 17 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `c1bd33209c7de3ee2904f5941eef2df6e016640ed7ae0f8a2a8c9ffad41f9cef` | `319a231c7dfd1da595772550176303ea17e466cc6328266064efcb835f5bd1d4` (38) |
| `natural_instance_tight_sufficient_condition_not_needed` | 18 (result); 18 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `9a74eff98b793383e2e0ae4548d5640bbecb84da196c30ecbd46b94fd8b35f98` | `d6ae28990956edabbd9b353c49b1872e605ddada00c87a77710834e77ecc20f2` (69) |
| `tight_hypothesis_not_needed` | 18 (result); 18 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `8d17c49197162b431b349989b245f9765e46ef5e52b38585abdac3a395cce136` | `f2f1647eba88b16d01acef53ac78b148c256fc5fa2fa31148c245be0192680d0` (71) |
| `interp_never_open` | 18 (cited) | `propext` | `d8287c8dbc402b6d51e2ed1c3b3972de8fb1bf358cd9ef92e2d28b56a8bb5c36` | `0900fd252e8a6fb6abf5cac93bb9aa026ccaef89bae987edcbb141b64fefdceb` (34) |
| `interp_literallySafe_strengtheningSafe_unblocked` | 18 (cited) | `Quot.sound`, `propext` | `4cd61f3a8db3413d30e2e2c9d8f9b0f666d37a104c9c171b15a271dd400d4dde` | `1046652c2fb2699dc67c925687aff1f7222a91908287cd7af1122d8ba0b22126` (73) |
| `tightFor_does_not_check_theorem` | 18 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `a5af153892ceda0d7118b53962d7628e7e0c138e16d3fa41db719f723949d362` | `c597693c794795e82c48bdc268a2ae945dfedb79586312447499c587e7e941b1` (38) |
| `tightFor_pos` | 18 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `9325df73c27bd6415a21721878f687f76cfdd04c67f798e33ed0268f72df32f7` | `b1819b31665a747246aebe632ef4236876eaa0dd3a624b21af8488f52443153c` (37) |
| `tightFor_neg` | 18 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `6ce55543a88368d4adb1cf35dd0be70adf0ee5172cd516995ae8e51fd9954d16` | `c597693c794795e82c48bdc268a2ae945dfedb79586312447499c587e7e941b1` (38) |
| `not_shown_read_as_false_unsafe_iff_open` | 19 (result) | `Quot.sound`, `propext` | `5915b3fdd735742d2a8a9cb9b0fdb4582af789098ccca95c3c04edd9dc7b8170` | `dd2ef9e5690a7f98efa60637fcd723793e916b163dce163548ec4b9a10814406` (42) |
| `not_shown_not_refuted_safe_iff_open` | 19 (result) | `Quot.sound`, `propext` | `23580c9934ff34ba086b09eee057fa3ad028d234bc67d4c3ca3bb110b05602fe` | `dd2ef9e5690a7f98efa60637fcd723793e916b163dce163548ec4b9a10814406` (42) |
| `not_shown_tight_htrue` | 19 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `040c63f2c80ed930d6403fdf12f8e2d887daa275cabd74b99d0f3151cb5cbfb7` | `a4b54ae9ec57084a6236d9aaaa332b82cd657d41760ad2b636dbb1f9959a79f2` (45) |
| `disclaimer_nonvacuous` | 19 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `4c54663af4c8f224cf868323c1e3e74eff80fa71b4234adce52d29addfb7ff6c` | `a4b54ae9ec57084a6236d9aaaa332b82cd657d41760ad2b636dbb1f9959a79f2` (45) |
| `not_shown_read_as_false_safe_when_refuted` | 19 (positive control) | `Classical.choice`, `Quot.sound`, `propext` | `c1dcbbf5a83656da93e80bc945e058267dfbdd85e4b2df14fe397f3b26f4307a` | `eb47a282ca023cbbcb88c220569820d9a09b74440667be59aa78f3c2ef87a3b8` (44) |
| `open_pos` | 19 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `dafc57b78ec088fd3a628d244f7689141f71954301cfc1469a22f87790d5df5c` | `eb35e8685a02dbad89ce626236f23c56989fa5b430b29b72ead43166d85e9f19` (36) |
| `open_neg` | 19 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `ee34d588119f6744be1e7b81f91e4605919251ee5d6fe6f37d065ca32982fec3` | `eb35e8685a02dbad89ce626236f23c56989fa5b430b29b72ead43166d85e9f19` (36) |
| `disclaimerSafe_pos` | 19 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `4b04a69077b41786d30db0f30d5a3f7f442d387d9f3395a234ff8a3145dc2c06` | `eb47a282ca023cbbcb88c220569820d9a09b74440667be59aa78f3c2ef87a3b8` (44) |
| `disclaimerSafe_neg` | 19 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `0ae551b095d7c1606a1222d1a17cbee8bc724bb558077639b6420113ea752b2b` | `eb47a282ca023cbbcb88c220569820d9a09b74440667be59aa78f3c2ef87a3b8` (44) |
| `disclaimerTrue_neg` | 19 (definition example) | `Classical.choice`, `Quot.sound`, `propext` | `325e5ad14b1c501980f16b7d574c6dc455aca460927761535090415a9d2ec20d` | `cc2f751b74d261bda0a3c557ecb987d6383deca9e0ba02a0b14eb46c47cc07fc` (42) |
| `forall_conditional_unblocked_unsafe_of_perfection_consistent_of_converse_excludable` | 20 (result) | `Classical.choice`, `Quot.sound`, `propext` | `c032825ac54c8a3b7a3cb17c4e3d220dac4a8bcd703061e04d80fe5ce64386cb` | `578f97f8e96dd403e25a0be01618004db758d0c057839bce8c1677083dad4f55` (90) |
| `forall_conditional_blockers_by_converse_status` | 20 (result) | `Classical.choice`, `Quot.sound`, `propext` | `cd64840a13874344ca51f92ec3b3fac15d2cc272c46b34bbfa8e0c296cedbd19` | `11c71d196f50c2825dcc44357e146e57df62ce4835bb0c8b5c732efef4d9f0c8` (89) |
| `forall_conditional_blockers_of_open_converse` | 20 (result) | `Classical.choice`, `Quot.sound`, `propext` | `7a9a962187d2dc2ad4ab15d3e6b83bde2318eaea1dc63fcac4c48dd1369ded23` | `1ce08dc9835008ad612d176c3e342f29080a080763853b8517110e23c9f3e5aa` (86) |
| `forall_conditional_tight_hE` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `53b56b27b952cae51d65bf589df1da7ba06d4b034db74c171ac42f0b450c833b` | `182d9e7cbef6f70c4da15bbcfef59fc6d840cc4a075f9f28ea0b65cc1c25450f` (95) |
| `forall_conditional_blockers_tight_hE` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `b13334dd4546a304a89967363edfd1ef6b48b70ea21e6c2ec17d965b3f88537a` | `9e34920f26faf55e0fe90215f5284060ce5dae8f88d4bce68fea831e9739e5c9` (92) |
| `forall_conditional_blockers_tight_hlit` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `09602ec6bcf0bedc019ae66d1905fb855eff7501d19d2c105c7052df76a4e299` | `94cfbc86b98cccab6d8d10ef3b3b7f704a4160a24d12df9468866bee3d80d89a` (90) |
| `forall_conditional_tight_hperf` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `f82fb97e056349b292cd1e178e5ce9df2abe4df179bafbca7f02f03aabb2ab5f` | `d0dfc7df7638cddea1fd707f386a766cf9330026db429d989d8a09bdc685f2f6` (92) |
| `forall_conditional_tight_hperf_full` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `b562658a855b57802983291f7d1ec9956b5082add9cd4819dedad409b32b4951` | `1087677e2c2f0ea19d6a72a3fdd31933b4ccf22bd8f3e061f363c4f628fca2d1` (93) |
| `forall_conditional_blockers_tight_hperf` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `c582f8a7de0f8ed518f40b76b425a1c7035d6a3b727c9ad56a142e898760a058` | `42f8282b9275203f420bcaf24c75ed91bda24d12bd4cc11864510c294af8a0c5` (90) |
| `forall_conditional_open_tight_hperf` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `0fc4d0dd7f9c69bf78fc10cda55a00a57d08f0ce2418b73c9079aa1941944e33` | `818d1e660ad192fd37d5e578e06505c2a03fc2c4f4ab5159bab5927f3df2f38c` (87) |
| `forall_conditional_tight_hconv` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `b9bcd26161342f9cbebc8e7380b3212b1f96f9fb1330627049433cb7755389d4` | `ed2d9f531f3ba83990aa0160d87f65fb9a8fc4d369eddd837b36267799dbfb0c` (92) |
| `forall_conditional_blockers_tight_hconv` | 20 (counterexample) | `Classical.choice`, `Quot.sound`, `propext` | `9c49587a14efb9b9d9a50ca932f13877d06d44169397d1408c3eec065b293caf` | `9e0fe1892215c62390464a5705d8c57000943cdd3eb86edfe0ee4734f05f9a58` (89) |
| `forall_conditional_open_tight_hopen` | 20 (counterexample) | `Quot.sound`, `propext` | `7fbe6bc02ec3ecfb193f50f33641e58997eb3f3531fdf65a3677ff85d94cfa2d` | `67a3c9882c5bdbb8d05bccb54a8d2127cd06b0e31ddb8842caaea338056fcec8` (89) |
| `forall_conditional_nonvacuous` | 20 (non-vacuity) | `Quot.sound`, `propext` | `4c35f22d9934f881aaf177144403ac9be227b597140f6f7a05e9b5c3de1fcbac` | `0842aec53f7ee6232d59efffadc49e8beec9e7482651ee5b71b175be874d41b2` (39) |
| `forall_conditional_blockers_nonvacuous` | 20 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `57fb5d1460a4af3341d33997bd637d56b6a3b0a166c05b8486b45a8118e00257` | `c8ddabe2677dead7bad2f7dfcd1b529bc9d563cad3c0a5707104211ac9f867d1` (93) |
| `forall_conditional_open_nonvacuous` | 20 (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `d5c9c313048d8b3709b3830cdd62b00b18095f58f8de39fc4068fbbaa8f0c9e9` | `8ff3f56549fb5c5f62283934447cecad7fbe188a155201a84d74772053c5111f` (39) |
| `forall_conditional_safe_with_blockers` | 20 (positive control) | `Classical.choice`, `Quot.sound`, `propext` | `c3e3d62fec113e8d57d03f95391d0d0b5df15599e764a00fb094dc9031e43896` | `66b06964e06eb6c03f27746e7db159251d86fe39bf74a226706b1fbd665dc824` (92) |
| `distinct_atoms_nondegenerate_in_full_spaces` | 20 (cited) | `Quot.sound`, `propext` | `091a5633999e6356c75556080cee5d7e7d75d2e7b8a7e36f7d96b7359384804f` | `12d26733724912bde412a4873a6e3ae069495505d9766bec9c0d67d286022ad7` (39) |
| `single_value_conditional_needs_exhaustification_flag` | 20 (cited) | `Classical.choice`, `Quot.sound`, `propext` | `f35a0a1e3e89a25f42bfe769b0a46d1aa50e8c0cc0a9dc0f7725017cbe5ac9e0` | `9c89c262772963cdea8ccef951a87e57887cd84637257f63ce66564793b8b468` (95) |
| `perfectionConsistent_pos` | 20 (definition example) | `Quot.sound`, `propext` | `05829e75bb856743348ebfe358c287db9d2149d646a55017573ee9339dedb0bd` | `13a1023bd8d47279a892e3469ff66c8e95527039d9f5651c12d7b352900defb2` (37) |
| `perfectionConsistent_neg` | 20 (definition example) | `Quot.sound`, `propext` | `8ca09f050d5e861c35ea0a560589130b8bfd4ef7d7037e7179e63d5829c22f5a` | `55db504fc6fba00a1305604f07c952fbae10832fa18a9e76fc9416802e58497c` (36) |
| `converseExcludable_pos` | 20 (definition example) | `Quot.sound`, `propext` | `7ec8d8f68b3335f03604ce9ec73008536220f5444f658de137122e79d50cb9c1` | `ec9a7137d4b2258a518c6eec7b2ea06a43a8786d956b1e5a48bf96ac06b71b04` (37) |
| `converseExcludable_neg` | 20 (definition example) | `Quot.sound`, `propext` | `4242d2cb95f82c57b7caa1c01d5c00f1863588e9738a345d06b743966d1d1eb7` | `ab6e52a00ca6a57055fa04a62d812bd5841acfe540536086ae5d8eebca915e98` (36) |

**Primary sources** (records checked against the publisher or Crossref metadata; the role of each source is stated in the cards' prior-art entries):

- M. L. Geis and A. M. Zwicky, "On invited inferences", Linguistic Inquiry 2(4):561-566, 1971 (no DOI; the volume, issue and pages were confirmed from the Crossref reference list of Horn 2000; the publisher record itself could not be consulted).
- L. R. Horn, A Natural History of Negation, University of Chicago Press, Chicago, 1989; reissued by CSLI Publications, Stanford, 2001, ISBN 1-57586-336-7. Chapter 4, "Negation and Quantity".
- L. R. Horn, "From if to iff: Conditional perfection as pragmatic strengthening", Journal of Pragmatics 32(3):289-326, 2000, doi:10.1016/S0378-2166(99)00053-3.
- H. P. Grice, "Logic and conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics 3: Speech Acts, Academic Press, New York, 1975, pp. 41-58; Brill reissue doi:10.1163/9789004368811_003.
- I. A. Noveck, "When children are more logical than adults: Experimental investigations of scalar implicature", Cognition 78(2):165-188, 2001, doi:10.1016/S0010-0277(00)00114-1.
- L. Bott and I. A. Noveck, "Some utterances are underinformative: The onset and time course of scalar inferences", Journal of Memory and Language 51(3):437-457, 2004, doi:10.1016/j.jml.2004.05.006.
- D. Fox, "Free choice and the theory of scalar implicatures", in U. Sauerland and P. Stateva (eds.), Presupposition and Implicature in Compositional Semantics, Palgrave Macmillan, 2007, pp. 71-120, doi:10.1057/9780230210752_4.
- U. Sauerland, "Scalar implicatures in complex sentences", Linguistics and Philosophy 27(3):367-391, 2004, doi:10.1023/B:LING.0000023378.71748.db.
- M. Krifka, "Focus and presupposition in dynamic interpretation", Journal of Semantics 10(4):269-300, 1993, doi:10.1093/jos/10.4.269.
- B. Spector, "Comparing exhaustivity operators", Semantics and Pragmatics 9, article 11, pp. 1-33, 2016 (published 27 April 2016), doi:10.3765/sp.9.11. Cited results: Proposition 1 and Corollary 2 (p. 11), Proposition 7 and Corollary 8 (p. 12), Theorem 9 (p. 13), section 2.2.2 (pp. 8-9).
- G. Chierchia, D. Fox and B. Spector, "Scalar implicature as a grammatical phenomenon", in C. Maienborn, K. von Heusinger and P. Portner (eds.), Semantics: An International Handbook of Natural Language Meaning, vol. 3, De Gruyter, Berlin, 2012, pp. 2297-2332, doi:10.1515/9783110253382.2297.
- K. Schulz and R. van Rooij, "Pragmatic meaning and non-monotonic reasoning: The case of exhaustive interpretation", Linguistics and Philosophy 29(2):205-250, 2006, doi:10.1007/s10988-005-3760-4.
- K. von Fintel, "Conditional strengthening: A case study in implicature", unpublished manuscript, MIT, draft version of 13 September 2001 (page header "Draft • Version from 9/13/01 1:08 PM"), https://web.mit.edu/fintel/fintel-2001-condstrength.pdf (no DOI, and no content hash is recorded: the URL and the page header are the strongest identity available for this manuscript, so a later replacement of the file at that URL would not be detected from this record; the header and the cited passages were checked against the file at that URL on 2026-11-21). Cited passages: the section "Not True No Matter What" (pp. 5-8) and the discussion of the scale "if and only if p, q" versus "if p, q" and Atlas and Levinson (1981) (pp. 13-14).
- J. van der Auwera, "Pragmatics in the last quarter century: The case of conditional perfection", Journal of Pragmatics 27(3):261-274, 1997, doi:10.1016/S0378-2166(96)00058-6.
- R. Katzir, "Structurally-defined alternatives", Linguistics and Philosophy 30(6):669-690, 2007, doi:10.1007/s10988-008-9029-y.
- J. D. Atlas and S. C. Levinson, "It-clefts, informativeness and logical form: Radical pragmatics (revised standard version)", in P. Cole (ed.), Radical Pragmatics, Academic Press, New York, 1981, pp. 1-61 (one library record gives pp. 1-62; no DOI).

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The primary check, run from the package directory, is:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects `sorry`, `admit`, `native_decide` and `axiom` declarations in the sources, computes the axioms of every declaration of the library with Lean's `collectAxioms` (allowing `propext`, `Classical.choice`, `Quot.sound`), and recomputes, for every Lean name referenced by `results.json`, the statement hash (SHA-256 of Lean's `repr` of its type) and the closure hash (SHA-256 of the sorted `name : repr(type) := repr(value)` lines of the package-local constants reachable from the statement, theorem bodies excluded), comparing both with `audit/statements.json`. Exit status 0 means every check passed.

A manual axiom audit of the card theorems needs `lake` alone:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` (outside the library target) imports `Implicature` and runs `#print axioms` for every Lean name referenced by `results.json`; each output line should list a subset of `propext`, `Classical.choice`, `Quot.sound`. To check a single statement by eye, compare the quoted source lines in **Findings** with the cited lines of `lean/Implicature/*.lean`.

A passing revalidation establishes that the theorems hold for the Lean definitions as quoted; it does not test the modeling bridges.

