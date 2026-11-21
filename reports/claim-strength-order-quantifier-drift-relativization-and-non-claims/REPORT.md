# Claim strength: order, quantifier drift, relativization, and non-claims

## Summary

This package is a Lean 4 formalization (core Lean and `Std`, no Mathlib) of a vocabulary for how strongly a report establishes a claim, and of recurring ways in which a summary of a result can claim more than the result. A claim is a predicate on interpretations and a report is the finite list of claims it establishes. A claim is *supported* by a report if it holds in every interpretation consistent with the report, *contradicted* if its negation is supported, and *undetermined* if it is neither supported nor contradicted. On this three-answer semantics the package proves when the correct answer is unique, which question forms make an answer key inconsistent with the semantics, sufficient criteria for one quantifier-prefix claim shape to entail another (quantifier order, universal-to-existential weakening, binder domains, premises) together with the fragments in which each criterion is also necessary and the failures outside them, drift counterexamples (a strictly stronger reading that does not follow) paired with the weaker reading that does follow, and a frontier test for positive over-reading. Every result is a kernel-checked theorem about this toy model.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Scope.** These are statements about the toy model; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason. Model–system relation: none proved (no embedding, abstraction or simulation between the model and real reports or readers is defined or proved). Remarks that connect a theorem to real reports are separate claims labelled `Basis: derived (modeling bridge)`.

**Vocabulary.** Each phrase names exactly one predicate: *supported* (also *established*) is `Supported E q`; *unsupported* (also *not established*) is `¬ Supported E q`; *contradicted* is `Contradicted E q`; *not contradicted* is `¬ Contradicted E q`; *undetermined* is `Undetermined E q` (unsupported and not contradicted). An unsupported claim of a satisfiable report can be contradicted; an undetermined claim cannot. The phrase "not supported" is not used.

What each result does *not* show is listed under **Boundaries**, first subsection (**Non-claims**), card by card; read the non-claims of a card together with its plain claim. Every package identifier named in this report is quoted verbatim with its `file:line` range under **Applicability** (definitions), **Findings** (theorems) or **Findings → Auxiliary lemmas cited by name**.

Results (plain-language claims, as recorded in `results.json`):

1. **`three-answers-exactly-one-iff-satisfiable`** (characterization, T0, definitional, reference point). For every report E and claim q: exactly one of Supported E q, Contradicted E q, Undetermined E q holds if and only if E is satisfiable. If E is unsatisfiable, then q is both supported and contradicted. If E is satisfiable and both a and b are correct answers about q, then a = b. Some answer is always correct. For every E, q, a: a is incorrect iff a is a positive over-reading (answering supported for an unsupported claim), a negative over-reading (answering contradicted for a claim that is not contradicted), or an under-reading (answering undetermined for a claim that is supported or contradicted).
2. **`answers-monotone-under-satisfiable-report-extension`** (theorem, T0, shallow, reference point). If every claim of E is in E', then a claim supported by E is supported by E' and a claim contradicted by E is contradicted by E'. If every claim of E is in E' and E' is satisfiable, then, whenever a correct answer about q for E differs from a correct answer about q for E', the E-answer is undetermined.
3. **`undetermined-iff-witnesses-both-ways`** (characterization, T0, definitional, reference point). Undetermined E q holds if and only if some interpretation consistent with E satisfies q and some interpretation consistent with E falsifies q; Contradicted E q is the same as Supported E (¬q); if c ∈ E and c entails ¬q (for example, an exhibited counterexample to a universal claim q), then q is contradicted; and over Nat the satisfiable report [n ≤ 1, 1 ≤ n] contradicts n = 0 ∨ n = 2 although neither of its claims alone entails the negation.
4. **`unsupported-does-not-imply-contradicted`** (counterexample, T0, definitional, reference point). Over the interpretations Bool, it is not the case that for every report E and claim q, 'unsupported' (¬ Supported E q) implies 'contradicted': the empty report leaves q = (b = true) unsupported and not contradicted (unsupported_not_imply_contradicted_witness). With the predicates P on Nat as the interpretations, the universal claim 'every m satisfies P' is undetermined by the empty report and contradicted once the claim '¬ P 0' is added. Conversely, if q is contradicted by E and E is satisfiable, then q is unsupported.
5. **`meta-level-questions-are-never-undetermined`** (impossibility, T1, shallow). For every report E and every world-independent claim q (its truth does not depend on the interpretation), Undetermined E q is false, with no satisfiability assumption. The meta-level question 'E establishes q' (the constant claim Supported E q) is world-independent; if q is unsupported by E, it is contradicted. For every E and q, the one-entry answer key [(Establishes E q, undetermined)], which marks 'E establishes q' as undetermined, is incorrect; since KeyCorrect requires every entry of a key to be correct, every answer key containing that entry is incorrect as well (immediate from the definition of KeyCorrect, not stated as a separate theorem). If Undetermined E q, the answer key that marks 'E establishes q' as contradicted and q as undetermined is correct.
6. **`compound-answer-tables-over-satisfiable-reports`** (characterization, T0, shallow, reference point). If E is satisfiable, q₁ has correct answer a₁, and q₂ has correct answer a₂, then the correct answer for q₁ ∧ q₂ lies in andTable a₁ a₂ and that for q₁ ∨ q₂ lies in orTable a₁ a₂: for ∧, contradicted if either conjunct is contradicted, the other conjunct's answer if one is supported, and undetermined or contradicted when both are undetermined; dually for ∨. Every answer listed in every cell occurs for some pair of claims over four interpretations (Bool × Bool) with the empty report; in the cell (undetermined, undetermined) both answers occur with distinct component claims. For every report, if a is a correct answer for q then negAnswer a (swapping supported and contradicted, keeping undetermined) is a correct answer for ¬q. For every element w₀ : W, if every interpretation consistent with E equals w₀ (so E has at most one consistent interpretation; E may also be unsatisfiable), then no claim is undetermined by E.
7. **`prefix-criterion-sufficient-environment-semantics`** (theorem, T1, substantive). For quantifier prefixes φ and ψ on the variables Fin n, in front of the same uninterpreted matrix (variables matched by index), if no variable is bound twice in φ, every variable is bound exactly once in ψ, (i) every variable universal in ψ is universal in φ, and (ii) whenever v is existential in φ and u is universal in both with u bound before v in φ, u is also bound before v in ψ, then for every base type α, every matrix R and every environment ρ : Fin n → α, φ with R implies ψ with R (SEntailsAt α φ ψ). This holds vacuously when α is empty and n ≥ 1, where there is no environment and every pair satisfies SEntailsAt (sentailsAt_of_isEmpty). If a prefix binds every variable, its value does not depend on the environment. For every type α, (∀ P, (∀x, P x) → ∃x, P x) holds iff α is nonempty.
8. **`prefix-criterion-necessary-two-point-base`** (theorem, T1, substantive). For prefixes φ and ψ on the variables Fin n (same matrix, variables matched by index): (1) if no variable is bound twice in φ or in ψ, the base type α has two distinct elements, and SEntailsAt α φ ψ holds, then parts (i) and (ii) of the prefix criterion hold. (2) If no variable is bound twice in φ and every variable is bound exactly once in ψ, then for every base type α with two distinct elements, SEntailsAt α φ ψ holds iff the criterion holds. (3) If no variable is bound twice in φ and every variable is bound exactly once in ψ, then SEntails φ ψ (SEntailsAt at every base type) holds iff the criterion holds. (4) For all φ and ψ, SEntails φ ψ holds iff SEntailsAt α φ ψ holds at every base type α with two distinct elements. (5) If α has at most one element (Subsingleton α), then every prefix evaluates to its matrix at the environment, and SEntailsAt α φ ψ holds for all φ and ψ.
9. **`prefix-entailment-decidable`** (characterization, T1, shallow). The Boolean function prefixCritB satisfies prefixCritB φ ψ = true ↔ PrefixCrit φ ψ, and wfB φ = true ↔ WF φ. If the base type α has two distinct elements, no variable is bound twice in φ, and every variable is bound exactly once in ψ, then SEntailsAt α φ ψ holds iff prefixCritB φ ψ = true. On two variables: ∃y∀x entails ∀x∃y at every base type, and ∀x∃y does not entail ∃y∀x at Bool (countermodel: the matrix y = x, under which ∀x∃y holds and ∃y∀x fails; forall_exists_not_sentails_exists_forall_witness). On one variable: ∀x entails ∃x at every base type under environment semantics (vacuously when the type is empty), and ∃x does not entail ∀x at Bool. prefixCritB returns true / false on these four pairs, and false on ∀x₀∃x₁ versus ∀x₁∃x₀. Over relations on Nat, '∀x ∃n, R x n' does not entail '∃n ∀x, R x n' (countermodel R = ≤; in particular (∀x, ∃n, x ≤ n) → (∃n, ∀x, x ≤ n) is false over Nat), and '∃n ∀x' entails '∀x ∃n'.
10. **`domain-and-premise-variance`** (characterization, T0, definitional, reference point). For domains D, D' and premises H, H' on a type α: '∀x ∈ D, P x' entails '∀x ∈ D', P x' for every predicate P iff D' ⊆ D; '∃x ∈ D, P x' entails '∃x ∈ D', P x' for every P iff D ⊆ D'; '∀x, H x → C x' entails '∀x, H' x → C x' for every C iff H' ⊆ H; and '∀x, H x → C x' entails '∀x, C x' for every C iff H holds everywhere. Instances: over predicates P on Nat, 'P 2' does not entail '∀k ≥ 1, P k' (countermodel P k := k = 2; single_parameter_not_range_witness) while the converse holds; over pairs (H, C) of predicates on Nat, '∀x, H x → C x' does not entail '∀x, C x' (countermodel H = C = (· = 0); relative_not_absolute_witness) while '∀x, C x' entails '∀x, H x → C x' (absolute_entails_relative); over pairs (A, C) of propositions, 'A → C' does not entail 'C' (countermodel A = C = False; relative_to_assumption_not_absolute_witness); over triples (H₁, H₂, C) of propositions, 'H₁ ∧ H₂ → C' does not entail 'H₁ ∨ H₂ → C' (countermodel H₁ = True, H₂ = False, C = False; conj_premise_not_disj_witness) while the converse holds.
11. **`drift-single-counterexample-versus-universal-or-subclass`** (counterexample, T0, definitional, reference point). Over predicates P on Nat, a single counterexample ('∃m, ¬P m') does not entail a universal refutation ('∀m, ¬P m') (countermodel P m := m ≠ 0; single_counterexample_not_universal_witness), and a counterexample among all naturals does not give one among the even naturals (countermodel P m := m % 2 = 0, which fails at 1 and holds at every even number; counterexample_in_class_not_in_subclass_witness). Conversely, for every nonempty type α, '∀m, ¬P m' entails '∃m, ¬P m' over predicates P on α; and over predicates P on Nat, for classes K, K' of naturals such that every element of K' is in K, a counterexample in K' is one in K.
12. **`drift-sufficient-versus-characterization`** (counterexample, T0, definitional, reference point). Over pairs (A, B) of propositions, 'A → B' does not entail 'A ↔ B' and does not entail 'B → A' (countermodel A = False, B = True; sufficient_not_characterization_witness, sufficient_not_converse_witness), while 'A ↔ B' entails 'A → B'. For checkers on Nat (an acceptance function and a goodness predicate), soundness ('accept → good') does not entail completeness ('good → accept') (countermodel zeroChecker, which accepts exactly the input 0, with the even numbers good; checker_sound_not_complete_witness), completeness does not entail soundness (countermodel acceptAll, which accepts every input, with no input good; checker_complete_not_sound_witness), and soundness-and-completeness entails soundness.
13. **`relativized-criterion-sound`** (theorem, T1, substantive). For relativized shapes φ and ψ (a prefix whose binders carry named domain classes, plus one named premise, evaluated by Holds as Q₁x₁∈I k₁ … Qₘxₘ∈I kₘ (J p x⃗ → M x⃗)), if both prefixes bind every variable exactly once, the tables incl, meets, impl are sound for the interpretations I, J (incl k k' = true implies I k ⊆ I k'; meets k k' = true implies I k and I k' share an element; impl p p' = true implies J p ⊆ J p'), and RCrit incl meets impl φ ψ holds (the prefix criterion; incl ψ-domain φ-domain = true for each variable universal in ψ; incl φ-domain ψ-domain = true for each variable existential in φ; meets φ-domain ψ-domain = true for each variable universal in φ and existential in ψ; impl ψ.prem φ.prem = true), then for every matrix M and environment ρ, φ with M implies ψ with M. No cardinality or nonemptiness assumption; when α is empty and n ≥ 1 the conclusion holds vacuously (rEntails_of_isEmpty). RCrit is decided by rcritB. If every domain of a prefix is nonempty and the premise does not depend on the variables it binds, the premise can be pulled out of the prefix (evalR_premise_pull_out); over Nat the shape ∀x ∈ {0,1} ∃y ∈ Nat (x ≤ 1 ∧ y ≤ 1 → M) holds for every M.
14. **`relativized-criterion-complete-polarized-two-point-premise-free`** (theorem, T1, substantive). If no variable is bound twice in the prefix of φ or of ψ (a prefix may leave variables unbound; they take their values from the environment), the tables incl, meets, impl are exact for I, J (incl k k' = true iff I k ⊆ I k'; meets k k' = true iff I k and I k' share an element; impl p p' = true iff J p ⊆ J p'), the base type α is nonempty, every existential domain of φ and every universal domain of ψ has at least two elements, and both premises hold at every assignment, then REntails I J φ ψ implies RCrit incl meets impl φ ψ. If α is nonempty, every existential domain of φ and every universal domain of ψ has at least two elements, the premise of ψ holds at every assignment, and REntails I J φ ψ holds, then every domain of φ and of ψ is nonempty (nonempty_domains_of_rEntails).
15. **`relativized-criterion-incomplete-outside-fragment`** (counterexample, T1, shallow). Outside the fragment of the completeness theorem the combined criterion is not complete. Over the base type Nat with the exact tables clsIncl, clsMeets, premImpl there are shapes for which the entailment holds for every matrix but the criterion fails, caused by: an empty or singleton existential domain in φ; an empty or singleton universal domain in ψ; a singleton domain on both sides (also with both shapes in normal form); a premise of φ that restricts a universal domain or is implied by an existential domain; a premise of ψ that restricts a universal domain, is unsatisfiable, or constrains an existential variable (making ψ valid); a repeated binder in φ or in ψ. Over Nat, with two-point domains, trivial premises and shapes without repeated binders, replacing one exact table by a sound but inexact one (inclusion 'equal classes', overlap 'never', implication 'never') also breaks completeness. Over the empty base type, with exact tables, ∀x entails ∃x vacuously while the criterion fails.
16. **`frontier-testing-detects-overreading-for-closed-readers`** (theorem, T1, shallow). For a report E, a finite candidate list Q, and a reader's endorsement predicate End: if q is unsupported and q' entails q, then q' is unsupported; every nonempty list of claims has an entailment-weakest element; if q ∈ Q is unsupported, it entails some frontier candidate (a weakest unsupported candidate); and if End is closed under entailment among the candidates and endorses no frontier candidate, then every candidate End endorses is supported, so answering 'supported' for an endorsed candidate is never a positive over-reading. Undetermined claims are not closed upward in strength; every End treats logically equivalent claims alike; and the test says nothing about claims outside Q.

## Applicability

**Model fidelity.** All definitions are toy models written for this package; none is a production definition of an existing system. The definitions are meant to capture how a reader of a technical report should answer comprehension questions of the form "does the report establish q?", and how a one-sentence summary of a formal result relates in strength to the result it summarizes. The known gaps are listed with each component:

- *Claims and reports.* A claim is an arbitrary predicate `W → Prop` on an arbitrary interpretation type `W`; a report is the finite list `E` of claims it establishes. Not modeled: natural-language meaning, hedges, examples, the process by which a reader answers, or any particular report.
- *Claim shapes.* A quantifier prefix over variables `Fin n` ranging over one base type `α`, in front of an uninterpreted matrix (an arbitrary predicate on full assignments `Fin n → α`); variables are matched by index. Schematic entailment uses environment semantics: it quantifies over matrices and over environments `ρ : Fin n → α` (which give values to variables a prefix leaves unbound), so it is vacuous on an empty base type when `n ≥ 1`. Relativized shapes add a named domain class per binder (interpreted by `I : K → α → Prop`) and one named premise (interpreted by `J : P → (Fin n → α) → Prop`) that sits, as an implication antecedent, inside the scope of every binder. Not modeled: several sorts, function symbols, connectives between quantifiers, partially ordered prefixes, a restricted matrix language, renaming of variables.

**Model–system relation: none proved.** No embedding, abstraction or simulation relating the model to natural-language reports, to readers, or to any particular report is defined or proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason. Each connection this report draws between a theorem and real reports or answer keys is a separate claim labelled `Basis: derived (modeling bridge)`, with its reasoning (see **Findings → Design consequences**).

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library and `Std`, with no Mathlib and no other Lake dependency. The Lake package `claim_strength` in `lean/` has one library, `ClaimStrength` (modules `Basic`, `Compound`, `Drift`, `Frontier`, `Prefix`, `PrefixList`, `Relativized`, `Complete`, `PrefixResults`, `RelResults`, `Witnesses`), and every declaration lives in the namespace `Toy.ClaimStrength`. Proofs use classical logic; the axiom audit under **Evidence** lists the axioms per declaration.

**Subjects.** `REPORT.json` lists the Lean toolchain, which checks every proof, and the 11 cited papers that have a DOI, each identified by its DOI. The five cited works without a DOI (Enderton 2001, Grice 1975, Henkin 1961, Horn 1984, and Geis and Zwicky 1971) are not listed in `REPORT.json`; their full bibliographic records are under **Evidence → Primary sources**. None of the cited works is formalized here; each card states what it takes from its citations.

### Definitions (verbatim)

Every package definition that occurs in a statement quoted in this report. Each block quotes the source verbatim; its first line gives the file (relative to `lean/`) and the line range.

**`Claim`**
```lean
-- ClaimStrength/Basic.lean:24
abbrev Claim (W : Type) := W → Prop
```

**`Entails`**
```lean
-- ClaimStrength/Basic.lean:29
def Entails (A B : Claim W) : Prop := ∀ w, A w → B w
```

**`Models`**
```lean
-- ClaimStrength/Basic.lean:32
def Models (E : List (Claim W)) (w : W) : Prop := ∀ e ∈ E, e w
```

**`Satisfiable`**
```lean
-- ClaimStrength/Basic.lean:35
def Satisfiable (E : List (Claim W)) : Prop := ∃ w, Models E w
```

**`Supported`**
```lean
-- ClaimStrength/Basic.lean:39
def Supported (E : List (Claim W)) (q : Claim W) : Prop := ∀ w, Models E w → q w
```

**`Contradicted`**
```lean
-- ClaimStrength/Basic.lean:42
def Contradicted (E : List (Claim W)) (q : Claim W) : Prop := ∀ w, Models E w → ¬ q w
```

**`Undetermined`**
```lean
-- ClaimStrength/Basic.lean:47-48
def Undetermined (E : List (Claim W)) (q : Claim W) : Prop :=
  ¬ Supported E q ∧ ¬ Contradicted E q
```

**`Answer`**
```lean
-- ClaimStrength/Basic.lean:51-55
inductive Answer
  | supported
  | undetermined
  | contradicted
  deriving DecidableEq, Repr
```

**`Correct`**
```lean
-- ClaimStrength/Basic.lean:58-61
def Correct (E : List (Claim W)) (q : Claim W) : Answer → Prop
  | .supported => Supported E q
  | .undetermined => Undetermined E q
  | .contradicted => Contradicted E q
```

**`ExactlyOne3`**
```lean
-- ClaimStrength/Basic.lean:64-65
def ExactlyOne3 (a b c : Prop) : Prop :=
  (a ∧ ¬ b ∧ ¬ c) ∨ (¬ a ∧ b ∧ ¬ c) ∨ (¬ a ∧ ¬ b ∧ c)
```

**`PositiveOverReading`**
```lean
-- ClaimStrength/Basic.lean:68-69
def PositiveOverReading (E : List (Claim W)) (q : Claim W) (a : Answer) : Prop :=
  a = .supported ∧ ¬ Supported E q
```

**`NegativeOverReading`**
```lean
-- ClaimStrength/Basic.lean:72-73
def NegativeOverReading (E : List (Claim W)) (q : Claim W) (a : Answer) : Prop :=
  a = .contradicted ∧ ¬ Contradicted E q
```

**`UnderReading`**
```lean
-- ClaimStrength/Basic.lean:76-77
def UnderReading (E : List (Claim W)) (q : Claim W) (a : Answer) : Prop :=
  a = .undetermined ∧ (Supported E q ∨ Contradicted E q)
```

**`WorldIndependent`**
```lean
-- ClaimStrength/Basic.lean:81
def WorldIndependent (q : Claim W) : Prop := ∀ w w', q w → q w'
```

**`Establishes`**
```lean
-- ClaimStrength/Basic.lean:85
def Establishes (E : List (Claim W)) (q : Claim W) : Claim W := fun _ => Supported E q
```

**`AnswerKey`**
```lean
-- ClaimStrength/Basic.lean:88
abbrev AnswerKey (W : Type) := List (Claim W × Answer)
```

**`KeyCorrect`**
```lean
-- ClaimStrength/Basic.lean:91-92
def KeyCorrect (E : List (Claim W)) (key : AnswerKey W) : Prop :=
  ∀ p ∈ key, Correct E p.1 p.2
```

**`andTable`**
```lean
-- ClaimStrength/Compound.lean:20-25
def andTable : Answer → Answer → List Answer
  | .contradicted, _ => [.contradicted]
  | .supported, b => [b]
  | .undetermined, .contradicted => [.contradicted]
  | .undetermined, .supported => [.undetermined]
  | .undetermined, .undetermined => [.undetermined, .contradicted]
```

**`orTable`**
```lean
-- ClaimStrength/Compound.lean:28-33
def orTable : Answer → Answer → List Answer
  | .supported, _ => [.supported]
  | .contradicted, b => [b]
  | .undetermined, .supported => [.supported]
  | .undetermined, .contradicted => [.undetermined]
  | .undetermined, .undetermined => [.undetermined, .supported]
```

**`negAnswer`**
```lean
-- ClaimStrength/Compound.lean:36-39
def negAnswer : Answer → Answer
  | .supported => .contradicted
  | .undetermined => .undetermined
  | .contradicted => .supported
```

**`Quant`**
```lean
-- ClaimStrength/Prefix.lean:20-23
inductive Quant
  | all
  | ex
  deriving DecidableEq, Repr
```

**`Binder`**
```lean
-- ClaimStrength/Prefix.lean:26-29
structure Binder (n : Nat) (K : Type) where
  q : Quant
  var : Fin n
  dom : K
```

**`Prefix`**
```lean
-- ClaimStrength/Prefix.lean:32
abbrev Prefix (n : Nat) := List (Binder n Unit)
```

**`upd`**
```lean
-- ClaimStrength/Prefix.lean:35-36
def upd {n : Nat} {α : Type} (ρ : Fin n → α) (x : Fin n) (a : α) : Fin n → α :=
  fun y => if y = x then a else ρ y
```

**`quantify`**
```lean
-- ClaimStrength/Prefix.lean:39-42
def quantify {α : Type} (q : Quant) (D : α → Prop) (P : α → Prop) : Prop :=
  match q with
  | .all => ∀ a, D a → P a
  | .ex => ∃ a, D a ∧ P a
```

**`evalR`**
```lean
-- ClaimStrength/Prefix.lean:49-51
def evalR (I : K → α → Prop) : List (Binder n K) → ((Fin n → α) → Prop) → (Fin n → α) → Prop
  | [], L, ρ => L ρ
  | b :: rest, L, ρ => quantify b.q (I b.dom) (fun a => evalR I rest L (upd ρ b.var a))
```

**`eval`**
```lean
-- ClaimStrength/Prefix.lean:54-55
def eval (φ : Prefix n) (R : (Fin n → α) → Prop) (ρ : Fin n → α) : Prop :=
  evalR (fun (_ : Unit) (_ : α) => True) φ R ρ
```

**`bvars`**
```lean
-- ClaimStrength/Prefix.lean:58
def bvars (φ : List (Binder n K)) : List (Fin n) := φ.map Binder.var
```

**`bOf`**
```lean
-- ClaimStrength/Prefix.lean:61-63
def bOf : List (Binder n K) → Fin n → Option (Binder n K)
  | [], _ => none
  | b :: rest, v => if b.var = v then some b else bOf rest v
```

**`qOf`**
```lean
-- ClaimStrength/Prefix.lean:66
def qOf (φ : List (Binder n K)) (v : Fin n) : Option Quant := (bOf φ v).map Binder.q
```

**`precL`**
```lean
-- ClaimStrength/Prefix.lean:70-72
def precL : List (Fin n) → Fin n → Fin n → Bool
  | [], _, _ => false
  | x :: rest, u, v => if x = u then rest.contains v else if x = v then false else precL rest u v
```

**`Precedes`**
```lean
-- ClaimStrength/Prefix.lean:75
def Precedes (φ : List (Binder n K)) (u v : Fin n) : Prop := precL (bvars φ) u v = true
```

**`WF`**
```lean
-- ClaimStrength/Prefix.lean:81
def WF (φ : List (Binder n K)) : Prop := (bvars φ).Nodup ∧ ∀ v : Fin n, v ∈ bvars φ
```

**`SEntailsAt`**
```lean
-- ClaimStrength/Prefix.lean:87-88
def SEntailsAt (α : Type) (φ ψ : Prefix n) : Prop :=
  ∀ (R : (Fin n → α) → Prop) (ρ : Fin n → α), eval φ R ρ → eval ψ R ρ
```

**`SEntails`**
```lean
-- ClaimStrength/Prefix.lean:92-93
def SEntails (φ ψ : Prefix n) : Prop :=
  ∀ α : Type, SEntailsAt α φ ψ
```

**`UnivReflected`**
```lean
-- ClaimStrength/Prefix.lean:96-97
def UnivReflected (φ ψ : List (Binder n K)) : Prop :=
  ∀ v, qOf ψ v = some .all → qOf φ v = some .all
```

**`SkolemOrderPreserved`**
```lean
-- ClaimStrength/Prefix.lean:102-104
def SkolemOrderPreserved (φ ψ : List (Binder n K)) : Prop :=
  ∀ u v, qOf φ v = some .ex → qOf φ u = some .all → qOf ψ u = some .all →
    Precedes φ u v → Precedes ψ u v
```

**`PrefixCrit`**
```lean
-- ClaimStrength/Prefix.lean:107
def PrefixCrit (φ ψ : List (Binder n K)) : Prop := UnivReflected φ ψ ∧ SkolemOrderPreserved φ ψ
```

**`prefixCritB`**
```lean
-- ClaimStrength/Prefix.lean:110-114
def prefixCritB (φ ψ : List (Binder n K)) : Bool :=
  (List.finRange n).all (fun v => !decide (qOf ψ v = some .all) || decide (qOf φ v = some .all)) &&
  (List.finRange n).all (fun u => (List.finRange n).all (fun v =>
    !(decide (qOf φ v = some .ex) && decide (qOf φ u = some .all) &&
      decide (qOf ψ u = some .all) && precL (bvars φ) u v) || precL (bvars ψ) u v))
```

**`wfB`**
```lean
-- ClaimStrength/Prefix.lean:117-118
def wfB (φ : List (Binder n K)) : Bool :=
  decide (bvars φ).Nodup && (List.finRange n).all (fun v => decide (v ∈ bvars φ))
```

**`Shape`**
```lean
-- ClaimStrength/Relativized.lean:23-25
structure Shape (n : Nat) (K P : Type) where
  pre : List (Binder n K)
  prem : P
```

**`Holds`**
```lean
-- ClaimStrength/Relativized.lean:35-37
def Holds (I : K → α → Prop) (J : P → (Fin n → α) → Prop) (s : Shape n K P)
    (M : (Fin n → α) → Prop) (ρ : Fin n → α) : Prop :=
  evalR I s.pre (fun σ => J s.prem σ → M σ) ρ
```

**`REntails`**
```lean
-- ClaimStrength/Relativized.lean:43-44
def REntails (I : K → α → Prop) (J : P → (Fin n → α) → Prop) (φ ψ : Shape n K P) : Prop :=
  ∀ (M : (Fin n → α) → Prop) (ρ : Fin n → α), Holds I J φ M ρ → Holds I J ψ M ρ
```

**`UnivDomainsContravariant`**
```lean
-- ClaimStrength/Relativized.lean:47-48
def UnivDomainsContravariant (incl : K → K → Bool) (φ ψ : List (Binder n K)) : Prop :=
  ∀ v b b', bOf φ v = some b → bOf ψ v = some b' → b'.q = .all → incl b'.dom b.dom = true
```

**`ExDomainsCovariant`**
```lean
-- ClaimStrength/Relativized.lean:51-52
def ExDomainsCovariant (incl : K → K → Bool) (φ ψ : List (Binder n K)) : Prop :=
  ∀ v b b', bOf φ v = some b → bOf ψ v = some b' → b.q = .ex → incl b.dom b'.dom = true
```

**`InstantiatedDomainsMeet`**
```lean
-- ClaimStrength/Relativized.lean:55-57
def InstantiatedDomainsMeet (meets : K → K → Bool) (φ ψ : List (Binder n K)) : Prop :=
  ∀ v b b', bOf φ v = some b → bOf ψ v = some b' → b.q = .all → b'.q = .ex →
    meets b.dom b'.dom = true
```

**`PremiseContravariant`**
```lean
-- ClaimStrength/Relativized.lean:60-61
def PremiseContravariant (impl : P → P → Bool) (φ ψ : Shape n K P) : Prop :=
  impl ψ.prem φ.prem = true
```

**`RCrit`**
```lean
-- ClaimStrength/Relativized.lean:64-67
def RCrit (incl meets : K → K → Bool) (impl : P → P → Bool) (φ ψ : Shape n K P) : Prop :=
  PrefixCrit φ.pre ψ.pre ∧ UnivDomainsContravariant incl φ.pre ψ.pre ∧
  ExDomainsCovariant incl φ.pre ψ.pre ∧ InstantiatedDomainsMeet meets φ.pre ψ.pre ∧
  PremiseContravariant impl φ ψ
```

**`InclSound`**
```lean
-- ClaimStrength/Relativized.lean:70-71
def InclSound (I : K → α → Prop) (incl : K → K → Bool) : Prop :=
  ∀ k k', incl k k' = true → ∀ a, I k a → I k' a
```

**`MeetsSound`**
```lean
-- ClaimStrength/Relativized.lean:74-75
def MeetsSound (I : K → α → Prop) (meets : K → K → Bool) : Prop :=
  ∀ k k', meets k k' = true → ∃ a, I k a ∧ I k' a
```

**`ImplSound`**
```lean
-- ClaimStrength/Relativized.lean:78-79
def ImplSound (J : P → (Fin n → α) → Prop) (impl : P → P → Bool) : Prop :=
  ∀ p p', impl p p' = true → ∀ σ, J p σ → J p' σ
```

**`InclExact`**
```lean
-- ClaimStrength/Relativized.lean:82-83
def InclExact (I : K → α → Prop) (incl : K → K → Bool) : Prop :=
  ∀ k k', incl k k' = true ↔ ∀ a, I k a → I k' a
```

**`MeetsExact`**
```lean
-- ClaimStrength/Relativized.lean:86-87
def MeetsExact (I : K → α → Prop) (meets : K → K → Bool) : Prop :=
  ∀ k k', meets k k' = true ↔ ∃ a, I k a ∧ I k' a
```

**`ImplExact`**
```lean
-- ClaimStrength/Relativized.lean:90-91
def ImplExact (J : P → (Fin n → α) → Prop) (impl : P → P → Bool) : Prop :=
  ∀ p p', impl p p' = true ↔ ∀ σ, J p σ → J p' σ
```

**`TwoPoint`**
```lean
-- ClaimStrength/Relativized.lean:94
def TwoPoint (D : α → Prop) : Prop := ∃ a b, a ≠ b ∧ D a ∧ D b
```

**`ShapeNF`**
```lean
-- ClaimStrength/RelResults.lean:198-199
def ShapeNF (meets : K → K → Bool) (s : Shape n K P) : Prop :=
  WF s.pre ∧ ∀ b ∈ s.pre, meets b.dom b.dom = true
```

**`Cls`**
```lean
-- ClaimStrength/RelResults.lean:82-87
inductive Cls
  | empty
  | zero
  | zeroOne
  | all
  deriving DecidableEq, Repr
```

**`clsI`**
```lean
-- ClaimStrength/RelResults.lean:90-94
def clsI : Cls → Nat → Prop
  | .empty, _ => False
  | .zero, a => a = 0
  | .zeroOne, a => a ≤ 1
  | .all, _ => True
```

**`clsIncl`**
```lean
-- ClaimStrength/RelResults.lean:97-105
def clsIncl : Cls → Cls → Bool
  | .empty, _ => true
  | .zero, .zero => true
  | .zero, .zeroOne => true
  | .zero, .all => true
  | .zeroOne, .zeroOne => true
  | .zeroOne, .all => true
  | .all, .all => true
  | _, _ => false
```

**`clsMeets`**
```lean
-- ClaimStrength/RelResults.lean:108-111
def clsMeets : Cls → Cls → Bool
  | .empty, _ => false
  | _, .empty => false
  | _, _ => true
```

**`Prem`**
```lean
-- ClaimStrength/RelResults.lean:114-118
inductive Prem
  | top
  | bot
  | atMostOne
  deriving DecidableEq, Repr
```

**`premJ`**
```lean
-- ClaimStrength/RelResults.lean:121-124
def premJ (m : Nat) : Prem → (Fin (m + 1) → Nat) → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atMostOne, σ => ∀ v, σ v ≤ 1
```

**`premImpl`**
```lean
-- ClaimStrength/RelResults.lean:127-131
def premImpl : Prem → Prem → Bool
  | .bot, _ => true
  | _, .top => true
  | .atMostOne, .atMostOne => true
  | _, _ => false
```

**`Checker`**
```lean
-- ClaimStrength/Drift.lean:188-190
structure Checker where
  accept : Nat → Bool
  good : Nat → Prop
```

**`CheckerSound`**
```lean
-- ClaimStrength/Drift.lean:193
def CheckerSound (c : Checker) : Prop := ∀ p, c.accept p = true → c.good p
```

**`CheckerComplete`**
```lean
-- ClaimStrength/Drift.lean:196
def CheckerComplete (c : Checker) : Prop := ∀ p, c.good p → c.accept p = true
```

**`Frontier`**
```lean
-- ClaimStrength/Frontier.lean:19-20
def Frontier (E Q : List (Claim W)) (q : Claim W) : Prop :=
  q ∈ Q ∧ ¬ Supported E q ∧ ∀ q' ∈ Q, ¬ Supported E q' → Entails q q' → Entails q' q
```

**`ClosedUnderEntailmentIn`**
```lean
-- ClaimStrength/Frontier.lean:23-24
def ClosedUnderEntailmentIn (Q : List (Claim W)) (End : Claim W → Prop) : Prop :=
  ∀ q ∈ Q, ∀ q' ∈ Q, End q → Entails q q' → End q'
```

**`BB`**
```lean
-- ClaimStrength/Compound.lean:122
abbrev BB := Bool × Bool
```

**`canon`**
```lean
-- ClaimStrength/Compound.lean:137-140
def canon : Answer → BB → Bool
  | .supported => fun _ => true
  | .contradicted => fun _ => false
  | .undetermined => fun w => w.1
```

**`acceptAll`**
```lean
-- ClaimStrength/Drift.lean:202
def acceptAll : Checker := ⟨fun _ => true, fun _ => False⟩
```

**`evenChecker`**
```lean
-- ClaimStrength/Drift.lean:205
def evenChecker : Checker := ⟨fun n => decide (n % 2 = 0), fun n => n % 2 = 0⟩
```

**`zeroChecker`**
```lean
-- ClaimStrength/Drift.lean:208
def zeroChecker : Checker := ⟨fun n => decide (n = 0), fun n => n % 2 = 0⟩
```

**`qStrong`**
```lean
-- ClaimStrength/Frontier.lean:77
def qStrong : Claim Nat := fun n => n = 1
```

**`qWeak`**
```lean
-- ClaimStrength/Frontier.lean:79
def qWeak : Claim Nat := fun n => n ≠ 0
```

**`qTriv`**
```lean
-- ClaimStrength/Frontier.lean:81
def qTriv : Claim Nat := fun _ => True
```

**`candidates`**
```lean
-- ClaimStrength/Frontier.lean:83
def candidates : List (Claim Nat) := [qStrong, qWeak, qTriv]
```

**`A`**
```lean
-- ClaimStrength/Prefix.lean:121
def A (x : Fin n) : Binder n Unit := ⟨.all, x, ()⟩
```

**`X`**
```lean
-- ClaimStrength/Prefix.lean:123
def X (x : Fin n) : Binder n Unit := ⟨.ex, x, ()⟩
```

**`pairAllB`**
```lean
-- ClaimStrength/RelResults.lean:19-23
def pairAllB (c : Binder n K → Binder n K → Bool) (φ ψ : List (Binder n K)) : Bool :=
  (List.finRange n).all fun v =>
    match bOf φ v, bOf ψ v with
    | some b, some b' => c b b'
    | _, _ => true
```

**`rcritB`**
```lean
-- ClaimStrength/RelResults.lean:65-71
def rcritB (incl meets : K → K → Bool) (impl : P → P → Bool) (φ ψ : Shape n K P) : Bool :=
  prefixCritB φ.pre ψ.pre &&
  pairAllB (fun b b' => !decide (b'.q = .all) || incl b'.dom b.dom) φ.pre ψ.pre &&
  pairAllB (fun b b' => !decide (b.q = .ex) || incl b.dom b'.dom) φ.pre ψ.pre &&
  pairAllB (fun b b' => !(decide (b.q = .all) && decide (b'.q = .ex)) || meets b.dom b'.dom)
    φ.pre ψ.pre &&
  impl ψ.prem φ.prem
```

**`nvφ`**
```lean
-- ClaimStrength/RelResults.lean:377
def nvφ : Shape 2 Cls Prem := ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .all⟩], .top⟩
```

**`nvψ`**
```lean
-- ClaimStrength/RelResults.lean:379
def nvψ : Shape 2 Cls Prem := ⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .zeroOne⟩], .atMostOne⟩
```

**`nvφD`**
```lean
-- ClaimStrength/RelResults.lean:381
def nvφD : Shape 2 Cls Prem := ⟨[⟨.ex, 1, .zero⟩, ⟨.all, 0, .all⟩], .top⟩
```

**`nvψD`**
```lean
-- ClaimStrength/RelResults.lean:384
def nvψD : Shape 2 Cls Prem := ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩], .top⟩
```

**`nvψTop`**
```lean
-- ClaimStrength/RelResults.lean:386
def nvψTop : Shape 2 Cls Prem := ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .all⟩], .top⟩
```

**`emptyI`**
```lean
-- ClaimStrength/RelResults.lean:803
def emptyI : Unit → Empty → Prop := fun _ _ => True
```

**`emptyJ`**
```lean
-- ClaimStrength/RelResults.lean:805
def emptyJ : Unit → (Fin 1 → Empty) → Prop := fun _ _ => True
```

**`emptyφ`**
```lean
-- ClaimStrength/RelResults.lean:807
def emptyφ : Shape 1 Unit Unit := ⟨[⟨.all, 0, ()⟩], ()⟩
```

**`emptyψ`**
```lean
-- ClaimStrength/RelResults.lean:809
def emptyψ : Shape 1 Unit Unit := ⟨[⟨.ex, 0, ()⟩], ()⟩
```

## Findings

Each card gives the tier, kind and depth; the plain claim; the Lean statements, quoted verbatim up to the top-level `:=` (proofs omitted; definitions are quoted under **Applicability**); for the cards whose statements are phrased with defined predicates, an unfolded rendering of the headline theorem, which is a Lean term definitionally equal to the quoted statement; the hypothesis ledger; the non-vacuity witness; the positive control for the impossibility result; prior art; and the design question it informs. In a ledger, a hypothesis is *tight* when a proved theorem states that every other hypothesis of the named theorem holds and its conclusion fails; the ledger records the class in which that witness lies. Tightness is a statement about that witness, not a claim that the hypothesis is necessary in every setting. The statements of all counterexamples, non-vacuity witnesses and positive controls are quoted at the end of this section. Non-claims are under **Boundaries**.

### 1. `three-answers-exactly-one-iff-satisfiable`

Tier T0 · kind: characterization · depth: definitional · reference point

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** For every report E and claim q: exactly one of Supported E q, Contradicted E q, Undetermined E q holds if and only if E is satisfiable. If E is unsatisfiable, then q is both supported and contradicted. If E is satisfiable and both a and b are correct answers about q, then a = b. Some answer is always correct. For every E, q, a: a is incorrect iff a is a positive over-reading (answering supported for an unsupported claim), a negative over-reading (answering contradicted for a claim that is not contradicted), or an under-reading (answering undetermined for a claim that is supported or contradicted).

**Tier.** Textbook classification of a sentence relative to a theory (entailed, refuted, independent) restated for reports; the same three labels are used by natural-language-inference and fact-verification datasets.

**Lean statements.**

**`exactlyOne_answer_iff_satisfiable`**
```lean
-- ClaimStrength/Basic.lean:243-244
theorem exactlyOne_answer_iff_satisfiable (E : List (Claim W)) (q : Claim W) :
    ExactlyOne3 (Supported E q) (Contradicted E q) (Undetermined E q) ↔ Satisfiable E
```

**`unsatisfiable_supported_and_contradicted`**
```lean
-- ClaimStrength/Basic.lean:224-225
theorem unsatisfiable_supported_and_contradicted {E : List (Claim W)}
    (hE : ¬ Satisfiable E) (q : Claim W) : Supported E q ∧ Contradicted E q
```

**`correct_unique_of_satisfiable`**
```lean
-- ClaimStrength/Basic.lean:264-265
theorem correct_unique_of_satisfiable {E : List (Claim W)} (hE : Satisfiable E) {q : Claim W}
    {a b : Answer} (ha : Correct E q a) (hb : Correct E q b) : a = b
```

**`exists_correct`**
```lean
-- ClaimStrength/Basic.lean:315
theorem exists_correct (E : List (Claim W)) (q : Claim W) : ∃ a, Correct E q a
```

**`incorrect_iff_reading_error`**
```lean
-- ClaimStrength/Basic.lean:325-327
theorem incorrect_iff_reading_error (E : List (Claim W)) (q : Claim W) (a : Answer) :
    ¬ Correct E q a ↔
      PositiveOverReading E q a ∨ NegativeOverReading E q a ∨ UnderReading E q a
```

Unfolded statement of `unsatisfiable_supported_and_contradicted` (Satisfiable, Models, Supported and Contradicted written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {W : Type} {E : List (Claim W)}, ¬ (∃ w, ∀ e ∈ E, e w) → ∀ (q : Claim W),
  (∀ w, (∀ e ∈ E, e w) → q w) ∧ (∀ w, (∀ e ∈ E, e w) → ¬ q w)
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hE : ¬ Satisfiable E (in unsatisfiable_supported_and_contradicted) | with a satisfiable report the conclusion fails: the empty report does not contradict True | tight: `unsatisfiable_hE_tight` | the empty report over Nat |
| hE : Satisfiable E (in correct_unique_of_satisfiable) | over an unsatisfiable report both supported and contradicted are correct, so two different answers are correct | tight: `correct_unique_hE_tight` | the unsatisfiable one-claim report [False] over Nat |
| ha : Correct E q a (in correct_unique_of_satisfiable) | an incorrect answer a can differ from a correct answer b | tight: `correct_unique_ha_tight` | a satisfiable one-claim report over Nat ([n ≤ 1], q = (n = 0), a = supported, b = undetermined) |
| hb : Correct E q b (in correct_unique_of_satisfiable) | an incorrect answer b can differ from a correct answer a | tight: `correct_unique_hb_tight` | a satisfiable one-claim report over Nat ([n ≤ 1], q = (n = 0), a = undetermined, b = supported) |

**Non-vacuity.** E = [n ≤ 1] over Nat, q = (n = 0): satisfiable, and the unique correct answer is undetermined; [False] over Nat is unsatisfiable. (`exactlyOne_nonvacuous`, `unsatisfiable_nonvacuous`, `correct_unique_nonvacuous`)

**Prior art.**

- H. B. Enderton, A Mathematical Introduction to Logic, 2nd ed., Harcourt/Academic Press, 2001, Chapter 2 (satisfiability and logical consequence); the classification is the textbook one. Chapter-level reference; section numbers not checked against a copy.
- S. R. Bowman, G. Angeli, C. Potts, C. D. Manning, "A large annotated corpus for learning natural language inference", Proceedings of EMNLP 2015, pp. 632-642, doi:10.18653/v1/D15-1075 (three labels entailment / contradiction / neutral for premise-hypothesis pairs; the same trichotomy as supported / contradicted / undetermined).
- J. Thorne, A. Vlachos, C. Christodoulopoulos, A. Mittal, "FEVER: a large-scale dataset for Fact Extraction and VERification", Proceedings of NAACL-HLT 2018, pp. 809-819, doi:10.18653/v1/N18-1074 (labels SUPPORTED / REFUTED / NOT ENOUGH INFO for claims against evidence).

**Design question.** Reference point: a definitional fact recorded so that other cards can cite it. How should the correct answer to a comprehension question about a report be defined, and which answers are well defined?

**Non-claims.** Listed under **Boundaries → Non-claims → 1**.

### 2. `answers-monotone-under-satisfiable-report-extension`

Tier T0 · kind: theorem · depth: shallow · reference point

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** If every claim of E is in E', then a claim supported by E is supported by E' and a claim contradicted by E is contradicted by E'. If every claim of E is in E' and E' is satisfiable, then, whenever a correct answer about q for E differs from a correct answer about q for E', the E-answer is undetermined.

**Tier.** Monotonicity of classical consequence, specialized to the three answers.

**Lean statements.**

**`supported_mono`**
```lean
-- ClaimStrength/Basic.lean:344-345
theorem supported_mono {E E' : List (Claim W)} (hsub : ∀ e ∈ E, e ∈ E') {q : Claim W}
    (h : Supported E q) : Supported E' q
```

**`contradicted_mono`**
```lean
-- ClaimStrength/Basic.lean:350-351
theorem contradicted_mono {E E' : List (Claim W)} (hsub : ∀ e ∈ E, e ∈ E') {q : Claim W}
    (h : Contradicted E q) : Contradicted E' q
```

**`answer_changes_only_from_undetermined_of_satisfiable`**
```lean
-- ClaimStrength/Basic.lean:399-401
theorem answer_changes_only_from_undetermined_of_satisfiable {E E' : List (Claim W)}
    (hsub : ∀ e ∈ E, e ∈ E') (hsat : Satisfiable E') {q : Claim W} {a a' : Answer}
    (ha : Correct E q a) (ha' : Correct E' q a') : a' = a ∨ a = .undetermined
```

Unfolded statement of `supported_mono` (Supported and Models written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {W : Type} {E E' : List (Claim W)}, (∀ e ∈ E, e ∈ E') → ∀ {q : Claim W},
  (∀ w, (∀ e ∈ E, e w) → q w) → ∀ w, (∀ e ∈ E', e w) → q w
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hsub : ∀ e ∈ E, e ∈ E' (in supported_mono) | if E' drops a claim of E, a claim supported by E can be unsupported by E' | tight: `supported_mono_hsub_tight` | one-claim versus empty report over Nat |
| h : Supported E q (in supported_mono) | a claim that E does not support need not be supported by E' | tight: `supported_mono_h_tight` | the empty report extended to [n ≤ 1] over Nat, q = (n = 0) |
| hsub : ∀ e ∈ E, e ∈ E' (in contradicted_mono) | if E' drops a claim of E, a claim contradicted by E can be not contradicted by E' | tight: `contradicted_mono_hsub_tight` | one-claim versus empty report over Nat |
| h : Contradicted E q (in contradicted_mono) | a claim that E does not contradict need not be contradicted by E' | tight: `contradicted_mono_h_tight` | the empty report extended to [n ≤ 1] over Nat, q = (n = 0) |
| hsub : ∀ e ∈ E, e ∈ E' (in answer_changes_only_from_undetermined_of_satisfiable) | if E' drops a claim of E, a supported answer can change to undetermined | tight: `answer_changes_hsub_tight` | one-claim versus empty report over Nat |
| hsat : Satisfiable E' (in answer_changes_only_from_undetermined_of_satisfiable; supported_mono and contradicted_mono have no such hypothesis) | over an unsatisfiable extension a supported claim also becomes contradicted, so the answer contradicted is correct for E' | tight: `answer_changes_hsat_tight` | extending the empty report over Nat by False |
| ha : Correct E q a (in answer_changes_only_from_undetermined_of_satisfiable) | with an incorrect E-answer a (here contradicted) the conclusion fails | tight: `answer_changes_ha_tight` | the empty report extended to [n = 0] over Nat, q = (n = 0) |
| ha' : Correct E' q a' (in answer_changes_only_from_undetermined_of_satisfiable) | with an incorrect E'-answer a' (here contradicted) the conclusion fails | tight: `answer_changes_ha'_tight` | the empty report extended to [n = 0] over Nat, q = True |

**Non-vacuity.** [] ⊆ [n = 0] over Nat: n = 0 moves from undetermined to supported (all hypotheses of answer_changes_only_from_undetermined_of_satisfiable hold); [n = 0] ⊆ [n = 0, n ≤ 5] with n ≤ 1 supported and n = 1 contradicted by the smaller report (all hypotheses of supported_mono and contradicted_mono hold). (`answer_changes_nonvacuous`, `mono_nonvacuous`)

**Prior art.**

- H. B. Enderton, A Mathematical Introduction to Logic, 2nd ed., Harcourt/Academic Press, 2001, Chapter 2 (monotonicity of logical consequence: adding hypotheses preserves consequences). Chapter-level reference.

**Design question.** Reference point: a definitional fact recorded so that other cards can cite it. How should the correct answer to a comprehension question about a report be defined, and which answers are well defined?

**Non-claims.** Listed under **Boundaries → Non-claims → 2**.

### 3. `undetermined-iff-witnesses-both-ways`

Tier T0 · kind: characterization · depth: definitional · reference point

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** Undetermined E q holds if and only if some interpretation consistent with E satisfies q and some interpretation consistent with E falsifies q; Contradicted E q is the same as Supported E (¬q); if c ∈ E and c entails ¬q (for example, an exhibited counterexample to a universal claim q), then q is contradicted; and over Nat the satisfiable report [n ≤ 1, 1 ≤ n] contradicts n = 0 ∨ n = 2 although neither of its claims alone entails the negation.

**Tier.** Independence of a sentence from a theory restated for reports.

**Lean statements.**

**`undetermined_iff_exists_both`**
```lean
-- ClaimStrength/Basic.lean:479-480
theorem undetermined_iff_exists_both (E : List (Claim W)) (q : Claim W) :
    Undetermined E q ↔ (∃ w, Models E w ∧ q w) ∧ (∃ w, Models E w ∧ ¬ q w)
```

**`contradicted_iff_supported_not`**
```lean
-- ClaimStrength/Basic.lean:492-493
theorem contradicted_iff_supported_not (E : List (Claim W)) (q : Claim W) :
    Contradicted E q ↔ Supported E (fun w => ¬ q w)
```

**`contradicted_of_mem_entails_not`**
```lean
-- ClaimStrength/Basic.lean:497-498
theorem contradicted_of_mem_entails_not {E : List (Claim W)} {q c : Claim W} (hc : c ∈ E)
    (hneg : Entails c (fun w => ¬ q w)) : Contradicted E q
```

**`contradicted_jointly_without_single_claim`**
```lean
-- ClaimStrength/Basic.lean:530-534
theorem contradicted_jointly_without_single_claim :
    Satisfiable [fun n : Nat => n ≤ 1, fun n => 1 ≤ n] ∧
    Contradicted [fun n : Nat => n ≤ 1, fun n => 1 ≤ n] (fun n => n = 0 ∨ n = 2) ∧
    ∀ c ∈ [fun n : Nat => n ≤ 1, fun n => 1 ≤ n],
      ¬ Entails c (fun n => ¬ (n = 0 ∨ n = 2))
```

Unfolded statement of `contradicted_of_mem_entails_not` (Entails, Contradicted and Models written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {W : Type} {E : List (Claim W)} {q c : Claim W}, c ∈ E →
  (∀ w, c w → ¬ q w) → ∀ w, (∀ e ∈ E, e w) → ¬ q w
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hc : c ∈ E (in contradicted_of_mem_entails_not) | a claim entailing ¬q that is not established by the report does not contradict q | tight: `contradicted_of_mem_hc_tight` | the empty report over interpretations Nat → Prop |
| hneg : Entails c (fun w => ¬ q w) (in contradicted_of_mem_entails_not) | an established claim that does not rule out q need not contradict q | tight: `contradicted_of_mem_hneg_tight` | a one-claim report over interpretations Nat → Prop |

**Non-vacuity.** Worlds are predicates P on Nat; E = [¬ P 0] contradicts q = (∀ m, P m). (`contradicted_of_mem_nonvacuous`, `undetermined_example_pos`)

**Prior art.**

- H. B. Enderton, A Mathematical Introduction to Logic, 2nd ed., Harcourt/Academic Press, 2001, Chapter 2 (a sentence is independent of a set of sentences when neither it nor its negation is a consequence). Chapter-level reference.

**Design question.** Reference point: a definitional fact recorded so that other cards can cite it. How should the correct answer to a comprehension question about a report be defined, and which answers are well defined?

**Non-claims.** Listed under **Boundaries → Non-claims → 3**.

### 4. `unsupported-does-not-imply-contradicted`

Tier T0 · kind: counterexample · depth: definitional · reference point

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** Over the interpretations Bool, it is not the case that for every report E and claim q, 'unsupported' (¬ Supported E q) implies 'contradicted': the empty report leaves q = (b = true) unsupported and not contradicted (unsupported_not_imply_contradicted_witness). With the predicates P on Nat as the interpretations, the universal claim 'every m satisfies P' is undetermined by the empty report and contradicted once the claim '¬ P 0' is added. Conversely, if q is contradicted by E and E is satisfiable, then q is unsupported.

**Tier.** Textbook distinction between 'not proved' and 'disproved', stated as a kernel-checked non-entailment with its valid converse.

**Lean statements.**

**`unsupported_not_imply_contradicted`**
```lean
-- ClaimStrength/Basic.lean:548-549
theorem unsupported_not_imply_contradicted :
    ¬ (∀ (E : List (Claim Bool)) (q : Claim Bool), ¬ Supported E q → Contradicted E q)
```

**`unsupported_not_imply_contradicted_witness`**
```lean
-- ClaimStrength/Witnesses.lean:17-19
theorem unsupported_not_imply_contradicted_witness :
    ¬ Supported ([] : List (Claim Bool)) (fun b => b = true) ∧
    ¬ Contradicted ([] : List (Claim Bool)) (fun b => b = true)
```

**`universal_undetermined_until_counterexample`**
```lean
-- ClaimStrength/Basic.lean:559-561
theorem universal_undetermined_until_counterexample :
    Undetermined ([] : List (Claim (Nat → Prop))) (fun P => ∀ m, P m) ∧
    Contradicted [fun P : Nat → Prop => ¬ P 0] (fun P => ∀ m, P m)
```

**`unsupported_of_contradicted_of_satisfiable`**
```lean
-- ClaimStrength/Drift.lean:259-260
theorem unsupported_of_contradicted_of_satisfiable {E : List (Claim W)} {q : Claim W}
    (hc : Contradicted E q) (hE : Satisfiable E) : ¬ Supported E q
```

Unfolded statement of `unsupported_of_contradicted_of_satisfiable` (Contradicted, Satisfiable, Supported and Models written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {W : Type} {E : List (Claim W)} {q : Claim W},
  (∀ w, (∀ e ∈ E, e w) → ¬ q w) → (∃ w, ∀ e ∈ E, e w) → ¬ ∀ w, (∀ e ∈ E, e w) → q w
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hc : Contradicted E q (in unsupported_of_contradicted_of_satisfiable) | a claim that is not contradicted can be supported | tight: `unsupported_of_contradicted_hc_tight` | the empty report over Nat, q = True |
| hE : Satisfiable E (in unsupported_of_contradicted_of_satisfiable) | an unsatisfiable report contradicts and supports every claim | tight: `unsupported_of_contradicted_hE_tight` | the unsatisfiable one-claim report [False] over Nat |

**Non-vacuity.** E = [n = 0] over Nat contradicts q = (n = 1) and is satisfiable. (`unsupported_of_contradicted_nonvacuous`)

**Prior art.**

- H. P. Grice, "Logic and Conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics, Vol. 3: Speech Acts, Academic Press, New York, 1975, pp. 41-58 (first maxim of Quantity: a speaker who could have asserted q and did not may be taken to implicate that q does not hold; this motivates reading 'q is not established' as 'q is false'). Cited for the prose motivation of this drift; no formal statement is taken from it.
- J. Thorne, A. Vlachos, C. Christodoulopoulos, A. Mittal, "FEVER: a large-scale dataset for Fact Extraction and VERification", Proceedings of NAACL-HLT 2018, pp. 809-819, doi:10.18653/v1/N18-1074 (the label NOT ENOUGH INFO is distinct from REFUTED).

**Design question.** Which recurring summary drifts turn a proved claim into a strictly stronger unproved one, and what is the weaker reading that does follow? Reference point: a definitional fact recorded so that other cards can cite it.

**Non-claims.** Listed under **Boundaries → Non-claims → 4**.

### 5. `meta-level-questions-are-never-undetermined`

Tier T1 · kind: impossibility · depth: shallow

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** For every report E and every world-independent claim q (its truth does not depend on the interpretation), Undetermined E q is false, with no satisfiability assumption. The meta-level question 'E establishes q' (the constant claim Supported E q) is world-independent; if q is unsupported by E, it is contradicted. For every E and q, the one-entry answer key [(Establishes E q, undetermined)], which marks 'E establishes q' as undetermined, is incorrect; since KeyCorrect requires every entry of a key to be correct, every answer key containing that entry is incorrect as well (immediate from the definition of KeyCorrect, not stated as a separate theorem). If Undetermined E q, the answer key that marks 'E establishes q' as contradicted and q as undetermined is correct.

**Tier.** Folklore distinction between object-level and meta-level questions, made precise for answer keys.

**Lean statements.**

**`worldIndependent_not_undetermined`**
```lean
-- ClaimStrength/Basic.lean:572-573
theorem worldIndependent_not_undetermined (E : List (Claim W)) {q : Claim W}
    (hq : WorldIndependent q) : ¬ Undetermined E q
```

**`establishes_worldIndependent`**
```lean
-- ClaimStrength/Basic.lean:582-583
theorem establishes_worldIndependent (E : List (Claim W)) (q : Claim W) :
    WorldIndependent (Establishes E q)
```

**`establishes_contradicted_of_unsupported`**
```lean
-- ClaimStrength/Basic.lean:587-588
theorem establishes_contradicted_of_unsupported {E : List (Claim W)} {q : Claim W}
    (h : ¬ Supported E q) : Contradicted E (Establishes E q)
```

**`establishes_undetermined_key_never_correct`**
```lean
-- ClaimStrength/Basic.lean:605-606
theorem establishes_undetermined_key_never_correct (E : List (Claim W)) (q : Claim W) :
    ¬ KeyCorrect E [(Establishes E q, .undetermined)]
```

**`establishes_answer_key`**
```lean
-- ClaimStrength/Basic.lean:613-614
theorem establishes_answer_key {E : List (Claim W)} {q : Claim W} (h : Undetermined E q) :
    KeyCorrect E [(Establishes E q, .contradicted), (q, .undetermined)]
```

Unfolded statement of `worldIndependent_not_undetermined` (WorldIndependent, Undetermined, Supported, Contradicted and Models written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {W : Type} (E : List (Claim W)) {q : Claim W}, (∀ w w', q w → q w') →
  ¬ (¬ (∀ w, (∀ e ∈ E, e w) → q w) ∧ ¬ (∀ w, (∀ e ∈ E, e w) → ¬ q w))
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hq : WorldIndependent q (in worldIndependent_not_undetermined) | a claim whose truth depends on the interpretation can be undetermined | tight: `worldIndependent_tight` | the empty report over Bool, q = (b = true) |
| h : ¬ Supported E q (in establishes_contradicted_of_unsupported) | if E supports q, the meta-level question 'E establishes q' is true, hence not contradicted | tight: `establishes_contradicted_h_tight` | the empty report over Nat, q = True |
| h : Undetermined E q (in establishes_answer_key) | if q is supported, the key entry 'E establishes q: contradicted' is incorrect | tight: `establishes_answer_key_tight` | the empty report over Nat, q = True |

**Non-vacuity.** E = [n ≤ 1] over Nat leaves q = (n = 0) undetermined; the meta-level question is contradicted. (`establishes_answer_key_nonvacuous`, `establishes_contradicted_nonvacuous`)

**Positive control.** The object-level, world-dependent claim b = true over Bool is undetermined by the empty report. (`worldIndependent_tight`)

**Prior art.**

- No specific prior statement located; elementary consequence of the definitions.
- J. Thorne, A. Vlachos, C. Christodoulopoulos, A. Mittal, "FEVER: a large-scale dataset for Fact Extraction and VERification", Proceedings of NAACL-HLT 2018, pp. 809-819, doi:10.18653/v1/N18-1074 (fact-verification labels apply to object-level claims checked against evidence).

**Design question.** Which question forms make the correct answer ill-defined, and how should an answer key treat questions about the report itself?

**Non-claims.** Listed under **Boundaries → Non-claims → 5**.

### 6. `compound-answer-tables-over-satisfiable-reports`

Tier T0 · kind: characterization · depth: shallow · reference point

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** If E is satisfiable, q₁ has correct answer a₁, and q₂ has correct answer a₂, then the correct answer for q₁ ∧ q₂ lies in andTable a₁ a₂ and that for q₁ ∨ q₂ lies in orTable a₁ a₂: for ∧, contradicted if either conjunct is contradicted, the other conjunct's answer if one is supported, and undetermined or contradicted when both are undetermined; dually for ∨. Every answer listed in every cell occurs for some pair of claims over four interpretations (Bool × Bool) with the empty report; in the cell (undetermined, undetermined) both answers occur with distinct component claims. For every report, if a is a correct answer for q then negAnswer a (swapping supported and contradicted, keeping undetermined) is a correct answer for ¬q. For every element w₀ : W, if every interpretation consistent with E equals w₀ (so E has at most one consistent interpretation; E may also be unsatisfiable), then no claim is undetermined by E.

**Tier.** Re-derivation of the supervaluation pattern (van Fraassen 1966; Fine 1975) for the three answers.

**Lean statements.**

**`and_answer_mem_andTable_of_satisfiable`**
```lean
-- ClaimStrength/Compound.lean:58-61
theorem and_answer_mem_andTable_of_satisfiable {E : List (Claim W)} (hE : Satisfiable E)
    {q₁ q₂ : Claim W} {a₁ a₂ a : Answer}
    (h₁ : Correct E q₁ a₁) (h₂ : Correct E q₂ a₂)
    (h : Correct E (fun w => q₁ w ∧ q₂ w) a) : a ∈ andTable a₁ a₂
```

**`andTable_realizable`**
```lean
-- ClaimStrength/Compound.lean:152-154
theorem andTable_realizable (a₁ a₂ : Answer) :
    ∀ a ∈ andTable a₁ a₂, ∃ q₁ q₂ : Claim BB,
      Correct [] q₁ a₁ ∧ Correct [] q₂ a₂ ∧ Correct [] (fun w => q₁ w ∧ q₂ w) a
```

**`andTable_undetermined_cell_distinct`**
```lean
-- ClaimStrength/Compound.lean:249-256
theorem andTable_undetermined_cell_distinct :
    (fun w : BB => w.1 = true) ≠ (fun w => w.2 = true) ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => w.2 = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∧ w.2 = true) .undetermined ∧
    (fun w : BB => w.1 = true) ≠ (fun w => (!w.1) = true) ∧
    Correct ([] : List (Claim BB)) (fun w => (!w.1) = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∧ (!w.1) = true) .contradicted
```

**`or_answer_mem_orTable_of_satisfiable`**
```lean
-- ClaimStrength/Compound.lean:84-87
theorem or_answer_mem_orTable_of_satisfiable {E : List (Claim W)} (hE : Satisfiable E)
    {q₁ q₂ : Claim W} {a₁ a₂ a : Answer}
    (h₁ : Correct E q₁ a₁) (h₂ : Correct E q₂ a₂)
    (h : Correct E (fun w => q₁ w ∨ q₂ w) a) : a ∈ orTable a₁ a₂
```

**`orTable_realizable`**
```lean
-- ClaimStrength/Compound.lean:174-176
theorem orTable_realizable (a₁ a₂ : Answer) :
    ∀ a ∈ orTable a₁ a₂, ∃ q₁ q₂ : Claim BB,
      Correct [] q₁ a₁ ∧ Correct [] q₂ a₂ ∧ Correct [] (fun w => q₁ w ∨ q₂ w) a
```

**`orTable_undetermined_cell_distinct`**
```lean
-- ClaimStrength/Compound.lean:271-275
theorem orTable_undetermined_cell_distinct :
    (fun w : BB => w.1 = true) ≠ (fun w => w.2 = true) ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∨ w.2 = true) .undetermined ∧
    (fun w : BB => w.1 = true) ≠ (fun w => (!w.1) = true) ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∨ (!w.1) = true) .supported
```

**`neg_answer_correct`**
```lean
-- ClaimStrength/Compound.lean:111-112
theorem neg_answer_correct {E : List (Claim W)} {q : Claim W} {a : Answer}
    (h : Correct E q a) : Correct E (fun w => ¬ q w) (negAnswer a)
```

**`not_undetermined_of_unique_model`**
```lean
-- ClaimStrength/Compound.lean:286-287
theorem not_undetermined_of_unique_model {E : List (Claim W)} {w₀ : W}
    (hu : ∀ w, Models E w → w = w₀) (q : Claim W) : ¬ Undetermined E q
```

Unfolded statement of `not_undetermined_of_unique_model` (Models, Undetermined, Supported and Contradicted written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {W : Type} {E : List (Claim W)} {w₀ : W}, (∀ w, (∀ e ∈ E, e w) → w = w₀) →
  ∀ (q : Claim W), ¬ (¬ (∀ w, (∀ e ∈ E, e w) → q w) ∧ ¬ (∀ w, (∀ e ∈ E, e w) → ¬ q w))
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hE : Satisfiable E (in and_answer_mem_andTable_of_satisfiable) | over an unsatisfiable report two answers are correct for each claim, and some combinations fall outside the table | tight: `and_answer_hE_tight` | the unsatisfiable one-claim report [False] over Nat |
| h₁ : Correct E q₁ a₁ (in and_answer_mem_andTable_of_satisfiable) | with an incorrect component answer a₁ the compound answer can lie outside the cell | tight: `and_answer_h₁_tight` | the empty report over Bool × Bool, q₁ = q₂ = True, a₁ = contradicted |
| h₂ : Correct E q₂ a₂ (in and_answer_mem_andTable_of_satisfiable) | with an incorrect component answer a₂ the compound answer can lie outside the cell | tight: `and_answer_h₂_tight` | the empty report over Bool × Bool, q₁ = q₂ = True, a₂ = contradicted |
| h : Correct E (fun w => q₁ w ∧ q₂ w) a (in and_answer_mem_andTable_of_satisfiable) | an incorrect compound answer can lie outside the cell | tight: `and_answer_h_tight` | the empty report over Bool × Bool, q₁ = q₂ = True, a = contradicted |
| hE : Satisfiable E (in or_answer_mem_orTable_of_satisfiable) | over an unsatisfiable report two answers are correct for each claim, and some combinations fall outside the table | tight: `or_answer_hE_tight` | the unsatisfiable one-claim report [False] over Nat |
| h₁ : Correct E q₁ a₁ (in or_answer_mem_orTable_of_satisfiable) | with an incorrect component answer a₁ the compound answer can lie outside the cell | tight: `or_answer_h₁_tight` | the empty report over Bool × Bool, q₁ = q₂ = False, a₁ = supported |
| h₂ : Correct E q₂ a₂ (in or_answer_mem_orTable_of_satisfiable) | with an incorrect component answer a₂ the compound answer can lie outside the cell | tight: `or_answer_h₂_tight` | the empty report over Bool × Bool, q₁ = q₂ = False, a₂ = supported |
| h : Correct E (fun w => q₁ w ∨ q₂ w) a (in or_answer_mem_orTable_of_satisfiable) | an incorrect compound answer can lie outside the cell | tight: `or_answer_h_tight` | the empty report over Bool × Bool, q₁ = q₂ = False, a = supported |
| h : Correct E q a (in neg_answer_correct) | from an incorrect answer a, negAnswer a can be incorrect for ¬q | tight: `neg_answer_h_tight` | the empty report over Bool × Bool, q = True, a = contradicted |
| hu : ∀ w, Models E w → w = w₀ (in not_undetermined_of_unique_model) | a report with two consistent interpretations can leave a claim undetermined | tight: `not_undetermined_of_unique_model_hu_tight` | the empty report over Bool (two consistent interpretations): hu fails for every w₀ : Bool, and b = true is undetermined |

**Non-vacuity.** Empty report over Bool × Bool (satisfiable): q₁ contradicted, q₂ = (first coordinate) undetermined, conjunction contradicted; q₁ = first coordinate and q₂ = its negation, both undetermined, disjunction supported; [n ≤ 1] over Nat for negation (n = 0 undetermined); [n = 0] over Nat, whose unique consistent interpretation is 0 (hu holds with w₀ = 0). (`and_answer_nonvacuous`, `or_answer_nonvacuous`, `neg_answer_nonvacuous`, `not_undetermined_of_unique_model_nonvacuous`)

**Prior art.**

- B. C. van Fraassen, "Singular terms, truth-value gaps, and free logic", Journal of Philosophy 63(17):481-495, 1966, doi:10.2307/2024549 (supervaluations: a compound can be determinately true or false although a component has no truth value). Bibliographic record and the cited idea checked via secondary sources; the full text was not consulted.
- K. Fine, "Vagueness, truth and logic", Synthese 30(3-4):265-300, 1975, doi:10.1007/BF00485047 (supervaluationist treatment in which compounds of indeterminate sentences need not be truth-functional, e.g. P or not-P is true though both disjuncts are indeterminate).

**Design question.** Reference point: a definitional fact recorded so that other cards can cite it. Which question forms make the correct answer ill-defined (compound questions about undetermined claims)?

**Non-claims.** Listed under **Boundaries → Non-claims → 6**.

### 7. `prefix-criterion-sufficient-environment-semantics`

Tier T1 · kind: theorem · depth: substantive

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** For quantifier prefixes φ and ψ on the variables Fin n, in front of the same uninterpreted matrix (variables matched by index), if no variable is bound twice in φ, every variable is bound exactly once in ψ, (i) every variable universal in ψ is universal in φ, and (ii) whenever v is existential in φ and u is universal in both with u bound before v in φ, u is also bound before v in ψ, then for every base type α, every matrix R and every environment ρ : Fin n → α, φ with R implies ψ with R (SEntailsAt α φ ψ). This holds vacuously when α is empty and n ≥ 1, where there is no environment and every pair satisfies SEntailsAt (sentailsAt_of_isEmpty). If a prefix binds every variable, its value does not depend on the environment. For every type α, (∀ P, (∀x, P x) → ∃x, P x) holds iff α is nonempty.

**Tier.** Skolem-dependency transfer between quantifier prefixes is folklore; this exact entailment criterion (with universal-to-existential weakening, over all matrices) was not located in the checked sources and is mechanized here.

**Lean statements.**

**`prefixCrit_sound_of_nodup_wf`**
```lean
-- ClaimStrength/PrefixResults.lean:116-117
theorem prefixCrit_sound_of_nodup_wf {φ ψ : Prefix n} (hφ : (bvars φ).Nodup) (hψ : WF ψ)
    (h : PrefixCrit φ ψ) : SEntailsAt α φ ψ
```

**`eval_env_irrelevant_of_covers`**
```lean
-- ClaimStrength/PrefixResults.lean:82-83
theorem eval_env_irrelevant_of_covers {φ : Prefix n} (hcov : ∀ v : Fin n, v ∈ bvars φ)
    (R : (Fin n → α) → Prop) (ρ ρ' : Fin n → α) : eval φ R ρ ↔ eval φ R ρ'
```

**`sentailsAt_of_isEmpty`**
```lean
-- ClaimStrength/PrefixResults.lean:100
theorem sentailsAt_of_isEmpty (hα : α → False) (φ ψ : Prefix (n + 1)) : SEntailsAt α φ ψ
```

**`closed_forall_imp_exists_iff_nonempty`**
```lean
-- ClaimStrength/PrefixResults.lean:105-106
theorem closed_forall_imp_exists_iff_nonempty (α : Type) :
    (∀ P : α → Prop, (∀ x, P x) → ∃ x, P x) ↔ Nonempty α
```

Unfolded statement of `prefixCrit_sound_of_nodup_wf` (WF, PrefixCrit, UnivReflected, SkolemOrderPreserved and SEntailsAt written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {n : Nat} {α : Type} {φ ψ : Prefix n}, (bvars φ).Nodup →
  ((bvars ψ).Nodup ∧ ∀ v : Fin n, v ∈ bvars ψ) →
  ((∀ v, qOf ψ v = some .all → qOf φ v = some .all) ∧
    (∀ u v, qOf φ v = some .ex → qOf φ u = some .all → qOf ψ u = some .all →
      Precedes φ u v → Precedes ψ u v)) →
  ∀ (R : (Fin n → α) → Prop) (ρ : Fin n → α), eval φ R ρ → eval ψ R ρ
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hφ : (bvars φ).Nodup (in prefixCrit_sound_of_nodup_wf) | a repeated binder in φ shadows the first one, which the criterion reads; the entailment can then fail | tight: `prefixCrit_sound_hφ_tight` | one variable at Bool (φ = ∀x ∃x, ψ = ∀x) |
| hψ : WF ψ — no repeated binder and every variable bound (in prefixCrit_sound_of_nodup_wf) | a repeated binder in ψ shadows the first one; a variable left unbound by ψ behaves like an outermost universal; in both cases the entailment can fail | tight: `prefixCrit_sound_hψ_tight_dup`, `prefixCrit_sound_hψ_tight_missing` | one variable at Bool (ψ = ∃x ∀x for the duplicate half; ψ empty with x free for the covering half) |
| h : PrefixCrit φ ψ, part (i) UnivReflected (in prefixCrit_sound_of_nodup_wf) | if a variable universal in ψ is existential in φ, the entailment can fail | tight: `prefixCrit_part_i_tight` | one variable at Bool (∃x versus ∀x) |
| h : PrefixCrit φ ψ, part (ii) SkolemOrderPreserved (in prefixCrit_sound_of_nodup_wf) | if ψ moves an existential of φ before a universal it depends on, the entailment can fail | tight: `prefixCrit_part_ii_tight` | two variables at Bool (∀x ∃y versus ∃y ∀x) |
| hcov : ∀ v : Fin n, v ∈ bvars φ (in eval_env_irrelevant_of_covers) | a variable left unbound takes its value from the environment | tight: `eval_env_irrelevant_hcov_tight` | one variable at Bool, empty prefix |
| hα : α → False (in sentailsAt_of_isEmpty) | over an inhabited base type the conclusion fails for ∃x versus ∀x | tight: `sentailsAt_of_isEmpty_tight` | Bool, one variable |

**Non-vacuity.** φ = ∀x ∃y, ψ = ∃y ∃x on two variables: no repeated binder in φ, ψ well formed, criterion holds (x is instantiated), and φ is satisfiable at Bool; the prefix ∀x binds the single variable of Fin 1; Empty is empty. (`prefixCrit_sound_nonvacuous`, `eval_env_irrelevant_of_covers_nonvacuous`, `sentailsAt_of_isEmpty_nonvacuous`)

**Prior art.**

- M. Samer and S. Szeider, "Backdoor Sets of Quantified Boolean Formulas", Journal of Automated Reasoning 42(1):77-97, 2009, doi:10.1007/s10817-008-9114-5. Definition 2 (dependency schemes: the variables a variable may depend on can be shifted without changing the truth value of the formula, i.e. equivalence is preserved) and Definition 4 (the trivial dependency scheme relates every variable x, existential or universal, to all variables from the first later quantifier block of the other quantifier onward), checked in the authors' version. The trivial scheme therefore also constrains pairs with an existential variable before a universal one, as equivalence-preserving reordering requires. The criterion here constrains the pairs with a universal variable before an existential one, and no other pairs (the Skolem dependencies), because it characterizes one-way entailment, under which ∃y ∀x entails ∀x ∃y.
- F. Slivovsky and S. Szeider, "Quantifier Reordering for QBF", Journal of Automated Reasoning 56(4):459-477, 2016, doi:10.1007/s10817-015-9353-1 (dependency schemes used to reorder the prefix of a fixed formula while preserving its truth value; checked against the publisher's abstract). Related but different: that work preserves the truth of one formula; the result here characterizes one-way entailment between two prefixes over all matrices, including universal-to-existential weakening.
- H. B. Enderton, A Mathematical Introduction to Logic, 2nd ed., Harcourt/Academic Press, 2001, Section 4.2 "Skolem functions" (section number from secondary sources, not checked against a copy). The Skolem dependency of an existential variable on the universal variables before it is the relation that part (ii) of the criterion preserves; the proof here does not construct Skolem functions.
- L. Henkin, "Some remarks on infinitely long formulas", in Infinitistic Methods (Proc. Symp. Foundations of Mathematics, Warsaw 1959), Pergamon/PWN, 1961, pp. 167-183 (partially ordered quantifier prefixes; bibliographic record from secondary sources). The prefixes treated here are linear.
- W. J. Walkoe, Jr., "Finite partially-ordered quantification", Journal of Symbolic Logic 35(4):535-555, 1970, doi:10.2307/2271440 (partially ordered prefixes and their expressive power). Out of scope here: partially ordered prefixes; the prefixes treated here are linear.
- V. Balabanov, H.-J. K. Chiang, J.-H. R. Jiang, "Henkin quantifiers and Boolean formulae: A certification perspective of DQBF", Theoretical Computer Science 523:86-100, 2014, doi:10.1016/j.tcs.2013.12.020 (Skolem-function certificates where each existential variable names the universals it may depend on; bibliographic record from index sources).

**Design question.** Is strength between quantifier-prefix claim shapes decidable and syntactically visible, so that a summary that reorders or flips quantifiers can be checked mechanically?

**Non-claims.** Listed under **Boundaries → Non-claims → 7**.

### 8. `prefix-criterion-necessary-two-point-base`

Tier T1 · kind: theorem · depth: substantive

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** For prefixes φ and ψ on the variables Fin n (same matrix, variables matched by index): (1) if no variable is bound twice in φ or in ψ, the base type α has two distinct elements, and SEntailsAt α φ ψ holds, then parts (i) and (ii) of the prefix criterion hold. (2) If no variable is bound twice in φ and every variable is bound exactly once in ψ, then for every base type α with two distinct elements, SEntailsAt α φ ψ holds iff the criterion holds. (3) If no variable is bound twice in φ and every variable is bound exactly once in ψ, then SEntails φ ψ (SEntailsAt at every base type) holds iff the criterion holds. (4) For all φ and ψ, SEntails φ ψ holds iff SEntailsAt α φ ψ holds at every base type α with two distinct elements. (5) If α has at most one element (Subsingleton α), then every prefix evaluates to its matrix at the environment, and SEntailsAt α φ ψ holds for all φ and ψ.

**Tier.** Folklore countermodels (x_v = c and x_v = g(x_u)) made precise and mechanized for arbitrary prefixes.

**Lean statements.**

**`prefixCrit_necessary_of_two_point_nodup`**
```lean
-- ClaimStrength/PrefixResults.lean:176-178
theorem prefixCrit_necessary_of_two_point_nodup (hα : ∃ a b : α, a ≠ b) {φ ψ : Prefix n}
    (hφ : (bvars φ).Nodup) (hψ : (bvars ψ).Nodup) (h : SEntailsAt α φ ψ) :
    PrefixCrit φ ψ
```

**`sentailsAt_iff_prefixCrit_of_two_point_nodup_wf`**
```lean
-- ClaimStrength/PrefixResults.lean:260-261
theorem sentailsAt_iff_prefixCrit_of_two_point_nodup_wf (hα : ∃ a b : α, a ≠ b) {φ ψ : Prefix n}
    (hφ : (bvars φ).Nodup) (hψ : WF ψ) : SEntailsAt α φ ψ ↔ PrefixCrit φ ψ
```

**`sentails_iff_prefixCrit_of_nodup_wf`**
```lean
-- ClaimStrength/PrefixResults.lean:291-292
theorem sentails_iff_prefixCrit_of_nodup_wf {φ ψ : Prefix n} (hφ : (bvars φ).Nodup) (hψ : WF ψ) :
    SEntails φ ψ ↔ PrefixCrit φ ψ
```

**`sentails_iff_twoPoint_types`**
```lean
-- ClaimStrength/PrefixResults.lean:280-281
theorem sentails_iff_twoPoint_types (φ ψ : Prefix n) :
    SEntails φ ψ ↔ ∀ α : Type, (∃ a b : α, a ≠ b) → SEntailsAt α φ ψ
```

**`sentailsAt_of_subsingleton`**
```lean
-- ClaimStrength/PrefixResults.lean:276
theorem sentailsAt_of_subsingleton [Subsingleton α] (φ ψ : Prefix n) : SEntailsAt α φ ψ
```

**`eval_subsingleton`**
```lean
-- ClaimStrength/PrefixResults.lean:264-265
theorem eval_subsingleton [Subsingleton α] :
    ∀ (φ : Prefix n) (R : (Fin n → α) → Prop) (ρ : Fin n → α), eval φ R ρ ↔ R ρ
```

Unfolded statement of `prefixCrit_necessary_of_two_point_nodup` (SEntailsAt, PrefixCrit, UnivReflected and SkolemOrderPreserved written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {n : Nat} {α : Type}, (∃ a b : α, a ≠ b) → ∀ {φ ψ : Prefix n},
  (bvars φ).Nodup → (bvars ψ).Nodup →
  (∀ (R : (Fin n → α) → Prop) (ρ : Fin n → α), eval φ R ρ → eval ψ R ρ) →
  (∀ v, qOf ψ v = some .all → qOf φ v = some .all) ∧
    (∀ u v, qOf φ v = some .ex → qOf φ u = some .all → qOf ψ u = some .all →
      Precedes φ u v → Precedes ψ u v)
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hα : ∃ a b : α, a ≠ b (in prefixCrit_necessary_of_two_point_nodup) | on a one-element base type ∃x entails ∀x although the criterion fails | tight: `prefixCrit_necessary_hα_tight` | the one-element type Unit, one variable |
| hφ : (bvars φ).Nodup (in prefixCrit_necessary_of_two_point_nodup) | a repeated binder in φ shadows the first one, which the criterion reads | tight: `prefixCrit_necessary_hφ_tight` | one variable at Bool (φ = ∃x ∀x, ψ = ∀x) |
| hψ : (bvars ψ).Nodup (in prefixCrit_necessary_of_two_point_nodup) | a repeated binder in ψ shadows the first one, which the criterion reads | tight: `prefixCrit_necessary_hψ_tight` | one variable at Bool (φ = ∃x, ψ = ∀x ∃x) |
| h : SEntailsAt α φ ψ (in prefixCrit_necessary_of_two_point_nodup) | without the entailment the criterion can fail | tight: `prefixCrit_necessary_h_tight` | two variables at Bool (∀x ∃y versus ∃y ∀x) |
| hα : ∃ a b : α, a ≠ b (in sentailsAt_iff_prefixCrit_of_two_point_nodup_wf) | on a one-element base type the entailment holds and the criterion fails, so the biconditional fails | tight: `sentailsAt_iff_hα_tight` | the one-element type Unit, one variable (φ = ∃x, ψ = ∀x) |
| hφ : (bvars φ).Nodup (in sentailsAt_iff_prefixCrit_of_two_point_nodup_wf) | with a repeated binder in φ the entailment holds and the criterion fails | tight: `sentailsAt_iff_hφ_tight` | one variable at Bool (φ = ∃x ∀x, ψ = ∀x) |
| hψ : WF ψ (in sentailsAt_iff_prefixCrit_of_two_point_nodup_wf) | with a repeated binder in ψ, or a variable left unbound by ψ, the criterion holds and the entailment fails | tight: `sentailsAt_iff_hψ_tight_dup`, `sentailsAt_iff_hψ_tight_missing` | one variable at Bool (φ = ∃x; ψ = ∃x ∀x for the duplicate half, ψ empty for the covering half) |
| hφ : (bvars φ).Nodup (in sentails_iff_prefixCrit_of_nodup_wf) | with a repeated binder in φ the entailment holds at every base type and the criterion fails | tight: `sentails_iff_hφ_tight` | one variable (φ = ∃x ∀x, ψ = ∀x) |
| hψ : WF ψ (in sentails_iff_prefixCrit_of_nodup_wf) | with a repeated binder in ψ, or a variable left unbound by ψ, the criterion holds and the entailment fails at Bool | tight: `sentails_iff_hψ_tight_dup`, `sentails_iff_hψ_tight_missing` | one variable, failure at Bool (φ = ∃x; ψ = ∃x ∀x for the duplicate half, ψ empty for the covering half) |
| [Subsingleton α] (in sentailsAt_of_subsingleton) | on a base type with two elements ∀x ∃y does not entail ∃y ∀x | tight: `sentailsAt_of_subsingleton_tight` | Bool, two variables |
| [Subsingleton α] (in eval_subsingleton) | on a base type with two elements ∀x (x = true) does not evaluate to its matrix at the environment x := true | tight: `eval_subsingleton_tight` | Bool, one variable |

**Non-vacuity.** At Bool, ∃y ∀x versus ∀x ∃y: no repeated binders, ψ well formed, the entailment and the criterion hold (also at every base type); Unit is a subsingleton, and there ∃x entails ∀x. (`prefixCrit_necessary_nonvacuous`, `sentailsAt_iff_nonvacuous`, `sentails_iff_nonvacuous`, `subsingleton_nonvacuous`)

**Prior art.**

- M. Samer and S. Szeider, "Backdoor Sets of Quantified Boolean Formulas", Journal of Automated Reasoning 42(1):77-97, 2009, doi:10.1007/s10817-008-9114-5. Definition 2 (dependency schemes: the variables a variable may depend on can be shifted without changing the truth value of the formula, i.e. equivalence is preserved) and Definition 4 (the trivial dependency scheme relates every variable x, existential or universal, to all variables from the first later quantifier block of the other quantifier onward), checked in the authors' version. The trivial scheme therefore also constrains pairs with an existential variable before a universal one, as equivalence-preserving reordering requires. The criterion here constrains the pairs with a universal variable before an existential one, and no other pairs (the Skolem dependencies), because it characterizes one-way entailment, under which ∃y ∀x entails ∀x ∃y.
- F. Slivovsky and S. Szeider, "Quantifier Reordering for QBF", Journal of Automated Reasoning 56(4):459-477, 2016, doi:10.1007/s10817-015-9353-1 (dependency schemes used to reorder the prefix of a fixed formula while preserving its truth value; checked against the publisher's abstract). Related but different: that work preserves the truth of one formula; the result here characterizes one-way entailment between two prefixes over all matrices, including universal-to-existential weakening.
- H. B. Enderton, A Mathematical Introduction to Logic, 2nd ed., Harcourt/Academic Press, 2001, Section 4.2 "Skolem functions" (section number from secondary sources, not checked against a copy). The Skolem dependency of an existential variable on the universal variables before it is the relation that part (ii) of the criterion preserves; the proof here does not construct Skolem functions.

**Design question.** Is strength between quantifier-prefix claim shapes decidable and syntactically visible, so that a summary that reorders or flips quantifiers can be checked mechanically?

**Non-claims.** Listed under **Boundaries → Non-claims → 8**.

### 9. `prefix-entailment-decidable`

Tier T1 · kind: characterization · depth: shallow

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** The Boolean function prefixCritB satisfies prefixCritB φ ψ = true ↔ PrefixCrit φ ψ, and wfB φ = true ↔ WF φ. If the base type α has two distinct elements, no variable is bound twice in φ, and every variable is bound exactly once in ψ, then SEntailsAt α φ ψ holds iff prefixCritB φ ψ = true. On two variables: ∃y∀x entails ∀x∃y at every base type, and ∀x∃y does not entail ∃y∀x at Bool (countermodel: the matrix y = x, under which ∀x∃y holds and ∃y∀x fails; forall_exists_not_sentails_exists_forall_witness). On one variable: ∀x entails ∃x at every base type under environment semantics (vacuously when the type is empty), and ∃x does not entail ∀x at Bool. prefixCritB returns true / false on these four pairs, and false on ∀x₀∃x₁ versus ∀x₁∃x₀. Over relations on Nat, '∀x ∃n, R x n' does not entail '∃n ∀x, R x n' (countermodel R = ≤; in particular (∀x, ∃n, x ≤ n) → (∃n, ∀x, x ≤ n) is false over Nat), and '∃n ∀x' entails '∀x ∃n'.

**Tier.** The decision procedure follows from the characterization; the one- and two-variable instances are textbook.

**Lean statements.**

**`prefixCritB_iff`**
```lean
-- ClaimStrength/PrefixResults.lean:24
theorem prefixCritB_iff (φ ψ : List (Binder n K)) : prefixCritB φ ψ = true ↔ PrefixCrit φ ψ
```

**`wfB_iff`**
```lean
-- ClaimStrength/PrefixResults.lean:21
theorem wfB_iff (φ : List (Binder n K)) : wfB φ = true ↔ WF φ
```

**`sentailsAt_iff_prefixCritB_of_two_point_nodup_wf`**
```lean
-- ClaimStrength/PrefixResults.lean:301-303
theorem sentailsAt_iff_prefixCritB_of_two_point_nodup_wf (hα : ∃ a b : α, a ≠ b)
    {φ ψ : Prefix n} (hφ : (bvars φ).Nodup) (hψ : WF ψ) :
    SEntailsAt α φ ψ ↔ prefixCritB φ ψ = true
```

**`exists_forall_sentails_forall_exists`**
```lean
-- ClaimStrength/PrefixResults.lean:307-308
theorem exists_forall_sentails_forall_exists (α : Type) :
    SEntailsAt α ([X 1, A 0] : Prefix 2) [A 0, X 1]
```

**`forall_exists_not_sentails_exists_forall`**
```lean
-- ClaimStrength/PrefixResults.lean:321-322
theorem forall_exists_not_sentails_exists_forall :
    ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0]
```

**`forall_exists_not_sentails_exists_forall_witness`**
```lean
-- ClaimStrength/Witnesses.lean:25-27
theorem forall_exists_not_sentails_exists_forall_witness :
    eval ([A 0, X 1] : Prefix 2) (fun σ : Fin 2 → Bool => σ 1 = σ 0) (fun _ => false) ∧
    ¬ eval ([X 1, A 0] : Prefix 2) (fun σ : Fin 2 → Bool => σ 1 = σ 0) (fun _ => false)
```

**`forall_sentails_exists`**
```lean
-- ClaimStrength/PrefixResults.lean:337
theorem forall_sentails_exists (α : Type) : SEntailsAt α ([A 0] : Prefix 1) [X 0]
```

**`exists_not_sentails_forall`**
```lean
-- ClaimStrength/PrefixResults.lean:344
theorem exists_not_sentails_forall : ¬ SEntailsAt Bool ([X 0] : Prefix 1) [A 0]
```

**`prefixCritB_exists_forall_forall_exists`**
```lean
-- ClaimStrength/PrefixResults.lean:352-353
theorem prefixCritB_exists_forall_forall_exists :
    prefixCritB ([X 1, A 0] : Prefix 2) [A 0, X 1] = true
```

**`prefixCritB_forall_exists_exists_forall`**
```lean
-- ClaimStrength/PrefixResults.lean:355-356
theorem prefixCritB_forall_exists_exists_forall :
    prefixCritB ([A 0, X 1] : Prefix 2) [X 1, A 0] = false
```

**`prefixCritB_forall_exists`**
```lean
-- ClaimStrength/PrefixResults.lean:358
theorem prefixCritB_forall_exists : prefixCritB ([A 0] : Prefix 1) [X 0] = true
```

**`prefixCritB_exists_forall`**
```lean
-- ClaimStrength/PrefixResults.lean:360
theorem prefixCritB_exists_forall : prefixCritB ([X 0] : Prefix 1) [A 0] = false
```

**`prefixCritB_renamed_false`**
```lean
-- ClaimStrength/PrefixResults.lean:364
theorem prefixCritB_renamed_false : prefixCritB ([A 0, X 1] : Prefix 2) [A 1, X 0] = false
```

**`pointwise_bound_not_uniform`**
```lean
-- ClaimStrength/Drift.lean:135-136
theorem pointwise_bound_not_uniform :
    ¬ Entails (W := Nat → Nat → Prop) (fun R => ∀ x, ∃ n, R x n) (fun R => ∃ n, ∀ x, R x n)
```

**`nat_pointwise_bound_not_uniform`**
```lean
-- ClaimStrength/Drift.lean:142-143
theorem nat_pointwise_bound_not_uniform :
    ¬ ((∀ x : Nat, ∃ n, x ≤ n) → ∃ n, ∀ x : Nat, x ≤ n)
```

**`uniform_entails_pointwise`**
```lean
-- ClaimStrength/Drift.lean:149-150
theorem uniform_entails_pointwise :
    Entails (W := Nat → Nat → Prop) (fun R => ∃ n, ∀ x, R x n) (fun R => ∀ x, ∃ n, R x n)
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hα : ∃ a b : α, a ≠ b (in sentailsAt_iff_prefixCritB_of_two_point_nodup_wf) | on a one-element base type the entailment holds and prefixCritB returns false | tight: `sentailsAt_iff_hα_tight` | the one-element type Unit, one variable (φ = ∃x, ψ = ∀x) |
| hφ : (bvars φ).Nodup (in sentailsAt_iff_prefixCritB_of_two_point_nodup_wf) | with a repeated binder in φ the entailment holds and prefixCritB returns false | tight: `sentailsAt_iff_hφ_tight` | one variable at Bool (φ = ∃x ∀x, ψ = ∀x) |
| hψ : WF ψ (in sentailsAt_iff_prefixCritB_of_two_point_nodup_wf) | with a repeated binder in ψ, or a variable left unbound by ψ, prefixCritB returns true and the entailment fails | tight: `sentailsAt_iff_hψ_tight_dup`, `sentailsAt_iff_hψ_tight_missing` | one variable at Bool (φ = ∃x; ψ = ∃x ∀x for the duplicate half, ψ empty for the covering half) |

**Non-vacuity.** At Bool, ∃y ∀x versus ∀x ∃y: every hypothesis holds and both sides hold; prefixCritB returns true on this pair (decide); the relation n = 0 on Nat has the uniform bound 0. (`sentailsAt_iff_nonvacuous`, `prefixCritB_exists_forall_forall_exists`, `uniform_entails_pointwise_nonvacuous`)

**Prior art.**

- M. Samer and S. Szeider, "Backdoor Sets of Quantified Boolean Formulas", Journal of Automated Reasoning 42(1):77-97, 2009, doi:10.1007/s10817-008-9114-5. Definition 2 (dependency schemes: the variables a variable may depend on can be shifted without changing the truth value of the formula, i.e. equivalence is preserved) and Definition 4 (the trivial dependency scheme relates every variable x, existential or universal, to all variables from the first later quantifier block of the other quantifier onward), checked in the authors' version. The trivial scheme therefore also constrains pairs with an existential variable before a universal one, as equivalence-preserving reordering requires. The criterion here constrains the pairs with a universal variable before an existential one, and no other pairs (the Skolem dependencies), because it characterizes one-way entailment, under which ∃y ∀x entails ∀x ∃y.
- H. S. Kurtzman and M. C. MacDonald, "Resolution of quantifier scope ambiguities", Cognition 48(3):243-279, 1993, doi:10.1016/0010-0277(93)90042-T (experimental study of how readers resolve "every ... a ..." scope ambiguities; record and abstract from index sources). Cited for the prose motivation of the forall-exists / exists-forall drift.

**Design question.** Is strength between quantifier-prefix claim shapes decidable and syntactically visible, so that a summary that reorders or flips quantifiers can be checked mechanically?

**Non-claims.** Listed under **Boundaries → Non-claims → 9**.

### 10. `domain-and-premise-variance`

Tier T0 · kind: characterization · depth: definitional · reference point

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** For domains D, D' and premises H, H' on a type α: '∀x ∈ D, P x' entails '∀x ∈ D', P x' for every predicate P iff D' ⊆ D; '∃x ∈ D, P x' entails '∃x ∈ D', P x' for every P iff D ⊆ D'; '∀x, H x → C x' entails '∀x, H' x → C x' for every C iff H' ⊆ H; and '∀x, H x → C x' entails '∀x, C x' for every C iff H holds everywhere. Instances: over predicates P on Nat, 'P 2' does not entail '∀k ≥ 1, P k' (countermodel P k := k = 2; single_parameter_not_range_witness) while the converse holds; over pairs (H, C) of predicates on Nat, '∀x, H x → C x' does not entail '∀x, C x' (countermodel H = C = (· = 0); relative_not_absolute_witness) while '∀x, C x' entails '∀x, H x → C x' (absolute_entails_relative); over pairs (A, C) of propositions, 'A → C' does not entail 'C' (countermodel A = C = False; relative_to_assumption_not_absolute_witness); over triples (H₁, H₂, C) of propositions, 'H₁ ∧ H₂ → C' does not entail 'H₁ ∨ H₂ → C' (countermodel H₁ = True, H₂ = False, C = False; conj_premise_not_disj_witness) while the converse holds.

**Tier.** Monotonicity of bounded quantifiers restated, with the drift instances it explains.

**Lean statements.**

**`forall_domain_entails_iff`**
```lean
-- ClaimStrength/Drift.lean:24-26
theorem forall_domain_entails_iff (D D' : α → Prop) :
    Entails (W := α → Prop) (fun P => ∀ x, D x → P x) (fun P => ∀ x, D' x → P x) ↔
      ∀ x, D' x → D x
```

**`exists_domain_entails_iff`**
```lean
-- ClaimStrength/Drift.lean:33-35
theorem exists_domain_entails_iff (D D' : α → Prop) :
    Entails (W := α → Prop) (fun P => ∃ x, D x ∧ P x) (fun P => ∃ x, D' x ∧ P x) ↔
      ∀ x, D x → D' x
```

**`premise_entails_iff`**
```lean
-- ClaimStrength/Drift.lean:45-47
theorem premise_entails_iff (H H' : α → Prop) :
    Entails (W := α → Prop) (fun C => ∀ x, H x → C x) (fun C => ∀ x, H' x → C x) ↔
      ∀ x, H' x → H x
```

**`relative_entails_absolute_iff`**
```lean
-- ClaimStrength/Drift.lean:52-53
theorem relative_entails_absolute_iff (H : α → Prop) :
    Entails (W := α → Prop) (fun C => ∀ x, H x → C x) (fun C => ∀ x, C x) ↔ ∀ x, H x
```

**`single_parameter_not_range`**
```lean
-- ClaimStrength/Drift.lean:124-125
theorem single_parameter_not_range :
    ¬ Entails (W := Nat → Prop) (fun P => P 2) (fun P => ∀ k, 1 ≤ k → P k)
```

**`single_parameter_not_range_witness`**
```lean
-- ClaimStrength/Witnesses.lean:40-42
theorem single_parameter_not_range_witness :
    (fun P : Nat → Prop => P 2) (fun k => k = 2) ∧
    ¬ (fun P : Nat → Prop => ∀ k, 1 ≤ k → P k) (fun k => k = 2)
```

**`range_entails_single`**
```lean
-- ClaimStrength/Drift.lean:130-131
theorem range_entails_single :
    Entails (W := Nat → Prop) (fun P => ∀ k, 1 ≤ k → P k) (fun P => P 2)
```

**`relative_not_absolute`**
```lean
-- ClaimStrength/Drift.lean:154-156
theorem relative_not_absolute :
    ¬ Entails (W := (Nat → Prop) × (Nat → Prop)) (fun w => ∀ x, w.1 x → w.2 x)
      (fun w => ∀ x, w.2 x)
```

**`relative_not_absolute_witness`**
```lean
-- ClaimStrength/Witnesses.lean:49-51
theorem relative_not_absolute_witness :
    (fun w : (Nat → Prop) × (Nat → Prop) => ∀ x, w.1 x → w.2 x) ((· = 0), (· = 0)) ∧
    ¬ (fun w : (Nat → Prop) × (Nat → Prop) => ∀ x, w.2 x) ((· = 0), (· = 0))
```

**`relative_to_assumption_not_absolute`**
```lean
-- ClaimStrength/Drift.lean:161-162
theorem relative_to_assumption_not_absolute :
    ¬ Entails (W := Prop × Prop) (fun w => w.1 → w.2) (fun w => w.2)
```

**`relative_to_assumption_not_absolute_witness`**
```lean
-- ClaimStrength/Witnesses.lean:58-60
theorem relative_to_assumption_not_absolute_witness :
    (fun w : Prop × Prop => w.1 → w.2) (False, False) ∧
    ¬ (fun w : Prop × Prop => w.2) (False, False)
```

**`absolute_entails_relative`**
```lean
-- ClaimStrength/Drift.lean:166-168
theorem absolute_entails_relative :
    Entails (W := (Nat → Prop) × (Nat → Prop)) (fun w => ∀ x, w.2 x)
      (fun w => ∀ x, w.1 x → w.2 x)
```

**`conj_premise_not_disj`**
```lean
-- ClaimStrength/Drift.lean:246-248
theorem conj_premise_not_disj :
    ¬ Entails (W := Prop × Prop × Prop) (fun w => w.1 ∧ w.2.1 → w.2.2)
      (fun w => w.1 ∨ w.2.1 → w.2.2)
```

**`conj_premise_not_disj_witness`**
```lean
-- ClaimStrength/Witnesses.lean:65-67
theorem conj_premise_not_disj_witness :
    (fun w : Prop × Prop × Prop => w.1 ∧ w.2.1 → w.2.2) (True, False, False) ∧
    ¬ (fun w : Prop × Prop × Prop => w.1 ∨ w.2.1 → w.2.2) (True, False, False)
```

**`disj_premise_entails_conj`**
```lean
-- ClaimStrength/Drift.lean:252-254
theorem disj_premise_entails_conj :
    Entails (W := Prop × Prop × Prop) (fun w => w.1 ∨ w.2.1 → w.2.2)
      (fun w => w.1 ∧ w.2.1 → w.2.2)
```

**Hypothesis ledger.** None of the theorems of this card has a hypothesis.

**Non-vacuity.** Over Nat: '∀k ≥ 1, P k' entails '∀k = 2, P k', and '∃k = 2, P k' entails '∃k ≥ 1, P k'; the converse entailments hold at the interpretations P k := 1 ≤ k, (· = 0, True), (True, False, True). (`domain_variance_nonvacuous`, `range_entails_single_nonvacuous`, `absolute_entails_relative_nonvacuous`, `disj_premise_entails_conj_nonvacuous`)

**Prior art.**

- No specific prior statement located; elementary consequence of the definitions.
- S. A. Cook, "Soundness and completeness of an axiom system for program verification", SIAM J. Comput. 7(1):70-90, 1978, doi:10.1137/0207005 (completeness of Hoare logic relative to an oracle for the assertion theory under an expressiveness assumption: a standard example of a relativized completeness claim; record and abstract checked, full text not consulted). Cited as an example of a relative claim.

**Design question.** Reference point: a definitional fact recorded so that other cards can cite it. Which recurring summary drifts turn a proved claim into a strictly stronger unproved one, and what is the weaker reading that does follow?

**Non-claims.** Listed under **Boundaries → Non-claims → 10**.

### 11. `drift-single-counterexample-versus-universal-or-subclass`

Tier T0 · kind: counterexample · depth: definitional · reference point

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** Over predicates P on Nat, a single counterexample ('∃m, ¬P m') does not entail a universal refutation ('∀m, ¬P m') (countermodel P m := m ≠ 0; single_counterexample_not_universal_witness), and a counterexample among all naturals does not give one among the even naturals (countermodel P m := m % 2 = 0, which fails at 1 and holds at every even number; counterexample_in_class_not_in_subclass_witness). Conversely, for every nonempty type α, '∀m, ¬P m' entails '∃m, ¬P m' over predicates P on α; and over predicates P on Nat, for classes K, K' of naturals such that every element of K' is in K, a counterexample in K' is one in K.

**Tier.** Elementary quantifier facts, kernel-checked with natural countermodels.

**Lean statements.**

**`single_counterexample_not_universal`**
```lean
-- ClaimStrength/Drift.lean:70-71
theorem single_counterexample_not_universal :
    ¬ Entails (W := Nat → Prop) (fun P => ∃ m, ¬ P m) (fun P => ∀ m, ¬ P m)
```

**`single_counterexample_not_universal_witness`**
```lean
-- ClaimStrength/Witnesses.lean:72-74
theorem single_counterexample_not_universal_witness :
    (fun P : Nat → Prop => ∃ m, ¬ P m) (fun m => m ≠ 0) ∧
    ¬ (fun P : Nat → Prop => ∀ m, ¬ P m) (fun m => m ≠ 0)
```

**`universal_refutation_entails_single_of_nonempty`**
```lean
-- ClaimStrength/Drift.lean:77-78
theorem universal_refutation_entails_single_of_nonempty {α : Type} [Nonempty α] :
    Entails (W := α → Prop) (fun P => ∀ m, ¬ P m) (fun P => ∃ m, ¬ P m)
```

**`counterexample_in_class_not_in_subclass`**
```lean
-- ClaimStrength/Drift.lean:99-100
theorem counterexample_in_class_not_in_subclass :
    ¬ Entails (W := Nat → Prop) (fun P => ∃ m, ¬ P m) (fun P => ∃ m, m % 2 = 0 ∧ ¬ P m)
```

**`counterexample_in_class_not_in_subclass_witness`**
```lean
-- ClaimStrength/Witnesses.lean:82-84
theorem counterexample_in_class_not_in_subclass_witness :
    (fun P : Nat → Prop => ∃ m, ¬ P m) (fun m => m % 2 = 0) ∧
    ¬ (fun P : Nat → Prop => ∃ m, m % 2 = 0 ∧ ¬ P m) (fun m => m % 2 = 0)
```

**`counterexample_in_subclass_lifts`**
```lean
-- ClaimStrength/Drift.lean:106-107
theorem counterexample_in_subclass_lifts {K K' : Nat → Prop} (h : ∀ m, K' m → K m) :
    Entails (W := Nat → Prop) (fun P => ∃ m, K' m ∧ ¬ P m) (fun P => ∃ m, K m ∧ ¬ P m)
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| [Nonempty α] (in universal_refutation_entails_single_of_nonempty) | over the empty type the universal refutation holds vacuously and no counterexample exists | tight: `universal_refutation_nonempty_tight` | the empty type Empty |
| h : ∀ m, K' m → K m (in counterexample_in_subclass_lifts) | if K' is not contained in K, a counterexample in K' need not give one in K | tight: `counterexample_in_subclass_lifts_h_tight` | predicates on Nat, K' = all naturals, K = even naturals |

**Non-vacuity.** Even numbers inside all numbers; P m := m ≠ 0 has the even counterexample 0; Nat is nonempty and P := False is universally refuted. (`counterexample_in_subclass_lifts_nonvacuous`, `universal_refutation_nonvacuous`)

**Prior art.**

- L. R. Horn, "Toward a new taxonomy for pragmatic inference: Q-based and R-based implicature", in D. Schiffrin (ed.), Meaning, Form, and Use in Context: Linguistic Applications (GURT 1984), Georgetown University Press, 1984, pp. 11-42 (distinguishes Q-based, upper-bounding implicature, where a weaker statement suggests the stronger one fails, from R-based enrichment, where a statement is read as a stronger, stereotypical proposition; bibliographic record and summary from secondary sources). Cited as prose motivation: the strengthening drifts here resemble R-based enrichment, not Quantity.

**Design question.** Reference point: a definitional fact recorded so that other cards can cite it. Which recurring summary drifts turn a proved claim into a strictly stronger unproved one, and what is the weaker reading that does follow?

**Non-claims.** Listed under **Boundaries → Non-claims → 11**.

### 12. `drift-sufficient-versus-characterization`

Tier T0 · kind: counterexample · depth: definitional · reference point

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** Over pairs (A, B) of propositions, 'A → B' does not entail 'A ↔ B' and does not entail 'B → A' (countermodel A = False, B = True; sufficient_not_characterization_witness, sufficient_not_converse_witness), while 'A ↔ B' entails 'A → B'. For checkers on Nat (an acceptance function and a goodness predicate), soundness ('accept → good') does not entail completeness ('good → accept') (countermodel zeroChecker, which accepts exactly the input 0, with the even numbers good; checker_sound_not_complete_witness), completeness does not entail soundness (countermodel acceptAll, which accepts every input, with no input good; checker_complete_not_sound_witness), and soundness-and-completeness entails soundness.

**Tier.** Elementary; kernel-checked countermodels.

**Lean statements.**

**`sufficient_not_characterization`**
```lean
-- ClaimStrength/Drift.lean:173-174
theorem sufficient_not_characterization :
    ¬ Entails (W := Prop × Prop) (fun w => w.1 → w.2) (fun w => w.1 ↔ w.2)
```

**`sufficient_not_characterization_witness`**
```lean
-- ClaimStrength/Witnesses.lean:91-93
theorem sufficient_not_characterization_witness :
    (fun w : Prop × Prop => w.1 → w.2) (False, True) ∧
    ¬ (fun w : Prop × Prop => w.1 ↔ w.2) (False, True)
```

**`sufficient_not_converse`**
```lean
-- ClaimStrength/Drift.lean:178-179
theorem sufficient_not_converse :
    ¬ Entails (W := Prop × Prop) (fun w => w.1 → w.2) (fun w => w.2 → w.1)
```

**`sufficient_not_converse_witness`**
```lean
-- ClaimStrength/Witnesses.lean:98-100
theorem sufficient_not_converse_witness :
    (fun w : Prop × Prop => w.1 → w.2) (False, True) ∧
    ¬ (fun w : Prop × Prop => w.2 → w.1) (False, True)
```

**`characterization_entails_sufficient`**
```lean
-- ClaimStrength/Drift.lean:183-184
theorem characterization_entails_sufficient :
    Entails (W := Prop × Prop) (fun w => w.1 ↔ w.2) (fun w => w.1 → w.2)
```

**`checker_sound_not_complete`**
```lean
-- ClaimStrength/Drift.lean:224
theorem checker_sound_not_complete : ¬ Entails CheckerSound CheckerComplete
```

**`checker_sound_not_complete_witness`**
```lean
-- ClaimStrength/Witnesses.lean:105-106
theorem checker_sound_not_complete_witness :
    CheckerSound zeroChecker ∧ ¬ CheckerComplete zeroChecker
```

**`checker_complete_not_sound`**
```lean
-- ClaimStrength/Drift.lean:228
theorem checker_complete_not_sound : ¬ Entails CheckerComplete CheckerSound
```

**`checker_complete_not_sound_witness`**
```lean
-- ClaimStrength/Witnesses.lean:111-112
theorem checker_complete_not_sound_witness :
    CheckerComplete acceptAll ∧ ¬ CheckerSound acceptAll
```

**`checker_sound_complete_entails_sound`**
```lean
-- ClaimStrength/Drift.lean:232-233
theorem checker_sound_complete_entails_sound :
    Entails (fun c => CheckerSound c ∧ CheckerComplete c) CheckerSound
```

**Hypothesis ledger.** None of the theorems of this card has a hypothesis.

**Non-vacuity.** The checker accepting exactly the even numbers is sound and complete and accepts 0; A = B = True is a characterization. (`checker_sound_complete_nonvacuous`, `characterization_entails_sufficient_nonvacuous`, `checkerSound_example_pos`)

**Prior art.**

- M. L. Geis and A. M. Zwicky, "On Invited Inferences", Linguistic Inquiry 2(4):561-566, 1971 (conditional perfection: "if p then q" invites "if not p then not q"; bibliographic record and summary from secondary sources; the full text was not consulted). Cited for the prose motivation of the if/iff drift; no formal statement is taken from it.

**Design question.** Reference point: a definitional fact recorded so that other cards can cite it. Which recurring summary drifts turn a proved claim into a strictly stronger unproved one, and what is the weaker reading that does follow?

**Non-claims.** Listed under **Boundaries → Non-claims → 12**.

### 13. `relativized-criterion-sound`

Tier T1 · kind: theorem · depth: substantive

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** For relativized shapes φ and ψ (a prefix whose binders carry named domain classes, plus one named premise, evaluated by Holds as Q₁x₁∈I k₁ … Qₘxₘ∈I kₘ (J p x⃗ → M x⃗)), if both prefixes bind every variable exactly once, the tables incl, meets, impl are sound for the interpretations I, J (incl k k' = true implies I k ⊆ I k'; meets k k' = true implies I k and I k' share an element; impl p p' = true implies J p ⊆ J p'), and RCrit incl meets impl φ ψ holds (the prefix criterion; incl ψ-domain φ-domain = true for each variable universal in ψ; incl φ-domain ψ-domain = true for each variable existential in φ; meets φ-domain ψ-domain = true for each variable universal in φ and existential in ψ; impl ψ.prem φ.prem = true), then for every matrix M and environment ρ, φ with M implies ψ with M. No cardinality or nonemptiness assumption; when α is empty and n ≥ 1 the conclusion holds vacuously (rEntails_of_isEmpty). RCrit is decided by rcritB. If every domain of a prefix is nonempty and the premise does not depend on the variables it binds, the premise can be pulled out of the prefix (evalR_premise_pull_out); over Nat the shape ∀x ∈ {0,1} ∃y ∈ Nat (x ≤ 1 ∧ y ≤ 1 → M) holds for every M.

**Tier.** Combines the prefix criterion with folklore monotonicity of bounded quantifiers; the overlap condition for instantiated variables and the mechanized proof are made precise here.

**Lean statements.**

**`rcrit_sound`**
```lean
-- ClaimStrength/Relativized.lean:334-337
theorem rcrit_sound {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
    {incl meets : K → K → Bool} {impl : P → P → Bool} {φ ψ : Shape n K P}
    (hφ : WF φ.pre) (hψ : WF ψ.pre) (hI : InclSound I incl) (hM : MeetsSound I meets)
    (hJ : ImplSound J impl) (h : RCrit incl meets impl φ ψ) : REntails I J φ ψ
```

**`rcritB_iff`**
```lean
-- ClaimStrength/RelResults.lean:74-75
theorem rcritB_iff (incl meets : K → K → Bool) (impl : P → P → Bool) (φ ψ : Shape n K P) :
    rcritB incl meets impl φ ψ = true ↔ RCrit incl meets impl φ ψ
```

**`rEntails_of_isEmpty`**
```lean
-- ClaimStrength/Relativized.lean:347-348
theorem rEntails_of_isEmpty {I : K → α → Prop} {J : P → (Fin (n + 1) → α) → Prop}
    (hα : α → False) (φ ψ : Shape (n + 1) K P) : REntails I J φ ψ
```

**`evalR_premise_pull_out`**
```lean
-- ClaimStrength/Relativized.lean:354-357
theorem evalR_premise_pull_out (I : K → α → Prop) (H L : (Fin n → α) → Prop) :
    ∀ (pre : List (Binder n K)) (ρ : Fin n → α), (∀ b ∈ pre, ∃ a, I b.dom a) →
      (∀ b ∈ pre, ∀ (σ : Fin n → α) (a : α), H (upd σ b.var a) ↔ H σ) →
      (evalR I pre (fun σ => H σ → L σ) ρ ↔ (H ρ → evalR I pre L ρ))
```

**`holds_premise_on_existential_trivial`**
```lean
-- ClaimStrength/RelResults.lean:364-365
theorem holds_premise_on_existential_trivial (M : (Fin 2 → Nat) → Prop) (ρ : Fin 2 → Nat) :
    Holds clsI (premJ 1) ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .all⟩], .atMostOne⟩ M ρ
```

Unfolded statement of `rcrit_sound` (InclSound, MeetsSound, ImplSound, REntails and Holds written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {n : Nat} {K P α : Type} {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
  {incl meets : K → K → Bool} {impl : P → P → Bool} {φ ψ : Shape n K P},
  WF φ.pre → WF ψ.pre →
  (∀ k k', incl k k' = true → ∀ a, I k a → I k' a) →
  (∀ k k', meets k k' = true → ∃ a, I k a ∧ I k' a) →
  (∀ p p', impl p p' = true → ∀ σ, J p σ → J p' σ) →
  RCrit incl meets impl φ ψ →
  ∀ (M : (Fin n → α) → Prop) (ρ : Fin n → α),
    evalR I φ.pre (fun σ => J φ.prem σ → M σ) ρ → evalR I ψ.pre (fun σ => J ψ.prem σ → M σ) ρ
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hφ : WF φ.pre (in rcrit_sound) | a repeated binder shadows the first one; a variable left unbound by φ takes an environment value that need not lie in the domain; in both cases the entailment can fail | tight: `rcrit_sound_hφ_tight`, `rcrit_sound_hφ_tight_missing` | one variable over Nat (φ = ∀x ∃x; φ empty with ψ = ∃x ∈ {0}) |
| hψ : WF ψ.pre (in rcrit_sound) | a repeated binder shadows the first one; a variable left unbound by ψ behaves like an outer universal; in both cases the entailment can fail | tight: `rcrit_sound_hψ_tight`, `rcrit_sound_hψ_tight_missing` | one variable over Nat (ψ = ∃x ∀x; ψ empty) |
| hI : InclSound I incl (in rcrit_sound) | with an inclusion verdict that is not a true inclusion the entailment can fail | tight: `rcrit_sound_hI_tight` | one variable over Nat with the table 'everything included' |
| hM : MeetsSound I meets (in rcrit_sound) | with an overlap verdict that is not a true overlap the entailment can fail | tight: `rcrit_sound_hM_tight` | one variable over Nat with the table 'everything overlaps' |
| hJ : ImplSound J impl (in rcrit_sound) | with an implication verdict that is not a true implication the entailment can fail | tight: `rcrit_sound_hJ_tight` | one variable over Nat with the table 'every premise implies every other' |
| h : RCrit incl meets impl φ ψ, part (i) UnivReflected (in rcrit_sound) | if a variable universal in ψ is existential in φ, the entailment can fail | tight: `rcrit_part_i_tight` | one variable over Nat |
| h : RCrit incl meets impl φ ψ, part (ii) SkolemOrderPreserved (in rcrit_sound) | if ψ moves an existential of φ before a universal it depends on, the entailment can fail | tight: `rcrit_part_ii_tight` | two variables over Nat |
| h : RCrit incl meets impl φ ψ, UnivDomainsContravariant (in rcrit_sound) | if a universal domain of ψ is not included in the corresponding domain of φ, the entailment can fail | tight: `rcrit_univ_domain_tight` | one variable over Nat |
| h : RCrit incl meets impl φ ψ, ExDomainsCovariant (in rcrit_sound) | if an existential domain of φ is not included in the corresponding domain of ψ, the entailment can fail | tight: `rcrit_ex_domain_tight` | one variable over Nat |
| h : RCrit incl meets impl φ ψ, InstantiatedDomainsMeet (in rcrit_sound) | if the domains of a variable universal in φ and existential in ψ do not overlap, the entailment can fail | tight: `rcrit_meet_tight` | one variable over Nat |
| h : RCrit incl meets impl φ ψ, PremiseContravariant (in rcrit_sound) | if the premise of ψ does not imply that of φ, the entailment can fail | tight: `rcrit_premise_tight` | one variable over Nat |
| hα : α → False (in rEntails_of_isEmpty) | over an inhabited base type the conclusion fails for ∃x versus ∀x | tight: `rEntails_of_isEmpty_tight` | Nat, one variable |
| (∀ b ∈ pre, ∃ a, I b.dom a) — every domain of the prefix is nonempty (in evalR_premise_pull_out) | an empty existential domain makes the left side false while the right side holds when the premise is false | tight: `evalR_premise_pull_out_hne_tight` | one existential variable over Nat with empty domain |
| (∀ b ∈ pre, ∀ σ a, H (upd σ b.var a) ↔ H σ) — the premise does not depend on the variables bound in the prefix (in evalR_premise_pull_out) | a premise on an existential variable can be falsified by the witness | tight: `evalR_premise_pull_out_hind_tight` | one existential variable over Nat with premise x ≤ 1 |

**Non-vacuity.** ∃y ∈ {0,1} ∀x ∈ Nat (⊤ → M) entails ∀x ∈ Nat ∃y ∈ {0,1} (x ≤ 1 ∧ y ≤ 1 → M) (reordered prefix, stronger premise that restricts x), and ∃y ∈ {0} ∀x ∈ Nat (⊤ → M) entails ∀x ∈ {0,1} ∃y ∈ {0,1} (⊤ → M) (shrunk universal domain, grown existential domain); in both the source holds for M = True and the target fails for M = False, so the entailments are not degenerate. Empty is empty (rEntails_of_isEmpty). For evalR_premise_pull_out: two variables over Nat, prefix ∃y ∈ {0,1}, premise x ≤ 1 on the variable x left free by the prefix (not true at every assignment). (`rcrit_sound_nonvacuous`, `rcrit_sound_nonvacuous_domains`, `sentailsAt_of_isEmpty_nonvacuous`, `evalR_premise_pull_out_nonvacuous`)

**Prior art.**

- M. Samer and S. Szeider, "Backdoor Sets of Quantified Boolean Formulas", Journal of Automated Reasoning 42(1):77-97, 2009, doi:10.1007/s10817-008-9114-5. Definition 2 (dependency schemes: the variables a variable may depend on can be shifted without changing the truth value of the formula, i.e. equivalence is preserved) and Definition 4 (the trivial dependency scheme relates every variable x, existential or universal, to all variables from the first later quantifier block of the other quantifier onward), checked in the authors' version. The trivial scheme therefore also constrains pairs with an existential variable before a universal one, as equivalence-preserving reordering requires. The criterion here constrains the pairs with a universal variable before an existential one, and no other pairs (the Skolem dependencies), because it characterizes one-way entailment, under which ∃y ∀x entails ∀x ∃y.
- F. Slivovsky and S. Szeider, "Quantifier Reordering for QBF", Journal of Automated Reasoning 56(4):459-477, 2016, doi:10.1007/s10817-015-9353-1 (dependency schemes used to reorder the prefix of a fixed formula while preserving its truth value; checked against the publisher's abstract). Related but different: that work preserves the truth of one formula; the result here characterizes one-way entailment between two prefixes over all matrices, including universal-to-existential weakening.
- S. A. Cook, "Soundness and completeness of an axiom system for program verification", SIAM J. Comput. 7(1):70-90, 1978, doi:10.1137/0207005 (completeness of Hoare logic relative to an oracle for the assertion theory under an expressiveness assumption: a standard example of a relativized completeness claim; record and abstract checked, full text not consulted). Cited as an example of a relative claim.

**Design question.** For relativized claim shapes (domains and a premise), is strength decidable by a syntactic criterion, and where does the syntactic criterion stop being complete?

**Non-claims.** Listed under **Boundaries → Non-claims → 13**.

### 14. `relativized-criterion-complete-polarized-two-point-premise-free`

Tier T1 · kind: theorem · depth: substantive

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** If no variable is bound twice in the prefix of φ or of ψ (a prefix may leave variables unbound; they take their values from the environment), the tables incl, meets, impl are exact for I, J (incl k k' = true iff I k ⊆ I k'; meets k k' = true iff I k and I k' share an element; impl p p' = true iff J p ⊆ J p'), the base type α is nonempty, every existential domain of φ and every universal domain of ψ has at least two elements, and both premises hold at every assignment, then REntails I J φ ψ implies RCrit incl meets impl φ ψ. If α is nonempty, every existential domain of φ and every universal domain of ψ has at least two elements, the premise of ψ holds at every assignment, and REntails I J φ ψ holds, then every domain of φ and of ψ is nonempty (nonempty_domains_of_rEntails).

**Tier.** Countermodel constructions generalize the unrelativized ones; mechanized here.

**Lean statements.**

**`rcrit_complete_polarized_two_point_premise_free`**
```lean
-- ClaimStrength/Complete.lean:434-442
theorem rcrit_complete_polarized_two_point_premise_free {I : K → α → Prop}
    {J : P → (Fin n → α) → Prop} {incl meets : K → K → Bool} {impl : P → P → Bool}
    {φ ψ : Shape n K P}
    (hφ : (bvars φ.pre).Nodup) (hψ : (bvars ψ.pre).Nodup) (hI : InclExact I incl)
    (hM : MeetsExact I meets) (hJ : ImplExact J impl) (hα : Nonempty α)
    (h2φ : ∀ b ∈ φ.pre, b.q = .ex → TwoPoint (I b.dom))
    (h2ψ : ∀ b ∈ ψ.pre, b.q = .all → TwoPoint (I b.dom))
    (hpφ : ∀ σ, J φ.prem σ) (hpψ : ∀ σ, J ψ.prem σ) (h : REntails I J φ ψ) :
    RCrit incl meets impl φ ψ
```

**`nonempty_domains_of_rEntails`**
```lean
-- ClaimStrength/Complete.lean:252-257
theorem nonempty_domains_of_rEntails {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
    {φ ψ : Shape n K P} (hα : Nonempty α)
    (h2φ : ∀ b ∈ φ.pre, b.q = .ex → TwoPoint (I b.dom))
    (h2ψ : ∀ b ∈ ψ.pre, b.q = .all → TwoPoint (I b.dom))
    (hpψ : ∀ σ, J ψ.prem σ) (h : REntails I J φ ψ) :
    (∀ b ∈ φ.pre, ∃ a, I b.dom a) ∧ (∀ b ∈ ψ.pre, ∃ a, I b.dom a)
```

Unfolded statement of `rcrit_complete_polarized_two_point_premise_free` (InclExact, MeetsExact, ImplExact, TwoPoint, REntails and Holds written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {n : Nat} {K P α : Type} {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
  {incl meets : K → K → Bool} {impl : P → P → Bool} {φ ψ : Shape n K P},
  (bvars φ.pre).Nodup → (bvars ψ.pre).Nodup →
  (∀ k k', incl k k' = true ↔ ∀ a, I k a → I k' a) →
  (∀ k k', meets k k' = true ↔ ∃ a, I k a ∧ I k' a) →
  (∀ p p', impl p p' = true ↔ ∀ σ, J p σ → J p' σ) →
  Nonempty α →
  (∀ b ∈ φ.pre, b.q = .ex → ∃ a a', a ≠ a' ∧ I b.dom a ∧ I b.dom a') →
  (∀ b ∈ ψ.pre, b.q = .all → ∃ a a', a ≠ a' ∧ I b.dom a ∧ I b.dom a') →
  (∀ σ, J φ.prem σ) → (∀ σ, J ψ.prem σ) →
  (∀ (M : (Fin n → α) → Prop) (ρ : Fin n → α),
    evalR I φ.pre (fun σ => J φ.prem σ → M σ) ρ → evalR I ψ.pre (fun σ => J ψ.prem σ → M σ) ρ) →
  RCrit incl meets impl φ ψ
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| hφ : (bvars φ.pre).Nodup (in rcrit_complete_polarized_two_point_premise_free) | with a repeated binder the criterion reads the shadowed first binder | tight: `rcrit_incomplete_not_wf` | one variable over Nat, φ = ∃x ∀x |
| hψ : (bvars ψ.pre).Nodup (in rcrit_complete_polarized_two_point_premise_free) | with a repeated binder the criterion reads the shadowed first binder | tight: `rcrit_incomplete_not_wf_target` | one variable over Nat, ψ = ∀x ∃x |
| hI : InclExact I incl (in rcrit_complete_polarized_two_point_premise_free) | a sound but inexact inclusion table misses true inclusions | tight: `rcrit_incomplete_inexact_incl` | one variable over Nat, table 'equal classes' |
| hM : MeetsExact I meets (in rcrit_complete_polarized_two_point_premise_free) | a sound but inexact overlap table misses true overlaps | tight: `rcrit_incomplete_inexact_meets` | one variable over Nat, table 'never' |
| hJ : ImplExact J impl (in rcrit_complete_polarized_two_point_premise_free) | a sound but inexact premise table misses true implications | tight: `rcrit_incomplete_inexact_impl` | one variable over Nat, table 'never' |
| hα : Nonempty α (in rcrit_complete_polarized_two_point_premise_free) | over an empty base type REntails holds vacuously while the overlap part fails | tight: `rcrit_complete_hα_tight` | the empty base type Empty, one variable |
| h2φ : ∀ b ∈ φ.pre, b.q = .ex → TwoPoint (I b.dom) (in rcrit_complete_polarized_two_point_premise_free) | with an empty or one-element existential domain in φ the entailment can hold while part (i) or (ii) fails | tight: `rcrit_incomplete_empty_domain`, `rcrit_incomplete_singleton_existential` | one variable over Nat with an empty existential domain; two variables over Nat with a singleton existential domain |
| h2ψ : ∀ b ∈ ψ.pre, b.q = .all → TwoPoint (I b.dom) (in rcrit_complete_polarized_two_point_premise_free) | with an empty or one-element universal domain in ψ the entailment can hold while part (i) or (ii) fails | tight: `rcrit_incomplete_empty_universal_domain`, `rcrit_incomplete_singleton_universal` | one variable over Nat with an empty universal domain; two variables over Nat with a singleton universal domain |
| hpφ : ∀ σ, J φ.prem σ (in rcrit_complete_polarized_two_point_premise_free) | a premise of φ can restrict a universal domain, or be implied by an existential domain | tight: `rcrit_incomplete_premise_as_domain`, `rcrit_incomplete_redundant_existential_premise` | one variable over Nat (universal and existential binder respectively) |
| hpψ : ∀ σ, J ψ.prem σ (in rcrit_complete_polarized_two_point_premise_free) | a premise of ψ can restrict a universal domain, be unsatisfiable, or constrain an existential variable and so make ψ valid | tight: `rcrit_incomplete_target_premise_as_domain`, `rcrit_incomplete_false_target_premise`, `rcrit_incomplete_target_premise_on_existential` | one variable over Nat (first two); two variables over Nat (third) |
| h : REntails I J φ ψ (in rcrit_complete_polarized_two_point_premise_free) | without the entailment the criterion can fail | tight: `rcrit_complete_hE_tight` | one variable over Nat |
| hα : Nonempty α (in nonempty_domains_of_rEntails) | over an empty base type every domain is empty while REntails holds vacuously | tight: `nonempty_domains_hα_tight` | the empty base type Empty, one variable (φ = ∀x, ψ = ∃x) |
| h2φ : ∀ b ∈ φ.pre, b.q = .ex → TwoPoint (I b.dom) (in nonempty_domains_of_rEntails) | an empty existential domain makes φ unsatisfiable, so φ entails ψ | tight: `nonempty_domains_h2φ_tight` | one variable over Nat, φ = ∃x ∈ ∅, ψ = ∀x ∈ {0,1} |
| h2ψ : ∀ b ∈ ψ.pre, b.q = .all → TwoPoint (I b.dom) (in nonempty_domains_of_rEntails) | an empty universal domain makes ψ valid, so φ entails ψ | tight: `nonempty_domains_h2ψ_tight` | one variable over Nat, φ = ∃x ∈ {0,1}, ψ = ∀x ∈ ∅ |
| hpψ : ∀ σ, J ψ.prem σ (in nonempty_domains_of_rEntails) | an unsatisfiable premise makes ψ valid, so a φ with an empty universal domain entails ψ | tight: `nonempty_domains_hpψ_tight` | one variable over Nat, φ = ∀x ∈ ∅ (⊤ → M), ψ = ∀x ∈ Nat (⊥ → M) |
| h : REntails I J φ ψ (in nonempty_domains_of_rEntails) | without the entailment, φ may have an empty universal domain | tight: `nonempty_domains_hE_tight` | one variable over Nat, φ = ∀x ∈ ∅, ψ = ∀x ∈ {0,1} |

**Non-vacuity.** ∃y ∈ {0,1} ∀x ∈ Nat versus ∀x ∈ {0,1} ∃y ∈ Nat, both premises ⊤, base type Nat with exact tables: every hypothesis of both theorems holds, and the target fails for M = False. A second instance leaves a variable unbound: φ = ∀x ∈ Nat versus the empty prefix ψ (x free); every hypothesis holds although ψ is not well formed, and the entailment and the criterion hold. (`rcrit_complete_nonvacuous`, `rcrit_complete_nonvacuous_free_variable`)

**Prior art.**

- M. Samer and S. Szeider, "Backdoor Sets of Quantified Boolean Formulas", Journal of Automated Reasoning 42(1):77-97, 2009, doi:10.1007/s10817-008-9114-5. Definition 2 (dependency schemes: the variables a variable may depend on can be shifted without changing the truth value of the formula, i.e. equivalence is preserved) and Definition 4 (the trivial dependency scheme relates every variable x, existential or universal, to all variables from the first later quantifier block of the other quantifier onward), checked in the authors' version. The trivial scheme therefore also constrains pairs with an existential variable before a universal one, as equivalence-preserving reordering requires. The criterion here constrains the pairs with a universal variable before an existential one, and no other pairs (the Skolem dependencies), because it characterizes one-way entailment, under which ∃y ∀x entails ∀x ∃y.

**Design question.** For relativized claim shapes (domains and a premise), is strength decidable by a syntactic criterion, and where does the syntactic criterion stop being complete?

**Non-claims.** Listed under **Boundaries → Non-claims → 14**.

### 15. `relativized-criterion-incomplete-outside-fragment`

Tier T1 · kind: counterexample · depth: shallow

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** Outside the fragment of the completeness theorem the combined criterion is not complete. Over the base type Nat with the exact tables clsIncl, clsMeets, premImpl there are shapes for which the entailment holds for every matrix but the criterion fails, caused by: an empty or singleton existential domain in φ; an empty or singleton universal domain in ψ; a singleton domain on both sides (also with both shapes in normal form); a premise of φ that restricts a universal domain or is implied by an existential domain; a premise of ψ that restricts a universal domain, is unsatisfiable, or constrains an existential variable (making ψ valid); a repeated binder in φ or in ψ. Over Nat, with two-point domains, trivial premises and shapes without repeated binders, replacing one exact table by a sound but inexact one (inclusion 'equal classes', overlap 'never', implication 'never') also breaks completeness. Over the empty base type, with exact tables, ∀x entails ∃x vacuously while the criterion fails.

**Tier.** Each failure is elementary; collected and kernel-checked.

**Lean statements.**

**`rcrit_incomplete_empty_domain`**
```lean
-- ClaimStrength/RelResults.lean:447-456
theorem rcrit_incomplete_empty_domain :
    (bvars ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    ¬ (∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .empty⟩], .top⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .empty⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩
```

**`rcrit_incomplete_singleton_existential`**
```lean
-- ClaimStrength/RelResults.lean:469-483
theorem rcrit_incomplete_singleton_existential :
    (bvars ([⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zero⟩] : List (Binder 2 Cls))).Nodup ∧
    (bvars ([⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zeroOne⟩] : List (Binder 2 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 1) premImpl ∧
    Nonempty Nat ∧
    ¬ (∀ b ∈ ([⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zero⟩] : List (Binder 2 Cls)), b.q = .ex →
      TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zeroOne⟩] : List (Binder 2 Cls)), b.q = .all →
      TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 1 .top σ) ∧ (∀ σ, premJ 1 .top σ) ∧
    REntails clsI (premJ 1) ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zero⟩], .top⟩
      ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zero⟩], .top⟩ : Shape 2 Cls Prem)
      ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zeroOne⟩], .top⟩
```

**`rcrit_incomplete_empty_universal_domain`**
```lean
-- ClaimStrength/RelResults.lean:498-507
theorem rcrit_incomplete_empty_universal_domain :
    (bvars ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .empty⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .empty⟩], .top⟩
```

**`rcrit_incomplete_singleton_universal`**
```lean
-- ClaimStrength/RelResults.lean:518-532
theorem rcrit_incomplete_singleton_universal :
    (bvars ([⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩] : List (Binder 2 Cls))).Nodup ∧
    (bvars ([⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zero⟩] : List (Binder 2 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 1) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩] : List (Binder 2 Cls)), b.q = .ex →
      TwoPoint (clsI b.dom)) ∧
    ¬ (∀ b ∈ ([⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zero⟩] : List (Binder 2 Cls)), b.q = .all →
      TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 1 .top σ) ∧ (∀ σ, premJ 1 .top σ) ∧
    REntails clsI (premJ 1) ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩], .top⟩
      ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zero⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩], .top⟩ : Shape 2 Cls Prem)
      ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zero⟩], .top⟩
```

**`rcrit_incomplete_singleton_domain`**
```lean
-- ClaimStrength/RelResults.lean:550-556
theorem rcrit_incomplete_singleton_domain :
    (bvars ([⟨.ex, 0, .zero⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    ¬ TwoPoint (clsI .zero) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zero⟩], .top⟩ ⟨[⟨.all, 0, .zero⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zero⟩], .top⟩
```

**`rcrit_incomplete_in_normal_form`**
```lean
-- ClaimStrength/RelResults.lean:569-574
theorem rcrit_incomplete_in_normal_form :
    ShapeNF clsMeets (⟨[⟨.ex, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) ∧
    ShapeNF clsMeets (⟨[⟨.all, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zero⟩], .top⟩ ⟨[⟨.all, 0, .zero⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zero⟩], .top⟩
```

**`rcrit_incomplete_premise_as_domain`**
```lean
-- ClaimStrength/RelResults.lean:583-592
theorem rcrit_incomplete_premise_as_domain :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ σ, premJ 0 .atMostOne σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .all⟩], .atMostOne⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩
```

**`rcrit_incomplete_redundant_existential_premise`**
```lean
-- ClaimStrength/RelResults.lean:605-614
theorem rcrit_incomplete_redundant_existential_premise :
    (bvars ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ σ, premJ 0 .atMostOne σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zeroOne⟩], .atMostOne⟩ ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .zeroOne⟩], .atMostOne⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩
```

**`rcrit_incomplete_target_premise_as_domain`**
```lean
-- ClaimStrength/RelResults.lean:628-637
theorem rcrit_incomplete_target_premise_as_domain :
    (bvars ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ ¬ (∀ σ, premJ 0 .atMostOne σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .atMostOne⟩
```

**`rcrit_incomplete_false_target_premise`**
```lean
-- ClaimStrength/RelResults.lean:649-658
theorem rcrit_incomplete_false_target_premise :
    (bvars ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ ¬ (∀ σ, premJ 0 .bot σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .bot⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .bot⟩
```

**`rcrit_incomplete_target_premise_on_existential`**
```lean
-- ClaimStrength/RelResults.lean:669-683
theorem rcrit_incomplete_target_premise_on_existential :
    (bvars ([⟨.ex, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))).Nodup ∧
    (bvars ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 1) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls)), b.q = .ex →
      TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls)), b.q = .all →
      TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 1 .top σ) ∧ ¬ (∀ σ, premJ 1 .atMostOne σ) ∧
    REntails clsI (premJ 1) ⟨[⟨.ex, 0, .all⟩, ⟨.ex, 1, .all⟩], .top⟩
      ⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩], .atMostOne⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩, ⟨.ex, 1, .all⟩], .top⟩ : Shape 2 Cls Prem)
      ⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩], .atMostOne⟩
```

**`rcrit_incomplete_not_wf`**
```lean
-- ClaimStrength/RelResults.lean:753-764
theorem rcrit_incomplete_not_wf :
    ¬ (bvars ([⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex →
      TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_incomplete_not_wf_target`**
```lean
-- ClaimStrength/RelResults.lean:778-789
theorem rcrit_incomplete_not_wf_target :
    (bvars ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    ¬ (bvars ([⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all →
      TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩], .top⟩
```

**`rcrit_incomplete_inexact_incl`**
```lean
-- ClaimStrength/RelResults.lean:696-705
theorem rcrit_incomplete_inexact_incl :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧
    InclSound clsI (fun k k' => decide (k = k')) ∧ ¬ InclExact clsI (fun k k' => decide (k = k')) ∧
    MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧ Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit (fun k k' => decide (k = k')) clsMeets premImpl
      (⟨[⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩
```

**`rcrit_incomplete_inexact_meets`**
```lean
-- ClaimStrength/RelResults.lean:715-725
theorem rcrit_incomplete_inexact_meets :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧
    MeetsSound clsI (fun _ _ => false) ∧ ¬ MeetsExact clsI (fun _ _ => false) ∧
    ImplExact (premJ 0) premImpl ∧ Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .top⟩ ⟨[⟨.ex, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl (fun _ _ => false) premImpl
      (⟨[⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .all⟩], .top⟩
```

**`rcrit_incomplete_inexact_impl`**
```lean
-- ClaimStrength/RelResults.lean:735-745
theorem rcrit_incomplete_inexact_impl :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧
    ImplSound (premJ 0) (fun _ _ => false) ∧ ¬ ImplExact (premJ 0) (fun _ _ => false) ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets (fun _ _ => false)
      (⟨[⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_complete_hα_tight`**
```lean
-- ClaimStrength/RelResults.lean:815-823
theorem rcrit_complete_hα_tight :
    (bvars emptyφ.pre).Nodup ∧ (bvars emptyψ.pre).Nodup ∧ InclExact emptyI (fun _ _ => true) ∧
    MeetsExact emptyI (fun _ _ => false) ∧ ImplExact emptyJ (fun _ _ => true) ∧
    ¬ Nonempty Empty ∧
    (∀ b ∈ emptyφ.pre, b.q = .ex → TwoPoint (emptyI b.dom)) ∧
    (∀ b ∈ emptyψ.pre, b.q = .all → TwoPoint (emptyI b.dom)) ∧
    (∀ σ, emptyJ emptyφ.prem σ) ∧ (∀ σ, emptyJ emptyψ.prem σ) ∧
    REntails emptyI emptyJ emptyφ emptyψ ∧
    ¬ RCrit (fun _ _ => true) (fun _ _ => false) (fun _ _ => true) emptyφ emptyψ
```

**Hypothesis ledger.** None of the theorems of this card has a hypothesis.

**Non-vacuity.** Each listed theorem exhibits its instance. (`rcrit_incomplete_empty_domain`)

**Prior art.**

- No specific prior statement located; elementary consequence of the definitions.

**Design question.** For relativized claim shapes (domains and a premise), is strength decidable by a syntactic criterion, and where does the syntactic criterion stop being complete?

**Non-claims.** Listed under **Boundaries → Non-claims → 15**.

### 16. `frontier-testing-detects-overreading-for-closed-readers`

Tier T1 · kind: theorem · depth: shallow

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

**Plain claim.** For a report E, a finite candidate list Q, and a reader's endorsement predicate End: if q is unsupported and q' entails q, then q' is unsupported; every nonempty list of claims has an entailment-weakest element; if q ∈ Q is unsupported, it entails some frontier candidate (a weakest unsupported candidate); and if End is closed under entailment among the candidates and endorses no frontier candidate, then every candidate End endorses is supported, so answering 'supported' for an endorsed candidate is never a positive over-reading. Undetermined claims are not closed upward in strength; every End treats logically equivalent claims alike; and the test says nothing about claims outside Q.

**Tier.** Minimal elements of a finite preorder applied to unsupported claims; the closure assumption and its countermodel are made precise here.

**Lean statements.**

**`unsupported_of_entails`**
```lean
-- ClaimStrength/Frontier.lean:28-29
theorem unsupported_of_entails {E : List (Claim W)} {q q' : Claim W}
    (h : ¬ Supported E q) (h' : Entails q' q) : ¬ Supported E q'
```

**`exists_weakest`**
```lean
-- ClaimStrength/Frontier.lean:33-34
theorem exists_weakest :
    ∀ (L : List (Claim W)), L ≠ [] → ∃ m ∈ L, ∀ x ∈ L, Entails m x → Entails x m
```

**`exists_frontier_below`**
```lean
-- ClaimStrength/Frontier.lean:51-52
theorem exists_frontier_below {E Q : List (Claim W)} {q : Claim W} (hq : q ∈ Q)
    (hns : ¬ Supported E q) : ∃ q', Frontier E Q q' ∧ Entails q q'
```

**`frontier_test_detects_overreading`**
```lean
-- ClaimStrength/Frontier.lean:65-67
theorem frontier_test_detects_overreading {E Q : List (Claim W)} {End : Claim W → Prop}
    (hclosed : ClosedUnderEntailmentIn Q End) (hfront : ∀ q, Frontier E Q q → ¬ End q) :
    ∀ q ∈ Q, End q → Supported E q
```

**`frontier_test_no_positiveOverReading`**
```lean
-- ClaimStrength/Frontier.lean:183-185
theorem frontier_test_no_positiveOverReading {E Q : List (Claim W)} {End : Claim W → Prop}
    (hclosed : ClosedUnderEntailmentIn Q End) (hfront : ∀ q, Frontier E Q q → ¬ End q) :
    ∀ q ∈ Q, End q → ¬ PositiveOverReading E q .supported
```

**`undetermined_not_upward_closed`**
```lean
-- ClaimStrength/Frontier.lean:190-193
theorem undetermined_not_upward_closed :
    Undetermined [fun n : Nat => n ≤ 1] (fun n => n = 0) ∧
    Entails (fun _ : Nat => False) (fun n => n = 0) ∧
    ¬ Undetermined [fun n : Nat => n ≤ 1] (fun _ => False)
```

**`endorsement_respects_equivalence`**
```lean
-- ClaimStrength/Frontier.lean:198-199
theorem endorsement_respects_equivalence (End : Claim W → Prop) {q₁ q₂ : Claim W}
    (h₁ : Entails q₁ q₂) (h₂ : Entails q₂ q₁) : End q₁ ↔ End q₂
```

**`frontier_test_outside_candidates`**
```lean
-- ClaimStrength/Frontier.lean:206-209
theorem frontier_test_outside_candidates :
    ClosedUnderEntailmentIn [qTriv] (fun q => q = qStrong) ∧
    (∀ q, Frontier [] [qTriv] q → ¬ (fun q => q = qStrong) q) ∧
    qStrong ∉ [qTriv] ∧ ¬ Supported ([] : List (Claim Nat)) qStrong
```

Unfolded statement of `frontier_test_detects_overreading` (ClosedUnderEntailmentIn and Frontier written out), with every binder explicit; it elaborates in the namespace `Toy.ClaimStrength` and is definitionally equal to the quoted statement:

```lean
∀ {W : Type} {E Q : List (Claim W)} {End : Claim W → Prop},
  (∀ q ∈ Q, ∀ q' ∈ Q, End q → Entails q q' → End q') →
  (∀ q, (q ∈ Q ∧ ¬ Supported E q ∧ ∀ q' ∈ Q, ¬ Supported E q' → Entails q q' → Entails q' q) →
    ¬ End q) →
  ∀ q ∈ Q, End q → Supported E q
```

**Hypothesis ledger.** A `tight` entry names a theorem stating that every other hypothesis of the named theorem holds and its conclusion fails, in the witness class shown.

| Hypothesis | Without it | Status | Witness class |
| :--- | :--- | :--- | :--- |
| h : ¬ Supported E q (in unsupported_of_entails) | if q is supported, a stronger claim can be supported too | tight: `unsupported_of_entails_h_tight` | the empty report over Nat |
| h' : Entails q' q (in unsupported_of_entails) | a claim that does not entail q can be supported although q is not | tight: `unsupported_of_entails_h'_tight` | the empty report over Nat |
| L ≠ [] (in exists_weakest) | the empty list has no element | tight: `exists_weakest_tight` | the empty list of claims over Nat |
| hq : q ∈ Q (in exists_frontier_below) | for a claim outside Q no frontier candidate below it need exist | tight: `exists_frontier_below_hq_tight` | a one-candidate list over Nat, empty report |
| hns : ¬ Supported E q (in exists_frontier_below) | a supported claim entails no unsupported claim | tight: `exists_frontier_below_hns_tight` | three candidates over Nat, empty report |
| hclosed : ClosedUnderEntailmentIn Q End (in frontier_test_detects_overreading) | a reader who endorses a strong claim without its weaker consequences can avoid the frontier | tight: `frontier_test_hclosed_tight` | three candidates over Nat, empty report |
| hfront : ∀ q, Frontier E Q q → ¬ End q (in frontier_test_detects_overreading) | a closed reader that endorses a frontier candidate endorses an unsupported candidate | tight: `frontier_test_hfront_tight` | three candidates over Nat, empty report |
| hclosed : ClosedUnderEntailmentIn Q End (in frontier_test_no_positiveOverReading) | a reader who endorses a strong claim without its weaker consequences can avoid the frontier | tight: `frontier_test_hclosed_tight` | three candidates over Nat, empty report |
| hfront : ∀ q, Frontier E Q q → ¬ End q (in frontier_test_no_positiveOverReading) | a closed reader that endorses a frontier candidate endorses an unsupported candidate | tight: `frontier_test_hfront_tight` | three candidates over Nat, empty report |
| h₁ : Entails q₁ q₂ (in endorsement_respects_equivalence) | a predicate can separate claims that are not equivalent | tight: `endorsement_respects_equivalence_h₁_tight` | claims over Nat: q₁ = qWeak (n ≠ 0), q₂ = qStrong (n = 1) |
| h₂ : Entails q₂ q₁ (in endorsement_respects_equivalence) | a predicate can separate claims that are not equivalent | tight: `endorsement_respects_equivalence_h₂_tight` | claims over Nat: q₁ = qStrong (n = 1), q₂ = qWeak (n ≠ 0) |

**Non-vacuity.** Empty report over Nat, candidates [n = 1, n ≠ 0, True], frontier {n ≠ 0}; the reader endorsing exactly the supported candidates satisfies both hypotheses. (`frontier_test_nonvacuous`, `unsupported_of_entails_nonvacuous`, `exists_frontier_below_nonvacuous`, `exists_weakest_nonvacuous`, `endorsement_respects_equivalence_nonvacuous`)

**Prior art.**

- T. M. Mitchell, "Generalization as search", Artificial Intelligence 18(2):203-226, 1982, doi:10.1016/0004-3702(82)90040-6 (a version space of hypotheses ordered by generality is represented by its boundary sets of maximally general and maximally specific members; the frontier here is the analogous boundary of the unsupported candidates under entailment).
- L. R. Horn, "Toward a new taxonomy for pragmatic inference: Q-based and R-based implicature", in D. Schiffrin (ed.), Meaning, Form, and Use in Context: Linguistic Applications (GURT 1984), Georgetown University Press, 1984, pp. 11-42 (distinguishes Q-based, upper-bounding implicature, where a weaker statement suggests the stronger one fails, from R-based enrichment, where a statement is read as a stronger, stereotypical proposition; bibliographic record and summary from secondary sources). Cited as prose motivation: the strengthening drifts here resemble R-based enrichment, not Quantity.

**Design question.** Which comprehension questions detect over-reading most efficiently?

**Non-claims.** Listed under **Boundaries → Non-claims → 16**.

### Design consequences

Basis: derived (modeling bridge). Each bullet applies the cited theorems to a summary sentence or an answer key under one modeling assumption: the summary, the result and each comprehension question are represented as claims or claim shapes over the same, aligned variables, and a report is represented by the list of claims it establishes. That representation step is not formalized, so each bullet holds for a real report to the extent that the representation is faithful.

- A summary sentence and the result it summarizes can be compared mechanically when both are put in prefix form over the same, aligned variables. If no variable is bound twice in the result's prefix and every variable is bound exactly once in the summary's prefix, then at every base type with two distinct elements `prefixCritB` decides whether the result entails the summary for every matrix (`sentailsAt_iff_prefixCritB_of_two_point_nodup_wf`). For relativized forms (domains, one premise) whose prefixes bind every variable exactly once, with sound tables `incl`, `meets`, `impl`, a `true` verdict of `rcritB` implies entailment (`rcrit_sound`, `rcritB_iff`). A `false` verdict on the relativized form is not a proof of over-reading when premises are nontrivial, domains may be empty or have one element, or a prefix binds a variable twice (card 15). Constraints on existential witnesses belong in binder domains, not in the premise (`holds_premise_on_existential_trivial`).
- Comprehension questions aimed at over-reading can ask for the weakest unsupported strengthenings of each established claim (the frontier), phrased at the object level (for every report, a world-independent question, such as a question about what the report establishes, is never undetermined: `worldIndependent_not_undetermined`) and one claim per question (in the cell (undetermined, undetermined) the compound answer is not determined by the component answers: `andTable_undetermined_cell_distinct`). The frontier test detects positive over-reading when the reader's endorsements are closed under entailment among the candidates (`frontier_test_detects_overreading`; without closure it can miss over-reading: `frontier_test_hclosed_tight`); real readers may violate this assumption.
- An answer key can give "contradicted" for "the report establishes q" when q is unsupported (`establishes_contradicted_of_unsupported`), and "undetermined" for the object-level q exactly when q is undetermined, that is, unsupported and consistent with the report (`undetermined_iff_exists_both`).

### Auxiliary lemmas cited by name

Proved companion theorems that the non-claims cite by name. Each is listed in `results.json` (`lean_names`), so its statement and closure hashes are recorded under **Evidence**.

**`sentailsAt_iff_fixed_env_of_covers`**
```lean
-- ClaimStrength/PrefixResults.lean:91-93
theorem sentailsAt_iff_fixed_env_of_covers {φ ψ : Prefix n} (hφ : ∀ v : Fin n, v ∈ bvars φ)
    (hψ : ∀ v : Fin n, v ∈ bvars ψ) (ρ₀ : Fin n → α) :
    SEntailsAt α φ ψ ↔ ∀ R : (Fin n → α) → Prop, eval φ R ρ₀ → eval ψ R ρ₀
```

**`rcrit_complete_of_nonempty_domains`**
```lean
-- ClaimStrength/Complete.lean:285-293
theorem rcrit_complete_of_nonempty_domains {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
    {incl meets : K → K → Bool} {impl : P → P → Bool} {φ ψ : Shape n K P}
    (hφ : (bvars φ.pre).Nodup) (hψ : (bvars ψ.pre).Nodup) (hI : InclExact I incl)
    (hM : MeetsExact I meets) (hJ : ImplExact J impl)
    (hneφ : ∀ b ∈ φ.pre, ∃ a, I b.dom a) (hneψ : ∀ b ∈ ψ.pre, ∃ a, I b.dom a)
    (h2φ : ∀ b ∈ φ.pre, b.q = .ex → TwoPoint (I b.dom))
    (h2ψ : ∀ b ∈ ψ.pre, b.q = .all → TwoPoint (I b.dom))
    (hpφ : ∀ σ, J φ.prem σ) (hpψ : ∀ σ, J ψ.prem σ) (h : REntails I J φ ψ) :
    RCrit incl meets impl φ ψ
```

**`rcrit_complete_two_point_premise_free`**
```lean
-- ClaimStrength/Complete.lean:450-456
theorem rcrit_complete_two_point_premise_free {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
    {incl meets : K → K → Bool} {impl : P → P → Bool} {φ ψ : Shape n K P}
    (hφ : (bvars φ.pre).Nodup) (hψ : (bvars ψ.pre).Nodup) (hI : InclExact I incl)
    (hM : MeetsExact I meets) (hJ : ImplExact J impl)
    (h2φ : ∀ b ∈ φ.pre, TwoPoint (I b.dom)) (h2ψ : ∀ b ∈ ψ.pre, TwoPoint (I b.dom))
    (hpφ : ∀ σ, J φ.prem σ) (hpψ : ∀ σ, J ψ.prem σ) (h : REntails I J φ ψ) :
    RCrit incl meets impl φ ψ
```

**`evalR_of_valid`**
```lean
-- ClaimStrength/Complete.lean:174-176
theorem evalR_of_valid (I : K → α → Prop) {L : (Fin n → α) → Prop} (hL : ∀ σ, L σ) :
    ∀ (φ : List (Binder n K)) (ρ : Fin n → α), (∀ b ∈ φ, b.q = .ex → ∃ a, I b.dom a) →
      evalR I φ L ρ
```

### Statements of counterexamples, non-vacuity witnesses and positive controls (verbatim)

**`exactlyOne_nonvacuous`**
```lean
-- ClaimStrength/Basic.lean:469-472
theorem exactlyOne_nonvacuous :
    ExactlyOne3 (Supported [fun n : Nat => n ≤ 1] (fun n => n = 0))
      (Contradicted [fun n : Nat => n ≤ 1] (fun n => n = 0))
      (Undetermined [fun n : Nat => n ≤ 1] (fun n => n = 0))
```

**`unsatisfiable_nonvacuous`**
```lean
-- ClaimStrength/Basic.lean:238
theorem unsatisfiable_nonvacuous : ¬ Satisfiable [fun _ : Nat => False]
```

**`correct_unique_nonvacuous`**
```lean
-- ClaimStrength/Basic.lean:309-311
theorem correct_unique_nonvacuous :
    Satisfiable [fun n : Nat => n ≤ 1] ∧
    Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined
```

**`unsatisfiable_hE_tight`**
```lean
-- ClaimStrength/Basic.lean:230-233
theorem unsatisfiable_hE_tight :
    Satisfiable ([] : List (Claim Nat)) ∧
    ¬ (Supported ([] : List (Claim Nat)) (fun _ => True) ∧
      Contradicted ([] : List (Claim Nat)) (fun _ => True))
```

**`correct_unique_hE_tight`**
```lean
-- ClaimStrength/Basic.lean:276-280
theorem correct_unique_hE_tight :
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Correct [fun _ : Nat => False] (fun _ => True) .supported ∧
    Correct [fun _ : Nat => False] (fun _ => True) .contradicted ∧
    Answer.supported ≠ Answer.contradicted
```

**`correct_unique_ha_tight`**
```lean
-- ClaimStrength/Basic.lean:289-293
theorem correct_unique_ha_tight :
    Satisfiable [fun n : Nat => n ≤ 1] ∧
    ¬ Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .supported ∧
    Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined ∧
    Answer.supported ≠ Answer.undetermined
```

**`correct_unique_hb_tight`**
```lean
-- ClaimStrength/Basic.lean:300-304
theorem correct_unique_hb_tight :
    Satisfiable [fun n : Nat => n ≤ 1] ∧
    Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined ∧
    ¬ Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .supported ∧
    Answer.undetermined ≠ Answer.supported
```

**`answer_changes_nonvacuous`**
```lean
-- ClaimStrength/Basic.lean:459-463
theorem answer_changes_nonvacuous :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n = 0]) ∧
    Satisfiable [fun n : Nat => n = 0] ∧
    Correct ([] : List (Claim Nat)) (fun n => n = 0) .undetermined ∧
    Correct [fun n : Nat => n = 0] (fun n => n = 0) .supported
```

**`mono_nonvacuous`**
```lean
-- ClaimStrength/Basic.lean:391-394
theorem mono_nonvacuous :
    (∀ e ∈ [fun n : Nat => n = 0], e ∈ [fun n : Nat => n = 0, fun n => n ≤ 5]) ∧
    Supported [fun n : Nat => n = 0] (fun n => n ≤ 1) ∧
    Contradicted [fun n : Nat => n = 0] (fun n => n = 1)
```

**`supported_mono_hsub_tight`**
```lean
-- ClaimStrength/Basic.lean:356-359
theorem supported_mono_hsub_tight :
    ¬ (∀ e ∈ [fun n : Nat => n = 0], e ∈ ([] : List (Claim Nat))) ∧
    Supported [fun n : Nat => n = 0] (fun n => n = 0) ∧
    ¬ Supported ([] : List (Claim Nat)) (fun n => n = 0)
```

**`supported_mono_h_tight`**
```lean
-- ClaimStrength/Basic.lean:375-378
theorem supported_mono_h_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n ≤ 1]) ∧
    ¬ Supported ([] : List (Claim Nat)) (fun n => n = 0) ∧
    ¬ Supported [fun n : Nat => n ≤ 1] (fun n => n = 0)
```

**`contradicted_mono_hsub_tight`**
```lean
-- ClaimStrength/Basic.lean:366-369
theorem contradicted_mono_hsub_tight :
    ¬ (∀ e ∈ [fun n : Nat => n = 0], e ∈ ([] : List (Claim Nat))) ∧
    Contradicted [fun n : Nat => n = 0] (fun n => n = 1) ∧
    ¬ Contradicted ([] : List (Claim Nat)) (fun n => n = 1)
```

**`contradicted_mono_h_tight`**
```lean
-- ClaimStrength/Basic.lean:383-386
theorem contradicted_mono_h_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n ≤ 1]) ∧
    ¬ Contradicted ([] : List (Claim Nat)) (fun n => n = 0) ∧
    ¬ Contradicted [fun n : Nat => n ≤ 1] (fun n => n = 0)
```

**`answer_changes_hsub_tight`**
```lean
-- ClaimStrength/Basic.lean:411-416
theorem answer_changes_hsub_tight :
    ¬ (∀ e ∈ [fun n : Nat => n = 0], e ∈ ([] : List (Claim Nat))) ∧
    Satisfiable ([] : List (Claim Nat)) ∧
    Correct [fun n : Nat => n = 0] (fun n => n = 0) .supported ∧
    Correct ([] : List (Claim Nat)) (fun n => n = 0) .undetermined ∧
    ¬ ((Answer.undetermined = .supported) ∨ (Answer.supported = .undetermined))
```

**`answer_changes_hsat_tight`**
```lean
-- ClaimStrength/Basic.lean:424-429
theorem answer_changes_hsat_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun _ : Nat => False]) ∧
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Correct ([] : List (Claim Nat)) (fun _ => True) .supported ∧
    Correct [fun _ : Nat => False] (fun _ => True) .contradicted ∧
    ¬ ((Answer.contradicted = .supported) ∨ (Answer.supported = .undetermined))
```

**`answer_changes_ha_tight`**
```lean
-- ClaimStrength/Basic.lean:436-441
theorem answer_changes_ha_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n = 0]) ∧
    Satisfiable [fun n : Nat => n = 0] ∧
    ¬ Correct ([] : List (Claim Nat)) (fun n => n = 0) .contradicted ∧
    Correct [fun n : Nat => n = 0] (fun n => n = 0) .supported ∧
    ¬ ((Answer.supported = .contradicted) ∨ (Answer.contradicted = .undetermined))
```

**`answer_changes_ha'_tight`**
```lean
-- ClaimStrength/Basic.lean:448-453
theorem answer_changes_ha'_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n = 0]) ∧
    Satisfiable [fun n : Nat => n = 0] ∧
    Correct ([] : List (Claim Nat)) (fun _ => True) .supported ∧
    ¬ Correct [fun n : Nat => n = 0] (fun _ => True) .contradicted ∧
    ¬ ((Answer.contradicted = .supported) ∨ (Answer.supported = .undetermined))
```

**`contradicted_of_mem_nonvacuous`**
```lean
-- ClaimStrength/Basic.lean:522-524
theorem contradicted_of_mem_nonvacuous :
    (fun P : Nat → Prop => ¬ P 0) ∈ [fun P : Nat → Prop => ¬ P 0] ∧
    Entails (fun P : Nat → Prop => ¬ P 0) (fun P => ¬ (∀ m, P m))
```

**`undetermined_example_pos`**
```lean
-- ClaimStrength/Basic.lean:134
theorem undetermined_example_pos : Undetermined [fun n : Nat => n ≤ 1] (fun n => n = 0)
```

**`contradicted_of_mem_hc_tight`**
```lean
-- ClaimStrength/Basic.lean:504-507
theorem contradicted_of_mem_hc_tight :
    (fun P : Nat → Prop => ¬ P 0) ∉ ([] : List (Claim (Nat → Prop))) ∧
    Entails (fun P : Nat → Prop => ¬ P 0) (fun P => ¬ (∀ m, P m)) ∧
    ¬ Contradicted ([] : List (Claim (Nat → Prop))) (fun P => ∀ m, P m)
```

**`contradicted_of_mem_hneg_tight`**
```lean
-- ClaimStrength/Basic.lean:514-517
theorem contradicted_of_mem_hneg_tight :
    (fun P : Nat → Prop => P 0) ∈ [fun P : Nat → Prop => P 0] ∧
    ¬ Entails (fun P : Nat → Prop => P 0) (fun P => ¬ (∀ m, P m)) ∧
    ¬ Contradicted [fun P : Nat → Prop => P 0] (fun P => ∀ m, P m)
```

**`unsupported_of_contradicted_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:281-282
theorem unsupported_of_contradicted_nonvacuous :
    Contradicted [fun n : Nat => n = 0] (fun n => n = 1) ∧ Satisfiable [fun n : Nat => n = 0]
```

**`unsupported_of_contradicted_hc_tight`**
```lean
-- ClaimStrength/Drift.lean:275-277
theorem unsupported_of_contradicted_hc_tight :
    Satisfiable ([] : List (Claim Nat)) ∧ ¬ Contradicted ([] : List (Claim Nat)) (fun _ => True) ∧
    Supported ([] : List (Claim Nat)) (fun _ => True)
```

**`unsupported_of_contradicted_hE_tight`**
```lean
-- ClaimStrength/Drift.lean:266-269
theorem unsupported_of_contradicted_hE_tight :
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Contradicted [fun _ : Nat => False] (fun _ => True) ∧
    Supported [fun _ : Nat => False] (fun _ => True)
```

**`establishes_answer_key_nonvacuous`**
```lean
-- ClaimStrength/Basic.lean:642-644
theorem establishes_answer_key_nonvacuous :
    Undetermined [fun n : Nat => n ≤ 1] (fun n => n = 0) ∧
    WorldIndependent (Establishes [fun n : Nat => n ≤ 1] (fun n => n = 0))
```

**`establishes_contradicted_nonvacuous`**
```lean
-- ClaimStrength/Basic.lean:600-601
theorem establishes_contradicted_nonvacuous :
    ¬ Supported [fun n : Nat => n ≤ 1] (fun n => n = 0)
```

**`worldIndependent_tight`**
```lean
-- ClaimStrength/Basic.lean:624-626
theorem worldIndependent_tight :
    ¬ WorldIndependent (fun b : Bool => b = true) ∧
    Undetermined ([] : List (Claim Bool)) (fun b => b = true)
```

**`establishes_contradicted_h_tight`**
```lean
-- ClaimStrength/Basic.lean:593-595
theorem establishes_contradicted_h_tight :
    Supported ([] : List (Claim Nat)) (fun _ => True) ∧
    ¬ Contradicted ([] : List (Claim Nat)) (Establishes [] (fun _ => True))
```

**`establishes_answer_key_tight`**
```lean
-- ClaimStrength/Basic.lean:633-636
theorem establishes_answer_key_tight :
    ¬ Undetermined ([] : List (Claim Nat)) (fun _ => True) ∧
    ¬ KeyCorrect ([] : List (Claim Nat))
      [(Establishes [] (fun _ => True), .contradicted), ((fun _ => True), .undetermined)]
```

**`and_answer_nonvacuous`**
```lean
-- ClaimStrength/Compound.lean:223-228
theorem and_answer_nonvacuous :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun w => canon .contradicted w = true) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun w => canon .undetermined w = true) .undetermined ∧
    Correct ([] : List (Claim BB))
      (fun w => canon .contradicted w = true ∧ canon .undetermined w = true) .contradicted
```

**`or_answer_nonvacuous`**
```lean
-- ClaimStrength/Compound.lean:234-238
theorem or_answer_nonvacuous :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => (!w.1) = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∨ (!w.1) = true) .supported
```

**`neg_answer_nonvacuous`**
```lean
-- ClaimStrength/Compound.lean:302-303
theorem neg_answer_nonvacuous :
    Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined
```

**`not_undetermined_of_unique_model_nonvacuous`**
```lean
-- ClaimStrength/Compound.lean:296-297
theorem not_undetermined_of_unique_model_nonvacuous :
    ∀ w, Models [fun n : Nat => n = 0] w → w = 0
```

**`and_answer_hE_tight`**
```lean
-- ClaimStrength/Compound.lean:197-202
theorem and_answer_hE_tight :
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Correct [fun _ : Nat => False] (fun _ => True) .supported ∧
    Correct [fun _ : Nat => False] (fun w => (fun _ => True) w ∧ (fun _ => True) w)
      .contradicted ∧
    Answer.contradicted ∉ andTable .supported .supported
```

**`and_answer_h₁_tight`**
```lean
-- ClaimStrength/Compound.lean:308-313
theorem and_answer_h₁_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => True) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun _ => True) .supported ∧
    Correct ([] : List (Claim BB)) (fun w => (fun _ => True) w ∧ (fun _ => True) w) .supported ∧
    Answer.supported ∉ andTable .contradicted .supported
```

**`and_answer_h₂_tight`**
```lean
-- ClaimStrength/Compound.lean:320-325
theorem and_answer_h₂_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun _ => True) .supported ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => True) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun w => (fun _ => True) w ∧ (fun _ => True) w) .supported ∧
    Answer.supported ∉ andTable .supported .contradicted
```

**`and_answer_h_tight`**
```lean
-- ClaimStrength/Compound.lean:332-338
theorem and_answer_h_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun _ => True) .supported ∧
    Correct ([] : List (Claim BB)) (fun _ => True) .supported ∧
    ¬ Correct ([] : List (Claim BB)) (fun w => (fun _ => True) w ∧ (fun _ => True) w)
      .contradicted ∧
    Answer.contradicted ∉ andTable .supported .supported
```

**`or_answer_hE_tight`**
```lean
-- ClaimStrength/Compound.lean:210-215
theorem or_answer_hE_tight :
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Correct [fun _ : Nat => False] (fun _ => False) .contradicted ∧
    Correct [fun _ : Nat => False] (fun w => (fun _ => False) w ∨ (fun _ => False) w)
      .supported ∧
    Answer.supported ∉ orTable .contradicted .contradicted
```

**`or_answer_h₁_tight`**
```lean
-- ClaimStrength/Compound.lean:345-351
theorem or_answer_h₁_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => False) .supported ∧
    Correct ([] : List (Claim BB)) (fun _ => False) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun w => (fun _ => False) w ∨ (fun _ => False) w)
      .contradicted ∧
    Answer.contradicted ∉ orTable .supported .contradicted
```

**`or_answer_h₂_tight`**
```lean
-- ClaimStrength/Compound.lean:358-364
theorem or_answer_h₂_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun _ => False) .contradicted ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => False) .supported ∧
    Correct ([] : List (Claim BB)) (fun w => (fun _ => False) w ∨ (fun _ => False) w)
      .contradicted ∧
    Answer.contradicted ∉ orTable .contradicted .supported
```

**`or_answer_h_tight`**
```lean
-- ClaimStrength/Compound.lean:371-377
theorem or_answer_h_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun _ => False) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun _ => False) .contradicted ∧
    ¬ Correct ([] : List (Claim BB)) (fun w => (fun _ => False) w ∨ (fun _ => False) w)
      .supported ∧
    Answer.supported ∉ orTable .contradicted .contradicted
```

**`neg_answer_h_tight`**
```lean
-- ClaimStrength/Compound.lean:395-397
theorem neg_answer_h_tight :
    ¬ Correct ([] : List (Claim BB)) (fun _ => True) .contradicted ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => ¬ True) (negAnswer .contradicted)
```

**`not_undetermined_of_unique_model_hu_tight`**
```lean
-- ClaimStrength/Compound.lean:384-386
theorem not_undetermined_of_unique_model_hu_tight :
    (∀ w₀ : Bool, ¬ ∀ w, Models ([] : List (Claim Bool)) w → w = w₀) ∧
    Undetermined ([] : List (Claim Bool)) (fun b => b = true)
```

**`prefixCrit_sound_nonvacuous`**
```lean
-- ClaimStrength/PrefixResults.lean:437-440
theorem prefixCrit_sound_nonvacuous :
    (bvars ([A 0, X 1] : Prefix 2)).Nodup ∧ WF ([X 1, X 0] : Prefix 2) ∧
    PrefixCrit ([A 0, X 1] : Prefix 2) [X 1, X 0] ∧
    eval ([A 0, X 1] : Prefix 2) (fun _ => True) (fun _ => true)
```

**`eval_env_irrelevant_of_covers_nonvacuous`**
```lean
-- ClaimStrength/PrefixResults.lean:761
theorem eval_env_irrelevant_of_covers_nonvacuous : ∀ v : Fin 1, v ∈ bvars ([A 0] : Prefix 1)
```

**`sentailsAt_of_isEmpty_nonvacuous`**
```lean
-- ClaimStrength/PrefixResults.lean:610
theorem sentailsAt_of_isEmpty_nonvacuous : Empty → False
```

**`prefixCrit_sound_hφ_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:489-491
theorem prefixCrit_sound_hφ_tight :
    ¬ (bvars ([A 0, X 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    PrefixCrit ([A 0, X 0] : Prefix 1) [A 0] ∧ ¬ SEntailsAt Bool ([A 0, X 0] : Prefix 1) [A 0]
```

**`prefixCrit_sound_hψ_tight_dup`**
```lean
-- ClaimStrength/PrefixResults.lean:503-505
theorem prefixCrit_sound_hψ_tight_dup :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([X 0, A 0] : Prefix 1) ∧
    PrefixCrit ([X 0] : Prefix 1) [X 0, A 0] ∧ ¬ SEntailsAt Bool ([X 0] : Prefix 1) [X 0, A 0]
```

**`prefixCrit_sound_hψ_tight_missing`**
```lean
-- ClaimStrength/PrefixResults.lean:518-520
theorem prefixCrit_sound_hψ_tight_missing :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([] : Prefix 1) ∧
    PrefixCrit ([X 0] : Prefix 1) [] ∧ ¬ SEntailsAt Bool ([X 0] : Prefix 1) []
```

**`prefixCrit_part_i_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:455-458
theorem prefixCrit_part_i_tight :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    SkolemOrderPreserved ([X 0] : Prefix 1) [A 0] ∧
    ¬ UnivReflected ([X 0] : Prefix 1) [A 0] ∧ ¬ SEntailsAt Bool ([X 0] : Prefix 1) [A 0]
```

**`prefixCrit_part_ii_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:470-474
theorem prefixCrit_part_ii_tight :
    (bvars ([A 0, X 1] : Prefix 2)).Nodup ∧ WF ([X 1, A 0] : Prefix 2) ∧
    UnivReflected ([A 0, X 1] : Prefix 2) [X 1, A 0] ∧
    ¬ SkolemOrderPreserved ([A 0, X 1] : Prefix 2) [X 1, A 0] ∧
    ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0]
```

**`eval_env_irrelevant_hcov_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:596-599
theorem eval_env_irrelevant_hcov_tight :
    ¬ (∀ v : Fin 1, v ∈ bvars ([] : Prefix 1)) ∧
    ¬ (eval ([] : Prefix 1) (fun σ => σ 0 = true) (fun _ => true) ↔
      eval ([] : Prefix 1) (fun σ => σ 0 = true) (fun _ => false))
```

**`sentailsAt_of_isEmpty_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:605-606
theorem sentailsAt_of_isEmpty_tight :
    ¬ (Bool → False) ∧ ¬ SEntailsAt Bool ([X 0] : Prefix 1) [A 0]
```

**`prefixCrit_necessary_nonvacuous`**
```lean
-- ClaimStrength/PrefixResults.lean:446-449
theorem prefixCrit_necessary_nonvacuous :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 1, A 0] : Prefix 2)).Nodup ∧
    (bvars ([A 0, X 1] : Prefix 2)).Nodup ∧
    SEntailsAt Bool ([X 1, A 0] : Prefix 2) [A 0, X 1]
```

**`sentailsAt_iff_nonvacuous`**
```lean
-- ClaimStrength/PrefixResults.lean:699-702
theorem sentailsAt_iff_nonvacuous :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 1, A 0] : Prefix 2)).Nodup ∧ WF ([A 0, X 1] : Prefix 2) ∧
    SEntailsAt Bool ([X 1, A 0] : Prefix 2) [A 0, X 1] ∧
    PrefixCrit ([X 1, A 0] : Prefix 2) [A 0, X 1]
```

**`sentails_iff_nonvacuous`**
```lean
-- ClaimStrength/PrefixResults.lean:735-737
theorem sentails_iff_nonvacuous :
    (bvars ([X 1, A 0] : Prefix 2)).Nodup ∧ WF ([A 0, X 1] : Prefix 2) ∧
    SEntails ([X 1, A 0] : Prefix 2) [A 0, X 1] ∧ PrefixCrit ([X 1, A 0] : Prefix 2) [A 0, X 1]
```

**`subsingleton_nonvacuous`**
```lean
-- ClaimStrength/PrefixResults.lean:756-757
theorem subsingleton_nonvacuous :
    Subsingleton Unit ∧ SEntailsAt Unit ([X 0] : Prefix 1) [A 0]
```

**`prefixCrit_necessary_hα_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:530-533
theorem prefixCrit_necessary_hα_tight :
    ¬ (∃ a b : Unit, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧
    (bvars ([A 0] : Prefix 1)).Nodup ∧
    SEntailsAt Unit ([X 0] : Prefix 1) [A 0] ∧ ¬ PrefixCrit ([X 0] : Prefix 1) [A 0]
```

**`prefixCrit_necessary_hφ_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:539-542
theorem prefixCrit_necessary_hφ_tight :
    (∃ a b : Bool, a ≠ b) ∧ ¬ (bvars ([X 0, A 0] : Prefix 1)).Nodup ∧
    (bvars ([A 0] : Prefix 1)).Nodup ∧
    SEntailsAt Bool ([X 0, A 0] : Prefix 1) [A 0] ∧ ¬ PrefixCrit ([X 0, A 0] : Prefix 1) [A 0]
```

**`prefixCrit_necessary_hψ_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:559-562
theorem prefixCrit_necessary_hψ_tight :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧
    ¬ (bvars ([A 0, X 0] : Prefix 1)).Nodup ∧
    SEntailsAt Bool ([X 0] : Prefix 1) [A 0, X 0] ∧ ¬ PrefixCrit ([X 0] : Prefix 1) [A 0, X 0]
```

**`prefixCrit_necessary_h_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:580-584
theorem prefixCrit_necessary_h_tight :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([A 0, X 1] : Prefix 2)).Nodup ∧
    (bvars ([X 1, A 0] : Prefix 2)).Nodup ∧
    ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0] ∧
    ¬ PrefixCrit ([A 0, X 1] : Prefix 2) [X 1, A 0]
```

**`sentailsAt_iff_hα_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:640-644
theorem sentailsAt_iff_hα_tight :
    ¬ (∃ a b : Unit, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    ¬ (SEntailsAt Unit ([X 0] : Prefix 1) [A 0] ↔ PrefixCrit ([X 0] : Prefix 1) [A 0]) ∧
    ¬ (SEntailsAt Unit ([X 0] : Prefix 1) [A 0] ↔
        prefixCritB ([X 0] : Prefix 1) [A 0] = true)
```

**`sentailsAt_iff_hφ_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:655-660
theorem sentailsAt_iff_hφ_tight :
    (∃ a b : Bool, a ≠ b) ∧ ¬ (bvars ([X 0, A 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    ¬ (SEntailsAt Bool ([X 0, A 0] : Prefix 1) [A 0] ↔
        PrefixCrit ([X 0, A 0] : Prefix 1) [A 0]) ∧
    ¬ (SEntailsAt Bool ([X 0, A 0] : Prefix 1) [A 0] ↔
        prefixCritB ([X 0, A 0] : Prefix 1) [A 0] = true)
```

**`sentailsAt_iff_hψ_tight_dup`**
```lean
-- ClaimStrength/PrefixResults.lean:685-690
theorem sentailsAt_iff_hψ_tight_dup :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([X 0, A 0] : Prefix 1) ∧
    ¬ (SEntailsAt Bool ([X 0] : Prefix 1) [X 0, A 0] ↔
        PrefixCrit ([X 0] : Prefix 1) [X 0, A 0]) ∧
    ¬ (SEntailsAt Bool ([X 0] : Prefix 1) [X 0, A 0] ↔
        prefixCritB ([X 0] : Prefix 1) [X 0, A 0] = true)
```

**`sentailsAt_iff_hψ_tight_missing`**
```lean
-- ClaimStrength/PrefixResults.lean:671-674
theorem sentailsAt_iff_hψ_tight_missing :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([] : Prefix 1) ∧
    ¬ (SEntailsAt Bool ([X 0] : Prefix 1) [] ↔ PrefixCrit ([X 0] : Prefix 1) []) ∧
    ¬ (SEntailsAt Bool ([X 0] : Prefix 1) [] ↔ prefixCritB ([X 0] : Prefix 1) [] = true)
```

**`sentails_iff_hφ_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:709-711
theorem sentails_iff_hφ_tight :
    ¬ (bvars ([X 0, A 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    ¬ (SEntails ([X 0, A 0] : Prefix 1) [A 0] ↔ PrefixCrit ([X 0, A 0] : Prefix 1) [A 0])
```

**`sentails_iff_hψ_tight_dup`**
```lean
-- ClaimStrength/PrefixResults.lean:727-729
theorem sentails_iff_hψ_tight_dup :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([X 0, A 0] : Prefix 1) ∧
    ¬ (SEntails ([X 0] : Prefix 1) [X 0, A 0] ↔ PrefixCrit ([X 0] : Prefix 1) [X 0, A 0])
```

**`sentails_iff_hψ_tight_missing`**
```lean
-- ClaimStrength/PrefixResults.lean:718-720
theorem sentails_iff_hψ_tight_missing :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([] : Prefix 1) ∧
    ¬ (SEntails ([X 0] : Prefix 1) [] ↔ PrefixCrit ([X 0] : Prefix 1) [])
```

**`sentailsAt_of_subsingleton_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:590-591
theorem sentailsAt_of_subsingleton_tight :
    ¬ Subsingleton Bool ∧ ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0]
```

**`eval_subsingleton_tight`**
```lean
-- ClaimStrength/PrefixResults.lean:744-747
theorem eval_subsingleton_tight :
    ¬ Subsingleton Bool ∧
    ¬ (eval ([A 0] : Prefix 1) (fun σ => σ 0 = true) (fun _ => true) ↔
        (fun σ : Fin 1 → Bool => σ 0 = true) (fun _ => true))
```

**`uniform_entails_pointwise_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:296-297
theorem uniform_entails_pointwise_nonvacuous :
    (fun R : Nat → Nat → Prop => ∃ n, ∀ x, R x n) (fun _ n => n = 0)
```

**`domain_variance_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:61-63
theorem domain_variance_nonvacuous :
    Entails (W := Nat → Prop) (fun P => ∀ k, 1 ≤ k → P k) (fun P => ∀ k, k = 2 → P k) ∧
    Entails (W := Nat → Prop) (fun P => ∃ k, k = 2 ∧ P k) (fun P => ∃ k, 1 ≤ k ∧ P k)
```

**`range_entails_single_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:292-293
theorem range_entails_single_nonvacuous :
    (fun P : Nat → Prop => ∀ k, 1 ≤ k → P k) (fun k => 1 ≤ k)
```

**`absolute_entails_relative_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:300-301
theorem absolute_entails_relative_nonvacuous :
    (fun w : (Nat → Prop) × (Nat → Prop) => ∀ x, w.2 x) ((· = 0), fun _ => True)
```

**`disj_premise_entails_conj_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:305-306
theorem disj_premise_entails_conj_nonvacuous :
    (fun w : Prop × Prop × Prop => w.1 ∨ w.2.1 → w.2.2) (True, False, True)
```

**`counterexample_in_subclass_lifts_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:286-288
theorem counterexample_in_subclass_lifts_nonvacuous :
    (∀ m, (fun m => m % 2 = 0) m → (fun _ => True) m) ∧
    (fun P : Nat → Prop => ∃ m, m % 2 = 0 ∧ ¬ P m) (fun m => m ≠ 0)
```

**`universal_refutation_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:93-94
theorem universal_refutation_nonvacuous :
    Nonempty Nat ∧ (fun P : Nat → Prop => ∀ m, ¬ P m) (fun _ => False)
```

**`universal_refutation_nonempty_tight`**
```lean
-- ClaimStrength/Drift.lean:84-86
theorem universal_refutation_nonempty_tight :
    ¬ Nonempty Empty ∧
    ¬ Entails (W := Empty → Prop) (fun P => ∀ m, ¬ P m) (fun P => ∃ m, ¬ P m)
```

**`counterexample_in_subclass_lifts_h_tight`**
```lean
-- ClaimStrength/Drift.lean:113-117
theorem counterexample_in_subclass_lifts_h_tight :
    ¬ (∀ m : Nat, (fun _ => True) m → (fun m => m % 2 = 0) m) ∧
    ¬ Entails (W := Nat → Prop)
        (fun P => ∃ m, (fun _ => True) m ∧ ¬ P m)
        (fun P => ∃ m, (fun m => m % 2 = 0) m ∧ ¬ P m)
```

**`checker_sound_complete_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:237-238
theorem checker_sound_complete_nonvacuous :
    CheckerSound evenChecker ∧ CheckerComplete evenChecker ∧ evenChecker.accept 0 = true
```

**`characterization_entails_sufficient_nonvacuous`**
```lean
-- ClaimStrength/Drift.lean:242-243
theorem characterization_entails_sufficient_nonvacuous :
    (fun w : Prop × Prop => w.1 ↔ w.2) (True, True)
```

**`checkerSound_example_pos`**
```lean
-- ClaimStrength/Drift.lean:210
theorem checkerSound_example_pos : CheckerSound zeroChecker ∧ zeroChecker.accept 0 = true
```

**`rcrit_sound_nonvacuous`**
```lean
-- ClaimStrength/RelResults.lean:390-394
theorem rcrit_sound_nonvacuous :
    WF nvφ.pre ∧ WF nvψ.pre ∧ InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧
    ImplSound (premJ 1) premImpl ∧ RCrit clsIncl clsMeets premImpl nvφ nvψ ∧
    Holds clsI (premJ 1) nvφ (fun _ => True) (fun _ => 0) ∧
    ¬ Holds clsI (premJ 1) nvψ (fun _ => False) (fun _ => 0)
```

**`rcrit_sound_nonvacuous_domains`**
```lean
-- ClaimStrength/RelResults.lean:407-411
theorem rcrit_sound_nonvacuous_domains :
    WF nvφD.pre ∧ WF nvψD.pre ∧ InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧
    ImplSound (premJ 1) premImpl ∧ RCrit clsIncl clsMeets premImpl nvφD nvψD ∧
    Holds clsI (premJ 1) nvφD (fun _ => True) (fun _ => 0) ∧
    ¬ Holds clsI (premJ 1) nvψD (fun _ => False) (fun _ => 0)
```

**`evalR_premise_pull_out_nonvacuous`**
```lean
-- ClaimStrength/RelResults.lean:1261-1265
theorem evalR_premise_pull_out_nonvacuous :
    (∀ b ∈ ([⟨.ex, 1, .zeroOne⟩] : List (Binder 2 Cls)), ∃ a, clsI b.dom a) ∧
    (∀ b ∈ ([⟨.ex, 1, .zeroOne⟩] : List (Binder 2 Cls)), ∀ (σ : Fin 2 → Nat) (a : Nat),
      (fun τ : Fin 2 → Nat => τ 0 ≤ 1) (upd σ b.var a) ↔ (fun τ : Fin 2 → Nat => τ 0 ≤ 1) σ) ∧
    ¬ (∀ σ : Fin 2 → Nat, (fun τ : Fin 2 → Nat => τ 0 ≤ 1) σ)
```

**`rcrit_sound_hφ_tight`**
```lean
-- ClaimStrength/RelResults.lean:1006-1012
theorem rcrit_sound_hφ_tight :
    ¬ WF ([⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧
    WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_sound_hφ_tight_missing`**
```lean
-- ClaimStrength/RelResults.lean:1023-1027
theorem rcrit_sound_hφ_tight_missing :
    ¬ WF ([] : List (Binder 1 Cls)) ∧ WF ([⟨.ex, 0, .zero⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl clsMeets premImpl (⟨[], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .zero⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[], .top⟩ ⟨[⟨.ex, 0, .zero⟩], .top⟩
```

**`rcrit_sound_hψ_tight`**
```lean
-- ClaimStrength/RelResults.lean:977-983
theorem rcrit_sound_hψ_tight :
    WF ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧
    ¬ WF ([⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_sound_hψ_tight_missing`**
```lean
-- ClaimStrength/RelResults.lean:994-998
theorem rcrit_sound_hψ_tight_missing :
    WF ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧ ¬ WF ([] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl clsMeets premImpl (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[], .top⟩
```

**`rcrit_sound_hI_tight`**
```lean
-- ClaimStrength/RelResults.lean:1039-1045
theorem rcrit_sound_hI_tight :
    WF ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    ¬ InclSound clsI (fun _ _ => true) ∧ MeetsSound clsI clsMeets ∧
    ImplSound (premJ 0) premImpl ∧
    RCrit (fun _ _ => true) clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_sound_hM_tight`**
```lean
-- ClaimStrength/RelResults.lean:1052-1058
theorem rcrit_sound_hM_tight :
    WF ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ ¬ MeetsSound clsI (fun _ _ => true) ∧
    ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl (fun _ _ => true) premImpl
      (⟨[⟨.all, 0, .empty⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .empty⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .empty⟩], .top⟩ ⟨[⟨.ex, 0, .empty⟩], .top⟩
```

**`rcrit_sound_hJ_tight`**
```lean
-- ClaimStrength/RelResults.lean:1068-1074
theorem rcrit_sound_hJ_tight :
    WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧
    ¬ ImplSound (premJ 0) (fun _ _ => true) ∧
    RCrit clsIncl clsMeets (fun _ _ => true)
      (⟨[⟨.all, 0, .all⟩], .atMostOne⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_part_i_tight`**
```lean
-- ClaimStrength/RelResults.lean:1084-1094
theorem rcrit_part_i_tight :
    WF ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    SkolemOrderPreserved ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    PremiseContravariant premImpl (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem)
      ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ UnivReflected ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_part_ii_tight`**
```lean
-- ClaimStrength/RelResults.lean:1105-1123
theorem rcrit_part_ii_tight :
    WF ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls)) ∧
    WF ([⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] : List (Binder 2 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 1) premImpl ∧
    UnivReflected ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    PremiseContravariant premImpl
      (⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩], .top⟩ : Shape 2 Cls Prem)
      ⟨[⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ SkolemOrderPreserved ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    ¬ REntails clsI (premJ 1) ⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩], .top⟩
      ⟨[⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_univ_domain_tight`**
```lean
-- ClaimStrength/RelResults.lean:1137-1148
theorem rcrit_univ_domain_tight :
    WF ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    PrefixCrit ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))
      [⟨.all, 0, .all⟩] ∧
    PremiseContravariant premImpl (⟨[⟨.all, 0, .zeroOne⟩], .top⟩ : Shape 1 Cls Prem)
      ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ UnivDomainsContravariant clsIncl ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))
      [⟨.all, 0, .all⟩] ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`rcrit_ex_domain_tight`**
```lean
-- ClaimStrength/RelResults.lean:1156-1167
theorem rcrit_ex_domain_tight :
    WF ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    PrefixCrit ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .zeroOne⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))
      [⟨.ex, 0, .zeroOne⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))
      [⟨.ex, 0, .zeroOne⟩] ∧
    PremiseContravariant premImpl (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem)
      ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ ∧
    ¬ ExDomainsCovariant clsIncl ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .zeroOne⟩] ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩
```

**`rcrit_meet_tight`**
```lean
-- ClaimStrength/RelResults.lean:1181-1191
theorem rcrit_meet_tight :
    WF ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    PrefixCrit ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .empty⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .empty⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .empty⟩] ∧
    PremiseContravariant premImpl (⟨[⟨.all, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem)
      ⟨[⟨.ex, 0, .empty⟩], .top⟩ ∧
    ¬ InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls))
      [⟨.ex, 0, .empty⟩] ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .zero⟩], .top⟩ ⟨[⟨.ex, 0, .empty⟩], .top⟩
```

**`rcrit_premise_tight`**
```lean
-- ClaimStrength/RelResults.lean:1202-1211
theorem rcrit_premise_tight :
    WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    PrefixCrit ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ¬ PremiseContravariant premImpl (⟨[⟨.all, 0, .all⟩], .atMostOne⟩ : Shape 1 Cls Prem)
      ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`rEntails_of_isEmpty_tight`**
```lean
-- ClaimStrength/RelResults.lean:1219-1221
theorem rEntails_of_isEmpty_tight :
    ¬ (Nat → False) ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`evalR_premise_pull_out_hne_tight`**
```lean
-- ClaimStrength/RelResults.lean:1227-1234
theorem evalR_premise_pull_out_hne_tight :
    ¬ (∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
    (∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), ∀ (σ : Fin 1 → Nat) (a : Nat),
      (fun _ => False) (upd σ b.var a) ↔ (fun _ : Fin 1 → Nat => False) σ) ∧
    ¬ (evalR clsI ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls))
        (fun σ => (fun _ => False) σ → (fun _ => False) σ) (fun _ => 0) ↔
      ((fun _ : Fin 1 → Nat => False) (fun _ => 0) →
        evalR clsI ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)) (fun _ => False) (fun _ => 0)))
```

**`evalR_premise_pull_out_hind_tight`**
```lean
-- ClaimStrength/RelResults.lean:1244-1251
theorem evalR_premise_pull_out_hind_tight :
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
    ¬ (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), ∀ (σ : Fin 1 → Nat) (a : Nat),
      (fun τ : Fin 1 → Nat => τ 0 ≤ 1) (upd σ b.var a) ↔ (fun τ : Fin 1 → Nat => τ 0 ≤ 1) σ) ∧
    ¬ (evalR clsI ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))
        (fun σ => σ 0 ≤ 1 → False) (fun _ => 0) ↔
      ((fun τ : Fin 1 → Nat => τ 0 ≤ 1) (fun _ => 0) →
        evalR clsI ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) (fun _ => False) (fun _ => 0)))
```

**`rcrit_complete_nonvacuous`**
```lean
-- ClaimStrength/RelResults.lean:421-427
theorem rcrit_complete_nonvacuous :
    (bvars nvφ.pre).Nodup ∧ (bvars nvψTop.pre).Nodup ∧ InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧
    ImplExact (premJ 1) premImpl ∧ Nonempty Nat ∧
    (∀ b ∈ nvφ.pre, b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ nvψTop.pre, b.q = .all → TwoPoint (clsI b.dom)) ∧ (∀ σ, premJ 1 nvφ.prem σ) ∧
    (∀ σ, premJ 1 nvψTop.prem σ) ∧ REntails clsI (premJ 1) nvφ nvψTop ∧
    ¬ Holds clsI (premJ 1) nvψTop (fun _ => False) (fun _ => 0)
```

**`rcrit_complete_nonvacuous_free_variable`**
```lean
-- ClaimStrength/RelResults.lean:857-866
theorem rcrit_complete_nonvacuous_free_variable :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    (bvars ([] : List (Binder 1 Cls))).Nodup ∧ ¬ WF ([] : List (Binder 1 Cls)) ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .top⟩ ⟨[], .top⟩ ∧
    RCrit clsIncl clsMeets premImpl (⟨[⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[], .top⟩
```

**`rcrit_complete_hE_tight`**
```lean
-- ClaimStrength/RelResults.lean:835-844
theorem rcrit_complete_hE_tight :
    (bvars ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩
```

**`nonempty_domains_hα_tight`**
```lean
-- ClaimStrength/RelResults.lean:882-887
theorem nonempty_domains_hα_tight :
    ¬ Nonempty Empty ∧
    (∀ b ∈ emptyφ.pre, b.q = .ex → TwoPoint (emptyI b.dom)) ∧
    (∀ b ∈ emptyψ.pre, b.q = .all → TwoPoint (emptyI b.dom)) ∧
    (∀ σ, emptyJ emptyψ.prem σ) ∧ REntails emptyI emptyJ emptyφ emptyψ ∧
    ¬ ((∀ b ∈ emptyφ.pre, ∃ a, emptyI b.dom a) ∧ (∀ b ∈ emptyψ.pre, ∃ a, emptyI b.dom a))
```

**`nonempty_domains_h2φ_tight`**
```lean
-- ClaimStrength/RelResults.lean:898-905
theorem nonempty_domains_h2φ_tight :
    Nonempty Nat ∧
    ¬ (∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .empty⟩], .top⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ ((∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
      (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a))
```

**`nonempty_domains_h2ψ_tight`**
```lean
-- ClaimStrength/RelResults.lean:918-925
theorem nonempty_domains_h2ψ_tight :
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .empty⟩], .top⟩ ∧
    ¬ ((∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
      (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a))
```

**`nonempty_domains_hpψ_tight`**
```lean
-- ClaimStrength/RelResults.lean:937-944
theorem nonempty_domains_hpψ_tight :
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ σ, premJ 0 .bot σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .empty⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .bot⟩ ∧
    ¬ ((∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
      (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a))
```

**`nonempty_domains_hE_tight`**
```lean
-- ClaimStrength/RelResults.lean:955-962
theorem nonempty_domains_hE_tight :
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .empty⟩], .top⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ ((∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
      (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a))
```

**`frontier_test_nonvacuous`**
```lean
-- ClaimStrength/Frontier.lean:172-175
theorem frontier_test_nonvacuous :
    ClosedUnderEntailmentIn candidates (fun q => Supported ([] : List (Claim Nat)) q) ∧
    (∀ q, Frontier [] candidates q → ¬ Supported ([] : List (Claim Nat)) q) ∧
    Frontier [] candidates qWeak
```

**`unsupported_of_entails_nonvacuous`**
```lean
-- ClaimStrength/Frontier.lean:233-234
theorem unsupported_of_entails_nonvacuous :
    ¬ Supported ([] : List (Claim Nat)) qWeak ∧ Entails qStrong qWeak
```

**`exists_frontier_below_nonvacuous`**
```lean
-- ClaimStrength/Frontier.lean:263-264
theorem exists_frontier_below_nonvacuous :
    qStrong ∈ candidates ∧ ¬ Supported ([] : List (Claim Nat)) qStrong
```

**`exists_weakest_nonvacuous`**
```lean
-- ClaimStrength/Frontier.lean:275
theorem exists_weakest_nonvacuous : candidates ≠ []
```

**`endorsement_respects_equivalence_nonvacuous`**
```lean
-- ClaimStrength/Frontier.lean:297-298
theorem endorsement_respects_equivalence_nonvacuous :
    Entails qWeak (fun n => n ≠ 0 ∧ True) ∧ Entails (fun n => n ≠ 0 ∧ True) qWeak
```

**`unsupported_of_entails_h_tight`**
```lean
-- ClaimStrength/Frontier.lean:219-221
theorem unsupported_of_entails_h_tight :
    Supported ([] : List (Claim Nat)) qTriv ∧ Entails qTriv qTriv ∧
    Supported ([] : List (Claim Nat)) qTriv
```

**`unsupported_of_entails_h'_tight`**
```lean
-- ClaimStrength/Frontier.lean:226-228
theorem unsupported_of_entails_h'_tight :
    ¬ Supported ([] : List (Claim Nat)) qStrong ∧ ¬ Entails qTriv qStrong ∧
    Supported ([] : List (Claim Nat)) qTriv
```

**`exists_weakest_tight`**
```lean
-- ClaimStrength/Frontier.lean:269-271
theorem exists_weakest_tight :
    ¬ (([] : List (Claim Nat)) ≠ []) ∧
    ¬ (∃ m ∈ ([] : List (Claim Nat)), ∀ x ∈ ([] : List (Claim Nat)), Entails m x → Entails x m)
```

**`exists_frontier_below_hq_tight`**
```lean
-- ClaimStrength/Frontier.lean:240-244
theorem exists_frontier_below_hq_tight :
    (fun n : Nat => n = 1) ∉ [fun n : Nat => n = 2] ∧
    ¬ Supported ([] : List (Claim Nat)) (fun n => n = 1) ∧
    ¬ (∃ q', Frontier ([] : List (Claim Nat)) [fun n => n = 2] q' ∧
      Entails (fun n : Nat => n = 1) q')
```

**`exists_frontier_below_hns_tight`**
```lean
-- ClaimStrength/Frontier.lean:255-257
theorem exists_frontier_below_hns_tight :
    qTriv ∈ candidates ∧ Supported ([] : List (Claim Nat)) qTriv ∧
    ¬ (∃ q', Frontier ([] : List (Claim Nat)) candidates q' ∧ Entails qTriv q')
```

**`frontier_test_hclosed_tight`**
```lean
-- ClaimStrength/Frontier.lean:139-143
theorem frontier_test_hclosed_tight :
    ¬ ClosedUnderEntailmentIn candidates (fun q => q = qStrong) ∧
    (∀ q, Frontier [] candidates q → ¬ (fun q => q = qStrong) q) ∧
    ¬ (∀ q ∈ candidates, (fun q => q = qStrong) q → Supported [] q) ∧
    ¬ (∀ q ∈ candidates, (fun q => q = qStrong) q → ¬ PositiveOverReading [] q .supported)
```

**`frontier_test_hfront_tight`**
```lean
-- ClaimStrength/Frontier.lean:153-158
theorem frontier_test_hfront_tight :
    ClosedUnderEntailmentIn candidates (fun q => q = qWeak ∨ q = qTriv) ∧
    ¬ (∀ q, Frontier [] candidates q → ¬ (fun q => q = qWeak ∨ q = qTriv) q) ∧
    ¬ (∀ q ∈ candidates, (fun q => q = qWeak ∨ q = qTriv) q → Supported [] q) ∧
    ¬ (∀ q ∈ candidates, (fun q => q = qWeak ∨ q = qTriv) q →
        ¬ PositiveOverReading [] q .supported)
```

**`endorsement_respects_equivalence_h₁_tight`**
```lean
-- ClaimStrength/Frontier.lean:280-282
theorem endorsement_respects_equivalence_h₁_tight :
    ¬ Entails qWeak qStrong ∧ Entails qStrong qWeak ∧
    ¬ ((fun q => q = qStrong) qWeak ↔ (fun q => q = qStrong) qStrong)
```

**`endorsement_respects_equivalence_h₂_tight`**
```lean
-- ClaimStrength/Frontier.lean:289-291
theorem endorsement_respects_equivalence_h₂_tight :
    Entails qStrong qWeak ∧ ¬ Entails qWeak qStrong ∧
    ¬ ((fun q => q = qStrong) qStrong ↔ (fun q => q = qStrong) qWeak)
```

## Boundaries

### Non-claims

Read each card's non-claims together with its plain claim. The non-claims of every card share the vocabulary stated under **Summary**; scope disclaimers name the model–system relation (none proved). A non-claim that relates a predicate to the wording of a real report or to real readers (for example, in card 4, that a bare disclaimer "q is not established here" corresponds to `¬ Supported E q`; in card 16, that real readers need not endorse all entailed candidates) is a modeling-bridge remark, Basis: derived (modeling bridge): it applies the definitions under the representation of a report as the list of claims it establishes, and it is not itself a kernel-checked statement.

#### Non-claims of 1. `three-answers-exactly-one-iff-satisfiable`

- Vocabulary: 'supported' is Supported E q; 'unsupported' is ¬ Supported E q; 'contradicted' is Contradicted E q; 'undetermined' is Undetermined E q (unsupported and not contradicted). An unsupported claim of a satisfiable report can be contradicted; an undetermined claim cannot.
- Supported is semantic (truth in every interpretation consistent with the report); nothing is claimed about computing answers or about what a reader can verify.
- Exclusivity of the three answers holds if and only if the report is satisfiable (exactlyOne_answer_iff_satisfiable); with an unsatisfiable report every claim is both supported and contradicted and Undetermined never holds.
- Over an interpretation type with no elements every report is unsatisfiable, so correct_unique_of_satisfiable has no instances there (not proved here as a separate theorem; immediate from the definition of Satisfiable).
- The three reading-error predicates classify incorrect answers by which answer was given; they do not distinguish, for example, answering contradicted for a supported claim from answering contradicted for an undetermined claim (both are negative over-readings).
- A report is the set of claims it establishes; hedges, scope statements, examples, and other prose of a real report are not modeled.
- These are statements about the toy model (claims are arbitrary predicates on an arbitrary interpretation type; a report is identified with the finite list of claims it establishes); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason.

#### Non-claims of 2. `answers-monotone-under-satisfiable-report-extension`

- Does not say that adding claims changes any answer; it bounds which changes are possible.
- The theorems concern adding established claims; removing or weakening a claim can turn supported into undetermined (answer_changes_hsub_tight).
- Without satisfiability of the extended report, a supported claim also becomes (vacuously) contradicted (answer_changes_hsat_tight).
- These are statements about the toy model (claims are arbitrary predicates on an arbitrary interpretation type; a report is identified with the finite list of claims it establishes); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason.

#### Non-claims of 3. `undetermined-iff-witnesses-both-ways`

- Vocabulary: 'supported' is Supported E q; 'unsupported' is ¬ Supported E q; 'contradicted' is Contradicted E q; 'undetermined' is Undetermined E q (unsupported and not contradicted). An unsupported claim of a satisfiable report can be contradicted; an undetermined claim cannot.
- The characterization is classical (proved with excluded middle) and gives no constructive witnesses.
- A single established claim entailing ¬q is sufficient for 'contradicted' but not necessary: several claims of the report can jointly rule out q although none does alone (contradicted_jointly_without_single_claim). A counterexample to a different claim, or in a different class, does not by itself contradict q (see the drift cards).
- These are statements about the toy model (claims are arbitrary predicates on an arbitrary interpretation type; a report is identified with the finite list of claims it establishes); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason.

#### Non-claims of 4. `unsupported-does-not-imply-contradicted`

- Vocabulary: 'supported' is Supported E q; 'unsupported' is ¬ Supported E q; 'contradicted' is Contradicted E q; 'undetermined' is Undetermined E q (unsupported and not contradicted). An unsupported claim of a satisfiable report can be contradicted; an undetermined claim cannot.
- A bare disclaimer in a report ('q is not established here') corresponds to ¬ Supported E q (unsupported), not to Undetermined E q: Undetermined additionally asserts ¬ Contradicted E q, i.e. that q is consistent with the established claims (undetermined_iff_exists_both). By the definition of NegativeOverReading, reading such a disclaimer as 'contradicted' is a negative over-reading exactly when q is not contradicted.
- Does not say anything about whether an unsupported claim is true.
- These are statements about the toy model (claims are arbitrary predicates on an arbitrary interpretation type; a report is identified with the finite list of claims it establishes); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason.

#### Non-claims of 5. `meta-level-questions-are-never-undetermined`

- Vocabulary: 'supported' is Supported E q; 'unsupported' is ¬ Supported E q; 'contradicted' is Contradicted E q; 'undetermined' is Undetermined E q (unsupported and not contradicted). An unsupported claim of a satisfiable report can be contradicted; an undetermined claim cannot.
- worldIndependent_not_undetermined has no satisfiability hypothesis: over an unsatisfiable report every claim is supported (unsatisfiable_supported_and_contradicted), so Undetermined fails there as well.
- Does not say that 'not established' is a bad answer in ordinary language; it says that under this three-answer semantics a question about the report has a supported or contradicted answer, so an answer key using 'undetermined' for it is inconsistent with the semantics.
- Escape hatches (not modeled, not proved here): the impossibility depends on fixing the whole report E outside the interpretation and on reading 'establishes' as semantic consequence Supported E q. If a reader sees an excerpt instead of the full report, so that the full report varies across the interpretations consistent with the prompt, or if 'establishes' means explicit derivation in an incomplete proof system, a question about what the report establishes need not be world-independent and can be undetermined.
- Says nothing about which question phrasing readers find easier or less ambiguous.
- These are statements about the toy model (claims are arbitrary predicates on an arbitrary interpretation type; a report is identified with the finite list of claims it establishes); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason.

#### Non-claims of 6. `compound-answer-tables-over-satisfiable-reports`

- Vocabulary: 'supported' is Supported E q; 'unsupported' is ¬ Supported E q; 'contradicted' is Contradicted E q; 'undetermined' is Undetermined E q (unsupported and not contradicted). An unsupported claim of a satisfiable report can be contradicted; an undetermined claim cannot.
- Over an unsatisfiable report both supported and contradicted are correct for every claim, so negAnswer gives a correct answer for ¬q but not a unique one: uniqueness fails over the unsatisfiable report [False] (correct_unique_hE_tight) and holds over every satisfiable report (correct_unique_of_satisfiable).
- Realizability is shown in one interpretation space with the empty report. For a fixed report, if a claim is undetermined, then the report has two consistent interpretations, one satisfying and one falsifying the claim (undetermined_iff_exists_both); not_undetermined_of_unique_model states the contrapositive for reports with at most one consistent interpretation.
- Which answer occurs in the cell (undetermined, undetermined) depends on how the claims relate, not just on their answers; negation keeping 'undetermined' does not make it a truth value: q and ¬q are both undetermined while q ∨ ¬q is supported (or_answer_nonvacuous).
- Does not say that readers answer compounds wrongly; it says the compound answer is not a function of the component answers in the cell (undetermined, undetermined): both compound answers occur there for undetermined components (andTable_undetermined_cell_distinct, orTable_undetermined_cell_distinct).
- These are statements about the toy model (claims are arbitrary predicates on an arbitrary interpretation type; a report is identified with the finite list of claims it establishes); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason.

#### Non-claims of 7. `prefix-criterion-sufficient-environment-semantics`

- SEntailsAt uses environment semantics: it quantifies over every matrix R and every environment ρ : Fin n → α. When α is empty and n ≥ 1 there is no environment, so SEntailsAt α φ ψ holds vacuously for every pair (sentailsAt_of_isEmpty); in particular the closed implication (∀x, P x) → ∃x, P x fails on an empty type (closed_forall_imp_exists_iff_nonempty) although SEntailsAt α [∀x] [∃x] holds there. For prefixes that bind every variable, SEntailsAt at α equals entailment at one fixed environment (sentailsAt_iff_fixed_env_of_covers), so the quantification over environments can make a difference for prefixes that leave a variable free and for an empty base type (sentailsAt_of_isEmpty).
- No cardinality assumption is made. For an empty base type and n ≥ 1 the claim is vacuous (sentailsAt_of_isEmpty); the non-vacuity witness uses an inhabited base type.
- The covering half of well-formedness is not assumed for φ: a variable free in φ behaves like an outermost universal that both sides share through the environment. It is assumed for ψ, where it is tight (prefixCrit_sound_hψ_tight_missing).
- Variables are matched by index (Fin n), not up to renaming: the same prefix with renamed variables in front of the same matrix can fail the criterion (prefixCritB_renamed_false); formulas whose equality depends on a symmetry of the matrix are not recognized unless variables are aligned first (not proved here).
- One sort and an arbitrary predicate as matrix; entailments that depend on the matrix (for a specific R) are outside the claim.
- Does not give a normal form or characterize equivalence classes of prefixes.
- Partially ordered (Henkin) prefixes and dependency-quantified formulas are not covered.
- These are statements about a toy prefix language (a list of (quantifier, variable) pairs over one sort, in front of an uninterpreted matrix); model–system relation: none proved; they neither establish nor refute the corresponding claims about any real specification language.

#### Non-claims of 8. `prefix-criterion-necessary-two-point-base`

- SEntailsAt uses environment semantics: it quantifies over every matrix R and every environment ρ : Fin n → α. When α is empty and n ≥ 1 there is no environment, so SEntailsAt α φ ψ holds vacuously for every pair (sentailsAt_of_isEmpty); in particular the closed implication (∀x, P x) → ∃x, P x fails on an empty type (closed_forall_imp_exists_iff_nonempty) although SEntailsAt α [∀x] [∃x] holds there. For prefixes that bind every variable, SEntailsAt at α equals entailment at one fixed environment (sentailsAt_iff_fixed_env_of_covers), so the quantification over environments can make a difference for prefixes that leave a variable free and for an empty base type (sentailsAt_of_isEmpty).
- Necessity uses arbitrary matrices; for a fixed matrix, entailment can hold without the criterion (for example any φ, ψ with the matrix True; not proved here as a separate theorem).
- The countermodels use matrices built from equality with constants and a two-valued function of one variable; with a restricted matrix language (for example without equality, or with monotone matrices), necessity is not established here.
- Variables are matched by index (Fin n), not up to renaming: the same prefix with renamed variables in front of the same matrix can fail the criterion (prefixCritB_renamed_false); formulas whose equality depends on a symmetry of the matrix are not recognized unless variables are aligned first (not proved here).
- Base types range over Type (universe 0).
- These are statements about a toy prefix language (a list of (quantifier, variable) pairs over one sort, in front of an uninterpreted matrix); model–system relation: none proved; they neither establish nor refute the corresponding claims about any real specification language or about how readers compare quantified sentences.

#### Non-claims of 9. `prefix-entailment-decidable`

- No complexity bound is claimed (the function loops over pairs of variables and scans the prefix).
- ∀x entails ∃x at every base type because the environment supplies an element; on an empty base type the statement holds vacuously (sentailsAt_of_isEmpty), and the closed implication (∀x, P x) → ∃x, P x fails there (closed_forall_imp_exists_iff_nonempty).
- prefixCritB decides strength between prefixes over all matrices; it does not decide entailment for a given matrix: for a specific relation the uniform bound can hold (uniform_entails_pointwise_nonvacuous).
- Variables are matched by index (Fin n), not up to renaming: the same prefix with renamed variables in front of the same matrix can fail the criterion (prefixCritB_renamed_false); formulas whose equality depends on a symmetry of the matrix are not recognized unless variables are aligned first (not proved here).
- These are statements about a toy prefix language (a list of (quantifier, variable) pairs over one sort, in front of an uninterpreted matrix); model–system relation: none proved; they neither establish nor refute the corresponding claims about any real specification language or about how readers compare quantified sentences.

#### Non-claims of 10. `domain-and-premise-variance`

- No hypotheses: the four laws are biconditionals and the instances are closed statements.
- Entailment is for every predicate (schematic); for a particular predicate the implication can hold although the domain condition fails (for example with the predicate True; not proved here as a separate theorem).
- Does not say a range claim, absolute claim, or disjunctive-premise claim is false for the intended predicates; the countermodels show that it does not follow.
- The propositional converse of relative_to_assumption_not_absolute, that 'C' entails 'A → C', is not stated as a theorem (not proved here); the converse that is stated is absolute_entails_relative, over pairs of predicates on Nat.
- The four laws concern one quantifier; several quantifiers with domains are treated on the relativized-criterion cards.
- The premise law and the universal-domain law are the same formal statement; they are listed separately for their two readings, not as two facts.
- Relative completeness in the sense of Cook (1978) is a claim relative to an oracle and an expressiveness assumption. This card shows that a relative form does not entail the absolute form in general (relative_not_absolute); no relation between this toy model and Hoare logic is proved (model–system relation: none proved), and it neither establishes nor refutes any claim about Hoare logic.
- These are statements about the toy model (claims are predicates on an arbitrary type, instantiated over Nat and Prop); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language summaries, about any particular result, or about how readers reason.

#### Non-claims of 11. `drift-single-counterexample-versus-universal-or-subclass`

- An impossibility shown by one countermodel in a toy class does not, by itself, say anything about the intended class unless the countermodel is shown to lie in it.
- Interpretations are predicates on Nat (or on a nonempty α for the universal-refutation converse); no claim about particular real counterexamples.
- These are statements about the toy model (claims are predicates on Nat or on an arbitrary type); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language summaries, about any particular result, or about how readers reason.

#### Non-claims of 12. `drift-sufficient-versus-characterization`

- No hypotheses: every statement is closed.
- Says nothing about any particular checker or verifier; the checker model has inputs Nat and an arbitrary goodness predicate.
- Proving a checker sound and complete for one modeled property 'good' does not establish properties outside 'good' (not proved here).
- These are statements about the toy model (propositions, and checkers on Nat with an arbitrary goodness predicate); model–system relation: none proved; they neither establish nor refute the corresponding claims about any particular checker or verifier, or about how readers reason.

#### Non-claims of 13. `relativized-criterion-sound`

- In Holds the premise is an implication antecedent inside the scope of every binder, also existential ones: ∃y ∈ D (H → M) holds as soon as some y ∈ D falsifies H, so a premise that constrains an existentially bound variable is not a filter on witnesses and can make the shape valid (holds_premise_on_existential_trivial). Constraints on witnesses belong in binder domains. When the premise does not depend on the variables bound after a position and their domains are nonempty, it can be pulled out to that position (evalR_premise_pull_out).
- Every 'tight' entry of this card's hypothesis ledger (under Findings) is witnessed in the stated class. RCrit is not complete outside the fragment of the completeness card (for example rcrit_incomplete_singleton_domain), so a failed criterion part does not by itself refute the entailment (see the incompleteness card).
- Soundness is relative to the supplied tables; with unsound tables it fails (rcrit_sound_hI_tight, rcrit_sound_hM_tight, rcrit_sound_hJ_tight).
- Domains and premises are interpreted and fixed; the matrix is the schematic component. The premise is one named predicate on full assignments; premises are not decomposed per variable.
- No completeness claim on this card.
- Toy signature in the examples: base type Nat, four classes, three premises.
- These are statements about a toy language of relativized claim shapes (one sort, named domain classes, one named premise, an uninterpreted matrix); model–system relation: none proved; they neither establish nor refute the corresponding claims about any real specification language or natural-language summary.

#### Non-claims of 14. `relativized-criterion-complete-polarized-two-point-premise-free`

- Every hypothesis listed is witnessed tight by an instance in which all other hypotheses of the same theorem hold. Well-formedness of the prefixes is not assumed; the theorem assumes that no prefix binds a variable twice, and it applies to shapes that leave variables unbound (rcrit_complete_nonvacuous_free_variable). Nonemptiness of the domains is not a hypothesis; it is derived (nonempty_domains_of_rEntails). Universal domains of φ and existential domains of ψ may have one element.
- The fragment is premise-free in effect (both premises hold everywhere); with nontrivial premises the criterion is incomplete (incompleteness card).
- Flagging every domain as nonempty (normal form ShapeNF) does not restore completeness (rcrit_incomplete_in_normal_form).
- Completeness is for arbitrary matrices; for a fixed matrix it is not claimed.
- In Holds the premise is an implication antecedent inside the scope of every binder, also existential ones: ∃y ∈ D (H → M) holds as soon as some y ∈ D falsifies H, so a premise that constrains an existentially bound variable is not a filter on witnesses and can make the shape valid (holds_premise_on_existential_trivial). Constraints on witnesses belong in binder domains. When the premise does not depend on the variables bound after a position and their domains are nonempty, it can be pulled out to that position (evalR_premise_pull_out).
- The unpolarized form, with two-point domains everywhere and no hypothesis on α, is also proved (rcrit_complete_two_point_premise_free) and uses the same countermodel construction (rcrit_complete_of_nonempty_domains).
- These are statements about a toy language of relativized claim shapes (one sort, named domain classes, one named premise, an uninterpreted matrix); model–system relation: none proved; they neither establish nor refute the corresponding claims about any real specification language or natural-language summary.

#### Non-claims of 15. `relativized-criterion-incomplete-outside-fragment`

- These are the failures found; no claim that they exhaust the completeness failures for shapes with nontrivial premises.
- No complete syntactic criterion for the full relativized fragment is given.
- The soundness theorem is unaffected: in every listed instance the criterion fails, it does not hold wrongly.
- rcrit_incomplete_singleton_domain violates two hypotheses of the completeness theorem at once; it is listed as a failure, not as a tightness witness.
- In rcrit_incomplete_false_target_premise the source shape plays no role: every shape entails every shape whose premise is unsatisfiable and whose existential domains are nonempty (such as ∀x ∈ Nat (⊥ → M) here, by evalR_of_valid).
- In Holds the premise is an implication antecedent inside the scope of every binder, also existential ones: ∃y ∈ D (H → M) holds as soon as some y ∈ D falsifies H, so a premise that constrains an existentially bound variable is not a filter on witnesses and can make the shape valid (holds_premise_on_existential_trivial). Constraints on witnesses belong in binder domains. When the premise does not depend on the variables bound after a position and their domains are nonempty, it can be pulled out to that position (evalR_premise_pull_out).
- These are statements about a toy language of relativized claim shapes (one sort, named domain classes, one named premise, an uninterpreted matrix); model–system relation: none proved; they neither establish nor refute the corresponding claims about any real specification language or natural-language summary.

#### Non-claims of 16. `frontier-testing-detects-overreading-for-closed-readers`

- Vocabulary: 'supported' is Supported E q; 'unsupported' is ¬ Supported E q; 'contradicted' is Contradicted E q; 'undetermined' is Undetermined E q (unsupported and not contradicted). An unsupported claim of a satisfiable report can be contradicted; an undetermined claim cannot.
- Upward closure holds for unsupported claims, not for undetermined ones: strengthening an undetermined claim can make it contradicted (undetermined_not_upward_closed).
- Real readers need not endorse all entailed candidates; for a reader whose endorsements are not closed under entailment, frontier questions can miss over-reading (frontier_test_hclosed_tight).
- Because claims are predicates, every endorsement predicate treats logically equivalent claims alike (endorsement_respects_equivalence); framing effects between equivalent phrasings are not representable.
- The test covers the candidates in Q: an unsupported claim outside Q is not detected even for a closed reader (frontier_test_outside_candidates). When the unsupported candidates are pairwise incomparable, every one of them is a frontier candidate and the test saves no questions (not proved here).
- The theorems concern positive over-reading (endorsing unsupported claims); they neither establish nor refute any detection property for negative over-reading or under-reading (not proved here).
- Entailment is semantic; whether a reader recognizes entailments is not modeled.
- These are statements about the toy model (claims are arbitrary predicates on an arbitrary interpretation type; a report is identified with the finite list of claims it establishes); model–system relation: none proved; they neither establish nor refute the corresponding claims about natural-language reports, about any particular report, or about how readers reason.

### Escape hatches

Card 5 (`meta-level-questions-are-never-undetermined`) is the one impossibility result. Its hypothesis `hq : WorldIndependent q` is tight (`worldIndependent_tight`, which is also the positive control: the world-dependent claim b = true over Bool is undetermined by the empty report). Two modeling choices, neither modeled nor proved here, would defeat it: a reader who sees an excerpt instead of the full report, so that the report itself varies across the interpretations consistent with the prompt; and reading "establishes" as derivability in an incomplete proof system instead of semantic consequence (`Supported E q`). In either case a question about what the report establishes need not be world-independent (not proved here).

### Tightness status

All 92 recorded (hypothesis, theorem) rows are `tight`, each with a proved counterexample in the stated witness class. No hypothesis is recorded as `harmless` or `unknown`.

### Not examined

- Natural-language meaning, hedges, examples, scope statements and other prose of real reports; the process by which a reader answers; any particular report.
- Several sorts, function symbols, connectives between quantifiers, partially ordered (Henkin) prefixes, a restricted matrix language, and renaming of variables in claim shapes.
- A complete syntactic criterion for relativized shapes with nontrivial premises, empty or one-element domains, or repeated binders (card 15 lists failures of the given criterion there; it does not claim that they are exhaustive).
- Detection properties of frontier questions for negative over-reading and for under-reading (card 16 concerns positive over-reading).
- Whether readers recognize entailments, and framing effects between logically equivalent phrasings (claims are predicates, so every endorsement predicate treats logically equivalent claims alike: `endorsement_respects_equivalence`).

### Disproved or dropped statements

None. Every statement recorded for this package is proved as stated; no statement was found false and none was dropped.

## Evidence

**Kernel check.** Basis: execution (Lean kernel check). The library builds with `lake build` under `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) with no errors and no warnings, from a clean copy with Lake's artifact cache disabled, so every proof is re-elaborated and kernel-checked. The Lean sources contain no `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`, and no `axiom` or `opaque` declarations. An axiom audit with `Lean.collectAxioms` over 820 declarations of the library's modules finds no axioms other than `propext`, `Classical.choice` and `Quot.sound`; the per-declaration record is `audit/axioms.json`. Observed 2026-11-21.

**Statement and closure hashes.** For every Lean name referenced by a card (`lean`, `lean_names`, tightness counterexamples, non-vacuity witnesses, positive controls), `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (the sorted list of `name : type := value` for every package constant reachable from the statement, theorem bodies excluded), with the closure size. For a definition listed by name, the statement hash covers its type; its body is covered by the closure hash of every listed theorem whose statement reaches it, and every definition named in this report is reached by at least one listed theorem. A change to a definition reachable from a recorded statement changes the corresponding closure hash.

| Lean name | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :-- | :-- | :-- | :-- |
| `A` | none | `767950bd1b7f8d0d22fd3f389e70e0c04f03082a38953c1c0b1b1a46e91883b4` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `absolute_entails_relative` | none | `f4bbc9c2f8ee3fd400607e2e53a809cfa131d4e8d4371d63a8dcab90529c9149` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `absolute_entails_relative_nonvacuous` | none | `0beb81b214cfca836a38fe399fab116604ecb19d7a5face686c078ed018fb455` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `acceptAll` | none | `f3879aa3f9ec90750005d7a367e1ca8efcfff43656cad8bb70fc1be75a5eee2e` | `a82590f90bae108019b632d5482b7ee08c79b30b7f59fc4c5171e3c4b2165571` (2) |
| `and_answer_h_tight` | propext | `ad0265076eb4ff57695a8dba3122095b2b35cc5ed2145b1909953094a81ae16e` | `9292a56b92bd9abfe0c24bc8bd64ee79d4e1c9be6dbd5f66579cebf0cc55054f` (17) |
| `and_answer_hE_tight` | propext | `e36c7e80362da358fa22ad059271cb75f9a7754667210e90336b9716bb0b6ca9` | `274113561d93cb51e0c2da25d47c6cfaabbac7abc95b8e2c11f86b7c80870dc5` (16) |
| `and_answer_h₁_tight` | propext | `22bcc9bd4783a83639c79306584e14a5ae27e00847a33940d95541a241ee1e00` | `9292a56b92bd9abfe0c24bc8bd64ee79d4e1c9be6dbd5f66579cebf0cc55054f` (17) |
| `and_answer_h₂_tight` | propext | `cc2ac3ebd27fbfc4d2162f07f6e0c9f651d7368598d9fd7c0860996a998e7620` | `9292a56b92bd9abfe0c24bc8bd64ee79d4e1c9be6dbd5f66579cebf0cc55054f` (17) |
| `and_answer_mem_andTable_of_satisfiable` | propext | `d113481c00518d930955e5ff727d7cca6da4533f4895cb85286230f90dd282b7` | `274113561d93cb51e0c2da25d47c6cfaabbac7abc95b8e2c11f86b7c80870dc5` (16) |
| `and_answer_nonvacuous` | propext | `38850f24afd4d33f0f699a3fc2a1f0fe1e2b0ce88e013c106b6eb1bb014808b7` | `9f68cff97b6ddd0c2ab0412e009be52c2a147141b2a0fed6630efca40d31e752` (17) |
| `andTable` | none | `c6bc19812adce16874b056614a2366a7a74eaf820e366af163615f2483d8d3f0` | `62f9234db4b05f6f62837850d92d4a329603e61df3e111193714d89e3544f357` (4) |
| `andTable_realizable` | Quot.sound, propext | `c2000907370cc01b70502e3ddff40cdce4401bd5469b2299471aa4008c0fcc4d` | `db4c6d6c1f6d8f577c657c41f957ad58b77866a959b9cc922cf116210fd675a9` (16) |
| `andTable_undetermined_cell_distinct` | Quot.sound, propext | `387658890b87522f257d2442b8939aeaadd6ff198edbf8630217d78d6e783026` | `d669e0c923af6bb8919d8167d6588da4a41a5d1eec5e07c23934d43880c2d5cb` (14) |
| `Answer` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `answer_changes_ha'_tight` | Quot.sound, propext | `ee49180f07901fb8bcf2d70f904fa127e584e26c3c507f914887aae3aa79f410` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `answer_changes_ha_tight` | Quot.sound, propext | `3848425b9a0aed2841e2cfac8b0d425374877efc63b7f1ad5567ac271c39bfe6` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `answer_changes_hsat_tight` | Quot.sound, propext | `3e93c5a304b653bc874006ad215c68a2925ca51aa3d978e3b9751cc09ea2a5b3` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `answer_changes_hsub_tight` | Quot.sound, propext | `98f7e4f4df38dd01f72cf1f5ced7bb98c3b2729e3244754152330fddd3dcd32a` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `answer_changes_nonvacuous` | Quot.sound, propext | `4d392fdf07cb8cd1f20a9b878da8eabc1d9298b01742a2689eb1b750bb9ccbb3` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `answer_changes_only_from_undetermined_of_satisfiable` | propext | `4d39a908ee776500dde1785e03fcc4aaf0869ff5ef0f6f7911de94588fed062e` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `AnswerKey` | none | `da46238a3c743dcbbc48f1d0d2464e94469b283ac56bf5ddb75aea16bf58d296` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `BB` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Binder` | none | `b5b87be8f8f501aa45ebe3c5bd924517a86ee6c518cbe4696d560447a851f73d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `bOf` | none | `a0e7325b06077367c8b0dedabec8bd7746050e2ff69ea917e1415e313507dce4` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `bvars` | none | `d71072ec9a544028168b6f583071184357b20da28e304e91a7ec71f3d3ee4339` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `candidates` | none | `f4b4d506138961e1d0e6bbdf7d168ac6f98d6939107b458aa90ff55c02c9cfab` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `canon` | none | `5bc25c9a8122e43754ee5fae95a10d1e64fd2459ee361f85202c8cbbdab092b5` | `29b6699a00e1921bf17ab3b88a2d3356ce7b2398911d8558892c8788517b514b` (5) |
| `characterization_entails_sufficient` | none | `f1f338a806de5c08da4908c0554c72c768edee2a65d75df1a0dfaf43b05e8d21` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `characterization_entails_sufficient_nonvacuous` | none | `84a338f30ac9b1f602956b746238efa2e241206c90c2a01c7a7598768931f0fb` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Checker` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `checker_complete_not_sound` | none | `88f374ee287d8d8f4102d5a1c057553d1b66d597cf1e4c1a970ff0b71b64e6fc` | `c49fb531c9bc885ad92e2a17aacecdec4104feadcedf9f7a779ec772d51e32f3` (8) |
| `checker_complete_not_sound_witness` | none | `250edb7463dfd71f46368641d42a6fd558e944137a41b559f93a37d3c7d6ba3b` | `a949067362160625299a587260c81fe4383219e48e509ed29262e23c0d3163f7` (7) |
| `checker_sound_complete_entails_sound` | none | `00b3529858b6edd23353dd982611cf7d404e2711e22874a2fc06196d4522829c` | `c49fb531c9bc885ad92e2a17aacecdec4104feadcedf9f7a779ec772d51e32f3` (8) |
| `checker_sound_complete_nonvacuous` | none | `281781b7ed17027be8d09e2bab0f2ca792c99d0b800b482d6e84727f6195d9d3` | `9067dd904313c0f455dd24d791a34b88e81e4a89761e9d4d623ef810acfe9e55` (7) |
| `checker_sound_not_complete` | none | `f2cc35151dd10dd7aba842c46fd28efc66daabaa14ac761b8124e4b46983d1ed` | `c49fb531c9bc885ad92e2a17aacecdec4104feadcedf9f7a779ec772d51e32f3` (8) |
| `checker_sound_not_complete_witness` | none | `e1dddee1e3cfc84fd00a4038599445f72c65ddab4aa07eb8179192069c371984` | `2765cd89df997a2a7add6ec4ce4c3ff7da4a8ef39a367adf959a884711a8663f` (7) |
| `CheckerComplete` | none | `2d3510a2a2042c62c1c2d337681e9720a494c6a67138261d90f2de2e83124150` | `a82590f90bae108019b632d5482b7ee08c79b30b7f59fc4c5171e3c4b2165571` (2) |
| `CheckerSound` | none | `2d3510a2a2042c62c1c2d337681e9720a494c6a67138261d90f2de2e83124150` | `a82590f90bae108019b632d5482b7ee08c79b30b7f59fc4c5171e3c4b2165571` (2) |
| `checkerSound_example_pos` | none | `fcf63c16041bfaedfcae3b6a7060a921272023f46c0f983243fc35c04915847f` | `76d471cd9255dfaa8c3d9cd40ef388f1e199ff76528324a0b005d5d86202da1f` (6) |
| `Claim` | none | `da46238a3c743dcbbc48f1d0d2464e94469b283ac56bf5ddb75aea16bf58d296` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `closed_forall_imp_exists_iff_nonempty` | none | `02d5e09433d26de0d113a967efb52392ddaff302cf8c6d4766bb1c8935b17cb8` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ClosedUnderEntailmentIn` | none | `c60b06861cbdd821e15baff281a379ee8ac1e55860530705c3b949e8849f2a4d` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `Cls` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `clsI` | none | `e29a9e639323a4bbcf94279819d610211afb4aaabb45700f38df850342f972af` | `48b5be257108d7aa08d10bf7bccf36c8e3e2900d1d32604ff3c3142a642a9cf4` (5) |
| `clsIncl` | propext | `44983f869f51fd894d2f4968baf938e4e19417f453f12787e09013a78538c845` | `48b5be257108d7aa08d10bf7bccf36c8e3e2900d1d32604ff3c3142a642a9cf4` (5) |
| `clsMeets` | propext | `44983f869f51fd894d2f4968baf938e4e19417f453f12787e09013a78538c845` | `48b5be257108d7aa08d10bf7bccf36c8e3e2900d1d32604ff3c3142a642a9cf4` (5) |
| `conj_premise_not_disj` | none | `8393b69c9ffb23cc5c64ff8c64cde9150bf297fb19e3851b4d995dd109a6767a` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `conj_premise_not_disj_witness` | none | `d0d4e2fc7ea24d26493a45c18c5dfd24c1067b2252f45c57dbe689786e9a8d2d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Contradicted` | none | `12c6fcea22bf37ac03ba6bf6639b66890ff6618c980f741522760537d735bde7` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `contradicted_iff_supported_not` | none | `95a9b683abcfb6a64d14c7695801dcd945748597d03055b86a06883866fe017d` | `b1fa6e5978acc19da6e6b1a3035e7f41f92c070c8ba0636a861c978e73f70a15` (4) |
| `contradicted_jointly_without_single_claim` | Quot.sound, propext | `aa9a8200a6c4e1c60fe8f2e99c79eb86646dc666b3b28890ffcea5571122cb7d` | `4970fa35f75dbd728cf0970cd0a0b897fa305cc2c3249673c01018b03affba70` (5) |
| `contradicted_mono` | none | `58d8b931b52411660d7346bf79172ab05e7344a9746f3e5b0d53191bfb2d63d9` | `dc08fa2bce31a46f42ffdbcae555b91ab183549714122facdee09eac8f4ca957` (3) |
| `contradicted_mono_h_tight` | Quot.sound, propext | `f1801c2a15ba4f0ac814005c78785e123a8838ca93a9096cd1dd7cacfacbbb55` | `dc08fa2bce31a46f42ffdbcae555b91ab183549714122facdee09eac8f4ca957` (3) |
| `contradicted_mono_hsub_tight` | Quot.sound, propext | `96542b186ef90bc3a8c28dfa6f1efac81d8ab376c6a1d08ba14dbc04168f1769` | `dc08fa2bce31a46f42ffdbcae555b91ab183549714122facdee09eac8f4ca957` (3) |
| `contradicted_of_mem_entails_not` | none | `f69c79575a5ee60c92a8291e275e6f114700e34dd67ff4c100131b2f66f94e95` | `b9fe8091d0de99ac627fd3974f89428ad13342735485b3da96676599c6591ca6` (4) |
| `contradicted_of_mem_hc_tight` | propext | `206dfc4143992156e29a64006843d3fcf16bf0d1e0e85599d5313751e7973a3a` | `b9fe8091d0de99ac627fd3974f89428ad13342735485b3da96676599c6591ca6` (4) |
| `contradicted_of_mem_hneg_tight` | propext | `d8467aee0a635647520a75bae9709b14f87452d05284253581488c337e675f26` | `b9fe8091d0de99ac627fd3974f89428ad13342735485b3da96676599c6591ca6` (4) |
| `contradicted_of_mem_nonvacuous` | propext | `7be3904138119478f794f41ea38b058c5920ae2f23e3d759466031f620abae41` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `Correct` | none | `f63bd08a07bd5db0c7b39d1321ab79d6fd758b8112120761dd80f2a2cc6cbf48` | `436d98f026e8ac651cd55d785a36c6cf5be741b3a9ea13cc37b8cc2fce970323` (5) |
| `correct_unique_ha_tight` | Quot.sound, propext | `92af5ee4f1d3afbf45e5efe44b4fc27bf10d99d86b395ca25cf85303e3d4f797` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `correct_unique_hb_tight` | Quot.sound, propext | `fa65d9e8b9e2e0b2dfbe89607c247d3a46a053fbbd3998cc414f22ab90b305d3` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `correct_unique_hE_tight` | propext | `67c6dabfcbf674219fd4428a56e27924e63cf84ace11188f70eab371b76f347f` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `correct_unique_nonvacuous` | Quot.sound, propext | `143e720b67efb1e53351bcc7df36390103d9615bf2fa126d7ac1beb64791878d` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `correct_unique_of_satisfiable` | propext | `5a04918ba3a63bfe96b10804b8ab77fd55fb04c990e2d06e3297139207fdacf0` | `ad1106efbebcb1f66f2cb32c46b773fa8c7a06eddd5cdfe75c6b914cb0a15a62` (14) |
| `counterexample_in_class_not_in_subclass` | none | `1a2926d9d03a395db018dc7f928d93d3726a7b4d9661f3264976e8945a2e390d` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `counterexample_in_class_not_in_subclass_witness` | none | `d87e325b8c68b59be3e795176b87ceb6260eaa2c5fbc559764bb131f5c370c23` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `counterexample_in_subclass_lifts` | none | `3141f61d0c994a211c8ea35c043b603bbe5494b8bf775812440d2636f48e9b49` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `counterexample_in_subclass_lifts_h_tight` | none | `26c9bab8907575893955dec34c7f09cc0cd6266c31272020a071b72d6726ce2a` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `counterexample_in_subclass_lifts_nonvacuous` | none | `f5654dbf89308e0cfd9a42593ddc18a51b8207e7b1a06cff80b7399e48e60a9c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `disj_premise_entails_conj` | none | `0d57c57ab149606658360b0f8ee0c626c783723cf0f6b445d0a13c053d61446c` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `disj_premise_entails_conj_nonvacuous` | none | `434aa82c16012c3c146b92568abc066b77861f3a495a0cc21bde9cdd86905d74` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `domain_variance_nonvacuous` | Quot.sound, propext | `54e40aa22f8601c62350c3a7108250e3061d6c2a8135b82e01cd77b17406a5de` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `emptyI` | none | `22834ee05170fae229e1db52ce91b36c72af58647a007dece722e0d307061d35` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `emptyJ` | none | `a7fae823eb96b919ad2bf7b9475d016baecef839848aadb2dba376f3fc779f25` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `emptyφ` | propext | `9fedebf6aa4333db86d55f51d00e908cbb9ab34e72346f5fa70d8b28b13ed49f` | `b748b8aca9d7960c4adf24a7e8920cfc186b456a5d061a76d5ace9f4f1d68c2a` (7) |
| `emptyψ` | propext | `9fedebf6aa4333db86d55f51d00e908cbb9ab34e72346f5fa70d8b28b13ed49f` | `b748b8aca9d7960c4adf24a7e8920cfc186b456a5d061a76d5ace9f4f1d68c2a` (7) |
| `endorsement_respects_equivalence` | Quot.sound, propext | `16e89655f648691f60d75f6ef1a18bf94e946ffd8553d0123ef2c0b0d55beb84` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `endorsement_respects_equivalence_h₁_tight` | Quot.sound, propext | `98ba7137c60da6fc304e2b73943bacda57d3ddae4a48f4f1ac36f2a4c09b2d63` | `d8146353af6f1419ca04151f978033a24fef4ba6f6c1eb69f8540fe2b8a94f91` (4) |
| `endorsement_respects_equivalence_h₂_tight` | Quot.sound, propext | `572f14cb00882744d51f7db9f4567e00feffb5a0ff72a8f8abab1572b8244ead` | `d8146353af6f1419ca04151f978033a24fef4ba6f6c1eb69f8540fe2b8a94f91` (4) |
| `endorsement_respects_equivalence_nonvacuous` | none | `0bc168ed7a2c05409c479f8150c4a6b2a7d83cd875e5ed1dd2f49ba70c3caa6d` | `a1e81b714e8c69d679c0df9af1bf7caf3a84a7bea7bfe62da0ff3436c07953b9` (3) |
| `Entails` | none | `ebfb10af5684e3fa3559bb6d87ebf5d93b15f24819f48705a2d98dbeef8350b8` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `Establishes` | none | `cf6ab6c4f54860f9718cc395baec2dfc20d86914ae9f274b5f8e82ee75a4b559` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `establishes_answer_key` | propext | `f33893c30fd413333beac3f2bd23b4622dca9329004ff3e5121f56f9340ca72f` | `07f09cac15f00b6fb0c7d4fc272d2aefafb34c4fa6b64459b0b40ec1f67490dc` (16) |
| `establishes_answer_key_nonvacuous` | Quot.sound, propext | `56831470f9abd021377f1761e8d16d5079fe8d2c0b6497818044c63b7144b9f9` | `0522629101f1e608fa218885d2b8099880403b0faa10d7f61748f4244171b88b` (7) |
| `establishes_answer_key_tight` | propext | `bf7ab7f286e5b9bcf7ccf0a92a59f6444b9bda73c7d108b24e13450872f38560` | `07f09cac15f00b6fb0c7d4fc272d2aefafb34c4fa6b64459b0b40ec1f67490dc` (16) |
| `establishes_contradicted_h_tight` | none | `a0b76653bf56eda3f93e93089aa14c8d50292a303a13ddc29cd4c50ec674d79d` | `837fb022c01b6a0cd31655c8473d4faea37ebc4ba9bb36992866ea552a33da2c` (5) |
| `establishes_contradicted_nonvacuous` | Quot.sound, propext | `8822b4861dc70a4945d784c5e9c04f1bef46f379b14f9bc809d920a58c90bfcd` | `3a4056bb4132181169c15ec788e95df76278cb0fb765bbd174affcdcb241c71d` (3) |
| `establishes_contradicted_of_unsupported` | none | `821805de6786e7c3ff6a50d1bedac0f8c725a3a5573ef2a5c32b15fa05b939e3` | `837fb022c01b6a0cd31655c8473d4faea37ebc4ba9bb36992866ea552a33da2c` (5) |
| `establishes_undetermined_key_never_correct` | Classical.choice, Quot.sound, propext | `c27a3680a960080bf8d874eaf0ce4dc90609610de2b06cfad52c360dc67bc143` | `07f09cac15f00b6fb0c7d4fc272d2aefafb34c4fa6b64459b0b40ec1f67490dc` (16) |
| `establishes_worldIndependent` | none | `0ca40c146df389e5bb00237d862d190c2871ad22ed77659827891693a2adaf43` | `17efcc77cd32e6ece749ac510ef1cb411ac24d006ca31fd09eb681710b51ed11` (5) |
| `eval` | none | `0431ba49f4be9a8a73fc9ad78f0bf41df83f938bdce16ae1b90a83f5b2c2bd3f` | `ff123798b8ab9eb4cb64b51016d4ae17ce5493549a9bcc11c688331588011920` (6) |
| `eval_env_irrelevant_hcov_tight` | propext | `fb48e402b965d2b08b06026a925bdd025c3bae155cc99941f2d7762f25e25c7a` | `421cba61038821eeaeaa29b0c0028ef83f5be8cb4d38fb0fc3920298f2ed5294` (19) |
| `eval_env_irrelevant_of_covers` | Quot.sound, propext | `a5f998734d2a7cbe5af1ec1c413d83d97f6dc6d252c0b83d479e788dc6b6814d` | `421cba61038821eeaeaa29b0c0028ef83f5be8cb4d38fb0fc3920298f2ed5294` (19) |
| `eval_env_irrelevant_of_covers_nonvacuous` | Quot.sound, propext | `fd7aace6ceeb811fe0177224c3ac5ff77bf853e70c38169da80887b820e16050` | `6de6f57ebcbfc16985e287cabf934bc8d7cafb64c05aec9b86751cb27d1eb224` (8) |
| `eval_subsingleton` | Quot.sound, propext | `339bb825b5989b68bddcad7afe7134aab7f3eb9ccbf97185ae9d05d3e9a359f3` | `6ca1f509280163a80b6cb7498863f204aab1ee754aab5720fe01a8c35b80fd41` (18) |
| `eval_subsingleton_tight` | propext | `704281cdd6ce8f08dfed84f91f4227010c2478f3c91073bb7f1cb5e6e945294d` | `e271b2f874161374ba991b8493592c09d32ad304cb25eb8715d455b6e8ab446f` (19) |
| `evalR` | none | `d8fafeac8c06355b9562d520eca70da063538e3793184163466e5679e3417d54` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `evalR_of_valid` | none | `92804d2d7e01e172cfe8a43780f78f5ad3e6fa0c57d6d57852d8fbe8860acf04` | `c4e670f691d3de675d033ed28f9db470774558b6a5b75874d20ee73e983e53d1` (16) |
| `evalR_premise_pull_out` | Classical.choice, Quot.sound, propext | `5b22fcbc665c7f0fcd801f2da5221fb800134ca2b76210ba05cfbc65459acfd4` | `c4e670f691d3de675d033ed28f9db470774558b6a5b75874d20ee73e983e53d1` (16) |
| `evalR_premise_pull_out_hind_tight` | propext | `7659792e68d744063647923acddde91b7b5561b4daac17ebd5fe330b0f3dfc37` | `f3c3e8cb4b7951d35b652cda40af3fd67b0c12b34d02f96bedfc80e7262b4de5` (25) |
| `evalR_premise_pull_out_hne_tight` | propext | `7b018763015b3f04d84b45034b80c16a2a8fee6bb68c16fde5a61e06932aa380` | `f3c3e8cb4b7951d35b652cda40af3fd67b0c12b34d02f96bedfc80e7262b4de5` (25) |
| `evalR_premise_pull_out_nonvacuous` | propext | `d668f2bd4712beaea9556417ad8f22988179a5c3af6936f9951e9323d69aeb15` | `455726df1dc624277446bf16141eccb8f824d0a1ba3c893523c1445a0dcbea40` (17) |
| `evenChecker` | none | `f3879aa3f9ec90750005d7a367e1ca8efcfff43656cad8bb70fc1be75a5eee2e` | `a82590f90bae108019b632d5482b7ee08c79b30b7f59fc4c5171e3c4b2165571` (2) |
| `ExactlyOne3` | none | `5e180d8ae00e5587c1ff52008c8ae7fbf2f387d8e203a75769c114071de656b3` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `exactlyOne_answer_iff_satisfiable` | Classical.choice, Quot.sound, propext | `17957e644aba052617f0213ba5cdc6eba99a0bb38486d527221871bf25ec63b3` | `2db7d928281e7d27cd8e1ab63b3112c5384c477142a4c47208d214bb54ef842e` (7) |
| `exactlyOne_nonvacuous` | Quot.sound, propext | `767b4146f22a84eccafb9921ed96a3196d586cff876346d67f1fe5f6b235bf8b` | `ed19f085fcffb9d10c0cb129c460c70ec0587e828029156d6a543d582eb66272` (6) |
| `ExDomainsCovariant` | none | `99d5ee5e8264b304a4d5c548044c8ec381ded1f0fae15dbba25feadca9b9fd71` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `exists_correct` | Classical.choice, Quot.sound, propext | `2865f40ec250e7e758b8cc4e2e7c496cf923ecab8f3aab662eb361578c68480d` | `7791f574a62a6833a43ab18cf8d447487fc1639dc3e8f7b3fa637ad28744faeb` (13) |
| `exists_domain_entails_iff` | none | `badcadd0a676e8e881154132d1d5e8698e4d46b94019c8563a301966765256a2` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `exists_forall_sentails_forall_exists` | Quot.sound, propext | `1bf921f3a3a58be64679a70b9b474827ed5296be71bb905162325442555d8bd5` | `9857351d10ed78c77fc34cb09a44d2101a4fd710dc41c49146afe421505fe726` (21) |
| `exists_frontier_below` | Classical.choice, Quot.sound, propext | `14158c3e6ba9d2c381e9dfd43eaa87493ac3bbf360863d9617fd04c621283a57` | `ecc8b80a515bde255a1ed4320fcb398f70946c2d7d1725b9db32149b241f1140` (5) |
| `exists_frontier_below_hns_tight` | propext | `53347b10cd895d2a9d5b58837ba06c256338c8e06cb3a66a9c1a25998b42695d` | `e949838e7c27f5142fa66aca2036463fa29af62a06777c1b8e7a366467871bdd` (9) |
| `exists_frontier_below_hq_tight` | Quot.sound, propext | `4509026df635686f1b7ee0b120d565d8ab6b86f6515d49a5fe2a9b512c7e62be` | `ecc8b80a515bde255a1ed4320fcb398f70946c2d7d1725b9db32149b241f1140` (5) |
| `exists_frontier_below_nonvacuous` | propext | `77dbf3854dbdb63aa5ca4a01efc797ed1cf6a68aaf1858064a2bf8d17a0e4a6b` | `fee025ceb57df4c303c1b314013e53220e7d13acb485f8d85de88d25b2a062be` (7) |
| `exists_not_sentails_forall` | propext | `66566ba7cfeb97adca9f18f37f4345e933e9c54c95ff717c43999814bb1775ce` | `9857351d10ed78c77fc34cb09a44d2101a4fd710dc41c49146afe421505fe726` (21) |
| `exists_weakest` | Classical.choice, Quot.sound, propext | `af3d66da94f1ec12b4d4b6f01517b296f85964c4f59253755797b59568001cb3` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `exists_weakest_nonvacuous` | propext | `98702c29767d756862948165953e598776dd31292bb5ed538e9f2331b1738696` | `421d043d1619d5f37027c0760ae1d96236f5a73d8ceee35ccb0d4f1368d24a89` (5) |
| `exists_weakest_tight` | Classical.choice, Quot.sound, propext | `42fcb97abad64253004679f8cd7909ebc999082db43d51b5649064a740f38326` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `forall_domain_entails_iff` | none | `55e9d776a0ac2997ef1f85f4bb05b583a7d6f1719deaeb857a1c1d07a59e4ccc` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `forall_exists_not_sentails_exists_forall` | propext | `c0f82ff7268ec79ce1474d841b1946c0719c13ac760121ee4dd7460bb281f9b2` | `9857351d10ed78c77fc34cb09a44d2101a4fd710dc41c49146afe421505fe726` (21) |
| `forall_exists_not_sentails_exists_forall_witness` | propext | `92f06d6f292fc9ca3a63931af43a2997ab4baa6a181b5cc84c9577c9257b73a0` | `45428fcc95919fd7125f4deb95a00bd70ff20133450de4f2a344dd6c661cefba` (20) |
| `forall_sentails_exists` | propext | `6a8d46d6381fc21db6b6acc8ed421626e0b55e82fbc703d3424476e37b39e8c8` | `9857351d10ed78c77fc34cb09a44d2101a4fd710dc41c49146afe421505fe726` (21) |
| `Frontier` | none | `1fe4e578a27a1498303f7785043668dc16f7d233bd02fdb4c986244ad7e2dd1d` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `frontier_test_detects_overreading` | Classical.choice, Quot.sound, propext | `84ed5229c0c861e3a23564a04e6c8dc0db88df9874a38d8161c42912706c64a1` | `398a78368d013f891c238c43385d6fab494fc6d3ae42665aabc99fc81310f3de` (6) |
| `frontier_test_hclosed_tight` | Quot.sound, propext | `889931d8f696a63507a15a2333a3c83a73f877648d3c4c4d43fb325dea85312c` | `6f6598ab378850bfadfb6f35ca08793dabb3eb857ae462488af65868667d774b` (15) |
| `frontier_test_hfront_tight` | propext | `dff8252b63123fe02866a31d7c790c7f52f35df5cfd53cf33fcba73bf5126600` | `6f6598ab378850bfadfb6f35ca08793dabb3eb857ae462488af65868667d774b` (15) |
| `frontier_test_no_positiveOverReading` | Classical.choice, Quot.sound, propext | `c626c0768edbbecd37c7a7d95475326a703a29b1ee7286040c3376e4f39decae` | `ce6346c48056d73eb0f2ab343f3cdf8d225c7c7a713d0fe2950109aa93838035` (11) |
| `frontier_test_nonvacuous` | propext | `fe520bc0706bee291ee1d73b2ae8620cb5938fb0a754b989cd45879f454615d8` | `5c520f53f3c9aede5ca10d6262975c1d5dab7132d9a905780d6db47fc0c8369f` (10) |
| `frontier_test_outside_candidates` | propext | `3ffccf4b0acd825149dfca1560f980f4627281a4513d26af3aa9bfca587293de` | `a63c50b8fb189849fe24317a6336024d9f6444f87025187e9743036c1ec81d27` (8) |
| `Holds` | none | `c80b458c025c1830d3dbad35e9fc7f9d32c057fb804769a61023b405472b3fba` | `b748b8aca9d7960c4adf24a7e8920cfc186b456a5d061a76d5ace9f4f1d68c2a` (7) |
| `holds_premise_on_existential_trivial` | propext | `2ac95a71990dbff23f729d348658c931a22eb4146939b81f990674afb6e96df7` | `37e5d0f538af8a0243537bfacb824398fdfae574d4cb825ed3b11781a5f304b2` (38) |
| `ImplExact` | none | `478b9695f5caf95e74de5d687c23958234a6466662abcb4212100ec5637badd7` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ImplSound` | none | `478b9695f5caf95e74de5d687c23958234a6466662abcb4212100ec5637badd7` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `InclExact` | none | `3194597df57b35dab3c287005ac44b7786232b707e906cd3fa450e139c962f2b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `InclSound` | none | `3194597df57b35dab3c287005ac44b7786232b707e906cd3fa450e139c962f2b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `incorrect_iff_reading_error` | Classical.choice, Quot.sound, propext | `574df77d48a4409f7aa3c7c783a9902666d9d29f297940c334bc6da0cc20837e` | `49d4e104f0d426d4e249071d415f646e7ae25b42175312854c1740fdaa3e61de` (16) |
| `InstantiatedDomainsMeet` | none | `2fa1b7e47e95935d69d2b9e58e622725ecac5f9576914100a0945d3ad07394b3` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `KeyCorrect` | none | `20dba76e593b288631ad4064cf1ea07ce40522f1c26dae94a69c15c31cfde978` | `d9c59f6b323140cee91a920043ebac636aac72862f4ed8fd6af5b7da96693fe1` (6) |
| `MeetsExact` | none | `73a5a54848793298b450c721e175c2a4481e8b0ad2fb988c6a616316bc12e55c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `MeetsSound` | none | `73a5a54848793298b450c721e175c2a4481e8b0ad2fb988c6a616316bc12e55c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Models` | none | `7b1dfed33f6cd05d61304130e317718f4bee955ec93bd55a83789f54b8ff8a2c` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `mono_nonvacuous` | Quot.sound, propext | `bf972825f234f286338d38b13d6e18a5889b378872126df4811d5fa9f182486c` | `b1fa6e5978acc19da6e6b1a3035e7f41f92c070c8ba0636a861c978e73f70a15` (4) |
| `nat_pointwise_bound_not_uniform` | Quot.sound, propext | `120836a7d452624c32d8b52e1fe08df75f6fdbab38dc25b6c8418cdba8a26b82` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `neg_answer_correct` | Classical.choice, Quot.sound, propext | `e6580ef73ad76c2e0d626b0cd0706ab955afcda6020a43693d61a57f135eb3b6` | `5b10fa5577155f4bb9db497d7704cb8a19052ec921adb63702a048536f27b1c7` (15) |
| `neg_answer_h_tight` | none | `0a0c94dfc3f49fa08526ea1ee6bc180b25d9d35078eb74dd613246b2394a227a` | `991df7e6db7fbd951594b588bd41dce9eb999eeda67c74f6beebb1e61cfe772d` (16) |
| `neg_answer_nonvacuous` | Quot.sound, propext | `a5539e0546c4b4438311a3547d6c2321a2b9264d6a7eea4e64302157cda6db2d` | `7791f574a62a6833a43ab18cf8d447487fc1639dc3e8f7b3fa637ad28744faeb` (13) |
| `negAnswer` | none | `4020dee730d0719514be8d859474e5b9893c3cfb82e9c5defa8d6d4781e92171` | `62f9234db4b05f6f62837850d92d4a329603e61df3e111193714d89e3544f357` (4) |
| `NegativeOverReading` | none | `baf7db29fdca0971664b6dab7f2750e81d25751fa036ef5f48f11c8ca8f878b6` | `436d98f026e8ac651cd55d785a36c6cf5be741b3a9ea13cc37b8cc2fce970323` (5) |
| `nonempty_domains_h2φ_tight` | Quot.sound, propext | `2fb4c297f1de35afacfdf9f5e2ee2ebb1b85719a2fbd21d7950222e827766b87` | `0d7587fa259e29211dc0c8e8719be85ec34f6bf23a0e323f657b213e7d61f750` (40) |
| `nonempty_domains_h2ψ_tight` | Quot.sound, propext | `15619040addf1647bb11c74b91039311bf9cd7ec5a6412bc535dabfd84f68bb4` | `0d7587fa259e29211dc0c8e8719be85ec34f6bf23a0e323f657b213e7d61f750` (40) |
| `nonempty_domains_hE_tight` | Quot.sound, propext | `9d7a2afa9cdd4095dcd6a774d55870e0bab806b8cb2bc6c6a4b29136870efeea` | `0d7587fa259e29211dc0c8e8719be85ec34f6bf23a0e323f657b213e7d61f750` (40) |
| `nonempty_domains_hpψ_tight` | Quot.sound, propext | `289697f48932085df6977ce14d4cb1d2da4dc6c6c28de008b5e8d831f16ced68` | `0d7587fa259e29211dc0c8e8719be85ec34f6bf23a0e323f657b213e7d61f750` (40) |
| `nonempty_domains_hα_tight` | propext | `bd754a4eec4f500ac7427354a193ba1e444097c41a770ff0b2dfce5a28d42520` | `51fe861b03aa0648e17ec5d8247c07f21af84c6f0dcb6639e70077c69f5a5602` (28) |
| `nonempty_domains_of_rEntails` | Classical.choice, Quot.sound, propext | `a72192d5475f2860ee79aeff97e2e56032b44ef36ce71f6f1af7b3d5b9ffa60f` | `de1d5a40073d04096f0582df33119ef30d156ceb47ef763a89ad35f04c428e0f` (23) |
| `not_undetermined_of_unique_model` | Classical.choice, Quot.sound, propext | `1c3a1b4127a284714567d117763add0ebc1bbe07fbe4a05969e3b8201669621e` | `ea1e4472c4c8fc01c5af949bac271729232c82a500e8813fa4cb146c89bf46fd` (5) |
| `not_undetermined_of_unique_model_hu_tight` | propext | `901083fe1d77566dbc311710a51fbe759e65a2b24b36b414f42b24b8c18d3d7c` | `ea1e4472c4c8fc01c5af949bac271729232c82a500e8813fa4cb146c89bf46fd` (5) |
| `not_undetermined_of_unique_model_nonvacuous` | propext | `f892dff3e0eb3920f3e69840a2d902b7fea202c08064ac209ba11a290dafbf16` | `3085518c4ce94c25d48751faf056dea021e770f45a4636af4d5ad1226cc3ebd6` (2) |
| `nvφ` | propext | `a82bac80f7b4bf8e0bd10c27791eab5c531e719730f48c638ac6b9f9787fb317` | `eafc6f019430c452c1efb12431469374529939f45a9f1a470c9dba19fca7e05f` (16) |
| `nvφD` | propext | `a82bac80f7b4bf8e0bd10c27791eab5c531e719730f48c638ac6b9f9787fb317` | `eafc6f019430c452c1efb12431469374529939f45a9f1a470c9dba19fca7e05f` (16) |
| `nvψ` | propext | `a82bac80f7b4bf8e0bd10c27791eab5c531e719730f48c638ac6b9f9787fb317` | `eafc6f019430c452c1efb12431469374529939f45a9f1a470c9dba19fca7e05f` (16) |
| `nvψD` | propext | `a82bac80f7b4bf8e0bd10c27791eab5c531e719730f48c638ac6b9f9787fb317` | `eafc6f019430c452c1efb12431469374529939f45a9f1a470c9dba19fca7e05f` (16) |
| `nvψTop` | propext | `a82bac80f7b4bf8e0bd10c27791eab5c531e719730f48c638ac6b9f9787fb317` | `eafc6f019430c452c1efb12431469374529939f45a9f1a470c9dba19fca7e05f` (16) |
| `or_answer_h_tight` | propext | `ba940d991e44048ed82d5ee27256e9c7a315a65b19e401ad98f019e5ab5ac239` | `40adfcb0d202455ae420bcc5f3f5e24ff3124cdd46a17da57b6900062e2daaf9` (17) |
| `or_answer_hE_tight` | propext | `5e15888125395584050bf95dbd179f68531d431e55b783b6af99ae51b2a0a533` | `28ada497772dee1cb8a14e10adbce3d2e31704de5df67ace6e32dc00d1f3fd2e` (16) |
| `or_answer_h₁_tight` | propext | `9117a1e2aa99c9040b4c7b66044d7afb05fb6dffd833f7c63a4e0b11cd2ea332` | `40adfcb0d202455ae420bcc5f3f5e24ff3124cdd46a17da57b6900062e2daaf9` (17) |
| `or_answer_h₂_tight` | propext | `5f20cbc1d7ad38e241ef792cba4e83cf9851dabb2c3794b4dd6473d24b037086` | `40adfcb0d202455ae420bcc5f3f5e24ff3124cdd46a17da57b6900062e2daaf9` (17) |
| `or_answer_mem_orTable_of_satisfiable` | propext | `c7c6f882a5f55a7441332f7110958d337c8774a48c3096e4f9ac836de3e30610` | `28ada497772dee1cb8a14e10adbce3d2e31704de5df67ace6e32dc00d1f3fd2e` (16) |
| `or_answer_nonvacuous` | propext | `8d79f32d28b52bba489c8b573619c315320563e0b758c8494acaa20c9ff4dd5d` | `9d764def0cafcf65abddf01a1c5bc5ab5cdf40bf38cf338bfb475fe80e10b8cc` (15) |
| `orTable` | none | `c6bc19812adce16874b056614a2366a7a74eaf820e366af163615f2483d8d3f0` | `62f9234db4b05f6f62837850d92d4a329603e61df3e111193714d89e3544f357` (4) |
| `orTable_realizable` | Quot.sound, propext | `808c79a40a5f490d0c20d2cab44cc8701d6e2914a2b4ec38bc24ac64583888a8` | `ed0332841180ec08c12b1da93ff579b493a2f94be2d0f8c87a71606dfc715fad` (16) |
| `orTable_undetermined_cell_distinct` | Quot.sound, propext | `e70a8bf560f409a075906c75a584a4995c2f5b2157e2d758fe492215ea97670b` | `d669e0c923af6bb8919d8167d6588da4a41a5d1eec5e07c23934d43880c2d5cb` (14) |
| `pairAllB` | propext | `0232e09c4dd0d8b3d99475e97235f7e3d151c0fa2413a98e0c2a6e5d5c22fa25` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `pointwise_bound_not_uniform` | Quot.sound, propext | `ae4c5628f5e7740d9d7795fd6170d609c6754207c6191749f34d390a097ac8fb` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `PositiveOverReading` | none | `baf7db29fdca0971664b6dab7f2750e81d25751fa036ef5f48f11c8ca8f878b6` | `436d98f026e8ac651cd55d785a36c6cf5be741b3a9ea13cc37b8cc2fce970323` (5) |
| `Precedes` | none | `06bbe5788953b66ac739247e9928fd56b3fc28fcb315be67c5592d4c42657f22` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `precL` | none | `18c22a7adec9894253656c8d37e52fdff9f893540324cf7aba20400a97693be6` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Prefix` | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `PrefixCrit` | none | `7a7c749fea9666b729fd6150a394d2e3709f5693b88f90ec1cb2bd9855ffb101` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `prefixCrit_necessary_h_tight` | Quot.sound, propext | `d3621215cfb9d1f29512da2e47dfce58a34aece5a4d9591dd268f1d49afc10ae` | `50cb2cbf37350ace410abbf72201ddf161d2e04940a8b0424274ee802e5e161d` (33) |
| `prefixCrit_necessary_hα_tight` | Quot.sound, propext | `4ae97d61fc3f70d96a734e46da7803510f8ffcf46814fafe673f96d859cbee2a` | `50cb2cbf37350ace410abbf72201ddf161d2e04940a8b0424274ee802e5e161d` (33) |
| `prefixCrit_necessary_hφ_tight` | Quot.sound, propext | `690b37b38c2bd76c02b8fe9bb1b30352e027f08e279b395bfe4bf0a3433ad8f2` | `50cb2cbf37350ace410abbf72201ddf161d2e04940a8b0424274ee802e5e161d` (33) |
| `prefixCrit_necessary_hψ_tight` | Quot.sound, propext | `c08a9700e6e5c9744864b2479f735c5432d17299f72a87ef31a6b2efe6c20e5f` | `50cb2cbf37350ace410abbf72201ddf161d2e04940a8b0424274ee802e5e161d` (33) |
| `prefixCrit_necessary_nonvacuous` | Quot.sound, propext | `665b157354f5ecd15c18ea518d368376279f18411807c03f3ecba202ea6a086f` | `9ca5e25f3cd41556bcdb4ab7dee465bf166d4761a1cd2019404ea749ded7950f` (22) |
| `prefixCrit_necessary_of_two_point_nodup` | Classical.choice, Quot.sound, propext | `46d619a93797fe0157e26b3dad2bad10d8c261f0415c010cc049dea15fb90fb3` | `4a36b3cb7e2f6de1b2a136a56257b177501cc23c4e68757d925f6ad1b64a3cca` (31) |
| `prefixCrit_part_i_tight` | Quot.sound, propext | `b306c4411e9259fa323fa1ab0f5b0f3f0979d38663c39c14c135a95a74d83a47` | `ed5ba6f5baed0e24ad34e6ed8fcbc3db8b0184e52ef896163ef327ef73771c64` (33) |
| `prefixCrit_part_ii_tight` | Quot.sound, propext | `8ea78c8e934892ed8190aa22fce6d118aaccc7f4f20a1831c444de149e84d00e` | `ed5ba6f5baed0e24ad34e6ed8fcbc3db8b0184e52ef896163ef327ef73771c64` (33) |
| `prefixCrit_sound_hφ_tight` | Quot.sound, propext | `6814b449f8ed71de232f67a7c41c0d82e7dafad5a290693914aea493e494bb08` | `f5be357287f7b66c8f69af54799990b721c78859bac6db26af673d8a0a0bc279` (34) |
| `prefixCrit_sound_hψ_tight_dup` | Quot.sound, propext | `0f8b1dc89ce2b6156dffaf49e7dba6bfcd1b9bf0c29449c5d2c8af486bd955c9` | `f5be357287f7b66c8f69af54799990b721c78859bac6db26af673d8a0a0bc279` (34) |
| `prefixCrit_sound_hψ_tight_missing` | Quot.sound, propext | `a726db0519428782dd5491f881033253d24275f122803c3d03829bb59eb1c150` | `fd58706fd9ac06bc06184422d2a9ca38e0fcc342ea9ead3c39541558be74c21f` (33) |
| `prefixCrit_sound_nonvacuous` | Quot.sound, propext | `e33b72f7e93eea8625961ba838a3432cbe5f0990d7943beadb35b38526e4eb64` | `d2940a61ed9eab40ce59b91bd4cda223e0de81d1cb55c6170af965e58f78c35c` (33) |
| `prefixCrit_sound_of_nodup_wf` | Classical.choice, Quot.sound, propext | `b995340ac7e8f61b9aceee245a54cd9ec19b66858358c2a9980d760383f00401` | `300d2fef2171b2c12a7709d4cad6b37eb29a8975ed38683c49f3ec34bdf42065` (32) |
| `prefixCritB` | none | `debb3970953a844e6f94b3af1a3f8c447811f4d29be9c466f4d5b0f870654bee` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `prefixCritB_exists_forall` | propext | `cb8ca654e7e0683838c8e367d50c0063f5d7800c0f67a1b6d3b51433dfe1e692` | `7ec0944bccbe07f92a8f107eafe48c18adac2e6b9fa326d15638fc79ea3792b0` (24) |
| `prefixCritB_exists_forall_forall_exists` | propext | `03690c4b319efec83fc814dc0e94b0db4d7ea7e1f353617790289845760a6fc3` | `7ec0944bccbe07f92a8f107eafe48c18adac2e6b9fa326d15638fc79ea3792b0` (24) |
| `prefixCritB_forall_exists` | propext | `2d24f16edb43b1753cd97610a59445534e19bd45bdea4df18dc7f51592a4d1f7` | `7ec0944bccbe07f92a8f107eafe48c18adac2e6b9fa326d15638fc79ea3792b0` (24) |
| `prefixCritB_forall_exists_exists_forall` | propext | `e08d2e99966aeb0b7633e49751ae29293dd66f5de50ae0804409f2018ce42c78` | `7ec0944bccbe07f92a8f107eafe48c18adac2e6b9fa326d15638fc79ea3792b0` (24) |
| `prefixCritB_iff` | Quot.sound, propext | `11d3ca1c27dfac04d8959c51ba55aa1c15c8147ade726e9d85a6d146997007d6` | `adc3da05a345b179eb9d13d309ee55b378e7e09f8d5ca0527cde771150c0d029` (26) |
| `prefixCritB_renamed_false` | propext | `39ce6e1dc34021bae94a9771a520cf23bd67a081b7b7d6fa9c2f8ca4719f9030` | `7ec0944bccbe07f92a8f107eafe48c18adac2e6b9fa326d15638fc79ea3792b0` (24) |
| `Prem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `premImpl` | propext | `1744d673e3e8fb183df594df614889fa249e49c87cb031c5adbd9cc6df1cf5af` | `02080271805b9836dcbec5b06595e51637a9a10c8faaa46c5849b6807fa09b2c` (4) |
| `premise_entails_iff` | none | `4be8a8f12e12243e7fc959e217d67c383d55ff21b788107adc56a0d2168067e9` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `PremiseContravariant` | none | `b083ab51290d1698fc29c0082e690555467cac23349d6fe0d15a0f2bdc68e562` | `b748b8aca9d7960c4adf24a7e8920cfc186b456a5d061a76d5ace9f4f1d68c2a` (7) |
| `premJ` | none | `deeebac54e7e74f97072cdc415f5a1b6497f1c7db9ec5c67db5227ac4f1d1c6f` | `02080271805b9836dcbec5b06595e51637a9a10c8faaa46c5849b6807fa09b2c` (4) |
| `qOf` | none | `892d57ad7c78c3c0ba555ba70815ae1ec7d70e10f1f0f65bb39367db777d6282` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `qStrong` | none | `1450015f4d87e74e5d5ecc75b963bb018c9a51c5ae33dab92f753250a328a211` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `qTriv` | none | `1450015f4d87e74e5d5ecc75b963bb018c9a51c5ae33dab92f753250a328a211` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `Quant` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `quantify` | none | `d395dd03481ebfe8b0a8ae4129e43dafed6e46af54c126e0c51798e7667b151b` | `917dce36ee6ee267da5972f9329d969aa5954e297b94c1ceb4334ef9a220ac71` (3) |
| `qWeak` | none | `1450015f4d87e74e5d5ecc75b963bb018c9a51c5ae33dab92f753250a328a211` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `range_entails_single` | none | `2bd229f8fd1a9015178e937e90dd64cec869420dbf6b43b291d1a5a9c9cbffef` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `range_entails_single_nonvacuous` | none | `a598b24f42b7e23d77095f79fd395f181d500d70fc6bd8cd83821e15a394b1ba` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `RCrit` | none | `625b19152ef3d97739f03a58d8453f3ca1b578bb9fafefaed2fed9fb883de752` | `b748b8aca9d7960c4adf24a7e8920cfc186b456a5d061a76d5ace9f4f1d68c2a` (7) |
| `rcrit_complete_hE_tight` | Quot.sound, propext | `0bf39c9678068f82f7ece5055a483ed798adc0813147c0c75af7e1f97c54de6b` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_complete_hα_tight` | Quot.sound, propext | `2579f81234e0df1dacca223e3699263de1214ed629ce7761876fbab196cd02af` | `4f5897c505a8019ce2a7ddc15d03c778ca0563e81c7833e0bb52e059618224c9` (48) |
| `rcrit_complete_nonvacuous` | Quot.sound, propext | `44c68cbc3ec5d06bb28bbf1f53e3505b388eb0ecbb10af3a1c5d1e248aa498fe` | `728a42057ae4a42d4a2974f2ae718eb4fc6cfce08abadfa5c157b0497d8246eb` (62) |
| `rcrit_complete_nonvacuous_free_variable` | Quot.sound, propext | `514fd2c30e928a941c63a4dcee566b796a72d882e79514fca3d9bef604ff0946` | `1ba0f90f99df99196710036604388986a5c4a2d96bb6361dd4f534fde7b1d8e6` (76) |
| `rcrit_complete_of_nonempty_domains` | Classical.choice, Quot.sound, propext | `1dcb6058d400407cdf6773fe76bfe729dd7d65e64ed12f4105a89925bad67e60` | `6e4666ca04357901b06d25410ff93dabc00a2b588a7fcb914c58a5cc7a822ab2` (43) |
| `rcrit_complete_polarized_two_point_premise_free` | Classical.choice, Quot.sound, propext | `b1033702b0a6363cb7f0957de9e3168134a2d3d60aa900713c10828d6acb567d` | `6e4666ca04357901b06d25410ff93dabc00a2b588a7fcb914c58a5cc7a822ab2` (43) |
| `rcrit_complete_two_point_premise_free` | Classical.choice, Quot.sound, propext | `667257cdb86ab7c8ca75853d22e80af3ca71d909887b0520a3a2d01521b94458` | `6e4666ca04357901b06d25410ff93dabc00a2b588a7fcb914c58a5cc7a822ab2` (43) |
| `rcrit_ex_domain_tight` | Quot.sound, propext | `4d3f4163fcf4334a8a20c76b2073f99dfe5949e4602807ebb7c7688486e426dd` | `b99e3a9e5bc68d21f5509490d03686c9fc6da5e700d411844fa37a434be08312` (74) |
| `rcrit_incomplete_empty_domain` | Quot.sound, propext | `70c2d8c04cf064f9277338fcc695660ebed84565768ef494ca06f066a6cec8e3` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_empty_universal_domain` | Quot.sound, propext | `f5b7ea322b9245a89c51b3f7bbb0cf4b91b51c7502739381526b4152336ee7e2` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_false_target_premise` | Quot.sound, propext | `3752d26642004614a8fab360a85c2bc4f5ffed3ea95019c0b9d8e7eb0f80732a` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_in_normal_form` | Quot.sound, propext | `0e8b46b2c5669f9855b7ab2c44183af110f51209c81ce85e5f4a7552e6690303` | `fd6dd74577ff656bca6192b6024325e2e5ad007779de58602e80e7447bc88df3` (73) |
| `rcrit_incomplete_inexact_impl` | Quot.sound, propext | `32aba4483d9c8f67b06aa5fd4dfa3c202867bfee4e3c88fca8d00564e318e9a1` | `a3a773194d16366ec4e7a124b8c964d8b62cacaace1e55795f78ea18861d2772` (70) |
| `rcrit_incomplete_inexact_incl` | Quot.sound, propext | `4031c1aeccd496a2937361af451f61b1ac3c6b4d42ad8a9ab4bbec9495e4dd59` | `d635a16c9581c2f1c2817e9e24b6ecb76db38c960a47e98d55eb73d4661a873a` (74) |
| `rcrit_incomplete_inexact_meets` | Quot.sound, propext | `f7fe063869d5c8faf871402b7b410ff28042831898d5b347dce93ac8475bd84c` | `c77e4ace33122a5e353761646e27f855e57f4559ada0dd78e956f413a5e327f2` (73) |
| `rcrit_incomplete_not_wf` | Quot.sound, propext | `c2207a80538abbf39c5465d042e7dd827563b8a5c34f521fd9087a8f4513a796` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_not_wf_target` | Quot.sound, propext | `5575c968406174c6eb4b1444f2d38f73252736f605797ad6645dba584a79fa7d` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_premise_as_domain` | Quot.sound, propext | `d634dcefb106fab44b0f765b2b22516edaf860bb27a1dd77535faf35bfe8d7c1` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_redundant_existential_premise` | Quot.sound, propext | `afbd22821edcd4ae3ce28ebe1594d00a6b97f05f495c51364e4acb468cb42cb9` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_singleton_domain` | Quot.sound, propext | `b7bfbacefcbac9edcfdb149c7ce0ceb00235f373dbe0f494d7e49d2a4aa46169` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_singleton_existential` | Quot.sound, propext | `9f693cd3091a321e9e07527036bb53c66ffeea73f68a06a72e8cb9f2e3cbea56` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_singleton_universal` | Quot.sound, propext | `b406b37db4cc90e332b6767055d0b14f380cb00d05555fd52b15a1c3e3386a52` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_target_premise_as_domain` | Quot.sound, propext | `6b588386a3ee98e4bd66277aca48730216892071a8cbdead30b0c3fc9878c9f7` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_incomplete_target_premise_on_existential` | Quot.sound, propext | `67949906e56fba91b6e56eb3c6dc4dfad088c718ce0e6b42812cfaec6f7b1b79` | `015915400869bb451b0cdf8cad4d5cf30e73c48a773d5ec9b30a5e2dc0c0e343` (75) |
| `rcrit_meet_tight` | Quot.sound, propext | `c2e50e0f22168ef43c19fe0631d9acd9b01ab25319240145d3d36cdbbdf3c9bb` | `b99e3a9e5bc68d21f5509490d03686c9fc6da5e700d411844fa37a434be08312` (74) |
| `rcrit_part_i_tight` | Quot.sound, propext | `05736ad0966e570d8ccfa89a6fcaa8f05a5150a275c423f82e1777c6af685f08` | `3e447bd63fe92a65aae6b08e2c3ef28d0b887ee9afb83fc642db84649999e19a` (73) |
| `rcrit_part_ii_tight` | Classical.choice, Quot.sound, propext | `bdeca81c9331ff3b0abf9f82e2608e7be17002d74e0405718ddfa5c4c039f471` | `3e447bd63fe92a65aae6b08e2c3ef28d0b887ee9afb83fc642db84649999e19a` (73) |
| `rcrit_premise_tight` | Quot.sound, propext | `bb2193e1a049f1310294a51b92cd38c678df98f566a2b87e316fa0c36b1461e5` | `b99e3a9e5bc68d21f5509490d03686c9fc6da5e700d411844fa37a434be08312` (74) |
| `rcrit_sound` | Quot.sound, propext | `5fba7c773217bcbe1aa8468514402e9a04ea0a0ab7565b1b99d95f8fc7b7fd7e` | `3db6696f7801e09d4d3c3bf858ce594db8ed0720724fe7c0369f76781df0cf2f` (43) |
| `rcrit_sound_hI_tight` | Quot.sound, propext | `914cdc6c79042d375c9c7e80c76deea3c375aaa61d3d50b3be624afc505e8617` | `9dc3a23c4315f2dad6791d48f10861b6500ea9ec8bec46e4551ee6fcc56472eb` (70) |
| `rcrit_sound_hJ_tight` | Quot.sound, propext | `3e3345acaea7f910811a41da7fda54c22fc0f2388ea412ab7811b28a721145be` | `b206f51ab05eb50ae09c91f3d42121f21956a1636b261aa8dec149d480497fd2` (69) |
| `rcrit_sound_hM_tight` | Quot.sound, propext | `8e4243ab9c67b164935af688bee863ec6e8e743e30b942ae65b252d65564b577` | `a06645121a4d2e1f12ebfb1ca79d1703c95334d24e956390575721572048e9a4` (72) |
| `rcrit_sound_hφ_tight` | Quot.sound, propext | `b9ea458825be1f64dfb318d933fd6375349b334c506dea8daf76a48a8a15e206` | `67b78d5503b192ba751fef473658b8848d60bc1771415f1684c753ae0ccc9fb2` (75) |
| `rcrit_sound_hφ_tight_missing` | Quot.sound, propext | `c98c3933ca7ef6e925f5a565cae9cb82bfc9530b7670a7ff321a36c7f348986f` | `67b78d5503b192ba751fef473658b8848d60bc1771415f1684c753ae0ccc9fb2` (75) |
| `rcrit_sound_hψ_tight` | Quot.sound, propext | `736e156cc078f109358a16afcfb63bc6b9b132be5b500abf55a5e9603c3f5c70` | `67b78d5503b192ba751fef473658b8848d60bc1771415f1684c753ae0ccc9fb2` (75) |
| `rcrit_sound_hψ_tight_missing` | Quot.sound, propext | `74b50c082630ff20c9185b065d63b8534062a0581447ee4eb09171ac183349b2` | `67b78d5503b192ba751fef473658b8848d60bc1771415f1684c753ae0ccc9fb2` (75) |
| `rcrit_sound_nonvacuous` | Quot.sound, propext | `96b86afb767e9b4c5211f3ee0b2583dceb1a93e76d254e46660635f804ed92d4` | `9ffe38d54471aa71879935c367f0cca86fad27a9375c240268549741e0bbc98e` (77) |
| `rcrit_sound_nonvacuous_domains` | Quot.sound, propext | `c6fae4eceaefc8936fd74a3595bb093ab9d81f5a41a9bda85005c46e539f377e` | `11189effdd67503af1962d2ee1608f519d3ae0f788ed4fc9e50bfdcfe53e46c5` (77) |
| `rcrit_univ_domain_tight` | Quot.sound, propext | `2c7bc46abfe495899e8e55210ca9b8486e8781c7af5e2939c04b33f138212c3c` | `b99e3a9e5bc68d21f5509490d03686c9fc6da5e700d411844fa37a434be08312` (74) |
| `rcritB` | propext | `5e727f06c9a37a1f8ac0daf5d97d9facb4820351accf60f0d7bbdab2e8282a42` | `b748b8aca9d7960c4adf24a7e8920cfc186b456a5d061a76d5ace9f4f1d68c2a` (7) |
| `rcritB_iff` | Quot.sound, propext | `51a6171d97a3b038b94a1ba71fde6f481d8ef31c5d311d145d90c35793fa318f` | `81ce0b711bccb9d9954c0ae391b5a23b15e8ba332880be603903c7c9522239ce` (40) |
| `relative_entails_absolute_iff` | Quot.sound, propext | `a19fe8feb1b4636bc5b68667535b89dde6a72316a9ef6e82a8f55e1706530bbd` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `relative_not_absolute` | none | `6d232377a20b313f0e0d5607be92ef9f02311e65c68759315a7f24c533e0535a` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `relative_not_absolute_witness` | propext | `9a53a7dbab3f55655b9beb3a8ffb9864270a4bdf929c7361e84fd4633aed64ea` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `relative_to_assumption_not_absolute` | none | `7fe60bc2c7fefe8a16ce57372b43a36a95568483fc2ea2451f735c9af67192fb` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `relative_to_assumption_not_absolute_witness` | none | `0ad68606feaa7bea65aee58ef4bd4b19623d1bd0d4a243128c5308b304bcaa12` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `REntails` | none | `c7ee10199277c6872375d91fa91a4832feed237800a99fc961bf47de55c66eef` | `b748b8aca9d7960c4adf24a7e8920cfc186b456a5d061a76d5ace9f4f1d68c2a` (7) |
| `rEntails_of_isEmpty` | propext | `802c61f06654602258b2a234af67656c1cc8619b26d799422aa95ed98fc29ab2` | `44375d1807466191385e4e202cdbe7551185187cc55b01aa3999f9752a7247ca` (22) |
| `rEntails_of_isEmpty_tight` | Quot.sound, propext | `4452907113cdaf0b2a9f80f198ae10e9a88d9db741a5004b0a9e303c08642d39` | `c305f0f171890a8b11d95e7633ad24f7e87b907bebc81507a7deb2b95038777d` (39) |
| `Satisfiable` | none | `136dc6e2f983779699fc868db28d7c60df8a50d58ae96824d5cf037f7a94a52b` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `SEntails` | none | `77f904d702bc2f2d18688e45131b49d885d4fa39d1b65f1204f44b660ad15f5a` | `ff123798b8ab9eb4cb64b51016d4ae17ce5493549a9bcc11c688331588011920` (6) |
| `sentails_iff_hφ_tight` | Quot.sound, propext | `3d34b753aa8d9150abcf3ed7e061d3137962050aea8ab222c6de6bc3ea6d1a70` | `25c6c6143ced97fa62bcb03071239b232dd14ff378cd7fb726b0c0addf899635` (35) |
| `sentails_iff_hψ_tight_dup` | Quot.sound, propext | `a732fc1f7b71fadc97e10a087022d0cadf3274a7616a4edaa0fb5041eb0da91c` | `25c6c6143ced97fa62bcb03071239b232dd14ff378cd7fb726b0c0addf899635` (35) |
| `sentails_iff_hψ_tight_missing` | Quot.sound, propext | `4898b1c7a0e7bb2f6f81e49e9a6129ce93df9d94ec887cdd6c5cccf9626fb9be` | `541826cd9f4529be4fa30c139399229f56a7af5a56e3c2a35139629ee7cf4db8` (34) |
| `sentails_iff_nonvacuous` | Quot.sound, propext | `3bc35f51b854d634c1b0dd2cbda7d407bb51c8f7d810b72e6a15304e30e4b1c3` | `25c6c6143ced97fa62bcb03071239b232dd14ff378cd7fb726b0c0addf899635` (35) |
| `sentails_iff_prefixCrit_of_nodup_wf` | Classical.choice, Quot.sound, propext | `884a186f0c6caec04644ea82778219c192aacdad6bba599b6d580331692177c7` | `e72b2741556dc126d4fd4e81a79b84f7a9493323f352e64d57f8f2d0ffa9aa12` (33) |
| `sentails_iff_twoPoint_types` | Classical.choice, Quot.sound, propext | `477bbb6f7c5fc231c1969fd70368bdb409847d2054dd9a11c079b76a2c2ada86` | `396716eaf6d37723e47b1363567b7b73e859667ba33503cd6d9d48ccec0421a5` (20) |
| `SEntailsAt` | none | `ec31afeb0288cb7dcb7bcc5fcf75c4b540db82842fd454c1f0eb5166eb8c2f03` | `ff123798b8ab9eb4cb64b51016d4ae17ce5493549a9bcc11c688331588011920` (6) |
| `sentailsAt_iff_fixed_env_of_covers` | Quot.sound, propext | `737a01a49d6faab44b63b8774c761f978bf1cf42cf4c958d54328a14e0d15cb3` | `9cfac053d6de9d010a5b9683f5e8dbba7c6d9687d92ae4870c713de02f495d29` (20) |
| `sentailsAt_iff_hα_tight` | Quot.sound, propext | `3ff54e7a11183a267f8676678c59e974b846b8c6019eb15b5cd3f14fb0d504e5` | `cf424bb373683bc67eb7ff18467d7233ba1cdaae3a4055a6f6b99abba5c31e28` (39) |
| `sentailsAt_iff_hφ_tight` | Quot.sound, propext | `8e92a579a2f729d9a5ed1402682412e59d2825cff5878b37922a7e2c089aeb52` | `cf424bb373683bc67eb7ff18467d7233ba1cdaae3a4055a6f6b99abba5c31e28` (39) |
| `sentailsAt_iff_hψ_tight_dup` | Quot.sound, propext | `4181937ee0f8116bca6ea154a4f7374c3e2cb7a9ed4b94c82f944d7dbd99e31c` | `cf424bb373683bc67eb7ff18467d7233ba1cdaae3a4055a6f6b99abba5c31e28` (39) |
| `sentailsAt_iff_hψ_tight_missing` | Quot.sound, propext | `a97e0cb5f86f8f344fa88ef541bbacbb0cda7b7647039d3b906a90089cf127b7` | `71e2894be5e0fd2868f1a5ca52cb22d3bcab13064fc3a49140974a1c0293d2e2` (38) |
| `sentailsAt_iff_nonvacuous` | Quot.sound, propext | `23e38573bc310b22e1ab961d95dc623cd35ac19043688b35d2a8ca5a3654c14e` | `f5be357287f7b66c8f69af54799990b721c78859bac6db26af673d8a0a0bc279` (34) |
| `sentailsAt_iff_prefixCrit_of_two_point_nodup_wf` | Classical.choice, Quot.sound, propext | `8475aa40202ade62898f664e8a28f90a2e533c14ca17616983309f1225541c04` | `300d2fef2171b2c12a7709d4cad6b37eb29a8975ed38683c49f3ec34bdf42065` (32) |
| `sentailsAt_iff_prefixCritB_of_two_point_nodup_wf` | Classical.choice, Quot.sound, propext | `663ca6ce8ef2ec76e2a775d70286ba732bd34ff92cc1e0f8f6a09db5c9951a08` | `3b4745d09a2d067ff59a351547f27e6a5e7fd5004e8a337563cbf11d4523ef47` (33) |
| `sentailsAt_of_isEmpty` | propext | `d32ea12bb4c00578092775692060e6c123e49b15b5b89f02abbca667cd9773f4` | `c04782cf870e43f0d3258137f286c4cc9eca2d15e3bbbcf7b7918bb8e9ba8e8a` (19) |
| `sentailsAt_of_isEmpty_nonvacuous` | none | `f9d4c8c1346f09e2ce92c28de50f3ff39464823f95cbce5c135649712a204b34` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sentailsAt_of_isEmpty_tight` | propext | `64ea42a4b31a36f0da32aee27bcee38379a9d0f79d95ec7ab5270a718855a131` | `9857351d10ed78c77fc34cb09a44d2101a4fd710dc41c49146afe421505fe726` (21) |
| `sentailsAt_of_subsingleton` | Quot.sound, propext | `c94a77fed1ef500517dc18ed719dc67a2aa32c16a115e17ece85d31115fcea5b` | `c04782cf870e43f0d3258137f286c4cc9eca2d15e3bbbcf7b7918bb8e9ba8e8a` (19) |
| `sentailsAt_of_subsingleton_tight` | propext | `45de681b7e57e685fa69114272e8fbdfa962d24a0e3c71f0e612a25534803a29` | `9857351d10ed78c77fc34cb09a44d2101a4fd710dc41c49146afe421505fe726` (21) |
| `Shape` | none | `61be59090710d4a135a3640220d25bc63ba3c7c379c005ae1a928fad6d9b9cc8` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ShapeNF` | none | `44dcc51509a2c609db578d7fff74b6d7c684fcc2c501e312959b9e2d90d48ce7` | `b748b8aca9d7960c4adf24a7e8920cfc186b456a5d061a76d5ace9f4f1d68c2a` (7) |
| `single_counterexample_not_universal` | none | `290564d677171e67b69c2fcbb05d3e4a074e62cc9ef760fa3d1d32bc5ddd0af6` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `single_counterexample_not_universal_witness` | propext | `1e30c4804c87b4628e8bcae6836438cbb1e58f5840a31d1b2736f1cacfebe95d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `single_parameter_not_range` | none | `101c613db6e32182a808a4a8e682ae966a3ee5f29010ee2d519647eecd3047dc` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `single_parameter_not_range_witness` | propext | `189566f9347cc1f6db6fce7ad3f90afbd70f041030f25b4cb9c2f48f4cf3c40b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `SkolemOrderPreserved` | none | `7a7c749fea9666b729fd6150a394d2e3709f5693b88f90ec1cb2bd9855ffb101` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `subsingleton_nonvacuous` | Quot.sound, propext | `56a73a11a39bdfcc654fd9a65d2aaf0ade5b5ed1183b52e19ca99c5c3dd2b465` | `9857351d10ed78c77fc34cb09a44d2101a4fd710dc41c49146afe421505fe726` (21) |
| `sufficient_not_characterization` | none | `e562c552cee639e77ab921bbacd704da5f9789cb78b5c33c95bfb346a483a447` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `sufficient_not_characterization_witness` | none | `0fff70555b9af531a6a0e420916df36765dc9268aa0ce6e5d25de832aeeb779b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sufficient_not_converse` | none | `0b4f9cab218375a1a0400ab1438bf9de326e872c1a22790c7b3254dd7f687e10` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `sufficient_not_converse_witness` | none | `0dc9fde58c787d8d5030fabea94c537c8ee7c72fffd910fd81c8fd479ff6b96e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Supported` | none | `12c6fcea22bf37ac03ba6bf6639b66890ff6618c980f741522760537d735bde7` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `supported_mono` | none | `a7cb5732bdfc59c340af5781c095e3afe17979361a3edad3f34a426ce6f6ba4f` | `3a4056bb4132181169c15ec788e95df76278cb0fb765bbd174affcdcb241c71d` (3) |
| `supported_mono_h_tight` | Quot.sound, propext | `6b32b104c43c14b0e7a8293ce410b744d860fd71cdbb20e645c86a0eb92d6267` | `3a4056bb4132181169c15ec788e95df76278cb0fb765bbd174affcdcb241c71d` (3) |
| `supported_mono_hsub_tight` | Quot.sound, propext | `04a1030d865a6774a65183b00c708da14229a9d4b3c0cb5bdfb0be47c9c0d419` | `3a4056bb4132181169c15ec788e95df76278cb0fb765bbd174affcdcb241c71d` (3) |
| `TwoPoint` | none | `d81c4e60534bc373fecb0291097d869a4ba2c6bebafc3750f1da7ae8c6815e49` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `UnderReading` | none | `baf7db29fdca0971664b6dab7f2750e81d25751fa036ef5f48f11c8ca8f878b6` | `436d98f026e8ac651cd55d785a36c6cf5be741b3a9ea13cc37b8cc2fce970323` (5) |
| `Undetermined` | none | `12c6fcea22bf37ac03ba6bf6639b66890ff6618c980f741522760537d735bde7` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `undetermined_example_pos` | Quot.sound, propext | `7f946a431a33279558d798f79da7b0ea254a1bdb01341400a67ba49c69f1db43` | `ea1e4472c4c8fc01c5af949bac271729232c82a500e8813fa4cb146c89bf46fd` (5) |
| `undetermined_iff_exists_both` | Classical.choice, Quot.sound, propext | `96ebe91372142f54ddc8de08ae062a3c61490307b5bb92d82e8c3bf20b72d959` | `ea1e4472c4c8fc01c5af949bac271729232c82a500e8813fa4cb146c89bf46fd` (5) |
| `undetermined_not_upward_closed` | Quot.sound, propext | `d13504ecada09c265de8fed987b8d79a3199ed6f172820e066f08965ebc86265` | `76733e9725311586f866e1d1fe3c7bc27bfa53d13638b63b1fb58d7461ab287f` (6) |
| `uniform_entails_pointwise` | none | `6540e306cf95a3532e092b59c07d0144790d669645bdeba87b80042384a20016` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `uniform_entails_pointwise_nonvacuous` | none | `0a564e8ba9920cb628b9a6a2be808e69868c8291a945c26d80803788d0b00109` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `UnivDomainsContravariant` | none | `99d5ee5e8264b304a4d5c548044c8ec381ded1f0fae15dbba25feadca9b9fd71` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `universal_refutation_entails_single_of_nonempty` | none | `97cd821424e08065e7054c7297af2ff95cb5d72a67f04202b059cb00d542bb4f` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `universal_refutation_nonempty_tight` | none | `77b3abadfec6037092a04f019f70ac35db6bf45ccd74d994642ad681b784e370` | `cd9532577c46c0bbeeddbe056619d50d244bd87e23b4e301cdc251a9ef96d29e` (2) |
| `universal_refutation_nonvacuous` | none | `7ef55bcc2423b0e4a4d8646379c1ae110dfb5f25826685319ec72c11fe714aa3` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `universal_undetermined_until_counterexample` | propext | `a6ac314ac0efa46e1a818c65c9898a0a73084aa19653459ec9dbb15de4f6afb0` | `ea1e4472c4c8fc01c5af949bac271729232c82a500e8813fa4cb146c89bf46fd` (5) |
| `UnivReflected` | none | `7a7c749fea9666b729fd6150a394d2e3709f5693b88f90ec1cb2bd9855ffb101` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `unsatisfiable_hE_tight` | none | `9959c592559dfd5ed42824ea2dca228cf6652c7d1a16b5187ec92d01b10b0440` | `306266fe3560bb6b0b49c19bf964b6b7a29b9e2c2250f006306ac4df70753a2e` (5) |
| `unsatisfiable_nonvacuous` | propext | `7fd7a0bed3ae668cdc45754ad3082cd3d97c77c3cbcecefa9a2a7183eba642c5` | `4f42e09ef3985ce23210d3fcade8c02a9a72152471e1591871fca8f4f7959456` (3) |
| `unsatisfiable_supported_and_contradicted` | none | `f1b222ef6b3da374c4649a96067a19933d8460169f896bb4ca2813dcc917cae4` | `306266fe3560bb6b0b49c19bf964b6b7a29b9e2c2250f006306ac4df70753a2e` (5) |
| `unsupported_not_imply_contradicted` | propext | `8878d1c9cf5424bcced480858a4ef7a67bd8081f3547ee1ebad3cbd7a30607fd` | `b1fa6e5978acc19da6e6b1a3035e7f41f92c070c8ba0636a861c978e73f70a15` (4) |
| `unsupported_not_imply_contradicted_witness` | propext | `ff0b96bd083fb20ab0e5608e110275581e9680784070b5419ef3947ad6e53c13` | `b1fa6e5978acc19da6e6b1a3035e7f41f92c070c8ba0636a861c978e73f70a15` (4) |
| `unsupported_of_contradicted_hc_tight` | none | `d9f5bcdc68549b181cbe3991633da74ee188fd00454ab788e619bce066fe6f8a` | `306266fe3560bb6b0b49c19bf964b6b7a29b9e2c2250f006306ac4df70753a2e` (5) |
| `unsupported_of_contradicted_hE_tight` | propext | `35fe2f31c775aa31d6984c688d1f36cd74d4f3f909380bcddf4ced6e0c6a1ae2` | `306266fe3560bb6b0b49c19bf964b6b7a29b9e2c2250f006306ac4df70753a2e` (5) |
| `unsupported_of_contradicted_nonvacuous` | Quot.sound, propext | `36f37d914184e6b23bcd7ea93983d5e207bc91006fce2e98b889201defe1422d` | `08c5cc1bf680b83f1be3c6b2c8ae5e553b465f441eef0e2bb5ba5fbd9dda30d5` (4) |
| `unsupported_of_contradicted_of_satisfiable` | none | `a55c86deffaeb19ecac8f3ab0afde68a6f4139d1ccc13bba62a65fa762878354` | `306266fe3560bb6b0b49c19bf964b6b7a29b9e2c2250f006306ac4df70753a2e` (5) |
| `unsupported_of_entails` | none | `89135e3fd430af04f2be0739fb7e8627e734d55249c59e6d12ec5d3e6eb4f82e` | `d8bad440f0f02cfc4511a289cd00a4bc45a6f3c6de0a3f5e748e3342e99dcfa8` (4) |
| `unsupported_of_entails_h'_tight` | propext | `228be69600d5cccc8bfb3cd498f54519a55639507159540bdcba95ed3c7293a2` | `56dcf6b95c635ee81744ed2e54f9fdb79079fa92d2608b66d96891a794a59331` (6) |
| `unsupported_of_entails_h_tight` | none | `1bd9d9339890a0b3517c17d2d7be82ba6650756edd703f9ff3f73bb9bbd4417a` | `b6c98df4dcfe04dad5cf45ebbb0cdeb2bbec586e1fb7a33f3294055ab7fb105f` (5) |
| `unsupported_of_entails_nonvacuous` | Quot.sound, propext | `5eb25352b2dbe07f76996ddd0b54fbc30f64b3fd05c5481a4aa87cb72466a43d` | `5816bd6a4bf2d671d1a3c234782bdf4ec3b2892c6e84aafb0f5e94719f73c8d0` (6) |
| `upd` | none | `98a8635c3280020db56030312f877ae99772c16fd2345b50d6d37f389f675bd2` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `WF` | none | `f013e15721555ff360aabf12e0530ef588884d48e422f4265bd7e0123b817d87` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `wfB` | propext | `936d993f3a2222bcd97ce95ebb4f584f0e3f0b8472b9c33a1c2c524b7051f20b` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `wfB_iff` | Quot.sound, propext | `bb615965b6cbd206791e2100359647cd00b3550e4f482352310dbf29286e3db5` | `36f67064ee9411730f6e951d1376f0bb1950889b4855a4b6a9695f76acc1fc75` (10) |
| `WorldIndependent` | none | `5a78119c17823d4dd9699d17d8ca0a6986b317a9805f378bd3f9f8b786e1689a` | `bf116168e41a6f83f8ec03604cae7ba4bf639c0ad034c94dc19181033857c6da` (1) |
| `worldIndependent_not_undetermined` | Classical.choice, Quot.sound, propext | `8c0f461491e79a71ca1d1ed12f1067ffb5b729b654cc96d2059f9e0a8767187d` | `7421dddf0aabb1e97d8fc99ba56bda41a9be5b6ce3b955e5e7ca9732714dd055` (6) |
| `worldIndependent_tight` | propext | `dcf7b792b7319f840ab649e9c70c567017e1ad997359ad8a953389b00b7e155a` | `7421dddf0aabb1e97d8fc99ba56bda41a9be5b6ce3b955e5e7ca9732714dd055` (6) |
| `X` | none | `767950bd1b7f8d0d22fd3f389e70e0c04f03082a38953c1c0b1b1a46e91883b4` | `80e699e5593b9c9db2b9b20cd9483dc076ec88dc31f6715d124ff50ea0a45262` (5) |
| `zeroChecker` | none | `f3879aa3f9ec90750005d7a367e1ca8efcfff43656cad8bb70fc1be75a5eee2e` | `a82590f90bae108019b632d5482b7ee08c79b30b7f59fc4c5171e3c4b2165571` (2) |

**Toolchain.** `leanprover/lean4` tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (the tag points directly to this commit), pinned in `lean/lean-toolchain`. The Lake manifest lists no packages: the library depends on the Lean core library and `Std`, with no Mathlib and no other dependency.

**Primary sources.** Bibliographic records as cited in the cards (each record below is the bibliographic part of the corresponding prior-art entry, without the note that follows it); DOIs were resolved against the Crossref registry on 2026-11-21 (title, venue, volume, issue and pages match the records below). Books and book chapters are cited by chapter or page range, as stated in the cards. Five works have no DOI and are not listed in `REPORT.json`: Enderton (2001), Grice (1975), Henkin (1961), Horn (1984), and Geis and Zwicky (1971); for these the record below is the strongest identity given.

- H. B. Enderton, A Mathematical Introduction to Logic, 2nd ed., Harcourt/Academic Press, 2001, Chapter 2
- S. R. Bowman, G. Angeli, C. Potts, C. D. Manning, "A large annotated corpus for learning natural language inference", Proceedings of EMNLP 2015, pp. 632-642, doi:10.18653/v1/D15-1075
- J. Thorne, A. Vlachos, C. Christodoulopoulos, A. Mittal, "FEVER: a large-scale dataset for Fact Extraction and VERification", Proceedings of NAACL-HLT 2018, pp. 809-819, doi:10.18653/v1/N18-1074
- H. P. Grice, "Logic and Conversation", in P. Cole and J. L. Morgan (eds.), Syntax and Semantics, Vol. 3: Speech Acts, Academic Press, New York, 1975, pp. 41-58
- B. C. van Fraassen, "Singular terms, truth-value gaps, and free logic", Journal of Philosophy 63(17):481-495, 1966, doi:10.2307/2024549
- K. Fine, "Vagueness, truth and logic", Synthese 30(3-4):265-300, 1975, doi:10.1007/BF00485047
- M. Samer and S. Szeider, "Backdoor Sets of Quantified Boolean Formulas", Journal of Automated Reasoning 42(1):77-97, 2009, doi:10.1007/s10817-008-9114-5
- F. Slivovsky and S. Szeider, "Quantifier Reordering for QBF", Journal of Automated Reasoning 56(4):459-477, 2016, doi:10.1007/s10817-015-9353-1
- H. B. Enderton, A Mathematical Introduction to Logic, 2nd ed., Harcourt/Academic Press, 2001, Section 4.2 "Skolem functions"
- L. Henkin, "Some remarks on infinitely long formulas", in Infinitistic Methods (Proc. Symp. Foundations of Mathematics, Warsaw 1959), Pergamon/PWN, 1961, pp. 167-183
- W. J. Walkoe, Jr., "Finite partially-ordered quantification", Journal of Symbolic Logic 35(4):535-555, 1970, doi:10.2307/2271440
- V. Balabanov, H.-J. K. Chiang, J.-H. R. Jiang, "Henkin quantifiers and Boolean formulae: A certification perspective of DQBF", Theoretical Computer Science 523:86-100, 2014, doi:10.1016/j.tcs.2013.12.020
- H. S. Kurtzman and M. C. MacDonald, "Resolution of quantifier scope ambiguities", Cognition 48(3):243-279, 1993, doi:10.1016/0010-0277(93)90042-T
- S. A. Cook, "Soundness and completeness of an axiom system for program verification", SIAM J. Comput. 7(1):70-90, 1978, doi:10.1137/0207005
- L. R. Horn, "Toward a new taxonomy for pragmatic inference: Q-based and R-based implicature", in D. Schiffrin (ed.), Meaning, Form, and Use in Context: Linguistic Applications (GURT 1984), Georgetown University Press, 1984, pp. 11-42
- M. L. Geis and A. M. Zwicky, "On Invited Inferences", Linguistic Inquiry 2(4):561-566, 1971
- T. M. Mitchell, "Generalization as search", Artificial Intelligence 18(2):203-226, 1982, doi:10.1016/0004-3702(82)90040-6

Primary-source content is cited as prior art or as motivation for a modeling bridge; no paper or book above is formalized in this package.

## Revalidation

Requirements: `elan` (which installs the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

The script copies `lean/` to a temporary directory and runs `lake build`; scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations; runs a generated Lean program that computes, with `Lean.collectAxioms`, the axioms of every declaration of the library (allowed: `propext`, `Classical.choice`, `Quot.sound`); and recomputes, for every Lean name referenced by `results.json` and every name in `audit/statements.json`, the SHA-256 of the statement (`repr` of its type) and of its definition closure (types and values of every package constant reachable from the statement, theorem bodies excluded), comparing them with `audit/statements.json`. It prints `REVALIDATED` on success. The package itself is not modified.

A shorter check of the build and of per-declaration axioms, with `lake` and no Python:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` (outside the library target, so `lake build` does not build it) imports `ClaimStrength` and runs `#print axioms` for every Lean name referenced by `results.json`; each output line must list a subset of `propext`, `Classical.choice` and `Quot.sound`, or report that the declaration depends on no axioms. A passing run establishes that the recorded statements are kernel-checked under the pinned toolchain with the standard axioms; it does not re-establish the modeling bridges, which are argued in prose. A failed hash comparison means that a statement or a definition it reaches has changed, and the corresponding card must be re-examined.
