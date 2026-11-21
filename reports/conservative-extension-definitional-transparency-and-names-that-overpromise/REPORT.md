# Conservative extension, definitional transparency, and names that overpromise

## Summary

This package is a Lean 4 formalization (core Lean, no Mathlib) of when adding vocabulary to a theory or library preserves the meaning of what was already there, and of how names can promise more than their definitions deliver. It covers explicit definitions and their unfolding, axiomatized symbols, loose specifications of a function, finite example lists as would-be certificates, a cheap definition of "sorted", stored syntax versus displayed text under a toy elaborator, and requirements/specification criteria. Every result is a kernel-checked theorem about a toy model; claims about real systems are separate modeling-bridge claims, stated per card, and no model–system relation (embedding, abstraction or simulation) to any real system is proved.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Every predicate name used in this report denotes exactly the Lean definition of that name, quoted under **Applicability**; the table there lists the prose terms used for them. What each result does *not* show is listed under **Boundaries**, first subsection.

Results (plain-language claims, as recorded in `results.json`):

1. **`defext-expansions-eq-expand`** (characterization, T0). For any theory T, any explicit definition d (a new k-ary function symbol defined by an old term, or a new k-ary relation symbol defined by an old formula) and any model S of T: the structures on S's carrier that keep S's old symbols and satisfy the definitional extension T + d are exactly one structure, the canonical expansion d.expand S.
2. **`defext-expansion-unique-of-axiom`** (theorem, T0). For any explicit definition d, any L-structure S and any structure S' of the extended language on the same carrier: if the reduct of S' to L is S and S' satisfies the defining axiom of d, then S' is the canonical expansion d.expand S. No theory T is involved.
3. **`defext-conservative`** (theorem, T0). For any theory T and any explicit definition d, the definitional extension T + d is conservative over T: every old-language sentence it entails is entailed by T.
4. **`defext-unfold-preserves-sat-iff-defining-axiom`** (characterization, T1). For any explicit definition d and any structure S' of the extended language, the following are equivalent: (i) S' satisfies the defining axiom of d; (ii) unfolding preserves truth in S': every formula of the extended language has, under every assignment, the same truth value in S' as its unfolding d.unfold (each occurrence of the new symbol replaced by its definiens, read back along the inclusion); (iii) delta-conversion for d is sound in S': any two formulas whose unfoldings coincide have the same truth value in S' under every assignment. Moreover, for every theory T and formula psi, the definitional extension T + d entails the universal closure of psi <-> unfold psi.
5. **`explicit-definability-implies-unique-expansion`** (theorem, T0). For a theory T' over L plus one new k-ary function symbol c: if c is explicitly definable in T' (FnExplicitlyDefinable T': some old-language formula theta(y, x) satisfies T' |= forall y x, (c(x) = y <-> theta(y, x))), then any two models S1, S2 of T' on the same carrier whose reducts to L coincide are equal.
6. **`expansion-property-implies-conservative`** (theorem, T0). For any signature morphism iota : L -> L', theory T over L and theory T' over L': if every model of T expands (same carrier, old symbols read through iota unchanged) to a model of T', then T' is conservative over T along iota.
7. **`axiom-p-c-not-conservative`** (counterexample, T0). Over the language {P} with one unary predicate, the axiomatic extension of the empty theory by a fresh constant c with the single axiom P c entails the old-language sentence exists x, P x, which the empty theory does not entail; hence the extension is not conservative and does not have the expansion property.
8. **`fresh-constant-not-conservative-with-empty-carriers`** (counterexample, T1). With carriers allowed to be empty, over the language {P} (which has no closed terms), adding one fresh constant with no axioms to the empty theory is not conservative: the extension entails exists x, x = x, and the empty theory does not.
9. **`conservative-not-implies-expansion-property`** (counterexample, T1). Conservativity does not imply the expansion property: for T = Th(N0), the complete theory of (Nat + Nat, P = left), and T' = T plus 'the new unary function f maps the complement of P injectively into P', T' is conservative over T but does not have the expansion property; the model M0 = (Nat + (Nat -> Bool), P = left) of T has no expansion to a model of T'.
10. **`axext-entails-iff-lawful-interpretations`** (characterization, T0). For a theory T over L, axioms A over L plus one new k-ary function symbol, and a sentence psi of the extended language: T + A entails psi iff psi holds in S.withFn g for every model S of T (any carrier in Type) and every interpretation g of the new symbol for which S.withFn g satisfies A.
11. **`weak-sort-spec-admits-natsort-and-weirdsort`** (counterexample, T0). The characterization WeakSortSpec of a function List Nat -> List Nat ('for every list, the output is sorted by <= and has the input's length') is satisfied by merge sort natSort and by weirdSort = (l |-> replicate (length l) 0); these two functions differ, so WeakSortSpec has more than one lawful interpretation (not AtMostOneLawful WeakSortSpec).
12. **`strong-sort-spec-determines-natsort`** (characterization, T0). A function f : List Nat -> List Nat satisfies StrongSortSpec ('for every list, the output is sorted by <= and is a permutation of the input') iff f = natSort (merge sort). In particular StrongSortSpec determines a function: it has a lawful interpretation, and at most one.
13. **`label-deciders-agree-on-examples-one-misses-spec`** (theorem, T0). For any type a with decidable equality, intended predicate Spec, lists Pos and Neg with correct labels (every element of Pos satisfies Spec and no element of Neg does) and point x0 outside Pos ++ Neg: the two deciders memDecider Pos ('x is in Pos') and memDecider (x0 :: Pos) ('x is x0 or in Pos') both agree with Spec on every example, and at least one of them does not decide Spec.
14. **`unrestricted-decider-not-certified-by-finite-examples`** (impossibility, T0). For any infinite type a (no finite list contains every element), any intended predicate Spec on a and any finite example list E: some function d : a -> Bool, drawn from the unrestricted class of all Boolean-valued functions, agrees with Spec on E but does not decide Spec.
15. **`adjrel-iff-pairwise-on-all-lists-iff-transitive`** (characterization, T0). For any relation r on a type a: 'adjacent elements are related' (AdjRel r l) and 'every earlier element is related to every later one' (List.Pairwise r l) agree on every list l iff r is transitive.
16. **`adjrel-iff-pairwise-of-transon`** (theorem, T0). For any relation r and list l: if r is transitive on the elements of l (TransOn r l), then AdjRel r l holds iff List.Pairwise r l holds.
17. **`transon-not-necessary-for-single-list`** (counterexample, T1). For r = (!=) on Nat and the list [0, 1], AdjRel r [0, 1] and List.Pairwise r [0, 1] agree, although r is not transitive on the elements of [0, 1].
18. **`stored-formula-stable-under-expansion`** (theorem, T0). For any signature morphism iota : L -> L', structure S' of L' and formula phi of L: under every assignment, phi read along iota has the same truth value in S' as phi has in the reduct of S' (the old symbols read through iota).
19. **`text-not-stable-under-env-extension`** (counterexample, T1). In a toy elaborator from displayed arithmetic comparisons to stored sentences, each of three environment extensions (prepending int as the default numeral type, prepending a coercion nat -> int, prepending an instance making / on int Euclidean) changes the stored reading of an old displayed string from a false sentence to a true one in the intended structure on Int.
20. **`elab-preserves-check-iff`** (characterization, T0). For any two environments e, e' and finite list D of displayed strings of the toy elaborator: elabPreservesCheck e e' D = true iff every string of D that elaborates under e elaborates to the same stored sentence under e' (ElabPreservesAccepted); and elabInvariantCheck e e' D = true iff every string of D has the same elaboration result, including failure, under e and e' (ElabInvariantOn).
21. **`adequate-specconservative-implies-translated-domain-entails`** (theorem, T0). For a signature morphism iota : LE -> L, domain knowledge K and a requirement R over LE, and a specification Spec over L: if K u Spec adds no LE-consequence to the translated K (SpecConservative) and K, Spec |= R (Adequate), then the translated K already entails the translated R.
22. **`relconsistent-ev-requirement-implies-domain-entails`** (theorem, T1). In a split LEv -> LS -> LW (machine-visible environment-controlled phenomena, shared phenomena, environment-visible phenomena) with domain knowledge K over LW, a specification Spec over LS and a sentence rho over LEv: if Spec is relatively consistent with K (SpecRelConsistent: for every model M of K, some LS-structure on M's carrier has the same LEv-reduct as M and satisfies Spec, and every such LS-structure is the LS-reduct of some model of K on that carrier) and K, Spec |= rho (rho translated to LW; SpecAdequate), then K |= rho already.
23. **`crossing-control-spec-relconsistent-not-envconservative`** (counterexample, T1). With train environment-controlled and machine-visible, car environment-controlled and hidden, gate machine-controlled, domain knowledge domainA = {gate -> not car} and specification specA = {train -> gate}: the specification meets not (train and car) (SpecAdequate), the domain knowledge alone does not entail it, the specification is relatively consistent (SpecRelConsistent ιVSA ιSWA domainA specA), and domain knowledge plus specification is not consequence-conservative over the domain knowledge for sentences over the environment-controlled vocabulary {train, car} (not ConservativeFor ιEWA domainA (withSpec ιSWA domainA specA)).
24. **`crossing-restricting-spec-violates-env-input-condition`** (counterexample, T1). With train and car environment-controlled and machine-visible, gate machine-controlled and empty domain knowledge (ιSWB is the identity, so the shared and environment-visible vocabularies coincide): the specification specB = {train -> gate, gate -> not car} meets not (train and car) (SpecAdequate), the empty domain knowledge does not entail not (train and car), and specB does not accept every environment input (not SpecAcceptsEveryEnvInput ιVSB ιSWB Theory.empty specB); moreover, for every specification Spec over these phenomena, if Spec meets not (train and car) with empty domain knowledge, then Spec is not relatively consistent (not SpecRelConsistent ιVSB ιSWB Theory.empty Spec).

## Applicability

**Model fidelity.** All definitions are toy models written for this package; none is a production definition of an existing system. The first-order part is a single-sorted language with equality, well-scoped de Bruijn syntax, and Tarskian semantics over structures whose carriers are arbitrary types in `Type`, empty carriers included; semantic consequence (`Entails`) quantifies over all such structures. No proof system is modeled, so "conservative" always means consequence-conservativity for semantic entailment. The definitions are meant to capture: definitions and axioms added to a library (explicit definitions of one function or relation symbol, and fresh symbols characterized by axioms); a checker seeing through a defined name (`Defn.DeltaConv`, conversion for one defined symbol over first-order syntax); transparency of a name as explicit definability (`FnExplicitlyDefinable`); loose specifications of a function `List Nat → List Nat`; finite labeled tests of a Boolean-valued definition; a toy elaborator from displayed arithmetic comparisons to stored sentences (`Env.elab`, with default numeral types, coercions and operator instances); and the requirements setting of Zave and Jackson (1997) and of Gunter, Gunter, Jackson and Zave (2000), rendered model-theoretically over one shared carrier.

**Known gaps.** Kernel definitional equality of a dependent type theory, recursive, inductive, overloaded or polymorphic definitions, definitions by unique existence, proof systems, notation and name resolution, Lean's actual elaborator, time, and the machine and program of the reference model are not modeled. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean, Isabelle/HOL, any other proof assistant, or the reference model of Gunter et al.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library and `Std`, with no Mathlib and no other Lake dependency. The library `Toy` (namespace `Toy.Extension`) lives in `lean/`.

**Subjects.** `REPORT.json` lists the Lean toolchain that checks every proof, upstream library sources quoted for prior art (the Lean Language Reference at tag `v4.34.0`, Batteries at tag `v4.29.0`, the Rocq standard library at tag `V9.2.0`), and the papers whose notions are rendered or compared (Gunter et al. 2000; Zave and Jackson 1997; Beth 1953; Kunčar and Popescu 2018). The papers and libraries are prior art or modeling sources; none of them is formalized here.

### Names

| Prose term | Lean predicate (quoted below or in the card) | Exact meaning |
| :-- | :-- | :-- |
| T entails φ, T ⊨ φ | `Entails T φ` | φ holds in every model of T with carrier in `Type`, empty carriers included |
| conservative along ι | `Conservative ι T T'` | every L-sentence φ with `Entails T' (φ.map ι)` has `Entails T φ` (consequence-conservativity) |
| expansion property | `ExpansionProperty ι T T'` | every model of T expands, on the same carrier and with the old symbols read through ι unchanged, to a model of T' |
| definitional extension T + d | `Defn.theory T d` | the translated axioms of T together with the defining axiom `d.defAxiom` |
| canonical expansion | `Defn.expand d S` | S with the new symbol interpreted by its definiens |
| unfolding | `Defn.unfold d` | the syntactic replacement of the new symbol by its definiens (capture-avoiding) |
| delta-convertible | `Defn.DeltaConv d φ ψ` | `d.unfold φ = d.unfold ψ` (syntactic equality of unfoldings) |
| explicitly definable | `FnExplicitlyDefinable T'` | some old-language formula θ with `Entails T' (fnDefiningSentence θ)`; defined for a new function symbol (no relation-symbol version) |
| lawful interpretation | an expansion satisfying the axioms, or a function satisfying `Lspec` | as stated in each card |
| at most one lawful interpretation | `AtMostOneLawful Lspec` | any two functions satisfying `Lspec` are equal (vacuous if none does) |
| determines | `Determines Lspec` | some function satisfies `Lspec`, and `AtMostOneLawful Lspec` |
| agrees on the examples | `AgreesOn d Spec E` | `d x = true ↔ Spec x` for every x in the list E |
| decides | `Decides d Spec` | `d x = true ↔ Spec x` for every x |
| certified by examples | (no predicate) | prose for: every candidate in the class that agrees on the examples decides Spec |
| infinite type | `InfiniteType α` | no list contains every element of α |
| adjacent elements related | `AdjRel r l` | consecutive elements of l are related by r |
| transitive / transitive on l | `TransitiveRel r` / `TransOn r l` | global transitivity / transitivity with all three elements drawn from l |
| invariant on D | `ElabInvariantOn e e' D` | every string of D has the same elaboration result (including failure) under e and e' |
| preserves accepted strings | `ElabPreservesAccepted e e' D` | every string of D accepted under e elaborates to the same sentence under e' |
| adequate (generic setting) | `Adequate ι K Spec R` | `Entails (combined ι K Spec) (R.map ι)` |
| spec-conservative | `SpecConservative ι K Spec` | `combined ι K Spec` entails no translated LE-sentence beyond those `K.map ι` entails |
| adequate (split setting) | `SpecAdequate ιSW K Spec R` | `Entails (withSpec ιSW K Spec) R` |
| relatively consistent | `SpecRelConsistent ιVS ιSW K Spec` | `SpecAcceptsEveryEnvInput ∧ SpecResponsesDomainConsistent` (both quoted below) |
| consequence-conservative for LE-sentences | `ConservativeFor ιEW K K'` | every LE-sentence that K' entails (read in LW) is entailed by K |

Words inside theorem names abbreviate exact propositions and are not further predicates:
`not_conservative` means `¬ Conservative …`; `envConservative` (card 23) means
`ConservativeFor ιEWA domainA (withSpec ιSWA domainA specA)`; `violates_env_input_condition` (card 24) means
`¬ SpecAcceptsEveryEnvInput ιVSB ιSWB Theory.empty specB` (plus the further conjuncts quoted in the card);
`flips_truth` (card 19) means "the old elaboration is false and the new one is true in `intStr`";
`not_certified` (card 14) means "agrees on the examples but does not decide"; `translated_domain_entails`
(card 21) means `Entails (K.map ι) (R.map ι)`, not `Entails K R`.

### Key definitions (verbatim)

Each block quotes the source verbatim; the first line gives the file and line range within the package.

```lean
-- lean/Toy/Extension/Syntax.lean:11-15
structure Sig where
  Fn : Type
  Rel : Type
  fnArity : Fn → Nat
  relArity : Rel → Nat
```

```lean
-- lean/Toy/Extension/Syntax.lean:21-25
structure SigHom (L L' : Sig) where
  fn : L.Fn → L'.Fn
  rel : L.Rel → L'.Rel
  fnArity : ∀ f, L'.fnArity (fn f) = L.fnArity f
  relArity : ∀ r, L'.relArity (rel r) = L.relArity r
```

```lean
-- lean/Toy/Extension/Syntax.lean:30-32
inductive Term (L : Sig) (n : Nat) : Type where
  | var : Fin n → Term L n
  | app : (f : L.Fn) → (Fin (L.fnArity f) → Term L n) → Term L n
```

```lean
-- lean/Toy/Extension/Syntax.lean:36-44
inductive Formula (L : Sig) : Nat → Type where
  | eq {n : Nat} : Term L n → Term L n → Formula L n
  | rel {n : Nat} : (r : L.Rel) → (Fin (L.relArity r) → Term L n) → Formula L n
  | falsum {n : Nat} : Formula L n
  | imp {n : Nat} : Formula L n → Formula L n → Formula L n
  | and {n : Nat} : Formula L n → Formula L n → Formula L n
  | or {n : Nat} : Formula L n → Formula L n → Formula L n
  | all {n : Nat} : Formula L (n + 1) → Formula L n
  | ex {n : Nat} : Formula L (n + 1) → Formula L n
```

```lean
-- lean/Toy/Extension/Syntax.lean:48
abbrev Sentence (L : Sig) := Formula L 0
```

```lean
-- lean/Toy/Extension/Syntax.lean:55
def not {n : Nat} (φ : Formula L n) : Formula L n := imp φ falsum
```

```lean
-- lean/Toy/Extension/Syntax.lean:58
def tru {n : Nat} : Formula L n := imp falsum falsum
```

```lean
-- lean/Toy/Extension/Syntax.lean:61
def iff {n : Nat} (φ ψ : Formula L n) : Formula L n := and (imp φ ψ) (imp ψ φ)
```

```lean
-- lean/Toy/Extension/Syntax.lean:64-66
def closeAll : (k : Nat) → Formula L k → Sentence L
  | 0, φ => φ
  | k + 1, φ => closeAll k (all φ)
```

```lean
-- lean/Toy/Extension/Syntax.lean:77-79
def rename {n m : Nat} (ρ : Fin n → Fin m) : Term L n → Term L m
  | var i => var (ρ i)
  | app f ts => app f (fun j => (ts j).rename ρ)
```

```lean
-- lean/Toy/Extension/Syntax.lean:82-84
def subst {k n : Nat} (σ : Fin k → Term L n) : Term L k → Term L n
  | var i => σ i
  | app f ts => app f (fun j => (ts j).subst σ)
```

```lean
-- lean/Toy/Extension/Syntax.lean:87-89
def map {L' : Sig} (ι : SigHom L L') {n : Nat} : Term L n → Term L' n
  | var i => var i
  | app f ts => app (ι.fn f) (fun j => (ts (Fin.cast (ι.fnArity f) j)).map ι)
```

```lean
-- lean/Toy/Extension/Syntax.lean:99-101
def liftSubst {L : Sig} {k n : Nat} (σ : Fin k → Term L n) : Fin (k + 1) → Term L (n + 1)
  | ⟨0, _⟩ => Term.var ⟨0, Nat.succ_pos _⟩
  | ⟨j + 1, h⟩ => (σ ⟨j, Nat.lt_of_succ_lt_succ h⟩).rename Fin.succ
```

```lean
-- lean/Toy/Extension/Syntax.lean:120-128
def subst : {k n : Nat} → (Fin k → Term L n) → Formula L k → Formula L n
  | _, _, σ, eq s t => eq (s.subst σ) (t.subst σ)
  | _, _, σ, rel r ts => rel r (fun j => (ts j).subst σ)
  | _, _, _, falsum => falsum
  | _, _, σ, imp φ ψ => imp (φ.subst σ) (ψ.subst σ)
  | _, _, σ, and φ ψ => and (φ.subst σ) (ψ.subst σ)
  | _, _, σ, or φ ψ => or (φ.subst σ) (ψ.subst σ)
  | _, _, σ, all φ => all (φ.subst (liftSubst σ))
  | _, _, σ, ex φ => ex (φ.subst (liftSubst σ))
```

```lean
-- lean/Toy/Extension/Syntax.lean:132-140
def map {L' : Sig} (ι : SigHom L L') : {n : Nat} → Formula L n → Formula L' n
  | _, eq s t => eq (s.map ι) (t.map ι)
  | _, rel r ts => rel (ι.rel r) (fun j => (ts (Fin.cast (ι.relArity r) j)).map ι)
  | _, falsum => falsum
  | _, imp φ ψ => imp (φ.map ι) (ψ.map ι)
  | _, and φ ψ => and (φ.map ι) (ψ.map ι)
  | _, or φ ψ => or (φ.map ι) (ψ.map ι)
  | _, all φ => all (φ.map ι)
  | _, ex φ => ex (φ.map ι)
```

```lean
-- lean/Toy/Extension/Semantics.lean:12-14
structure Str (L : Sig) (α : Type) where
  fn : (f : L.Fn) → (Fin (L.fnArity f) → α) → α
  rel : (r : L.Rel) → (Fin (L.relArity r) → α) → Prop
```

```lean
-- lean/Toy/Extension/Semantics.lean:17-19
def scons {α : Type} {n : Nat} (a : α) (v : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩ => a
  | ⟨k + 1, h⟩ => v ⟨k, Nat.lt_of_succ_lt_succ h⟩
```

```lean
-- lean/Toy/Extension/Semantics.lean:22
def noVars {α : Type} : Fin 0 → α := fun i => i.elim0
```

```lean
-- lean/Toy/Extension/Semantics.lean:27-29
def Term.eval (S : Str L α) {n : Nat} (v : Fin n → α) : Term L n → α
  | .var i => v i
  | .app f ts => S.fn f (fun j => (ts j).eval S v)
```

```lean
-- lean/Toy/Extension/Semantics.lean:32-40
def Sat (S : Str L α) : {n : Nat} → (Fin n → α) → Formula L n → Prop
  | _, v, .eq s t => s.eval S v = t.eval S v
  | _, v, .rel r ts => S.rel r (fun j => (ts j).eval S v)
  | _, _, .falsum => False
  | _, v, .imp φ ψ => Sat S v φ → Sat S v ψ
  | _, v, .and φ ψ => Sat S v φ ∧ Sat S v ψ
  | _, v, .or φ ψ => Sat S v φ ∨ Sat S v ψ
  | _, v, .all φ => ∀ a, Sat S (scons a v) φ
  | _, v, .ex φ => ∃ a, Sat S (scons a v) φ
```

```lean
-- lean/Toy/Extension/Semantics.lean:43
def Str.Models (S : Str L α) (φ : Sentence L) : Prop := Sat S noVars φ
```

```lean
-- lean/Toy/Extension/Semantics.lean:46
abbrev Theory (L : Sig) := Sentence L → Prop
```

```lean
-- lean/Toy/Extension/Semantics.lean:49
def Str.ModelsTh (S : Str L α) (T : Theory L) : Prop := ∀ φ, T φ → S.Models φ
```

```lean
-- lean/Toy/Extension/Semantics.lean:53-54
def Entails (T : Theory L) (φ : Sentence L) : Prop :=
  ∀ (β : Type) (S : Str L β), S.ModelsTh T → S.Models φ
```

```lean
-- lean/Toy/Extension/Semantics.lean:59
def empty : Theory L := fun _ => False
```

```lean
-- lean/Toy/Extension/Semantics.lean:62
def union (T U : Theory L) : Theory L := fun φ => T φ ∨ U φ
```

```lean
-- lean/Toy/Extension/Semantics.lean:65
def ofList (l : List (Sentence L)) : Theory L := fun φ => φ ∈ l
```

```lean
-- lean/Toy/Extension/Semantics.lean:69
def map (ι : SigHom L L') (T : Theory L) : Theory L' := fun ψ => ∃ φ, T φ ∧ φ.map ι = ψ
```

```lean
-- lean/Toy/Extension/Semantics.lean:72
def th (S : Str L α) : Theory L := fun φ => S.Models φ
```

```lean
-- lean/Toy/Extension/Semantics.lean:78-80
def Str.reduct (ι : SigHom L L') (S : Str L' α) : Str L α where
  fn f args := S.fn (ι.fn f) (fun j => args (Fin.cast (ι.fnArity f) j))
  rel r args := S.rel (ι.rel r) (fun j => args (Fin.cast (ι.relArity r) j))
```

```lean
-- lean/Toy/Extension/Semantics.lean:84-85
def Conservative (ι : SigHom L L') (T : Theory L) (T' : Theory L') : Prop :=
  ∀ φ : Sentence L, Entails T' (φ.map ι) → Entails T φ
```

```lean
-- lean/Toy/Extension/Semantics.lean:89-90
def ExpansionProperty (ι : SigHom L L') (T : Theory L) (T' : Theory L') : Prop :=
  ∀ (β : Type) (S : Str L β), S.ModelsTh T → ∃ S' : Str L' β, S'.reduct ι = S ∧ S'.ModelsTh T'
```

```lean
-- lean/Toy/Extension/Definitional.lean:17-23
def Sig.addFn (L : Sig) (k : Nat) : Sig where
  Fn := Option L.Fn
  Rel := L.Rel
  fnArity := fun f => match f with
    | none => k
    | some f => L.fnArity f
  relArity := L.relArity
```

```lean
-- lean/Toy/Extension/Definitional.lean:26-32
def Sig.addRel (L : Sig) (k : Nat) : Sig where
  Fn := L.Fn
  Rel := Option L.Rel
  fnArity := L.fnArity
  relArity := fun r => match r with
    | none => k
    | some r => L.relArity r
```

```lean
-- lean/Toy/Extension/Definitional.lean:35-39
def SigHom.inclFn (L : Sig) (k : Nat) : SigHom L (L.addFn k) where
  fn := some
  rel := id
  fnArity := fun _ => rfl
  relArity := fun _ => rfl
```

```lean
-- lean/Toy/Extension/Definitional.lean:42-46
def SigHom.inclRel (L : Sig) (k : Nat) : SigHom L (L.addRel k) where
  fn := id
  rel := some
  fnArity := fun _ => rfl
  relArity := fun _ => rfl
```

```lean
-- lean/Toy/Extension/Definitional.lean:49-53
def Str.withFn {k : Nat} (S : Str L α) (g : (Fin k → α) → α) : Str (L.addFn k) α where
  fn := fun f => match f with
    | none => g
    | some f => S.fn f
  rel := S.rel
```

```lean
-- lean/Toy/Extension/Definitional.lean:56-60
def Str.withRel {k : Nat} (S : Str L α) (p : (Fin k → α) → Prop) : Str (L.addRel k) α where
  fn := S.fn
  rel := fun r => match r with
    | none => p
    | some r => S.rel r
```

```lean
-- lean/Toy/Extension/Definitional.lean:83-85
inductive Defn (L : Sig) : Type where
  | fn (k : Nat) (e : Term L k)
  | rel (k : Nat) (e : Formula L k)
```

```lean
-- lean/Toy/Extension/Definitional.lean:90-92
def sig : Defn L → Sig
  | fn k _ => L.addFn k
  | rel k _ => L.addRel k
```

```lean
-- lean/Toy/Extension/Definitional.lean:95-97
def incl : (d : Defn L) → SigHom L d.sig
  | fn k _ => SigHom.inclFn L k
  | rel k _ => SigHom.inclRel L k
```

```lean
-- lean/Toy/Extension/Definitional.lean:100-104
def defAxiom : (d : Defn L) → Sentence d.sig
  | fn k e => Formula.closeAll k
      (.eq (.app (none : (L.addFn k).Fn) (fun i => .var i)) (e.map (SigHom.inclFn L k)))
  | rel k e => Formula.closeAll k
      (.iff (.rel (none : (L.addRel k).Rel) (fun i => .var i)) (e.map (SigHom.inclRel L k)))
```

```lean
-- lean/Toy/Extension/Definitional.lean:108-109
def theory (T : Theory L) (d : Defn L) : Theory d.sig :=
  (T.map d.incl).union (Theory.ofList [d.defAxiom])
```

```lean
-- lean/Toy/Extension/Definitional.lean:112-114
def expand : (d : Defn L) → Str L α → Str d.sig α
  | fn _ e, S => S.withFn (fun args => e.eval S args)
  | rel _ e, S => S.withRel (fun args => Sat S args e)
```

```lean
-- lean/Toy/Extension/Definitional.lean:119-122
def unfoldFnTerm {k : Nat} (e : Term L k) {n : Nat} : Term (L.addFn k) n → Term L n
  | .var i => .var i
  | .app none ts => e.subst (fun j => unfoldFnTerm e (ts j))
  | .app (some f) ts => .app f (fun j => unfoldFnTerm e (ts j))
```

```lean
-- lean/Toy/Extension/Definitional.lean:125-133
def unfoldFnFormula {k : Nat} (e : Term L k) : {n : Nat} → Formula (L.addFn k) n → Formula L n
  | _, .eq s t => .eq (unfoldFnTerm e s) (unfoldFnTerm e t)
  | _, .rel r ts => .rel r (fun j => unfoldFnTerm e (ts j))
  | _, .falsum => .falsum
  | _, .imp φ ψ => .imp (unfoldFnFormula e φ) (unfoldFnFormula e ψ)
  | _, .and φ ψ => .and (unfoldFnFormula e φ) (unfoldFnFormula e ψ)
  | _, .or φ ψ => .or (unfoldFnFormula e φ) (unfoldFnFormula e ψ)
  | _, .all φ => .all (unfoldFnFormula e φ)
  | _, .ex φ => .ex (unfoldFnFormula e φ)
```

```lean
-- lean/Toy/Extension/Definitional.lean:136-138
def relTermDown {k n : Nat} : Term (L.addRel k) n → Term L n
  | .var i => .var i
  | .app f ts => .app f (fun j => relTermDown (ts j))
```

```lean
-- lean/Toy/Extension/Definitional.lean:142-151
def unfoldRelFormula {k : Nat} (e : Formula L k) : {n : Nat} → Formula (L.addRel k) n → Formula L n
  | _, .eq s t => .eq (relTermDown s) (relTermDown t)
  | _, .rel none ts => e.subst (fun j => relTermDown (ts j))
  | _, .rel (some r) ts => .rel r (fun j => relTermDown (ts j))
  | _, .falsum => .falsum
  | _, .imp φ ψ => .imp (unfoldRelFormula e φ) (unfoldRelFormula e ψ)
  | _, .and φ ψ => .and (unfoldRelFormula e φ) (unfoldRelFormula e ψ)
  | _, .or φ ψ => .or (unfoldRelFormula e φ) (unfoldRelFormula e ψ)
  | _, .all φ => .all (unfoldRelFormula e φ)
  | _, .ex φ => .ex (unfoldRelFormula e φ)
```

```lean
-- lean/Toy/Extension/Definitional.lean:154-156
def Defn.unfold : (d : Defn L) → {n : Nat} → Formula d.sig n → Formula L n
  | .fn _ e, _, ψ => unfoldFnFormula e ψ
  | .rel _ e, _, ψ => unfoldRelFormula e ψ
```

```lean
-- lean/Toy/Extension/Definitional.lean:512-513
def Defn.DeltaConv (d : Defn L) {n : Nat} (φ ψ : Formula d.sig n) : Prop :=
  d.unfold φ = d.unfold ψ
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:46
def SigHom.id (L : Sig) : SigHom L L := ⟨fun f => f, fun r => r, fun _ => rfl, fun _ => rfl⟩
```

```lean
-- lean/Toy/Extension/Transparency.lean:20-23
def fnDefiningSentence {k : Nat} (θ : Formula L (k + 1)) : Sentence (L.addFn k) :=
  Formula.closeAll (k + 1)
    (.iff (.eq (.app (none : (L.addFn k).Fn) (fun i => .var i.succ)) (.var ⟨0, Nat.succ_pos k⟩))
      (θ.map (SigHom.inclFn L k)))
```

```lean
-- lean/Toy/Extension/Transparency.lean:27-28
def FnExplicitlyDefinable {k : Nat} (T' : Theory (L.addFn k)) : Prop :=
  ∃ θ : Formula L (k + 1), Entails T' (fnDefiningSentence θ)
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:11-12
def WeakSortSpec (f : List Nat → List Nat) : Prop :=
  ∀ l, List.Pairwise (· ≤ ·) (f l) ∧ (f l).length = l.length
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:15-16
def StrongSortSpec (f : List Nat → List Nat) : Prop :=
  ∀ l, List.Pairwise (· ≤ ·) (f l) ∧ (f l).Perm l
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:19
def weirdSort (l : List Nat) : List Nat := List.replicate l.length 0
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:22
def natSort (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:27-28
def AtMostOneLawful {X Y : Type} (Lspec : (X → Y) → Prop) : Prop :=
  ∀ f g, Lspec f → Lspec g → f = g
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:32-33
def Determines {X Y : Type} (Lspec : (X → Y) → Prop) : Prop :=
  (∃ f, Lspec f) ∧ AtMostOneLawful Lspec
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:16-17
def AgreesOn (d : α → Bool) (Spec : α → Prop) (E : List α) : Prop :=
  ∀ x ∈ E, (d x = true ↔ Spec x)
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:20-21
def Decides (d : α → Bool) (Spec : α → Prop) : Prop :=
  ∀ x, (d x = true ↔ Spec x)
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:24-25
def InfiniteType (α : Type) : Prop :=
  ∀ l : List α, ∃ x, x ∉ l
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:28-29
def LabelsCorrect (Spec : α → Prop) (Pos Neg : List α) : Prop :=
  (∀ x ∈ Pos, Spec x) ∧ ∀ x ∈ Neg, ¬ Spec x
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:35
def memDecider [DecidableEq α] (l : List α) : α → Bool := fun x => decide (x ∈ l)
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:219
def thresholdDecider (k : Nat) : Nat → Bool := fun x => decide (k ≤ x)
```

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:13-16
def AdjRel (r : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => r a b ∧ AdjRel r (b :: l)
```

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:27-28
def TransitiveRel (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r b c → r a c
```

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:33-34
def TransOn (r : α → α → Prop) (l : List α) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, r a b → r b c → r a c
```

```lean
-- lean/Toy/Extension/Elaboration.lean:46-47
inductive Ty | nat | int
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Elaboration.lean:50-51
inductive Op | add | sub | div
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Elaboration.lean:56-57
inductive AFn | lit (k : Nat) | add | subN | subZ | divT | divE | castNZ | castZN
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Elaboration.lean:60-61
inductive ARel | lt
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Elaboration.lean:64-68
def AFn.arity : AFn → Nat
  | .lit _ => 0
  | .castNZ => 1
  | .castZN => 1
  | _ => 2
```

```lean
-- lean/Toy/Extension/Elaboration.lean:71
abbrev ASig : Sig := ⟨AFn, ARel, AFn.arity, fun _ => 2⟩
```

```lean
-- lean/Toy/Extension/Elaboration.lean:75-86
def intStr : Str ASig Int where
  fn := fun f => match f with
    | .lit k => fun _ => (k : Int)
    | .add => fun a => a ⟨0, by decide⟩ + a ⟨1, by decide⟩
    | .subN => fun a => if a ⟨1, by decide⟩ ≤ a ⟨0, by decide⟩ then a ⟨0, by decide⟩ - a ⟨1, by decide⟩ else 0
    | .subZ => fun a => a ⟨0, by decide⟩ - a ⟨1, by decide⟩
    | .divT => fun a => Int.tdiv (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | .divE => fun a => Int.ediv (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | .castNZ => fun a => a ⟨0, by decide⟩
    | .castZN => fun a => if 0 ≤ a ⟨0, by decide⟩ then a ⟨0, by decide⟩ else 0
  rel := fun r => match r with
    | .lt => fun a => a ⟨0, by decide⟩ < a ⟨1, by decide⟩
```

```lean
-- lean/Toy/Extension/Elaboration.lean:91-94
structure Env where
  defaults : List Ty
  coercions : List (Ty × Ty)
  instances : List (Op × Ty × AFn)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:97-100
inductive Stx
  | num : Nat → Stx
  | numAt : Nat → Ty → Stx
  | bin : Op → Stx → Stx → Stx
```

```lean
-- lean/Toy/Extension/Elaboration.lean:103-104
inductive Disp
  | lt : Stx → Stx → Disp
```

```lean
-- lean/Toy/Extension/Elaboration.lean:107-110
def Stx.annots : Stx → List Ty
  | .num _ => []
  | .numAt _ t => [t]
  | .bin _ a b => a.annots ++ b.annots
```

```lean
-- lean/Toy/Extension/Elaboration.lean:113-117
def Env.joinTy (e : Env) (t u : Ty) : Option Ty :=
  if t = u then some t else
  match e.coercions.find? (fun c => (c.1 == t && c.2 == u) || (c.1 == u && c.2 == t)) with
  | some c => some c.2
  | none => none
```

```lean
-- lean/Toy/Extension/Elaboration.lean:120-124
def Env.joinAll (e : Env) : Ty → List Ty → Option Ty
  | acc, [] => some acc
  | acc, u :: us => match e.joinTy acc u with
    | some t => e.joinAll t us
    | none => none
```

```lean
-- lean/Toy/Extension/Elaboration.lean:128-130
def Env.treeTy (e : Env) : List Ty → Option Ty
  | [] => e.defaults.head?
  | t :: ts => e.joinAll t ts
```

```lean
-- lean/Toy/Extension/Elaboration.lean:133-136
def castSym : Ty → Ty → Option AFn
  | .nat, .int => some .castNZ
  | .int, .nat => some .castZN
  | _, _ => none
```

```lean
-- lean/Toy/Extension/Elaboration.lean:139
def lit {n : Nat} (k : Nat) : Term ASig n := .app (AFn.lit k) (fun i => i.elim0)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:142
def app1 {n : Nat} (f : AFn) (x : Term ASig n) : Term ASig n := .app f (fun _ => x)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:145-146
def app2 {n : Nat} (f : AFn) (x y : Term ASig n) : Term ASig n :=
  .app f (fun j => if j.val = 0 then x else y)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:149-151
def Env.coe (e : Env) (t τ : Ty) (x : Term ASig 0) : Option (Term ASig 0) :=
  if t = τ then some x
  else if (t, τ) ∈ e.coercions then (castSym t τ).map (fun f => app1 f x) else none
```

```lean
-- lean/Toy/Extension/Elaboration.lean:154-155
def Env.lookupInst (e : Env) (op : Op) (τ : Ty) : Option AFn :=
  (e.instances.find? (fun i => i.1 == op && i.2.1 == τ)).map (fun i => i.2.2)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:158-164
def Env.elabAt (e : Env) (τ : Ty) : Stx → Option (Term ASig 0)
  | .num k => some (lit k)
  | .numAt k t => e.coe t τ (lit k)
  | .bin op a b =>
    match e.lookupInst op τ, e.elabAt τ a, e.elabAt τ b with
    | some f, some x, some y => some (app2 f x y)
    | _, _, _ => none
```

```lean
-- lean/Toy/Extension/Elaboration.lean:167-174
def Env.elab (e : Env) : Disp → Option (Sentence ASig)
  | .lt a b =>
    match e.treeTy (a.annots ++ b.annots) with
    | none => none
    | some τ =>
      match e.elabAt τ a, e.elabAt τ b with
      | some x, some y => some (.rel ARel.lt (fun j => if j.val = 0 then x else y))
      | _, _ => none
```

```lean
-- lean/Toy/Extension/Elaboration.lean:178-179
def Env.Extends (e' e : Env) : Prop :=
  ∃ ds cs is, e' = ⟨ds ++ e.defaults, cs ++ e.coercions, is ++ e.instances⟩
```

```lean
-- lean/Toy/Extension/Elaboration.lean:184-185
def ElabInvariantOn (e e' : Env) (D : List Disp) : Prop :=
  ∀ s ∈ D, e.elab s = e'.elab s
```

```lean
-- lean/Toy/Extension/Elaboration.lean:190-191
def ElabPreservesAccepted (e e' : Env) (D : List Disp) : Prop :=
  ∀ s ∈ D, ∀ φ, e.elab s = some φ → e'.elab s = some φ
```

```lean
-- lean/Toy/Extension/Elaboration.lean:194-195
def elabInvariantCheck (e e' : Env) (D : List Disp) : Bool :=
  D.all (fun s => decide (e.elab s = e'.elab s))
```

```lean
-- lean/Toy/Extension/Elaboration.lean:198-201
def elabPreservesCheck (e e' : Env) (D : List Disp) : Bool :=
  D.all fun s => match e.elab s with
    | none => true
    | some φ => decide (e'.elab s = some φ)
```

```lean
-- lean/Toy/Extension/Requirements.lean:30-31
def combined (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L) : Theory L :=
  (K.map ι).union Spec
```

```lean
-- lean/Toy/Extension/Requirements.lean:34-35
def Adequate (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L) (R : Sentence LE) : Prop :=
  Entails (combined ι K Spec) (R.map ι)
```

```lean
-- lean/Toy/Extension/Requirements.lean:40-42
def SpecAddedConsequence (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L)
    (φ : Sentence LE) : Prop :=
  Entails (combined ι K Spec) (φ.map ι) ∧ ¬ Entails (K.map ι) (φ.map ι)
```

```lean
-- lean/Toy/Extension/Requirements.lean:45-46
def SpecConservative (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L) : Prop :=
  ∀ φ : Sentence LE, Entails (combined ι K Spec) (φ.map ι) → Entails (K.map ι) (φ.map ι)
```

```lean
-- lean/Toy/Extension/Requirements.lean:50-52
def SpecExpansionProperty (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L) : Prop :=
  ∀ (β : Type) (M : Str L β), M.ModelsTh (K.map ι) →
    ∃ M' : Str L β, M'.reduct ι = M.reduct ι ∧ M'.ModelsTh (combined ι K Spec)
```

```lean
-- lean/Toy/Extension/Requirements.lean:214-215
def withSpec (ιSW : SigHom LS LW) (K : Theory LW) (Spec : Theory LS) : Theory LW :=
  K.union (Spec.map ιSW)
```

```lean
-- lean/Toy/Extension/Requirements.lean:218-220
def SpecAdequate (ιSW : SigHom LS LW) (K : Theory LW) (Spec : Theory LS) (R : Sentence LW) :
    Prop :=
  Entails (withSpec ιSW K Spec) R
```

```lean
-- lean/Toy/Extension/Requirements.lean:225-228
def SpecAcceptsEveryEnvInput (ιVS : SigHom LEv LS) (ιSW : SigHom LS LW) (K : Theory LW)
    (Spec : Theory LS) : Prop :=
  ∀ (β : Type) (M : Str LW β), M.ModelsTh K →
    ∃ N : Str LS β, N.reduct ιVS = (M.reduct ιSW).reduct ιVS ∧ N.ModelsTh Spec
```

```lean
-- lean/Toy/Extension/Requirements.lean:233-237
def SpecResponsesDomainConsistent (ιVS : SigHom LEv LS) (ιSW : SigHom LS LW) (K : Theory LW)
    (Spec : Theory LS) : Prop :=
  ∀ (β : Type) (M : Str LW β), M.ModelsTh K → ∀ N : Str LS β,
    N.reduct ιVS = (M.reduct ιSW).reduct ιVS → N.ModelsTh Spec →
      ∃ M' : Str LW β, M'.reduct ιSW = N ∧ M'.ModelsTh K
```

```lean
-- lean/Toy/Extension/Requirements.lean:240-242
def SpecRelConsistent (ιVS : SigHom LEv LS) (ιSW : SigHom LS LW) (K : Theory LW)
    (Spec : Theory LS) : Prop :=
  SpecAcceptsEveryEnvInput ιVS ιSW K Spec ∧ SpecResponsesDomainConsistent ιVS ιSW K Spec
```

```lean
-- lean/Toy/Extension/Requirements.lean:247-248
def ConservativeFor (ιEW : SigHom LE LW) (K K' : Theory LW) : Prop :=
  ∀ φ : Sentence LE, Entails K' (φ.map ιEW) → Entails K (φ.map ιEW)
```

### Concrete objects used in the counterexamples (verbatim)

```lean
-- lean/Toy/Extension/Axiomatic.lean:18-19
inductive PRel | P
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:22
abbrev LP : Sig := ⟨Empty, PRel, fun e => e.elim, fun _ => 1⟩
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:25-27
def pStr {β : Type} (p : β → Prop) : Str LP β where
  fn := fun e => e.elim
  rel := fun _ args => p (args ⟨0, Nat.zero_lt_one⟩)
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:30
def tC {n : Nat} : Term (LP.addFn 0) n := .app (none : (LP.addFn 0).Fn) (fun i => i.elim0)
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:33
def axPc : Sentence (LP.addFn 0) := .rel PRel.P (fun _ => tC)
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:36
def existsP : Sentence LP := .ex (.rel PRel.P (fun _ => .var 0))
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:42
def existsEq {L : Sig} : Sentence L := .ex (.eq (.var 0) (.var 0))
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:152-153
inductive ABRel | a | b
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:156
abbrev LAB : Sig := ⟨Empty, ABRel, fun e => e.elim, fun _ => 0⟩
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:159
abbrev LUnit : Sig := ⟨Empty, Unit, fun e => e.elim, fun _ => 0⟩
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:162
def ιCollapse : SigHom LAB LUnit := ⟨id, fun _ => (), fun e => e.elim, fun _ => rfl⟩
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:165-166
def abIff : Sentence LAB :=
  Formula.iff (.rel ABRel.a (fun i => i.elim0)) (.rel ABRel.b (fun i => i.elim0))
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:12-13
inductive NFn | zero | succ
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:16-17
inductive NRel | le
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:20-22
def NFn.arity : NFn → Nat
  | .zero => 0
  | .succ => 1
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:25
abbrev NSig : Sig := ⟨NFn, NRel, NFn.arity, fun _ => 2⟩
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:28-33
def natStr : Str NSig Nat where
  fn := fun f => match f with
    | .zero => fun _ => 0
    | .succ => fun a => a ⟨0, Nat.zero_lt_one⟩ + 1
  rel := fun r => match r with
    | .le => fun a => a ⟨0, by decide⟩ ≤ a ⟨1, by decide⟩
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:36-41
def natStr2 : Str NSig Nat where
  fn := fun f => match f with
    | .zero => fun _ => 0
    | .succ => fun a => a ⟨0, Nat.zero_lt_one⟩ + 2
  rel := fun r => match r with
    | .le => fun a => a ⟨0, by decide⟩ ≤ a ⟨1, by decide⟩
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:44
def tZero {n : Nat} : Term NSig n := .app NFn.zero (fun i => i.elim0)
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:47
def tSucc {n : Nat} (t : Term NSig n) : Term NSig n := .app NFn.succ (fun _ => t)
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:50
def dTwo : Defn NSig := .fn 0 (tSucc (tSucc tZero))
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:57
def tTwoNew : Term dTwo.sig 0 := .app (none : (NSig.addFn 0).Fn) (fun i => i.elim0)
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:60
def psiTwo : Sentence dTwo.sig := .eq tTwoNew ((tSucc (tSucc tZero)).map dTwo.incl)
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:200
def psiTwoRefl : Sentence dTwo.sig := .eq tTwoNew tTwoNew
```

```lean
-- lean/Toy/Extension/Transparency.lean:83
def pcModelTrue : Str (LP.addFn 0) Bool := (pStr (fun _ : Bool => True)).withFn (fun _ => true)
```

```lean
-- lean/Toy/Extension/Transparency.lean:86
def pcModelFalse : Str (LP.addFn 0) Bool := (pStr (fun _ : Bool => True)).withFn (fun _ => false)
```

```lean
-- lean/Toy/Extension/Converse.lean:146
def pN (x : Nat ⊕ Nat) : Prop := x.isLeft = true
```

```lean
-- lean/Toy/Extension/Converse.lean:150
def pM (x : Nat ⊕ (Nat → Bool)) : Prop := x.isLeft = true
```

```lean
-- lean/Toy/Extension/Converse.lean:153
def N0 : Str LP (Nat ⊕ Nat) := pStr pN
```

```lean
-- lean/Toy/Extension/Converse.lean:156
def M0 : Str LP (Nat ⊕ (Nat → Bool)) := pStr pM
```

```lean
-- lean/Toy/Extension/Converse.lean:187-188
def tF {n : Nat} (t : Term (LP.addFn 1) n) : Term (LP.addFn 1) n :=
  .app (none : (LP.addFn 1).Fn) (fun _ => t)
```

```lean
-- lean/Toy/Extension/Converse.lean:191-192
def atomP {n : Nat} (t : Term (LP.addFn 1) n) : Formula (LP.addFn 1) n :=
  .rel PRel.P (fun _ => t)
```

```lean
-- lean/Toy/Extension/Converse.lean:195-196
def injAx1 : Sentence (LP.addFn 1) :=
  .all (.imp (atomP (.var 0)).not (atomP (tF (.var 0))))
```

```lean
-- lean/Toy/Extension/Converse.lean:199-201
def injAx2 : Sentence (LP.addFn 1) :=
  .all (.all (.imp (atomP (.var 1)).not (.imp (atomP (.var 0)).not
    (.imp (.eq (tF (.var 1)) (tF (.var 0))) (.eq (.var 1) (.var 0))))))
```

```lean
-- lean/Toy/Extension/Converse.lean:204-205
def injTheory : Theory (LP.addFn 1) :=
  ((Theory.th N0).map (SigHom.inclFn LP 1)).union (Theory.ofList [injAx1, injAx2])
```

```lean
-- lean/Toy/Extension/ScopeExamples.lean:34-35
def singletonDefTheory : Theory (LP.addFn 0) :=
  Theory.ofList [fnDefiningSentence (L := LP) (k := 0) (.eq (.var 0) (.var 0))]
```

```lean
-- lean/Toy/Extension/ScopeExamples.lean:38
def atMostOneElt : Sentence LP := .all (.all (.eq (.var 0) (.var 1)))
```

```lean
-- lean/Toy/Extension/Elaboration.lean:217-221
def baseEnv : Env where
  defaults := [.nat]
  coercions := [(.int, .nat)]
  instances := [(.add, .nat, .add), (.add, .int, .add), (.sub, .nat, .subN),
    (.sub, .int, .subZ), (.div, .nat, .divT), (.div, .int, .divT)]
```

```lean
-- lean/Toy/Extension/Elaboration.lean:224
def envDefaultInt : Env := { baseEnv with defaults := .int :: baseEnv.defaults }
```

```lean
-- lean/Toy/Extension/Elaboration.lean:227
def envCoeNatInt : Env := { baseEnv with coercions := (.nat, .int) :: baseEnv.coercions }
```

```lean
-- lean/Toy/Extension/Elaboration.lean:230
def envDivE : Env := { baseEnv with instances := (.div, .int, .divE) :: baseEnv.instances }
```

```lean
-- lean/Toy/Extension/Elaboration.lean:233
def sDefault : Disp := .lt (.bin .sub (.num 0) (.num 1)) (.num 0)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:236
def sCoe : Disp := .lt (.bin .sub (.numAt 0 .nat) (.numAt 1 .nat)) (.numAt 0 .int)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:239-241
def sDiv : Disp :=
  .lt (.bin .add (.bin .div (.bin .sub (.numAt 0 .int) (.numAt 7 .int)) (.numAt 2 .int)) (.numAt 3 .int))
    (.numAt 0 .int)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:244
def sHarmless : Disp := .lt (.bin .sub (.numAt 1 .nat) (.numAt 0 .nat)) (.numAt 2 .int)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:327-330
def envNoCoe : Env where
  defaults := [.nat]
  coercions := []
  instances := baseEnv.instances
```

```lean
-- lean/Toy/Extension/Elaboration.lean:333
def envAddNatInt : Env := { envNoCoe with coercions := [(.nat, .int)] }
```

```lean
-- lean/Toy/Extension/Requirements.lean:110-111
inductive EnvRel | train | car
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Requirements.lean:114
abbrev LEnv : Sig := ⟨Empty, EnvRel, fun e => e.elim, fun _ => 0⟩
```

```lean
-- lean/Toy/Extension/Requirements.lean:118
abbrev LCross : Sig := LEnv.addRel 0
```

```lean
-- lean/Toy/Extension/Requirements.lean:121
def ιCross : SigHom LEnv LCross := SigHom.inclRel LEnv 0
```

```lean
-- lean/Toy/Extension/Requirements.lean:124
def trainIn : Sentence LEnv := .rel EnvRel.train (fun i => i.elim0)
```

```lean
-- lean/Toy/Extension/Requirements.lean:127
def carIn : Sentence LEnv := .rel EnvRel.car (fun i => i.elim0)
```

```lean
-- lean/Toy/Extension/Requirements.lean:130
def gateDown : Sentence LCross := .rel (none : LCross.Rel) (fun i => i.elim0)
```

```lean
-- lean/Toy/Extension/Requirements.lean:133
def noCollision : Sentence LEnv := (Formula.and trainIn carIn).not
```

```lean
-- lean/Toy/Extension/Requirements.lean:136-137
def specCross : Theory LCross :=
  Theory.ofList [.imp (trainIn.map ιCross) gateDown, .imp gateDown (carIn.map ιCross).not]
```

```lean
-- lean/Toy/Extension/Requirements.lean:273
abbrev propSig (P : Type) : Sig := ⟨Empty, P, fun e => e.elim, fun _ => 0⟩
```

```lean
-- lean/Toy/Extension/Requirements.lean:276-277
def propHom {P Q : Type} (f : P → Q) : SigHom (propSig P) (propSig Q) :=
  ⟨id, f, fun e => e.elim, fun _ => rfl⟩
```

```lean
-- lean/Toy/Extension/Requirements.lean:284
def atom {P : Type} (p : P) : Sentence (propSig P) := .rel p (fun i => i.elim0)
```

```lean
-- lean/Toy/Extension/Requirements.lean:315-316
inductive CEvA | train
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Requirements.lean:319-320
inductive CSA | train | gate
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Requirements.lean:324-325
inductive CWA | train | gate | car
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Requirements.lean:328-329
inductive CEnvA | train | car
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Requirements.lean:331-333
def ιVSA : SigHom (propSig CEvA) (propSig CSA) := propHom (fun | .train => .train)
def ιSWA : SigHom (propSig CSA) (propSig CWA) := propHom (fun | .train => .train | .gate => .gate)
def ιEWA : SigHom (propSig CEnvA) (propSig CWA) := propHom (fun | .train => .train | .car => .car)
```

```lean
-- lean/Toy/Extension/Requirements.lean:336-337
def domainA : Theory (propSig CWA) :=
  Theory.ofList [Formula.imp (atom CWA.gate) (atom CWA.car).not]
```

```lean
-- lean/Toy/Extension/Requirements.lean:340
def specA : Theory (propSig CSA) := Theory.ofList [Formula.imp (atom CSA.train) (atom CSA.gate)]
```

```lean
-- lean/Toy/Extension/Requirements.lean:343-344
def noCollisionE : Sentence (propSig CEnvA) :=
  (Formula.and (atom CEnvA.train) (atom CEnvA.car)).not
```

```lean
-- lean/Toy/Extension/Requirements.lean:412-413
inductive CEvB | train | car
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Requirements.lean:416-417
inductive CSB | train | car | gate
  deriving DecidableEq
```

```lean
-- lean/Toy/Extension/Requirements.lean:419-420
def ιVSB : SigHom (propSig CEvB) (propSig CSB) := propHom (fun | .train => .train | .car => .car)
def ιSWB : SigHom (propSig CSB) (propSig CSB) := propHom id
```

```lean
-- lean/Toy/Extension/Requirements.lean:424-425
def noCollisionEv : Sentence (propSig CEvB) :=
  (Formula.and (atom CEvB.train) (atom CEvB.car)).not
```

```lean
-- lean/Toy/Extension/Requirements.lean:428-430
def specB : Theory (propSig CSB) :=
  Theory.ofList [Formula.imp (atom CSB.train) (atom CSB.gate),
    Formula.imp (atom CSB.gate) (atom CSB.car).not]
```

## Findings

Each card gives the tier, kind and depth, the plain claim, the Lean statement quoted verbatim (signature up to `:=`), an unfolded rendering (checked to be definitionally equal to the statement, or labelled prose), the hypothesis ledger, the non-vacuity witness, positive controls where recorded, prior art, the design question, and the evidence basis. A hypothesis is *tight* when a proved counterexample satisfies all the other hypotheses and falsifies the conclusion; the class of that witness is recorded. Non-claims are under **Boundaries**.

### Definitional extensions and transparency

#### 1. `defext-expansions-eq-expand`

Tier T0 · kind: characterization · depth: shallow · Lean: `defExt_expansions_eq_expand`

**Plain claim.** For any theory T, any explicit definition d (a new k-ary function symbol defined by an old term, or a new k-ary relation symbol defined by an old formula) and any model S of T: the structures on S's carrier that keep S's old symbols and satisfy the definitional extension T + d are exactly one structure, the canonical expansion d.expand S.

**Statement.**

```lean
-- lean/Toy/Extension/Definitional.lean:265-267
theorem defExt_expansions_eq_expand (T : Theory L) (d : Defn L) (S : Str L α)
    (hS : S.ModelsTh T) :
    ∀ S' : Str d.sig α, (S'.reduct d.incl = S ∧ S'.ModelsTh (d.theory T)) ↔ S' = d.expand S
```

Unfolded statement of `defExt_expansions_eq_expand` (Defn.theory written out), after the binders T, d, S, hS:

```lean
∀ S' : Str d.sig α,
  (S'.reduct d.incl = S ∧ S'.ModelsTh ((T.map d.incl).union (Theory.ofList [d.defAxiom]))) ↔
    S' = d.expand S
```

**Hypothesis ledger.**

- `hS : S.ModelsTh T` — Gives that the canonical expansion satisfies the translated axioms of T. Tight; witness class: the inconsistent theory {falsum} over {zero, succ, le} with the standard structure on Nat, where the characterization fails at S' = d.expand S. (*tight: counterexample `defExt_expansions_eq_expand_ce_not_model`*)

**Non-vacuity.** The standard structure on Nat for {zero, succ, le}, the empty theory, and the definition two := succ (succ zero). (`defExt_expansions_eq_expand_nonvacuity`)

**Prior art.**

- Joseph R. Shoenfield, Mathematical Logic, Addison-Wesley, Reading MA, 1967, Section 4.6 'Extensions by definitions' (section title confirmed from the table of contents; page range approximately pp. 57-60, not visually confirmed). Treats extensions by definitions proof-theoretically over non-empty domains; the semantic statements here are not quoted from it.
- Wilfrid Hodges, A Shorter Model Theory, Cambridge University Press, 1997, ISBN 978-0-521-58713-6, Section 2.6 'Translations' (pp. 51-58, from the table of contents). General reference for reducts and expansions over non-empty structures; no exercise-level statement is claimed.

**Design question.** When a library adds an explicit definition, does each model of the old theory extend in exactly one way to a model of the extended theory?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 2. `defext-expansion-unique-of-axiom`

Tier T0 · kind: theorem · depth: shallow · Lean: `defExt_expansion_unique_of_axiom`

**Plain claim.** For any explicit definition d, any L-structure S and any structure S' of the extended language on the same carrier: if the reduct of S' to L is S and S' satisfies the defining axiom of d, then S' is the canonical expansion d.expand S. No theory T is involved.

**Statement.**

```lean
-- lean/Toy/Extension/Definitional.lean:224-226
theorem defExt_expansion_unique_of_axiom (d : Defn L) (S : Str L α) (S' : Str d.sig α)
    (hred : S'.reduct d.incl = S) (hax : S'.Models d.defAxiom) :
    S' = d.expand S
```

Unfolded (prose): what the hypothesis hax says.

```text
S'.Models d.defAxiom holds iff, for every argument tuple x̄ in the carrier,
  c(x̄) = e(x̄)      when d = Defn.fn k e   (a function symbol defined by a term), or
  c(x̄) ↔ e(x̄)      when d = Defn.rel k e  (a relation symbol defined by a formula),
where c is the new symbol as interpreted by S', and the old-language term or formula e is read along
the inclusion and evaluated in S' (equivalently, evaluated in the reduct of S').
```

**Hypothesis ledger.**

- `hred : S'.reduct d.incl = S` — Ties S' to S on the old symbols. Tight; witness class: {zero, succ, le} on Nat with the defined constant two, where the canonical expansion of the nonstandard structure natStr2 satisfies the defining axiom but is not the canonical expansion of natStr. (*tight: counterexample `defExt_expansion_unique_ce_reduct`*)
- `hax : S'.Models d.defAxiom` — Pins the new symbol to its definiens. Tight; witness class: {zero, succ, le} on Nat, interpreting two as 3. (*tight: counterexample `defExt_expansion_unique_ce_axiom`*)

**Non-vacuity.** The canonical expansion of the standard structure on Nat by two := succ (succ zero). (`defExt_axiom_nonvacuity`)

**Prior art.**

- Joseph R. Shoenfield, Mathematical Logic, Addison-Wesley, Reading MA, 1967, Section 4.6 'Extensions by definitions' (section title confirmed from the table of contents; page range approximately pp. 57-60, not visually confirmed). Treats extensions by definitions proof-theoretically over non-empty domains; the semantic statements here are not quoted from it.

**Design question.** Does the defining axiom of an explicit definition fix the meaning of the new symbol on every structure?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 3. `defext-conservative`

Tier T0 · kind: theorem · depth: shallow · Lean: `defExt_conservative`

**Plain claim.** For any theory T and any explicit definition d, the definitional extension T + d is conservative over T: every old-language sentence it entails is entailed by T.

**Statement.**

```lean
-- lean/Toy/Extension/Definitional.lean:280-281
theorem defExt_conservative (T : Theory L) (d : Defn L) :
    Conservative d.incl T (d.theory T)
```

Unfolded statement of `defExt_conservative` (Conservative and Entails written out), after the binders T, d:

```lean
∀ φ : Sentence L,
  (∀ (β : Type) (S : Str d.sig β), S.ModelsTh (d.theory T) → S.Models (φ.map d.incl)) →
    ∀ (β : Type) (S : Str L β), S.ModelsTh T → S.Models φ
```

**Hypothesis ledger.**

No hypotheses: the statement holds for every theory T and every explicit definition d.

**Non-vacuity.** The definitional extension of the empty {zero, succ, le}-theory by two := succ (succ zero) has a model. (`defExt_theory_has_model`)

**Prior art.**

- Joseph R. Shoenfield, Mathematical Logic, Addison-Wesley, Reading MA, 1967, Section 4.6 'Extensions by definitions' (section title confirmed from the table of contents; page range approximately pp. 57-60, not visually confirmed). Treats extensions by definitions proof-theoretically over non-empty domains; the semantic statements here are not quoted from it.
- Ondrej Kuncar and Andrei Popescu, 'Safety and Conservativity of Definitions in HOL and Isabelle/HOL', Proceedings of the ACM on Programming Languages 2(POPL), 2018, Article 24 (26 pages), DOI 10.1145/3158112 (proves safety and conservativity of definitions, including type definitions, for HOL and Isabelle/HOL; a counterpart for a real system, not formalized here).

**Design question.** When a library adds an explicit definition, can any old statement become provable that was not provable before?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Reading a non-recursive definition c := e in a proof assistant as Defn.theory (the definition adds its defining equation or equivalence) is the modeling step; under that reading the theorem says that such an addition entails no new old-vocabulary sentence. The reading covers explicit first-order definitions; it does not cover type definitions, recursive or overloaded definitions, or dependent typing (see the non-claims). Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean's kernel, Lean's elaborator, or any other proof assistant (for Isabelle/HOL, see Kunčar and Popescu 2018 under prior art).

#### 4. `defext-unfold-preserves-sat-iff-defining-axiom`

Tier T1 · kind: characterization · depth: substantive · Lean: `models_defAxiom_iff_unfold_preserves_sat`, `models_defAxiom_iff_deltaConv_sound`, `defExt_eliminable`

**Plain claim.** For any explicit definition d and any structure S' of the extended language, the following are equivalent: (i) S' satisfies the defining axiom of d; (ii) unfolding preserves truth in S': every formula of the extended language has, under every assignment, the same truth value in S' as its unfolding d.unfold (each occurrence of the new symbol replaced by its definiens, read back along the inclusion); (iii) delta-conversion for d is sound in S': any two formulas whose unfoldings coincide have the same truth value in S' under every assignment. Moreover, for every theory T and formula psi, the definitional extension T + d entails the universal closure of psi <-> unfold psi.

**Statement.**

```lean
-- lean/Toy/Extension/Definitional.lean:523-526
theorem models_defAxiom_iff_unfold_preserves_sat (d : Defn L) (S' : Str d.sig α) :
    S'.Models d.defAxiom ↔
      ∀ {n : Nat} (ψ : Formula d.sig n) (v : Fin n → α),
        Sat S' v ψ ↔ Sat S' v ((d.unfold ψ).map d.incl)
```

```lean
-- lean/Toy/Extension/Definitional.lean:534-537
theorem models_defAxiom_iff_deltaConv_sound (d : Defn L) (S' : Str d.sig α) :
    S'.Models d.defAxiom ↔
      ∀ {n : Nat} (φ ψ : Formula d.sig n), d.DeltaConv φ ψ →
        ∀ v : Fin n → α, (Sat S' v φ ↔ Sat S' v ψ)
```

```lean
-- lean/Toy/Extension/Definitional.lean:393-394
theorem defExt_eliminable (T : Theory L) (d : Defn L) {n : Nat} (ψ : Formula d.sig n) :
    Entails (d.theory T) (Formula.closeAll n (ψ.iff ((d.unfold ψ).map d.incl)))
```

Unfolded statement of `models_defAxiom_iff_deltaConv_sound` (Defn.DeltaConv written out), after the binders d, S':

```lean
S'.Models d.defAxiom ↔
  ∀ {n : Nat} (φ ψ : Formula d.sig n), d.unfold φ = d.unfold ψ →
    ∀ v : Fin n → α, (Sat S' v φ ↔ Sat S' v ψ)
```

**Hypothesis ledger.**

No hypotheses: `models_defAxiom_iff_unfold_preserves_sat` and `models_defAxiom_iff_deltaConv_sound` are equivalences stated for every explicit definition d and every structure S' of the extended language; `defExt_eliminable` holds for every theory T, explicit definition d and formula ψ of the extended language.

**Non-vacuity.** Both sides hold for the canonical expansion of the standard structure on Nat by two := succ (succ zero) (defExt_axiom_nonvacuity); both sides fail when two is interpreted as 3 (dTwo_three_not_models_defAxiom, defExt_unfold_equiv_ce_axiom, dTwo_deltaConv_sound_and_unsound); two convertible but different sentences are exhibited in dTwo_deltaConv_examples. (`defExt_axiom_nonvacuity`)

**Prior art.**

- Joseph R. Shoenfield, Mathematical Logic, Addison-Wesley, Reading MA, 1967, Section 4.6 'Extensions by definitions' (section title confirmed from the table of contents; page range approximately pp. 57-60, not visually confirmed). Treats extensions by definitions proof-theoretically over non-empty domains; the semantic statements here are not quoted from it.
- The Lean Language Reference, leanprover/reference-manual tag v4.34.0 (commit a6451f0647eb4dc46fce2dd0532331c59351f87c), Manual/Defs.lean: in the kernel a defined constant 'may be replaced via delta-reduction with the term that it stands for', and in the elaborator 'this replacement is governed by the constant's reducibility' (lines 489-490); 'Opaque constants are defined constants that are not subject to delta-reduction in the kernel' and 'can only be used for types that are inhabited' (lines 554-556). Cited for context; Lean's kernel is not formalized here.

**Design question.** When may a checker see through a defined name to its body (unfold it, or identify terms up to unfolding) without changing the meaning of any statement?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Reading a checker that identifies terms up to unfolding of a defined name as Defn.DeltaConv for that name is the modeling step; under that reading, the characterization says that such identification is sound in exactly the structures satisfying the defining axiom. Reading kernel delta-reduction in a dependent type theory as this first-order conversion is an analogy. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean's kernel delta-reduction or reducibility settings.

#### 5. `explicit-definability-implies-unique-expansion`

Tier T0 · kind: theorem · depth: shallow · Lean: `fnExplicitlyDefinable_expansion_unique`

**Plain claim.** For a theory T' over L plus one new k-ary function symbol c: if c is explicitly definable in T' (FnExplicitlyDefinable T': some old-language formula theta(y, x) satisfies T' |= forall y x, (c(x) = y <-> theta(y, x))), then any two models S1, S2 of T' on the same carrier whose reducts to L coincide are equal.

**Statement.**

```lean
-- lean/Toy/Extension/Transparency.lean:43-47
theorem fnExplicitlyDefinable_expansion_unique {k : Nat} (T' : Theory (L.addFn k))
    (hdef : FnExplicitlyDefinable T') {β : Type} (S₁ S₂ : Str (L.addFn k) β)
    (h₁ : S₁.ModelsTh T') (h₂ : S₂.ModelsTh T')
    (hred : S₁.reduct (SigHom.inclFn L k) = S₂.reduct (SigHom.inclFn L k)) :
    S₁ = S₂
```

Unfolded statement of `fnExplicitlyDefinable_expansion_unique` (FnExplicitlyDefinable written out), after the binder T':

```lean
(∃ θ : Formula L (k + 1), Entails T' (fnDefiningSentence θ)) →
  ∀ {β : Type} (S₁ S₂ : Str (L.addFn k) β), S₁.ModelsTh T' → S₂.ModelsTh T' →
    S₁.reduct (SigHom.inclFn L k) = S₂.reduct (SigHom.inclFn L k) → S₁ = S₂
```

**Hypothesis ledger.**

- `hdef : FnExplicitlyDefinable T'` — The substantive hypothesis: transparency of c, modeled as explicit definability. Tight; witness class: the language {P} plus a fresh constant c with the single axiom P c, on Bool with P everywhere true, where c = true and c = false are two models with the same reduct. (*tight: counterexample `axPc_two_lawful_interpretations`*)
- `h₁ : S₁.ModelsTh T'` — Assumes S1 is a model of T'. Tight; witness class: {zero, succ, le} on Nat with the definitional extension by two, S1 the expansion interpreting two as 3 and S2 the canonical expansion (the counterexample records both orders). (*tight: counterexample `fnExplicitlyDefinable_expansion_unique_ce_model`*)
- `h₂ : S₂.ModelsTh T'` — Assumes S2 is a model of T'. Tight; same witness class with the roles of S1 and S2 exchanged. (*tight: counterexample `fnExplicitlyDefinable_expansion_unique_ce_model`*)
- `hred : S₁.reduct (SigHom.inclFn L k) = S₂.reduct (SigHom.inclFn L k)` — Assumes the two models agree on the old symbols. Tight; witness class: {zero, succ, le} on Nat with the definitional extension by two, comparing the canonical expansions of natStr and natStr2. (*tight: counterexample `fnExplicitlyDefinable_expansion_unique_ce_reduct`*)

**Non-vacuity.** The definitional extension of the empty {zero, succ, le}-theory by two is explicitly definable and has a model (take S1 = S2 that model). (`fnExplicitlyDefinable_nonvacuity`)

**Prior art.**

- Alessandro Padoa, 'Essai d'une theorie algebrique des nombres entiers, precede d'une introduction logique a une theorie deductive quelconque', Bibliotheque du Congres International de Philosophie, vol. 3, Paris, 1901, pp. 309-365 (bibliographic data from a secondary bibliography; the two-model method for showing that a primitive is not definable from the others is attributed to this paper in the literature on Beth's theorem).
- E. W. Beth, 'On Padoa's method in the theory of definition', Proceedings KNAW Series A 56 = Indagationes Mathematicae 15 (1953), pp. 330-339, DOI 10.1016/S1385-7258(53)50042-3 (the converse direction, implicit definability implies explicit definability, is Beth's definability theorem; not proved here).

**Design question.** Can a symbol that a library characterizes by lemmas, without a definition, be read as an abbreviation of some old-language definiens, that is, is its name transparent?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Reading 'the name is transparent' as FnExplicitlyDefinable (the symbol can be replaced by an old-language definiens) is a modeling choice; the theorem then says that any two models of T' that agree on the old symbols (same carrier) interpret a transparent function symbol identically. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean's kernel, Lean's elaborator, or any other proof assistant.

### Axiomatic extensions

#### 6. `expansion-property-implies-conservative`

Tier T0 · kind: theorem · depth: shallow · Lean: `expansionProperty_implies_conservative`

**Plain claim.** For any signature morphism iota : L -> L', theory T over L and theory T' over L': if every model of T expands (same carrier, old symbols read through iota unchanged) to a model of T', then T' is conservative over T along iota.

**Statement.**

```lean
-- lean/Toy/Extension/Axiomatic.lean:59-61
theorem expansionProperty_implies_conservative {L L' : Sig} (ι : SigHom L L')
    (T : Theory L) (T' : Theory L') (hexp : ExpansionProperty ι T T') :
    Conservative ι T T'
```

Unfolded statement of `expansionProperty_implies_conservative` (ExpansionProperty and Conservative written out), after the binders ι, T, T':

```lean
(∀ (β : Type) (S : Str L β), S.ModelsTh T → ∃ S' : Str L' β, S'.reduct ι = S ∧ S'.ModelsTh T') →
  ∀ φ : Sentence L, Entails T' (φ.map ι) → Entails T φ
```

**Hypothesis ledger.**

- `hexp : ExpansionProperty ι T T'` — Assumes every model of T expands. Tight; witness class: the language {P} plus a fresh constant c with the axiom P c over the empty theory (a one-point countermodel). (*tight: counterexample `expansionProperty_implies_conservative_ce`*)

**Non-vacuity.** Adding a fresh 0-ary relation symbol with no axioms to the empty {P}-theory has the expansion property. (`expansionProperty_nonvacuity`)

**Prior art.**

- Wilfrid Hodges, A Shorter Model Theory, Cambridge University Press, 1997, ISBN 978-0-521-58713-6, Section 2.6 'Translations' (pp. 51-58, from the table of contents). General reference for reducts and expansions over non-empty structures; no exercise-level statement is claimed.

**Design question.** Is showing that every model of the old theory expands enough to establish that an extension is conservative?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 7. `axiom-p-c-not-conservative`

Tier T0 · kind: counterexample · depth: shallow · Lean: `axiom_P_c_not_conservative`

**Plain claim.** Over the language {P} with one unary predicate, the axiomatic extension of the empty theory by a fresh constant c with the single axiom P c entails the old-language sentence exists x, P x, which the empty theory does not entail; hence the extension is not conservative and does not have the expansion property.

**Statement.**

```lean
-- lean/Toy/Extension/Axiomatic.lean:72-76
theorem axiom_P_c_not_conservative :
    Entails (Theory.ofList [axPc]) (existsP.map (SigHom.inclFn LP 0)) ∧
    ¬ Entails (Theory.empty : Theory LP) existsP ∧
    ¬ Conservative (SigHom.inclFn LP 0) Theory.empty (Theory.ofList [axPc]) ∧
    ¬ ExpansionProperty (SigHom.inclFn LP 0) Theory.empty (Theory.ofList [axPc])
```

Unfolded statement of `axiom_P_c_not_conservative` (Conservative and ExpansionProperty written out):

```lean
Entails (Theory.ofList [axPc]) (existsP.map (SigHom.inclFn LP 0)) ∧
¬ Entails (Theory.empty : Theory LP) existsP ∧
¬ (∀ φ : Sentence LP, Entails (Theory.ofList [axPc]) (φ.map (SigHom.inclFn LP 0)) →
    Entails (Theory.empty : Theory LP) φ) ∧
¬ (∀ (β : Type) (S : Str LP β), S.ModelsTh (Theory.empty : Theory LP) →
    ∃ S' : Str (LP.addFn 0) β, S'.reduct (SigHom.inclFn LP 0) = S ∧ S'.ModelsTh (Theory.ofList [axPc]))
```

**Hypothesis ledger.**

No hypotheses: the statement is a closed proposition about the concrete language LP, the sentence axPc and the sentence existsP.

**Non-vacuity.** Concrete instance (no hypotheses).

**Prior art.**

- Standard textbook-style example; no specific source is claimed.
- The Lean Language Reference, leanprover/reference-manual tag v4.34.0 (commit a6451f0647eb4dc46fce2dd0532331c59351f87c), Manual/Defs.lean: in the kernel a defined constant 'may be replaced via delta-reduction with the term that it stands for', and in the elaborator 'this replacement is governed by the constant's reducibility' (lines 489-490); 'Opaque constants are defined constants that are not subject to delta-reduction in the kernel' and 'can only be used for types that are inhabited' (lines 554-556). Cited for context; Lean's kernel is not formalized here.

**Design question.** Can characterizing a new constant by an axiom change what is true of the old vocabulary?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Reading an axiom about a freshly declared library symbol as the axiomatic extension modeled here (an unchecked first-order axiom) is the modeling step; under that reading the theorem shows that such an axiom can add old-vocabulary consequences. The comparison with Lean's opaque declarations and @[irreducible] definitions is informal (see the non-claims). Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean's opaque or @[irreducible] declarations.

#### 8. `fresh-constant-not-conservative-with-empty-carriers`

Tier T1 · kind: counterexample · depth: shallow · Lean: `fresh_constant_not_conservative_with_empty_carriers`

**Plain claim.** With carriers allowed to be empty, over the language {P} (which has no closed terms), adding one fresh constant with no axioms to the empty theory is not conservative: the extension entails exists x, x = x, and the empty theory does not.

**Statement.**

```lean
-- lean/Toy/Extension/Axiomatic.lean:115-118
theorem fresh_constant_not_conservative_with_empty_carriers :
    Entails (Theory.empty : Theory (LP.addFn 0)) (existsEq.map (SigHom.inclFn LP 0)) ∧
    ¬ Entails (Theory.empty : Theory LP) existsEq ∧
    ¬ Conservative (SigHom.inclFn LP 0) Theory.empty Theory.empty
```

Unfolded statement of `fresh_constant_not_conservative_with_empty_carriers` (Conservative written out):

```lean
Entails (Theory.empty : Theory (LP.addFn 0)) (existsEq.map (SigHom.inclFn LP 0)) ∧
¬ Entails (Theory.empty : Theory LP) existsEq ∧
¬ (∀ φ : Sentence LP, Entails (Theory.empty : Theory (LP.addFn 0)) (φ.map (SigHom.inclFn LP 0)) →
    Entails (Theory.empty : Theory LP) φ)
```

**Hypothesis ledger.**

No hypotheses: the statement is a closed proposition about the concrete language LP, its extension LP.addFn 0 by one constant, and the sentence existsEq.

**Non-vacuity.** Concrete instance (no hypotheses).

**Prior art.**

- Andrzej Mostowski, 'On the rules of proof in the pure functional calculus of the first order', Journal of Symbolic Logic 16(2):107-111, 1951, DOI 10.2307/2266682, and Theodore Hailperin, 'Quantification theory and empty individual-domains', Journal of Symbolic Logic 18(3):197-200, 1953, DOI 10.2307/2267402 (first-order logic over possibly empty domains; background for the empty-carrier phenomenon; the conservativity statement here is not quoted from them).
- The Lean Language Reference, leanprover/reference-manual tag v4.34.0 (commit a6451f0647eb4dc46fce2dd0532331c59351f87c), Manual/Defs.lean: in the kernel a defined constant 'may be replaced via delta-reduction with the term that it stands for', and in the elaborator 'this replacement is governed by the constant's reducibility' (lines 489-490); 'Opaque constants are defined constants that are not subject to delta-reduction in the kernel' and 'can only be used for types that are inhabited' (lines 554-556). Cited for context; Lean's kernel is not formalized here.

**Design question.** Is declaring a new constant without axioms always harmless when carriers may be empty?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Lean requires opaque constants to have inhabited types (Lean Language Reference, Manual/Defs.lean lines 554-556). The theorem gives a first-order reason why a declared constant can carry content when carriers may be empty; the link to the inhabitation requirement is an analogy. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean's opaque declarations.

#### 9. `conservative-not-implies-expansion-property`

Tier T1 · kind: counterexample · depth: substantive · Lean: `conservative_not_implies_expansionProperty`

**Plain claim.** Conservativity does not imply the expansion property: for T = Th(N0), the complete theory of (Nat + Nat, P = left), and T' = T plus 'the new unary function f maps the complement of P injectively into P', T' is conservative over T but does not have the expansion property; the model M0 = (Nat + (Nat -> Bool), P = left) of T has no expansion to a model of T'.

**Statement.**

```lean
-- lean/Toy/Extension/Converse.lean:296-301
theorem conservative_not_implies_expansionProperty :
    Conservative (SigHom.inclFn LP 1) (Theory.th N0) injTheory ∧
    ¬ ExpansionProperty (SigHom.inclFn LP 1) (Theory.th N0) injTheory ∧
    M0.ModelsTh (Theory.th N0) ∧
    ¬ ∃ S' : Str (LP.addFn 1) (Nat ⊕ (Nat → Bool)),
        S'.reduct (SigHom.inclFn LP 1) = M0 ∧ S'.ModelsTh injTheory
```

Unfolded statement of `conservative_not_implies_expansionProperty` (Conservative and ExpansionProperty written out):

```lean
(∀ φ : Sentence LP, Entails injTheory (φ.map (SigHom.inclFn LP 1)) → Entails (Theory.th N0) φ) ∧
¬ (∀ (β : Type) (S : Str LP β), S.ModelsTh (Theory.th N0) →
    ∃ S' : Str (LP.addFn 1) β, S'.reduct (SigHom.inclFn LP 1) = S ∧ S'.ModelsTh injTheory) ∧
M0.ModelsTh (Theory.th N0) ∧
¬ ∃ S' : Str (LP.addFn 1) (Nat ⊕ (Nat → Bool)),
    S'.reduct (SigHom.inclFn LP 1) = M0 ∧ S'.ModelsTh injTheory
```

**Hypothesis ledger.**

No hypotheses: the statement is a closed proposition about the concrete theories Theory.th N0 and injTheory and the structure M0.

**Non-vacuity.** Concrete instance (no hypotheses).

**Prior art.**

- Classical back-and-forth technique and Cantor's diagonal argument; no source for this exact countermodel was verified, so none is claimed.
- Wilfrid Hodges, A Shorter Model Theory, Cambridge University Press, 1997, ISBN 978-0-521-58713-6, Section 2.6 'Translations' (pp. 51-58, from the table of contents). General reference for reducts and expansions over non-empty structures; no exercise-level statement is claimed.

**Design question.** Is conservativity of a specification enough to guarantee that every intended model can be extended to interpret the new symbols?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 10. `axext-entails-iff-lawful-interpretations`

Tier T0 · kind: characterization · depth: definitional · Lean: `axExt_entails_iff_lawful_interpretations`

**Plain claim.** For a theory T over L, axioms A over L plus one new k-ary function symbol, and a sentence psi of the extended language: T + A entails psi iff psi holds in S.withFn g for every model S of T (any carrier in Type) and every interpretation g of the new symbol for which S.withFn g satisfies A.

**Statement.**

```lean
-- lean/Toy/Extension/Axiomatic.lean:197-201
theorem axExt_entails_iff_lawful_interpretations {L : Sig} {k : Nat}
    (T : Theory L) (A : Theory (L.addFn k)) (ψ : Sentence (L.addFn k)) :
    Entails ((T.map (SigHom.inclFn L k)).union A) ψ ↔
      ∀ (β : Type) (S : Str L β), S.ModelsTh T →
        ∀ g : (Fin k → β) → β, (S.withFn g).ModelsTh A → (S.withFn g).Models ψ
```

Unfolded statement of `axExt_entails_iff_lawful_interpretations` (Entails written out on the left), after the binders T, A, ψ:

```lean
(∀ (β : Type) (S' : Str (L.addFn k) β), S'.ModelsTh ((T.map (SigHom.inclFn L k)).union A) → S'.Models ψ) ↔
  ∀ (β : Type) (S : Str L β), S.ModelsTh T →
    ∀ g : (Fin k → β) → β, (S.withFn g).ModelsTh A → (S.withFn g).Models ψ
```

**Hypothesis ledger.**

No hypotheses: the equivalence holds for every signature L, arity k, theory T over L, axiom set A over L.addFn k and sentence ψ of the extended language.

**Non-vacuity.** The axiom P c has a lawful interpretation (one point, P true, c that point). (`axExt_lawful_interpretation_exists`)

**Prior art.**

- Standard model-theoretic (loose) semantics of axiomatized symbols; no specific source is claimed.
- Wilfrid Hodges, A Shorter Model Theory, Cambridge University Press, 1997, ISBN 978-0-521-58713-6, Section 2.6 'Translations' (pp. 51-58, from the table of contents). General reference for reducts and expansions over non-empty structures; no exercise-level statement is claimed.

**Design question.** What may a reader conclude about a symbol that a library characterizes by axioms and no definition?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

### Loose specifications of a function

#### 11. `weak-sort-spec-admits-natsort-and-weirdsort`

Tier T0 · kind: counterexample · depth: shallow · Lean: `weakSortSpec_admits_natSort_and_weirdSort`

**Plain claim.** The characterization WeakSortSpec of a function List Nat -> List Nat ('for every list, the output is sorted by <= and has the input's length') is satisfied by merge sort natSort and by weirdSort = (l |-> replicate (length l) 0); these two functions differ, so WeakSortSpec has more than one lawful interpretation (not AtMostOneLawful WeakSortSpec).

**Statement.**

```lean
-- lean/Toy/Extension/LooseSpec.lean:92-94
theorem weakSortSpec_admits_natSort_and_weirdSort :
    WeakSortSpec natSort ∧ WeakSortSpec weirdSort ∧ natSort ≠ weirdSort ∧
    ¬ AtMostOneLawful WeakSortSpec
```

Unfolded statement of `weakSortSpec_admits_natSort_and_weirdSort` (AtMostOneLawful written out):

```lean
WeakSortSpec natSort ∧ WeakSortSpec weirdSort ∧ natSort ≠ weirdSort ∧
  ¬ ∀ f g : List Nat → List Nat, WeakSortSpec f → WeakSortSpec g → f = g
```

**Hypothesis ledger.**

No hypotheses: the statement is a closed proposition about natSort, weirdSort and WeakSortSpec.

**Non-vacuity.** Concrete instance (no hypotheses).

**Prior art.**

- Alessandro Padoa, 'Essai d'une theorie algebrique des nombres entiers, precede d'une introduction logique a une theorie deductive quelconque', Bibliotheque du Congres International de Philosophie, vol. 3, Paris, 1901, pp. 309-365 (bibliographic data from a secondary bibliography; the two-model method for showing that a primitive is not definable from the others is attributed to this paper in the literature on Beth's theorem).
- E. W. Beth, 'On Padoa's method in the theory of definition', Proceedings KNAW Series A 56 = Indagationes Mathematicae 15 (1953), pp. 330-339, DOI 10.1016/S1385-7258(53)50042-3 (the converse direction, implicit definability implies explicit definability, is Beth's definability theorem; not proved here).

**Design question.** Can a function characterized by plausible lemmas still mean something its name does not promise?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 12. `strong-sort-spec-determines-natsort`

Tier T0 · kind: characterization · depth: shallow · Lean: `strongSortSpec_iff_eq_natSort`, `strongSortSpec_determines`

**Plain claim.** A function f : List Nat -> List Nat satisfies StrongSortSpec ('for every list, the output is sorted by <= and is a permutation of the input') iff f = natSort (merge sort). In particular StrongSortSpec determines a function: it has a lawful interpretation, and at most one.

**Statement.**

```lean
-- lean/Toy/Extension/LooseSpec.lean:114-115
theorem strongSortSpec_iff_eq_natSort (f : List Nat → List Nat) :
    StrongSortSpec f ↔ f = natSort
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:124
theorem strongSortSpec_determines : Determines StrongSortSpec
```

Unfolded statement of `strongSortSpec_determines` (Determines, AtMostOneLawful and the existence part written out):

```lean
(∃ f : List Nat → List Nat, ∀ l, List.Pairwise (· ≤ ·) (f l) ∧ (f l).Perm l) ∧
  ∀ f g : List Nat → List Nat, StrongSortSpec f → StrongSortSpec g → f = g
```

**Hypothesis ledger.**

No hypotheses: `strongSortSpec_iff_eq_natSort` holds for every function f : List Nat → List Nat, and `strongSortSpec_determines` is a closed proposition about StrongSortSpec.

**Non-vacuity.** Merge sort satisfies StrongSortSpec. (`natSort_strongSortSpec`)

**Prior art.**

- Lean 4 core v4.34.1, Init/Data/List/Perm.lean line 530, theorem List.Perm.eq_of_pairwise: two lists sorted by a relation that is antisymmetric on their elements and permutations of each other are equal (used in the proof).

**Design question.** Which characterization of a sorting function leaves no room for unintended lawful interpretations?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

### Finite examples as certificates

#### 13. `label-deciders-agree-on-examples-one-misses-spec`

Tier T0 · kind: theorem · depth: shallow · Lean: `label_deciders_agree_on_examples_one_misses_spec`

**Plain claim.** For any type a with decidable equality, intended predicate Spec, lists Pos and Neg with correct labels (every element of Pos satisfies Spec and no element of Neg does) and point x0 outside Pos ++ Neg: the two deciders memDecider Pos ('x is in Pos') and memDecider (x0 :: Pos) ('x is x0 or in Pos') both agree with Spec on every example, and at least one of them does not decide Spec.

**Statement.**

```lean
-- lean/Toy/Extension/FiniteExamples.lean:85-90
theorem label_deciders_agree_on_examples_one_misses_spec [DecidableEq α]
    (Spec : α → Prop) (Pos Neg : List α) (hlab : LabelsCorrect Spec Pos Neg)
    (x₀ : α) (hx₀ : x₀ ∉ Pos ++ Neg) :
    AgreesOn (memDecider Pos) Spec (Pos ++ Neg) ∧
    AgreesOn (memDecider (x₀ :: Pos)) Spec (Pos ++ Neg) ∧
    (¬ Decides (memDecider Pos) Spec ∨ ¬ Decides (memDecider (x₀ :: Pos)) Spec)
```

Unfolded conclusion of `label_deciders_agree_on_examples_one_misses_spec` (AgreesOn and Decides written out), after all binders:

```lean
(∀ x ∈ Pos ++ Neg, (memDecider Pos x = true ↔ Spec x)) ∧
(∀ x ∈ Pos ++ Neg, (memDecider (x₀ :: Pos) x = true ↔ Spec x)) ∧
(¬ (∀ x, (memDecider Pos x = true ↔ Spec x)) ∨ ¬ (∀ x, (memDecider (x₀ :: Pos) x = true ↔ Spec x)))
```

**Hypothesis ledger.**

- `[DecidableEq α]` — Used to form memDecider (decide (x in l)). The deciders are built from the lists and this instance without consulting Spec; they are executable when the supplied instance is computable. Every type has a classical instance, so the hypothesis restricts nothing. (*harmless*)
- `hlab : LabelsCorrect Spec Pos Neg` — Used to show that memDecider Pos agrees with Spec on the examples. Tight; witness class: Bool with one mislabeled positive example (Spec = (. = true), Pos = [false], Neg = [], x0 = true). The conclusion can also hold when this hypothesis fails: on Nat with Spec = (. = 0), Pos = Neg = [0] and x0 = 1 the labels are incorrect and the conclusion holds (label_deciders_conclusion_without_hypotheses). (*tight: counterexample `label_deciders_ce_labels`*)
- `hx₀ : x₀ ∉ Pos ++ Neg` — Used to make the two deciders differ at x0. Tight; witness class: Bool exhausted by the examples (Spec = (. = true), Pos = [true], Neg = [false], x0 = true), where both deciders decide Spec. The conclusion can also hold when this hypothesis fails: on Nat with Spec = True, Pos = [0], Neg = [] and x0 = 0 the conclusion holds (label_deciders_conclusion_without_hypotheses). (*tight: counterexample `label_deciders_ce_point`*)

**Non-vacuity.** Nat, Spec = even, Pos = [0, 2], Neg = [1], x0 = 4. (`label_deciders_nonvacuity`)

**Prior art.**

- Tom M. Mitchell, Machine Learning, McGraw-Hill, 1997, Section 2.7.2 'An Unbiased Learner' (pp. 40-41: with the power set of the instances as hypothesis space, 'each unobserved instance will be classified positive by precisely half the hypotheses in the version space') and Section 2.7.3 'The Futility of Bias-Free Learning' (p. 42).

**Design question.** Can a finite set of positive and negative examples certify that a definition means what its name says?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Reading a finite suite of labeled tests for a Boolean-valued library definition as AgreesOn over the listed examples is the modeling step; under that reading the theorem exhibits two label-built deciders that pass every such test while one of them is wrong somewhere. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about any particular test suite or testing tool.

#### 14. `unrestricted-decider-not-certified-by-finite-examples`

Tier T0 · kind: impossibility · depth: shallow · Lean: `unrestricted_decider_not_certified_by_finite_examples_of_infinite`

**Plain claim.** For any infinite type a (no finite list contains every element), any intended predicate Spec on a and any finite example list E: some function d : a -> Bool, drawn from the unrestricted class of all Boolean-valued functions, agrees with Spec on E but does not decide Spec.

**Statement.**

```lean
-- lean/Toy/Extension/FiniteExamples.lean:118-120
theorem unrestricted_decider_not_certified_by_finite_examples_of_infinite
    (hinf : InfiniteType α) (Spec : α → Prop) (E : List α) :
    ∃ d : α → Bool, AgreesOn d Spec E ∧ ¬ Decides d Spec
```

Unfolded conclusion of `unrestricted_decider_not_certified_by_finite_examples_of_infinite` (AgreesOn and Decides written out), after all binders:

```lean
∃ d : α → Bool, (∀ x ∈ E, (d x = true ↔ Spec x)) ∧ ¬ ∀ x, (d x = true ↔ Spec x)
```

**Hypothesis ledger.**

- `hinf : InfiniteType α` — Provides a point outside the examples where d can deviate. Tight; witness class: the finite type Bool with the exhaustive example list [true, false], where every decider agreeing on the examples decides Spec. (*tight: counterexample `unrestricted_decider_not_certified_ce_finite`*)

**Non-vacuity.** Nat is infinite. (`unrestricted_decider_not_certified_nonvacuity`)

**Positive control.** Nearby settings where agreement on finitely many examples does imply Decides: a restricted candidate class on Nat (threshold deciders, two examples k - 1 and k; `threshold_examples_certify`), a domain exhausted by the examples (`exhaustive_examples_certify`), and an equivalence theorem against a reference that matches Spec (`reference_equivalence_certifies`).

**Prior art.**

- Tom M. Mitchell, Machine Learning, McGraw-Hill, 1997, Section 2.7.2 'An Unbiased Learner' (pp. 40-41: with the power set of the instances as hypothesis space, 'each unobserved instance will be classified positive by precisely half the hypotheses in the version space') and Section 2.7.3 'The Futility of Bias-Free Learning' (p. 42).
- Sally A. Goldman and Michael J. Kearns, 'On the Complexity of Teaching', Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003 (defines the teaching dimension of a concept class, the number of labeled examples needed to single out a concept within that class; context for the restricted-class positive control; it does not state the unrestricted infinite-domain impossibility).

**Design question.** Can a finite set of positive and negative examples certify that a definition means what its name says?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Reading a test suite that checks a candidate definition against finitely many labeled examples as AgreesOn is the modeling step; under that reading the theorem says that, over an infinite input type and with no restriction on the candidate, passing the suite does not imply Decides. Restricted candidate classes behave differently (threshold_examples_certify). Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about any particular test suite or testing tool.

### Conditional adequacy of a cheap definition of sorted

#### 15. `adjrel-iff-pairwise-on-all-lists-iff-transitive`

Tier T0 · kind: characterization · depth: shallow · Lean: `adjRel_iff_pairwise_on_all_lists_iff_transitive`

**Plain claim.** For any relation r on a type a: 'adjacent elements are related' (AdjRel r l) and 'every earlier element is related to every later one' (List.Pairwise r l) agree on every list l iff r is transitive.

**Statement.**

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:112-113
theorem adjRel_iff_pairwise_on_all_lists_iff_transitive (r : α → α → Prop) :
    (∀ l : List α, AdjRel r l ↔ List.Pairwise r l) ↔ TransitiveRel r
```

Unfolded statement of `adjRel_iff_pairwise_on_all_lists_iff_transitive` (TransitiveRel written out), after the binder r:

```lean
(∀ l : List α, AdjRel r l ↔ List.Pairwise r l) ↔ ∀ a b c, r a b → r b c → r a c
```

**Hypothesis ledger.**

No hypotheses: the equivalence holds for every type α and every relation r on α.

**Non-vacuity.** <= on Nat is transitive and the two readings agree on [1, 2, 2, 3]. (`sorted_readings_nonvacuity`)

**Prior art.**

- leanprover-community/batteries, tag v4.29.0 (commit 756e3321fd3b02a85ffda19fef789916223e578c), Batteries/Data/List/Lemmas.lean line 423: theorem List.isChain_iff_pairwise [Trans R R R] : IsChain R l <-> Pairwise R l (under global transitivity).
- Rocq standard library, rocq-prover/stdlib tag V9.2.0, theories/Sorting/Sorted.v lines 135-136: Lemma Sorted_StronglySorted : Transitive R -> forall l, Sorted l -> StronglySorted l.

**Design question.** When does the cheap definition of 'sorted' (adjacent pairs) mean what the name promises (all pairs)?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 16. `adjrel-iff-pairwise-of-transon`

Tier T0 · kind: theorem · depth: shallow · Lean: `adjRel_iff_pairwise_of_transOn`

**Plain claim.** For any relation r and list l: if r is transitive on the elements of l (TransOn r l), then AdjRel r l holds iff List.Pairwise r l holds.

**Statement.**

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:106-107
theorem adjRel_iff_pairwise_of_transOn (r : α → α → Prop) (l : List α) (htr : TransOn r l) :
    AdjRel r l ↔ List.Pairwise r l
```

Unfolded statement of `adjRel_iff_pairwise_of_transOn` (TransOn written out), after the binders r, l:

```lean
(∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, r a b → r b c → r a c) → (AdjRel r l ↔ List.Pairwise r l)
```

**Hypothesis ledger.**

- `htr : TransOn r l` — Lets adjacent relatedness propagate along the list. Tight; witness class: r = (!=) on Nat with the three-element list [0, 1, 0]. (*tight: counterexample `adjRel_ne_not_pairwise`*)

**Non-vacuity.** <= on Nat is transitive on [1, 2, 2, 3]. (`sorted_readings_nonvacuity`)

**Prior art.**

- leanprover-community/batteries, tag v4.29.0 (commit 756e3321fd3b02a85ffda19fef789916223e578c), Batteries/Data/List/Lemmas.lean line 423: theorem List.isChain_iff_pairwise [Trans R R R] : IsChain R l <-> Pairwise R l (under global transitivity).
- Rocq standard library, rocq-prover/stdlib tag V9.2.0, theories/Sorting/Sorted.v lines 135-136: Lemma Sorted_StronglySorted : Transitive R -> forall l, Sorted l -> StronglySorted l.

**Design question.** When does the cheap definition of 'sorted' (adjacent pairs) mean what the name promises (all pairs)?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 17. `transon-not-necessary-for-single-list`

Tier T1 · kind: counterexample · depth: shallow · Lean: `transOn_not_necessary_for_single_list`

**Plain claim.** For r = (!=) on Nat and the list [0, 1], AdjRel r [0, 1] and List.Pairwise r [0, 1] agree, although r is not transitive on the elements of [0, 1].

**Statement.**

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:139-141
theorem transOn_not_necessary_for_single_list :
    (AdjRel (· ≠ · : Nat → Nat → Prop) [0, 1] ↔ List.Pairwise (· ≠ ·) [0, 1]) ∧
    ¬ TransOn (· ≠ · : Nat → Nat → Prop) [0, 1]
```

Unfolded statement of `transOn_not_necessary_for_single_list` (TransOn written out):

```lean
(AdjRel (· ≠ · : Nat → Nat → Prop) [0, 1] ↔ List.Pairwise (· ≠ ·) [0, 1]) ∧
  ¬ ∀ a ∈ ([0, 1] : List Nat), ∀ b ∈ ([0, 1] : List Nat), ∀ c ∈ ([0, 1] : List Nat),
    a ≠ b → b ≠ c → a ≠ c
```

**Hypothesis ledger.**

No hypotheses: the statement is a closed proposition about the relation ≠ on Nat and the list [0, 1].

**Non-vacuity.** Concrete instance (no hypotheses).

**Prior art.**

- No source is claimed for this small counterexample.

**Design question.** When does the cheap definition of 'sorted' (adjacent pairs) mean what the name promises (all pairs)?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

### Stored syntax versus displayed text

#### 18. `stored-formula-stable-under-expansion`

Tier T0 · kind: theorem · depth: shallow · Lean: `stored_formula_stable_under_expansion`

**Plain claim.** For any signature morphism iota : L -> L', structure S' of L' and formula phi of L: under every assignment, phi read along iota has the same truth value in S' as phi has in the reduct of S' (the old symbols read through iota).

**Statement.**

```lean
-- lean/Toy/Extension/Elaboration.lean:17-19
theorem stored_formula_stable_under_expansion {L L' : Sig} (ι : SigHom L L') {α : Type}
    (S' : Str L' α) {n : Nat} (φ : Formula L n) (v : Fin n → α) :
    Sat S' v (φ.map ι) ↔ Sat (S'.reduct ι) v φ
```

Unfolded (prose): the two sides.

```text
Left:  Tarskian satisfaction, in the L'-structure S' under assignment v, of the L-formula φ with every
       symbol renamed along ι (Formula.map).
Right: satisfaction of φ itself in the L-structure S'.reduct ι, which reads each old symbol f as
       S'.fn (ι.fn f) and each old relation r as S'.rel (ι.rel r), on the same carrier.
```

**Hypothesis ledger.**

No hypotheses: the equivalence holds for every signature morphism ι, structure S' of the larger language, formula φ of the smaller one and assignment v.

**Non-vacuity.** Expanding a {P}-structure by a constant keeps the old symbols: its reduct is the original structure. (`stored_formula_stable_nonvacuity`)

**Prior art.**

- Wilfrid Hodges, A Shorter Model Theory, Cambridge University Press, 1997, ISBN 978-0-521-58713-6, Section 2.6 'Translations' (pp. 51-58, from the table of contents). General reference for reducts and expansions over non-empty structures; no exercise-level statement is claimed.

**Design question.** Does extending a library's vocabulary change the meaning of statements already stored as syntax trees?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 19. `text-not-stable-under-env-extension`

Tier T1 · kind: counterexample · depth: shallow · Lean: `default_numeral_change_flips_truth`, `new_coercion_flips_truth`, `new_instance_flips_truth`

**Plain claim.** In a toy elaborator from displayed arithmetic comparisons to stored sentences, each of three environment extensions (prepending int as the default numeral type, prepending a coercion nat -> int, prepending an instance making / on int Euclidean) changes the stored reading of an old displayed string from a false sentence to a true one in the intended structure on Int.

**Statement.**

```lean
-- lean/Toy/Extension/Elaboration.lean:281-284
theorem default_numeral_change_flips_truth :
    envDefaultInt.Extends baseEnv ∧
    ∃ φ φ', baseEnv.elab sDefault = some φ ∧ envDefaultInt.elab sDefault = some φ' ∧
      ¬ intStr.Models φ ∧ intStr.Models φ'
```

```lean
-- lean/Toy/Extension/Elaboration.lean:292-295
theorem new_coercion_flips_truth :
    envCoeNatInt.Extends baseEnv ∧
    ∃ φ φ', baseEnv.elab sCoe = some φ ∧ envCoeNatInt.elab sCoe = some φ' ∧
      ¬ intStr.Models φ ∧ intStr.Models φ'
```

```lean
-- lean/Toy/Extension/Elaboration.lean:305-308
theorem new_instance_flips_truth :
    envDivE.Extends baseEnv ∧
    ∃ φ φ', baseEnv.elab sDiv = some φ ∧ envDivE.elab sDiv = some φ' ∧
      ¬ intStr.Models φ ∧ intStr.Models φ'
```

Unfolded (prose): the stored sentences produced by the toy elaborator (as computed by the proofs, which close the elaboration goals by rfl).

```text
sDefault = "0 - 1 < 0":
  baseEnv       (default nat):         subN(0, 1) < 0     in intStr: 0 < 0 (subN is truncated subtraction), false
  envDefaultInt (default int first):   subZ(0, 1) < 0     in intStr: -1 < 0, true
sCoe = "(0 : nat) - (1 : nat) < (0 : int)":
  baseEnv       (its one coercion is int -> nat; join type nat):   computed with subN (truncated subtraction), false (0 < 0)
  envCoeNatInt  (coercion nat -> int first; join type int):  computed with subZ, true  (-1 < 0)
sDiv = "((0 : int) - (7 : int)) / (2 : int) + (3 : int) < (0 : int)":
  baseEnv       (/ on int is divT, truncating division):   -7 / 2 = -3, so 0 < 0, false
  envDivE       (/ on int is divE, Euclidean division):    -7 / 2 = -4, so -1 < 0, true
Each modified environment extends baseEnv (Env.Extends: entries are prepended, none removed).
```

**Hypothesis ledger.**

No hypotheses: the three statements are closed propositions about the concrete environments baseEnv, envDefaultInt, envCoeNatInt and envDivE and the displayed strings sDefault, sCoe and sDiv.

**Non-vacuity.** Concrete instances (no hypotheses).

**Prior art.**

- Lean 4 core v4.34.1, Init/Data/Int/DivMod/Basic.lean line 111: the Div Int instance uses Int.ediv (Euclidean division); context for the instance countermodel.

**Design question.** Does extending a library's environment change the meaning of statements kept as displayed text rather than as stored syntax?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Env.elab is a toy elaborator with default numeral types, coercions and operator instances; reading its environment extensions as declarations added to a library is the modeling step. The toy elaborator differs from Lean 4's (see the non-claims). Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean 4's elaborator.

#### 20. `elab-preserves-check-iff`

Tier T0 · kind: characterization · depth: definitional · Lean: `elabPreservesCheck_iff_elabPreservesAccepted`, `elabInvariantCheck_iff_elabInvariantOn`

**Plain claim.** For any two environments e, e' and finite list D of displayed strings of the toy elaborator: elabPreservesCheck e e' D = true iff every string of D that elaborates under e elaborates to the same stored sentence under e' (ElabPreservesAccepted); and elabInvariantCheck e e' D = true iff every string of D has the same elaboration result, including failure, under e and e' (ElabInvariantOn).

**Statement.**

```lean
-- lean/Toy/Extension/Elaboration.lean:439-440
theorem elabPreservesCheck_iff_elabPreservesAccepted (e e' : Env) (D : List Disp) :
    elabPreservesCheck e e' D = true ↔ ElabPreservesAccepted e e' D
```

```lean
-- lean/Toy/Extension/Elaboration.lean:446-447
theorem elabInvariantCheck_iff_elabInvariantOn (e e' : Env) (D : List Disp) :
    elabInvariantCheck e e' D = true ↔ ElabInvariantOn e e' D
```

Unfolded statement of `elabPreservesCheck_iff_elabPreservesAccepted` (ElabPreservesAccepted written out), after the binders e, e', D:

```lean
elabPreservesCheck e e' D = true ↔ ∀ s ∈ D, ∀ φ, e.elab s = some φ → e'.elab s = some φ
```

Unfolded statement of `elabInvariantCheck_iff_elabInvariantOn` (ElabInvariantOn written out), after the binders e, e', D:

```lean
elabInvariantCheck e e' D = true ↔ ∀ s ∈ D, e.elab s = e'.elab s
```

**Hypothesis ledger.**

No hypotheses: both equivalences hold for all environments e, e' and every finite list D of displayed strings.

**Non-vacuity.** The default-type change preserves the annotated strings sCoe and sDiv and does not preserve 0 - 1 < 0. (`default_change_preserves_examples`)

**Prior art.**

- Lean 4 core v4.34.1, Init/Data/List/Lemmas.lean line 576, theorem List.all_eq_true (used in the proof).

**Design question.** Can re-elaborating a library's displayed statements decide whether an environment change preserved them?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Reading the re-elaboration of a library's displayed statements after an environment change, followed by a comparison of the stored results, as elabPreservesCheck / elabInvariantCheck on the toy elaborator is the modeling step; under that reading, each check returns true exactly when the corresponding property (ElabPreservesAccepted / ElabInvariantOn) holds for the listed strings. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean 4's elaborator or any library tooling.

### Requirements and specifications

#### 21. `adequate-specconservative-implies-translated-domain-entails`

Tier T0 · kind: theorem · depth: definitional · Lean: `adequate_specConservative_implies_translated_domain_entails`

**Plain claim.** For a signature morphism iota : LE -> L, domain knowledge K and a requirement R over LE, and a specification Spec over L: if K u Spec adds no LE-consequence to the translated K (SpecConservative) and K, Spec |= R (Adequate), then the translated K already entails the translated R.

**Statement.**

```lean
-- lean/Toy/Extension/Requirements.lean:80-83
theorem adequate_specConservative_implies_translated_domain_entails (ι : SigHom LE L)
    (K : Theory LE) (Spec : Theory L) (R : Sentence LE)
    (hcons : SpecConservative ι K Spec) (hadq : Adequate ι K Spec R) :
    Entails (K.map ι) (R.map ι)
```

Unfolded statement of `adequate_specConservative_implies_translated_domain_entails` (SpecConservative, Adequate and combined written out), after the binders ι, K, Spec, R:

```lean
(∀ φ : Sentence LE, Entails ((K.map ι).union Spec) (φ.map ι) → Entails (K.map ι) (φ.map ι)) →
  Entails ((K.map ι).union Spec) (R.map ι) → Entails (K.map ι) (R.map ι)
```

**Hypothesis ledger.**

- `hcons : SpecConservative ι K Spec` — The criterion under test. Tight; witness class: a two-symbol propositional base vocabulary {train, car} extended by one symbol gate, with K empty and Spec = {train -> gate, gate -> not car}. (*tight: counterexample `translated_domain_entails_ce_not_conservative`*)
- `hadq : Adequate ι K Spec R` — The requirement argument. Tight; same witness class, with the empty specification. (*tight: counterexample `translated_domain_entails_ce_not_adequate`*)

**Non-vacuity.** Domain knowledge {not (train and car)} with the empty specification is conservative and adequate. (`translated_domain_entails_nonvacuity`)

**Prior art.**

- Pamela Zave and Michael Jackson, 'Four dark corners of requirements engineering', ACM Transactions on Software Engineering and Methodology 6(1):1-30, 1997, DOI 10.1145/237432.237434 (Section 4.1, p. 11: phenomena are environment- or machine-controlled and shared or unshared; p. 19 and Section 6.3, p. 27: the argument S, K |- R; Section 6.3, p. 27: the members of S 'do not constrain the environment; they are not stated in terms of any unshared actions or state components').

**Design question.** Can consequence-conservativity of K u Spec over K detect specifications that silently assume something about the environment?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Reading K as domain knowledge, R as a requirement and Spec as a specification follows Zave and Jackson (1997). The theorem says that the consequence-conservativity criterion SpecConservative, applied over a vocabulary that contains the requirement, leaves the specification nothing to contribute. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about the reference model of Gunter, Gunter, Jackson and Zave (2000) or any real requirements document.

#### 22. `relconsistent-ev-requirement-implies-domain-entails`

Tier T1 · kind: theorem · depth: shallow · Lean: `specRelConsistent_adequate_ev_requirement_implies_domain_entails`

**Plain claim.** In a split LEv -> LS -> LW (machine-visible environment-controlled phenomena, shared phenomena, environment-visible phenomena) with domain knowledge K over LW, a specification Spec over LS and a sentence rho over LEv: if Spec is relatively consistent with K (SpecRelConsistent: for every model M of K, some LS-structure on M's carrier has the same LEv-reduct as M and satisfies Spec, and every such LS-structure is the LS-reduct of some model of K on that carrier) and K, Spec |= rho (rho translated to LW; SpecAdequate), then K |= rho already.

**Statement.**

```lean
-- lean/Toy/Extension/Requirements.lean:254-258
theorem specRelConsistent_adequate_ev_requirement_implies_domain_entails
    (ιVS : SigHom LEv LS) (ιSW : SigHom LS LW) (K : Theory LW) (Spec : Theory LS)
    (ρ : Sentence LEv) (hrc : SpecRelConsistent ιVS ιSW K Spec)
    (hadq : SpecAdequate ιSW K Spec ((ρ.map ιVS).map ιSW)) :
    Entails K ((ρ.map ιVS).map ιSW)
```

Unfolded statement of `specRelConsistent_adequate_ev_requirement_implies_domain_entails` (SpecRelConsistent split into its two named halves; SpecAdequate and withSpec written out), after the binders ιVS, ιSW, K, Spec, ρ:

```lean
SpecAcceptsEveryEnvInput ιVS ιSW K Spec ∧ SpecResponsesDomainConsistent ιVS ιSW K Spec →
  Entails (K.union (Spec.map ιSW)) ((ρ.map ιVS).map ιSW) → Entails K ((ρ.map ιVS).map ιSW)
```

Unfolded (prose): the two halves, read with LEv-reducts as behaviours of the machine-visible environment-controlled phenomena.

```text
SpecAcceptsEveryEnvInput ιVS ιSW K Spec:
  for every carrier β and every model M of K on β, some LS-structure N on β has the same
  LEv-reduct as M and satisfies Spec.
SpecResponsesDomainConsistent ιVS ιSW K Spec:
  for every model M of K on β and every LS-structure N on β with the same LEv-reduct as M that
  satisfies Spec, some model M' of K on β has LS-reduct exactly N.
```

**Hypothesis ledger.**

- `hrc : SpecRelConsistent ιVS ιSW K Spec` — The specification condition. Tight; witness class: a propositional split with train and car machine-visible and environment-controlled, gate machine-controlled, no hidden phenomena, K empty and Spec = {train -> gate, gate -> not car}. (*tight: counterexample `ev_requirement_ce_not_relConsistent`*)
- `hadq : SpecAdequate ιSW K Spec ((ρ.map ιVS).map ιSW)` — Specification adequacy. Tight; same witness class with the empty specification. (*tight: counterexample `ev_requirement_ce_not_adequate`*)

**Non-vacuity.** Same split with K = {not (train and car)} and the empty specification. (`ev_requirement_nonvacuity`)

**Positive control.** A nearby setting where the conclusion fails: when the requirement mentions a hidden environment-controlled phenomenon (car), a specification that is SpecRelConsistent and adequate meets it while the domain knowledge alone does not entail it (`crossing_control_spec_relConsistent_not_envConservative`).

**Prior art.**

- Carl A. Gunter, Elsa L. Gunter, Michael Jackson and Pamela Zave, 'A Reference Model for Requirements and Specifications', IEEE Software 17(3):37-43, 2000, DOI 10.1109/52.896248 (p. 38: e = eh u ev and s = sv u sh; terms for eh, ev and sv are 'used in W and R', and S is restricted to ev and sv; p. 40: specification adequacy (4) 'forall e s. W and S => R' and relative consistency (5) 'forall ev. (exists eh s. W) => (exists s. S) and (forall s. S => exists eh. W)').
- Pamela Zave and Michael Jackson, 'Four dark corners of requirements engineering', ACM Transactions on Software Engineering and Methodology 6(1):1-30, 1997, DOI 10.1145/237432.237434 (Section 4.1, p. 11: phenomena are environment- or machine-controlled and shared or unshared; p. 19 and Section 6.3, p. 27: the argument S, K |- R; Section 6.3, p. 27: the members of S 'do not constrain the environment; they are not stated in terms of any unshared actions or state components').

**Design question.** Which requirements can a specification establish without assuming something about the environment?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — SpecRelConsistent is a model-theoretic rendering of the relative-consistency formula (5) of Gunter et al. (2000, p. 40), with all phenomena interpreted over one shared carrier and without time, the machine M or the program P. Under that reading, a specification that does not restrict the environment cannot establish a requirement expressed over the machine-visible environment-controlled phenomena (a translated LEv-sentence) unless the domain knowledge already entails it. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about the reference model of Gunter, Gunter, Jackson and Zave (2000) or any real requirements document.

#### 23. `crossing-control-spec-relconsistent-not-envconservative`

Tier T1 · kind: counterexample · depth: shallow · Lean: `crossing_control_spec_relConsistent_not_envConservative`

**Plain claim.** With train environment-controlled and machine-visible, car environment-controlled and hidden, gate machine-controlled, domain knowledge domainA = {gate -> not car} and specification specA = {train -> gate}: the specification meets not (train and car) (SpecAdequate), the domain knowledge alone does not entail it, the specification is relatively consistent (SpecRelConsistent ιVSA ιSWA domainA specA), and domain knowledge plus specification is not consequence-conservative over the domain knowledge for sentences over the environment-controlled vocabulary {train, car} (not ConservativeFor ιEWA domainA (withSpec ιSWA domainA specA)).

**Statement.**

```lean
-- lean/Toy/Extension/Requirements.lean:365-369
theorem crossing_control_spec_relConsistent_not_envConservative :
    SpecAdequate ιSWA domainA specA (noCollisionE.map ιEWA) ∧
    ¬ Entails domainA (noCollisionE.map ιEWA) ∧
    SpecRelConsistent ιVSA ιSWA domainA specA ∧
    ¬ ConservativeFor ιEWA domainA (withSpec ιSWA domainA specA)
```

Unfolded statement of `crossing_control_spec_relConsistent_not_envConservative` (SpecAdequate, withSpec, SpecRelConsistent and ConservativeFor written out):

```lean
Entails (domainA.union (specA.map ιSWA)) (noCollisionE.map ιEWA) ∧
¬ Entails domainA (noCollisionE.map ιEWA) ∧
(SpecAcceptsEveryEnvInput ιVSA ιSWA domainA specA ∧ SpecResponsesDomainConsistent ιVSA ιSWA domainA specA) ∧
¬ ∀ φ : Sentence (propSig CEnvA),
    Entails (domainA.union (specA.map ιSWA)) (φ.map ιEWA) → Entails domainA (φ.map ιEWA)
```

**Hypothesis ledger.**

No hypotheses: the statement is a closed proposition about the concrete crossing vocabularies, the domain knowledge domainA and the specification specA.

**Non-vacuity.** Concrete instance (no hypotheses).

**Prior art.**

- Carl A. Gunter, Elsa L. Gunter, Michael Jackson and Pamela Zave, 'A Reference Model for Requirements and Specifications', IEEE Software 17(3):37-43, 2000, DOI 10.1109/52.896248 (p. 38: e = eh u ev and s = sv u sh; terms for eh, ev and sv are 'used in W and R', and S is restricted to ev and sv; p. 40: specification adequacy (4) 'forall e s. W and S => R' and relative consistency (5) 'forall ev. (exists eh s. W) => (exists s. S) and (forall s. S => exists eh. W)').
- Pamela Zave and Michael Jackson, 'Four dark corners of requirements engineering', ACM Transactions on Software Engineering and Methodology 6(1):1-30, 1997, DOI 10.1145/237432.237434 (Section 4.1, p. 11: phenomena are environment- or machine-controlled and shared or unshared; p. 19 and Section 6.3, p. 27: the argument S, K |- R; Section 6.3, p. 27: the members of S 'do not constrain the environment; they are not stated in terms of any unshared actions or state components').

**Design question.** Can consequence-conservativity of K u Spec over K detect specifications that silently assume something about the environment?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Under the same rendering of formula (5) by SpecRelConsistent, the example shows that a consequence-conservativity check over the environment-controlled vocabulary rejects a specification that is relatively consistent and adequate; reading the gate as legitimate machine control is the reference-model reading. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about the reference model of Gunter, Gunter, Jackson and Zave (2000) or any real requirements document, or about real railway crossings.

#### 24. `crossing-restricting-spec-violates-env-input-condition`

Tier T1 · kind: counterexample · depth: shallow · Lean: `crossing_restricting_spec_violates_env_input_condition`

**Plain claim.** With train and car environment-controlled and machine-visible, gate machine-controlled and empty domain knowledge (ιSWB is the identity, so the shared and environment-visible vocabularies coincide): the specification specB = {train -> gate, gate -> not car} meets not (train and car) (SpecAdequate), the empty domain knowledge does not entail not (train and car), and specB does not accept every environment input (not SpecAcceptsEveryEnvInput ιVSB ιSWB Theory.empty specB); moreover, for every specification Spec over these phenomena, if Spec meets not (train and car) with empty domain knowledge, then Spec is not relatively consistent (not SpecRelConsistent ιVSB ιSWB Theory.empty Spec).

**Statement.**

```lean
-- lean/Toy/Extension/Requirements.lean:452-458
theorem crossing_restricting_spec_violates_env_input_condition :
    SpecAdequate ιSWB Theory.empty specB ((noCollisionEv.map ιVSB).map ιSWB) ∧
    ¬ Entails (Theory.empty : Theory (propSig CSB)) ((noCollisionEv.map ιVSB).map ιSWB) ∧
    ¬ SpecAcceptsEveryEnvInput ιVSB ιSWB Theory.empty specB ∧
    ∀ Spec : Theory (propSig CSB),
      SpecAdequate ιSWB Theory.empty Spec ((noCollisionEv.map ιVSB).map ιSWB) →
        ¬ SpecRelConsistent ιVSB ιSWB Theory.empty Spec
```

Unfolded statement of `crossing_restricting_spec_violates_env_input_condition` (SpecAcceptsEveryEnvInput written out in the third conjunct):

```lean
SpecAdequate ιSWB Theory.empty specB ((noCollisionEv.map ιVSB).map ιSWB) ∧
¬ Entails (Theory.empty : Theory (propSig CSB)) ((noCollisionEv.map ιVSB).map ιSWB) ∧
¬ (∀ (β : Type) (M : Str (propSig CSB) β), M.ModelsTh (Theory.empty : Theory (propSig CSB)) →
    ∃ N : Str (propSig CSB) β, N.reduct ιVSB = (M.reduct ιSWB).reduct ιVSB ∧ N.ModelsTh specB) ∧
∀ Spec : Theory (propSig CSB),
  SpecAdequate ιSWB Theory.empty Spec ((noCollisionEv.map ιVSB).map ιSWB) →
    ¬ SpecRelConsistent ιVSB ιSWB Theory.empty Spec
```

**Hypothesis ledger.**

No hypotheses: the statement is a closed proposition about the concrete crossing vocabularies, the empty domain knowledge and the specification specB; its last conjunct is quantified over every specification Spec over propSig CSB.

**Non-vacuity.** Concrete instance (no hypotheses).

**Prior art.**

- Carl A. Gunter, Elsa L. Gunter, Michael Jackson and Pamela Zave, 'A Reference Model for Requirements and Specifications', IEEE Software 17(3):37-43, 2000, DOI 10.1109/52.896248 (p. 38: e = eh u ev and s = sv u sh; terms for eh, ev and sv are 'used in W and R', and S is restricted to ev and sv; p. 40: specification adequacy (4) 'forall e s. W and S => R' and relative consistency (5) 'forall ev. (exists eh s. W) => (exists s. S) and (forall s. S => exists eh. W)').
- Pamela Zave and Michael Jackson, 'Four dark corners of requirements engineering', ACM Transactions on Software Engineering and Methodology 6(1):1-30, 1997, DOI 10.1145/237432.237434 (Section 4.1, p. 11: phenomena are environment- or machine-controlled and shared or unshared; p. 19 and Section 6.3, p. 27: the argument S, K |- R; Section 6.3, p. 27: the members of S 'do not constrain the environment; they are not stated in terms of any unshared actions or state components').

**Design question.** Which requirements can a specification establish without assuming something about the environment?

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Calling the failure of SpecAcceptsEveryEnvInput an assumption about the environment is the reading of the first half of formula (5) of Gunter et al.; the theorem itself is about the toy split. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and the systems named next is formalized). These are statements about the toy model; they neither establish nor refute the corresponding claims about the reference model of Gunter, Gunter, Jackson and Zave (2000) or any real requirements document.

### Auxiliary lemmas cited by name (verbatim)

Each block quotes, verbatim and up to `:=`, the statement of a theorem that this report names outside a card's **Statement** block: tightness counterexamples, non-vacuity witnesses, positive controls, and the further theorems cited in ledgers, non-claims and escape hatches. Blocks are grouped by source file. Every theorem quoted here is listed in `results.json` (fields `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, or a hypothesis `counterexample`), so `audit/statements.json` records its statement and closure hashes.

```lean
-- lean/Toy/Extension/Semantics.lean:144-145
theorem sat_map (ι : SigHom L L') (S : Str L' α) {n : Nat} (v : Fin n → α) (φ : Formula L n) :
    Sat S v (φ.map ι) ↔ Sat (S.reduct ι) v φ
```

```lean
-- lean/Toy/Extension/Definitional.lean:255-256
theorem defExt_expansion_iff_of_axiom (d : Defn L) (S : Str L α) (S' : Str d.sig α) :
    (S'.reduct d.incl = S ∧ S'.Models d.defAxiom) ↔ S' = d.expand S
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:75-76
theorem dTwo_three_not_models_defAxiom :
    ¬ (natStr.withFn (fun _ : Fin 0 → Nat => 3)).Models (dTwo.defAxiom)
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:122-126
theorem defExt_expansions_eq_expand_ce_not_model :
    ¬ natStr.ModelsTh (Theory.ofList [Formula.falsum]) ∧
    ¬ (∀ S' : Str dTwo.sig Nat,
        (S'.reduct dTwo.incl = natStr ∧ S'.ModelsTh (dTwo.theory (Theory.ofList [Formula.falsum])))
          ↔ S' = dTwo.expand natStr)
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:134-137
theorem defExt_expansion_unique_ce_reduct :
    (dTwo.expand natStr2).Models dTwo.defAxiom ∧
    (dTwo.expand natStr2).reduct dTwo.incl ≠ natStr ∧
    dTwo.expand natStr2 ≠ dTwo.expand natStr
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:150-152
theorem defExt_expansion_unique_ce_axiom :
    (natStr.withFn (fun _ : Fin 0 → Nat => 3)).reduct dTwo.incl = natStr ∧
    natStr.withFn (fun _ : Fin 0 → Nat => 3) ≠ dTwo.expand natStr
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:161-163
theorem defExt_unfold_equiv_ce_axiom :
    ¬ (Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars psiTwo ↔
       Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars ((dTwo.unfold psiTwo).map dTwo.incl))
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:174
theorem defExt_expansions_eq_expand_nonvacuity : natStr.ModelsTh (Theory.empty : Theory NSig)
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:180-181
theorem defExt_axiom_nonvacuity :
    (dTwo.expand natStr).reduct dTwo.incl = natStr ∧ (dTwo.expand natStr).Models dTwo.defAxiom
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:186-187
theorem defExt_theory_has_model :
    (dTwo.expand natStr).ModelsTh (dTwo.theory (Theory.empty : Theory NSig))
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:205-208
theorem dTwo_deltaConv_sound_and_unsound :
    (Sat (dTwo.expand natStr) noVars psiTwo ↔ Sat (dTwo.expand natStr) noVars psiTwoRefl) ∧
    ¬ (Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars psiTwo ↔
       Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars psiTwoRefl)
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:217-219
theorem dTwo_deltaConv_examples :
    dTwo.DeltaConv psiTwo psiTwoRefl ∧ psiTwo ≠ psiTwoRefl ∧
    ¬ dTwo.DeltaConv psiTwo Formula.falsum
```

```lean
-- lean/Toy/Extension/DefinitionalExamples.lean:227-230
theorem unfold_preserves_tru_without_defAxiom :
    ¬ (natStr.withFn (fun _ : Fin 0 → Nat => 3)).Models dTwo.defAxiom ∧
    (Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars Formula.tru ↔
     Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars ((dTwo.unfold Formula.tru).map dTwo.incl))
```

```lean
-- lean/Toy/Extension/Transparency.lean:61-62
theorem defnFn_theory_fnExplicitlyDefinable (T : Theory L) {k : Nat} (e : Term L k) :
    FnExplicitlyDefinable (k := k) ((Defn.fn k e).theory T)
```

```lean
-- lean/Toy/Extension/Transparency.lean:93-96
theorem axPc_two_lawful_interpretations :
    pcModelTrue.ModelsTh (Theory.ofList [axPc]) ∧ pcModelFalse.ModelsTh (Theory.ofList [axPc]) ∧
    pcModelTrue.reduct (SigHom.inclFn LP 0) = pcModelFalse.reduct (SigHom.inclFn LP 0) ∧
    pcModelTrue ≠ pcModelFalse
```

```lean
-- lean/Toy/Extension/Transparency.lean:109-110
theorem axPc_not_fnExplicitlyDefinable :
    ¬ FnExplicitlyDefinable (k := 0) (Theory.ofList [axPc])
```

```lean
-- lean/Toy/Extension/Transparency.lean:122-129
theorem fnExplicitlyDefinable_expansion_unique_ce_model :
    FnExplicitlyDefinable (k := 0) (dTwo.theory (Theory.empty : Theory NSig)) ∧
    ¬ (natStr.withFn (fun _ : Fin 0 → Nat => 3)).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (natStr.withFn (fun _ : Fin 0 → Nat => 3)).reduct (SigHom.inclFn NSig 0) =
      (dTwo.expand natStr).reduct dTwo.incl ∧
    natStr.withFn (fun _ : Fin 0 → Nat => 3) ≠ dTwo.expand natStr ∧
    dTwo.expand natStr ≠ natStr.withFn (fun _ : Fin 0 → Nat => 3)
```

```lean
-- lean/Toy/Extension/Transparency.lean:138-143
theorem fnExplicitlyDefinable_expansion_unique_ce_reduct :
    FnExplicitlyDefinable (k := 0) (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr2).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr2).reduct dTwo.incl ≠ (dTwo.expand natStr).reduct dTwo.incl ∧
    dTwo.expand natStr2 ≠ dTwo.expand natStr
```

```lean
-- lean/Toy/Extension/Transparency.lean:151-153
theorem fnExplicitlyDefinable_nonvacuity :
    FnExplicitlyDefinable (k := 0) (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr).ModelsTh (dTwo.theory (Theory.empty : Theory NSig))
```

```lean
-- lean/Toy/Extension/ScopeExamples.lean:16-18
theorem fnExplicitlyDefinable_of_no_model {k : Nat} (T' : Theory (L.addFn k))
    (hno : ∀ (β : Type) (S : Str (L.addFn k) β), ¬ S.ModelsTh T') :
    FnExplicitlyDefinable T'
```

```lean
-- lean/Toy/Extension/ScopeExamples.lean:23-26
theorem falsum_theory_fnExplicitlyDefinable_no_model :
    FnExplicitlyDefinable (k := 0) (Theory.ofList [Formula.falsum] : Theory (LP.addFn 0)) ∧
    ¬ ∃ (β : Type) (S : Str (LP.addFn 0) β),
      S.ModelsTh (Theory.ofList [Formula.falsum] : Theory (LP.addFn 0))
```

```lean
-- lean/Toy/Extension/ScopeExamples.lean:46-52
theorem fnExplicitlyDefinable_satisfiable_not_conservative :
    FnExplicitlyDefinable (k := 0) singletonDefTheory ∧
    ((pStr (fun _ : Unit => False)).withFn (fun _ => ())).ModelsTh singletonDefTheory ∧
    Entails singletonDefTheory (atMostOneElt.map (SigHom.inclFn LP 0)) ∧
    ¬ Entails (Theory.empty : Theory LP) atMostOneElt ∧
    ¬ Conservative (SigHom.inclFn LP 0) Theory.empty singletonDefTheory ∧
    ¬ ExpansionProperty (SigHom.inclFn LP 0) Theory.empty singletonDefTheory
```

```lean
-- lean/Toy/Extension/ScopeExamples.lean:83-86
theorem reinterpreted_symbol_need_not_flip_truth :
    pStr (fun b : Bool => b = true) ≠ pStr (fun b : Bool => b = false) ∧
    (pStr (fun b : Bool => b = true)).Models existsP ∧
    (pStr (fun b : Bool => b = false)).Models existsP
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:97-99
theorem expansionProperty_implies_conservative_ce :
    ¬ ExpansionProperty (SigHom.inclFn LP 0) Theory.empty (Theory.ofList [axPc]) ∧
    ¬ Conservative (SigHom.inclFn LP 0) Theory.empty (Theory.ofList [axPc])
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:105-106
theorem expansionProperty_nonvacuity :
    ExpansionProperty (SigHom.inclRel LP 0) Theory.empty Theory.empty
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:131-133
theorem fresh_constant_conservative_of_nonempty_models {L : Sig} (T : Theory L)
    (hne : Entails T existsEq) :
    Conservative (SigHom.inclFn L 0) T (T.map (SigHom.inclFn L 0))
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:143-144
theorem fresh_constant_conservative_iff_entails_nonempty {L : Sig} (T : Theory L) :
    Conservative (SigHom.inclFn L 0) T (T.map (SigHom.inclFn L 0)) ↔ Entails T existsEq
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:175-179
theorem noninjective_hom_empty_theories_not_conservative :
    Entails (Theory.empty : Theory LUnit) (abIff.map ιCollapse) ∧
    ¬ Entails (Theory.empty : Theory LAB) abIff ∧
    ¬ Conservative ιCollapse Theory.empty Theory.empty ∧
    ¬ ExpansionProperty ιCollapse Theory.empty Theory.empty
```

```lean
-- lean/Toy/Extension/Axiomatic.lean:215-217
theorem axExt_lawful_interpretation_exists :
    ((pStr (fun _ : Unit => True)).withFn (fun _ : Fin 0 → Unit => ())).ModelsTh
      (((Theory.empty : Theory LP).map (SigHom.inclFn LP 0)).union (Theory.ofList [axPc]))
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:44
theorem natSort_strongSortSpec : StrongSortSpec natSort
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:83-85
theorem false_spec_atMostOneLawful_not_determines :
    AtMostOneLawful (fun _ : List Nat → List Nat => False) ∧
    ¬ Determines (fun _ : List Nat → List Nat => False)
```

```lean
-- lean/Toy/Extension/LooseSpec.lean:100-101
theorem weakSortSpec_satisfiable_not_determines :
    (∃ f, WeakSortSpec f) ∧ ¬ Determines WeakSortSpec
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:137-142
theorem label_deciders_ce_labels :
    (true ∉ [false] ++ ([] : List Bool)) ∧
    ¬ (AgreesOn (memDecider [false]) (· = true) ([false] ++ []) ∧
       AgreesOn (memDecider (true :: [false])) (· = true) ([false] ++ []) ∧
       (¬ Decides (memDecider [false]) (· = true) ∨
        ¬ Decides (memDecider (true :: [false])) (· = true)))
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:151-156
theorem label_deciders_ce_point :
    LabelsCorrect (· = true) [true] [false] ∧
    ¬ (AgreesOn (memDecider [true]) (· = true) ([true] ++ [false]) ∧
       AgreesOn (memDecider (true :: [true])) (· = true) ([true] ++ [false]) ∧
       (¬ Decides (memDecider [true]) (· = true) ∨
        ¬ Decides (memDecider (true :: [true])) (· = true)))
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:173-183
theorem label_deciders_conclusion_without_hypotheses :
    (¬ LabelsCorrect (· = 0 : Nat → Prop) [0] [0] ∧ ((1 : Nat) ∉ [0] ++ [0]) ∧
      AgreesOn (memDecider [0]) (· = 0 : Nat → Prop) ([0] ++ [0]) ∧
      AgreesOn (memDecider (1 :: [0])) (· = 0 : Nat → Prop) ([0] ++ [0]) ∧
      (¬ Decides (memDecider [0]) (· = 0 : Nat → Prop) ∨
       ¬ Decides (memDecider (1 :: [0])) (· = 0 : Nat → Prop))) ∧
    (LabelsCorrect (fun _ : Nat => True) [0] [] ∧ (0 : Nat) ∈ ([0] ++ ([] : List Nat)) ∧
      AgreesOn (memDecider [0]) (fun _ : Nat => True) ([0] ++ []) ∧
      AgreesOn (memDecider (0 :: [0])) (fun _ : Nat => True) ([0] ++ []) ∧
      (¬ Decides (memDecider [0]) (fun _ : Nat => True) ∨
       ¬ Decides (memDecider (0 :: [0])) (fun _ : Nat => True)))
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:203-205
theorem unrestricted_decider_not_certified_ce_finite :
    ¬ InfiniteType Bool ∧
    ¬ ∃ d : Bool → Bool, AgreesOn d (· = true) [true, false] ∧ ¬ Decides d (· = true)
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:214-215
theorem exhaustive_examples_certify (d : α → Bool) (Spec : α → Prop) (E : List α)
    (hall : ∀ x, x ∈ E) (hag : AgreesOn d Spec E) : Decides d Spec
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:224-226
theorem threshold_examples_certify (j k : Nat)
    (hag : AgreesOn (thresholdDecider j) (fun x => k ≤ x) [k - 1, k]) :
    Decides (thresholdDecider j) (fun x => k ≤ x)
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:236-237
theorem reference_equivalence_certifies (d : α → Bool) (ref Spec : α → Prop)
    (hd : ∀ x, d x = true ↔ ref x) (href : ∀ x, ref x ↔ Spec x) : Decides d Spec
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:242-244
theorem decides_iff_reference_matches_spec (d : α → Bool) (ref Spec : α → Prop)
    (hd : ∀ x, d x = true ↔ ref x) :
    Decides d Spec ↔ (∀ x, ref x ↔ Spec x)
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:249-251
theorem reference_equivalence_moves_trust :
    Decides (fun _ : Bool => true) (fun _ => True) ∧
    ¬ Decides (fun _ : Bool => true) (· = true)
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:258-259
theorem label_deciders_nonvacuity :
    LabelsCorrect (fun n : Nat => n % 2 = 0) [0, 2] [1] ∧ (4 : Nat) ∉ [0, 2] ++ [1]
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:273
theorem unrestricted_decider_not_certified_nonvacuity : InfiniteType Nat
```

```lean
-- lean/Toy/Extension/FiniteExamples.lean:277-278
theorem threshold_examples_certify_nonvacuity :
    AgreesOn (thresholdDecider 3) (fun x => 3 ≤ x) [3 - 1, 3]
```

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:48
theorem ne_not_transOn : ¬ TransOn (· ≠ · : Nat → Nat → Prop) [0, 1]
```

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:73-74
theorem pairwise_implies_adjRel (r : α → α → Prop) (l : List α) (hpw : List.Pairwise r l) :
    AdjRel r l
```

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:80-82
theorem pairwise_implies_adjRel_ce :
    ¬ List.Pairwise (· ≤ · : Nat → Nat → Prop) [2, 1] ∧
    ¬ AdjRel (· ≤ · : Nat → Nat → Prop) [2, 1]
```

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:126-130
theorem adjRel_ne_not_pairwise :
    ¬ TransOn (· ≠ · : Nat → Nat → Prop) [0, 1, 0] ∧
    ¬ (AdjRel (· ≠ · : Nat → Nat → Prop) [0, 1, 0] ↔ List.Pairwise (· ≠ ·) [0, 1, 0]) ∧
    AdjRel (· ≠ · : Nat → Nat → Prop) [0, 1, 0] ∧
    ¬ List.Pairwise (· ≠ · : Nat → Nat → Prop) [0, 1, 0]
```

```lean
-- lean/Toy/Extension/SortedAdequacy.lean:149-151
theorem sorted_readings_nonvacuity :
    TransitiveRel (· ≤ · : Nat → Nat → Prop) ∧ TransOn (· ≤ ·) [1, 2, 2, 3] ∧
    AdjRel (· ≤ ·) [1, 2, 2, 3] ∧ List.Pairwise (· ≤ ·) [1, 2, 2, 3]
```

```lean
-- lean/Toy/Extension/Elaboration.lean:26-29
theorem stored_formula_stable_ce_reinterpreted :
    (pStr (fun _ : Unit => False)).reduct (SigHom.id LP) ≠ pStr (fun _ : Unit => True) ∧
    ¬ (Sat (pStr (fun _ : Unit => False)) noVars (existsP.map (SigHom.id LP)) ↔
       Sat (pStr (fun _ : Unit => True)) noVars existsP)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:39-41
theorem stored_formula_stable_nonvacuity :
    ((pStr (fun _ : Unit => True)).withFn (fun _ : Fin 0 → Unit => ())).reduct (SigHom.inclFn LP 0)
      = pStr (fun _ : Unit => True)
```

```lean
-- lean/Toy/Extension/Elaboration.lean:204-205
theorem elabInvariantOn_symm (e e' : Env) (D : List Disp) :
    ElabInvariantOn e e' D ↔ ElabInvariantOn e' e D
```

```lean
-- lean/Toy/Extension/Elaboration.lean:272-274
theorem default_change_preserves_examples :
    elabPreservesCheck baseEnv envDefaultInt [sCoe, sDiv] = true ∧
    elabPreservesCheck baseEnv envDefaultInt [sDefault] = false
```

```lean
-- lean/Toy/Extension/Elaboration.lean:317-319
theorem elab_change_without_truth_change :
    ∃ φ φ', baseEnv.elab sHarmless = some φ ∧ envCoeNatInt.elab sHarmless = some φ' ∧
      φ ≠ φ' ∧ intStr.Models φ ∧ intStr.Models φ'
```

```lean
-- lean/Toy/Extension/Elaboration.lean:394-399
theorem additive_coercion_preserves_but_not_invariant :
    envAddNatInt.Extends envNoCoe ∧
    (∀ (s : Disp) (φ : Sentence ASig), envNoCoe.elab s = some φ → envAddNatInt.elab s = some φ) ∧
    envNoCoe.elab sCoe = none ∧ (envAddNatInt.elab sCoe).isSome = true ∧
    ¬ ElabInvariantOn envNoCoe envAddNatInt [sCoe] ∧
    ElabPreservesAccepted envNoCoe envAddNatInt [sCoe]
```

```lean
-- lean/Toy/Extension/Requirements.lean:88-90
theorem specExpansionProperty_adequate_iff (ι : SigHom LE L) (K : Theory LE)
    (Spec : Theory L) (R : Sentence LE) (hexp : SpecExpansionProperty ι K Spec) :
    Adequate ι K Spec R ↔ Entails (K.map ι) (R.map ι)
```

```lean
-- lean/Toy/Extension/Requirements.lean:186-188
theorem translated_domain_entails_ce_not_conservative :
    Adequate ιCross Theory.empty specCross noCollision ∧
    ¬ Entails ((Theory.empty : Theory LEnv).map ιCross) (noCollision.map ιCross)
```

```lean
-- lean/Toy/Extension/Requirements.lean:194-196
theorem translated_domain_entails_ce_not_adequate :
    SpecConservative ιCross (Theory.empty : Theory LEnv) Theory.empty ∧
    ¬ Entails ((Theory.empty : Theory LEnv).map ιCross) (noCollision.map ιCross)
```

```lean
-- lean/Toy/Extension/Requirements.lean:202-204
theorem translated_domain_entails_nonvacuity :
    SpecConservative ιCross (Theory.ofList [noCollision]) Theory.empty ∧
    Adequate ιCross (Theory.ofList [noCollision]) Theory.empty noCollision
```

```lean
-- lean/Toy/Extension/Requirements.lean:480-482
theorem ev_requirement_ce_not_relConsistent :
    SpecAdequate ιSWB Theory.empty specB ((noCollisionEv.map ιVSB).map ιSWB) ∧
    ¬ Entails (Theory.empty : Theory (propSig CSB)) ((noCollisionEv.map ιVSB).map ιSWB)
```

```lean
-- lean/Toy/Extension/Requirements.lean:498-500
theorem ev_requirement_ce_not_adequate :
    SpecRelConsistent ιVSB ιSWB Theory.empty Theory.empty ∧
    ¬ Entails (Theory.empty : Theory (propSig CSB)) ((noCollisionEv.map ιVSB).map ιSWB)
```

```lean
-- lean/Toy/Extension/Requirements.lean:506-509
theorem ev_requirement_nonvacuity :
    SpecRelConsistent ιVSB ιSWB (Theory.ofList [(noCollisionEv.map ιVSB).map ιSWB]) Theory.empty ∧
    SpecAdequate ιSWB (Theory.ofList [(noCollisionEv.map ιVSB).map ιSWB]) Theory.empty
      ((noCollisionEv.map ιVSB).map ιSWB)
```

## Boundaries

### Non-claims

What each result does not show. Theorem names in parentheses are proved in the package; "(not proved here)" marks statements that are neither proved nor refuted here.

#### Non-claims of 1. `defext-expansions-eq-expand`

- Uniqueness holds without assuming that S models T (defExt_expansion_unique_of_axiom).
- The structures share the carrier with S; nothing is said about expansions up to isomorphism or on other carriers.
- Kernel definitional equality of a dependent type theory is not modeled: Defn.theory adds a first-order defining axiom, and Defn.DeltaConv is conversion for one defined symbol over first-order syntax (no beta, iota or eta, no type-level conversion such as Vec a c versus Vec a e).
- Recursive definitions (the new symbol occurring in its own definiens), type or inductive definitions, definitions of a function symbol by a formula with a proved unique-existence condition, and polymorphic or overloaded definitions are not modeled.
- Applies to stored first-order syntax read along d.incl; in a surface language with name resolution, notations, coercions or instances, adding declarations can change how displayed text elaborates (default_numeral_change_flips_truth, new_coercion_flips_truth, new_instance_flips_truth).

#### Non-claims of 2. `defext-expansion-unique-of-axiom`

- Says nothing about structures whose old symbols differ from S.
- Equality is equality of structures on a fixed carrier (function and propositional extensionality are used), not isomorphism.
- The converse also holds and is proved as defExt_expansion_iff_of_axiom (a helper, not a separate card).
- Kernel definitional equality of a dependent type theory is not modeled: Defn.theory adds a first-order defining axiom, and Defn.DeltaConv is conversion for one defined symbol over first-order syntax (no beta, iota or eta, no type-level conversion such as Vec a c versus Vec a e).
- Recursive definitions (the new symbol occurring in its own definiens), type or inductive definitions, definitions of a function symbol by a formula with a proved unique-existence condition, and polymorphic or overloaded definitions are not modeled.

#### Non-claims of 3. `defext-conservative`

- Conservativity is semantic (entailment over all structures with carriers in Type, including empty ones); no proof system is modeled.
- Does not cover axiomatic extensions, which can fail to be conservative (axiom_P_c_not_conservative).
- Applies to stored first-order syntax read along d.incl; in a surface language with name resolution, notations, coercions or instances, adding declarations can change how displayed text elaborates (default_numeral_change_flips_truth, new_coercion_flips_truth, new_instance_flips_truth).
- Kernel definitional equality of a dependent type theory is not modeled: Defn.theory adds a first-order defining axiom, and Defn.DeltaConv is conversion for one defined symbol over first-order syntax (no beta, iota or eta, no type-level conversion such as Vec a c versus Vec a e).
- Recursive definitions (the new symbol occurring in its own definiens), type or inductive definitions, definitions of a function symbol by a formula with a proved unique-existence condition, and polymorphic or overloaded definitions are not modeled.

#### Non-claims of 4. `defext-unfold-preserves-sat-iff-defining-axiom`

- Kernel definitional equality of a dependent type theory is not modeled: Defn.theory adds a first-order defining axiom, and Defn.DeltaConv is conversion for one defined symbol over first-order syntax (no beta, iota or eta, no type-level conversion such as Vec a c versus Vec a e).
- Items (ii) and (iii) quantify over all formulas; for one fixed formula, truth can be preserved without the defining axiom (unfold_preserves_tru_without_defAxiom).
- The unfolding is one specific syntactic function (Defn.unfold); nothing is said about other old-language equivalents, or about the size of the unfolding.
- Depth: the proof uses a substitution lemma for formulas under binders.
- Recursive definitions (the new symbol occurring in its own definiens), type or inductive definitions, definitions of a function symbol by a formula with a proved unique-existence condition, and polymorphic or overloaded definitions are not modeled.

#### Non-claims of 5. `explicit-definability-implies-unique-expansion`

- The converse (uniqueness of expansions implies explicit definability, Beth's theorem) is not proved here.
- The theorem is about a new function symbol; the analogue for a new relation symbol is not stated.
- Transparency here means explicit definability by a first-order formula of the old language; it is not kernel delta-reduction in a dependent type theory.
- WeakSortSpec and StrongSortSpec are higher-order characterizations of a function on List Nat; this first-order theorem does not apply to them, and any analogy to weakSortSpec_admits_natSort_and_weirdSort is informal (not proved here).
- Separately proved consequences, which are not part of this theorem's statement: a symbol introduced by an explicit definition is explicitly definable in the definitional extension (defnFn_theory_fnExplicitlyDefinable), and the constant whose sole axiom is P c is not explicitly definable (axPc_not_fnExplicitlyDefinable).
- FnExplicitlyDefinable T' holds vacuously when T' has no model on any carrier (fnExplicitlyDefinable_of_no_model; instance: falsum_theory_fnExplicitlyDefinable_no_model); the conclusion is then vacuous as well.
- For a satisfiable T', FnExplicitlyDefinable T' gives uniqueness of expansions (S1 = S2), not conservativity or the expansion property over a base theory: singletonDefTheory explicitly defines c and has a model, yet it entails the old-language sentence forall x y, x = y, which the empty {P}-theory does not entail; so it is not Conservative over the empty theory and does not have the ExpansionProperty over it (fnExplicitlyDefinable_satisfiable_not_conservative).

#### Non-claims of 6. `expansion-property-implies-conservative`

- The converse fails: conservative_not_implies_expansionProperty.
- Along the non-injective morphism ιCollapse from {a, b} (two 0-ary relation symbols) to a language with one 0-ary relation symbol, the empty theory over the target language is not Conservative over the empty theory over the source language and does not have the ExpansionProperty over it (noninjective_hom_empty_theories_not_conservative).
- Terminology: ExpansionProperty is what algebraic specification often calls model-theoretic conservativity, and Conservative is consequence-conservativity (terminology remark; no source is cited for it here).

#### Non-claims of 7. `axiom-p-c-not-conservative`

- An axiomatized symbol here models unchecked first-order axioms about a fresh symbol. It is not a model of Lean's opaque keyword (which requires an inhabited type and attaches no characterizing axioms) or of @[irreducible] definitions (which keep one fixed body); these comparisons are informal (not proved here).
- Axioms that admit a lawful interpretation in every model of the base theory give conservative extensions (expansionProperty_implies_conservative).
- The axiom P c also leaves c undetermined: it is not explicitly definable (axPc_not_fnExplicitlyDefinable).

#### Non-claims of 8. `fresh-constant-not-conservative-with-empty-carriers`

- For every signature L and theory T over L, adding a fresh constant with no axioms is conservative iff T entails exists x, x = x (fresh_constant_conservative_iff_entails_nonempty; the positive direction is fresh_constant_conservative_of_nonempty_models).
- The link to Lean's requirement that opaque constants have inhabited types is an informal analogy (not proved here).
- Explicit definitions are unaffected: a defined constant has a closed definiens (defExt_conservative).

#### Non-claims of 9. `conservative-not-implies-expansion-property`

- T = Th(N0) is a complete theory given as a predicate on sentences, not a recursively axiomatized theory.
- The standard compactness-based characterization ('T' is conservative over T iff every model of T is elementarily equivalent to a reduct of a model of T'') is not proved here.
- Proof note: M0 |= Th(N0) is shown by a back-and-forth argument for one unary predicate with infinite extension and complement; the non-expansion uses Cantor's diagonal argument; compactness is not used.

#### Non-claims of 10. `axext-entails-iff-lawful-interpretations`

- Reference point: this is the definition of semantic consequence restricted to expansions; it is included for use by the other cards.
- An axiomatized symbol here models unchecked first-order axioms about a fresh symbol. It is not a model of Lean's opaque keyword (which requires an inhabited type and attaches no characterizing axioms) or of @[irreducible] definitions (which keep one fixed body); these comparisons are informal (not proved here).
- Conservativity of an axiomatic extension follows from existence of a lawful interpretation in every model of the base theory (expansionProperty_implies_conservative), not from uniqueness; the loose characterization WeakSortSpec is satisfiable yet does not determine a function (weakSortSpec_satisfiable_not_determines).

#### Non-claims of 11. `weak-sort-spec-admits-natsort-and-weirdsort`

- WeakSortSpec is satisfiable: existence without uniqueness (weakSortSpec_satisfiable_not_determines).
- AtMostOneLawful alone is vacuous for an unsatisfiable characterization (false_spec_atMostOneLawful_not_determines); the positive counterpart for StrongSortSpec states existence as well (strongSortSpec_determines).
- Does not say which lemmas a library should state, or that other weak characterizations fail in the same way.

#### Non-claims of 12. `strong-sort-spec-determines-natsort`

- The uniqueness part follows from antisymmetry of <= on Nat through List.Perm.eq_of_pairwise (two lists that are sorted by an antisymmetric relation and are permutations of each other are equal); existence (natSort_strongSortSpec) uses totality and transitivity through the merge-sort library lemmas. For a preorder that is not antisymmetric, uniqueness can fail (not proved here).
- The statements are about <= on Nat; other orders and element types are not treated.

#### Non-claims of 13. `label-deciders-agree-on-examples-one-misses-spec`

- Does not say which of the two deciders is wrong; that depends on Spec x0.
- Deciders are Boolean-valued functions; computability is not expressed as a proposition. memDecider Pos is executable when the supplied DecidableEq instance is computable; an instance exists classically for every type, and computability is outside the formal statement.
- The deciders are built from the labels alone; deciders that consult further information are not addressed.

#### Non-claims of 14. `unrestricted-decider-not-certified-by-finite-examples`

- Escape hatch: the decider ranges over all functions a -> Bool. Within a restricted class, finite examples can certify on an infinite domain: for threshold deciders x |-> (j <= x) on Nat, agreement with (k <= .) on the two examples k - 1 and k certifies the decider (threshold_examples_certify).
- Rules out finite example lists as certificates of correctness over the unrestricted class; it does not make examples useless as falsification checks that reject wrong definitions.
- Given d proved equivalent to a reference definition ref, d decides Spec iff ref matches Spec (decides_iff_reference_matches_spec): an equivalence theorem moves the trust to ref.
- Deciders are Boolean-valued functions; computability is not modeled.

#### Non-claims of 15. `adjrel-iff-pairwise-on-all-lists-iff-transitive`

- The direction from List.Pairwise r l to AdjRel r l holds for every r and l (pairwise_implies_adjRel; its hypothesis is tight by pairwise_implies_adjRel_ce).
- For one fixed list, transitivity of r on the list's elements suffices (adjRel_iff_pairwise_of_transOn) and is not necessary (transOn_not_necessary_for_single_list).

#### Non-claims of 16. `adjrel-iff-pairwise-of-transon`

- TransOn r l lets the three elements range independently over the members of l, with repetition and ignoring list positions (so [0, 1] fails TransOn (!=) via 0, 1, 0; ne_not_transOn); a version restricted to positions i < j < k is not stated.
- Not necessary for a single list (transOn_not_necessary_for_single_list).

#### Non-claims of 17. `transon-not-necessary-for-single-list`

- Uniform agreement over all lists still requires transitivity (adjRel_iff_pairwise_on_all_lists_iff_transitive).

#### Non-claims of 18. `stored-formula-stable-under-expansion`

- Reference point: the same statement as the infrastructure lemma sat_map (structural induction on formulas).
- Stability is relative to the reduct: reinterpreting an old symbol can change a truth value (stored_formula_stable_ce_reinterpreted) but need not (reinterpreted_symbol_need_not_flip_truth).
- Along the non-injective morphism ιCollapse from {a, b} (two 0-ary relation symbols) to a language with one 0-ary relation symbol, the empty theory over the target language is not Conservative over the empty theory over the source language and does not have the ExpansionProperty over it (noninjective_hom_empty_theories_not_conservative).
- Displayed text is not stable under environment extension in the toy elaborator (default_numeral_change_flips_truth, new_coercion_flips_truth, new_instance_flips_truth).

#### Non-claims of 19. `text-not-stable-under-env-extension`

- Env.elab computes one join type for both sides of a comparison and pushes coercions to numeral leaves, including inside ascribed subterms (so - in (0 : nat) - (1 : nat) < (0 : int) becomes integer subtraction after the coercion is added); Lean 4 elaborates (0 : Nat) - (1 : Nat) at Nat before coercing (not proved here).
- A changed elaboration need not change truth (elab_change_without_truth_change).
- Notation and name-resolution changes are not modeled.

#### Non-claims of 20. `elab-preserves-check-iff`

- Reference point: the checkers are List.all over decidable equality of elaboration results; the theorem is definitional.
- ElabInvariantOn is symmetric (elabInvariantOn_symm) and can reject an extension that changes no previously accepted string: adding the coercion nat -> int to a coercion-free environment preserves every accepted string of the whole surface language but is not invariant on [sCoe], which it newly accepts (additive_coercion_preserves_but_not_invariant).
- ElabPreservesAccepted ignores strings rejected under e; whether a string is accepted is the separate check (e.elab s).isSome.
- Equal stored syntax read under the same interpretations of its symbols has the same truth value (stored_formula_stable_under_expansion, relative to the reduct). Reinterpreting a referenced symbol can change a truth value (stored_formula_stable_ce_reinterpreted) but need not (reinterpreted_symbol_need_not_flip_truth).

#### Non-claims of 21. `adequate-specconservative-implies-translated-domain-entails`

- Consequence: under SpecConservative, a specification contributes nothing toward a requirement over LE; whenever K, Spec |= R holds, the translated K alone entails the translated R. In the setting with control and visibility, the analogous criterion ConservativeFor rejects the relatively consistent (SpecRelConsistent) and adequate specification of crossing_control_spec_relConsistent_not_envConservative.
- The expansion-property criterion collapses in the same way: under SpecExpansionProperty, Adequate holds iff the translated K entails the translated R (specExpansionProperty_adequate_iff).
- The conclusion is about the translated K. Reading it back as K |= R follows when the change of vocabulary is itself conservative (Conservative ι K (K.map ι), by the definition of Conservative); without that, the reading can fail: the empty theory over the target language (which has the same models as the translated empty theory) entails a translated sentence that the empty theory over the source language does not, for a fresh constant over empty carriers (fresh_constant_not_conservative_with_empty_carriers) and for a non-injective morphism (noninjective_hom_empty_theories_not_conservative).
- This generic setting is not the reference-model split of Gunter et al.: there K and R may mention machine-controlled shared phenomena and the specification uses a smaller vocabulary; see specRelConsistent_adequate_ev_requirement_implies_domain_entails.

#### Non-claims of 22. `relconsistent-ev-requirement-implies-domain-entails`

- The theorem assumes the requirement is a translated LEv-sentence. For a requirement that mentions hidden environment phenomena the conclusion can fail: a relatively consistent specification meets a requirement that K alone does not entail (crossing_control_spec_relConsistent_not_envConservative).
- SpecRelConsistent renders formula (5) of Gunter et al. model-theoretically, with all phenomena interpreted over one shared carrier; this correspondence is a modeling bridge (derived), not a kernel-checked fact about their notation.
- Time, the machine M and the program P of the reference model are not modeled.

#### Non-claims of 23. `crossing-control-spec-relconsistent-not-envconservative`

- One example: it shows that ConservativeFor over the environment-controlled vocabulary fails for a specification that is adequate and SpecRelConsistent; it says nothing about how often this happens. Calling this control legitimate is the reading of SpecRelConsistent as the relative-consistency condition of Gunter et al. (derived, modeling bridge).
- Whether gate -> not car is true of a real crossing is a domain assumption of the example, not a proved fact.
- Name: 'envConservative' in the theorem name stands for ConservativeFor ιEWA domainA (withSpec ιSWA domainA specA), consequence-conservativity of domain knowledge plus specification over the domain knowledge for sentences over {train, car}. It is neither the generic SpecConservative of the vocabulary-extension setting nor Conservative ι T T' along a signature morphism ι.

#### Non-claims of 24. `crossing-restricting-spec-violates-env-input-condition`

- The universal part is stated for this setting (car environment-controlled and visible to the machine, empty domain knowledge). In the different setting of crossing_control_spec_relConsistent_not_envConservative (car hidden, domain knowledge gate -> not car), an adequate specification that is SpecRelConsistent exists.
- Calling the failure an assumption about the environment is the reading of the relative-consistency condition in Gunter et al.; it is a modeling bridge (derived), not a separate theorem.
- Proof detail, not part of the statement: the witness for not SpecAcceptsEveryEnvInput is the one-point model in which train and car both hold; no structure on the shared phenomena with that train and car satisfies specB. The universal part follows from specRelConsistent_adequate_ev_requirement_implies_domain_entails.

### Escape hatches

- `unrestricted-decider-not-certified-by-finite-examples` is defeated by restricting the candidate class (threshold deciders on Nat: `threshold_examples_certify`), by a finite domain exhausted by the examples (`exhaustive_examples_certify`; tightness witness `unrestricted_decider_not_certified_ce_finite`), or by an equivalence theorem against a reference definition (`reference_equivalence_certifies`, which moves trust to the reference: `decides_iff_reference_matches_spec`, `reference_equivalence_moves_trust`).
- `fresh-constant-not-conservative-with-empty-carriers` is defeated when the base theory entails that the carrier is nonempty (`fresh_constant_conservative_iff_entails_nonempty`).
- `axiom-p-c-not-conservative` does not extend to axioms that admit a lawful interpretation in every model of the base theory (`expansionProperty_implies_conservative`).
- `relconsistent-ev-requirement-implies-domain-entails` does not extend to requirements that mention hidden environment phenomena (`crossing_control_spec_relConsistent_not_envConservative`).
- `adequate-specconservative-implies-translated-domain-entails` concludes about the translated domain knowledge; reading it back over the base vocabulary can fail along a non-conservative change of vocabulary (`fresh_constant_not_conservative_with_empty_carriers`, `noninjective_hom_empty_theories_not_conservative`).

### Tightness status

Every recorded hypothesis is `tight` (with a proved counterexample in the stated witness class) or `harmless` (the `[DecidableEq α]` instance of card 13). No hypothesis has `unknown` tightness.

### Not examined

- Beth's definability theorem (the converse of card 5) and the compactness-based characterization of conservativity by elementary equivalence (card 9).
- Explicit definability of relation symbols, and definitions of function symbols by formulas with a proved unique-existence condition.
- Kernel delta-reduction, reducibility settings, `opaque` and `@[irreducible]` in Lean; type definitions in HOL.
- Lean 4's real elaborator, notation, name resolution and instance priorities.
- Time, the machine M and the program P of the reference model; multi-sorted or temporal phenomena.

### Disproved or dropped statements

None. Every statement recorded for this package is proved as stated; no statement was found false and none was dropped.

## Evidence

**Kernel check.** The library builds with `lake build` under `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) with no errors and no warnings. Lean sources contain no `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern]` or `unsafe`, and no `axiom` or `opaque` declarations. Basis: execution (Lean kernel check). An axiom audit with `Lean.collectAxioms` over all 1038 declarations of the library's modules finds no axioms other than `propext`, `Classical.choice` and `Quot.sound`; the per-declaration record is `audit/axioms.json`.

**Statement and closure hashes.** For every Lean name referenced by a card in `results.json` (results, tightness counterexamples, non-vacuity witnesses, positive controls, and, under `lean_names`, the further theorems cited by name in ledgers, non-claims and escape hatches), `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (the sorted list of `name : type := value` for every package constant reachable from the statement, theorem bodies excluded). The table lists all 92 of them with the axioms of each declaration; their statements are quoted in the cards or under **Auxiliary lemmas cited by name (verbatim)**. Definitions are not listed separately, because the statement hash of a definition covers its type and not its body; a definition's body is recorded through the closure hashes of the statements that reach it. Every definition, structure and inductive type quoted in this report lies in the closure of at least one statement in the table, except `SpecAddedConsequence`, which no recorded statement reaches.

| Lean name | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :-- | :-- | :-- | :-- |
| `additive_coercion_preserves_but_not_invariant` | Quot.sound, propext | `a17acfdd10864542ca225fd3793f96873c3a3f830c8e86a36d6ac126001cdd27` | `eae83e3474f233d48b9e4c909f8fe7f6ceb6f6cf80e20fccb586286aa862bfaa` (110) |
| `adequate_specConservative_implies_translated_domain_entails` | none | `5477f3d250cd3be40ca41d6210f6555857e5cb228178bd18082013a03c6eff87` | `3014530ac45830ee43b52b51d7e629ca349c8e03af6bf90db5c81c43b56c622f` (63) |
| `adjRel_iff_pairwise_of_transOn` | none | `1cd849d3403d24112058e033805c8af4c6a4a7bd9a92f918946eb820fb6e36f6` | `d503361774f14131ed0778e4fc433941a40537bdf39513b5fe1bd452e3f5c81e` (4) |
| `adjRel_iff_pairwise_on_all_lists_iff_transitive` | none | `fe48cd223cc0d82837ad9b6ded7972c6b6e3c755cff582d721e4d2e78ef2156c` | `efc3634135e9a13098316037000b5a36aad44c7d3cbb86f7db4e3954761cf0b4` (4) |
| `adjRel_ne_not_pairwise` | Quot.sound, propext | `3f4e3e2937688275c673c00a6219129e277ad71a933d19ce463257be657fdaed` | `d503361774f14131ed0778e4fc433941a40537bdf39513b5fe1bd452e3f5c81e` (4) |
| `axExt_entails_iff_lawful_interpretations` | Quot.sound, propext | `0440d9f70eb78f7dda6535b74f6409f3ec6e2e3c4be929fdd7611564e68dce83` | `43e8e066c24843e7a225e0ee83c6bd9acc0674a6da8eb5ccb2dfe23d6ede028d` (67) |
| `axExt_lawful_interpretation_exists` | none | `b759d5d7e481198db86bea44caff9860e3ef88dae24782914f2e938fa2028196` | `66b9ca2ec6e47633e3d6d8101f35f03cf68195b58315f40bc790fcdfe1413b78` (74) |
| `axPc_not_fnExplicitlyDefinable` | Quot.sound, propext | `7f90ecd8ddaceff3258a31dfa783cfa7f4c2638be95eae30c7201e82cb23c5f1` | `b166ffe565d780034f617bc4744fbc0aaf3d662f5fce0840a6c60481f50fa2c6` (75) |
| `axPc_two_lawful_interpretations` | none | `d0e94f736cab616f8f00af2b0245cab108934ba886c6ed6d6708f8a39e5a717a` | `f102a187260ed1e51e3b86fb2fe5f13105f4688ac5571341b3b49946dd2b78d5` (68) |
| `axiom_P_c_not_conservative` | propext | `1841f4a8e46c9407b997cc1884b78c87efb52549e04d89111dd63321a9fdfd71` | `085d96f5fa99350ccc14bea260660fa4652b5176eddb6475edcbcab9d48d9b50` (75) |
| `conservative_not_implies_expansionProperty` | Classical.choice, Quot.sound, propext | `52b89a99ada92a130ca4573cc754ced6d7e8c32f521f9597e9b97489ff0f4756` | `c1e18c2a23680e7c4d61fcc63c0cfab57cdbd37f9ceec35e9ae32d5a6669314f` (86) |
| `crossing_control_spec_relConsistent_not_envConservative` | Quot.sound, propext | `1058cec2e0d489bd5727aed181ab4d9ff5a47da9442e94ff09c42fbbcdcfb051` | `6cf19f230179520407c56d8a11580f485099ee5fe3913f895e5d729a20bce1d6` (101) |
| `crossing_restricting_spec_violates_env_input_condition` | Quot.sound, propext | `1023725316f9a987c2b10c2dd072baca84e465a42f0bfeecd87d1ae10d70a7ed` | `bdc72f54df6cdb8f93e804e43c9aaf6276e704d1a9d4dce43a4fd744d06ed354` (88) |
| `dTwo_deltaConv_examples` | Quot.sound | `0ad5039bc09d21f7ed7430185fd5150e1134a56c8276699a048ba083f3128fee` | `5bd69dd5d6b866bf96e8661725466ed85f21ad3a06ae72a1981c821e121559af` (94) |
| `dTwo_deltaConv_sound_and_unsound` | none | `d133c29998f890c6be4fccc84a99bdca6c3247fb5cc9c7fee071fde969c2fcb0` | `c8019e57d05cdf05232e8d80046f74614bb24fd4dcf88032d4079af5cc7621ae` (96) |
| `dTwo_three_not_models_defAxiom` | none | `3a73df89028dd23e6c19a9e889fd8b9f7ae2fd5a56f80a63af599a597a08ba5d` | `3004432eca92571a0950527f52fe201633f8ce4044914c78aa1cabd0e17470db` (99) |
| `decides_iff_reference_matches_spec` | none | `99742eb4d929f24c2bf03149a8341072e60c6df9ff0bd60822edbafd4bbe1014` | `4c1e80d575579c1d52e601d245995cd82cbbeb87828de0d92425515f746158c3` (1) |
| `defExt_axiom_nonvacuity` | none | `007459aa1d8ceda205a132d1dae76e63876d86142848a0d001f9f4f8f463dd17` | `31d9dd6c1a3f33fe8b56783e3f732acda83415906677ff1b3969ea621f511379` (105) |
| `defExt_conservative` | Quot.sound, propext | `35556d17e63934ca54205614de84cd69de286f97fe404325b435a5a88cbda7bf` | `223018512a1cf8ee41ef2268a8de6fdacef26d8cef50f856aa5b5cf9117ff864` (86) |
| `defExt_eliminable` | Quot.sound, propext | `6d11a420b837dcc6e0ef4254c44cae3b38d102b16b706af071f6a2edda15bb9b` | `4cc8ee2fb04c0f85a7021df0ef1bd2d9b9d78e42a4a42857157f493a3b45d656` (108) |
| `defExt_expansion_iff_of_axiom` | Quot.sound, propext | `58fe34982605dbf2dad09658539c265865cc4b1310058998c01d4c634b4a0739` | `1a96525dceb70f06d320a679974d1208a0a82cf1549b313ca3b4ba6ffbdb6b07` (85) |
| `defExt_expansion_unique_ce_axiom` | none | `71a6ea5dce8dee65d9d4dc9ae73b019d419ee7b14b8fb879ee63586363ef7fbe` | `b6b02a9ca2a89e858fdf1076df5bfdb263487a4db417e8527cc747731270faff` (91) |
| `defExt_expansion_unique_ce_reduct` | none | `7cad40e3d05b154253ecdce6890bdf8aa7ec3c06d497ab4b611d8c3c75c33603` | `24faf141b77ddd62da0cc4df312e46de345c705d012a4278521baaccaea9dcd3` (106) |
| `defExt_expansion_unique_of_axiom` | Quot.sound, propext | `e39303a0e10770ba5634b5a4026ce7074e830a138728dc85a214c43fbfb40976` | `1a96525dceb70f06d320a679974d1208a0a82cf1549b313ca3b4ba6ffbdb6b07` (85) |
| `defExt_expansions_eq_expand` | Quot.sound, propext | `caa32f3d00fdeaaf27bafa75dd4716c27c0664731af7773d9a7a543bde30b149` | `a726c35e6ab3672c720124c558f6e5adb8c155b42b530858ef3f0082bc5c7f00` (91) |
| `defExt_expansions_eq_expand_ce_not_model` | none | `99f7521d6ef27c0856f28987c3786e7302b48a1a23f8a6bbf8db64e0c9225518` | `ca88728434ba60c85de77b82f9eda24d3d0862e542bf5ffb5817ac091f8754bb` (111) |
| `defExt_expansions_eq_expand_nonvacuity` | none | `168380177f288a5dace60c334860e18b96e6d992b34006ada9510fba65e4ee23` | `b3d122177950c851dfc03167d3651e82889f872df709dd8a6732775bca6ad193` (63) |
| `defExt_theory_has_model` | none | `e1bea69ba12674ed163273828ca91115a138c610624f597e688e318969786ad4` | `2b01dbae2cd3e36b821ac455cc00defe8578f6e94325cf8adc41f475edec7082` (111) |
| `defExt_unfold_equiv_ce_axiom` | Quot.sound | `4238fb139f81f04478a8d7d5f0ae447f4646050827e71da66c16c47535e00fb5` | `0808ec7908cf77633489d5cc907274b234a1804b43bc23769fce619ea510cbd9` (119) |
| `default_change_preserves_examples` | Quot.sound, propext | `c9872d7ab3095ca827f5ad11edfef3b7b277e78af4afbd61fe974a9daf3472f4` | `507af96d992a2edad3c6d4f5c57960a19f4055804f9cf7efa392db2933dde339` (226) |
| `default_numeral_change_flips_truth` | propext | `2cea5588cfd30482571e9f2cc7d0f98104452e2e415d1d09323ba9a31e6bedc1` | `d2848e89c6d5686153368c080c648442b7e05a5cec26c2ecb5a358cde816d29c` (150) |
| `defnFn_theory_fnExplicitlyDefinable` | Quot.sound, propext | `1ed3d5b980c922216ff5269708742d99081bae964c31e5b9a67c2a3d384c73d6` | `99ca30a9469bc493a080efc6567e4f18fba1626dae9bdd64e8a45729476b15a2` (87) |
| `elabInvariantCheck_iff_elabInvariantOn` | Quot.sound, propext | `d9ea4d7dde2c889de8681e7f224d4bd19ed6b85f6b5cd54b9deff6f4130d738a` | `465a959948e38c923b42e38cad979ddc8355eb0695ee15890e2e8dbbad9e84bf` (221) |
| `elabInvariantOn_symm` | propext | `59e411d34de5d900181ed7ed30732673faaa1f7f4a55ac17149f1deb331c0875` | `4d7af4e6b7b213ad96a41722e9fa84e259063c725ea1b73dc6bba8b8657be6e1` (104) |
| `elabPreservesCheck_iff_elabPreservesAccepted` | Quot.sound, propext | `81695f3b35b200930fdcc1a7fa0decbce682d4e954eb56dc3541625187ec94cd` | `2671dda4ff296fe50cb45881055e885cfe92e05bc1b91549cf197cc462db6e08` (222) |
| `elab_change_without_truth_change` | Quot.sound, propext | `541ef4910845ae5755d27cde57c2f556621095798dc6fd50336c74c177d7c839` | `698b0825e9317e19d5dfc81d585ddfa9bf30cd311d09e0bb4e642fecf44869ba` (149) |
| `ev_requirement_ce_not_adequate` | Quot.sound, propext | `f4157e660eb9d2af6af6de8317261f7391b5961eb6797c4cbff076cb3b209607` | `6272e9481947eaa9f776f0d1646b2eb6ed9eebdce6b5099a310e0d8f4ed6d44d` (82) |
| `ev_requirement_ce_not_relConsistent` | Quot.sound, propext | `bc6194a35932b7362793681599f53adeba077708639f27387a6868fa05028a8f` | `85690bdbb0f5741ca59da481678827a5570ea0ba75e4ba468e491cdc75aee708` (84) |
| `ev_requirement_nonvacuity` | Quot.sound, propext | `50e3bd7822ee5593060289c619e020d7a18a918bbe5af4f5fbe40ce524a71b70` | `a5e89735b18cda13bc0cfef6b257f0d733f6abfb2359e98bde56375b1c0a4069` (87) |
| `exhaustive_examples_certify` | none | `d98705357c71a5dc00e4d915ffbcae782a28e64b7de292d51b895b8b8f002261` | `c0f10dabcb473361515982e571d884506a986db6efcd39029ee39af6524eb6bc` (2) |
| `expansionProperty_implies_conservative` | Quot.sound, propext | `5558d33ee4b8512e5203e999bef92046cfe496692102935a18a106c42b168574` | `4fe81f144a0289557a1047391e77138c47a0bc0731a873fc176246de99af1fbe` (61) |
| `expansionProperty_implies_conservative_ce` | propext | `1ac768764c2e7a1d8d33cb7a2be884cf1445397f5372465e0219a689db8284c7` | `5a40164c20b244d10a36e1835f46210909b8249a0e801c077b3a2cbf0f75353e` (73) |
| `expansionProperty_nonvacuity` | none | `ee02f29e423a9e38e8cee2a0ae82be71b5a64829dfdf40eacc0af19f95aab69d` | `7d6c2d391b80a0214174d3ae868a0df94e6009aba10ecff43daa1715dbf9e9d2` (62) |
| `false_spec_atMostOneLawful_not_determines` | none | `bcd5af8e86d72f8382593f4c1cabfe1ecfda2a7d84911704108689678d742dc8` | `ba93221996e910938d74df25ad867d8d0923af41d4c42f85be4585d225fc5b0e` (2) |
| `falsum_theory_fnExplicitlyDefinable_no_model` | none | `9b5e4adb6bc7a52d32e44ab6ac6a43e84933dbdd154382b85476887261b40537` | `c3b3dbe16b7d8e975ce92aedd4751d4767c0c5ba0aa9ac40d172d0af42aba237` (73) |
| `fnExplicitlyDefinable_expansion_unique` | Quot.sound, propext | `d7513a13ea55a7f4aa9c94d9c5ff82ccaa33e2d832ea69a2aca2ef57f8ec6b18` | `1b3ff9e7019ed2dc96f100ef4a2a2ed042d1e5efa7364fdb7f6f1598e8cf1a7c` (70) |
| `fnExplicitlyDefinable_expansion_unique_ce_model` | Quot.sound, propext | `e0a44cf3ed51ab0938e6e88f51405619dd8a2083e022aaf8fa8be19bc0abb39d` | `c8b4dcc2984e689f7bcf1c5e14e8c1ac830a54223df6905fbb07ca8dde6c9a2f` (115) |
| `fnExplicitlyDefinable_expansion_unique_ce_reduct` | Quot.sound, propext | `6c29c4937f5306547c454363dc92e990f063a216523c80ae475fc0296c895788` | `afb49f655e31e1d4dfd19d6f07637a8b6df9d86c3b6fe1e3eee022180befd654` (116) |
| `fnExplicitlyDefinable_nonvacuity` | Quot.sound, propext | `96073d5668d16dd43b7cf04533724c7c61f9c1a41951a470bbdfd71eb35bcb90` | `86884e1df10fdde69aa8c548abcd7f290090bc07f5a34880d9ce548f39e28ec6` (114) |
| `fnExplicitlyDefinable_of_no_model` | none | `1e849db712d3b4382a3a687ee74e3d4199d0b3b855adde44f886f77697204751` | `1033f5c2687acd5d8b083682f5bf1be6deda63090534c782f0c969e955837fa5` (69) |
| `fnExplicitlyDefinable_satisfiable_not_conservative` | Quot.sound, propext | `5a3556ba659bb717f6bb976e50a0d739201fb58a33dd4f48e3e358c102673743` | `49ff81c60dbd635dde59890efe82091c1974506eed6783c0ab7a146577395fbe` (84) |
| `fresh_constant_conservative_iff_entails_nonempty` | Quot.sound, propext | `9d9573de2d379f071c5414e34379f63874652b1119e19dd3d88aca1a613393c7` | `a064ca547f43bccb5a9527248a3117c2f0183ef56eccc886a4cab30f17e14e0a` (67) |
| `fresh_constant_conservative_of_nonempty_models` | Quot.sound, propext | `d2196cc4e1a366a0bb230b3b30d3e2eba0d71ed02713b049554a8205ae540d20` | `a064ca547f43bccb5a9527248a3117c2f0183ef56eccc886a4cab30f17e14e0a` (67) |
| `fresh_constant_not_conservative_with_empty_carriers` | propext | `65bdad75fa284f167336e01b99b013fa772ab4578263d67979e9b2b52ab7b799` | `aaae9d3f01e5caa4a78d1f5631a9686365cdda4b49014d7f89bf476cb8060281` (70) |
| `label_deciders_agree_on_examples_one_misses_spec` | Classical.choice, Quot.sound, propext | `b49a92c2b74f7d8c1832a183db4fcea8b92c7bef6a120ccbf7b51bcff3cb516e` | `592e969855cb9f991ba57443cf82430469f6745e810d46b6774c1a00e63fc6d8` (4) |
| `label_deciders_ce_labels` | propext | `5d70603c783635d030f842aab3749a82131657b0b43fd570095d4355df3e40e1` | `43abe2aaaaed2b6721d36bc496d714236a892a48f15f167c9c30cfd69f76035c` (3) |
| `label_deciders_ce_point` | propext | `9738deb088e4a08fbda46ac2265afc506cfdf67103ba203a66eb8f0564f872b5` | `592e969855cb9f991ba57443cf82430469f6745e810d46b6774c1a00e63fc6d8` (4) |
| `label_deciders_conclusion_without_hypotheses` | Quot.sound, propext | `e49abf0ee12ffa7b6a746d0b587f633b647dac2b7b784bd564c12a18b850fe39` | `592e969855cb9f991ba57443cf82430469f6745e810d46b6774c1a00e63fc6d8` (4) |
| `label_deciders_nonvacuity` | Quot.sound, propext | `91ae6d70100c1bfbd3e128242a0d5783956ecb63e0f6aaf981d4eab026a3d240` | `435faa635d830ab19933bdc9d7c9e4ad008796a0a1b805f1428fac09f2162e34` (1) |
| `models_defAxiom_iff_deltaConv_sound` | Quot.sound, propext | `b2edee127470f2e271277fb2e040ac02347a364834e46a77181c6bac11793c47` | `5da72a5646e391aae288608326fe43d0fd8e895f704e80c9cdc29152b65ba6b9` (101) |
| `models_defAxiom_iff_unfold_preserves_sat` | Quot.sound, propext | `b85019d42f881ebe3586ca183ee5e49e7c7be17feac592ef99c56ecc4eaa0389` | `f25a6d13c071a2cf8c9ecc1129574f2048290d0af8f44eecbd3b2adbe8314ee6` (101) |
| `natSort_strongSortSpec` | Quot.sound, propext | `ad8b0d873a0b972cc50782d710b942cff0229d7d8d7293284bc6a722f8c57f73` | `5c23722f4dff730e161ff62fbb4ed1f9f673d12c38797b7a6aa24dc9e82b1196` (2) |
| `ne_not_transOn` | Quot.sound, propext | `5921faa751c672aa7bafc82be9182664002c73b35a2758500b5379e7f09eaf5c` | `ad23ba9d473c1ced9a04f63cc5d187278e848ccbd5a0cad42e730522eff8a479` (1) |
| `new_coercion_flips_truth` | propext | `2f404f127feacc9e467c7c43e9fce026e8a26fbf72b84dc4ca1305710e71e2b1` | `c8802cd2b0bc8b91f9fe85ea8324a9ce99b62c5bcab777751057517c2fca5ae2` (150) |
| `new_instance_flips_truth` | propext | `e9a4fa3f4288b7d194490a6da8dbd90654a0906621af006d8b00a8059ca5d459` | `115c39f0d55fcdbb911e8454853f2ab334a4c5ba04ba34b69f10cf2add46b679` (150) |
| `noninjective_hom_empty_theories_not_conservative` | none | `b77ebc268f367cad19e7dfab6a29e13844d9355381976a63bbf7e6efb754cf31` | `400333223dd37811d798590c946a86b3f3d6336bcb43f0bf02bf4d501d24bbad` (72) |
| `pairwise_implies_adjRel` | none | `e28fd6a924a9f38bf7ac0d01576f0efc4245dbbc8845263628420e9aab3ffc3a` | `086f0559a6ab5ab135fd29a1dd862c4f3b22acf226153b8719520515b26d062b` (3) |
| `pairwise_implies_adjRel_ce` | none | `abbe0f58f0be6f504019678ef651c725a5010f33d0cd69bc5f7276be4d41450c` | `086f0559a6ab5ab135fd29a1dd862c4f3b22acf226153b8719520515b26d062b` (3) |
| `reference_equivalence_certifies` | none | `689c2000765d4d81a2a13bf5dcc57cb2b5389e8ffb906900add9084eb596d8ab` | `4c1e80d575579c1d52e601d245995cd82cbbeb87828de0d92425515f746158c3` (1) |
| `reference_equivalence_moves_trust` | none | `1165f47d91f2694b94c7cc6141b29be2b7c779a48dcae90e4a4011ff806fa9b8` | `4c1e80d575579c1d52e601d245995cd82cbbeb87828de0d92425515f746158c3` (1) |
| `reinterpreted_symbol_need_not_flip_truth` | propext | `d00ac62e60476c706b7ca08245e5faefb2019048068f4035c9893f917caa06c7` | `0e6afc8c3b2c7397cc74985c6f6e3e8a560b49bb655f02d3f4ab08c4f00a0efd` (49) |
| `sat_map` | Quot.sound, propext | `d55b95e4929b8f3a49b278654e30d6fc35bd88e1d2fde16227b8c65ad6a46afd` | `4e9cc5a972c6894654d2be488eab9de8e4f817b5f5fd5d4d1bbbd4f593e8325e` (53) |
| `sorted_readings_nonvacuity` | none | `06889211eb25afd8f4d144282341126d680ed00fe69869e2afb028c383a59b9c` | `ed35746a7c0ee7cd4880ae6673b720ede9f27b6564e97752956a61bc0cafebb7` (5) |
| `specExpansionProperty_adequate_iff` | Quot.sound, propext | `6fb870d50befb358f0b4cdc8f8f3d219d6a44246e0c9c54a64f4865b8c89ecea` | `fe2d1a16d7458aa993b72734c72ef17131d41ffc8fcb0fe8162dbd9e83055d2c` (64) |
| `specRelConsistent_adequate_ev_requirement_implies_domain_entails` | Quot.sound, propext | `a141aad88748daa9ccd925fb6208d6b330f8b5d7405dd6aabb6f3adf3e14b30a` | `71b236851620632a9743498a202e0c70d336df3fc77f4bbd8c27d45fe38b8275` (66) |
| `stored_formula_stable_ce_reinterpreted` | propext | `468ab703f68850ea5ce0e7c4c67056a6e0f9541f7907c9b778a87a0d2d4f5340` | `bbbae7a047a71de28d2102d1c0342e01e1e745b35703f54d0ead840c13f5890e` (64) |
| `stored_formula_stable_nonvacuity` | none | `521dbd03ea046fe5733eca2ed7c89543af0ecd7f2d72f1a629b016cd83b71ac3` | `256443ffebaa833821dae60ff6be0bcb43b033efd316c41bf1080bd81c341075` (28) |
| `stored_formula_stable_under_expansion` | Quot.sound, propext | `df0f842b112af1b4d2e451067f881376ad8a9354af2fb4b860646a2efed22720` | `4e9cc5a972c6894654d2be488eab9de8e4f817b5f5fd5d4d1bbbd4f593e8325e` (53) |
| `strongSortSpec_determines` | Quot.sound, propext | `0471c7dc594d309a9c054d9f8fbd052035deaa26a00dc4447789c1cb2db992db` | `2a61791e2fff3f6a68c12e437bb0e458a2782189b60b5d2525eea01ee623cb18` (3) |
| `strongSortSpec_iff_eq_natSort` | Quot.sound, propext | `df7e57d03645b704155b0724ed2019fe0a2f2da6786159279e17e517baec8a42` | `5c23722f4dff730e161ff62fbb4ed1f9f673d12c38797b7a6aa24dc9e82b1196` (2) |
| `threshold_examples_certify` | Classical.choice, Quot.sound, propext | `70874fcba5f1a653df93a63191b5540daa1f37360366655792dd1977ca6e917f` | `a008a9b6fba1c773c0a05498e1bc5d5b7a4919e1baf256582f113075fa7488f8` (3) |
| `threshold_examples_certify_nonvacuity` | propext | `bb3162d2d32210718ccc23dbbcbb8ac46f674beba7165146fbc89d1e14b5d700` | `26b6c93125b13b70ed185999776a3cd3fb60701ff624ea6982d2ec2c0bbb7fab` (2) |
| `transOn_not_necessary_for_single_list` | Quot.sound, propext | `ffc39221ac3dab820704ab29fcc2a3ab8e8da433f184d1b2e8b7893b77d16a50` | `d503361774f14131ed0778e4fc433941a40537bdf39513b5fe1bd452e3f5c81e` (4) |
| `translated_domain_entails_ce_not_adequate` | Quot.sound, propext | `e6beba485d3a006c16e731be4275574afebd91539e7a1dd724dc059099d8abd1` | `8f17a053fe8de22e4ced66601a773f807a27709e5b9bbe4c7bc81190d7c2e00e` (78) |
| `translated_domain_entails_ce_not_conservative` | Quot.sound, propext | `a2526d800d99e18edda19c7c3949ae2b3f0e754e7d1ed9435e99840d3aa55581` | `5449e5a1d12e71d89323bf1c1af5bbd4ea8e74417453ab990a5efc64a1bdfcb8` (81) |
| `translated_domain_entails_nonvacuity` | none | `55b492d4bedeeb72dc68dd870db94530c8e05e822d1cc1bbbabaecfd66d4edcf` | `fc5330bc3950a77e8d4cf00ffdb000492f189d5667ed1dff6ca5028df4c63ab8` (80) |
| `unfold_preserves_tru_without_defAxiom` | none | `b14f876385f94821e8553a342079ce8cced795a1f79fb1f71bbba276e9a0d82b` | `81bbef76c744832060bf73caa872e820b8a173255aad5dfd821729c3c51ea7b6` (124) |
| `unrestricted_decider_not_certified_by_finite_examples_of_infinite` | Classical.choice, Quot.sound, propext | `524bd5ef0ae0bd5ad83f71a0e33130b9672ccab5f8bbdeb1cddef3bc2eb2d09a` | `333817e087f786724f78639f9bdb924bddcfbb7a6f67015858dd5e8e4d612c2c` (3) |
| `unrestricted_decider_not_certified_ce_finite` | propext | `7e639e6f8a916474f9faca42efd7d2441967f54e52f342a83de4bab09e774453` | `333817e087f786724f78639f9bdb924bddcfbb7a6f67015858dd5e8e4d612c2c` (3) |
| `unrestricted_decider_not_certified_nonvacuity` | Quot.sound, propext | `47bf0d588a421d035df6447a9bc5962c2e4f07d02d2df9ca1b0859b04c8cebc3` | `e88533118459e9c7935d42e0dc354662a22ff56cb19812475e2e998fe798d85d` (1) |
| `weakSortSpec_admits_natSort_and_weirdSort` | Quot.sound, propext | `6e5b39c6172983988be5fd914c6816957d7ecf01db1ad5a05a01ae1d8d59dd22` | `84fea1cc2c4852c60e595f897d43b5e85849a70bc1a17744e6339267b0b475d0` (4) |
| `weakSortSpec_satisfiable_not_determines` | Quot.sound, propext | `a9b5f3a59f3db8f161e51dc7a69b7ea6d521d7ca3e547e5872cb9c1a1407b992` | `e52af09b938f5a967e023f989f1fd5971775cb200383bf9fdd7cc426e29b50fd` (3) |

**Primary sources.** Checked on 2026-11-21 unless stated otherwise.

- Lean 4 core, `leanprover/lean4` tag `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`): `src/Init/Data/List/Perm.lean` line 530 (`List.Perm.eq_of_pairwise`), `src/Init/Data/Int/DivMod/Basic.lean` line 111 (`instance : Div Int`, Euclidean division `Int.ediv`), `src/Init/Data/List/Lemmas.lean` line 576 (`List.all_eq_true`).
- The Lean Language Reference, `leanprover/reference-manual` tag `v4.34.0` (commit `a6451f0647eb4dc46fce2dd0532331c59351f87c`), `Manual/Defs.lean` lines 489-490 (delta-reduction of defined constants in the kernel; reducibility in the elaborator) and 554-556 (opaque constants are 'not subject to delta-reduction in the kernel' and 'can only be used for types that are inhabited', quoted).
- Batteries, `leanprover-community/batteries` tag `v4.29.0` (commit `756e3321fd3b02a85ffda19fef789916223e578c`), `Batteries/Data/List/Lemmas.lean` line 423 (`List.isChain_iff_pairwise [Trans R R R]`).
- Rocq standard library, `rocq-prover/stdlib` tag `V9.2.0` (commit `8dd155bc10529814202f8f4c643e5ae6c2c88fa6`), `theories/Sorting/Sorted.v` lines 135-136 (`Sorted_StronglySorted`).
- Carl A. Gunter, Elsa L. Gunter, Michael Jackson and Pamela Zave, 'A Reference Model for Requirements and Specifications', IEEE Software 17(3):37-43, 2000, DOI 10.1109/52.896248 (pp. 38 and 40: vocabulary rules and formulas (4) and (5)).
- Pamela Zave and Michael Jackson, 'Four Dark Corners of Requirements Engineering', ACM Transactions on Software Engineering and Methodology 6(1):1-30, 1997, DOI 10.1145/237432.237434 (Section 4.1, p. 11; p. 19; Section 6.3, p. 27).
- E. W. Beth, 'On Padoa's method in the theory of definition', Indagationes Mathematicae 15 (1953), pp. 330-339, DOI 10.1016/S1385-7258(53)50042-3.
- Ondřej Kunčar and Andrei Popescu, 'Safety and Conservativity of Definitions in HOL and Isabelle/HOL', Proceedings of the ACM on Programming Languages 2(POPL), Article 24, 2018, DOI 10.1145/3158112.
- Andrzej Mostowski, Journal of Symbolic Logic 16(2):107-111, 1951, DOI 10.2307/2266682; Theodore Hailperin, Journal of Symbolic Logic 18(3):197-200, 1953, DOI 10.2307/2267402; Sally A. Goldman and Michael J. Kearns, Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003 (bibliographic records).
- Books cited by section (not quoted): Shoenfield, Mathematical Logic (1967), Section 4.6; Hodges, A Shorter Model Theory (1997), Section 2.6; Mitchell, Machine Learning (1997), Sections 2.7.2-2.7.3. The record for Padoa (1901) comes from a secondary bibliography; the cards say so.

Primary-source content is cited as prior art or as the basis of a modeling bridge; no paper or library above is formalized in this package.

## Revalidation

Requirements: `elan` (which installs the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

The script copies `lean/` to a temporary directory and runs `lake build`; scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations; runs a generated Lean program that computes, with `Lean.collectAxioms`, the axioms of every declaration of the library (allowed: `propext`, `Classical.choice`, `Quot.sound`); and recomputes, for every Lean name referenced by `results.json` and every name in `audit/statements.json`, the SHA-256 of the statement (`repr` of its type) and of its definition closure (types and values of every package constant reachable from the statement, theorem bodies excluded), comparing them with `audit/statements.json`. It prints `REVALIDATED` on success. The package itself is not modified.

A shorter check of the build and of per-theorem axioms, with `lake` and no Python:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` (outside the library target) imports `Toy` and runs `#print axioms` for every theorem named in a card or cited above; each output line must list a subset of `propext`, `Classical.choice` and `Quot.sound`, or report that the declaration depends on no axioms. A change to any Lean definition reachable from a recorded statement changes its closure hash, so a failed hash comparison means the corresponding card must be re-examined.
