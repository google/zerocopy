# First-order unification, the occurs check, and impl-overlap coherence (Lean 4 formalization)

## Summary

This package formalizes, in Lean 4 without Mathlib, a toy theory of first-order syntactic unification and of the impl-overlap check built on it. It covers soundness, idempotence, most generality, completeness and a termination measure of a solved-form unification algorithm; what changes when the occurs check is deleted, over finite terms and for a depth-indexed reading of infinite unfoldings; one-sided matching versus unification; and what an overlap checker's "disjoint" verdict guarantees in the presence of where-clauses, negative reasoning and downstream impls under a toy orphan rule. All 19 results have tier T0 or T1 (known or folklore results restated or made precise); none is claimed to be new. Every statement is kernel-checked.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers, rustc's coherence checker, the Rust orphan rules or the `#[fundamental]` attribute. Connections to those systems are stated separately, as `derived (modeling bridge)` lines under Findings.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Design question.** Type checkers and trait solvers rely on first-order syntactic unification: a coherence checker decides whether two impl headers overlap by unifying them. When is the algorithm sound, complete and most general; what goes wrong without the occurs check; and what does a "these impls do not overlap" verdict guarantee once where-clauses, negative reasoning and downstream impls are taken into account?

**The occurs-check results, with their exact quantifier structure** (these are the results most easily over-read):

- *Deleting the occurs check breaks soundness, by concrete counterexamples* (result 6, existential). On the input X =? Box X the occurs-check-free variant `unifyNoOC` returns [X ↦ Box X], which is not a unifier. On the single concrete input (X, (X, (Y, Z))) =? (Box X, (Box Y, (Vec Y, Z))) it returns an association list that binds X twice and whose k-fold unfoldings of the two sides disagree at depth 2 for every k (`eqUpTo 2` returns `false`). The package does not prove that this input has no solution among infinite trees (no infinite-tree semantics is formalized), and it says nothing about inputs other than the two shown.
- *A depth-indexed soundness theorem holds under a distinctness hypothesis* (result 8, universal). For all terms s, t and every σ: if `unifyNoOC s t = some σ` and the left-hand variables of the returned list σ are pairwise distinct, then for every depth n there is a number k such that the k-fold unfoldings `iterSubst σ k s` and `iterSubst σ k t` agree at every position of depth below n (`eqUpTo n` returns `true`). Removing the shadowed binding from the list of result 6 gives a duplicate-free list that acts identically on terms and still fails (`dupσ_dedup_still_fails`), so the hypothesis is about the returned list, not about the substitution it denotes.
- *False disjointness is impossible for renamed-apart headers* (result 19, impossibility, universal). For all impls i and j: if their self types share no variable (`VarsDisjoint i.selfTy j.selfTy`) and the occurs-check-free checker says disjoint (`overlapCheckSaysDisjointNoOC i j = true`), then `¬ HeadersOverlap i j` (the traits differ, or the self types have no common ground instance). Positive control: without renaming apart, the checker says disjoint for two headers that overlap (`noOC_check_false_disjoint_without_renaming`).
- *False overlap does occur* (result 18, existential). For the renamed-apart pair impl<T> Tr for (T, T) and impl<U> Tr for (U, Box<U>), which have no common ground instance (`¬ HeadersOverlap`), the checker with the occurs check says disjoint and the occurs-check-free checker does not. Results 18 and 19 together do not say that false overlap is the sole cost of omitting the occurs check: on the renamed-apart pair (T, (T, T)), (U, ((U, U), (U, U))) the occurs-check-free run exhausts every fuel (`unifyNoOC_outOfFuel_example`).

**Results** (each sentence is the result's plain claim; numbering is used throughout this report):

1. **`unify-sound-idempotent`** (theorem, T0). For finite first-order terms s and t, if unify s t returns some σ, then σ unifies s and t (σ s = σ t syntactically) and σ is idempotent (σ (σ u) = σ u for every term u).
2. **`unify-most-general`** (theorem, T0). For finite terms s and t, if unify s t returns some σ and τ is any unifier of s and t, then τ (σ u) = τ u for every term u; hence σ is more general than τ, with τ itself as the factor.
3. **`unify-complete`** (theorem, T0). For finite terms s and t, if some substitution τ unifies s and t then unify s t returns some substitution; consequently unify s t = none exactly when s and t have no unifier over finite terms.
4. **`unify-termination-measure`** (theorem, T0). With the occurs check on (oc = true), for every equation list eqs and every initial accumulator substitution σ (arbitrary: σ need not be in solved form, since no pass of the algorithm branches on it), if fuel ≥ numVars eqs (the number of distinct variables of eqs), then run oc fuel eqs σ does not return outOfFuel.
5. **`occurs-failure-sound`** (theorem, T0). If a variable x occurs in a term u and u is not the variable x itself, then x and u have no unifier over finite terms.
6. **`occurs-check-removal-unsound`** (counterexample, T1). Removing the occurs check, and changing nothing else, breaks soundness: on X =? Box X the variant returns [X ↦ Box X], which is not a unifier, no finite unifier exists, and unify returns none; and on (X, (X, (Y, Z))) =? (Box X, (Box Y, (Vec Y, Z))) it returns dupσ = [(1, Vec Y), (0, Vec Y), (0, Box (Vec Y))], whose list of bound variables is [1, 0, 0] (X is bound twice), and whose k-fold unfoldings of the two sides disagree at depth 2 for every k, so the depth-indexed solution property fails.
7. **`no-oc-agrees-when-unify-succeeds`** (characterization, T0). If the run with the occurs check returns ok σ' then the run without it, from the same fuel, equations and initial accumulator substitution σ (arbitrary; σ need not be in solved form), returns ok σ'; hence if unify s t = some σ then unifyNoOC s t = some σ, and if unifyNoOC s t = some σ then σ unifies s and t iff s and t are unifiable.
8. **`no-oc-infinite-unfolding-sound-without-double-elimination`** (theorem, T1). If unifyNoOC s t returns some σ and the left-hand variables of the returned association list σ are pairwise distinct (the run eliminated no variable twice), then for every depth n there is a number k such that σ applied k times to s and to t gives terms that agree at every position of depth below n; agreement up to depth n is preserved by applying any substitution; agreement of the k-fold unfoldings persists for every number of unfoldings m ≥ k; and on finite terms, agreement at every depth is equality.
9. **`matching-vs-unification-differ`** (counterexample, T0). One-sided matching and unification differ in both directions: (X, u8) and (u32, Y) are unifiable but (X, u8) does not match (u32, Y); and X matches Box X (by X ↦ Box X, the target left untouched) while X and Box X are not unifiable.
10. **`matching-needs-no-occurs-check`** (theorem, T0). The matching algorithm matchAlg, which performs no occurs check and never applies its bindings to the target, is sound (if matchAlg p t = some σ then σ p = t) and complete (if some σ satisfies σ p = t, then matchAlg p t returns some substitution).
11. **`matching-iff-unification-on-ground-targets`** (characterization, T0). If the target t is ground, then p matches t iff p and t are unifiable; and matchAlg p t returns a substitution iff unify p t does.
12. **`overlap-check-unification-characterization`** (characterization, T0). For two impl headers whose self types share no variable, the headers overlap (same trait and a common ground instance of the self types) iff the traits agree and unify succeeds on the self types; so if the checker says disjoint (traits differ or unify fails on the self types), the headers have no common ground instance, the two impls overlap in no impl set at all, and hence that verdict is stable under every extension of any impl set; in particular it is StableUnderDownstream for every fundamental-constructor predicate fund, every impl set and all query symbols (it holds after every orphan-allowed downstream extension).
13. **`where-clause-overlap-iff-mgu-instance`** (characterization, T1). For two impls whose variables (in self types and where-clauses) are renamed apart, they overlap in an impl set I iff the traits agree, unify returns some σ on the self types, and some θ grounds σ applied to the first self type while every where-clause of both impls is derivable in I at θ ∘ σ.
14. **`where-clauses-break-converse-nonmonotone`** (counterexample, T1). impl<T: A> Tr for T and impl<U: B> Tr for U have unifiable self types, so the checker does not say disjoint (overlapCheckSaysDisjoint i1 i2 = false) and their headers overlap; no type implements both A and B in I_AB = {impl A for u8, impl B for u32, the two Tr impls}, and the impls do not overlap in I_AB; adding the single impl `impl B for u8` makes u8 an instance of both self types with u8: A and u8: B derivable, so they overlap; hence where-clause-based disjointness is not monotone in the impl set.
15. **`ground-negative-facts-stable-downstream`** (theorem, T1). For a ground type X: if every where-clause variable of every impl in I occurs in that impl's self type, crate c owns no trait or constructor mentioned in I, c owns neither the trait B nor any constructor of X, and every impl in E is orphan-allowed for c, then X: B is derivable from I ++ E iff it is derivable from I; in particular a negative fact ¬(X: B) in I remains true in I ++ E; equivalently, for ground X and constrained I, ¬(X: B) in I is stable for every fundamental-constructor predicate fund (StableUnderDownstream fund relative to the query symbols B and the constructors of X: it holds after every orphan-allowed extension by every crate that owns no trait or constructor mentioned in I, B or X, under every ownership map whose fundamental constructors are given by fund).
16. **`orphan-addressable-iff-fundamental-spine`** (characterization, T1). If crate c owns neither the trait B nor any constructor of X, and owns at least one constructor L, then c may write (under the toy orphan rule) an impl of B whose self type shares a ground instance with X iff following first arguments of fundamental head constructors from the root of X reaches a variable. Moreover, for any ownership map o₀: if no impl of B in I has a self type sharing a ground instance with X, and following first arguments of o₀'s fundamental head constructors from the root of X does not reach a variable, then 'no ground instance of X implements B' is stable (StableUnderDownstream relative to o₀.fundamental, the trait B and the constructors of X: it holds after every orphan-allowed extension by every crate that owns no trait or constructor mentioned in I, B or X, under every ownership map whose fundamental constructors are those of o₀).
17. **`negative-reasoning-unstable`** (counterexample, T1). (a) For the non-fundamental Vec and I_vecC = {impl<T: C> B for Vec<T>}, no ground instance of Vec<T> implements B, and no impl of B that crate 2 may write has a self type sharing a ground instance with Vec<T>; yet crate 2, fresh for I_vecC, B and Vec, may add `impl C for L`, after which Vec<L>: B is derivable, so ¬(some instance of Vec<T> implements B) is not stable relative to the fundamental constructors of ownersEx (under which Box is fundamental and Vec is not); (b) impl<T: A> Tr for T and impl<U: B> Tr for U do not overlap in I_AB, but crate 2, fresh for I_AB and for the symbols of both impls, may add `impl A for L` and `impl B for L`, after which L instantiates both self types with L: A and L: B derivable, so they overlap at L and that non-overlap verdict is not stable relative to the fundamental constructors of ownersEx.
18. **`no-oc-checker-false-overlap`** (counterexample, T1). impl<T> Tr for (T, T) and impl<U> Tr for (U, Box<U>), renamed apart, have no common ground instance; the checker with the occurs check says disjoint, while the checker using the occurs-check-free variant does not.
19. **`no-oc-checker-never-false-disjoint`** (impossibility, T1). For impl headers whose self types are renamed apart, if the checker using the occurs-check-free variant says disjoint, then the headers have no common ground instance; more generally, for any verdict function chk on unifier outputs and any proposition P that implies that s and t are unifiable: if chk (unify s t) = true rules out P and chk (unifyNoOC s t) = true, then P fails; uniformly, if chk fed unify is sound for an overlap relation P (implying unifiability) on every input, it is sound on every input when fed unifyNoOC.

Each result has non-claims that limit how it may be read. They are listed per result at the start of **Boundaries**, followed by the escape hatches of the impossibility result (19) and the stronger readings that are not established. Read them before relying on a result.

## Applicability

**Model fidelity.** This is a toy model.

- Terms are first-order trees over constructor symbols named by natural numbers, with explicit argument lists (a symbol used at two arities gives terms that never unify; there is no separate signature or well-sortedness predicate). Example symbols: `u8` (0), `u32` (1), `Box` (2), `Vec` (3), `Pair` (4), `L` (7); traits `Tr` (10), `A` (11), `B` (12), `C` (13). Variables are natural numbers; in prose X, Y, Z are variables 0, 1, 2 and T, U, V, W name variables of impls.
- Substitutions are finite association lists with first-binding lookup.
- The algorithm is a Martelli–Montanari-style solved-form algorithm (the naive equation-transformation rules with eager substitution, not the multiequation algorithm): each pass decomposes all pending equations into bindings and eliminates the first binding, substituting into the remaining bindings and into the accumulated substitution. Fuel counts eliminations. `unifyNoOC` is the same algorithm with the occurs check as the sole difference.
- Impls have one trait (no trait type parameters), a self type and where-clauses `Trait(ty)`. `Implements` is derivability by impl application at ground types (no negative impls, auto traits, associated types, lifetimes or specialization).
- Crate model: each trait and constructor has an owning crate; some constructors are fundamental; extensions are by a single fresh downstream crate under a toy orphan rule without a covered-parameter check. Stability (`StableUnderDownstream fund`) quantifies over all ownership maps whose fundamental constructors are given by a fixed predicate `fund` and under which the extending crate owns none of the relevant symbols; an extension cannot change which constructors are fundamental. Upstream evolution and multi-crate extensions are not modeled.

**What the definitions are meant to capture, and the known gaps.** `unify` and `unifyNoOC` stand for the syntactic unifiers used by type checkers and trait solvers, with and without the occurs check; `matchAlg` for one-sided matching of an impl header against a goal; `overlapCheckSaysDisjoint` and `overlapCheckSaysDisjointNoOC` for the header-unification part of a coherence (overlap) check; `Implements`, `OrphanOK`, `FreshFor` and `StableUnderDownstream` for trait derivability, the orphan rule and the question "can a downstream crate invalidate this negative fact". Known gaps: no infinite-tree (rational-tree) semantics is formalized, so results about infinite unfoldings are stated with the depth-indexed comparison `eqUpTo` and iterated substitution `iterSubst`; no arity discipline; no trait type parameters, lifetimes, associated types or projections, negative impls, auto traits, specialization or fundamental traits; the orphan rule ignores every argument of a fundamental constructor after the first (no covered-parameter check, unlike RFC 2451); one downstream crate at a time, and no upstream evolution.

Model–system relation for every result: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers, rustc's coherence checker, the orphan rules or `#[fundamental]`. Every theorem is a kernel-checked statement about this model (`Basis: execution (Lean kernel check)`); each result also carries a separate `Basis: derived (modeling bridge)` line that states, with its reasoning, what the theorem suggests about real systems. Those lines are not proved.

**Subjects.** The Lean 4 toolchain release in `REPORT.json` is the checker for every theorem. The papers, RFCs and documentation in `REPORT.json` are the primary sources whose known results or design rules are restated (tiers T0 and T1). The report does not claim that their proofs were checked; each result states how its statement relates to its sources, and each source entry records what was consulted.

**Lean.** `leanprover/lean4:v4.34.1`, the Lean core library and `Std`; no Mathlib and no Lake dependencies. Namespace `Toy.Unify`; library `ToyUnify` in `lean/` (Lake package `first_order_unification_coherence`).

## Findings

All Lean names below are in namespace `Toy.Unify` (prefix omitted in prose). Definitions come first, each with its intent and proved positive and negative examples; then the concrete example objects; then the 19 results; then every auxiliary declaration that the report cites by name. Statement blocks are verbatim quotes of the Lean source with the cited `file:line` range; proofs are elided as `…`. "Unfolded (prose)" lines are prose readings of the quoted definitions, not Lean terms.

### Definitions

#### `Term`

First-order terms: variables `var x` and constructor applications `con f args`; a model of type expressions without binders. Argument lists are explicit, so an arity mismatch is a clash.

```lean
-- lean/ToyUnify/Term.lean:19-22
inductive Term where
  | var : Nat → Term
  | con : Nat → List Term → Term
  deriving Inhabited
```

Positive example(s): `term_eq_example`, `term_arity_ne_example`. Negative example(s): `term_ne_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:15
theorem term_eq_example : box u8 = box u8 := by …
-- lean/ToyUnify/DefExamples.lean:19
theorem term_arity_ne_example : (Term.con 4 [u8] : Term) ≠ pair u8 u8 := by …
-- lean/ToyUnify/DefExamples.lean:17
theorem term_ne_example : box u8 ≠ box u32 := by …
```

#### `Term.vars`

Variables of a term, left to right, with repetitions.

```lean
-- lean/ToyUnify/Term.lean:84-93
mutual
/-- The variables occurring in a term, in left-to-right order (with repetitions). -/
def Term.vars : Term → List Nat
  | .var x => [x]
  | .con _ ts => Term.varsList ts
/-- The variables occurring in a list of terms (companion of `Term.vars`). -/
def Term.varsList : List Term → List Nat
  | [] => []
  | t :: ts => Term.vars t ++ Term.varsList ts
end
```

Positive example(s): `vars_example`. Negative example(s): `vars_ground_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:23
theorem vars_example : (pair (.var 0) (box (.var 5))).vars = [0, 5] := by …
-- lean/ToyUnify/DefExamples.lean:24
theorem vars_ground_example : (vec u8).vars = [] := by …
```

#### `Term.ctors`

Constructor symbols of a term, with repetitions.

```lean
-- lean/ToyUnify/Term.lean:95-104
mutual
/-- The constructor symbols occurring in a term (with repetitions). -/
def Term.ctors : Term → List Nat
  | .var _ => []
  | .con f ts => f :: Term.ctorsList ts
/-- The constructor symbols occurring in a list of terms (companion of `Term.ctors`). -/
def Term.ctorsList : List Term → List Nat
  | [] => []
  | t :: ts => Term.ctors t ++ Term.ctorsList ts
end
```

Positive example(s): `ctors_example`. Negative example(s): `ctors_var_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:25
theorem ctors_example : (pair (.var 0) (box u8)).ctors = [4, 2, 0] := by …
-- lean/ToyUnify/DefExamples.lean:26
theorem ctors_var_example : (Term.var 3).ctors = [] := by …
```

#### `occurs`

The occurs-check test: `x` occurs in `t`.

```lean
-- lean/ToyUnify/Term.lean:108
def occurs (x : Nat) (t : Term) : Bool := t.vars.contains x
```

Positive example(s): `occurs_example`. Negative example(s): `not_occurs_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:27
theorem occurs_example : occurs 0 (box (pair u8 (.var 0))) = true := by …
-- lean/ToyUnify/DefExamples.lean:28
theorem not_occurs_example : occurs 1 (box (pair u8 (.var 0))) = false := by …
```

#### `IsGround`

A term without variables (a concrete type).

```lean
-- lean/ToyUnify/Term.lean:111
def IsGround (t : Term) : Prop := t.vars = []
```

Positive example(s): `isGround_example`. Negative example(s): `not_isGround_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:32
theorem isGround_example : IsGround (pair u8 (vec u32)) := by …
-- lean/ToyUnify/DefExamples.lean:33
theorem not_isGround_example : ¬ IsGround (vec (.var 0)) := by …
```

#### `VarsDisjoint`

Two terms share no variable (renamed apart).

```lean
-- lean/ToyUnify/Term.lean:116
def VarsDisjoint (s t : Term) : Prop := ∀ x ∈ s.vars, x ∉ t.vars
```

Positive example(s): `varsDisjoint_example`. Negative example(s): `not_varsDisjoint_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:34
theorem varsDisjoint_example : VarsDisjoint (pair (.var 0) u8) (vec (.var 1)) := by …
-- lean/ToyUnify/DefExamples.lean:35
theorem not_varsDisjoint_example : ¬ VarsDisjoint (pair (.var 0) u8) (vec (.var 0)) := by …
```

#### `Subst`

Finite substitutions as association lists; first binding wins; unbound variables are fixed.

```lean
-- lean/ToyUnify/Term.lean:125
abbrev Subst := List (Nat × Term)
```

Positive example(s): `substVar_first_binding_example`. Negative example(s): `substVar_unbound_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:39
theorem substVar_first_binding_example : substVar [(0, u8), (0, u32)] 0 = u8 := by …
-- lean/ToyUnify/DefExamples.lean:40
theorem substVar_unbound_example : substVar [(0, u8)] 1 = .var 1 := by …
```

#### `substVar`

Image of a variable under a substitution.

```lean
-- lean/ToyUnify/Term.lean:128-131
def substVar (σ : Subst) (x : Nat) : Term :=
  match σ.lookup x with
  | some t => t
  | none => .var x
```

Positive example(s): `substVar_first_binding_example`. Negative example(s): `substVar_unbound_example`.

#### `subst`

Simultaneous application of a substitution to a term.

```lean
-- lean/ToyUnify/Term.lean:133-142
mutual
/-- Apply a substitution to a term (simultaneous replacement of variables). -/
def subst (σ : Subst) : Term → Term
  | .var x => substVar σ x
  | .con f ts => .con f (substList σ ts)
/-- Apply a substitution to each term of a list (companion of `subst`). -/
def substList (σ : Subst) : List Term → List Term
  | [] => []
  | t :: ts => subst σ t :: substList σ ts
end
```

Positive example(s): `subst_example`. Negative example(s): `subst_ne_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:41-42
theorem subst_example :
    subst [(0, u8), (1, box (.var 0))] (pair (.var 0) (.var 1)) = pair u8 (box (.var 0)) := by …
-- lean/ToyUnify/DefExamples.lean:44-45
theorem subst_ne_example :
    subst [(0, u8)] (pair (.var 0) (.var 1)) ≠ pair (.var 0) (.var 1) := by …
```

#### `Subst.comp`

Composition: `subst (Subst.comp θ σ) t = subst θ (subst σ t)` (lemma `subst_comp`).

```lean
-- lean/ToyUnify/Term.lean:231
def Subst.comp (θ σ : Subst) : Subst := σ.map (fun p => (p.1, subst θ p.2)) ++ θ
```

Positive example(s): `comp_example`. Negative example(s): `comp_order_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:51-53
theorem comp_example :
    subst (Subst.comp [(1, u8)] [(0, box (.var 1))]) (pair (.var 0) (.var 1)) =
      pair (box u8) u8 := by …
-- lean/ToyUnify/DefExamples.lean:55-56
theorem comp_order_example :
    subst (Subst.comp [(0, box (.var 1))] [(1, u8)]) (.var 0) ≠ box u8 := by …
-- lean/ToyUnify/Term.lean:245-246
theorem subst_comp (θ σ : Subst) (t : Term) :
    subst (Subst.comp θ σ) t = subst θ (subst σ t) := …
```

#### `iterSubst`

`k`-fold application; unfolds cyclic bindings.

```lean
-- lean/ToyUnify/Term.lean:146-148
def iterSubst (σ : Subst) : Nat → Term → Term
  | 0, t => t
  | k + 1, t => iterSubst σ k (subst σ t)
```

Positive example(s): `iterSubst_example`. Negative example(s): `iterSubst_ne_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:46-47
theorem iterSubst_example :
    iterSubst [(0, box (.var 0))] 3 (.var 0) = box (box (box (.var 0))) := by …
-- lean/ToyUnify/DefExamples.lean:48-49
theorem iterSubst_ne_example :
    iterSubst [(0, box (.var 0))] 2 (.var 0) ≠ box (box (box (.var 0))) := by …
```

#### `Unifies`

`σ` makes both sides syntactically equal (finite terms).

```lean
-- lean/ToyUnify/Algorithm.lean:23
def Unifies (σ : Subst) (s t : Term) : Prop := subst σ s = subst σ t
```

Positive example(s): `unifies_example`. Negative example(s): `not_unifies_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:60
theorem unifies_example : Unifies [(0, u8)] (pair (.var 0) u8) (pair u8 (.var 0)) := by …
-- lean/ToyUnify/DefExamples.lean:61
theorem not_unifies_example : ¬ Unifies [(0, u32)] (pair (.var 0) u8) (pair u8 (.var 0)) := by …
```

#### `Unifiable`

Some finite substitution unifies the two terms.

```lean
-- lean/ToyUnify/Algorithm.lean:29
def Unifiable (s t : Term) : Prop := ∃ σ : Subst, Unifies σ s t
```

Positive example(s): `unifiable_example`. Negative example(s): `not_unifiable_u8_u32`, `not_unifiable_var_box`.

```lean
-- lean/ToyUnify/DefExamples.lean:64
theorem unifiable_example : Unifiable (pair (.var 0) u8) (pair u32 (.var 1)) := …
-- lean/ToyUnify/DefExamples.lean:67
theorem not_unifiable_u8_u32 : ¬ Unifiable u8 u32 := by …
-- lean/ToyUnify/DefExamples.lean:79
theorem not_unifiable_var_box : ¬ Unifiable (.var 0) (box (.var 0)) := by …
```

#### `Idempotent`

Applying the substitution twice equals applying it once.

```lean
-- lean/ToyUnify/Algorithm.lean:32
def Idempotent (σ : Subst) : Prop := ∀ t : Term, subst σ (subst σ t) = subst σ t
```

Positive example(s): `idempotent_example`. Negative example(s): `not_idempotent_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:87
theorem idempotent_example : Idempotent [(0, pair (.var 1) u8)] := by …
-- lean/ToyUnify/DefExamples.lean:94
theorem not_idempotent_example : ¬ Idempotent [(0, box (.var 0))] := by …
```

#### `MoreGeneral`

The instance preorder: `τ` factors as `ρ ∘ σ` on every term.

```lean
-- lean/ToyUnify/Algorithm.lean:36
def MoreGeneral (σ τ : Subst) : Prop := ∃ ρ : Subst, ∀ t : Term, subst τ t = subst ρ (subst σ t)
```

Positive example(s): `moreGeneral_example`. Negative example(s): `not_moreGeneral_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:102
theorem moreGeneral_example : MoreGeneral [(0, .var 1)] [(0, u8), (1, u8)] := by …
-- lean/ToyUnify/DefExamples.lean:110
theorem not_moreGeneral_example : ¬ MoreGeneral [(0, u8)] [(0, .var 1)] := by …
```

#### `decomp`

Decompose one equation into variable bindings; `none` on a clash.

```lean
-- lean/ToyUnify/Algorithm.lean:40-57
mutual
/-- Decompose one equation `s =? t` into variable bindings, or `none` on a constructor clash
(different symbols or different argument counts). `var x =? var x` is dropped and
`t =? var x` (with `t` not a variable) is oriented to `x ↦ t`. -/
def decomp : Term → Term → Option (List (Nat × Term))
  | .var x, .var y => if x = y then some [] else some [(x, .var y)]
  | .var x, .con g ts => some [(x, .con g ts)]
  | .con f ss, .var x => some [(x, .con f ss)]
  | .con f ss, .con g ts => if f = g then decompList ss ts else none
/-- Decompose the pointwise equations of two argument lists (companion of `decomp`). -/
def decompList : List Term → List Term → Option (List (Nat × Term))
  | [], [] => some []
  | s :: ss, t :: ts =>
    match decomp s t, decompList ss ts with
    | some a, some b => some (a ++ b)
    | _, _ => none
  | _, _ => none
end
```

Positive example(s): `decomp_example`. Negative example(s): `decomp_clash_example`, `decomp_arity_clash_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:117-118
theorem decomp_example :
    decomp (pair (.var 0) u8) (pair (box (.var 1)) (.var 2)) = some [(0, box (.var 1)), (2, u8)] := by …
-- lean/ToyUnify/DefExamples.lean:120
theorem decomp_clash_example : decomp (pair (.var 0) u8) (pair (.var 1) u32) = none := by …
-- lean/ToyUnify/DefExamples.lean:121
theorem decomp_arity_clash_example : decomp (Term.con 4 [u8]) (pair u8 u8) = none := by …
```

#### `decompAll`

Decompose a list of equations.

```lean
-- lean/ToyUnify/Algorithm.lean:60-65
def decompAll : List (Term × Term) → Option (List (Nat × Term))
  | [] => some []
  | (s, t) :: es =>
    match decomp s t, decompAll es with
    | some a, some b => some (a ++ b)
    | _, _ => none
```

Positive example(s): `decompAll_example`. Negative example(s): `decomp_clash_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:122-123
theorem decompAll_example :
    decompAll [(.var 0, .var 0), (box (.var 1), box u8)] = some [(1, u8)] := by …
```

#### `Result`

Outcome of a run.

```lean
-- lean/ToyUnify/Algorithm.lean:71-75
inductive Result where
  | ok (σ : Subst)
  | fail
  | outOfFuel
  deriving Repr, DecidableEq
```

Positive example(s): `run_outOfFuel_example`. Negative example(s): `unify_clash_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:140
theorem run_outOfFuel_example : run true 0 [(.var 0, u8)] [] = .outOfFuel := by …
-- lean/ToyUnify/DefExamples.lean:135
theorem unify_clash_example : unify u8 u32 = none := by …
```

#### `Result.toOption`

Reads a run's result as an optional substitution: `fail` and `outOfFuel` both become `none`. `unify` and `unifyNoOC` apply it to the result of `run`. (Helper definition; it is exercised by the examples of `unify` and `unifyNoOC`.)

```lean
-- lean/ToyUnify/Algorithm.lean:78-80
def Result.toOption : Result → Option Subst
  | .ok σ => some σ
  | _ => none
```

#### `Step`

The outcome of one pass of `step`: finished with a `Result`, or a new list of pending equations together with a new accumulated substitution. (Helper type; it is exercised by the examples of `step` and `run`.)

```lean
-- lean/ToyUnify/Algorithm.lean:83-85
inductive Step where
  | done (r : Result)
  | next (eqs : List (Term × Term)) (σ : Subst)
```

#### `elimBinding`

Substitutes `u` for the variable `x` on both sides of a pending binding `b`, turning it back into an equation; `step` applies it to the bindings that remain after eliminating `x ↦ u`. (Helper definition; it is exercised by the examples of `step`.)

```lean
-- lean/ToyUnify/Algorithm.lean:88-89
def elimBinding (x : Nat) (u : Term) (b : Nat × Term) : Term × Term :=
  (subst [(x, u)] (.var b.1), subst [(x, u)] b.2)
```

#### `step`

One pass: decompose all pending equations; succeed if no binding remains; otherwise eliminate the first binding (failing first if the occurs check is on and fires). Decomposition drops trivial equations `x =? x`.

```lean
-- lean/ToyUnify/Algorithm.lean:94-100
def step (oc : Bool) (eqs : List (Term × Term)) (σ : Subst) : Step :=
  match decompAll eqs with
  | none => .done .fail
  | some [] => .done (.ok σ)
  | some ((x, u) :: bs) =>
    if oc && occurs x u then .done .fail
    else .next (bs.map (elimBinding x u)) ((x, u) :: σ.map (fun p => (p.1, subst [(x, u)] p.2)))
```

Positive example(s): `unify_example`. Negative example(s): `unify_occurs_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:133-134
theorem unify_example :
    unify (pair (.var 0) u8) (pair u32 (.var 1)) = some [(1, u8), (0, u32)] := by …
-- lean/ToyUnify/DefExamples.lean:136
theorem unify_occurs_example : unify (.var 0) (box (.var 0)) = none := by …
```

#### `run`

Iterate passes; each elimination consumes one unit of fuel.

```lean
-- lean/ToyUnify/Algorithm.lean:103-109
def run (oc : Bool) (fuel : Nat) (eqs : List (Term × Term)) (σ : Subst) : Result :=
  match step oc eqs σ with
  | .done r => r
  | .next eqs' σ' =>
    match fuel with
    | 0 => .outOfFuel
    | n + 1 => run oc n eqs' σ'
```

Positive example(s): `unify_example`. Negative example(s): `run_outOfFuel_example`.

#### `eqsVars`

The variables of an equation list, with repetitions, in order of occurrence; `numVars` counts its distinct entries. (Helper definition; it is exercised by the examples of `numVars`, including `numVars_dedup_example`.)

```lean
-- lean/ToyUnify/Algorithm.lean:112-113
def eqsVars (eqs : List (Term × Term)) : List Nat :=
  eqs.flatMap (fun e => e.1.vars ++ e.2.vars)
```

#### `numVars`

Termination measure: number of distinct variables of an equation list.

```lean
-- lean/ToyUnify/Algorithm.lean:116
def numVars (eqs : List (Term × Term)) : Nat := (eqsVars eqs).eraseDups.length
```

Positive example(s): `numVars_example`. Negative example(s): `numVars_dedup_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:127
theorem numVars_example : numVars [(pair (.var 0) (.var 1), pair (.var 1) (.var 0))] = 2 := by …
-- lean/ToyUnify/DefExamples.lean:131
theorem numVars_dedup_example : numVars [(.var 0, pair (.var 0) (.var 0))] = 1 := by …
```

#### `unify`

Unification with the occurs check, fuel `numVars`.

```lean
-- lean/ToyUnify/Algorithm.lean:120-121
def unify (s t : Term) : Option Subst :=
  (run true (numVars [(s, t)]) [(s, t)] []).toOption
```

Positive example(s): `unify_example`. Negative example(s): `unify_clash_example`, `unify_occurs_example`.

#### `unifyNoOC`

The same algorithm with the occurs check removed and nothing else changed.

```lean
-- lean/ToyUnify/Algorithm.lean:124-125
def unifyNoOC (s t : Term) : Option Subst :=
  (run false (numVars [(s, t)]) [(s, t)] []).toOption
```

Positive example(s): `unifyNoOC_example`. Negative example(s): `unifyNoOC_clash_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:137-138
theorem unifyNoOC_example :
    unifyNoOC (pair (.var 0) u8) (pair u32 (.var 1)) = some [(1, u8), (0, u32)] := by …
-- lean/ToyUnify/DefExamples.lean:139
theorem unifyNoOC_clash_example : unifyNoOC u8 u32 = none := by …
```

#### `eqUpTo`

Agreement at all positions of depth `< n` (finite approximation of infinite-tree equality).

```lean
-- lean/ToyUnify/Algorithm.lean:129-142
mutual
/-- `eqUpTo n a b`: `a` and `b` have the same variables and constructor symbols (with the same
argument counts) at every position of depth `< n`. Positions at depth `≥ n` are not compared. -/
def eqUpTo : Nat → Term → Term → Bool
  | 0, _, _ => true
  | _ + 1, .var x, .var y => x == y
  | n + 1, .con f ss, .con g ts => f == g && eqUpToList n ss ts
  | _ + 1, _, _ => false
/-- List companion of `eqUpTo`: same length and pointwise `eqUpTo n`. -/
def eqUpToList : Nat → List Term → List Term → Bool
  | _, [], [] => true
  | n, s :: ss, t :: ts => eqUpTo n s t && eqUpToList n ss ts
  | _, _, _ => false
end
```

Positive example(s): `eqUpTo_example`. Negative example(s): `eqUpTo_ne_example`, `eqUpTo_arity_ne_example`.

```lean
-- lean/ToyUnify/DefExamples.lean:144
theorem eqUpTo_example : eqUpTo 1 (box u8) (box u32) = true := by …
-- lean/ToyUnify/DefExamples.lean:145
theorem eqUpTo_ne_example : eqUpTo 2 (box u8) (box u32) = false := by …
-- lean/ToyUnify/DefExamples.lean:147
theorem eqUpTo_arity_ne_example : eqUpTo 1 (Term.con 4 [u8]) (pair u8 u8) = false := by …
```

#### `Matchable`

One-sided matching: some `σ` with `σ p = t`, target untouched.

```lean
-- lean/ToyUnify/Matching.lean:16
def Matchable (p t : Term) : Prop := ∃ σ : Subst, subst σ p = t
```

Positive example(s): `matchable_example`. Negative example(s): `not_matchable_example`.

```lean
-- lean/ToyUnify/Matching.lean:44
theorem matchable_example : Matchable (pair (.var 0) (.var 0)) (pair u8 u8) := …
-- lean/ToyUnify/Matching.lean:47
theorem not_matchable_example : ¬ Matchable (pair (.var 0) (.var 0)) (pair u8 u32) := by …
```

#### `matchAux`

The matching algorithm (no occurs check; bindings never applied to the target).

```lean
-- lean/ToyUnify/Matching.lean:18-37
mutual
/-- Match pattern `p` against target `t`, extending the accumulated bindings `σ`. A pattern
variable already bound must be bound to exactly `t`; there is no occurs check, and `σ` is never
applied to the target. -/
def matchAux : Term → Term → Subst → Option Subst
  | .var x, t, σ =>
    match σ.lookup x with
    | some u => if u = t then some σ else none
    | none => some ((x, t) :: σ)
  | .con f ps, .con g ts, σ => if f = g then matchList ps ts σ else none
  | .con _ _, .var _, _ => none
/-- Match argument lists pointwise (companion of `matchAux`). -/
def matchList : List Term → List Term → Subst → Option Subst
  | [], [], σ => some σ
  | p :: ps, t :: ts, σ =>
    match matchAux p t σ with
    | some σ' => matchList ps ts σ'
    | none => none
  | _, _, _ => none
end
```

Positive example(s): `matchAlg_example`. Negative example(s): `matchAlg_none_example`.

```lean
-- lean/ToyUnify/Matching.lean:53
theorem matchAlg_example : matchAlg (pair (.var 0) (.var 0)) (pair u8 u8) = some [(0, u8)] := by …
-- lean/ToyUnify/Matching.lean:56
theorem matchAlg_none_example : matchAlg (pair (.var 0) (.var 0)) (pair u8 u32) = none := by …
```

#### `matchAlg`

The matching algorithm: `matchAux` from no bindings. It performs no occurs check and never applies its bindings to the target.

```lean
-- lean/ToyUnify/Matching.lean:40
def matchAlg (p t : Term) : Option Subst := matchAux p t []
```

Positive example(s): `matchAlg_example`. Negative example(s): `matchAlg_none_example`.

#### `Bound`

A where-clause `Trait(ty)`.

```lean
-- lean/ToyUnify/Impls.lean:19-22
structure Bound where
  trait : Nat
  ty : Term
  deriving Repr, DecidableEq
```

Positive example(s): `implements_via_bound_example`. Negative example(s): `implements_isGround_example`.

```lean
-- lean/ToyUnify/Impls.lean:154
theorem implements_via_bound_example : Implements I_AB 10 u8 := by …
-- lean/ToyUnify/Impls.lean:162
theorem implements_isGround_example : ¬ Implements I_AB 10 (.var 0) := …
```

#### `Impl`

An impl header `impl<vars> trait for selfTy where bounds`.

```lean
-- lean/ToyUnify/Impls.lean:26-30
structure Impl where
  trait : Nat
  selfTy : Term
  bounds : List Bound
  deriving Repr, DecidableEq
```

Positive example(s): `implements_example`. Negative example(s): `not_headersOverlap_example`.

```lean
-- lean/ToyUnify/Impls.lean:150
theorem implements_example : Implements I_AB 11 u8 := …
-- lean/ToyUnify/Impls.lean:180
theorem not_headersOverlap_example : ¬ HeadersOverlap i1 implA_u8 := by …
```

#### `ImplSet`

A set of impls, as a list: the impls visible to the crate making a judgement.

```lean
-- lean/ToyUnify/Impls.lean:33
abbrev ImplSet := List Impl
```

Positive example(s): `I_AB` (see Example objects). Negative example(s): none (any list of impls is an impl set).

#### `Impl.vars`

All variables of an impl header: those of the self type, then those of the where-clauses (with repetitions).

```lean
-- lean/ToyUnify/Impls.lean:36
def Impl.vars (i : Impl) : List Nat := i.selfTy.vars ++ i.bounds.flatMap (fun b => b.ty.vars)
```

Positive example(s): `impl_vars_example`. Negative example(s): `not_mem_impl_vars_example`.

```lean
-- lean/ToyUnify/Impls.lean:165
theorem impl_vars_example : i1.vars = [0, 0] := by …
-- lean/ToyUnify/Impls.lean:166
theorem not_mem_impl_vars_example : 1 ∉ i1.vars := by …
```

#### `Impl.traits`

All trait symbols of an impl header: the implemented trait and the where-clause traits.

```lean
-- lean/ToyUnify/Impls.lean:39
def Impl.traits (i : Impl) : List Nat := i.trait :: i.bounds.map (fun b => b.trait)
```

Positive example(s): `impl_traits_example`. Negative example(s): `not_mem_impl_traits_example`.

```lean
-- lean/ToyUnify/Impls.lean:167
theorem impl_traits_example : i1.traits = [10, 11] := by …
-- lean/ToyUnify/Impls.lean:168
theorem not_mem_impl_traits_example : 12 ∉ i1.traits := by …
```

#### `Impl.ctors`

All constructor symbols of an impl header.

```lean
-- lean/ToyUnify/Impls.lean:42
def Impl.ctors (i : Impl) : List Nat := i.selfTy.ctors ++ i.bounds.flatMap (fun b => b.ty.ctors)
```

Positive example(s): `impl_ctors_example`. Negative example(s): `impl_ctors_nil_example`.

```lean
-- lean/ToyUnify/Impls.lean:169
theorem impl_ctors_example : implA_u8.ctors = [0] := by …
-- lean/ToyUnify/Impls.lean:170
theorem impl_ctors_nil_example : i1.ctors = [] := by …
```

#### `Implements`

Ground trait facts derivable from an impl set (least fixed point).

```lean
-- lean/ToyUnify/Impls.lean:48-51
inductive Implements (I : ImplSet) : Nat → Term → Prop
  | intro (i : Impl) (θ : Subst) (hi : i ∈ I) (hg : IsGround (subst θ i.selfTy))
      (hb : ∀ b ∈ i.bounds, Implements I b.trait (subst θ b.ty)) :
      Implements I i.trait (subst θ i.selfTy)
```

Positive example(s): `implements_example`, `implements_via_bound_example`. Negative example(s): `not_implements_example`, `implements_isGround_example`.

```lean
-- lean/ToyUnify/Impls.lean:151
theorem not_implements_example : ¬ Implements I_AB 11 u32 := by …
```

#### `CommonGroundInstance`

Two terms share a ground instance, each instantiated separately.

```lean
-- lean/ToyUnify/Impls.lean:55-56
def CommonGroundInstance (s t : Term) : Prop :=
  ∃ θ₁ θ₂ : Subst, IsGround (subst θ₁ s) ∧ subst θ₁ s = subst θ₂ t
```

Positive example(s): `commonGroundInstance_example`. Negative example(s): `not_commonGroundInstance_example`.

```lean
-- lean/ToyUnify/Impls.lean:172
theorem commonGroundInstance_example : CommonGroundInstance (pair (.var 0) u8) (pair u32 (.var 0)) := …
-- lean/ToyUnify/Impls.lean:174
theorem not_commonGroundInstance_example : ¬ CommonGroundInstance u8 u32 := by …
```

#### `HeadersOverlap`

Semantic header overlap ignoring where-clauses.

```lean
-- lean/ToyUnify/Impls.lean:60
def HeadersOverlap (i j : Impl) : Prop := i.trait = j.trait ∧ CommonGroundInstance i.selfTy j.selfTy
```

Positive example(s): `headersOverlap_example`. Negative example(s): `not_headersOverlap_example`.

```lean
-- lean/ToyUnify/Impls.lean:178
theorem headersOverlap_example : HeadersOverlap i1 i2 := …
```

#### `ImplsOverlapIn`

Semantic overlap in a fixed impl set (closed world): same trait and a ground instance of both self types at which all where-clauses of both impls are derivable in `I`. `I` need not contain `i` or `j`.

```lean
-- lean/ToyUnify/Impls.lean:66-70
def ImplsOverlapIn (I : ImplSet) (i j : Impl) : Prop :=
  i.trait = j.trait ∧ ∃ θ₁ θ₂ : Subst, IsGround (subst θ₁ i.selfTy) ∧
    subst θ₁ i.selfTy = subst θ₂ j.selfTy ∧
    (∀ b ∈ i.bounds, Implements I b.trait (subst θ₁ b.ty)) ∧
    (∀ b ∈ j.bounds, Implements I b.trait (subst θ₂ b.ty))
```

Positive example(s): `implsOverlapIn_not_monotone`. Negative example(s): `headersOverlap_not_implsOverlapIn`.

#### `overlapCheckSaysDisjoint`

The checker's verdict (distinct from the semantic properties): traits differ or `unify` fails.

```lean
-- lean/ToyUnify/Impls.lean:74-75
def overlapCheckSaysDisjoint (i j : Impl) : Bool :=
  i.trait != j.trait || (unify i.selfTy j.selfTy).isNone
```

Positive example(s): `overlapCheckSaysDisjoint_example`. Negative example(s): `overlapCheckSaysDisjoint_false_example`.

```lean
-- lean/ToyUnify/Impls.lean:184-185
theorem overlapCheckSaysDisjoint_example :
    overlapCheckSaysDisjoint ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ = true := by …
-- lean/ToyUnify/Impls.lean:186
theorem overlapCheckSaysDisjoint_false_example : overlapCheckSaysDisjoint i1 i2 = false := by …
```

#### `Owners`

Toy crate graph: owner of each trait and constructor; fundamental constructors.

```lean
-- lean/ToyUnify/Orphan.lean:34-37
structure Owners where
  traitOwner : Nat → Nat
  ctorOwner : Nat → Nat
  fundamental : Nat → Bool
```

Positive example(s): `isLocalTy_example`. Negative example(s): `not_isLocalTy_example`.

```lean
-- lean/ToyUnify/Orphan.lean:130
theorem isLocalTy_example : isLocalTy ownersEx 2 localL = true := by …
-- lean/ToyUnify/Orphan.lean:132
theorem not_isLocalTy_example : isLocalTy ownersEx 2 (vec localL) = false := by …
```

#### `isLocalTy`

The type counts as local to crate `c` for the toy orphan rule: its head constructor is owned by `c`, or its head is fundamental and its first argument is local. A variable is never local. Arguments after the first of a fundamental constructor are not inspected (no covered-parameter check).

```lean
-- lean/ToyUnify/Orphan.lean:44-47
def isLocalTy (o : Owners) (c : Nat) : Term → Bool
  | .var _ => false
  | .con f [] => o.ctorOwner f == c
  | .con f (a :: _) => o.ctorOwner f == c || (o.fundamental f && isLocalTy o c a)
```

Positive example(s): `isLocalTy_example`, `isLocalTy_fundamental_example`. Negative example(s): `not_isLocalTy_example`, `not_isLocalTy_var_example`.

```lean
-- lean/ToyUnify/Orphan.lean:131
theorem isLocalTy_fundamental_example : isLocalTy ownersEx 2 (box localL) = true := by …
-- lean/ToyUnify/Orphan.lean:133
theorem not_isLocalTy_var_example : isLocalTy ownersEx 2 (.var 0) = false := by …
```

#### `OrphanOK`

Toy orphan rule.

```lean
-- lean/ToyUnify/Orphan.lean:51-52
def OrphanOK (o : Owners) (c : Nat) (e : Impl) : Prop :=
  o.traitOwner e.trait = c ∨ isLocalTy o c e.selfTy = true
```

Positive example(s): `orphanOK_example`. Negative example(s): `not_orphanOK_example`.

```lean
-- lean/ToyUnify/Orphan.lean:135
theorem orphanOK_example : OrphanOK ownersEx 2 ⟨12, localL, []⟩ := by …
-- lean/ToyUnify/Orphan.lean:136
theorem not_orphanOK_example : ¬ OrphanOK ownersEx 2 ⟨12, u8, []⟩ := by …
```

#### `FreshCrate`

A crate owning no symbol of the impl set (downstream of it).

```lean
-- lean/ToyUnify/Orphan.lean:59-60
def FreshCrate (o : Owners) (c : Nat) (I : ImplSet) : Prop :=
  ∀ i ∈ I, (∀ tr ∈ i.traits, o.traitOwner tr ≠ c) ∧ (∀ f ∈ i.ctors, o.ctorOwner f ≠ c)
```

Positive example(s): `freshCrate_example`. Negative example(s): `not_freshCrate_example`.

```lean
-- lean/ToyUnify/Orphan.lean:138
theorem freshCrate_example : FreshCrate ownersEx 2 I_AB := by …
-- lean/ToyUnify/Orphan.lean:139
theorem not_freshCrate_example : ¬ FreshCrate ownersEx 0 I_AB := by …
```

#### `FreshFor`

Crate `c` is fresh for the impl set `I` and for the query symbols (`trs` traits, `ctors` constructors): it owns none of them.

```lean
-- lean/ToyUnify/Orphan.lean:76-77
def FreshFor (o : Owners) (c : Nat) (I : ImplSet) (trs ctors : List Nat) : Prop :=
  FreshCrate o c I ∧ (∀ tr ∈ trs, o.traitOwner tr ≠ c) ∧ (∀ f ∈ ctors, o.ctorOwner f ≠ c)
```

Positive example(s): `freshFor_example`. Negative example(s): `not_freshFor_example`.

```lean
-- lean/ToyUnify/Orphan.lean:141
theorem freshFor_example : FreshFor ownersEx 2 I_AB [12] (u8.ctors) := by …
-- lean/ToyUnify/Orphan.lean:143
theorem not_freshFor_example : ¬ FreshFor ownersEx 2 [] [] (localL.ctors) := by …
```

#### `Constrained`

Every where-clause variable occurs in the self type.

```lean
-- lean/ToyUnify/Orphan.lean:67-68
def Constrained (I : ImplSet) : Prop :=
  ∀ i ∈ I, ∀ b ∈ i.bounds, ∀ x ∈ b.ty.vars, x ∈ i.selfTy.vars
```

Positive example(s): `constrained_example`. Negative example(s): `not_constrained_example`.

```lean
-- lean/ToyUnify/Orphan.lean:145
theorem constrained_example : Constrained I_AB := by …
-- lean/ToyUnify/Orphan.lean:146
theorem not_constrained_example : ¬ Constrained [⟨12, u8, [⟨13, .var 0⟩]⟩] := by …
```

#### `StableUnderDownstream`

A predicate on impl sets is stable for `I`, relative to a fundamental-constructor predicate `fund` and query symbols, if it holds for `I ++ E` for every ownership map `o` with `o.fundamental = fund`, every crate fresh (under `o`) for `I` and the query symbols, and every list `E` of impls that crate may write under the orphan rule. The ownership of traits and constructors not mentioned in `I` or the query is unconstrained, so the new crate may own any of them; which constructors are fundamental (upstream ones and the new crate's alike) is fixed by `fund`. Stability implies the predicate holds for `I` itself (`StableUnderDownstream.self`).

```lean
-- lean/ToyUnify/Orphan.lean:91-94
def StableUnderDownstream (fund : Nat → Bool) (I : ImplSet) (trs ctors : List Nat)
    (P : ImplSet → Prop) : Prop :=
  ∀ (o : Owners) (c : Nat) (E : ImplSet), o.fundamental = fund → FreshFor o c I trs ctors →
    (∀ e ∈ E, OrphanOK o c e) → P (I ++ E)
```

Positive example(s): `stableUnderDownstream_example`. Negative example(s): `whereClause_disjointness_not_stable` (last conjunct). Dependence on `fund`: `noInstanceImplements_vec_stable_example` (stable relative to `ownersEx.fundamental`, under which `Vec` is not fundamental) and `noInstanceImplements_vec_not_stable_of_vec_fundamental` (with every constructor fundamental, the corresponding statement for the empty impl set is not stable).

```lean
-- lean/ToyUnify/Orphan.lean:153-155
theorem stableUnderDownstream_example :
    StableUnderDownstream ownersEx.fundamental I_AB [10] [3, 2]
      (fun I' => ¬ ImplsOverlapIn I' ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩) := by …
-- lean/ToyUnify/Orphan.lean:691-694
theorem noInstanceImplements_vec_stable_example :
    NoInstanceImplements I_AB 12 (vec (.var 0)) ∧
      StableUnderDownstream ownersEx.fundamental I_AB [12] (vec (.var 0)).ctors
        (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := …
-- lean/ToyUnify/Orphan.lean:734-739
theorem noInstanceImplements_vec_not_stable_of_vec_fundamental :
    (∀ i ∈ ([] : ImplSet), i.trait = 12 → ¬ CommonGroundInstance i.selfTy (vec (.var 0))) ∧
      fundSpineVar ownersAllFund (vec (.var 0)) = true ∧
      NoInstanceImplements [] 12 (vec (.var 0)) ∧
      ¬ StableUnderDownstream ownersAllFund.fundamental [] [12] (vec (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := by …
```

#### `fundSpineVar`

Following first arguments through fundamental heads reaches a variable.

```lean
-- lean/ToyUnify/Orphan.lean:106-109
def fundSpineVar (o : Owners) : Term → Bool
  | .var _ => true
  | .con _ [] => false
  | .con f (a :: _) => o.fundamental f && fundSpineVar o a
```

Positive example(s): `fundSpineVar_example`. Negative example(s): `not_fundSpineVar_example`.

```lean
-- lean/ToyUnify/Orphan.lean:148
theorem fundSpineVar_example : fundSpineVar ownersEx (box (.var 0)) = true := by …
-- lean/ToyUnify/Orphan.lean:149
theorem not_fundSpineVar_example : fundSpineVar ownersEx (vec (.var 0)) = false := by …
```

#### `NoInstanceImplements`

Negative reasoning over an open type: no ground instance implements the trait.

```lean
-- lean/ToyUnify/Orphan.lean:112-113
def NoInstanceImplements (I : ImplSet) (B : Nat) (X : Term) : Prop :=
  ∀ θ : Subst, ¬ Implements I B (subst θ X)
```

Positive example(s): `noInstanceImplements_example`. Negative example(s): `not_noInstanceImplements_example`.

```lean
-- lean/ToyUnify/Orphan.lean:160
theorem noInstanceImplements_example : NoInstanceImplements I_AB 12 u8 := by …
-- lean/ToyUnify/Orphan.lean:164
theorem not_noInstanceImplements_example : ¬ NoInstanceImplements I_AB 12 (.var 0) := …
```

#### `overlapCheckSaysDisjointNoOC`

The occurs-check-free checker's verdict.

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:23-24
def overlapCheckSaysDisjointNoOC (i j : Impl) : Bool :=
  i.trait != j.trait || (unifyNoOC i.selfTy j.selfTy).isNone
```

Positive example(s): `overlapCheckSaysDisjointNoOC_example`. Negative example(s): `overlapCheckSaysDisjointNoOC_false_example`.

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:26-27
theorem overlapCheckSaysDisjointNoOC_example :
    overlapCheckSaysDisjointNoOC ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ = true := by …
-- lean/ToyUnify/NoOccursCoherence.lean:28-29
theorem overlapCheckSaysDisjointNoOC_false_example :
    overlapCheckSaysDisjointNoOC i1 i2 = false := by …
```

### Example objects

Concrete terms, impls, impl sets and ownership maps used by the examples, counterexamples and non-vacuity theorems.

```lean
-- lean/ToyUnify/Term.lean:72
def u8 : Term := .con 0 []
```

```lean
-- lean/ToyUnify/Term.lean:74
def u32 : Term := .con 1 []
```

```lean
-- lean/ToyUnify/Term.lean:76
def box (t : Term) : Term := .con 2 [t]
```

```lean
-- lean/ToyUnify/Term.lean:78
def vec (t : Term) : Term := .con 3 [t]
```

```lean
-- lean/ToyUnify/Term.lean:80
def pair (a b : Term) : Term := .con 4 [a, b]
```

```lean
-- lean/ToyUnify/Impls.lean:111
def implA_u8 : Impl := ⟨11, u8, []⟩
```

```lean
-- lean/ToyUnify/Impls.lean:113
def implB_u32 : Impl := ⟨12, u32, []⟩
```

```lean
-- lean/ToyUnify/Impls.lean:115
def i1 : Impl := ⟨10, .var 0, [⟨11, .var 0⟩]⟩
```

```lean
-- lean/ToyUnify/Impls.lean:117
def i2 : Impl := ⟨10, .var 1, [⟨12, .var 1⟩]⟩
```

```lean
-- lean/ToyUnify/Impls.lean:120
def I_AB : ImplSet := [implA_u8, implB_u32, i1, i2]
```

```lean
-- lean/ToyUnify/Impls.lean:361
def iShared1 : Impl := ⟨10, pair (.var 0) u8, []⟩
```

```lean
-- lean/ToyUnify/Impls.lean:363
def iShared2 : Impl := ⟨10, pair u32 (.var 0), []⟩
```

```lean
-- lean/ToyUnify/Impls.lean:386
def iW1 : Impl := ⟨10, pair (.var 0) u8, [⟨11, .var 5⟩]⟩
```

```lean
-- lean/ToyUnify/Impls.lean:388
def iW2 : Impl := ⟨10, pair u32 (.var 1), [⟨12, .var 5⟩]⟩
```

```lean
-- lean/ToyUnify/Orphan.lean:121-123
def ownersEx : Owners :=
  { traitOwner := fun _ => 1, ctorOwner := fun f => if f = 7 then 2 else 0,
    fundamental := fun f => f == 2 }
```

```lean
-- lean/ToyUnify/Orphan.lean:126
def localL : Term := .con 7 []
```

```lean
-- lean/ToyUnify/Orphan.lean:470
def I_unconstrained : ImplSet := [⟨12, u8, [⟨13, .var 0⟩]⟩]
```

```lean
-- lean/ToyUnify/Orphan.lean:510-512
def ownersC : Owners :=
  { traitOwner := fun tr => if tr = 13 then 2 else 1, ctorOwner := fun f => if f = 7 then 2 else 0,
    fundamental := fun f => f == 2 }
```

```lean
-- lean/ToyUnify/Orphan.lean:515
def I_vecC : ImplSet := [⟨12, vec (.var 0), [⟨13, .var 0⟩]⟩]
```

```lean
-- lean/ToyUnify/Orphan.lean:544-546
def ownersB : Owners :=
  { traitOwner := fun tr => if tr = 12 then 2 else 1, ctorOwner := fun f => if f = 7 then 2 else 0,
    fundamental := fun f => f == 2 }
```

```lean
-- lean/ToyUnify/Orphan.lean:626
def E_C : ImplSet := [⟨13, localL, []⟩]
```

```lean
-- lean/ToyUnify/Orphan.lean:729
def ownersAllFund : Owners := { ownersEx with fundamental := fun _ => true }
```

```lean
-- lean/ToyUnify/Orphan.lean:748
def E_AB : ImplSet := [⟨11, localL, []⟩, ⟨12, localL, []⟩]
```

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:32
def iPairSame : Impl := ⟨10, pair (.var 0) (.var 0), []⟩
```

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:34
def iPairBox : Impl := ⟨10, pair (.var 1) (box (.var 1)), []⟩
```

```lean
-- lean/ToyUnify/OccursCheck.lean:871
def dupS : Term := pair (.var 0) (pair (.var 0) (pair (.var 1) (.var 2)))
```

```lean
-- lean/ToyUnify/OccursCheck.lean:873
def dupT : Term := pair (box (.var 0)) (pair (box (.var 1)) (pair (vec (.var 1)) (.var 2)))
```

```lean
-- lean/ToyUnify/OccursCheck.lean:875
def dupσ : Subst := [(1, vec (.var 1)), (0, vec (.var 1)), (0, box (vec (.var 1)))]
```

```lean
-- lean/ToyUnify/OccursCheck.lean:913
def dupσDedup : Subst := [(1, vec (.var 1)), (0, vec (.var 1))]
```

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:209
def loopS : Term := pair (.var 0) (pair (.var 0) (.var 0))
```

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:211
def loopT : Term := pair (.var 1) (pair (pair (.var 1) (.var 1)) (pair (.var 1) (.var 1)))
```

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:213-214
def loopEqs : List (Term × Term) :=
  [(pair (.var 1) (.var 1), pair (pair (.var 1) (.var 1)) (pair (.var 1) (.var 1)))]
```

```lean
-- lean/ToyUnify/Orphan.lean:812
def iUpBox2 : Impl := ⟨12, .con 2 [.var 0, u8], []⟩
```

```lean
-- lean/ToyUnify/Orphan.lean:815
def eDownBox2 : Impl := ⟨12, .con 2 [localL, .var 1], []⟩
```

### Results

Each result gives its kind and tier, plain claim, verbatim Lean statement(s), hypothesis ledger (tightness, counterexample and witness class), depth label, non-vacuity witness, positive control (for the impossibility result), prior art, design question and evidence basis. Non-claims are under Boundaries.

### 1. `unify-sound-idempotent` (theorem, T0)

**Plain claim.** For finite first-order terms s and t, if unify s t returns some σ, then σ unifies s and t (σ s = σ t syntactically) and σ is idempotent (σ (σ u) = σ u for every term u).

**Tier T0.** Soundness and idempotence of the substitution computed by Robinson / Martelli-Montanari style unification (Robinson 1965; Martelli and Montanari 1982; Lassez, Maher and Marriott 1988; Baader and Snyder 2001), restated for this solved-form algorithm with explicit fuel; mechanized before in other systems (Paulson 1985 in LCF; McBride 2003 in Lego; Kumar and Norrish 2010 in HOL4; Ribeiro and Camarão 2016 in Coq; Sternagel and Thiemann 2018 in Isabelle/HOL).

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Correctness.lean:39
theorem unify_sound {s t : Term} {σ : Subst} (h : unify s t = some σ) : Unifies σ s t := by …
```

```lean
-- lean/ToyUnify/Correctness.lean:46
theorem unify_idempotent {s t : Term} {σ : Subst} (h : unify s t = some σ) : Idempotent σ := by …
```

Unfolded (prose): `Unifies σ s t` is `subst σ s = subst σ t`; `Idempotent σ` is `∀ t, subst σ (subst σ t) = subst σ t`; `unify s t` is `(run true (numVars [(s, t)]) [(s, t)] []).toOption`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `h : unify s t = some σ` | Restricts the claim to substitutions actually returned by unify. | tight: counterexample `unify_sound_needs_output`, `unify_idempotent_needs_output` | unify_sound_needs_output: the instance X =? u8 (one variable, one nullary constructor) with the non-output σ = []; unify_idempotent_needs_output: the instance X =? Box X with the non-output σ = [X ↦ Box X]. |

**Depth.** substantive — Needs the solved-form invariant Inv (bound variables pairwise distinct and absent from every right-hand side and from the pending equations), maintained through decomposition and elimination passes, plus preservation of the solutions of the combined system Sys by each pass (both in ToyUnify/UnifyLemmas.lean).

**Non-vacuity witness.** unify (X, Box Y) (Box u8, X) returns [Y ↦ u8, X ↦ Box u8]. (`unify_sound_nonvacuous`)

**Prior art.**
- J. A. Robinson, "A Machine-Oriented Logic Based on the Resolution Principle", Journal of the ACM 12(1):23-41, 1965, doi:10.1145/321250.321253 (bibliographic data verified via the dblp record journals/jacm/Robinson65; full text not consulted). Standard attribution for syntactic unification and most general unifiers.
- A. Martelli and U. Montanari, "An Efficient Unification Algorithm", ACM Transactions on Programming Languages and Systems 4(2):258-282, 1982, doi:10.1145/357162.357169 (verified via the dblp record journals/toplas/MartelliM82; full text not consulted). Standard source for unification as the transformation of a set of equations into solved form. This package formalizes the paper's naive equation-transformation rules with eager substitution (which can build exponentially large terms), not its efficient multiequation algorithm.
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.
- L. C. Paulson, "Verifying the Unification Algorithm in LCF", Science of Computer Programming 5(2):143-169, 1985, doi:10.1016/0167-6423(85)90009-7 (verified via dblp; full text not consulted). An earlier mechanized correctness proof of a unification algorithm.
- C. Sternagel and R. Thiemann, "First-Order Terms", Archive of Formal Proofs, February 2018 (entry page https://www.isa-afp.org/entries/First_Order_Terms.html consulted: its abstract states that it formalizes matching and a first-order unification algorithm in Isabelle/HOL).
- J.-L. Lassez, M. J. Maher and K. Marriott, "Unification Revisited", in Foundations of Deductive Databases and Logic Programming, 1988, pp. 587-625, doi:10.1016/B978-0-934613-40-8.50019-1 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Clarifies the notions of most general and idempotent unifiers; the characterization of idempotent most general unifiers by the factor law τ = τ ∘ σ is attributed to it by secondary sources (not checked against the full text).
- C. McBride, "First-order unification by structural recursion", Journal of Functional Programming 13(6):1061-1075, 2003, doi:10.1017/S0956796803004957 (verified via the Crossref record; its abstract states that the program and its correctness proof were checked in the proof assistant Lego). A structurally recursive unification algorithm whose termination follows from the number of variables in scope.
- R. Kumar and M. Norrish, "(Nominal) Unification by Recursive Descent with Triangular Substitutions", Interactive Theorem Proving (ITP 2010), Springer, pp. 51-66, doi:10.1007/978-3-642-14052-5_6 (bibliographic data verified via the Crossref record; full text not consulted). A mechanized unification algorithm in HOL4.
- R. Ribeiro and C. Camarão, "A Mechanized Textbook Proof of a Type Unification Algorithm", Formal Methods: Foundations and Applications (SBMF 2015), Springer, 2016, pp. 127-141, doi:10.1007/978-3-319-29473-5_8 (bibliographic data verified via the Crossref record; full text not consulted). A mechanized unification proof in Coq.

**Design question.** What exactly does a successful unification call guarantee about its output?

**Non-claims.** Listed under Boundaries, result 1; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement depends on the input–output behaviour of `unify` alone. An implementation that returns the same result as `unify` on every input therefore satisfies the same statement; one that differs in any output (another binding order, another substitution representation such as union-find or triangular substitutions, multiequations, or merged or re-checked bindings) is related to this model by no proved relation, and whether a given production unifier or trait solver computes these functions is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 2. `unify-most-general` (theorem, T0)

**Plain claim.** For finite terms s and t, if unify s t returns some σ and τ is any unifier of s and t, then τ (σ u) = τ u for every term u; hence σ is more general than τ, with τ itself as the factor.

**Tier T0.** Most generality of the computed unifier, in the standard form 'every unifier τ satisfies τ = τ ∘ σ' for idempotent most general unifiers (Lassez, Maher and Marriott 1988; Baader and Snyder 2001); Robinson 1965 states most generality with an existential factor. Restated for this algorithm.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Correctness.lean:57-58
theorem unify_mgu_factor {s t : Term} {σ τ : Subst} (h : unify s t = some σ)
    (hτ : Unifies τ s t) : ∀ u : Term, subst τ (subst σ u) = subst τ u := by …
```

```lean
-- lean/ToyUnify/Correctness.lean:69-70
theorem unify_moreGeneral {s t : Term} {σ τ : Subst} (h : unify s t = some σ)
    (hτ : Unifies τ s t) : MoreGeneral σ τ := …
```

Unfolded (prose): `MoreGeneral σ τ` is `∃ ρ : Subst, ∀ t, subst τ t = subst ρ (subst σ t)`; the first theorem exhibits `ρ = τ`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `h : unify s t = some σ` | Restricts σ to the output of unify; another unifier need not be a factor of τ. | tight: counterexample `unify_mgu_factor_needs_output` | The instance X =? Y (two variables, two nullary constructors) with the non-output unifier [X ↦ u8, Y ↦ u8] and τ = [X ↦ u32, Y ↦ u32]; both conclusions (the factor law and MoreGeneral) fail. |
| `hτ : Unifies τ s t` | Without assuming that τ unifies s and t, τ need not satisfy τ ∘ σ = τ. | tight: counterexample `unify_mgu_factor_needs_unifier` | The instance X =? u8 with σ = [X ↦ u8] and the non-unifier τ = []; both conclusions fail. |

**Depth.** substantive — Every pass preserves the solutions of the combined system, so τ solves each solved binding x ↦ u, i.e. τ x = τ u; with first-binding lookup this gives τ ∘ σ = τ on every variable.

**Non-vacuity witness.** unify X (Y, u8) returns [X ↦ (Y, u8)] and [X ↦ (u32, u8), Y ↦ u32] unifies X and (Y, u8). (`unify_mgu_factor_nonvacuous`)

**Prior art.**
- J. A. Robinson, "A Machine-Oriented Logic Based on the Resolution Principle", Journal of the ACM 12(1):23-41, 1965, doi:10.1145/321250.321253 (bibliographic data verified via the dblp record journals/jacm/Robinson65; full text not consulted). Standard attribution for syntactic unification and most general unifiers.
- A. Martelli and U. Montanari, "An Efficient Unification Algorithm", ACM Transactions on Programming Languages and Systems 4(2):258-282, 1982, doi:10.1145/357162.357169 (verified via the dblp record journals/toplas/MartelliM82; full text not consulted). Standard source for unification as the transformation of a set of equations into solved form. This package formalizes the paper's naive equation-transformation rules with eager substitution (which can build exponentially large terms), not its efficient multiequation algorithm.
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.
- J.-L. Lassez, M. J. Maher and K. Marriott, "Unification Revisited", in Foundations of Deductive Databases and Logic Programming, 1988, pp. 587-625, doi:10.1016/B978-0-934613-40-8.50019-1 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Clarifies the notions of most general and idempotent unifiers; the characterization of idempotent most general unifiers by the factor law τ = τ ∘ σ is attributed to it by secondary sources (not checked against the full text).

**Design question.** Can a client rely on the unifier being most general, and with which explicit factor?

**Non-claims.** Listed under Boundaries, result 2; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement depends on the input–output behaviour of `unify` alone. An implementation that returns the same result as `unify` on every input therefore satisfies the same statement; one that differs in any output (another binding order, another substitution representation such as union-find or triangular substitutions, multiequations, or merged or re-checked bindings) is related to this model by no proved relation, and whether a given production unifier or trait solver computes these functions is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 3. `unify-complete` (theorem, T0)

**Plain claim.** For finite terms s and t, if some substitution τ unifies s and t then unify s t returns some substitution; consequently unify s t = none exactly when s and t have no unifier over finite terms.

**Tier T0.** Completeness of syntactic unification (Robinson 1965; Martelli and Montanari 1982), restated for this algorithm with its fuel bound.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Correctness.lean:75-76
theorem unify_complete {s t : Term} {τ : Subst} (hτ : Unifies τ s t) :
    ∃ σ, unify s t = some σ := by …
```

```lean
-- lean/ToyUnify/Correctness.lean:84
theorem unify_eq_none_iff (s t : Term) : unify s t = none ↔ ¬ Unifiable s t := by …
```

Unfolded (prose): `Unifiable s t` is `∃ σ, subst σ s = subst σ t`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `hτ : Unifies τ s t (first theorem)` | A unifier must exist for an output to be guaranteed. | tight: counterexample `unify_complete_needs_unifier` | The instance u8 =? u32 (two distinct nullary constructors) with τ = []: no output. |

**Depth.** substantive — Needs preservation of the solutions of the combined system by every pass, that a clash or occurs-check failure leaves no solution (decompAll_none, not_unifies_var_of_occurs), and termination within fuel numVars.

**Non-vacuity witness.** [X ↦ u8] unifies (X, u8) and (u8, X). (`unify_complete_nonvacuous`)

**Prior art.**
- J. A. Robinson, "A Machine-Oriented Logic Based on the Resolution Principle", Journal of the ACM 12(1):23-41, 1965, doi:10.1145/321250.321253 (bibliographic data verified via the dblp record journals/jacm/Robinson65; full text not consulted). Standard attribution for syntactic unification and most general unifiers.
- A. Martelli and U. Montanari, "An Efficient Unification Algorithm", ACM Transactions on Programming Languages and Systems 4(2):258-282, 1982, doi:10.1145/357162.357169 (verified via the dblp record journals/toplas/MartelliM82; full text not consulted). Standard source for unification as the transformation of a set of equations into solved form. This package formalizes the paper's naive equation-transformation rules with eager substitution (which can build exponentially large terms), not its efficient multiequation algorithm.
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.

**Design question.** Does a failed unification prove that two types can never be made equal?

**Non-claims.** Listed under Boundaries, result 3; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement depends on the input–output behaviour of `unify` alone. An implementation that returns the same result as `unify` on every input therefore satisfies the same statement; one that differs in any output (another binding order, another substitution representation such as union-find or triangular substitutions, multiequations, or merged or re-checked bindings) is related to this model by no proved relation, and whether a given production unifier or trait solver computes these functions is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 4. `unify-termination-measure` (theorem, T0)

**Plain claim.** With the occurs check on (oc = true), for every equation list eqs and every initial accumulator substitution σ (arbitrary: σ need not be in solved form, since no pass of the algorithm branches on it), if fuel ≥ numVars eqs (the number of distinct variables of eqs), then run oc fuel eqs σ does not return outOfFuel.

**Tier T0.** The standard termination argument for solved-form unification (each variable elimination removes a variable from the pending equations; Martelli and Montanari 1982), stated as an explicit fuel bound; McBride 2003 gives a structural argument mechanized in Lego.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Correctness.lean:99-101
theorem run_ne_outOfFuel_of_numVars_le (oc : Bool) (hoc : oc = true) (fuel : Nat)
    (eqs : List (Term × Term)) (σ : Subst) (hfuel : numVars eqs ≤ fuel) :
    run oc fuel eqs σ ≠ .outOfFuel := by …
```

Unfolded (prose): `numVars eqs` is the length of the duplicate-free list of variables occurring in `eqs`; `run` consumes one unit of fuel per elimination pass and returns `outOfFuel` when an elimination pass is required at fuel 0 (the `.next` branch of `run` with fuel `0`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `hoc : oc = true` | The occurs check guarantees that an eliminated variable disappears from the pending equations. | tight: counterexample `run_needs_occurs_check_for_bound` | The equation (X, (X, Y)) =? (Box X, (Box Y, Vec Y)) (measure 2) with fuel 2 and oc = false: X is eliminated twice and the run runs out of fuel. |
| `hfuel : numVars eqs ≤ fuel` | Each elimination pass consumes one unit of fuel. | tight: counterexample `run_needs_fuel_bound` | The equation X =? u8 (measure 1) with fuel 0. |

**Depth.** substantive — Decomposition never introduces variables and every elimination pass strictly decreases the number of distinct variables of the pending equations (step_true_next_numVars); induction on fuel.

**Non-vacuity witness.** numVars [((X, Y), (Y, u8))] ≤ 2, so with oc = true (hoc holds by rfl) and fuel = 2 both hypotheses hold. (`run_ne_outOfFuel_nonvacuous`)

**Prior art.**
- A. Martelli and U. Montanari, "An Efficient Unification Algorithm", ACM Transactions on Programming Languages and Systems 4(2):258-282, 1982, doi:10.1145/357162.357169 (verified via the dblp record journals/toplas/MartelliM82; full text not consulted). Standard source for unification as the transformation of a set of equations into solved form. This package formalizes the paper's naive equation-transformation rules with eager substitution (which can build exponentially large terms), not its efficient multiequation algorithm.
- C. McBride, "First-order unification by structural recursion", Journal of Functional Programming 13(6):1061-1075, 2003, doi:10.1017/S0956796803004957 (verified via the Crossref record; its abstract states that the program and its correctness proof were checked in the proof assistant Lego). A structurally recursive unification algorithm whose termination follows from the number of variables in scope.
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.

**Design question.** What explicit measure bounds the work of a unification-based checker, and what does that bound rely on?

**Non-claims.** Listed under Boundaries, result 4; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement depends on the input–output behaviour of `run` (with the occurs check on) and `numVars` alone. An implementation that returns the same result as `run` (with the occurs check on) and `numVars` on every input therefore satisfies the same statement; one that differs in any output (another binding order, another substitution representation such as union-find or triangular substitutions, multiequations, or merged or re-checked bindings) is related to this model by no proved relation, and whether a given production unifier or trait solver computes these functions is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 5. `occurs-failure-sound` (theorem, T0)

**Plain claim.** If a variable x occurs in a term u and u is not the variable x itself, then x and u have no unifier over finite terms.

**Tier T0.** The textbook justification of the occurs check over finite terms (Robinson 1965; Baader and Snyder 2001).

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/OccursCheck.lean:33-34
theorem not_unifiable_var_of_occurs {x : Nat} {u : Term} (hocc : occurs x u = true)
    (hne : u ≠ .var x) : ¬ Unifiable (.var x) u := by …
```

Unfolded (prose): `occurs x u` is `u.vars.contains x`; `¬ Unifiable (.var x) u` is `¬ ∃ σ, substVar σ x = subst σ u`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `hocc : occurs x u = true` | Without an occurrence, x ↦ u is a unifier. | tight: counterexample `not_unifiable_var_of_occurs_needs_occurs` | The instance X =? Box Y (X does not occur), which [X ↦ Box Y] unifies. |
| `hne : u ≠ .var x` | x =? x is unified by any substitution. | tight: counterexample `not_unifiable_var_of_occurs_needs_ne` | The instance X =? X, which [] unifies. |

**Depth.** shallow — A size argument: σ u is strictly larger than σ x when x occurs strictly inside u (size_substVar_lt_con).

**Non-vacuity witness.** X occurs in Box X, and Box X ≠ X. (`not_unifiable_var_of_occurs_nonvacuous`)

**Prior art.**
- J. A. Robinson, "A Machine-Oriented Logic Based on the Resolution Principle", Journal of the ACM 12(1):23-41, 1965, doi:10.1145/321250.321253 (bibliographic data verified via the dblp record journals/jacm/Robinson65; full text not consulted). Standard attribution for syntactic unification and most general unifiers.
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.

**Design question.** Why is the occurs-check failure branch of a unifier a sound 'no unifier' answer?

**Non-claims.** Listed under Boundaries, result 5; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement is about substitutions on finite first-order terms and involves no algorithm, so it applies to any type language that is represented faithfully by such terms (variables, and constructor symbols with argument lists); type languages with aliases, associated-type projections, binders or subtyping are not represented, and no faithful representation of a production type language is proved. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 6. `occurs-check-removal-unsound` (counterexample, T1)

**Plain claim.** Removing the occurs check, and changing nothing else, breaks soundness: on X =? Box X the variant returns [X ↦ Box X], which is not a unifier, no finite unifier exists, and unify returns none; and on (X, (X, (Y, Z))) =? (Box X, (Box Y, (Vec Y, Z))) it returns dupσ = [(1, Vec Y), (0, Vec Y), (0, Box (Vec Y))], whose list of bound variables is [1, 0, 0] (X is bound twice), and whose k-fold unfoldings of the two sides disagree at depth 2 for every k, so the depth-indexed solution property fails.

**Tier T1.** That omitting the occurs check yields non-unifiers over finite terms is classical (the "occur-check problem"; Plaisted 1984). The second instance, showing that this solved-form algorithm without the occurs check is not sound even for infinite unfoldings when a variable is eliminated twice, is made precise here for this specific algorithm; no source stating it was found, and no novelty search was recorded.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/OccursCheck.lean:57-61
theorem unifyNoOC_returns_nonunifier_var_box :
    unifyNoOC (.var 0) (box (.var 0)) = some [(0, box (.var 0))] ∧
      ¬ Unifies [(0, box (.var 0))] (.var 0) (box (.var 0)) ∧
      ¬ Unifiable (.var 0) (box (.var 0)) ∧
      unify (.var 0) (box (.var 0)) = none := …
```

```lean
-- lean/ToyUnify/OccursCheck.lean:899-903
theorem unifyNoOC_eqUpTo_fails_with_duplicate_elimination :
    unifyNoOC dupS dupT = some dupσ ∧ dupσ.map Prod.fst = [1, 0, 0] ∧
      ¬ (dupσ.map Prod.fst).Nodup ∧
      (∀ k, eqUpTo 2 (iterSubst dupσ k dupS) (iterSubst dupσ k dupT) = false) ∧
      ¬ (∀ n, ∃ k, eqUpTo n (iterSubst dupσ k dupS) (iterSubst dupσ k dupT) = true) := by …
```

Unfolded (prose): First theorem: `unifyNoOC (var 0) (box (var 0)) = some [(0, box (var 0))]`, that substitution does not equate `var 0` and `box (var 0)`, no substitution does, and `unify` returns `none`. Second theorem: `dupS` is `(X, (X, (Y, Z)))`, `dupT` is `(Box X, (Box Y, (Vec Y, Z)))` and `dupσ = [(1, Vec Y), (0, Vec Y), (0, Box (Vec Y))]` (X, Y, Z are variables 0, 1, 2; see Example objects); its bound variables are `[1, 0, 0]`; `eqUpTo 2` compares the roots and their immediate arguments.

**Hypothesis ledger.**

No hypotheses (closed counterexample statements).

**Depth.** shallow — Evaluation of the algorithm on two inputs, a size argument for the absence of finite unifiers, and a case split on k for the unfoldings.

**Non-vacuity witness.** Counterexample; its instances are the witnesses. (`unifyNoOC_returns_nonunifier_var_box`)

**Prior art.**
- G. Huet, "Resolution d'equations dans des langages d'ordre 1, 2, ..., omega", these de doctorat d'Etat, Universite Paris VII, defended 28 September 1976 (author-hosted scan at http://gallium.inria.fr/~huet/PUBLIC/Huet1976.pdf consulted: its introduction states that Chapter 5 treats first-order languages, proves existence of a principal unifier via rational congruences, and extends the existence of a principal solution to solutions among finite or infinite terms, such a solution being rational, i.e. recognizable by a finite automaton).
- A. Colmerauer, "Prolog and Infinite Trees", in K. L. Clark and S.-A. Tärnlund (eds.), Logic Programming, Academic Press, 1982, pp. 231-251 (bibliographic data taken from secondary indexes, the Computer History Museum Prolog bibliography and a reference list on EuDML; not verified at the publisher; full text not consulted). Solving equations over rational trees.
- J. Jaffar, "Efficient Unification over Infinite Terms", New Generation Computing 2(3):207-219, 1984, doi:10.1007/BF03037057 (verified via the dblp record journals/ngc/Jaffar84; full text not consulted).
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.
- D. A. Plaisted, "The occur-check problem in Prolog", New Generation Computing 2(4):309-322, 1984, doi:10.1007/BF03037324 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Analyses the consequences of omitting the occurs check in Prolog unification.
- A. Martelli and G. Rossi, "Efficient Unification with Infinite Terms in Logic Programming", in Proceedings of the International Conference on Fifth Generation Computer Systems (FGCS 1984), Tokyo, 1984, pp. 202-209 (bibliographic data from the second author's publication list; no DOI; full text not consulted). A unification algorithm over infinite (rational) terms.

**Design question.** What exactly breaks when a unifier skips the occurs check, over finite and over infinite terms?

**Non-claims.** Listed under Boundaries, result 6; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The two counterexamples concern the outputs of `unifyNoOC` on two concrete inputs. Any implementation that returns the same substitution on such an input exhibits the same failure there, because each failure is a property of the input and the returned substitution (not a unifier; unfoldings that disagree at depth 2). An implementation that returns other substitutions on these inputs is not covered, and whether a given production unifier without the occurs check returns them is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 7. `no-oc-agrees-when-unify-succeeds` (characterization, T0)

**Plain claim.** If the run with the occurs check returns ok σ' then the run without it, from the same fuel, equations and initial accumulator substitution σ (arbitrary; σ need not be in solved form), returns ok σ'; hence if unify s t = some σ then unifyNoOC s t = some σ, and if unifyNoOC s t = some σ then σ unifies s and t iff s and t are unifiable.

**Tier T0.** A known fact about unification without the occurs check: on equation systems with a finite unifier the occurs check never fires, so the variant takes the same steps (the NSTO literature; Plaisted 1984; Deransart, Ferrand and Téguia 1991; Apt and Pellegrini 1994). Restated for this algorithm (same passes, same fuel).

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/OccursCheck.lean:69-70
theorem run_false_eq_ok_of_run_true_eq_ok {fuel : Nat} {eqs : List (Term × Term)}
    {σ σ' : Subst} (h : run true fuel eqs σ = .ok σ') : run false fuel eqs σ = .ok σ' := by …
```

```lean
-- lean/ToyUnify/OccursCheck.lean:112-113
theorem unifyNoOC_eq_some_of_unify_eq_some {s t : Term} {σ : Subst} (h : unify s t = some σ) :
    unifyNoOC s t = some σ := by …
```

```lean
-- lean/ToyUnify/OccursCheck.lean:149-150
theorem unifyNoOC_unifies_iff_unifiable {s t : Term} {σ : Subst} (h : unifyNoOC s t = some σ) :
    Unifies σ s t ↔ Unifiable s t := by …
```

Unfolded (prose): `unify s t` and `unifyNoOC s t` are both `(run oc (numVars [(s, t)]) [(s, t)] []).toOption`, with `oc = true` and `oc = false` respectively.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `h : run true fuel eqs σ = .ok σ' (first theorem)` | Agreement is claimed when the run with the check succeeds. | tight: counterexample `run_agreement_needs_run_true_ok` | The equation X =? u8 with fuel 0 and σ' = []: both runs run out of fuel. |
| `h : unify s t = some σ (second theorem)` | As above, at the level of unify. | tight: counterexample `unifyNoOC_eq_some_needs_unify_output` | The instance X =? u8 with the non-output σ = []. |
| `h : unifyNoOC s t = some σ (third theorem)` | The equivalence is about the variant's output. | tight: counterexample `unifyNoOC_unifies_iff_needs_output` | The instance X =? u8 (unifiable) with the non-output σ = [], which does not unify it. |

**Depth.** shallow — Induction on fuel: the two runs take identical passes until an occurs-check failure, which a successful run never meets; the third theorem then follows from soundness and completeness of unify.

**Non-vacuity witness.** unify (X, u8) (u32, Y) succeeds with [Y ↦ u8, X ↦ u32]; unifyNoOC returns outputs both on that unifiable pair and on the non-unifiable X =? Box X. (`agreement_nonvacuous`, `unifyNoOC_unifies_iff_unifiable_nonvacuous`)

**Prior art.**
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.
- D. A. Plaisted, "The occur-check problem in Prolog", New Generation Computing 2(4):309-322, 1984, doi:10.1007/BF03037324 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Analyses the consequences of omitting the occurs check in Prolog unification.
- P. Deransart, G. Ferrand and M. Téguia, "NSTO programs (not subject to occur-check)", in V. A. Saraswat and K. Ueda (eds.), Logic Programming, Proceedings of the 1991 International Symposium, MIT Press, 1991, pp. 533-547 (bibliographic data taken from a secondary source, the bibliography of arXiv:2103.01911v2; not verified at the publisher; full text not consulted).
- K. R. Apt and A. Pellegrini, "On the occur-check-free PROLOG programs", ACM Transactions on Programming Languages and Systems 16(3):687-726, 1994, doi:10.1145/177492.177673 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Studies when unification without the occurs check is safe, building on the notion of equation systems "not subject to occur-check" (NSTO); the relationship of that notion to results 7 and 19 is stated from secondary descriptions and was not checked against the full text.

**Design question.** On which inputs can removing the occurs check change a unifier's answer?

**Non-claims.** Listed under Boundaries, result 7; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement depends on the input–output behaviour of `run`, `unify` and `unifyNoOC` alone. An implementation that returns the same result as `run`, `unify` and `unifyNoOC` on every input therefore satisfies the same statement; one that differs in any output (another binding order, another substitution representation such as union-find or triangular substitutions, multiequations, or merged or re-checked bindings) is related to this model by no proved relation, and whether a given production unifier or trait solver computes these functions is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 8. `no-oc-infinite-unfolding-sound-without-double-elimination` (theorem, T1)

**Plain claim.** If unifyNoOC s t returns some σ and the left-hand variables of the returned association list σ are pairwise distinct (the run eliminated no variable twice), then for every depth n there is a number k such that σ applied k times to s and to t gives terms that agree at every position of depth below n; agreement up to depth n is preserved by applying any substitution; agreement of the k-fold unfoldings persists for every number of unfoldings m ≥ k; and on finite terms, agreement at every depth is equality.

**Tier T1.** Solvability of first-order equations over infinite (rational) trees is classical (Huet 1976, Chapter 5; Colmerauer 1982; Courcelle 1983; Jaffar 1984; Martelli and Rossi 1984; Maher 1988). The representation-specific, depth-indexed statement for this solved-form algorithm, with the no-double-elimination condition, is made precise here; no source stating it was found, and no novelty search was recorded.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/OccursCheck.lean:843-845
theorem unifyNoOC_eqUpTo_of_nodup {s t : Term} {σ : Subst} (h : unifyNoOC s t = some σ)
    (hnd : (σ.map Prod.fst).Nodup) :
    ∀ n, ∃ k, eqUpTo n (iterSubst σ k s) (iterSubst σ k t) = true := by …
```

```lean
-- lean/ToyUnify/OccursCheck.lean:215-216
theorem eqUpTo_subst : ∀ {n : Nat} {a b : Term} (σ : Subst), eqUpTo n a b = true →
    eqUpTo n (subst σ a) (subst σ b) = true
```

```lean
-- lean/ToyUnify/OccursCheck.lean:251-253
theorem eqUpTo_iterSubst_mono {n k m : Nat} {a b : Term} (σ : Subst) (hkm : k ≤ m)
    (h : eqUpTo n (iterSubst σ k a) (iterSubst σ k b) = true) :
    eqUpTo n (iterSubst σ m a) (iterSubst σ m b) = true := by …
```

```lean
-- lean/ToyUnify/OccursCheck.lean:330
theorem eqUpTo_forall_iff_eq (a b : Term) : (∀ n, eqUpTo n a b = true) ↔ a = b := by …
```

Unfolded (prose): `iterSubst σ k t` applies `σ` exactly `k` times; `eqUpTo n a b = true` holds iff at every position of depth `< n`, `a` and `b` carry the same variable or the same constructor with the same number of arguments; `(σ.map Prod.fst).Nodup` says the left-hand variables of the association list are pairwise distinct.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `h : unifyNoOC s t = some σ (first theorem)` | The claim is about the variant's output. | tight: counterexample `unifyNoOC_eqUpTo_needs_output` | The instance X =? u8 with the non-output σ = [] (duplicate-free): X and u8 disagree at depth 1 after any number of unfoldings. |
| `hnd : (σ.map Prod.fst).Nodup (first theorem)` | No variable may have been eliminated twice; a re-eliminated variable's earlier binding is rewritten in the solved part and never re-checked. | tight: counterexample `unifyNoOC_eqUpTo_fails_with_duplicate_elimination` | The instance (X, (X, (Y, Z))) =? (Box X, (Box Y, (Vec Y, Z))) (three variables; constructors Box, Vec, Pair), whose output binds X twice. |
| `h : eqUpTo n a b = true (eqUpTo_subst)` | Congruence needs agreement before substitution. | tight: counterexample `eqUpTo_subst_needs_agreement` | The instance u8, u32 (two nullary constructors) with n = 1 and the empty substitution. |
| `hkm : k ≤ m (eqUpTo_iterSubst_mono)` | Fewer unfoldings can disagree where more agree. | tight: counterexample `eqUpTo_iterSubst_mono_needs_le` | The substitution [X ↦ u8] with k = 1, m = 0 on X and u8. |
| `h : eqUpTo n (iterSubst σ k a) (iterSubst σ k b) = true (eqUpTo_iterSubst_mono)` | Persistence needs agreement at k. | tight: counterexample `eqUpTo_iterSubst_mono_needs_agreement` | The instance u8, u32 with n = 1, k = 0, m = 1 and the empty substitution: k ≤ m holds, the 0-fold unfoldings disagree at depth 1 (h fails) and so do the 1-fold unfoldings (the conclusion fails). |

**Depth.** substantive — The proof (ToyUnify/OccursCheck.lean) shows that agreement in the limit (LimEq) is an equivalence and a congruence preserved backwards by every pass, that in a run whose output is duplicate-free a variable bound to a variable never reappears (invariant ChainInv), so var-to-var chains in the output have length at most one, and that then 2n and 2n + 1 unfoldings agree up to depth n (eqUpTo_iterSubst_converge).

**Non-vacuity witness.** unifyNoOC X (Box X) = some [X ↦ Box X], whose bound variables are distinct, on an input with no finite unifier; Box u8 and Box u32 agree up to depth 1 although they differ; k = 0 ≤ m = 3 with agreeing 0-fold unfoldings. (`unifyNoOC_eqUpTo_of_nodup_nonvacuous`, `eqUpTo_subst_nonvacuous`, `eqUpTo_iterSubst_mono_nonvacuous`)

**Prior art.**
- G. Huet, "Resolution d'equations dans des langages d'ordre 1, 2, ..., omega", these de doctorat d'Etat, Universite Paris VII, defended 28 September 1976 (author-hosted scan at http://gallium.inria.fr/~huet/PUBLIC/Huet1976.pdf consulted: its introduction states that Chapter 5 treats first-order languages, proves existence of a principal unifier via rational congruences, and extends the existence of a principal solution to solutions among finite or infinite terms, such a solution being rational, i.e. recognizable by a finite automaton).
- A. Colmerauer, "Prolog and Infinite Trees", in K. L. Clark and S.-A. Tärnlund (eds.), Logic Programming, Academic Press, 1982, pp. 231-251 (bibliographic data taken from secondary indexes, the Computer History Museum Prolog bibliography and a reference list on EuDML; not verified at the publisher; full text not consulted). Solving equations over rational trees.
- J. Jaffar, "Efficient Unification over Infinite Terms", New Generation Computing 2(3):207-219, 1984, doi:10.1007/BF03037057 (verified via the dblp record journals/ngc/Jaffar84; full text not consulted).
- B. Courcelle, "Fundamental properties of infinite trees", Theoretical Computer Science 25(2):95-169, 1983, doi:10.1016/0304-3975(83)90059-2 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Standard reference for infinite and rational trees.
- A. Martelli and G. Rossi, "Efficient Unification with Infinite Terms in Logic Programming", in Proceedings of the International Conference on Fifth Generation Computer Systems (FGCS 1984), Tokyo, 1984, pp. 202-209 (bibliographic data from the second author's publication list; no DOI; full text not consulted). A unification algorithm over infinite (rational) terms.
- M. J. Maher, "Complete axiomatizations of the algebras of finite, rational and infinite trees", Proceedings of the Third Annual Symposium on Logic in Computer Science (LICS 1988), Edinburgh, IEEE Computer Society Press, pp. 348-357, doi:10.1109/LICS.1988.5132 (bibliographic data verified via the Crossref record of the DOI; full text not consulted).

**Design question.** Is an occurs-check-free unifier at least a correct solver for cyclic (infinite) types, and under what condition?

**Non-claims.** Listed under Boundaries, result 8; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement depends on the input–output behaviour of `unifyNoOC` alone. An implementation that returns the same result as `unifyNoOC` on every input therefore satisfies the same statement; one that differs in any output (another binding order, another substitution representation such as union-find or triangular substitutions, multiequations, or merged or re-checked bindings) is related to this model by no proved relation, and whether a given production unifier or trait solver computes these functions is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 9. `matching-vs-unification-differ` (counterexample, T0)

**Plain claim.** One-sided matching and unification differ in both directions: (X, u8) and (u32, Y) are unifiable but (X, u8) does not match (u32, Y); and X matches Box X (by X ↦ Box X, the target left untouched) while X and Box X are not unifiable.

**Tier T0.** The difference between one-sided matching and unification is textbook (Baader and Snyder 2001).

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Matching.lean:63-65
theorem unifiable_not_matchable :
    Unifiable (pair (.var 0) u8) (pair u32 (.var 1)) ∧
      ¬ Matchable (pair (.var 0) u8) (pair u32 (.var 1)) := by …
```

```lean
-- lean/ToyUnify/Matching.lean:72-73
theorem matchable_not_unifiable :
    Matchable (.var 0) (box (.var 0)) ∧ ¬ Unifiable (.var 0) (box (.var 0)) := …
```

Unfolded (prose): `Matchable p t` is `∃ σ, subst σ p = t`; `Unifiable p t` is `∃ σ, subst σ p = subst σ t`.

**Hypothesis ledger.**

No hypotheses (closed counterexample statements).

**Depth.** shallow — Explicit witnesses and constructor/size arguments.

**Non-vacuity witness.** Counterexample; its instances are the witnesses. (`matchable_not_unifiable`)

**Prior art.**
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.

**Design question.** When may a solver use one-sided matching instead of unification?

**Non-claims.** Listed under Boundaries, result 9; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement is about substitutions on finite first-order terms and involves no algorithm, so it applies to any type language that is represented faithfully by such terms (variables, and constructor symbols with argument lists); type languages with aliases, associated-type projections, binders or subtyping are not represented, and no faithful representation of a production type language is proved. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 10. `matching-needs-no-occurs-check` (theorem, T0)

**Plain claim.** The matching algorithm matchAlg, which performs no occurs check and never applies its bindings to the target, is sound (if matchAlg p t = some σ then σ p = t) and complete (if some σ satisfies σ p = t, then matchAlg p t returns some substitution).

**Tier T0.** Correctness of syntactic matching (Baader and Snyder 2001); matching was formalized before in Isabelle/HOL (Sternagel and Thiemann 2018).

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Matching.lean:194-195
theorem matchAlg_sound {p t : Term} {σ : Subst} (h : matchAlg p t = some σ) :
    subst σ p = t := …
```

```lean
-- lean/ToyUnify/Matching.lean:199
theorem matchAlg_complete {p t : Term} (h : Matchable p t) : ∃ σ, matchAlg p t = some σ := by …
```

Unfolded (prose): `matchAlg p t` is `matchAux p t []`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `h : matchAlg p t = some σ (soundness)` | Restricts σ to the output. | tight: counterexample `matchAlg_sound_needs_output` | The instance X against u8 with the non-output σ = []. |
| `h : Matchable p t (completeness)` | An output is guaranteed when a matcher exists. | tight: counterexample `matchAlg_complete_needs_matchable` | The instance u8 against u32 (two distinct nullary constructors). |

**Depth.** shallow — Structural induction on the pattern with an invariant on the accumulated bindings (they extend the input bindings and bind every pattern variable seen; for completeness, they agree with a given matcher).

**Non-vacuity witness.** matchAlg X (Box X) = some [X ↦ Box X], the instance on which unification needs the occurs check, and X matches Box X. (`matchAlg_nonvacuous`)

**Prior art.**
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.
- C. Sternagel and R. Thiemann, "First-Order Terms", Archive of Formal Proofs, February 2018 (entry page https://www.isa-afp.org/entries/First_Order_Terms.html consulted: its abstract states that it formalizes matching and a first-order unification algorithm in Isabelle/HOL).

**Design question.** Which steps of a type checker can safely skip the occurs check?

**Non-claims.** Listed under Boundaries, result 10; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement depends on the input–output behaviour of `matchAlg` alone. An implementation that returns the same result as `matchAlg` on every input therefore satisfies the same statement; one that differs in any output (another binding order, another substitution representation such as union-find or triangular substitutions, multiequations, or merged or re-checked bindings) is related to this model by no proved relation, and whether a given production unifier or trait solver computes these functions is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 11. `matching-iff-unification-on-ground-targets` (characterization, T0)

**Plain claim.** If the target t is ground, then p matches t iff p and t are unifiable; and matchAlg p t returns a substitution iff unify p t does.

**Tier T0.** Immediate from the definitions; a standard observation.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Matching.lean:239-240
theorem matchable_iff_unifiable_of_isGround {p t : Term} (ht : IsGround t) :
    Matchable p t ↔ Unifiable p t := by …
```

```lean
-- lean/ToyUnify/Matching.lean:245-246
theorem matchAlg_isSome_iff_unify_isSome_of_isGround {p t : Term} (ht : IsGround t) :
    (matchAlg p t).isSome = true ↔ (unify p t).isSome = true := by …
```

Unfolded (prose): `IsGround t` is `t.vars = []`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `ht : IsGround t (both theorems)` | With variables in the target, matching and unification can differ. | tight: counterexample `matchable_iff_unifiable_needs_ground`, `matchAlg_isSome_iff_unify_needs_ground` | The instance X against Box X (one variable, one unary constructor; the target is not ground). |

**Depth.** shallow — The first theorem is definitional: one rewrite with subst_of_isGround (substitutions fix ground terms). The second combines it with soundness and completeness of matchAlg and of unify.

**Non-vacuity witness.** Vec u8 is ground. (`matchable_iff_unifiable_of_isGround_nonvacuous`)

**Prior art.**
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.

**Design question.** When is selecting an impl for a concrete type the same problem as unifying with its header?

**Non-claims.** Listed under Boundaries, result 11; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — The statement depends on the input–output behaviour of `matchAlg` and `unify` alone. An implementation that returns the same result as `matchAlg` and `unify` on every input therefore satisfies the same statement; one that differs in any output (another binding order, another substitution representation such as union-find or triangular substitutions, multiequations, or merged or re-checked bindings) is related to this model by no proved relation, and whether a given production unifier or trait solver computes these functions is not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about production unifiers or trait solvers.

### 12. `overlap-check-unification-characterization` (characterization, T0)

**Plain claim.** For two impl headers whose self types share no variable, the headers overlap (same trait and a common ground instance of the self types) iff the traits agree and unify succeeds on the self types; so if the checker says disjoint (traits differ or unify fails on the self types), the headers have no common ground instance, the two impls overlap in no impl set at all, and hence that verdict is stable under every extension of any impl set; in particular it is StableUnderDownstream for every fundamental-constructor predicate fund, every impl set and all query symbols (it holds after every orphan-allowed downstream extension).

**Tier T0.** That two variable-disjoint first-order terms have a common ground instance iff they are unifiable, and hence that a header-unification overlap check soundly reports disjointness, is standard (Baader and Snyder 2001; it underlies the apartness check of Eisenberg et al. 2014 and the overlap check described in the rustc-dev-guide). Restated here, including the renaming-apart hypothesis.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Impls.lean:283-284
theorem headersOverlap_iff_unify_isSome {i j : Impl} (hdisj : VarsDisjoint i.selfTy j.selfTy) :
    HeadersOverlap i j ↔ i.trait = j.trait ∧ (unify i.selfTy j.selfTy).isSome = true := by …
```

```lean
-- lean/ToyUnify/Impls.lean:262-264
theorem not_headersOverlap_of_overlapCheckSaysDisjoint {i j : Impl}
    (hdisj : VarsDisjoint i.selfTy j.selfTy) (h : overlapCheckSaysDisjoint i j = true) :
    ¬ HeadersOverlap i j := by …
```

```lean
-- lean/ToyUnify/Impls.lean:276-278
theorem not_implsOverlapIn_of_overlapCheckSaysDisjoint {i j : Impl}
    (hdisj : VarsDisjoint i.selfTy j.selfTy) (h : overlapCheckSaysDisjoint i j = true)
    (I : ImplSet) : ¬ ImplsOverlapIn I i j := …
```

```lean
-- lean/ToyUnify/Orphan.lean:304-306
theorem overlapCheckSaysDisjoint_stable (fund : Nat → Bool) (I : ImplSet) (trs ctors : List Nat)
    {i j : Impl} (hdisj : VarsDisjoint i.selfTy j.selfTy) (h : overlapCheckSaysDisjoint i j = true) :
    StableUnderDownstream fund I trs ctors (fun I' => ¬ ImplsOverlapIn I' i j) := …
```

Unfolded (prose): `HeadersOverlap i j` is `i.trait = j.trait ∧ ∃ θ₁ θ₂, IsGround (subst θ₁ i.selfTy) ∧ subst θ₁ i.selfTy = subst θ₂ j.selfTy`; `overlapCheckSaysDisjoint i j = true` holds iff `i.trait ≠ j.trait` or `unify i.selfTy j.selfTy = none`; `StableUnderDownstream fund I trs ctors P` is `∀ o c E, o.fundamental = fund → FreshFor o c I trs ctors → (∀ e ∈ E, OrphanOK o c e) → P (I ++ E)`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `hdisj : VarsDisjoint i.selfTy j.selfTy (all four theorems)` | Self types must be renamed apart; with a shared variable name unification can fail although the headers overlap. | tight: counterexample `overlapCheck_needs_renaming_apart`, `overlapCheckSaysDisjoint_stable_needs_renaming_apart` | Two impls of one trait without where-clauses whose self types (T, u8) and (u32, T) share the variable name T: the checker says disjoint, the characterization fails, the impls overlap in every impl set, and non-overlap is not stable. |
| `h : overlapCheckSaysDisjoint i j = true (not_headersOverlap_of_overlapCheckSaysDisjoint, not_implsOverlapIn_of_overlapCheckSaysDisjoint, overlapCheckSaysDisjoint_stable)` | The 'disjoint' verdict is what is claimed sound; when it is false the impls can overlap, and can come to overlap after a downstream extension. | tight: counterexample `overlapCheckSaysDisjoint_needs_verdict` | The renamed-apart blanket impls impl<T: A> Tr for T and impl<U: B> Tr for U: the checker does not say disjoint, the headers overlap, the impls overlap in I_AB ++ E_AB, and non-overlap is not stable for I_AB. |

**Depth.** shallow — Merge the two instantiations into one substitution (variables disjoint), then use soundness and completeness of unify; a ground instance of the unifier is obtained by sending all remaining variables to u8; stability is a corollary (the verdict excludes overlap in every impl set).

**Non-vacuity witness.** impl<T> Tr for Vec<T> and impl<U> Tr for Box<U>: self types renamed apart and the checker says disjoint; impl<T: A> Tr for T and impl<U: B> Tr for U have self types renamed apart. (`not_headersOverlap_of_overlapCheckSaysDisjoint_nonvacuous`, `headersOverlap_iff_unify_isSome_nonvacuous`)

**Prior art.**
- rustc-dev-guide, chapter "Coherence", file src/coherence.md of https://github.com/rust-lang/rustc-dev-guide at commit 33fa6bef32eee98a8e38c9376645cf6fbcb2ca67 (consulted). It describes overlap checks on pairs of impls that unify the impl headers (its example obtains ?E = &str), the implicit negative impl check impl_intersection_has_impossible_obligation (an overlap is impossible when an obligation cannot hold, using that downstream crates cannot implement a remote trait for a remote type), and the orphan check, which guards against impls that could be added by upstream crates in a backwards-compatible way or by downstream crates.
- Rust RFC 1023, "Rebalancing coherence" (feature fundamental_attribute, start date 2015-03-27), file text/1023-rebalancing-coherence.md of https://github.com/rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (consulted). It restricts negative reasoning to obey the orphan rules ('we cannot conclude that a proposition like T0: !Trait<T1..Tn> holds unless T0: Trait<T1..Tn> meets the orphan rules'), motivated by letting parent (upstream) crates add impls without breaking children, and introduces #[fundamental]: a fundamental type is one where implementing a blanket impl over it is a breaking change; it is applied to Box so that Box behaves like & and &mut with respect to coherence.
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.
- R. A. Eisenberg, D. Vytiniotis, S. Peyton Jones and S. Weirich, "Closed type families with overlapping equations", POPL 2014, pp. 671-683, doi:10.1145/2535838.2535856 (bibliographic data verified via the Crossref record; author-hosted full text consulted). Its apartness check (Definition 6) uses ordinary first-order unification; Section 6.1 shows with the pair (a, a) and ([b], b) that an occurs-check-based apartness verdict becomes unsound in the presence of non-terminating type families, Section 6.2 defines unification over infinite types (Definition 19) and conjectures, without proof, that using it restores soundness, and Section 6.3 reports that GHC uses it for the overlap check of open type families.

**Design question.** What does a 'no overlap' verdict computed by header unification alone guarantee, and on what renaming discipline does it depend?

**Non-claims.** Listed under Boundaries, result 12; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — rustc's overlap check compares two impl headers by unifying them (rustc-dev-guide, Coherence chapter, pinned commit). The toy check overlapCheckSaysDisjoint models the header-unification part of such a check for traits without type parameters. rustc additionally handles trait parameters, lifetimes, associated types, negative impls, specialization and the orphan check; none of these is modeled. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about rustc.

### 13. `where-clause-overlap-iff-mgu-instance` (characterization, T1)

**Plain claim.** For two impls whose variables (in self types and where-clauses) are renamed apart, they overlap in an impl set I iff the traits agree, unify returns some σ on the self types, and some θ grounds σ applied to the first self type while every where-clause of both impls is derivable in I at θ ∘ σ.

**Tier T1.** The decomposition 'overlap = unify the headers, then satisfy all where-clauses at an instance of the unifier' underlies coherence overlap checks (rustc-dev-guide, Coherence chapter); made precise here using most generality.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Impls.lean:305-310
theorem implsOverlapIn_iff_mgu_instance (I : ImplSet) {i j : Impl}
    (hdisj : ∀ x ∈ i.vars, x ∉ j.vars) :
    ImplsOverlapIn I i j ↔
      i.trait = j.trait ∧ ∃ σ, unify i.selfTy j.selfTy = some σ ∧
        ∃ θ : Subst, IsGround (subst θ (subst σ i.selfTy)) ∧
          ∀ b ∈ i.bounds ++ j.bounds, Implements I b.trait (subst θ (subst σ b.ty)) := by …
```

Unfolded (prose): `ImplsOverlapIn I i j` is `i.trait = j.trait ∧ ∃ θ₁ θ₂, IsGround (subst θ₁ i.selfTy) ∧ subst θ₁ i.selfTy = subst θ₂ j.selfTy ∧ (∀ b ∈ i.bounds, Implements I b.trait (subst θ₁ b.ty)) ∧ (∀ b ∈ j.bounds, Implements I b.trait (subst θ₂ b.ty))`; `i.vars` lists the variables of the self type and of all where-clauses.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `hdisj : ∀ x ∈ i.vars, x ∉ j.vars` | Renaming apart must cover where-clause variables too: a variable that the two impls share in their where-clauses but not in their self types is forced to one value on the right but may take two values on the left. | tight: counterexample `implsOverlapIn_iff_mgu_instance_needs_bound_vars_disjoint` | Two impls (T, u8) where W: A and (u32, V) where W: B whose self types are renamed apart but whose where-clauses share the variable W, in I_AB. |

**Depth.** shallow — The forward direction merges the two instantiations and factors the resulting common instance through the most general unifier (unify_mgu_factor); the backward direction composes. No new induction beyond the unify results used as black boxes.

**Non-vacuity witness.** impl<T: A> Tr for T and impl<U: B> Tr for U have all variables renamed apart. (`implsOverlapIn_iff_mgu_instance_nonvacuous`)

**Prior art.**
- rustc-dev-guide, chapter "Coherence", file src/coherence.md of https://github.com/rust-lang/rustc-dev-guide at commit 33fa6bef32eee98a8e38c9376645cf6fbcb2ca67 (consulted). It describes overlap checks on pairs of impls that unify the impl headers (its example obtains ?E = &str), the implicit negative impl check impl_intersection_has_impossible_obligation (an overlap is impossible when an obligation cannot hold, using that downstream crates cannot implement a remote trait for a remote type), and the orphan check, which guards against impls that could be added by upstream crates in a backwards-compatible way or by downstream crates.
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.

**Design question.** Exactly what extra fact beyond header unification must hold for two impls with where-clauses to overlap?

**Non-claims.** Listed under Boundaries, result 13; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — rustc's overlap check first unifies the two impl headers and then asks whether the instantiated where-clause obligations could hold (rustc-dev-guide, Coherence chapter, pinned commit). In the toy, subst θ (subst σ b.ty) mirrors instantiating a where-clause after header unification with σ = unify i.selfTy j.selfTy, and derivability in the fixed impl set I stands in for 'the obligation holds'. rustc's checks are open-world (an obligation counts as impossible when no crate could make it hold), while ImplsOverlapIn is closed-world. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about rustc.

### 14. `where-clauses-break-converse-nonmonotone` (counterexample, T1)

**Plain claim.** impl<T: A> Tr for T and impl<U: B> Tr for U have unifiable self types, so the checker does not say disjoint (overlapCheckSaysDisjoint i1 i2 = false) and their headers overlap; no type implements both A and B in I_AB = {impl A for u8, impl B for u32, the two Tr impls}, and the impls do not overlap in I_AB; adding the single impl `impl B for u8` makes u8 an instance of both self types with u8: A and u8: B derivable, so they overlap; hence where-clause-based disjointness is not monotone in the impl set.

**Tier T1.** The standard example motivating restrictions on negative reasoning in coherence (cf. RFC 1023), made precise in the toy.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Impls.lean:425-427
theorem headersOverlap_not_implsOverlapIn :
    HeadersOverlap i1 i2 ∧ Unifiable i1.selfTy i2.selfTy ∧ overlapCheckSaysDisjoint i1 i2 = false ∧
      (¬ ∃ ty, Implements I_AB 11 ty ∧ Implements I_AB 12 ty) ∧ ¬ ImplsOverlapIn I_AB i1 i2 := by …
```

```lean
-- lean/ToyUnify/Impls.lean:444-448
theorem implsOverlapIn_not_monotone :
    ¬ ImplsOverlapIn I_AB i1 i2 ∧
      subst [(0, u8)] i1.selfTy = u8 ∧ subst [(1, u8)] i2.selfTy = u8 ∧
      Implements (I_AB ++ [⟨12, u8, []⟩]) 11 u8 ∧ Implements (I_AB ++ [⟨12, u8, []⟩]) 12 u8 ∧
      ImplsOverlapIn (I_AB ++ [⟨12, u8, []⟩]) i1 i2 := by …
```

Unfolded (prose): `i1 = ⟨10, var 0, [⟨11, var 0⟩]⟩` (`impl<T: A> Tr for T`), `i2 = ⟨10, var 1, [⟨12, var 1⟩]⟩` (`impl<U: B> Tr for U`), `I_AB = [⟨11, u8, []⟩, ⟨12, u32, []⟩, i1, i2]` (see Example objects).

**Hypothesis ledger.**

No hypotheses (closed counterexample statements).

**Depth.** shallow — Inversion of the derivability relation on a four-impl set.

**Non-vacuity witness.** Counterexample; its instances are the witnesses. (`headersOverlap_not_implsOverlapIn`)

**Prior art.**
- Rust RFC 1023, "Rebalancing coherence" (feature fundamental_attribute, start date 2015-03-27), file text/1023-rebalancing-coherence.md of https://github.com/rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (consulted). It restricts negative reasoning to obey the orphan rules ('we cannot conclude that a proposition like T0: !Trait<T1..Tn> holds unless T0: Trait<T1..Tn> meets the orphan rules'), motivated by letting parent (upstream) crates add impls without breaking children, and introduces #[fundamental]: a fundamental type is one where implementing a blanket impl over it is a breaking change; it is applied to Box so that Box behaves like & and &mut with respect to coherence.
- rustc-dev-guide, chapter "Coherence", file src/coherence.md of https://github.com/rust-lang/rustc-dev-guide at commit 33fa6bef32eee98a8e38c9376645cf6fbcb2ca67 (consulted). It describes overlap checks on pairs of impls that unify the impl headers (its example obtains ?E = &str), the implicit negative impl check impl_intersection_has_impossible_obligation (an overlap is impossible when an obligation cannot hold, using that downstream crates cannot implement a remote trait for a remote type), and the orphan check, which guards against impls that could be added by upstream crates in a backwards-compatible way or by downstream crates.
- J. G. Morris and M. P. Jones, "Instance chains: type class programming without overlapping instances", ICFP 2010, pp. 375-386, doi:10.1145/1863543.1863596 (bibliographic data verified via the Crossref record; full text not consulted). Type-class design in which negative information about instances is made explicit.
- S. Peyton Jones, M. Jones and E. Meijer, "Type classes: an exploration of the design space", Haskell Workshop, 1997 (title, authors and venue verified via the publisher page of Microsoft Research; full text not consulted). Discusses overlapping instances and the design space of instance resolution.

**Design question.** Can a coherence checker use 'no type implements both bounds' to accept two blanket impls?

**Non-claims.** Listed under Boundaries, result 14; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — RFC 1023 restricts negative reasoning to facts that the orphan rules make knowable, and the rustc-dev-guide's implicit negative impl check uses that downstream crates cannot implement a remote trait for a remote type. The toy models extensions by one fresh downstream crate under a simplified orphan rule; upstream crates adding impls in later versions (the main motivation in RFC 1023) and simultaneous extensions by several crates are not modeled. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about Rust's coherence rules.

### 15. `ground-negative-facts-stable-downstream` (theorem, T1)

**Plain claim.** For a ground type X: if every where-clause variable of every impl in I occurs in that impl's self type, crate c owns no trait or constructor mentioned in I, c owns neither the trait B nor any constructor of X, and every impl in E is orphan-allowed for c, then X: B is derivable from I ++ E iff it is derivable from I; in particular a negative fact ¬(X: B) in I remains true in I ++ E; equivalently, for ground X and constrained I, ¬(X: B) in I is stable for every fundamental-constructor predicate fund (StableUnderDownstream fund relative to the query symbols B and the constructors of X: it holds after every orphan-allowed extension by every crate that owns no trait or constructor mentioned in I, B or X, under every ownership map whose fundamental constructors are given by fund).

**Tier T1.** Folklore behind orphan-rule-based negative reasoning (RFC 1023; the rustc-dev-guide's implicit negative impl check), made precise in the toy for one fresh downstream crate.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Orphan.lean:314-318
theorem implements_append_iff_of_orphanOK (o : Owners) (c : Nat) (I E : ImplSet) (B : Nat)
    (X : Term) (hXg : IsGround X) (hcons : Constrained I) (hfresh : FreshCrate o c I)
    (hB : o.traitOwner B ≠ c) (hX : ∀ f ∈ X.ctors, o.ctorOwner f ≠ c)
    (hE : ∀ e ∈ E, OrphanOK o c e) :
    Implements (I ++ E) B X ↔ Implements I B X := by …
```

```lean
-- lean/ToyUnify/Orphan.lean:350-353
theorem not_implements_append_of_orphanOK (o : Owners) (c : Nat) (I E : ImplSet) (B : Nat)
    (X : Term) (hXg : IsGround X) (hcons : Constrained I) (hfresh : FreshCrate o c I)
    (hB : o.traitOwner B ≠ c) (hX : ∀ f ∈ X.ctors, o.ctorOwner f ≠ c)
    (hE : ∀ e ∈ E, OrphanOK o c e) (hneg : ¬ Implements I B X) : ¬ Implements (I ++ E) B X := …
```

```lean
-- lean/ToyUnify/Orphan.lean:359-361
theorem not_implements_stable_of_isGround (fund : Nat → Bool) (I : ImplSet) (B : Nat) (X : Term)
    (hXg : IsGround X) (hcons : Constrained I) (hneg : ¬ Implements I B X) :
    StableUnderDownstream fund I [B] X.ctors (fun I' => ¬ Implements I' B X) := …
```

Unfolded (prose): `Constrained I`: every where-clause variable of each impl of `I` occurs in its self type; `FreshCrate o c I`: `c` owns no trait (implemented or in a where-clause) and no constructor of any impl of `I`; `OrphanOK o c e`: `o.traitOwner e.trait = c ∨ isLocalTy o c e.selfTy = true`; `FreshFor o c I trs ctors` adds that `c` owns no trait in `trs` and no constructor in `ctors`; `StableUnderDownstream fund I trs ctors P` is `∀ o c E, o.fundamental = fund → FreshFor o c I trs ctors → (∀ e ∈ E, OrphanOK o c e) → P (I ++ E)`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `hXg : IsGround X (all three theorems)` | Restricts the claim to ground facts; Implements derives no fact about a non-ground type (Implements.isGround). | harmless | Not tight: for a non-ground X both sides of the first theorem are false and the stability of ¬(X: B) holds trivially (implements_append_iff_of_not_isGround, not_implements_stable_of_not_isGround). The hypothesis is a domain restriction that keeps the statement from being read as a claim about open types. |
| `hcons : Constrained I` | An unconstrained where-clause variable can be instantiated with the new crate's type. | tight: counterexample `implements_append_iff_needs_constrained`, `not_implements_stable_needs_constrained` | The one-impl set {impl<U: C> B for u8} with the unconstrained U, X = u8, and the extension {impl C for L} by crate 2 (for the stability form: under ownersEx, relative to ownersEx.fundamental). |
| `hfresh : FreshCrate o c I (first two theorems)` | If c owns a where-clause trait of I, it can satisfy that where-clause for old types. | tight: counterexample `implements_append_iff_needs_fresh` | The one-impl set {impl<T: C> B for Vec<T>} where crate 2 owns C, X = Vec<u8>, and the extension {impl C for u8}. |
| `hB : o.traitOwner B ≠ c (first two theorems)` | If c owns B, it may implement B for X directly. | tight: counterexample `implements_append_iff_needs_trait_not_owned` | The empty impl set, crate 2 owning B, X = u8, and the extension {impl B for u8}. |
| `hX : ∀ f ∈ X.ctors, o.ctorOwner f ≠ c (first two theorems)` | If X mentions c's type, c may implement B for X directly. | tight: counterexample `implements_append_iff_needs_ctors_not_owned` | The empty impl set, X = L owned by crate 2, and the extension {impl B for L}. |
| `hE : ∀ e ∈ E, OrphanOK o c e (first two theorems)` | Without the orphan rule any impl can be added. | tight: counterexample `implements_append_iff_needs_orphanOK` | The empty impl set, X = u8, and the orphan-disallowed extension {impl B for u8} by crate 2. |
| `hneg : ¬ Implements I B X (second and third theorems)` | The conclusion is the persistence of this negative fact. | tight: counterexample `not_implements_append_needs_neg`, `not_implements_stable_needs_neg` | The one-impl set {impl B for u8} with X = u8 (and the empty extension; for the stability form, relative to ownersEx.fundamental). |

**Depth.** substantive — Induction on derivations in I ++ E, with constrainedness keeping every instantiated where-clause inside the constructors of the derived type, and the orphan rule excluding E-impls from deriving facts over symbols c does not own.

**Non-vacuity witness.** I_AB, crate 2, E = [impl A for L, impl B for L], trait B and the ground type X = u8 (u8: B is not derivable in I_AB). (`implements_append_iff_of_orphanOK_nonvacuous`, `not_implements_stable_of_isGround_nonvacuous`)

**Prior art.**
- Rust RFC 1023, "Rebalancing coherence" (feature fundamental_attribute, start date 2015-03-27), file text/1023-rebalancing-coherence.md of https://github.com/rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (consulted). It restricts negative reasoning to obey the orphan rules ('we cannot conclude that a proposition like T0: !Trait<T1..Tn> holds unless T0: Trait<T1..Tn> meets the orphan rules'), motivated by letting parent (upstream) crates add impls without breaking children, and introduces #[fundamental]: a fundamental type is one where implementing a blanket impl over it is a breaking change; it is applied to Box so that Box behaves like & and &mut with respect to coherence.
- rustc-dev-guide, chapter "Coherence", file src/coherence.md of https://github.com/rust-lang/rustc-dev-guide at commit 33fa6bef32eee98a8e38c9376645cf6fbcb2ca67 (consulted). It describes overlap checks on pairs of impls that unify the impl headers (its example obtains ?E = &str), the implicit negative impl check impl_intersection_has_impossible_obligation (an overlap is impossible when an obligation cannot hold, using that downstream crates cannot implement a remote trait for a remote type), and the orphan check, which guards against impls that could be added by upstream crates in a backwards-compatible way or by downstream crates.

**Design question.** Which negative facts about the current impl set survive any downstream crate's orphan-allowed impls?

**Non-claims.** Listed under Boundaries, result 15; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — RFC 1023 restricts negative reasoning to facts that the orphan rules make knowable, and the rustc-dev-guide's implicit negative impl check uses that downstream crates cannot implement a remote trait for a remote type. The toy models extensions by one fresh downstream crate under a simplified orphan rule; upstream crates adding impls in later versions (the main motivation in RFC 1023) and simultaneous extensions by several crates are not modeled. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about Rust's coherence rules.

### 16. `orphan-addressable-iff-fundamental-spine` (characterization, T1)

**Plain claim.** If crate c owns neither the trait B nor any constructor of X, and owns at least one constructor L, then c may write (under the toy orphan rule) an impl of B whose self type shares a ground instance with X iff following first arguments of fundamental head constructors from the root of X reaches a variable. Moreover, for any ownership map o₀: if no impl of B in I has a self type sharing a ground instance with X, and following first arguments of o₀'s fundamental head constructors from the root of X does not reach a variable, then 'no ground instance of X implements B' is stable (StableUnderDownstream relative to o₀.fundamental, the trait B and the constructors of X: it holds after every orphan-allowed extension by every crate that owns no trait or constructor mentioned in I, B or X, under every ownership map whose fundamental constructors are those of o₀).

**Tier T1.** The role of fundamental types in what downstream crates may implement, and the restriction of negative reasoning to facts that the orphan rules make knowable, are described informally in RFC 1023; this toy characterization and the stability condition are made precise here.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Orphan.lean:376-379
theorem exists_orphanOK_overlapping_impl_iff_fundSpineVar (o : Owners) (c B L : Nat) (X : Term)
    (hB : o.traitOwner B ≠ c) (hX : ∀ f ∈ X.ctors, o.ctorOwner f ≠ c) (hL : o.ctorOwner L = c) :
    (∃ e : Impl, OrphanOK o c e ∧ e.trait = B ∧ CommonGroundInstance e.selfTy X) ↔
      fundSpineVar o X = true := by …
```

```lean
-- lean/ToyUnify/Orphan.lean:401-405
theorem noInstanceImplements_stable_of_not_fundSpineVar (o₀ : Owners) (I : ImplSet) (B : Nat)
    (X : Term) (hI : ∀ i ∈ I, i.trait = B → ¬ CommonGroundInstance i.selfTy X)
    (hspine : fundSpineVar o₀ X = false) :
    StableUnderDownstream o₀.fundamental I [B] X.ctors
      (fun I' => NoInstanceImplements I' B X) := by …
```

Unfolded (prose): `isLocalTy o c t`: the head of `t` is owned by `c`, or the head is fundamental and the first argument is (recursively) local; `fundSpineVar o X`: `X` is a variable, or its head is fundamental, it has at least one argument, and its first argument satisfies `fundSpineVar`; `CommonGroundInstance s t` is `∃ θ₁ θ₂, IsGround (subst θ₁ s) ∧ subst θ₁ s = subst θ₂ t`; `NoInstanceImplements I B X` is `∀ θ, ¬ Implements I B (subst θ X)`; `StableUnderDownstream fund I trs ctors P` is `∀ o c E, o.fundamental = fund → FreshFor o c I trs ctors → (∀ e ∈ E, OrphanOK o c e) → P (I ++ E)`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `hB : o.traitOwner B ≠ c (first theorem)` | If c owns B, a blanket impl of B is allowed and overlaps every X. | tight: counterexample `exists_orphanOK_iff_needs_trait_not_owned` | Crate 2 owning B, X = u8, and the blanket impl impl<T> B for T. |
| `hX : ∀ f ∈ X.ctors, o.ctorOwner f ≠ c (first theorem)` | If X mentions c's type, c may target X directly. | tight: counterexample `exists_orphanOK_iff_needs_ctors_not_owned` | X = L owned by crate 2, and impl B for L. |
| `hL : o.ctorOwner L = c (first theorem)` | A crate that defines no type cannot write a local self type. | tight: counterexample `exists_orphanOK_iff_needs_local_ctor` | Crate 3 owning no type constructor at all (in ownersEx), with X = T. |
| `hI : ∀ i ∈ I, i.trait = B → ¬ CommonGroundInstance i.selfTy X (second theorem)` | An existing impl of B that matches an instance of X may have where-clauses that a downstream crate can satisfy. | tight: counterexample `noInstanceImplements_stable_needs_no_matching_impl` | The one-impl set I_vecC = {impl<T: C> B for Vec<T>} with X = Vec<T> under ownersEx (Vec not fundamental, so hspine holds); crate 2 adds impl C for L, after which Vec<L>: B. |
| `hspine : fundSpineVar o₀ X = false (second theorem)` | If the spine ends in a variable, a downstream crate can write an impl of B for an instance of X directly (first theorem). | tight: counterexample `noInstanceImplements_stable_needs_not_fundSpineVar`, `noInstanceImplements_vec_not_stable_of_vec_fundamental` | The empty impl set (so hI holds) with X = Box<T> under ownersEx (Box fundamental), where crate 2 adds impl B for Box<L>; and the empty impl set with X = Vec<T> under ownersAllFund (every constructor fundamental), where crate 2 adds impl B for Vec<L>. |

**Depth.** shallow — Induction along the first-argument spine; the reverse direction substitutes the local type for the spine variable; the stability theorem inverts the last step of a derivation of B at an instance of X: an impl of I is excluded by hI, an impl of the extension is excluded by the forward direction of the first theorem and the fact that ownership maps with the same fundamental constructors give the same fundSpineVar (fundSpineVar_congr).

**Non-vacuity witness.** ownersEx, crate 2, trait B, local type L, with X = Box T (criterion holds) and X = Vec T (criterion fails); for the stability theorem, o₀ = ownersEx, I = I_AB (its one impl of B, impl B for u32, matches no instance of Vec<T>), B and X = Vec<T>, giving that no ground instance of Vec<T> implements B in I_AB, stably. (`exists_orphanOK_overlapping_impl_iff_fundSpineVar_nonvacuous`, `noInstanceImplements_stable_of_not_fundSpineVar_nonvacuous`, `noInstanceImplements_vec_stable_example`)

**Prior art.**
- Rust RFC 1023, "Rebalancing coherence" (feature fundamental_attribute, start date 2015-03-27), file text/1023-rebalancing-coherence.md of https://github.com/rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (consulted). It restricts negative reasoning to obey the orphan rules ('we cannot conclude that a proposition like T0: !Trait<T1..Tn> holds unless T0: Trait<T1..Tn> meets the orphan rules'), motivated by letting parent (upstream) crates add impls without breaking children, and introduces #[fundamental]: a fundamental type is one where implementing a blanket impl over it is a breaking change; it is applied to Box so that Box behaves like & and &mut with respect to coherence.
- Rust RFC 2451, "Re-rebalancing coherence" (start date 2018-05-30), file text/2451-re-rebalancing-coherence.md of https://github.com/rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (consulted). It clarifies RFC 1023, allows impl<T> ForeignTrait<LocalType> for ForeignType<T>, defines covered and uncovered type parameters, and states that fundamental types cannot cover other types.

**Design question.** Which (trait, type) patterns can a downstream crate address directly, how do fundamental type constructors change that, and when does negative reasoning about the remaining patterns survive downstream extensions?

**Non-claims.** Listed under Boundaries, result 16; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — RFC 1023 makes Box behave like & and &mut for coherence via #[fundamental], so that a downstream crate may implement a remote trait for Box<LocalType>. The toy marks some constructors fundamental and lets the orphan rule look through their first argument; RFC 2451's covered/uncovered parameter rules, trait type parameters and fundamental traits are not modeled. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about Rust's orphan rules.

### 17. `negative-reasoning-unstable` (counterexample, T1)

**Plain claim.** (a) For the non-fundamental Vec and I_vecC = {impl<T: C> B for Vec<T>}, no ground instance of Vec<T> implements B, and no impl of B that crate 2 may write has a self type sharing a ground instance with Vec<T>; yet crate 2, fresh for I_vecC, B and Vec, may add `impl C for L`, after which Vec<L>: B is derivable, so ¬(some instance of Vec<T> implements B) is not stable relative to the fundamental constructors of ownersEx (under which Box is fundamental and Vec is not); (b) impl<T: A> Tr for T and impl<U: B> Tr for U do not overlap in I_AB, but crate 2, fresh for I_AB and for the symbols of both impls, may add `impl A for L` and `impl B for L`, after which L instantiates both self types with L: A and L: B derivable, so they overlap at L and that non-overlap verdict is not stable relative to the fundamental constructors of ownersEx.

**Tier T1.** Instances of the hazard RFC 1023 addresses, made precise in the toy with orphan-allowed downstream extensions.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/Orphan.lean:633-642
theorem noInstanceImplements_vec_not_stable :
    ownersEx.fundamental 3 = false ∧ fundSpineVar ownersEx (vec (.var 0)) = false ∧
      NoInstanceImplements I_vecC 12 (vec (.var 0)) ∧
      (¬ ∃ e : Impl, OrphanOK ownersEx 2 e ∧ e.trait = 12 ∧
        CommonGroundInstance e.selfTy (vec (.var 0))) ∧
      FreshFor ownersEx 2 I_vecC [12] (vec (.var 0)).ctors ∧
      (∀ e ∈ E_C, OrphanOK ownersEx 2 e) ∧ Implements (I_vecC ++ E_C) 12 (vec localL) ∧
      ¬ NoInstanceImplements (I_vecC ++ E_C) 12 (vec (.var 0)) ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_vecC [12] (vec (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := by …
```

```lean
-- lean/ToyUnify/Orphan.lean:754-762
theorem whereClause_disjointness_not_stable :
    ¬ ImplsOverlapIn I_AB i1 i2 ∧
      FreshFor ownersEx 2 I_AB (i1.traits ++ i2.traits) (i1.ctors ++ i2.ctors) ∧
      (∀ e ∈ E_AB, OrphanOK ownersEx 2 e) ∧
      subst [(0, localL)] i1.selfTy = localL ∧ subst [(1, localL)] i2.selfTy = localL ∧
      Implements (I_AB ++ E_AB) 11 localL ∧ Implements (I_AB ++ E_AB) 12 localL ∧
      ImplsOverlapIn (I_AB ++ E_AB) i1 i2 ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_AB (i1.traits ++ i2.traits)
          (i1.ctors ++ i2.ctors) (fun I' => ¬ ImplsOverlapIn I' i1 i2) := by …
```

Unfolded (prose): `NoInstanceImplements I B X` is `∀ θ, ¬ Implements I B (subst θ X)`; `I_vecC = [⟨12, Vec T, [⟨13, T⟩]⟩]`, `E_C = [⟨13, L, []⟩]`, `E_AB = [⟨11, L, []⟩, ⟨12, L, []⟩]`; in `ownersEx` crate 2 owns `L` and no other symbol, and `Box` is the one fundamental constructor; `StableUnderDownstream ownersEx.fundamental I trs ctors P` quantifies over the ownership maps `o` with `o.fundamental = ownersEx.fundamental`.

**Hypothesis ledger.**

No hypotheses (closed counterexample statements).

**Depth.** shallow — Explicit extensions and inversion of derivability on small impl sets; part (a) uses orphan-addressable-iff-fundamental-spine to exclude impls targeting Vec<T> directly.

**Non-vacuity witness.** Counterexample; its instances are the witnesses. (`whereClause_disjointness_not_stable`)

**Prior art.**
- Rust RFC 1023, "Rebalancing coherence" (feature fundamental_attribute, start date 2015-03-27), file text/1023-rebalancing-coherence.md of https://github.com/rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (consulted). It restricts negative reasoning to obey the orphan rules ('we cannot conclude that a proposition like T0: !Trait<T1..Tn> holds unless T0: Trait<T1..Tn> meets the orphan rules'), motivated by letting parent (upstream) crates add impls without breaking children, and introduces #[fundamental]: a fundamental type is one where implementing a blanket impl over it is a breaking change; it is applied to Box so that Box behaves like & and &mut with respect to coherence.
- rustc-dev-guide, chapter "Coherence", file src/coherence.md of https://github.com/rust-lang/rustc-dev-guide at commit 33fa6bef32eee98a8e38c9376645cf6fbcb2ca67 (consulted). It describes overlap checks on pairs of impls that unify the impl headers (its example obtains ?E = &str), the implicit negative impl check impl_intersection_has_impossible_obligation (an overlap is impossible when an obligation cannot hold, using that downstream crates cannot implement a remote trait for a remote type), and the orphan check, which guards against impls that could be added by upstream crates in a backwards-compatible way or by downstream crates.
- J. G. Morris and M. P. Jones, "Instance chains: type class programming without overlapping instances", ICFP 2010, pp. 375-386, doi:10.1145/1863543.1863596 (bibliographic data verified via the Crossref record; full text not consulted). Type-class design in which negative information about instances is made explicit.
- rust-lang/chalk, book chapter "Coherence", file book/src/clauses/coherence.md of https://github.com/rust-lang/chalk at commit 5fc7e4564e704ec94747a66affb5ea6bde555d3e (existence of the file at that commit confirmed via the GitHub API; its content was not consulted here). Cited as a reference treatment of Rust's orphan and overlap checks, including restrictions on negative reasoning.

**Design question.** Why must a coherence checker refuse negative reasoning about open types and conjunctions of bounds?

**Non-claims.** Listed under Boundaries, result 17; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — RFC 1023 restricts negative reasoning to facts that the orphan rules make knowable, and the rustc-dev-guide's implicit negative impl check uses that downstream crates cannot implement a remote trait for a remote type. The toy models extensions by one fresh downstream crate under a simplified orphan rule; upstream crates adding impls in later versions (the main motivation in RFC 1023) and simultaneous extensions by several crates are not modeled. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about Rust's coherence rules.

### 18. `no-oc-checker-false-overlap` (counterexample, T1)

**Plain claim.** impl<T> Tr for (T, T) and impl<U> Tr for (U, Box<U>), renamed apart, have no common ground instance; the checker with the occurs check says disjoint, while the checker using the occurs-check-free variant does not.

**Tier T1.** A known consequence of omitting the occurs check (Plaisted 1984); for type-level apartness the pair (a, a), ([b], b) plays this role in Eisenberg et al. 2014, Section 6. Made precise here for an overlap checker.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:39-42
theorem noOC_check_reports_false_overlap :
    VarsDisjoint iPairSame.selfTy iPairBox.selfTy ∧ ¬ HeadersOverlap iPairSame iPairBox ∧
      overlapCheckSaysDisjoint iPairSame iPairBox = true ∧
      overlapCheckSaysDisjointNoOC iPairSame iPairBox = false := by …
```

Unfolded (prose): `iPairSame = ⟨10, Pair T T, []⟩`, `iPairBox = ⟨10, Pair U (Box U), []⟩`.

**Hypothesis ledger.**

No hypotheses (closed counterexample statements).

**Depth.** shallow — Evaluation of both checkers and a size argument.

**Non-vacuity witness.** Counterexample; its instance is the witness. (`noOC_check_reports_false_overlap`)

**Prior art.**
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.
- rustc-dev-guide, chapter "Coherence", file src/coherence.md of https://github.com/rust-lang/rustc-dev-guide at commit 33fa6bef32eee98a8e38c9376645cf6fbcb2ca67 (consulted). It describes overlap checks on pairs of impls that unify the impl headers (its example obtains ?E = &str), the implicit negative impl check impl_intersection_has_impossible_obligation (an overlap is impossible when an obligation cannot hold, using that downstream crates cannot implement a remote trait for a remote type), and the orphan check, which guards against impls that could be added by upstream crates in a backwards-compatible way or by downstream crates.
- D. A. Plaisted, "The occur-check problem in Prolog", New Generation Computing 2(4):309-322, 1984, doi:10.1007/BF03037324 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Analyses the consequences of omitting the occurs check in Prolog unification.
- R. A. Eisenberg, D. Vytiniotis, S. Peyton Jones and S. Weirich, "Closed type families with overlapping equations", POPL 2014, pp. 671-683, doi:10.1145/2535838.2535856 (bibliographic data verified via the Crossref record; author-hosted full text consulted). Its apartness check (Definition 6) uses ordinary first-order unification; Section 6.1 shows with the pair (a, a) and ([b], b) that an occurs-check-based apartness verdict becomes unsound in the presence of non-terminating type families, Section 6.2 defines unification over infinite types (Definition 19) and conjectures, without proof, that using it restores soundness, and Section 6.3 reports that GHC uses it for the overlap check of open type families.

**Design question.** What does an overlap checker lose if its unifier omits the occurs check?

**Non-claims.** Listed under Boundaries, result 18; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — rustc's overlap check compares two impl headers by unifying them (rustc-dev-guide, Coherence chapter, pinned commit). The toy check overlapCheckSaysDisjointNoOC models the header-unification part of such a check for traits without type parameters. rustc additionally handles trait parameters, lifetimes, associated types, negative impls, specialization and the orphan check; none of these is modeled. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about rustc.

### 19. `no-oc-checker-never-false-disjoint` (impossibility, T1)

**Plain claim.** For impl headers whose self types are renamed apart, if the checker using the occurs-check-free variant says disjoint, then the headers have no common ground instance; more generally, for any verdict function chk on unifier outputs and any proposition P that implies that s and t are unifiable: if chk (unify s t) = true rules out P and chk (unifyNoOC s t) = true, then P fails; uniformly, if chk fed unify is sound for an overlap relation P (implying unifiability) on every input, it is sound on every input when fed unifyNoOC.

**Tier T1.** Follows from the agreement of the two variants on unifiable inputs; made precise here. It corrects the tempting belief that removing the occurs check can make a coherence checker accept overlapping impls.

**Lean statement(s)** (verbatim, proofs elided):

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:53-55
theorem not_headersOverlap_of_overlapCheckSaysDisjointNoOC {i j : Impl}
    (hdisj : VarsDisjoint i.selfTy j.selfTy) (h : overlapCheckSaysDisjointNoOC i j = true) :
    ¬ HeadersOverlap i j := by …
```

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:73-75
theorem noOC_verdict_sound_of_unify_verdict_sound {s t : Term} (chk : Option Subst → Bool)
    (P : Prop) (hP : P → Unifiable s t) (hchk : chk (unify s t) = true → ¬ P)
    (h : chk (unifyNoOC s t) = true) : ¬ P := by …
```

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:84-87
theorem noOC_verdict_sound_of_unify_verdict_sound_uniform (chk : Option Subst → Bool)
    (P : Term → Term → Prop) (hP : ∀ s t, P s t → Unifiable s t)
    (hchk : ∀ s t, chk (unify s t) = true → ¬ P s t) :
    ∀ s t, chk (unifyNoOC s t) = true → ¬ P s t := …
```

Unfolded (prose): `overlapCheckSaysDisjointNoOC i j = true` holds iff `i.trait ≠ j.trait` or `unifyNoOC i.selfTy j.selfTy = none`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Witness class |
|---|---|---|---|
| `hdisj : VarsDisjoint i.selfTy j.selfTy (first theorem)` | Renaming apart, as for the checker with the occurs check. | tight: counterexample `noOC_check_false_disjoint_without_renaming` | Two impls of one trait whose self types (T, u8) and (u32, T) share the variable name T. |
| `h : overlapCheckSaysDisjointNoOC i j = true (first theorem)` | The 'disjoint' verdict is what is claimed sound. | tight: counterexample `noOC_disjoint_needs_verdict` | The renamed-apart blanket impls impl<T: A> Tr for T and impl<U: B> Tr for U. |
| `hP : P → Unifiable s t (second theorem)` | The verdict's subject must imply unifiability; otherwise the variant's extra outputs can be misread. | tight: counterexample `noOC_verdict_transfer_needs_hP` | P := True, chk := Option.isSome on the pair (T, T), (U, Box U): hchk holds vacuously on this pair, h holds, and P holds. |
| `hP : ∀ s t, P s t → Unifiable s t (third theorem)` | As for the second theorem, on every input. | tight: counterexample `noOC_verdict_transfer_uniform_needs_hP` | chk := Option.isSome and P s t := ¬ Unifiable s t: hchk holds on every input (soundness of unify), hP fails at u8 =? u32, and the conclusion fails at X =? Box X, where unifyNoOC returns a substitution although the pair has no unifier. |
| `hchk : chk (unify s t) = true → ¬ P (second theorem)` | The verdict must be sound for unify to begin with. | tight: counterexample `noOC_verdict_transfer_needs_hchk` | The constant verdict true with P := Unifiable on X =? u8. |
| `hchk : ∀ s t, chk (unify s t) = true → ¬ P s t (third theorem)` | As for the second theorem, on every input. | tight: counterexample `noOC_verdict_transfer_uniform_needs_hchk` | The constant verdict true with P := Unifiable: hP holds on every input, and hchk and the conclusion both fail at X =? u8. |
| `h : chk (unifyNoOC s t) = true (second theorem)` | The claim concerns the variant's 'disjoint' verdict. The third theorem has no such hypothesis: there chk (unifyNoOC s t) = true is the antecedent of the universally quantified conclusion. | tight: counterexample `noOC_verdict_transfer_needs_noOC_verdict` | chk := Option.isNone, P := Unifiable on X =? u8, where the variant's verdict is false. |

**Depth.** shallow — Completeness of unify plus agreement of the variant on inputs where unify succeeds.

**Non-vacuity witness.** impl<T> Tr for Vec<T> and impl<U> Tr for Box<U>: renamed apart and the occurs-check-free checker says disjoint; for the second theorem, P = header overlap of that pair with chk = Option.isNone, all three hypotheses including chk (unifyNoOC …) = true; for the third, chk = Option.isNone and P = Unifiable satisfy both hypotheses, and the verdict fed unifyNoOC fires on u8 =? u32 (so the antecedent of the conclusion is satisfiable) and does not fire on X =? Vec Y or on X =? Box X. In every instance satisfying all hypotheses of the second theorem P is false, since that is its conclusion; the uniform version is the non-trivial reading. (`not_headersOverlap_of_overlapCheckSaysDisjointNoOC_nonvacuous`, `noOC_verdict_sound_of_unify_verdict_sound_nonvacuous`, `noOC_verdict_sound_of_unify_verdict_sound_uniform_nonvacuous`)

**Positive control.** `noOC_check_false_disjoint_without_renaming`, `noOC_verdict_transfer_needs_hP`, `noOC_verdict_transfer_needs_hchk`, `noOC_verdict_transfer_uniform_needs_hP`, `noOC_verdict_transfer_uniform_needs_hchk`

**Prior art.**
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties.
- rustc-dev-guide, chapter "Coherence", file src/coherence.md of https://github.com/rust-lang/rustc-dev-guide at commit 33fa6bef32eee98a8e38c9376645cf6fbcb2ca67 (consulted). It describes overlap checks on pairs of impls that unify the impl headers (its example obtains ?E = &str), the implicit negative impl check impl_intersection_has_impossible_obligation (an overlap is impossible when an obligation cannot hold, using that downstream crates cannot implement a remote trait for a remote type), and the orphan check, which guards against impls that could be added by upstream crates in a backwards-compatible way or by downstream crates.
- K. R. Apt and A. Pellegrini, "On the occur-check-free PROLOG programs", ACM Transactions on Programming Languages and Systems 16(3):687-726, 1994, doi:10.1145/177492.177673 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Studies when unification without the occurs check is safe, building on the notion of equation systems "not subject to occur-check" (NSTO); the relationship of that notion to results 7 and 19 is stated from secondary descriptions and was not checked against the full text.
- R. A. Eisenberg, D. Vytiniotis, S. Peyton Jones and S. Weirich, "Closed type families with overlapping equations", POPL 2014, pp. 671-683, doi:10.1145/2535838.2535856 (bibliographic data verified via the Crossref record; author-hosted full text consulted). Its apartness check (Definition 6) uses ordinary first-order unification; Section 6.1 shows with the pair (a, a) and ([b], b) that an occurs-check-based apartness verdict becomes unsound in the presence of non-terminating type families, Section 6.2 defines unification over infinite types (Definition 19) and conjectures, without proof, that using it restores soundness, and Section 6.3 reports that GHC uses it for the overlap check of open type families.

**Design question.** Can omitting the occurs check make a coherence checker accept overlapping impls?

**Non-claims.** Listed under Boundaries, result 19; read them before relying on this result.

Basis: execution (Lean kernel check) — every theorem quoted in this result and every counterexample, non-vacuity and positive-control theorem it names (quoted here or under "Auxiliary declarations cited by name"); axioms and hashes under Evidence.

Basis: derived (modeling bridge) — rustc's overlap check compares two impl headers by unifying them (rustc-dev-guide, Coherence chapter, pinned commit). The toy check overlapCheckSaysDisjointNoOC models the header-unification part of such a check for traits without type parameters. rustc additionally handles trait parameters, lifetimes, associated types, negative impls, specialization and the orphan check; none of these is modeled. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about rustc.

### Auxiliary declarations cited by name

Every package-local declaration named above that is not quoted as a main statement, a definition or an example object.

#### `BindingOK`

```lean
-- lean/ToyUnify/UnifyLemmas.lean:253-254
def BindingOK (V : List Nat) (p : Nat × Term) : Prop :=
  p.1 ∈ V ∧ (∀ z ∈ p.2.vars, z ∈ V) ∧ p.2 ≠ .var p.1
```

#### `ChainInv`

```lean
-- lean/ToyUnify/OccursCheck.lean:623-625
def ChainInv (eqs : List (Term × Term)) (acc : Subst) : Prop :=
  (acc.map Prod.fst).Nodup ∧ ∀ p ∈ acc, ∀ z, p.2 = .var z →
    (∀ q ∈ acc, p.1 ∉ q.2.vars) ∧ p.1 ∉ eqsVars eqs ∧ (∀ q ∈ acc, q.1 = z → ∀ w, q.2 ≠ .var w)
```

#### `Implements.isGround`

```lean
-- lean/ToyUnify/Impls.lean:85-86
theorem Implements.isGround {I : ImplSet} {tr : Nat} {ty : Term} (h : Implements I tr ty) :
    IsGround ty := by …
```

#### `Inv`

```lean
-- lean/ToyUnify/UnifyLemmas.lean:531-532
def Inv (eqs : List (Term × Term)) (σ : Subst) : Prop :=
  (σ.map Prod.fst).Nodup ∧ (∀ p ∈ σ, ∀ q ∈ σ, q.1 ∉ p.2.vars) ∧ ∀ q ∈ σ, q.1 ∉ eqsVars eqs
```

#### `LimEq`

```lean
-- lean/ToyUnify/OccursCheck.lean:412-413
def LimEq (σ : Subst) (a b : Term) : Prop :=
  ∀ n, ∃ k, eqUpTo n (iterSubst σ k a) (iterSubst σ k b) = true
```

#### `StableUnderDownstream.self`

```lean
-- lean/ToyUnify/Orphan.lean:97-98
theorem StableUnderDownstream.self {fund : Nat → Bool} {I : ImplSet} {trs ctors : List Nat}
    {P : ImplSet → Prop} (h : StableUnderDownstream fund I trs ctors P) : P I := by …
```

#### `Sys`

```lean
-- lean/ToyUnify/UnifyLemmas.lean:421-422
def Sys (τ : Subst) (eqs : List (Term × Term)) (σ : Subst) : Prop :=
  (∀ e ∈ eqs, subst τ e.1 = subst τ e.2) ∧ ∀ p ∈ σ, substVar τ p.1 = subst τ p.2
```

#### `Term.size`

The number of nodes of a term, defined together with its list companion `Term.sizeList`; it appears in the statement of `size_substVar_lt_con`.

```lean
-- lean/ToyUnify/UnifyLemmas.lean:17-26
mutual
/-- The number of nodes of a term. -/
def Term.size : Term → Nat
  | .var _ => 1
  | .con _ ts => Term.sizeList ts + 1
/-- The total number of nodes of a list of terms (companion of `Term.size`). -/
def Term.sizeList : List Term → Nat
  | [] => 0
  | t :: ts => Term.size t + Term.sizeList ts
end
```

#### `agreement_nonvacuous`

```lean
-- lean/ToyUnify/OccursCheck.lean:132-134
theorem agreement_nonvacuous :
    run true (numVars [(pair (.var 0) u8, pair u32 (.var 1))])
      [(pair (.var 0) u8, pair u32 (.var 1))] [] = .ok [(1, u8), (0, u32)] := by …
```

#### `decompAll_bindingOK`

```lean
-- lean/ToyUnify/UnifyLemmas.lean:366-367
theorem decompAll_bindingOK : ∀ (eqs : List (Term × Term)) (bs : List (Nat × Term)),
    decompAll eqs = some bs → ∀ p ∈ bs, BindingOK (eqsVars eqs) p
```

#### `decompAll_none`

```lean
-- lean/ToyUnify/UnifyLemmas.lean:354-355
theorem decompAll_none : ∀ (eqs : List (Term × Term)), decompAll eqs = none →
    ∀ τ : Subst, ¬ ∀ e ∈ eqs, subst τ e.1 = subst τ e.2
```

#### `dupσ_dedup_still_fails`

```lean
-- lean/ToyUnify/OccursCheck.lean:921-923
theorem dupσ_dedup_still_fails :
    (dupσDedup.map Prod.fst).Nodup ∧ (∀ t, subst dupσDedup t = subst dupσ t) ∧
      ∀ k, eqUpTo 2 (iterSubst dupσDedup k dupS) (iterSubst dupσDedup k dupT) = false := by …
```

#### `eqUpTo_iterSubst_converge`

```lean
-- lean/ToyUnify/OccursCheck.lean:787-789
theorem eqUpTo_iterSubst_converge {σ : Subst}
    (hsh : ∀ y z, substVar σ y = .var z → z ≠ y → ∀ w, substVar σ z = .var w → w = z) :
    ∀ (n : Nat) (a : Term), eqUpTo n (iterSubst σ (2 * n) a) (iterSubst σ (2 * n + 1) a) = true := by …
```

#### `eqUpTo_iterSubst_mono_needs_agreement`

```lean
-- lean/ToyUnify/OccursCheck.lean:291-293
theorem eqUpTo_iterSubst_mono_needs_agreement :
    0 ≤ 1 ∧ eqUpTo 1 (iterSubst [] 0 u8) (iterSubst [] 0 u32) = false ∧
      eqUpTo 1 (iterSubst [] 1 u8) (iterSubst [] 1 u32) = false := by …
```

#### `eqUpTo_iterSubst_mono_needs_le`

```lean
-- lean/ToyUnify/OccursCheck.lean:284-286
theorem eqUpTo_iterSubst_mono_needs_le :
    ¬ (1 ≤ 0) ∧ eqUpTo 1 (iterSubst [(0, u8)] 1 (.var 0)) (iterSubst [(0, u8)] 1 u8) = true ∧
      eqUpTo 1 (iterSubst [(0, u8)] 0 (.var 0)) (iterSubst [(0, u8)] 0 u8) = false := by …
```

#### `eqUpTo_iterSubst_mono_nonvacuous`

```lean
-- lean/ToyUnify/OccursCheck.lean:279-280
theorem eqUpTo_iterSubst_mono_nonvacuous :
    0 ≤ 3 ∧ eqUpTo 1 (iterSubst [] 0 (box u8)) (iterSubst [] 0 (box u32)) = true := by …
```

#### `eqUpTo_subst_needs_agreement`

```lean
-- lean/ToyUnify/OccursCheck.lean:269-270
theorem eqUpTo_subst_needs_agreement :
    eqUpTo 1 u8 u32 = false ∧ eqUpTo 1 (subst [] u8) (subst [] u32) = false := by …
```

#### `eqUpTo_subst_nonvacuous`

```lean
-- lean/ToyUnify/OccursCheck.lean:274
theorem eqUpTo_subst_nonvacuous : eqUpTo 1 (box u8) (box u32) = true ∧ box u8 ≠ box u32 := by …
```

#### `exists_orphanOK_iff_needs_ctors_not_owned`

```lean
-- lean/ToyUnify/Orphan.lean:616-619
theorem exists_orphanOK_iff_needs_ctors_not_owned :
    ownersEx.traitOwner 12 ≠ 2 ∧ ¬ (∀ f ∈ localL.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      ownersEx.ctorOwner 7 = 2 ∧ fundSpineVar ownersEx localL = false ∧
      (∃ e : Impl, OrphanOK ownersEx 2 e ∧ e.trait = 12 ∧ CommonGroundInstance e.selfTy localL) := …
```

#### `exists_orphanOK_iff_needs_local_ctor`

```lean
-- lean/ToyUnify/Orphan.lean:591-595
theorem exists_orphanOK_iff_needs_local_ctor :
    (∀ L, ownersEx.ctorOwner L ≠ 3) ∧ ownersEx.traitOwner 12 ≠ 3 ∧
      (∀ f ∈ (Term.var 0).ctors, ownersEx.ctorOwner f ≠ 3) ∧
      fundSpineVar ownersEx (.var 0) = true ∧
      ¬ (∃ e : Impl, OrphanOK ownersEx 3 e ∧ e.trait = 12 ∧ CommonGroundInstance e.selfTy (.var 0)) := by …
```

#### `exists_orphanOK_iff_needs_trait_not_owned`

```lean
-- lean/ToyUnify/Orphan.lean:607-610
theorem exists_orphanOK_iff_needs_trait_not_owned :
    ownersB.traitOwner 12 = 2 ∧ (∀ f ∈ u8.ctors, ownersB.ctorOwner f ≠ 2) ∧
      ownersB.ctorOwner 7 = 2 ∧ fundSpineVar ownersB u8 = false ∧
      (∃ e : Impl, OrphanOK ownersB 2 e ∧ e.trait = 12 ∧ CommonGroundInstance e.selfTy u8) := …
```

#### `exists_orphanOK_overlapping_impl_iff_fundSpineVar_nonvacuous`

```lean
-- lean/ToyUnify/Orphan.lean:434-436
theorem exists_orphanOK_overlapping_impl_iff_fundSpineVar_nonvacuous :
    ownersEx.traitOwner 12 ≠ 2 ∧ (∀ f ∈ (box (.var 0)).ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ f ∈ (vec (.var 0)).ctors, ownersEx.ctorOwner f ≠ 2) ∧ ownersEx.ctorOwner 7 = 2 := by …
```

#### `fundSpineVar_congr`

```lean
-- lean/ToyUnify/Orphan.lean:284-285
theorem fundSpineVar_congr {o o' : Owners} (h : o.fundamental = o'.fundamental) :
    ∀ X : Term, fundSpineVar o X = fundSpineVar o' X
```

#### `headersOverlap_iff_unify_isSome_nonvacuous`

```lean
-- lean/ToyUnify/Impls.lean:353
theorem headersOverlap_iff_unify_isSome_nonvacuous : VarsDisjoint i1.selfTy i2.selfTy := by …
```

#### `implements_append_iff_needs_constrained`

```lean
-- lean/ToyUnify/Orphan.lean:475-480
theorem implements_append_iff_needs_constrained :
    IsGround u8 ∧ ¬ Constrained I_unconstrained ∧ FreshCrate ownersEx 2 I_unconstrained ∧
      ownersEx.traitOwner 12 ≠ 2 ∧ (∀ f ∈ u8.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨13, localL, []⟩] : ImplSet), OrphanOK ownersEx 2 e) ∧
      Implements (I_unconstrained ++ [⟨13, localL, []⟩]) 12 u8 ∧
      ¬ Implements I_unconstrained 12 u8 := by …
```

#### `implements_append_iff_needs_ctors_not_owned`

```lean
-- lean/ToyUnify/Orphan.lean:563-567
theorem implements_append_iff_needs_ctors_not_owned :
    IsGround localL ∧ Constrained [] ∧ FreshCrate ownersEx 2 [] ∧ ownersEx.traitOwner 12 ≠ 2 ∧
      ¬ (∀ f ∈ localL.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨12, localL, []⟩] : ImplSet), OrphanOK ownersEx 2 e) ∧
      Implements ([] ++ [⟨12, localL, []⟩]) 12 localL ∧ ¬ Implements [] 12 localL := by …
```

#### `implements_append_iff_needs_fresh`

```lean
-- lean/ToyUnify/Orphan.lean:519-524
theorem implements_append_iff_needs_fresh :
    IsGround (vec u8) ∧ Constrained I_vecC ∧ ¬ FreshCrate ownersC 2 I_vecC ∧
      ownersC.traitOwner 12 ≠ 2 ∧
      (∀ f ∈ (vec u8).ctors, ownersC.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨13, u8, []⟩] : ImplSet), OrphanOK ownersC 2 e) ∧
      Implements (I_vecC ++ [⟨13, u8, []⟩]) 12 (vec u8) ∧ ¬ Implements I_vecC 12 (vec u8) := by …
```

#### `implements_append_iff_needs_orphanOK`

```lean
-- lean/ToyUnify/Orphan.lean:576-580
theorem implements_append_iff_needs_orphanOK :
    IsGround u8 ∧ Constrained [] ∧ FreshCrate ownersEx 2 [] ∧ ownersEx.traitOwner 12 ≠ 2 ∧
      (∀ f ∈ u8.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      ¬ (∀ e ∈ ([⟨12, u8, []⟩] : ImplSet), OrphanOK ownersEx 2 e) ∧
      Implements ([] ++ [⟨12, u8, []⟩]) 12 u8 ∧ ¬ Implements [] 12 u8 := by …
```

#### `implements_append_iff_needs_trait_not_owned`

```lean
-- lean/ToyUnify/Orphan.lean:550-554
theorem implements_append_iff_needs_trait_not_owned :
    IsGround u8 ∧ Constrained [] ∧ FreshCrate ownersB 2 [] ∧ ownersB.traitOwner 12 = 2 ∧
      (∀ f ∈ u8.ctors, ownersB.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨12, u8, []⟩] : ImplSet), OrphanOK ownersB 2 e) ∧
      Implements ([] ++ [⟨12, u8, []⟩]) 12 u8 ∧ ¬ Implements [] 12 u8 := by …
```

#### `implements_append_iff_of_not_isGround`

```lean
-- lean/ToyUnify/Orphan.lean:292-295
theorem implements_append_iff_of_not_isGround (I E : ImplSet) (B : Nat) {X : Term}
    (hng : ¬ IsGround X) :
    (Implements (I ++ E) B X ↔ Implements I B X) ∧ ¬ Implements (I ++ E) B X ∧
      ¬ Implements I B X := …
```

#### `implements_append_iff_of_orphanOK_nonvacuous`

```lean
-- lean/ToyUnify/Orphan.lean:423-427
theorem implements_append_iff_of_orphanOK_nonvacuous :
    IsGround u8 ∧ Constrained I_AB ∧ FreshCrate ownersEx 2 I_AB ∧ ownersEx.traitOwner 12 ≠ 2 ∧
      (∀ f ∈ u8.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨11, localL, []⟩, ⟨12, localL, []⟩] : ImplSet), OrphanOK ownersEx 2 e) ∧
      ¬ Implements I_AB 12 u8 := by …
```

#### `implsOverlapIn_iff_mgu_instance_needs_bound_vars_disjoint`

```lean
-- lean/ToyUnify/Impls.lean:393-399
theorem implsOverlapIn_iff_mgu_instance_needs_bound_vars_disjoint :
    VarsDisjoint iW1.selfTy iW2.selfTy ∧ ¬ (∀ x ∈ iW1.vars, x ∉ iW2.vars) ∧
      ImplsOverlapIn I_AB iW1 iW2 ∧
      ¬ (∃ σ, unify iW1.selfTy iW2.selfTy = some σ ∧
        ∃ θ : Subst, IsGround (subst θ (subst σ iW1.selfTy)) ∧
          ∀ b ∈ iW1.bounds ++ iW2.bounds,
            Implements I_AB b.trait (subst θ (subst σ b.ty))) := by …
```

#### `implsOverlapIn_iff_mgu_instance_nonvacuous`

```lean
-- lean/ToyUnify/Impls.lean:356
theorem implsOverlapIn_iff_mgu_instance_nonvacuous : ∀ x ∈ i1.vars, x ∉ i2.vars := by …
```

#### `matchAlg_complete_needs_matchable`

```lean
-- lean/ToyUnify/Matching.lean:226-227
theorem matchAlg_complete_needs_matchable :
    ¬ Matchable u8 u32 ∧ ¬ ∃ σ, matchAlg u8 u32 = some σ := by …
```

#### `matchAlg_isSome_iff_unify_needs_ground`

```lean
-- lean/ToyUnify/Matching.lean:261-265
theorem matchAlg_isSome_iff_unify_needs_ground :
    ¬ IsGround (box (.var 0)) ∧ (matchAlg (.var 0) (box (.var 0))).isSome = true ∧
      (unify (.var 0) (box (.var 0))).isSome = false ∧
      ¬ ((matchAlg (.var 0) (box (.var 0))).isSome = true ↔
        (unify (.var 0) (box (.var 0))).isSome = true) := by …
```

#### `matchAlg_nonvacuous`

```lean
-- lean/ToyUnify/Matching.lean:207-209
theorem matchAlg_nonvacuous :
    matchAlg (.var 0) (box (.var 0)) = some [(0, box (.var 0))] ∧
      Matchable (.var 0) (box (.var 0)) := …
```

#### `matchAlg_output_not_idempotent_example`

```lean
-- lean/ToyUnify/Matching.lean:214-217
theorem matchAlg_output_not_idempotent_example :
    matchAlg (.var 0) (box (.var 0)) = some [(0, box (.var 0))] ∧
      ¬ Idempotent [(0, box (.var 0))] ∧
      subst [(0, box (.var 0))] (box (.var 0)) ≠ box (.var 0) := …
```

#### `matchAlg_sound_needs_output`

```lean
-- lean/ToyUnify/Matching.lean:221-222
theorem matchAlg_sound_needs_output :
    matchAlg (.var 0) u8 ≠ some [] ∧ subst [] (.var 0) ≠ u8 := by …
```

#### `matchable_iff_unifiable_needs_ground`

```lean
-- lean/ToyUnify/Matching.lean:322-324
theorem matchable_iff_unifiable_needs_ground :
    ¬ IsGround (box (.var 0)) ∧
      ¬ (Matchable (.var 0) (box (.var 0)) ↔ Unifiable (.var 0) (box (.var 0))) := by …
```

#### `matchable_iff_unifiable_nonGround_example`

```lean
-- lean/ToyUnify/Matching.lean:330-333
theorem matchable_iff_unifiable_nonGround_example :
    ¬ IsGround (box (.var 1)) ∧ Matchable (.var 0) (box (.var 1)) ∧
      Unifiable (.var 0) (box (.var 1)) ∧
      (Matchable (.var 0) (box (.var 1)) ↔ Unifiable (.var 0) (box (.var 1))) := …
```

#### `matchable_iff_unifiable_of_isGround_nonvacuous`

```lean
-- lean/ToyUnify/Matching.lean:319
theorem matchable_iff_unifiable_of_isGround_nonvacuous : IsGround (vec u8) := by …
```

#### `noInstanceImplements_stable_needs_no_matching_impl`

```lean
-- lean/ToyUnify/Orphan.lean:703-707
theorem noInstanceImplements_stable_needs_no_matching_impl :
    fundSpineVar ownersEx (vec (.var 0)) = false ∧
      ¬ (∀ i ∈ I_vecC, i.trait = 12 → ¬ CommonGroundInstance i.selfTy (vec (.var 0))) ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_vecC [12] (vec (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := by …
```

#### `noInstanceImplements_stable_needs_not_fundSpineVar`

```lean
-- lean/ToyUnify/Orphan.lean:715-720
theorem noInstanceImplements_stable_needs_not_fundSpineVar :
    (∀ i ∈ ([] : ImplSet), i.trait = 12 → ¬ CommonGroundInstance i.selfTy (box (.var 0))) ∧
      fundSpineVar ownersEx (box (.var 0)) = true ∧
      NoInstanceImplements [] 12 (box (.var 0)) ∧
      ¬ StableUnderDownstream ownersEx.fundamental [] [12] (box (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (box (.var 0))) := by …
```

#### `noInstanceImplements_stable_of_not_fundSpineVar_nonvacuous`

```lean
-- lean/ToyUnify/Orphan.lean:677-679
theorem noInstanceImplements_stable_of_not_fundSpineVar_nonvacuous :
    (∀ i ∈ I_AB, i.trait = 12 → ¬ CommonGroundInstance i.selfTy (vec (.var 0))) ∧
      fundSpineVar ownersEx (vec (.var 0)) = false := by …
```

#### `noInstanceImplements_vec_not_stable_of_vec_fundamental`

```lean
-- lean/ToyUnify/Orphan.lean:734-739
theorem noInstanceImplements_vec_not_stable_of_vec_fundamental :
    (∀ i ∈ ([] : ImplSet), i.trait = 12 → ¬ CommonGroundInstance i.selfTy (vec (.var 0))) ∧
      fundSpineVar ownersAllFund (vec (.var 0)) = true ∧
      NoInstanceImplements [] 12 (vec (.var 0)) ∧
      ¬ StableUnderDownstream ownersAllFund.fundamental [] [12] (vec (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := by …
```

#### `noInstanceImplements_vec_stable_example`

```lean
-- lean/ToyUnify/Orphan.lean:691-694
theorem noInstanceImplements_vec_stable_example :
    NoInstanceImplements I_AB 12 (vec (.var 0)) ∧
      StableUnderDownstream ownersEx.fundamental I_AB [12] (vec (.var 0)).ctors
        (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := …
```

#### `noOC_check_false_disjoint_without_renaming`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:116-118
theorem noOC_check_false_disjoint_without_renaming :
    ¬ VarsDisjoint iShared1.selfTy iShared2.selfTy ∧
      overlapCheckSaysDisjointNoOC iShared1 iShared2 = true ∧ HeadersOverlap iShared1 iShared2 := …
```

#### `noOC_disjoint_needs_verdict`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:123-125
theorem noOC_disjoint_needs_verdict :
    VarsDisjoint i1.selfTy i2.selfTy ∧ overlapCheckSaysDisjointNoOC i1 i2 = false ∧
      HeadersOverlap i1 i2 := …
```

#### `noOC_verdict_sound_of_unify_verdict_sound_nonvacuous`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:132-137
theorem noOC_verdict_sound_of_unify_verdict_sound_nonvacuous :
    (HeadersOverlap ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ →
        Unifiable (vec (.var 0)) (box (.var 1))) ∧
      ((unify (vec (.var 0)) (box (.var 1))).isNone = true →
        ¬ HeadersOverlap ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩) ∧
      (unifyNoOC (vec (.var 0)) (box (.var 1))).isNone = true := by …
```

#### `noOC_verdict_sound_of_unify_verdict_sound_uniform_nonvacuous`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:95-100
theorem noOC_verdict_sound_of_unify_verdict_sound_uniform_nonvacuous :
    (∀ s t, Unifiable s t → Unifiable s t) ∧
      (∀ s t, (unify s t).isNone = true → ¬ Unifiable s t) ∧
      (unifyNoOC u8 u32).isNone = true ∧
      (unifyNoOC (.var 0) (vec (.var 1))).isNone = false ∧
      (unifyNoOC (.var 0) (box (.var 0))).isNone = false := by …
```

#### `noOC_verdict_transfer_needs_hP`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:158-161
theorem noOC_verdict_transfer_needs_hP :
    ¬ (True → Unifiable iPairSame.selfTy iPairBox.selfTy) ∧
      ((unify iPairSame.selfTy iPairBox.selfTy).isSome = true → ¬ True) ∧
      (unifyNoOC iPairSame.selfTy iPairBox.selfTy).isSome = true ∧ True := by …
```

#### `noOC_verdict_transfer_needs_hchk`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:174-177
theorem noOC_verdict_transfer_needs_hchk :
    (Unifiable (.var 0) u8 → Unifiable (.var 0) u8) ∧
      ¬ ((fun _ : Option Subst => true) (unify (.var 0) u8) = true → ¬ Unifiable (.var 0) u8) ∧
      (fun _ : Option Subst => true) (unifyNoOC (.var 0) u8) = true ∧ Unifiable (.var 0) u8 := …
```

#### `noOC_verdict_transfer_needs_noOC_verdict`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:148-151
theorem noOC_verdict_transfer_needs_noOC_verdict :
    (Unifiable (.var 0) u8 → Unifiable (.var 0) u8) ∧
      ((unify (.var 0) u8).isNone = true → ¬ Unifiable (.var 0) u8) ∧
      (unifyNoOC (.var 0) u8).isNone = false ∧ Unifiable (.var 0) u8 := …
```

#### `noOC_verdict_transfer_uniform_needs_hP`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:184-189
theorem noOC_verdict_transfer_uniform_needs_hP :
    ¬ (∀ s t, ¬ Unifiable s t → Unifiable s t) ∧
      (∀ s t, (unify s t).isSome = true → ¬ ¬ Unifiable s t) ∧
      ¬ (∀ s t, (unifyNoOC s t).isSome = true → ¬ ¬ Unifiable s t) ∧
      (unifyNoOC (.var 0) (box (.var 0))).isSome = true ∧
      ¬ Unifiable (.var 0) (box (.var 0)) := by …
```

#### `noOC_verdict_transfer_uniform_needs_hchk`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:199-202
theorem noOC_verdict_transfer_uniform_needs_hchk :
    (∀ s t, Unifiable s t → Unifiable s t) ∧
      ¬ (∀ s t, (fun _ : Option Subst => true) (unify s t) = true → ¬ Unifiable s t) ∧
      ¬ (∀ s t, (fun _ : Option Subst => true) (unifyNoOC s t) = true → ¬ Unifiable s t) := …
```

#### `not_headersOverlap_of_overlapCheckSaysDisjointNoOC_nonvacuous`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:109-111
theorem not_headersOverlap_of_overlapCheckSaysDisjointNoOC_nonvacuous :
    VarsDisjoint (vec (.var 0)) (box (.var 1)) ∧
      overlapCheckSaysDisjointNoOC ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ = true := by …
```

#### `not_headersOverlap_of_overlapCheckSaysDisjoint_nonvacuous`

```lean
-- lean/ToyUnify/Impls.lean:348-350
theorem not_headersOverlap_of_overlapCheckSaysDisjoint_nonvacuous :
    VarsDisjoint (vec (.var 0)) (box (.var 1)) ∧
      overlapCheckSaysDisjoint ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ = true := by …
```

#### `not_implements_append_needs_neg`

```lean
-- lean/ToyUnify/Orphan.lean:444-448
theorem not_implements_append_needs_neg :
    IsGround u8 ∧ Constrained [⟨12, u8, []⟩] ∧ FreshCrate ownersEx 2 [⟨12, u8, []⟩] ∧
      ownersEx.traitOwner 12 ≠ 2 ∧ (∀ f ∈ u8.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([] : ImplSet), OrphanOK ownersEx 2 e) ∧
      Implements ([⟨12, u8, []⟩] ++ []) 12 u8 := by …
```

#### `not_implements_stable_needs_constrained`

```lean
-- lean/ToyUnify/Orphan.lean:502-505
theorem not_implements_stable_needs_constrained :
    IsGround u8 ∧ ¬ Constrained I_unconstrained ∧ ¬ Implements I_unconstrained 12 u8 ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_unconstrained [12] u8.ctors
          (fun I' => ¬ Implements I' 12 u8) := by …
```

#### `not_implements_stable_needs_neg`

```lean
-- lean/ToyUnify/Orphan.lean:461-464
theorem not_implements_stable_needs_neg :
    IsGround u8 ∧ Constrained [⟨12, u8, []⟩] ∧ Implements [⟨12, u8, []⟩] 12 u8 ∧
      ¬ StableUnderDownstream ownersEx.fundamental [⟨12, u8, []⟩] [12] u8.ctors
          (fun I' => ¬ Implements I' 12 u8) := by …
```

#### `not_implements_stable_of_isGround_nonvacuous`

```lean
-- lean/ToyUnify/Orphan.lean:454-455
theorem not_implements_stable_of_isGround_nonvacuous :
    IsGround u8 ∧ Constrained I_AB ∧ ¬ Implements I_AB 12 u8 := …
```

#### `not_implements_stable_of_not_isGround`

```lean
-- lean/ToyUnify/Orphan.lean:367-369
theorem not_implements_stable_of_not_isGround (fund : Nat → Bool) (I : ImplSet)
    (trs ctors : List Nat) (B : Nat) {X : Term} (hng : ¬ IsGround X) :
    StableUnderDownstream fund I trs ctors (fun I' => ¬ Implements I' B X) := …
```

#### `not_unifiable_var_of_occurs_needs_ne`

```lean
-- lean/ToyUnify/OccursCheck.lean:49-50
theorem not_unifiable_var_of_occurs_needs_ne :
    occurs 0 (.var 0) = true ∧ Unifiable (.var 0) (.var 0) := …
```

#### `not_unifiable_var_of_occurs_needs_occurs`

```lean
-- lean/ToyUnify/OccursCheck.lean:43-45
theorem not_unifiable_var_of_occurs_needs_occurs :
    occurs 0 (box (.var 1)) = false ∧ box (.var 1) ≠ .var 0 ∧
      Unifiable (.var 0) (box (.var 1)) := …
```

#### `not_unifiable_var_of_occurs_nonvacuous`

```lean
-- lean/ToyUnify/OccursCheck.lean:39-40
theorem not_unifiable_var_of_occurs_nonvacuous :
    occurs 0 (box (.var 0)) = true ∧ box (.var 0) ≠ .var 0 := by …
```

#### `not_unifies_var_of_occurs`

```lean
-- lean/ToyUnify/UnifyLemmas.lean:70-71
theorem not_unifies_var_of_occurs {x : Nat} {u : Term} (hocc : occurs x u = true)
    (hne : u ≠ .var x) (σ : Subst) : subst σ (.var x) ≠ subst σ u := by …
```

#### `orphanOK_uncovered_param_overlap_example`

```lean
-- lean/ToyUnify/Orphan.lean:821-826
theorem orphanOK_uncovered_param_overlap_example :
    FreshCrate ownersEx 2 [iUpBox2] ∧ OrphanOK ownersEx 2 eDownBox2 ∧
      VarsDisjoint iUpBox2.selfTy eDownBox2.selfTy ∧
      subst [(0, localL)] iUpBox2.selfTy = .con 2 [localL, u8] ∧
      subst [(1, u8)] eDownBox2.selfTy = .con 2 [localL, u8] ∧
      ImplsOverlapIn [iUpBox2, eDownBox2] iUpBox2 eDownBox2 := by …
```

#### `overlapCheckSaysDisjoint_needs_verdict`

```lean
-- lean/ToyUnify/Orphan.lean:787-791
theorem overlapCheckSaysDisjoint_needs_verdict :
    VarsDisjoint i1.selfTy i2.selfTy ∧ overlapCheckSaysDisjoint i1 i2 = false ∧
      HeadersOverlap i1 i2 ∧ ImplsOverlapIn (I_AB ++ E_AB) i1 i2 ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_AB (i1.traits ++ i2.traits)
          (i1.ctors ++ i2.ctors) (fun I' => ¬ ImplsOverlapIn I' i1 i2) := …
```

#### `overlapCheckSaysDisjoint_stable_needs_renaming_apart`

```lean
-- lean/ToyUnify/Orphan.lean:798-802
theorem overlapCheckSaysDisjoint_stable_needs_renaming_apart :
    ¬ VarsDisjoint iShared1.selfTy iShared2.selfTy ∧
      overlapCheckSaysDisjoint iShared1 iShared2 = true ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_AB [] []
          (fun I' => ¬ ImplsOverlapIn I' iShared1 iShared2) := by …
```

#### `overlapCheck_needs_renaming_apart`

```lean
-- lean/ToyUnify/Impls.lean:369-374
theorem overlapCheck_needs_renaming_apart :
    ¬ VarsDisjoint iShared1.selfTy iShared2.selfTy ∧
      overlapCheckSaysDisjoint iShared1 iShared2 = true ∧
      HeadersOverlap iShared1 iShared2 ∧ (∀ I, ImplsOverlapIn I iShared1 iShared2) ∧
      ¬ (HeadersOverlap iShared1 iShared2 ↔
          iShared1.trait = iShared2.trait ∧ (unify iShared1.selfTy iShared2.selfTy).isSome = true) := by …
```

#### `run_agreement_needs_run_true_ok`

```lean
-- lean/ToyUnify/OccursCheck.lean:138-139
theorem run_agreement_needs_run_true_ok :
    run true 0 [(.var 0, u8)] [] ≠ .ok [] ∧ run false 0 [(.var 0, u8)] [] ≠ .ok [] := by …
```

#### `run_ne_outOfFuel_nonvacuous`

```lean
-- lean/ToyUnify/Correctness.lean:124-125
theorem run_ne_outOfFuel_nonvacuous :
    numVars [(pair (.var 0) (.var 1), pair (.var 1) u8)] ≤ 2 := by …
```

#### `run_needs_fuel_bound`

```lean
-- lean/ToyUnify/Correctness.lean:179-180
theorem run_needs_fuel_bound :
    numVars [(.var 0, u8)] = 1 ∧ run true 0 [(.var 0, u8)] [] = .outOfFuel := by …
```

#### `run_needs_occurs_check_for_bound`

```lean
-- lean/ToyUnify/Correctness.lean:184-188
theorem run_needs_occurs_check_for_bound :
    numVars [(pair (.var 0) (pair (.var 0) (.var 1)),
        pair (box (.var 0)) (pair (box (.var 1)) (vec (.var 1))))] = 2 ∧
      run false 2 [(pair (.var 0) (pair (.var 0) (.var 1)),
        pair (box (.var 0)) (pair (box (.var 1)) (vec (.var 1))))] [] = .outOfFuel := by …
```

#### `run_true_ne_ok_of_run_false_ok_example`

```lean
-- lean/ToyUnify/OccursCheck.lean:143-145
theorem run_true_ne_ok_of_run_false_ok_example :
    run false 1 [(.var 0, box (.var 0))] [] = .ok [(0, box (.var 0))] ∧
      run true 1 [(.var 0, box (.var 0))] [] = .fail := by …
```

#### `size_substVar_lt_con`

```lean
-- lean/ToyUnify/UnifyLemmas.lean:55-57
theorem size_substVar_lt_con (σ : Subst) (f : Nat) (ts : List Term) (x : Nat)
    (h : x ∈ (Term.con f ts).vars) :
    (substVar σ x).size < (subst σ (.con f ts)).size := by …
```

#### `step_true_next_numVars`

```lean
-- lean/ToyUnify/UnifyLemmas.lean:650-651
theorem step_true_next_numVars {eqs eqs' : List (Term × Term)} {σ σ' : Subst}
    (h : step true eqs σ = .next eqs' σ') : numVars eqs' < numVars eqs := by …
```

#### `subst_of_isGround`

```lean
-- lean/ToyUnify/Term.lean:252
theorem subst_of_isGround {t : Term} (h : IsGround t) (σ : Subst) : subst σ t = t := …
```

#### `unifiable_of_matchable_of_varsDisjoint`

```lean
-- lean/ToyUnify/Matching.lean:274-275
theorem unifiable_of_matchable_of_varsDisjoint {p t : Term} (hdisj : VarsDisjoint p t)
    (h : Matchable p t) : Unifiable p t := by …
```

#### `unifyNoOC_eqUpTo_needs_output`

```lean
-- lean/ToyUnify/OccursCheck.lean:180-183
theorem unifyNoOC_eqUpTo_needs_output :
    unifyNoOC (.var 0) u8 ≠ some [] ∧ (([] : Subst).map Prod.fst).Nodup ∧
      (∀ k, eqUpTo 1 (iterSubst [] k (.var 0)) (iterSubst [] k u8) = false) ∧
      ¬ (∀ n, ∃ k, eqUpTo n (iterSubst [] k (.var 0)) (iterSubst [] k u8) = true) := by …
```

#### `unifyNoOC_eqUpTo_of_nodup_nonvacuous`

```lean
-- lean/ToyUnify/OccursCheck.lean:865-867
theorem unifyNoOC_eqUpTo_of_nodup_nonvacuous :
    unifyNoOC (.var 0) (box (.var 0)) = some [(0, box (.var 0))] ∧
      ([(0, box (.var 0))].map Prod.fst).Nodup ∧ ¬ Unifiable (.var 0) (box (.var 0)) := …
```

#### `unifyNoOC_eq_some_needs_unify_output`

```lean
-- lean/ToyUnify/OccursCheck.lean:128-129
theorem unifyNoOC_eq_some_needs_unify_output :
    unify (.var 0) u8 ≠ some [] ∧ unifyNoOC (.var 0) u8 ≠ some [] := by …
```

#### `unifyNoOC_outOfFuel_example`

```lean
-- lean/ToyUnify/NoOccursCoherence.lean:230-233
theorem unifyNoOC_outOfFuel_example :
    VarsDisjoint loopS loopT ∧ ¬ Unifiable loopS loopT ∧
      (∀ fuel, run false fuel [(loopS, loopT)] [] = .outOfFuel) ∧ unifyNoOC loopS loopT = none ∧
      overlapCheckSaysDisjointNoOC ⟨10, loopS, []⟩ ⟨10, loopT, []⟩ = true := by …
```

#### `unifyNoOC_unifies_iff_needs_output`

```lean
-- lean/ToyUnify/OccursCheck.lean:162-163
theorem unifyNoOC_unifies_iff_needs_output :
    unifyNoOC (.var 0) u8 ≠ some [] ∧ ¬ (Unifies [] (.var 0) u8 ↔ Unifiable (.var 0) u8) := by …
```

#### `unifyNoOC_unifies_iff_unifiable_nonvacuous`

```lean
-- lean/ToyUnify/OccursCheck.lean:171-173
theorem unifyNoOC_unifies_iff_unifiable_nonvacuous :
    unifyNoOC (pair (.var 0) u8) (pair u32 (.var 1)) = some [(1, u8), (0, u32)] ∧
      unifyNoOC (.var 0) (box (.var 0)) = some [(0, box (.var 0))] := by …
```

#### `unify_complete_needs_unifier`

```lean
-- lean/ToyUnify/Correctness.lean:170-171
theorem unify_complete_needs_unifier :
    ¬ Unifies [] u8 u32 ∧ unify u8 u32 = none ∧ ¬ ∃ σ, unify u8 u32 = some σ := by …
```

#### `unify_complete_nonvacuous`

```lean
-- lean/ToyUnify/Correctness.lean:120
theorem unify_complete_nonvacuous : Unifies [(0, u8)] (pair (.var 0) u8) (pair u8 (.var 0)) := by …
```

#### `unify_idempotent_needs_output`

```lean
-- lean/ToyUnify/Correctness.lean:136-138
theorem unify_idempotent_needs_output :
    unify (.var 0) (box (.var 0)) ≠ some [(0, box (.var 0))] ∧
      ¬ Idempotent [(0, box (.var 0))] := …
```

#### `unify_mgu_factor_needs_output`

```lean
-- lean/ToyUnify/Correctness.lean:157-162
theorem unify_mgu_factor_needs_output :
    unify (.var 0) (.var 1) ≠ some [(0, u8), (1, u8)] ∧
      Unifies [(0, u32), (1, u32)] (.var 0) (.var 1) ∧
      subst [(0, u32), (1, u32)] (subst [(0, u8), (1, u8)] (.var 0)) ≠
        subst [(0, u32), (1, u32)] (.var 0) ∧
      ¬ MoreGeneral [(0, u8), (1, u8)] [(0, u32), (1, u32)] := by …
```

#### `unify_mgu_factor_needs_unifier`

```lean
-- lean/ToyUnify/Correctness.lean:144-147
theorem unify_mgu_factor_needs_unifier :
    unify (.var 0) u8 = some [(0, u8)] ∧ ¬ Unifies [] (.var 0) u8 ∧
      subst [] (subst [(0, u8)] (.var 0)) ≠ subst [] (.var 0) ∧
      ¬ MoreGeneral [(0, u8)] [] := by …
```

#### `unify_mgu_factor_nonvacuous`

```lean
-- lean/ToyUnify/Correctness.lean:115-117
theorem unify_mgu_factor_nonvacuous :
    unify (.var 0) (pair (.var 1) u8) = some [(0, pair (.var 1) u8)] ∧
      Unifies [(0, pair u32 u8), (1, u32)] (.var 0) (pair (.var 1) u8) := by …
```

#### `unify_sound_needs_output`

```lean
-- lean/ToyUnify/Correctness.lean:131
theorem unify_sound_needs_output : unify (.var 0) u8 ≠ some [] ∧ ¬ Unifies [] (.var 0) u8 := by …
```

#### `unify_sound_nonvacuous`

```lean
-- lean/ToyUnify/Correctness.lean:109-111
theorem unify_sound_nonvacuous :
    unify (pair (.var 0) (box (.var 1))) (pair (box u8) (.var 0)) =
      some [(1, u8), (0, box u8)] := by …
```

## Boundaries

### Non-claims

What each result does **not** show. These apply in addition to the package-wide scope statement: Model–system relation: none proved; these are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 1. `unify-sound-idempotent`

- These are statements about this toy algorithm on finite terms (run with fuel numVars); they neither establish nor refute the corresponding claims about any production trait solver's unifier. Model–system relation: none proved.
- It does not say unify returns a substitution whenever a unifier exists; that is unify-complete.
- Idempotence is a property of the returned association list read with first-binding lookup; it does not claim the list is minimal (not proved here). That the bound variables of σ are pairwise distinct is part of the solved-form invariant Inv maintained inside the proof, but it is not stated as a theorem about unify here. That they occur among the variables of s and t is not proved here.
- The idempotence counterexample [X ↦ Box X] is exactly what the occurs-check-free variant returns on X =? Box X; nothing here is claimed for unifyNoOC.

#### 2. `unify-most-general`

- Most generality is among finite substitutions over finite terms; it says nothing about infinite (rational) solutions.
- It does not claim σ is the unique most general unifier; most general unifiers are unique up to variable renaming, not literally unique (not proved here).
- The factor τ works because σ is the output of unify; the statement gives no factor for an arbitrary unifier in place of σ (see unify_mgu_factor_needs_output).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 3. `unify-complete`

- unify returns none on a constructor clash, on an occurs-check failure and on fuel exhaustion alike; the equivalence relies on fuel exhaustion never happening with fuel numVars (unify-termination-measure).
- It is about unifiers over finite terms; X =? Box X has no such unifier, although it has a solution among infinite trees (not proved here: no infinite-tree semantics is formalized).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 4. `unify-termination-measure`

- Fuel counts elimination passes, not primitive steps; no bound on running time or on the size of the solved form is claimed (solved forms can be exponentially large; not proved here).
- It does not claim numVars eqs is the least sufficient fuel for every input.
- Without the occurs check the bound fails, and some renamed-apart inputs exhaust every fuel (unifyNoOC_outOfFuel_example), so an occurs-check-free implementation without fuel can fail to terminate.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 5. `occurs-failure-sound`

- It is about unifiers over finite terms; it does not address infinite trees, among which X = Box X has a solution (classical; not proved here).
- It does not claim the occurs check is the sole reason unification fails (constructor clashes are another).
- The algorithm's occurs check `occurs x u` has no guard u ≠ var x; it is sound because decomposition drops trivial equations x =? x, so no binding x ↦ var x is ever formed (decompAll_bindingOK: every produced binding p satisfies p.2 ≠ .var p.1).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 6. `occurs-check-removal-unsound`

- The second instance shows that the returned substitution fails the depth-2 test for every number of unfoldings; that the equations X = Box X, X = Box Y, Y = Vec Y have no infinite-tree solution at all is not proved here (no infinite-tree semantics is formalized).
- The variable Z in the second instance is there to raise the fuel numVars from 2 to 3; without it the variant runs out of fuel and returns none on (X, (X, Y)) =? (Box X, (Box Y, Vec Y)) (run_needs_occurs_check_for_bound).
- It concerns this solved-form algorithm with the occurs check deleted; algorithms designed for infinite (rational) trees, which merge or re-check repeated bindings (Huet 1976; Martelli and Rossi 1984; Jaffar 1984), are not covered.
- It does not show the variant is unsound when no variable is bound twice; see no-oc-infinite-unfolding-sound-without-double-elimination.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 7. `no-oc-agrees-when-unify-succeeds`

- The converse fails: the occurs-check-free run can succeed where the run with the check fails (run_true_ne_ok_of_run_false_ok_example).
- It depends on the variant being this algorithm with the same fuel and with the occurs check as the sole difference; a variant that also reorders, merges or re-checks equations is not covered.
- It says nothing about what the variant returns on non-unifiable inputs (a substitution, a failure, or fuel exhaustion are all possible).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 8. `no-oc-infinite-unfolding-sound-without-double-elimination`

- It is a representation-specific, depth-indexed approximation: no type of infinite or rational trees is constructed, and convergence of the unfoldings to such a tree is not stated as a theorem here.
- The distinctness hypothesis is about the association list as returned (step prepends one binding per elimination and never removes any), not about the substitution it denotes: deleting the shadowed binding from dupσ gives a duplicate-free list that acts identically on every term and still fails the depth-2 test (dupσ_dedup_still_fails). A representation that keeps one binding per variable (a finite map, or post-hoc deduplication) therefore does not by itself make the occurs-check-free output a depth-indexed solution.
- No completeness: the variant may fail or run out of fuel on inputs that have infinite-tree solutions (not proved here).
- The distinctness condition is checked on the output; which inputs lead to double elimination is not characterized.
- The existential k is not a bound on k (the proof yields k = 2n for the output's own bindings, but no bound for s and t is stated).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 9. `matching-vs-unification-differ`

- Matching here keeps the target's variables fixed; it is not matching modulo renaming, nor unification of renamed-apart terms.
- The direction "matchable but not unifiable" depends on the pattern and the target sharing variable names: when they share none, every matchable pair is unifiable (unifiable_of_matchable_of_varsDisjoint).
- It does not say which notion a particular trait solver uses at a given point.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 10. `matching-needs-no-occurs-check`

- Completeness gives some output; it does not claim the output equals a given matcher (they agree on the pattern's variables; not proved here).
- The output need not be idempotent and need not fix the target when pattern and target share variable names: on X against Box X it returns [X ↦ Box X] (matchAlg_output_not_idempotent_example). It instantiates the pattern; it is not meant to be applied to the target.
- It says nothing about problems where the target's variables may also be instantiated; that is unification.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 11. `matching-iff-unification-on-ground-targets`

- Groundness of the target is sufficient, not necessary: for the non-ground target Box Y, X matches Box Y and X and Box Y are unifiable, so the equivalence holds (matchable_iff_unifiable_nonGround_example); for non-ground targets it is not guaranteed for all patterns (matchable_iff_unifiable_needs_ground, matching-vs-unification-differ).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 12. `overlap-check-unification-characterization`

- HeadersOverlap ignores where-clauses: unify succeeding does not imply that the impls overlap in a given impl set (where-clauses-break-converse-nonmonotone).
- Renaming apart is a hypothesis, not something the checker does; with shared variable names its verdict can be wrong (overlapCheck_needs_renaming_apart).
- The stability part holds for the trivial reason that the verdict excludes overlap in every impl set; it is not a statement about any orphan rule, and it holds equally for orphan-disallowed or upstream extensions.
- Not a model of rustc's coherence checker: no trait type parameters, lifetimes, associated types, negative impls, specialization or orphan check.

#### 13. `where-clause-overlap-iff-mgu-instance`

- The right-hand side quantifies over all grounding θ and over derivability in I; it is a characterization, not a decision procedure (derivability in impl sets with recursive where-clauses is not shown decidable here).
- ImplsOverlapIn I i j is a closed-world notion: where-clauses are evaluated in the fixed impl set I, which need not contain i or j. It does not model rustc's open-world checks (impl_intersection_has_impossible_obligation, impl_intersection_has_negative_obligation), which reason about impls that other crates could add; that a where-clause is not derivable in the current I does not make an overlap impossible in that open-world sense (negative-reasoning-unstable).
- Overlap is relative to the given impl set; it is not preserved by adding impls (where-clauses-break-converse-nonmonotone).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 14. `where-clauses-break-converse-nonmonotone`

- The added impl `impl B for u8` is not claimed to be writable by a downstream crate under the orphan rule; for an orphan-allowed downstream extension with the same effect see negative-reasoning-unstable.
- It does not say how rustc treats this pair of impls.

#### 15. `ground-negative-facts-stable-downstream`

- Implements I tr ty implies IsGround ty (Implements.isGround), so ¬ Implements I B X for an open X is trivially true and must never be read as NoInstanceImplements I B X ("no instance of X implements B"); negative reasoning over open types is not covered and can be unstable (negative-reasoning-unstable).
- The extensions are by a single fresh downstream crate; impls added by upstream crates in later versions, which RFC 1023's restriction on negative reasoning is chiefly about, are not modeled, and the theorem gives no stability against them.
- The non-vacuity instance reasons about u8: B from the point of view of a crate that owns neither u8 nor B; RFC 1023 forbids such a crate from relying on ¬(u8: B) in coherence, because an upstream crate could add the impl later. The theorem neither establishes nor refutes that Rust would accept such reasoning.
- Constrained is a hypothesis about I and is stricter in form than Rust's rule that impl parameters be constrained: Rust also counts parameters constrained through associated-type projections (where U: Trait<Assoc = T>), which can introduce constructors absent from the self type. That case is not modeled.
- OrphanOK has no covered-parameter check (orphanOK_uncovered_param_overlap_example); the theorem quantifies over the extensions this permissive rule allows. It neither establishes nor refutes the corresponding statement for RFC 2451's orphan rule, which also differs in other respects (trait type parameters).
- Simultaneous extensions by several crates are not modeled (not proved here).

#### 16. `orphan-addressable-iff-fundamental-spine`

- The first theorem concerns impls that target X directly. The second theorem assumes, besides the spine condition, that no impl of B in I has a self type sharing a ground instance with X; when such an impl has a where-clause, negative reasoning about X can be unstable although no downstream impl can target X directly (noInstanceImplements_vec_not_stable, noInstanceImplements_stable_needs_no_matching_impl).
- The second theorem gives a sufficient condition for stability; it is not claimed to be necessary (not proved here).
- Stability is relative to a fixed set of fundamental constructors (o₀.fundamental): whether the spine of X ends in a variable depends on it, and with every constructor fundamental, negative reasoning over Vec<T> is unstable even for the empty impl set (noInstanceImplements_vec_not_stable_of_vec_fundamental).
- The toy orphan rule (trait owned, or self type local, with fundamental constructors transparent in their first argument) simplifies RFC 1023/2451: no trait type parameters, no ordering conditions, no fundamental traits.
- isLocalTy ignores every argument of a fundamental constructor after the first, and Term enforces no arities, so there is no covered-parameter check: a fresh crate may write impl<A> B for Box<L, A>, which overlaps an upstream non-blanket impl<T> B for Box<T, u8> at Box<L, u8> (orphanOK_uncovered_param_overlap_example). RFC 2451 requires such type parameters to be covered.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 17. `negative-reasoning-unstable`

- It does not claim every negative fact over an open type is unstable: if no impl of B in I has a self type sharing a ground instance with X and the fundamental spine of X does not end in a variable, 'no ground instance of X implements B' is stable (noInstanceImplements_stable_of_not_fundSpineVar); for example, no ground instance of Vec<T> implements B in I_AB, stably (noInstanceImplements_vec_stable_example).
- The instability witnesses use one ownership map (ownersEx), and stability is taken relative to its fundamental constructors, under which Vec is not fundamental (first conjunct of noInstanceImplements_vec_not_stable); the instability does not come from treating Vec as fundamental. Nothing is claimed about upstream changes.

#### 18. `no-oc-checker-false-overlap`

- It shows incompleteness (rejecting impls that do not overlap), not unsoundness; see no-oc-checker-never-false-disjoint. Omitting the occurs check has a further effect:
- Without the fuel bound the occurs-check-free algorithm need not terminate: on the renamed-apart pair (T, (T, T)), (U, ((U, U), (U, U))) every fuel is exhausted (unifyNoOC_outOfFuel_example); here unifyNoOC returns none because the run returns outOfFuel, and the checker says disjoint for that reason.
- Uses of unification with positive polarity, such as deciding that one impl specializes another, would turn the variant's extra outputs into unsound permissions; no such use is modeled (not proved here).
- With associated-type normalization, semantic overlap need not imply syntactic unifiability of the headers (not proved here; not modeled).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about production unifiers, trait solvers or coherence checkers.

#### 19. `no-oc-checker-never-false-disjoint`

- Omitting the occurs check is still harmful: the checker can reject impls that do not overlap (no-oc-checker-false-overlap).
- It holds for this variant (same passes and fuel, with the occurs check as the sole difference). The fuel matters: some renamed-apart pairs exhaust every fuel without the occurs check (unifyNoOC_outOfFuel_example), and the variant's "disjoint" verdict on them comes from fuel exhaustion mapped to none. An implementation that loops instead, or that post-processes cyclic outputs differently, is not covered.
- Escape hatches: if P does not imply unifiability the transfer fails (pointwise with P := True, noOC_verdict_transfer_needs_hP; uniformly with P s t := ¬ Unifiable s t, noOC_verdict_transfer_uniform_needs_hP); this is the situation with associated-type normalization, where semantic overlap need not imply syntactic unifiability (not proved here; not modeled). Positive-polarity uses of unification, such as specialization, are not covered (not proved here).
- These are statements about the toy checkers; they neither establish nor refute the corresponding claims about rustc or any production coherence checker. Model–system relation: none proved.

### Escape hatches of the impossibility result

Result 19 (`no-oc-checker-never-false-disjoint`) says the occurs-check-free checker never reports false disjointness. Each hypothesis, if dropped, defeats it; the witnesses are proved counterexamples in which all other hypotheses hold and the conclusion fails:

- Renaming apart (`hdisj : VarsDisjoint i.selfTy j.selfTy`): without it the checker says disjoint for two impls of one trait whose self types (T, u8) and (u32, T) share the variable T and overlap (`noOC_check_false_disjoint_without_renaming`).
- The verdict's subject implies unifiability (`hP`): with P := True the pointwise transfer fails (`noOC_verdict_transfer_needs_hP`); with P s t := ¬ Unifiable s t the uniform transfer fails at X =? Box X (`noOC_verdict_transfer_uniform_needs_hP`). With associated-type normalization, semantic overlap need not imply syntactic unifiability of the headers (not proved here; not modeled), so this hatch is the relevant one in such settings.
- Soundness of the verdict for `unify` (`hchk`): the constant verdict `true` with P := Unifiable fails pointwise and uniformly at X =? u8 (`noOC_verdict_transfer_needs_hchk`, `noOC_verdict_transfer_uniform_needs_hchk`).
- The variant's verdict fires (`h : chk (unifyNoOC s t) = true`, pointwise theorem): `noOC_verdict_transfer_needs_noOC_verdict`.
- A different algorithm: the result is about `unifyNoOC` (the same passes and fuel as `unify`, with the occurs check as the sole difference). An implementation that loops instead of exhausting fuel, or that post-processes cyclic outputs differently, is not covered.

The counterexample results (6, 9, 14, 17, 18) are existential: each exhibits concrete instances and says nothing about other inputs.

### Tightness status

Every hypothesis of every result is `tight`, with a named, proved counterexample and a recorded witness class (see each result's hypothesis ledger), except `hXg : IsGround X` in result 15, which is `harmless`: for a non-ground X both sides of the first theorem are false and the stability statement holds trivially (`implements_append_iff_of_not_isGround`, `not_implements_stable_of_not_isGround`). No hypothesis has tightness `unknown`.

### Disproved or dropped statements

No result was dropped and no statement of a published result was found false. One candidate statement is false and is not published as a theorem: "if `unifyNoOC s t = some σ` then for every depth n some number k of unfoldings of σ makes s and t agree up to depth n" (that is, result 8 without the distinctness hypothesis `hnd`). Counterexample: `unifyNoOC_eqUpTo_fails_with_duplicate_elimination` (result 6), on the input (X, (X, (Y, Z))) =? (Box X, (Box Y, (Vec Y, Z))). The published statement is `unifyNoOC_eqUpTo_of_nodup` (result 8).

### Not examined

- Infinite (rational) trees as a semantic domain: no type of infinite trees, no infinite-tree solution notion, and no completeness of `unifyNoOC` with respect to one.
- Arity discipline (a well-formedness predicate on terms), sorts, binders, type aliases, associated-type projections and normalization, lifetimes, subtyping.
- Trait type parameters, negative impls, auto traits, specialization, fundamental traits, RFC 2451's covered-parameter rules, upstream crates adding impls in later versions, and simultaneous extensions by several crates.
- Running time, the size of solved forms, and implementations based on union-find, triangular substitutions or multiequations.
- Uses of unification with positive polarity (for example, deciding that one impl specializes another).

### Stronger readings not established

- "Omitting the occurs check is harmless for a coherence checker": not established. The occurs-check-free checker reports false overlap on a concrete pair (result 18), and on the renamed-apart pair (T, (T, T)), (U, ((U, U), (U, U))) the occurs-check-free run exhausts every fuel (`unifyNoOC_outOfFuel_example`).
- "Omitting the occurs check yields a correct unifier for rational trees": not established. For this algorithm it fails on a concrete input whose output binds a variable twice (result 6); the positive result 8 needs distinct left-hand variables in the returned list, is depth-indexed, and comes with no completeness statement.
- "Keeping one binding per variable (a finite map, or deduplication of the output) repairs the occurs-check-free output": refuted for the input of result 6 (`dupσ_dedup_still_fails`).
- "The occurs-check-free checker is never wrong": refuted (result 18). What is proved (result 19) is that its "disjoint" verdict implies `¬ HeadersOverlap` for renamed-apart headers; the corresponding statement about where-clause-aware overlap `ImplsOverlapIn` for the occurs-check-free checker is not stated here.
- "A failed `unify` proves that two types can never be made equal": established for substitutions over finite terms (result 3); X =? Box X has a solution among infinite trees (classical; not proved here).
- "Negative reasoning is stable under downstream extension": established under the hypotheses of result 15 (a ground type X, a constrained impl set, a crate that owns no symbol of I, B or X, orphan-allowed impls) and of result 16 (no impl of B in I has a self type sharing a ground instance with X, and the fundamental spine of X does not end in a variable); refuted for the concrete open negative fact and the concrete where-clause-based non-overlap verdict of result 17.
- "Header unification decides overlap once where-clauses are present": refuted (result 14); for impls whose variables (in self types and where-clauses) are renamed apart, where-clause-aware overlap is characterized by an instance of the unifier returned by `unify` (result 13), and where-clause-based disjointness is not monotone in the impl set (result 14).
- "Every result applies to rustc": not established; Model–system relation: none proved.

## Evidence

### Toolchain and build

- Toolchain: `leanprover/lean4` release `v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (the commit that `refs/tags/v4.34.1` points to, read from the GitHub API on 2026-11-21). Pinned in `lean/lean-toolchain`.
- Lake project `lean/`: `lakefile.toml` with one `[[lean_lib]]` named `ToyUnify` and no dependencies. Modules: `ToyUnify.Term` (terms, substitutions, `occurs`, `IsGround`, `iterSubst`), `ToyUnify.Algorithm` (unifiers, the algorithm, `eqUpTo`), `ToyUnify.UnifyLemmas` (term size, the decomposition specification, the solved-form invariant `Inv`, the system predicate `Sys`, the termination measure), `ToyUnify.DefExamples` (definition examples), `ToyUnify.Correctness` (results 1–4), `ToyUnify.OccursCheck` (results 5–8), `ToyUnify.Matching` (matching; results 9–11), `ToyUnify.Impls` (impls, derivability, overlap; results 12–14 except the stability theorem of result 12), `ToyUnify.Orphan` (crate model, orphan rule, stability; results 15–17 and `overlapCheckSaysDisjoint_stable` of result 12), `ToyUnify.NoOccursCoherence` (the occurs-check-free checker; results 18–19).
- `lake build` succeeds with no errors and no warnings. No source contains `sorry`, `admit` or `native_decide`, an `axiom` or `opaque` declaration, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`. All 805 declarations of the library depend at most on the axioms `propext`, `Classical.choice` and `Quot.sound` (439 depend on no axiom; the union over all declarations is `Classical.choice`, `Quot.sound`, `propext`); the per-declaration record is `audit/axioms.json`.
- Observation date of the build, the axiom audit, the statement hashes and the toolchain commit: 2026-11-21. The bibliographic records of the sources were checked before that date (the exact dates were not recorded); each source entry below states what was checked.

### Kernel-check record

For every Lean name referenced by `results.json` (312 names: results, non-vacuity witnesses, positive controls, counterexamples, and the definitions, examples and lemmas the report cites), the axioms reported by Lean's `collectAxioms`, the SHA-256 of the statement and the SHA-256 of its definition closure (with the closure size), as recorded in `audit/statements.json`. Roles give the result number; "cited" means the name is quoted in that result, in the definitions, among the example objects or under "Auxiliary declarations cited by name", and registered with that result in `results.json`. What is hashed is defined under Revalidation.

| Name | Roles | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Unify.unify_idempotent` | 1 result | `Classical.choice`, `Quot.sound`, `propext` | `0670e72e6714908b29143a33192c936c34fbfe3e02e9237d7574265ea87a4ff2` | `2a183e07487642533014d978b11a11be36e0929d779eb92ff738177a25533747` (60) |
| `Toy.Unify.unify_sound` | 1 result | `Classical.choice`, `Quot.sound`, `propext` | `4340ee937c039a8071544d797b253e55c594c0587693ec9ba66a7731b2e37c6b` | `a3eceb968cc6a890f1eab45d6d5067a555da6d2e5efa5267d4cc228ea1fb3d58` (60) |
| `Toy.Unify.Bound` | 1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Unify.Idempotent` | 1 cited | none | `c557e20df7313d6ee28706525d1989b3ed6aa82759e86e4b13a50acf612b752b` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.Impl.ctors` | 1 cited | none | `8b75d780f73d98dce25a68310156522d5caf3794b7ff9ac0283ad2089f19adff` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.Impl.traits` | 1 cited | none | `8b75d780f73d98dce25a68310156522d5caf3794b7ff9ac0283ad2089f19adff` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.Impl.vars` | 1 cited | none | `8b75d780f73d98dce25a68310156522d5caf3794b7ff9ac0283ad2089f19adff` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.Inv` | 1 cited | none | `affcb8b65dda789430ed52d788106ec3502ffc3a6a08a2bfc64c64e02d46d1b4` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.Result` | 1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Unify.Result.toOption` | 1 cited | `propext` | `8e5326dc096615bdef488a6b330bbe021c647f0b5a32fe10deab9fc4574eb090` | `1749a11426ff29e6013f8913970382b8c91f77fd89ce512e40714f48ab1c82ca` (8) |
| `Toy.Unify.Step` | 1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Unify.Subst` | 1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Unify.Subst.comp` | 1 cited | none | `e339f3e14cb4a1ec0620f6659a580eb0c3a8af114c8e815ce63ce6ed872288d2` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.Sys` | 1 cited | none | `7054199a4b14afe922abbe0c061c0b179b2c57b3c5cd98f2b088bdb6c8d12f8c` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.Term` | 1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Unify.Term.ctors` | 1 cited | none | `359b6e2ba0f3ba122150faa54e1bde21dc492f18f3564b01218d4e63de311650` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.Term.ctorsList` | 1 cited | none | `bebc63844e6ad6e2feaedc3024daf8331228b480907cc6d74dcf1ba558542bac` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.Term.vars` | 1 cited | none | `359b6e2ba0f3ba122150faa54e1bde21dc492f18f3564b01218d4e63de311650` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.Term.varsList` | 1 cited | none | `bebc63844e6ad6e2feaedc3024daf8331228b480907cc6d74dcf1ba558542bac` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.Unifies` | 1 cited | none | `e7b46ac900f8e95750aeb19a931764fd2ff4e963352bbfaba1a899032e59bd78` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.comp_example` | 1 cited | none | `05334d1c76ea0a01e12fee06c0b28b50a51745db3299a8bcbaa902821028c173` | `6fe62b8e48e7322fb6f1ce143476ba4e27a180cf6d6ba9714a7e15c92cfcc8e4` (22) |
| `Toy.Unify.comp_order_example` | 1 cited | none | `59ca32a23b8b68803da3a59fbc174e33f86096dac226fd4786a47c621d1d80c3` | `d5ffbe5bdd3a5cb13c509f789631a00eb3c9a72b160107e5adeafd081e2d1291` (21) |
| `Toy.Unify.ctors_example` | 1 cited | none | `dddb67c77b3efce8bf57c79ac42fc17f0bfacefc8121bf2e53d6251ce82e292d` | `3dd8ae9b1fa78075f197987feabb8d3625764505598112102b9a4a3857ced07b` (18) |
| `Toy.Unify.ctors_var_example` | 1 cited | none | `73cff7ca5f5d08ade10956572f00cb467935f6e0e3bc1ae27c2d6b853dd63969` | `38015e992dd155d14818bd30536029654007b7cc48cba562762f6a2ee9ab8052` (15) |
| `Toy.Unify.decomp` | 1 cited | `propext` | `2a8cdbe66b433ecec0ac294c282b209a280c6f932850937ddbe9679ba5549c5b` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.decompAll` | 1 cited | `propext` | `fcdc580405b6c089ff610df11cfbef25287e982b6aa0cd12c9d2f86374b8c07d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.decompAll_example` | 1 cited | `propext` | `42fec0dc51b8b35f6656340a8dc179ab88a9e8b2cae241185adadd837672dbe8` | `5d82d0856a7ff8d000c543a265cf41c2f45827585c60559a2ac5dedec02e1e04` (24) |
| `Toy.Unify.decompList` | 1 cited | `propext` | `29bb2106e89941d9f4150f853f80a07b933c8f2b83350f400bb0b1c9dd9342f9` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.decomp_arity_clash_example` | 1 cited | `propext` | `1666998d3bd1351f17f3923e16c92c764accd324f45d7061b50fc2bacd3216f3` | `6a14da9c03a0b363484f51d4ab8eb9a36c2d442ae2d8594bd7b4540b8c1318e8` (21) |
| `Toy.Unify.decomp_clash_example` | 1 cited | `propext` | `f0947e846ec87f7635d422d04d32abe67d208aa7c2175db071eea236552591ae` | `6c715b18f8dee168a295cbfa07664bd3296c4fd7738cec0fefb8d52e0affe70f` (22) |
| `Toy.Unify.decomp_example` | 1 cited | `propext` | `958eaa4f7b232a0874090f8a3da26149ffb2be23f4e4ecba96db965bb25f5a1a` | `6028b9e7451ac5bf62fc75c835249aecf552980a14617bdda28104be00805fee` (22) |
| `Toy.Unify.elimBinding` | 1 cited | none | `8bd930bfc980fa7125e4683f27ae4abac7d1f11ab0f4e9daa92e7dfd4c59bb98` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.eqsVars` | 1 cited | none | `77d2e4612a980f50925eea425fd6c384579097225345bab18c39d742ce7f2c73` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.idempotent_example` | 1 cited | `Classical.choice`, `Quot.sound`, `propext` | `7fad50d535ec47dcbc66d9422d007fac249a9abf5118d269c96432137b077d46` | `b2426fa3713bfebb6c17dd53d57e9a3525640700e1ac562aa9ab6081cea72090` (21) |
| `Toy.Unify.impl_ctors_example` | 1 cited | none | `fdb29cd6bfc1973abb83f65fc6a54ec13032174876aa874a98ae83bd6461fd9b` | `73debe55fdc95831a013364d727154b404baad677468dd9777618e268e2cf899` (25) |
| `Toy.Unify.impl_ctors_nil_example` | 1 cited | none | `3f4cec8c26aae364099e7194e5022aea7dc0edb67dd8ea240891ec037011b8a4` | `59baeae8db5318438b5c41ad3f7cfc7ca525c1557e3ae7f0edd54e4a76d109cb` (24) |
| `Toy.Unify.impl_traits_example` | 1 cited | none | `ee1f235114b87a50ee491ba4d85697182d9ef066497f703142447c29f0b9513c` | `866980bd1caeaa040fd3ef7a502f495152ffd59ca325764565cdeb612522c759` (12) |
| `Toy.Unify.impl_vars_example` | 1 cited | none | `e55f5b00d40718e340855dfb16c9a24743f0e617ad3726462765da3bc66c6425` | `fa719aa42cf55d12cfef099222b66ee0b8e5ff6138c51f74fed2380a95e54e4f` (24) |
| `Toy.Unify.implements_isGround_example` | 1 cited | none | `02b0cf3db2911d21edb9def411ddde398aeedda1a19b7de7bf77bdfb3e56aacb` | `bd5585e59d5b8e4ad25efca027c20eced0260287de3256b997e72e81e24aaed2` (41) |
| `Toy.Unify.implements_via_bound_example` | 1 cited | `propext` | `c37ca34afe2bb55e743788ef7fb4621aa0a9b862d5a46ebdac422662297b927c` | `bd5585e59d5b8e4ad25efca027c20eced0260287de3256b997e72e81e24aaed2` (41) |
| `Toy.Unify.loopEqs` | 1 cited | none | `a19a3a929c7c012b19abca1ec9cd51a6d3403caec87ee2c4857bf12d0d1cb487` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.not_idempotent_example` | 1 cited | none | `13b0d84adc79bb8b9fdc07a40be9c133b1e17018f0179c335fc733ce2752c051` | `bfc7735020e7707f93a3e2d95f901b761138de1da872d29e659bf0c066e6a0e8` (20) |
| `Toy.Unify.not_mem_impl_traits_example` | 1 cited | `Quot.sound`, `propext` | `3eb8fa5d99c2d693833d6a17fed1ca88656ba6792f2c5e9766b6ae74cf3a6f26` | `866980bd1caeaa040fd3ef7a502f495152ffd59ca325764565cdeb612522c759` (12) |
| `Toy.Unify.not_mem_impl_vars_example` | 1 cited | `Quot.sound`, `propext` | `327aa3e1170b8d543c8e4c45c0bbb49ff3ecf5b60c07d8e1fdf27828840ea3bc` | `fa719aa42cf55d12cfef099222b66ee0b8e5ff6138c51f74fed2380a95e54e4f` (24) |
| `Toy.Unify.not_unifies_example` | 1 cited | none | `3ed07784de6b263582f0f73fc36fbfbe065519eacd0b614644d0544f889d01f9` | `fa272daab5f5b991049b8d1e317edb365831cc367aa977dcaa8b78b27d786f0a` (22) |
| `Toy.Unify.numVars` | 1 cited | none | `eec11d38a0d3798f68e3eef2c0d98dfbabf481c3c360428764a1c4ca27d1775f` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.numVars_dedup_example` | 1 cited | none | `8241178b589b5539f7e2dc3af665b7dc0541cb4c91a2f6b213791e87dfdb823b` | `11f506b496a60003a9b6bdb8eaea5e6b1b13216131e04ce5549d3c679085208b` (18) |
| `Toy.Unify.numVars_example` | 1 cited | none | `582e9c7ea938524f085bca8ea4d99f7c9e7c371bf73074ca4fd3cf66ea26e374` | `11f506b496a60003a9b6bdb8eaea5e6b1b13216131e04ce5549d3c679085208b` (18) |
| `Toy.Unify.run` | 1 cited | `propext` | `880b027cc701cd5a68d0cf25eac221a807b0436e349507192525cc93953e7d8f` | `1749a11426ff29e6013f8913970382b8c91f77fd89ce512e40714f48ab1c82ca` (8) |
| `Toy.Unify.run_outOfFuel_example` | 1 cited | `propext` | `fb586416793e2a6ba901bfcda5a5dcda6e3b52bdb4eb8cf2475946feeee0b87e` | `5bf50fa35fc2cf26e4fe4ad56a295bb9bd11308f10941d086e66c1f83c815882` (51) |
| `Toy.Unify.step` | 1 cited | `propext` | `553da34a8a00e68203ca6200cc3e90b134522d9ea3d2b91dfcd12812e0b6c9b6` | `3e28456e2a0f7cedc1f31cba856389eec487c98d35dd23b90b03e7a60f611d9e` (11) |
| `Toy.Unify.subst` | 1 cited | none | `e26fc3b808843377d8310bc5c7a06785b552e683e2250c020004c3e179df1758` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.substList` | 1 cited | none | `4ec5af0261c73cad551d5db7ed38945893bbb45d83612c4ae425f7aabadf1f19` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.substVar_first_binding_example` | 1 cited | none | `147c1098529d063b09f8b7b32db17bf9c37945684ba81111946f233a441fcf6e` | `23aeb57295e747a1fd34a604ca7c4a5722f78ec25f9eef24e27c81b868b46725` (8) |
| `Toy.Unify.substVar_unbound_example` | 1 cited | none | `033c9b15a1508dab700e39491f80f24f3c804ffe93a5cbefb193d093a52d472e` | `c1037ddd7ada66aef515ee869b563e8078a6c99d3072ade2680f77375a80adb2` (7) |
| `Toy.Unify.subst_comp` | 1 cited | `Classical.choice`, `Quot.sound`, `propext` | `d818d6d28aab5a0d4f3dbede3ca9fa8fe3d4884e6380c136157f75fbbd97847b` | `05e0871319b864b32ec6dfd0c3a584391347d5914ce2062549d7fbab09a30bc4` (19) |
| `Toy.Unify.subst_example` | 1 cited | none | `9d4a06833d2d0a633c594287cd66359c7a4bc6d0d0b92935d1ce970f551102a7` | `c3a0157047674ff9a8f03a0b1e084432e431fdb259b0778af3ab2c92924a4d47` (21) |
| `Toy.Unify.subst_ne_example` | 1 cited | none | `d6991f79feaa27390b11f614e3fd221535b6ea27120db754f3a2b1d54b73d095` | `8c943da1722bd1726ba275209455642bda2cf721d8f63c7873c2e2cd1ec8a73e` (20) |
| `Toy.Unify.term_arity_ne_example` | 1 cited | none | `0191d277ee75ce9780a7e57ba8dc59f4827b2a34ffc095d5450e7e756c349606` | `8ddd1cfff76f7df4afb217590af70ae21fbeec86301a6d45a2bfda0c53bcb6bc` (5) |
| `Toy.Unify.term_eq_example` | 1 cited | none | `e0612551d3d6340c13569aa1c5ffd915f871f1e254f7894d4f18b31e8ab3d98f` | `ff3e14043dfd9ca443b8543a0c30868faa03db3b5aacd1bc5da041ed4c370c6b` (5) |
| `Toy.Unify.term_ne_example` | 1 cited | none | `445367465a49ef645627c1e05a67a97b7ca30c3565fbeddb0b9fae6345429f87` | `fbcc856a67a8cad332f1684d4592ad0badfc93a34022ed4ce4049025a43d8adf` (6) |
| `Toy.Unify.unifies_example` | 1 cited | none | `4d39aef81824c11a660ef95069e0f08e613ba6481eb4d375f611d9d86c8cb703` | `debde9d249b51d23392d5984746f501df68e378617f883423981423ecf759aa6` (21) |
| `Toy.Unify.unify` | 1 cited | `propext` | `92cb4a6bfef08ce43855282867e62410fcb444eaa2f33c095c44a8dcb66a2bec` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.unify_clash_example` | 1 cited | `propext` | `1255acef841708bca682dcc098ba4ec504d38ed34f4d350abc1c16a289bb1c7b` | `0375aed5aa6c4c52dfcc04f057f455d0cb7cd98ce3864f438dc76c713a275af6` (61) |
| `Toy.Unify.unify_example` | 1 cited | `propext` | `80528686d3e6afa32bde063c00c58fbb71e7597816f9cf5ae54522cd152ddf2d` | `3b6fc0fcb43dd0767603d24d6a752582c961c0a686f941b7944b81a7181416fa` (62) |
| `Toy.Unify.unify_idempotent_needs_output` | 1 counterexample | `propext` | `8174333cc9a55fd5cb4f62eed80a600e8b84d7bcc865e7c8fd11dff5d650bc07` | `fe3359b2d078c926c6db13e2ec0feaf657fff371369eca38392f0894d757bc2f` (61) |
| `Toy.Unify.unify_occurs_example` | 1 cited | `propext` | `a28267f20c424fc8ce8005c1699e27fe7a858d7407edd762c46fc836c0d35ab2` | `e329cbf9be06a7f4d6c70904b9c73dc0f03cb479b202504f26080ecf29112836` (60) |
| `Toy.Unify.unify_sound_needs_output` | 1 counterexample | `propext` | `6915c869391b6b0a248b71f3912d9f09f849472a03a9d260b95c3ce02fbe8e30` | `b1e5ab4de0b1fb25382fd9bb1766a44fcd3a76856174fd413ccb6121929530e7` (61) |
| `Toy.Unify.unify_sound_nonvacuous` | 1 non-vacuity | `propext` | `c33b0e3d86e29370eeb63050bd9b1314e51e93d9090fcacfd67e918e2826a988` | `fd9d95a85e0f59052758c2a97f6462ef254e46002ae1cdd5ae77e0fee849f978` (62) |
| `Toy.Unify.vars_example` | 1 cited | none | `ebd276a8b51e181c99fb5a3d00d8e981a0baf628602804f839d7383003dfd133` | `821031fdacd57a76d1100a62b752f79db733432d156f687d8845031a91a00700` (17) |
| `Toy.Unify.vars_ground_example` | 1 cited | none | `0b9ca18d5c00b5ee80aa27fa74800d9f967509db66fbe5e03c4a143484b197d1` | `777a8a70fd5a4faf26ad51a53223210a36dca2ad2c133be32dcd6ea2a1459797` (17) |
| `Toy.Unify.unify_mgu_factor` | 2 result; 13 cited | `Classical.choice`, `Quot.sound`, `propext` | `f3b1d30eacc30ecf5df19c81ddfcdc8bef4e38207a2633b70f80bba1451b62b5` | `a3eceb968cc6a890f1eab45d6d5067a555da6d2e5efa5267d4cc228ea1fb3d58` (60) |
| `Toy.Unify.unify_moreGeneral` | 2 result | `Classical.choice`, `Quot.sound`, `propext` | `2d339b7cd3666b484af01d0f3764f28da6e9758eb81adf9105aba95dbdb5d582` | `b7c3cb59cf55e82dd6e32f932566f9b1f97f0749cc10d40fc443bb41a2b6ad68` (61) |
| `Toy.Unify.MoreGeneral` | 2 cited | none | `b63740feced68a565c8e6c83f9e04536f0cd6387af48c9bb9018c903e775885d` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.moreGeneral_example` | 2 cited | `Classical.choice`, `Quot.sound`, `propext` | `c80e03656ff0379fa2d120a0acfb491407b158f7d0c53ae0fa38df9c69216f52` | `113a55da53d6a44649d49a3b54a6514492f42fa4acdebec56f0b4a164547f27e` (20) |
| `Toy.Unify.not_moreGeneral_example` | 2 cited | `Classical.choice`, `Quot.sound`, `propext` | `4ccada7ddbb5814ce882b60d973eb5c1480bad28857405d2281507b588ab75d2` | `113a55da53d6a44649d49a3b54a6514492f42fa4acdebec56f0b4a164547f27e` (20) |
| `Toy.Unify.unify_mgu_factor_needs_output` | 2 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `bdda733f3504114732530426d7b2a1b97e91cb717ee365b2d85c57098a843df2` | `48c9419f0337f9d2bb0df6daab32eb0bb9712861e25fd4b2d3c1030e816f6197` (63) |
| `Toy.Unify.unify_mgu_factor_needs_unifier` | 2 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `4ec59e11ba0db3d518091a51c2556b3dcf2562864c568448bc7f083f00e47992` | `3d2bd422fa24867166c50ed99bbb68cec66ab3d9705d88751ffce58e51e8fbf5` (62) |
| `Toy.Unify.unify_mgu_factor_nonvacuous` | 2 non-vacuity | `propext` | `21bf3fe77742fce7cd9c7faea8e3f000c881aab232bc19a1c24d223cffd6984a` | `085c505d476508c3395add8dbe69613d4c6eeb99ccdb977fc22fbf54fd19f421` (63) |
| `Toy.Unify.unify_complete` | 3 result | `Classical.choice`, `Quot.sound`, `propext` | `03e959a96a017660516da5dfe5ae94439f62ee278fef4bf0773cd6ca15b647e7` | `a3eceb968cc6a890f1eab45d6d5067a555da6d2e5efa5267d4cc228ea1fb3d58` (60) |
| `Toy.Unify.unify_eq_none_iff` | 3 result | `Classical.choice`, `Quot.sound`, `propext` | `b14109985375dde70bbcd6069a177117cce83a77710f65802550179ca31d6851` | `a19c110bf12bc86fa1b71187b23b85abea9d9c4779c6f2e2c93f9fdd78a73ac8` (61) |
| `Toy.Unify.Unifiable` | 3 cited | none | `06ae07e50925fcb30f1b151bdd8ce2fe592423d98fa685bbfa6124fdb623b699` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.decompAll_none` | 3 cited | `propext` | `0cedd5d7b855311c47f9a577b5ba927a12a8229530acb785a65ccefa12f2b79a` | `549b36b67af44f702d2dcedf7d6de402bf65f721bf8c4e52041bc5d27b337207` (30) |
| `Toy.Unify.not_unifiable_u8_u32` | 3 cited | `propext` | `b525afe18c173fea15090ac25a11c526f81dbf54dafa6aa8cca02718a17235f3` | `e78b3e9c8a0da2214485fcb3d443a676de1f4d3d30e7dae8d23de198e3ec05ec` (22) |
| `Toy.Unify.not_unifiable_var_box` | 3 cited | `Quot.sound`, `propext` | `4103a62334059f5422f0ee2117ab49c5755c52989c02ae60e1b15854da02b481` | `96302457b3837d7ea313c5887126ac8312ee7c6fe6adfd20c2b42a4fa4363317` (21) |
| `Toy.Unify.not_unifies_var_of_occurs` | 3 cited | `Quot.sound`, `propext` | `90e62b5e14619494c503e856b7f20ec6d5c8fe3bde4920bee3b6978d7b59a78b` | `09ed9a210f7e6afebd8c253fb96f5d9e85a42e0b41882f68a8dd9f8436b6332d` (22) |
| `Toy.Unify.unifiable_example` | 3 cited | none | `22bee9ad8507e4929a938a041110cdb6ac0d5ea0e893409c6cabbab6ad30c77a` | `17ab74abf317112aa6d262e62bebe4265ee86d7328afc35d2ce237bddc3b5efa` (23) |
| `Toy.Unify.unify_complete_needs_unifier` | 3 counterexample | `propext` | `1d2989c6e06385ce778f33208bb942fa98f906396bad8c6076ec0e59c2fe2cb5` | `0343410cc86abdffecc059bf59f05641d20d4798eb0e19b2a0f8d7e009b68b19` (62) |
| `Toy.Unify.unify_complete_nonvacuous` | 3 non-vacuity | none | `4d39aef81824c11a660ef95069e0f08e613ba6481eb4d375f611d9d86c8cb703` | `debde9d249b51d23392d5984746f501df68e378617f883423981423ecf759aa6` (21) |
| `Toy.Unify.run_ne_outOfFuel_of_numVars_le` | 4 result | `Classical.choice`, `Quot.sound`, `propext` | `fa5aae2f50806890f88862c3f20fdd7e594a31205d41974eed8754490f483fe1` | `488ffb28c1922196f278a193fa53349eeee06edc47796886dc685665338b2387` (52) |
| `Toy.Unify.run_ne_outOfFuel_nonvacuous` | 4 non-vacuity | none | `4e003bdd5f16ac93db4eeca0c2f103851f271b9c7355e043e4b074555a28e5ac` | `902cc11e0e0ac5414e157aea235ddfe0b51f57c72547c4cd6f5eaafc66920349` (19) |
| `Toy.Unify.run_needs_fuel_bound` | 4 counterexample | `propext` | `fada50833bd111a79030b952d2148a0d34daefd36ce348fed626ad11e43eb4df` | `d9419a5c4d846eaafb2411eb2b36b65dd9b25d51d75236eef008d627f0e276fc` (53) |
| `Toy.Unify.run_needs_occurs_check_for_bound` | 4 counterexample; 6 cited | `propext` | `d47c1ee33e48f4edf11e16f8e6db4ce622e7ceae7341d5a8c56929f50719f13c` | `57772f01dae756306034a8093293b7668d8b51d9c7b72b7369748544fb228137` (55) |
| `Toy.Unify.step_true_next_numVars` | 4 cited | `Classical.choice`, `Quot.sound`, `propext` | `52d0d62e29874f5598ff8e08cf0799441ec69c2e113bdc0b3e25e26412b5ebba` | `07a68452dd5c85b3b4f791ece0f93a3192a96a1aae456ea6ccfeb959a1d9dda7` (46) |
| `Toy.Unify.unifyNoOC_outOfFuel_example` | 4 cited; 18 cited; 19 cited | `Classical.choice`, `Quot.sound`, `propext` | `a41aa302f859ded282b6bca2d772ee4e4ca3554721fbc718d9136f4982de56ff` | `2a3aed2ff5fa45623d6adc1299cc851f1f3de74c7a3921f9302a2c468d5fa886` (72) |
| `Toy.Unify.not_unifiable_var_of_occurs` | 5 result | `Quot.sound`, `propext` | `5aa60a8b2dc8099a64ce5554aaf3aaf346c8029612eec879df12c34effedc8fb` | `7bfff5573d4d4b6c45a78355ed0f57dbeb6dbc350a9235451b3ea80c7c0dc332` (24) |
| `Toy.Unify.BindingOK` | 5 cited | none | `975be0b221953fc213ac4522b868b2a44469c3bf7baf080a36d3900ace17ac6c` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.Term.size` | 5 cited | none | `ce9c7bc2ce2f438b56029b0bb67cbc85eebfb996565b2aa2a4d502e6f4e708ea` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.Term.sizeList` | 5 cited | none | `a45d9a9a7963ef9152297f6013a39438944bce2407f78cc21db4b2ffddd637e0` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.decompAll_bindingOK` | 5 cited | `Quot.sound`, `propext` | `f4350117e66b24a8b1cc1a1dc4ee5b1fab995dd3220c731adda54b3f6a357f40` | `ff7ffbd4194b1a19603a270e5f42c5bb6b8306d047fdc3b3a1d3ec8cb29ed76c` (29) |
| `Toy.Unify.not_occurs_example` | 5 cited | none | `291d4e3621f025e0cda1f2b8f5cebe3526d3461a480ac3587f75eb80c2e3eca4` | `233ee4dd6ba9aaf31cc6a34ed39da0931dc838bcece08dccf69df81fe8909340` (19) |
| `Toy.Unify.not_unifiable_var_of_occurs_needs_ne` | 5 counterexample | none | `2c5f3f96b88e214eba6224160ee7cef7fb0063685c64c5349d765f3c55c2c692` | `7bfff5573d4d4b6c45a78355ed0f57dbeb6dbc350a9235451b3ea80c7c0dc332` (24) |
| `Toy.Unify.not_unifiable_var_of_occurs_needs_occurs` | 5 counterexample | none | `88730502b08383df9c7f076620d82566fb729ce1e4d484bde0f0ef3fddab96e8` | `54656e709d087f5ce8f62f83793968d34656fcba8978c320e0bffabb7a96e9a3` (25) |
| `Toy.Unify.not_unifiable_var_of_occurs_nonvacuous` | 5 non-vacuity | none | `32a62468ae5da8639a6a7ead6eaa8f11403dd16a731401cb6c830c01547aeb22` | `1255ef0fe2baaeb8fa3e88c94561a29a2f33f0cfeaa9dafd40e4f80f4c11a4e3` (17) |
| `Toy.Unify.occurs` | 5 cited | none | `5a6d1b561f91013ac6371c4af11586513ddd516cc64b8cb5b9361bee58f200b8` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.occurs_example` | 5 cited | none | `612d95e2309956041e4399ea178505e1b4aeb07ce42dbb649c6d7e88bf067685` | `233ee4dd6ba9aaf31cc6a34ed39da0931dc838bcece08dccf69df81fe8909340` (19) |
| `Toy.Unify.size_substVar_lt_con` | 5 cited | `Quot.sound`, `propext` | `612c13131b2d259aa3afbdc43c89acf4d1968aca39bde9e43413ce5a93be0d4f` | `f13672d802a9194214aa1332e5c9fd814ba87ce56c7fad06f9575a41c9e0255e` (26) |
| `Toy.Unify.substVar` | 5 cited | none | `2f6b6764b3d7128af72e6197ac6561ce28a23444e4fa3f791caad92c73c1d181` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.unifyNoOC_eqUpTo_fails_with_duplicate_elimination` | 6 result; 8 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `d85994c51ac4357dab9b184f9b8258c1ddebe5e5c1a253ae2a34d69bda2b7aa0` | `946e127c4d3429187c86b81333528e571a52bd36ad7b25ecd27e39c16c4b8378` (76) |
| `Toy.Unify.unifyNoOC_returns_nonunifier_var_box` | 6 result; 6 non-vacuity | `Quot.sound`, `propext` | `a705349126be2cef5ce2845586ac5886a3e75a1a42e4f68c2cfd1450382c8d18` | `4de08df94e8da6e7b2986416db6491c1ccdfe5eca9cfc8843d00ddc90d9f1494` (63) |
| `Toy.Unify.box` | 6 cited | none | `5b9b97a85a3b2c098972838117f5b54bd71e0044788fe5af8e83e83248f9ca11` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.dupS` | 6 cited | none | `01928932a9655d7f693b9700c81d1e1e27e9496d62212a5a7cb0fefbfbc7518d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.dupT` | 6 cited | none | `01928932a9655d7f693b9700c81d1e1e27e9496d62212a5a7cb0fefbfbc7518d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.dupσ` | 6 cited; 8 cited | none | `4763b44a1cef4e7de30b9ddf0ef6679e1285b3d50803d71dae518c7d1fac587d` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.eqUpTo` | 6 cited | `propext` | `3044e39ec0822a291b605e2c2635de21896238d800c4b43cd5b1992c0e0c7a57` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.eqUpToList` | 6 cited | `propext` | `e167152ff281bf8d28a6f624b3264495cee37cf5eb0cab9f94e8e9515168ed30` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.eqUpTo_arity_ne_example` | 6 cited | `propext` | `d708f828a1fcfc39c6221241781256fcc2267d3c603ff5fee03466ff8fc68eda` | `150da001f3b88534dd1aa7dc800314af5d96fb1c7c908bdd2d084a03d7f1f5d0` (22) |
| `Toy.Unify.eqUpTo_example` | 6 cited | `propext` | `96e97fade77b4a7f39948311f51953a4f20b7450ccfa0ff6cc2f157da013ee96` | `115428332efe859e51a6fa86c399b6edb32165e49e1ca63aa7b0436314bd8a91` (23) |
| `Toy.Unify.eqUpTo_ne_example` | 6 cited | `propext` | `460d43335a30c3974325cce2c5d695be162b61f94c03d0acf1c49ef3db96fe3b` | `115428332efe859e51a6fa86c399b6edb32165e49e1ca63aa7b0436314bd8a91` (23) |
| `Toy.Unify.iterSubst` | 6 cited | none | `69db43de032055c22229221fae9653e34a848ec612d48383d540de42dd4627be` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.iterSubst_example` | 6 cited | none | `ffbf476ff955d10e02a828ba4be2e3d9ea3a5c5d7e2ab6bf1c45314d4f534312` | `39be3287e3dfbd9508e8e48040882ab14abb09da98bef82640eb4fb341658cb1` (22) |
| `Toy.Unify.iterSubst_ne_example` | 6 cited | none | `b437be5705dd69df1fb0bc5295a87b8e74b96d88d87b1bf32d4a4b95a6690b14` | `39be3287e3dfbd9508e8e48040882ab14abb09da98bef82640eb4fb341658cb1` (22) |
| `Toy.Unify.unifyNoOC` | 6 cited | `propext` | `92cb4a6bfef08ce43855282867e62410fcb444eaa2f33c095c44a8dcb66a2bec` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.unifyNoOC_clash_example` | 6 cited | `propext` | `13909271e0d99d08ede775bc9441474b94805f3a3645fbd0b27cfae4da10f72d` | `8da450a29d5b526588bdeb0e5ac33b78078e51ecf73ee0dc6b7f83e553a163e6` (61) |
| `Toy.Unify.unifyNoOC_example` | 6 cited | `propext` | `5769c4361f3f9913c5801e7b13928057cfb9640f1fdf7e53351fd152c958abd4` | `f67ba13577c9de9e068ea24bfbf220d429f5652037b64e843bbd92794e9f149d` (62) |
| `Toy.Unify.run_false_eq_ok_of_run_true_eq_ok` | 7 result | `propext` | `759e5f99c97a84eb19a691e94154bf34417bdb3ce951f3c2b76abce43fa6cd67` | `d22fc26a19c4368f12d62e2e703b9f705beb47ed7ae296ca9df1316d2cc88176` (50) |
| `Toy.Unify.unifyNoOC_eq_some_of_unify_eq_some` | 7 result | `propext` | `6b6e840051baed12e4850d86fc1b29c9f82ea12f559b830c7c8408e59a20bd91` | `d376a4c2b632fa34ad0b57ac4df9db39aff4ff26e412ceb173e98bbf4d1fbf59` (60) |
| `Toy.Unify.unifyNoOC_unifies_iff_unifiable` | 7 result | `Classical.choice`, `Quot.sound`, `propext` | `c74d2e22488bcce915de7d9873538920267ff14a867e6cc1c7c75b9f7fff6cb2` | `fbd4af672f2fa7ccb06b1a961752dd438455eed6ca60fb526bb39b8700cf6c45` (61) |
| `Toy.Unify.agreement_nonvacuous` | 7 non-vacuity | `propext` | `2e9bf98120e1c4dfca7ddd087c885cfe58997a6e39e5ca24183b971342154000` | `d341abfd7d22e37bdc36f48176d4f893361e6ac5107366594781293c61ab0ddf` (55) |
| `Toy.Unify.run_agreement_needs_run_true_ok` | 7 counterexample | `propext` | `76ee23bc9b23c229384c42030bb93fbd760d93341f9eeed048c85770c2254cc1` | `5bf50fa35fc2cf26e4fe4ad56a295bb9bd11308f10941d086e66c1f83c815882` (51) |
| `Toy.Unify.run_true_ne_ok_of_run_false_ok_example` | 7 cited | `propext` | `fb7243980a018109b5467aeb4587b2581c20b33feb393701a787aba35ecf96b5` | `9dcc77f2b89d396904872f1c9c380533cbfeecd3b6d27bc68c7ea736c06d01c5` (51) |
| `Toy.Unify.unifyNoOC_eq_some_needs_unify_output` | 7 counterexample | `propext` | `ba29d2889264e5d585670450567825fa77e88b5348295abbe7c31be76c416983` | `52273f535e91096be1ca07690606a1612b410042d1c686393366da6fafd49580` (61) |
| `Toy.Unify.unifyNoOC_unifies_iff_needs_output` | 7 counterexample | `propext` | `b4404a3a1e3af76cf76fe3d2f2ed4ec1ec10c00e2672aaf266059c80dec5c9e8` | `b29767f0d9dc2d5e8385a3cff33ee3c7aea5a4800309f71648478830f16b7a93` (62) |
| `Toy.Unify.unifyNoOC_unifies_iff_unifiable_nonvacuous` | 7 non-vacuity | `propext` | `106df75bc16c2de9de7b76f27c8f7ee95c0a714f73687f5cf550da334b961381` | `421007a67aebdddaf9cff4dd26fecf80c2ad45a703a940fb2808b8f284c22762` (63) |
| `Toy.Unify.eqUpTo_forall_iff_eq` | 8 result | `Classical.choice`, `Quot.sound`, `propext` | `b34fd6628eb953045f1cc7f83debc13c711c7c946a8562b58c742210fc81d859` | `39fc706dff58191ee6ec29eb46e6ee314e69c1ca0929f1fd874351f124988f86` (20) |
| `Toy.Unify.eqUpTo_iterSubst_mono` | 8 result | `Classical.choice`, `Quot.sound`, `propext` | `817a080d7b8ab758619691623b088d144c79d314605aa539cce6e7ce5808af72` | `4795315a07dd90a4704c0331701ff4fea3d02e4e07917e8269b2a2e2fde36997` (31) |
| `Toy.Unify.eqUpTo_subst` | 8 result | `Classical.choice`, `Quot.sound`, `propext` | `0c8f1ae1de16e2e5496317ce678675904b285ab15add38ea7f8849cfe219b520` | `8eda5b83f4b4516af0a89b0ab7dbd90060327187910e0bb228f66b4a27b02392` (28) |
| `Toy.Unify.unifyNoOC_eqUpTo_of_nodup` | 8 result | `Classical.choice`, `Quot.sound`, `propext` | `4570f4c98e3001d97619b6e47b4d3917976a23a99a160d7b7e7ac2c92b0ca2df` | `b1f0fd5cf71340cc833212dbd8ecf16f83c5e1cd3a7f000517c3b70e8d807b7d` (70) |
| `Toy.Unify.ChainInv` | 8 cited | none | `ce569da1acc47eb9ae64aabaa0983333c1000a1763729e5ddc19855cca91cc56` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.LimEq` | 8 cited | `propext` | `c6579a47faef9d1b4e27e782e8f5849aa3fb368f703c0a63643c0c90993dd66b` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.dupσDedup` | 8 cited | none | `4763b44a1cef4e7de30b9ddf0ef6679e1285b3d50803d71dae518c7d1fac587d` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.dupσ_dedup_still_fails` | 8 cited | `Classical.choice`, `Quot.sound`, `propext` | `43349f91977da98e5852ffcf8d3cfaebc647a531296a326293357db617704daf` | `9c2cc41ef9ed9fdfcb146ae373610f3ebceccee9085ffaf931c1eaffcb51a098` (38) |
| `Toy.Unify.eqUpTo_iterSubst_converge` | 8 cited | `Classical.choice`, `Quot.sound`, `propext` | `1d9f5092cd515b42a16efcfe61a15bb599b2f8b4c1790bd3969920877637745a` | `4795315a07dd90a4704c0331701ff4fea3d02e4e07917e8269b2a2e2fde36997` (31) |
| `Toy.Unify.eqUpTo_iterSubst_mono_needs_agreement` | 8 counterexample | `propext` | `7245c78accb86dbfbdee68ddcff066a657789d9c2b5e755f270f8174fba55591` | `e13fb773eae0b98838a78f3b2488bf274d058b5498ff6919f740bd767cce9e84` (33) |
| `Toy.Unify.eqUpTo_iterSubst_mono_needs_le` | 8 counterexample | `propext` | `ebae0936b2f639fc4768bfab1d5c76320bfb54451c9fd93117b422a502a48860` | `b07281cf7925eeb6dad239ebde61e18709fb195736f08955197d78c5456c58a4` (32) |
| `Toy.Unify.eqUpTo_iterSubst_mono_nonvacuous` | 8 non-vacuity | `propext` | `029ba3de82bf6baf5a47f26cb815f29544d02c3c2d947ef5ded35d8233d53ae2` | `f6ecf69cc095422ae74ae8605929a79afe1f05f6a3c8bff1d7c999dedd11f679` (34) |
| `Toy.Unify.eqUpTo_subst_needs_agreement` | 8 counterexample | `propext` | `6cd551222eef211b7b445276d19403ff81f6294a866cdcac5e450e6ca37da5f4` | `d28be73a32e8ec58b4dc9d4d4cf4a6d6990ecf8a71253d49472aac578010998c` (30) |
| `Toy.Unify.eqUpTo_subst_nonvacuous` | 8 non-vacuity | `propext` | `7c78112128faf936a3dff70960811a81e399ea1f868cae4f8e89da93ab6b7d18` | `115428332efe859e51a6fa86c399b6edb32165e49e1ca63aa7b0436314bd8a91` (23) |
| `Toy.Unify.unifyNoOC_eqUpTo_needs_output` | 8 counterexample | `propext` | `8e0543f657228e7d07bc8f9bda665f86546b1d5d0534ad182e59d3cb16af771c` | `7f80b03465d9333ac82437e799eb397c783a19fb4556fc845f4bd7bb6e30571c` (71) |
| `Toy.Unify.unifyNoOC_eqUpTo_of_nodup_nonvacuous` | 8 non-vacuity | `Quot.sound`, `propext` | `9e837e6db08cf9018760f6202b30f3679cde297fdbc2cafdd8552aef282dd220` | `c7c2592d9ee10d3bd0876110d97b4ba4a1c178c18343d0dc8431b2756bf681b6` (62) |
| `Toy.Unify.matchable_not_unifiable` | 9 result; 9 non-vacuity | `Quot.sound`, `propext` | `2bd477ec5abc8b0bb97428e50ba4f20a9520d9fd22bd870ffd31256d6cbd528b` | `f5cfd08968f1bc393a0a3e76ecd9f69d43b56a5086c632778f2c57f12db20bce` (22) |
| `Toy.Unify.unifiable_not_matchable` | 9 result | `propext` | `2e6cc6817bf0eedf842d45a4174da0134748e11564c8359bd3fbfecc49a5874a` | `e84015cb74b7962f2d9b46c48f28e829902aef0fe238c94e7109e7dfea6c3e9a` (24) |
| `Toy.Unify.Matchable` | 9 cited | none | `dc7ffdeddc88eb014ed47a72ff42f771b044922633f2d36f92bcdf74a4622c8d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.matchable_example` | 9 cited | none | `40214512fae8eb430a5a9abb760cf76fa2889b05aa26a282ec6531ac7e8363f0` | `46f1f12c0acf7f054bb1c52cc28e225c957be6280cdb61622b50ea3fac8ebee1` (21) |
| `Toy.Unify.not_matchable_example` | 9 cited | `propext` | `72cf6cee3a62341b6d33784b56f1a1b2df8c93b4400a4e337fcdf2e3415cc5c4` | `54acc72bf8d67480a662f74188bb62ecfe16b213c20cf5e0c94e4d75f1bafe69` (22) |
| `Toy.Unify.pair` | 9 cited | none | `116df927d3c6a52a75997b23f82ec32d7c80d112dad7c61bf7c3b900adededa4` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.u32` | 9 cited | none | `01928932a9655d7f693b9700c81d1e1e27e9496d62212a5a7cb0fefbfbc7518d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.u8` | 9 cited | none | `01928932a9655d7f693b9700c81d1e1e27e9496d62212a5a7cb0fefbfbc7518d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.unifiable_of_matchable_of_varsDisjoint` | 9 cited | `Classical.choice`, `Quot.sound`, `propext` | `9ea51972340a753c0cf9c8e0d53d4217101640d90f1a8f00c5d9f261a15694dd` | `667423917ef4de3639e1ca5bac18a3b56eb7be4049e84ac143978216eee03a8a` (25) |
| `Toy.Unify.matchAlg_complete` | 10 result | `Classical.choice`, `Quot.sound`, `propext` | `bacbf27bdd4b6485f21be137b559711282b0e9e7686e9fbc62ca63ffaac14d1b` | `96c4698201458154efe2b57255998593e332166b3ec23bd1626670976772f041` (44) |
| `Toy.Unify.matchAlg_sound` | 10 result | `Classical.choice`, `Quot.sound`, `propext` | `61cfd12866ad1810571c0455330c68802f0153c224fd62dfab814649ce3c31d1` | `179e433a045aa5afb1a10cba8bc8407e38a45779e257cc5ae2a38d539ea97157` (43) |
| `Toy.Unify.matchAlg` | 10 cited | `propext` | `f49ad4d6711992ff2f27c212fe74aa6b86f08b06a96b8b75ffa9c6411c2f3ed1` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.matchAlg_complete_needs_matchable` | 10 counterexample | `propext` | `d5a84f6995ba2306247170df52acbb4a553e7d15e742d3382d68d776d5cd29da` | `a9b4105e177db2b377c57948b772bd4a1ab683447ee9ac0322293de6485390d7` (46) |
| `Toy.Unify.matchAlg_example` | 10 cited | `propext` | `0579a936b8b9eef0191b9f15a119700e6c9d42940a8c5dc14d9e2effe2de5fbb` | `30533418bf1b79c48d479ecdedcffe1499ca884b07c8cf79ffef6f61271b947b` (38) |
| `Toy.Unify.matchAlg_none_example` | 10 cited | `propext` | `e006a556bf8b1ef89a8f0fed8051543e0a757227512f4ebea222cae3f66a23f6` | `abbde8f32bb5a775f09ad3c9c098679ffa55c17b2cd654ec45702f2a87788b10` (39) |
| `Toy.Unify.matchAlg_nonvacuous` | 10 non-vacuity | `propext` | `6a21dc03c047f81817617c739423a4472bf27990c142e9a1e1f830dc5c788804` | `19801e71d5849b629fd953e7600a8b2c06ffc39cc0d4a52bf7f9efce84159227` (45) |
| `Toy.Unify.matchAlg_output_not_idempotent_example` | 10 cited | `propext` | `225be3122ce38c3d57230e95ed26326dfc22754ea8dad00fc8227376fe870d70` | `bcd0bb93e76b08a7a1983d83aea1255a34af82261a14807a54130c01222ac2b8` (45) |
| `Toy.Unify.matchAlg_sound_needs_output` | 10 counterexample | `propext` | `5f873396f90cf2b3d97f19a4ce8f4eaf49017d9a74bbcc06452be1f931b8e01d` | `8b870b066d4efcfa404be57ffeb98d07accad79548b0db16d911eb328364f506` (44) |
| `Toy.Unify.matchAux` | 10 cited | `propext` | `b7bb3de7bb012daea8845c25b056527d038ec556ffc51b7cd3e98f79d8f2f102` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.matchList` | 10 cited | `propext` | `8ca33758ce9e5c7b5fe97757265c6c509881615c0163ac7d9cfb4a2f03eccf7b` | `84b4e76dd616f3a686e979d09cc19aa12d6483461d6421957650634f3fe4c789` (4) |
| `Toy.Unify.matchAlg_isSome_iff_unify_isSome_of_isGround` | 11 result | `Classical.choice`, `Quot.sound`, `propext` | `707b74dbfa4bacbd474e75e26bc33d611c85d0f222decc44c3b06f9ce489aad6` | `8ac9a5144c7989a12df345f5424f954e85c4617cbaba5d78a5730a4491a0c704` (85) |
| `Toy.Unify.matchable_iff_unifiable_of_isGround` | 11 result | `Quot.sound`, `propext` | `01a3e28f812f06b84b373f49f0356d9707cd1d4a2bacd7baac8a4dece1a82aaa` | `9f9d781c382b14c3ca3d084b1642fb17aed9b3cd0ca5e94ee76dd421fde87417` (25) |
| `Toy.Unify.IsGround` | 11 cited | none | `db8fae7c52559750d857f2dbab4b8c3bb3cec137fd2d9b3ec7c73fb312b0f6f3` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.isGround_example` | 11 cited | none | `d06f655f31c2e5bb622393e9ea0fdbbd78f0ebd3db18fe009ffeb3017157b95b` | `55752338cf9d80acf43380b478a7869be5a45a56f31a6dc058e4ab92d696597b` (20) |
| `Toy.Unify.matchAlg_isSome_iff_unify_needs_ground` | 11 counterexample | `propext` | `02bb313fd49f798bcf02ff72ee056eca22a841df5774eaff2fd680ba38115bbd` | `37c539e4b5bf1f40f2cb5c2efc9c7a50d81c39c807b7c5d5216cc12d6e411580` (86) |
| `Toy.Unify.matchable_iff_unifiable_needs_ground` | 11 counterexample | `Quot.sound`, `propext` | `4b30ca530e11c2745ae05e728ee78acc3659a3fd85d23cc4f09e13da60b6275e` | `3d4cc18fc30b1a0beb5839531732094338a49aed9751e2d17e488ab85737028c` (26) |
| `Toy.Unify.matchable_iff_unifiable_nonGround_example` | 11 cited | none | `4d4aa182c5265b2ed3068b26fab8e73d665544a6d7496ef30d4e1c408cffbe2e` | `3d4cc18fc30b1a0beb5839531732094338a49aed9751e2d17e488ab85737028c` (26) |
| `Toy.Unify.matchable_iff_unifiable_of_isGround_nonvacuous` | 11 non-vacuity | none | `c2876304aa57e750b0e3a586f27aba7bee58a49b103301d8a3fcf2d963f35f5a` | `044b2542fff5739b659994fd67c122c6b466765b8d32946703c0e27f2dfd1a08` (18) |
| `Toy.Unify.not_isGround_example` | 11 cited | none | `2080dfff21ebb872a3f821f8491de8e590bf6c2f40d39e139006fa7fcc0b52f9` | `2b0e1d79b42aa85f26c6aa46fad7c669e1632ea9ae98f53684677f7f16adfed8` (17) |
| `Toy.Unify.subst_of_isGround` | 11 cited | `propext` | `1937d6170ad4bfce27e28e9da356a495a5fba12fe4413ac5d8184e701f38a252` | `dc9101e6baa39b8c11b42a1cd9c029fff8f6a18fbb4438d323c3684d53c0c8d9` (22) |
| `Toy.Unify.headersOverlap_iff_unify_isSome` | 12 result | `Classical.choice`, `Quot.sound`, `propext` | `e74df8f216ac81393a1c880e1da8cc5f5fc7ba322346fcdb0e4641b26106e75c` | `14e8448bec283c0b02a02cd4b6eea087884868f83198e467cfa997825eab8b38` (69) |
| `Toy.Unify.not_headersOverlap_of_overlapCheckSaysDisjoint` | 12 result | `Classical.choice`, `Quot.sound`, `propext` | `ae89da1f4532fa3f3e2598bbc16fa76f23d0813bda07bebc9d3cb97ebeb39d86` | `8064cc43745d1a98007023be475aaf73b03ffede8cdae9f3cad3cc97b6ec2c04` (70) |
| `Toy.Unify.not_implsOverlapIn_of_overlapCheckSaysDisjoint` | 12 result | `Classical.choice`, `Quot.sound`, `propext` | `46d7556e1a967168ecf18632e13992a619fa4680f0f4b7d04df3608794102c5e` | `38ea866b1c90f51651ad253a3dfe7ed40aed186b89738c7171c116cd43de2aa2` (75) |
| `Toy.Unify.overlapCheckSaysDisjoint_stable` | 12 result | `Classical.choice`, `Quot.sound`, `propext` | `f6d6a40b3d763391462665b6eff2a8d76752e6be98ecce4f0017825f2de85eb2` | `0db4d948819a1a479af8be887a63f5faec0b90e4ab052b0aa413870a89c921f0` (92) |
| `Toy.Unify.E_AB` | 12 cited; 17 cited | none | `75948f4890217e99d82e9693451cab5727dc766fd6b76d1ea954ff0cdb254aec` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.FreshFor` | 12 cited | none | `b25cac00706c5f62963cd70cc63488d6741cc4299c7a1628d943694c65be87b1` | `abf8aa2f615eb3dd1515fd6e303dbb13f9ccc1161eaf96fa87a50172d6934cb5` (10) |
| `Toy.Unify.HeadersOverlap` | 12 cited | none | `8fb0b5dea1afc324cb441ad3b290359fb5e2b74250921f7df0c4406e41b70fbb` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.I_AB` | 12 cited; 13 cited; 14 cited; 16 cited; 17 cited | none | `75948f4890217e99d82e9693451cab5727dc766fd6b76d1ea954ff0cdb254aec` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.Impl` | 12 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Unify.ImplSet` | 12 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Unify.ImplsOverlapIn` | 12 cited | none | `970433e9cb661227b33a5409ca64ecd399c8523045262b57b77cc2cae8b6eb44` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.OrphanOK` | 12 cited | none | `ffa8ed0378ddf0b352c6593e0b922f7d1feef92ed34eec8ceb0ae337206d8083` | `f68b5592a290316576cf2a455bdd0c541d5c3afa27f51159d4b8ed50f2790b9d` (9) |
| `Toy.Unify.StableUnderDownstream` | 12 cited | none | `877a7c75c93683dc73538cb92c1e3b0f7e6bb30d75e60ead4b57eb10711b3570` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.VarsDisjoint` | 12 cited | none | `06ae07e50925fcb30f1b151bdd8ce2fe592423d98fa685bbfa6124fdb623b699` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.freshFor_example` | 12 cited | none | `19b42083aca53c2a8ee2d90a439a37fa65c600827f7d31182ea0eceb0d7d7e4d` | `b7fc96c7333f082d97594290305b3166dde54556051c76006b7711853d113dbb` (41) |
| `Toy.Unify.headersOverlap_example` | 12 cited | none | `6e84ee200652c630abf1f1b794797314cbb1ccc65e4e491c54955402ed057027` | `a8e3cc77b11ee7d5c26e2a9254e551af8e1ae8f67f3f98384ed2f1801dbca08b` (32) |
| `Toy.Unify.headersOverlap_iff_unify_isSome_nonvacuous` | 12 non-vacuity | `Quot.sound`, `propext` | `faad16f6a5ca1d219abfa6273e72578ed8def520ac770b5ff70808324b44be9d` | `d2d16dd8541d9e020369bbb571f350a3a4f489de3575c6ce69e8f7059479250e` (23) |
| `Toy.Unify.i1` | 12 cited; 14 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.i2` | 12 cited; 14 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.iShared1` | 12 cited; 19 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.iShared2` | 12 cited; 19 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.implements_example` | 12 cited | `propext` | `8199e78e1fb90268a3b022509fa56f926a8137d8759f17603685dcd4bf927cbb` | `bd5585e59d5b8e4ad25efca027c20eced0260287de3256b997e72e81e24aaed2` (41) |
| `Toy.Unify.not_freshFor_example` | 12 cited | none | `baede187a9fdbde6c16b627c0413b94eb0c57a1e916dbb02727e543879fd2964` | `e78561a8e9872feca6a63b67782d6ced662358f9ffb5564ff0aef312a3399f29` (35) |
| `Toy.Unify.not_headersOverlap_example` | 12 cited | `propext` | `30fc10af72db06d894827570ae18c41dea38aea6f956c085eddd677d815ab158` | `dde269f50b03d4911b99035411642c1b9b1b57089784bd2be8dcc17db7731d7e` (33) |
| `Toy.Unify.not_headersOverlap_of_overlapCheckSaysDisjoint_nonvacuous` | 12 non-vacuity | `Quot.sound`, `propext` | `99160fbfbbf6c9c1ca0f4a59b26fe22903fc09fc376a89828c7d2599d2a3c3e7` | `0c28e8597765b31add0999966da093ba0cfd95520adb6e83232630cc7615b5ee` (69) |
| `Toy.Unify.not_orphanOK_example` | 12 cited | none | `f27e57b17303a305175a40a215be13d81249465b813e01b770f617af42c9075b` | `292adc6f34c96348863119f6e4b26c602d4585ed4b9ae3cae89a3484d4aa8173` (27) |
| `Toy.Unify.not_varsDisjoint_example` | 12 cited | `Quot.sound`, `propext` | `e0793147ad160495552dcc62e4606d198e977858a226fae19db1a78894673157` | `e720f3b034343052d2d78c5214f73037287191aa7b1873803b519a3816da92bb` (19) |
| `Toy.Unify.orphanOK_example` | 12 cited | none | `7c01f03bff15ad7ce4a21751a3406d8e06b8623ac3af8eb0ff1668d50f7af9c6` | `867b4f40ea8fbf766c14da9aca353fc844f9640e65bc67e2c70175baca5a593f` (27) |
| `Toy.Unify.overlapCheckSaysDisjoint` | 12 cited | `propext` | `ae3d4d9503375a69ad5a7478c441f03e8a29b2fdd0c0d72d1a5ce7da90e53f6a` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.overlapCheckSaysDisjoint_example` | 12 cited | `propext` | `0b0cd6b0403080e2bb9336b5f82cf28f59347350e5dadca679167c051cdc1acb` | `2d1b9e134ab615e316f98ebb939f1306c04e555c3b2c38cc771dd090831233a3` (68) |
| `Toy.Unify.overlapCheckSaysDisjoint_false_example` | 12 cited | `propext` | `a953b5aafe362ce31e112f98ee9bf1faaf27c1cb2c4780e2c6c43e1569d192a2` | `1fb1ce6dd4f544bfc28920b9c5a6cd2470a94481191a752ad739137dc6cd3a6c` (68) |
| `Toy.Unify.overlapCheckSaysDisjoint_needs_verdict` | 12 counterexample | `Quot.sound`, `propext` | `a48efb2f4542e5a6c81f0bc6ea9709e9e07197443680db97ce205499d16578ed` | `54bb6f960340e46edd0c24b8a338177234e737e188eefc5056112f5d8761e314` (104) |
| `Toy.Unify.overlapCheckSaysDisjoint_stable_needs_renaming_apart` | 12 counterexample | `Quot.sound`, `propext` | `254854af7c761e510f905a186232889d8b8fd9276e819d030db2028cd9f557b2` | `74d4d0d87a1d596cf81353bc9b3cfc0f3bbea39fd26b50a57bbe918588b6ded3` (103) |
| `Toy.Unify.overlapCheck_needs_renaming_apart` | 12 counterexample | `Quot.sound`, `propext` | `bdfa52ec8ef7c0228a1953889022c7bf853185fab8b169cd766f5fcd26e854fe` | `4b48fcb748e8b55d9a4972b830dac6462dcd0535a458c87ad66c3d6f8864d1aa` (82) |
| `Toy.Unify.stableUnderDownstream_example` | 12 cited | `propext` | `ba96ae325edf2583b4de0ddcb8051ac000aab993e7958c621081a736ae3523e1` | `2487479575909ce61c13417c159aad420fc0f1c08db21192f088c764bac3a0fc` (62) |
| `Toy.Unify.varsDisjoint_example` | 12 cited | `Quot.sound`, `propext` | `2329bbb117cddd5eeaa6686b8d7dc995f1b7b6c816ad9b83c5805ef43af1de68` | `e720f3b034343052d2d78c5214f73037287191aa7b1873803b519a3816da92bb` (19) |
| `Toy.Unify.implsOverlapIn_iff_mgu_instance` | 13 result | `Classical.choice`, `Quot.sound`, `propext` | `05b0d0d1b2cf40d5513f689578b8760d36be92783293738dbe71dd8750df5b2b` | `1c5ec5492e021792da61dc58bcfa260d61479b758168ab90dd7a5e020a0c7b1e` (74) |
| `Toy.Unify.Implements` | 13 cited | none | `5a02ea05f81d6c868513110cbfeeb4d51d5e0afb216bf8681cbac4be54e8385c` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.iW1` | 13 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.iW2` | 13 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.implsOverlapIn_iff_mgu_instance_needs_bound_vars_disjoint` | 13 counterexample | `Quot.sound`, `propext` | `7d740e42eaabf652320b47439082376b78d0d6f4c756e39df6b77085d9e9b3a8` | `49fda2de5c6bc346eed7c72836263096818d21b2b0e6f297527579ea584ea558` (85) |
| `Toy.Unify.implsOverlapIn_iff_mgu_instance_nonvacuous` | 13 non-vacuity | `Quot.sound`, `propext` | `c90d0bb3df32d6f6583882d5568aeb69619322d973cde57e471f52f7c4be8214` | `f515e551f95a4d3dddf01fa38d3a2f209ecc748ece01c910f037a1aad247a682` (25) |
| `Toy.Unify.not_implements_example` | 13 cited | `propext` | `a6dca387e2e7eeb87f8384010c11a22dbc838e2189205b13e66803e176bb5b9c` | `bd5585e59d5b8e4ad25efca027c20eced0260287de3256b997e72e81e24aaed2` (41) |
| `Toy.Unify.headersOverlap_not_implsOverlapIn` | 14 result; 14 non-vacuity | `propext` | `a311d51ae4c29f6d3b487ca58913a451445b0c0e7ab9aca32e25c6541ea5965b` | `a16dfff2812b188b5f7cd8b7efcb33e0cf29e67346e607b395b4fd9b73ad885b` (85) |
| `Toy.Unify.implsOverlapIn_not_monotone` | 14 result | `propext` | `85f2b97ac43fa69cb04a36a97c5a03c6f5f0254985f6f7c9c5d51665067cfe3b` | `f625ea607f269a3847559f2bc83df91f1c857dd87adfe17f17de1e2f905d7cac` (42) |
| `Toy.Unify.implA_u8` | 14 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.implB_u32` | 14 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.implements_append_iff_of_orphanOK` | 15 result | `Quot.sound`, `propext` | `d79295decd54be4431d1f88829d9fd810ad27330b976778a4720ff61bf4dc1af` | `89a26b78927b71cc063149ae326245498ec632179ee2662af68d7b0cf739993e` (50) |
| `Toy.Unify.not_implements_append_of_orphanOK` | 15 result | `Quot.sound`, `propext` | `76205049d57bb3446a9600da44b0314db70f680404a8cfcf81a154772ed6b7bb` | `89a26b78927b71cc063149ae326245498ec632179ee2662af68d7b0cf739993e` (50) |
| `Toy.Unify.not_implements_stable_of_isGround` | 15 result | `Quot.sound`, `propext` | `32e0281e3812d749f87da8513fabf6a285904d9187dc473af71d06a25692986d` | `18928231c80466919e2ffb85efbf47c84293604514f6ee001548be2be613197c` (52) |
| `Toy.Unify.Constrained` | 15 cited | none | `a9538f1ca765003a96603aa11f95186677c5938f70b5525e777627b938ab2482` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.FreshCrate` | 15 cited | none | `c9ee32b507c2aaef3f950192a89d19ac872cafa74ef0a7673785858574d992c3` | `abf8aa2f615eb3dd1515fd6e303dbb13f9ccc1161eaf96fa87a50172d6934cb5` (10) |
| `Toy.Unify.I_unconstrained` | 15 cited | none | `75948f4890217e99d82e9693451cab5727dc766fd6b76d1ea954ff0cdb254aec` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.I_vecC` | 15 cited; 16 cited; 17 cited | none | `75948f4890217e99d82e9693451cab5727dc766fd6b76d1ea954ff0cdb254aec` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.Implements.isGround` | 15 cited | none | `530b3b8d7d96caa90bb65868a75f43ac2648be2141b468d25c1a4844c95c98a0` | `bc5bf89215836ac3c2b4d8bd0bcdb8eec3d1a68784954bac2b733a1716584dde` (34) |
| `Toy.Unify.Owners` | 15 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Unify.StableUnderDownstream.self` | 15 cited | `propext` | `a176fd11fb966d7e4958c99bb7448e494a39d816f29102a3db0e53714ccb0922` | `e908454c9323b396e967c422c6e4246b731a5431979b6c900dfdbeb4fe10075f` (39) |
| `Toy.Unify.constrained_example` | 15 cited | `Quot.sound`, `propext` | `3c4afd7ec249d0efa8116209ffe282aff9cf5394d7e31446461a575eb792fd78` | `9c8368ecec1866c0e896d6af50a528ece4bd702e91a91ccef7073366902e1b1b` (31) |
| `Toy.Unify.freshCrate_example` | 15 cited | none | `918106e3e345aa403b923b45af01a722a51a52bda2ce69194a103a0bdc7e04af` | `b46e4a9bcef2503b1ab67fc70094e2e9b57a3121ae4c1e45162bd6d57b2e51d1` (40) |
| `Toy.Unify.implements_append_iff_needs_constrained` | 15 counterexample | `Quot.sound`, `propext` | `1a15fc0cac2c32bee65d13639524860ea5d8f3a0f378fe3513dbbfd57785d1dc` | `22b4461df6a75ea94c087ce9918f430ccdd564fa41576dba76fe1753acc58c2e` (54) |
| `Toy.Unify.implements_append_iff_needs_ctors_not_owned` | 15 counterexample | `Quot.sound`, `propext` | `3f0dc35fb4bcb36b7fa6b36de73dcef9d4ba26475ecca7c22036c5feaa67ae7e` | `781334439f475f21c5834011c7a20aa18d0380390351ac648a68012e855098e3` (52) |
| `Toy.Unify.implements_append_iff_needs_fresh` | 15 counterexample | `Quot.sound`, `propext` | `0c4921641bc67409c843fddf7e70f6ec5ed61827a27973dd3423c26de58f5f36` | `9bad0e0377c75c9a6ead4c5c8e85da5ea34f3291f61c6e84aba631f88fdb536a` (54) |
| `Toy.Unify.implements_append_iff_needs_orphanOK` | 15 counterexample | `Quot.sound`, `propext` | `05aca8fbb1f4ed8d905d4cf2187860243b90f4ba72f9fdc52e75e30e770861e9` | `591b2933997ec5280a2e84fb99d13041dc45568639967d1d068276e50fcb11bd` (52) |
| `Toy.Unify.implements_append_iff_needs_trait_not_owned` | 15 counterexample | `Quot.sound`, `propext` | `c0afc2a29573d5466fa2fd213c95e89afc85fe1230f7bc25d7477b9e07095e03` | `076b0f1bc73559e90c3d2bfe9c8931ac5ec598b8c27ae08dee4c0890005a5ffc` (52) |
| `Toy.Unify.implements_append_iff_of_not_isGround` | 15 cited | none | `86d21a5ccfe8bf3515fe92c74ff8a507efe00127307be22e36edb565e5a9b5df` | `bc5bf89215836ac3c2b4d8bd0bcdb8eec3d1a68784954bac2b733a1716584dde` (34) |
| `Toy.Unify.implements_append_iff_of_orphanOK_nonvacuous` | 15 non-vacuity | `Quot.sound`, `propext` | `fd566fd5a84f3fd8b13fe858958a9b1385eb8deefb1866006e2afb11362d4a30` | `c7aca12a79fe45c099ddc32bad44b6c4af40c9fd376bdca5591382a8148cff06` (59) |
| `Toy.Unify.isLocalTy` | 15 cited | none | `b4ae74eac031042c25eba739030abae4faf9e07d7961cce9f92a07134c5e660b` | `bef1ca367796614f199125bd0eccb60dee241a3bef9140497a5ad6f83b0bb1a9` (5) |
| `Toy.Unify.isLocalTy_example` | 15 cited | none | `1f88077d74c766ee51c1409e01035b00c040fe7c19ebedb11b11e29fcd486ff3` | `5c24154d6e64b5f1e45e27e8851c4f8a1ada75624ecc5b9de3afedc1e7faf4f8` (19) |
| `Toy.Unify.isLocalTy_fundamental_example` | 15 cited | none | `eab28bb0f4f28ae21e42a20d16607d84df0334b456d334006a33dc2cff373064` | `2f64d112b62b9cb03a3a3e8a87bb74028346523521e591a27af6abd6ac9fc3f2` (20) |
| `Toy.Unify.localL` | 15 cited; 16 cited; 17 cited | none | `01928932a9655d7f693b9700c81d1e1e27e9496d62212a5a7cb0fefbfbc7518d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.not_constrained_example` | 15 cited | `Quot.sound`, `propext` | `9781263dc64d7cfc079ca382461d951c8cd21d0b4a676537e7b3cd0d578da7ba` | `c68dd0b552c511e531dc6be9f5892694cdecece2ab2e5eb77174c10b855f2607` (25) |
| `Toy.Unify.not_freshCrate_example` | 15 cited | none | `b310871c6a83734ffda27cb9676458e543b2439220c61d1014212732d1fcf53d` | `b46e4a9bcef2503b1ab67fc70094e2e9b57a3121ae4c1e45162bd6d57b2e51d1` (40) |
| `Toy.Unify.not_implements_append_needs_neg` | 15 counterexample | `Quot.sound`, `propext` | `190d8720761bf537972bb24afef0ba114cb5ec4ce9d7e209508bdaca9a3cad8d` | `591b2933997ec5280a2e84fb99d13041dc45568639967d1d068276e50fcb11bd` (52) |
| `Toy.Unify.not_implements_stable_needs_constrained` | 15 counterexample | `Quot.sound`, `propext` | `540d48b43bfa75f6b49cf32becae8cde2827564e71dd8e378bcc6d655ad6afbd` | `03a8ad6b23b251d8e85f82f8e5f45ff0da2c718d0a6ba32d10df212b21c4ba92` (55) |
| `Toy.Unify.not_implements_stable_needs_neg` | 15 counterexample | `Quot.sound`, `propext` | `3f022633d680912ce75161c873ac9639d3a3aeff09e541c6f005a181d2a41d23` | `aab2b061aba106f1a68f3a8dc9c4ed0d3f448d558930619894eb7981e05f45b5` (54) |
| `Toy.Unify.not_implements_stable_of_isGround_nonvacuous` | 15 non-vacuity | `Quot.sound`, `propext` | `6ba98d0d62739244fb1d42935088ae1cc589ad963d8fe9b96f2bfb8919d5376f` | `881fbaa4e98c7e7a8d08bae9f3de2bb89a4438ec5ec835a0b917f0a56db1b940` (42) |
| `Toy.Unify.not_implements_stable_of_not_isGround` | 15 cited | none | `96afb0bb0b52d068437812e291571316cab1fb8513e0082531eb6763d2acf844` | `7a42f7dc3a25f926d9125125e511e62e25a1436e42545a927a273d29b44fffd2` (51) |
| `Toy.Unify.not_isLocalTy_example` | 15 cited | none | `7c567b7ec273510d7041924fa755b3c09750c27f432655fd3c15a22f762bb6d1` | `69797d757c6ac60dfddfae77bff6254b3f8a66b3c06c9781f546c31d579371c5` (20) |
| `Toy.Unify.not_isLocalTy_var_example` | 15 cited | none | `1ee2be5414748ec4289b0f144ee892bbdd860ffb119a414b181923bfdc564867` | `dc93a609e7a5323d4b4cb51d9227dddffbe70058da83055e3c1472ad54b6e63c` (18) |
| `Toy.Unify.orphanOK_uncovered_param_overlap_example` | 15 cited; 16 cited | `Quot.sound`, `propext` | `2d96ce685b6fcbbc661c6008c2ea0e015bf14e0031b665e20aced280754a80db` | `53805fe4443d5642883a68c96ddc2d4f4ff30777ba54e4230cb6cd5e138253df` (56) |
| `Toy.Unify.ownersB` | 15 cited; 16 cited | none | `48a50e979502fa07fba1c6c8fcf84a122bbb212984a33002f1919a3b0133f5af` | `e1592f25df8dd4167ecf578b129fd447ba505b453ed2c986e2aa0bd23360fa31` (2) |
| `Toy.Unify.ownersC` | 15 cited | none | `48a50e979502fa07fba1c6c8fcf84a122bbb212984a33002f1919a3b0133f5af` | `e1592f25df8dd4167ecf578b129fd447ba505b453ed2c986e2aa0bd23360fa31` (2) |
| `Toy.Unify.ownersEx` | 15 cited; 16 cited; 17 cited | none | `48a50e979502fa07fba1c6c8fcf84a122bbb212984a33002f1919a3b0133f5af` | `e1592f25df8dd4167ecf578b129fd447ba505b453ed2c986e2aa0bd23360fa31` (2) |
| `Toy.Unify.exists_orphanOK_overlapping_impl_iff_fundSpineVar` | 16 result; 17 cited | `Classical.choice`, `Quot.sound`, `propext` | `52ee9cd7bba2c716aa4cac90254bd6e8773abbe6a4bd3c5ef2ddf2f0cacbbadc` | `a8b02c2acf2ef305da92ec1d0657b49111ab82e76ab6140b5cccfb303fca296c` (43) |
| `Toy.Unify.noInstanceImplements_stable_of_not_fundSpineVar` | 16 result; 17 cited | `Quot.sound`, `propext` | `16d6e7a17fe0103a8080b16612859f377de9d0b18c1c25649a85770b5fbdfc06` | `8b98241d951f53d58d166be4d36978806111473b052deb2cecd174792973948a` (55) |
| `Toy.Unify.noInstanceImplements_vec_not_stable` | 16 cited; 17 result | `Classical.choice`, `Quot.sound`, `propext` | `243e9a7b3f1f7aede1d765cb7b61b6d82024621a7fc9906f669062622ddcdcb1` | `b09b1c2b2b1fba9a2159703c5e2d7ac8d6cffd12cf5088cb6af93c8d754ed44f` (60) |
| `Toy.Unify.CommonGroundInstance` | 16 cited | none | `06ae07e50925fcb30f1b151bdd8ce2fe592423d98fa685bbfa6124fdb623b699` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.E_C` | 16 cited; 17 cited | none | `75948f4890217e99d82e9693451cab5727dc766fd6b76d1ea954ff0cdb254aec` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.NoInstanceImplements` | 16 cited | none | `e4df3d46494cca25bce38d3d28955593421e320da3d65310ea391c228bac75b5` | `a78fcb5dc96365915855231211e7ea6b86f868314c2fc50ae78d8fc47ef57c74` (8) |
| `Toy.Unify.commonGroundInstance_example` | 16 cited | none | `a8951f6bcaa0a7913bf2ee8bda5b417be3e9790ec71c15eb6780e3182353bc5d` | `a414fe1e2bf7dcb1e31d8a3e5e210fd5100ac78bced14ac7cdbcb1933e94dd37` (26) |
| `Toy.Unify.eDownBox2` | 16 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.exists_orphanOK_iff_needs_ctors_not_owned` | 16 counterexample | none | `c446d9537481bef5082e008cafd40931c2ec0702dd166e47c738c36d1eae88c1` | `9b917c7b63346f0500f1e79441d948de89cd1a2e1530aafb0a80766e98ffb334` (45) |
| `Toy.Unify.exists_orphanOK_iff_needs_local_ctor` | 16 counterexample | `Quot.sound`, `propext` | `fe2edb8779a863e001ef725f435d8f8b176e667b545470c2601ae95a1e62c955` | `15aeea2c5556bb5515ead3214a2b0ae1e91c3ea5bbf2c4d6c45a6881803e42d1` (44) |
| `Toy.Unify.exists_orphanOK_iff_needs_trait_not_owned` | 16 counterexample | none | `f8fe4b2cb65244ed63dacabeebf8fab56bf14e6659fc513d960829154b38929d` | `8a1e2dda35e078a7bf6a267acf2cf7b9a316d8be13b5ad41a569a8b6254ed5ab` (45) |
| `Toy.Unify.exists_orphanOK_overlapping_impl_iff_fundSpineVar_nonvacuous` | 16 non-vacuity | none | `68db64994207fa0b03995187a4583b0e6fda48f95b1e4c06bf925c96b363aacc` | `05378386f7b066c5f9bc200f949fcb95378298cbd15833e3075c3a395edf6074` (22) |
| `Toy.Unify.fundSpineVar` | 16 cited | none | `febdd5b8dd57838d0e340bc57b4aea5bb661886c16f512eae77e545ee314174c` | `bef1ca367796614f199125bd0eccb60dee241a3bef9140497a5ad6f83b0bb1a9` (5) |
| `Toy.Unify.fundSpineVar_congr` | 16 cited | `propext` | `e5f0fe10ba7b4adbc06ec239b9449b1eb9d290cbdc5adaffdd8b96d416f0cfd1` | `55a3c1af99f9cd9647d3d2e2c2fc350fe28a34c85d1c66aaeddb6850492f761c` (16) |
| `Toy.Unify.fundSpineVar_example` | 16 cited | none | `a563f9a65dc9c69ec19a40ff9b4d1167608335ca0aa095b59b0f3aa6a732848e` | `e3764e18a778b05c0bb2d1a5cc9fdd560b6586b32a4c714b8e8ea405346fffd5` (18) |
| `Toy.Unify.iUpBox2` | 16 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.noInstanceImplements_example` | 16 cited | `propext` | `b5fc322527fb7c8d4eb4b13da9adbe358d695cb97b6e9d8a9a614ff03cf1bf1d` | `699a330badfd3adce3fd05fab4dc66b8ad37d99a73c659e134c4d2178badc80d` (42) |
| `Toy.Unify.noInstanceImplements_stable_needs_no_matching_impl` | 16 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `a70a56d25ea549c1c5f58a31e9370385fb4430c6ba5f56718f80a1197a1e5ec1` | `f8c6440716945f1677876edd8930fb45918efed7b26f85abb9e289f220e012ae` (58) |
| `Toy.Unify.noInstanceImplements_stable_needs_not_fundSpineVar` | 16 counterexample | `propext` | `0f1f4d5640e8d8a7dc4e9d1d1a238e01740c0d60ccccacf9425d9b47ea7249c0` | `38152c32b5e40017b86a64e90320306b250bca47d96e09d3e9d46fb3271da43b` (57) |
| `Toy.Unify.noInstanceImplements_stable_of_not_fundSpineVar_nonvacuous` | 16 non-vacuity | `propext` | `ed62dfce0e37109bae243919058ff0871aee85e86af8ef367a7645a69231ab29` | `2fe66be0491d30a376ce4ec38858cee45d40012dd7bdacf19276f71d5bf0ab16` (45) |
| `Toy.Unify.noInstanceImplements_vec_not_stable_of_vec_fundamental` | 16 counterexample | `propext` | `6f11e3616aabe4fbb9df78523928757d7a8fc525d444e8620c82c154c4627560` | `5c7c8a12fee2f02d8e6f3bade0ee9059f99ad0d8c1d9ea1014a0b1ec5d529f06` (58) |
| `Toy.Unify.noInstanceImplements_vec_stable_example` | 16 non-vacuity; 17 cited | `Quot.sound`, `propext` | `a25ef8cc96c84a2aa04f4bca7d7de7d0f497595d7bafcc89e4aaabcdabc3b028` | `332c44f2c260178870366312f94aa11a24dafb7170764898c75fd3cba7143218` (61) |
| `Toy.Unify.not_commonGroundInstance_example` | 16 cited | `propext` | `286fa9cbcf64962e6797accef4bc0a75d63eb35d32a638f680df74e45bd86c73` | `6461430cffac441cc50acdd31526781272b77743e36020102050a21b08d90170` (25) |
| `Toy.Unify.not_fundSpineVar_example` | 16 cited | none | `8929b698c813d18b4b6dbb7a37b09b9a9eeadce6f1954dc52bc19cb8c5221fb4` | `971f0bbb81fafc6536522ca0f5985981856799a115b4bfcbaccc78793f0f023a` (18) |
| `Toy.Unify.not_noInstanceImplements_example` | 16 cited | `propext` | `1f0e8aff876001b6f94c0d81a77a0bc711b7c64aa8eadea8c2e2e28e43437bce` | `699a330badfd3adce3fd05fab4dc66b8ad37d99a73c659e134c4d2178badc80d` (42) |
| `Toy.Unify.ownersAllFund` | 16 cited | none | `48a50e979502fa07fba1c6c8fcf84a122bbb212984a33002f1919a3b0133f5af` | `e1592f25df8dd4167ecf578b129fd447ba505b453ed2c986e2aa0bd23360fa31` (2) |
| `Toy.Unify.whereClause_disjointness_not_stable` | 17 result; 17 non-vacuity | `propext` | `d7814acd6b6140647c9f3284db7c48321cb3a7d1b197ec9b1533b8a516175748` | `2134c3251fba23195edf794970f5ea19b216d612fdc00ea9ce7aa038177ac012` (62) |
| `Toy.Unify.vec` | 17 cited | none | `5b9b97a85a3b2c098972838117f5b54bd71e0044788fe5af8e83e83248f9ca11` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.noOC_check_reports_false_overlap` | 18 result; 18 non-vacuity | `Quot.sound`, `propext` | `f9f7f2be16defa5dc211ed36b19e4d3de44817323554c87c610a25eea21f49b8` | `bbce68831a2c63d73a60740b4d2bdd0b64e3cc5a4109f5c27cc9f1b8c9c6df93` (76) |
| `Toy.Unify.iPairBox` | 18 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.iPairSame` | 18 cited | none | `80ffb0ba9b2c259f8511b7113a3ebfa91fb0527015fedf0c3b45c7f2d2d9f922` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.loopS` | 18 cited | none | `01928932a9655d7f693b9700c81d1e1e27e9496d62212a5a7cb0fefbfbc7518d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.loopT` | 18 cited | none | `01928932a9655d7f693b9700c81d1e1e27e9496d62212a5a7cb0fefbfbc7518d` | `9075a225ade168a0e680ad6829aab361cdbd65a6cc5aa034ee32ba4571e3be87` (3) |
| `Toy.Unify.overlapCheckSaysDisjointNoOC` | 18 cited | `propext` | `ae3d4d9503375a69ad5a7478c441f03e8a29b2fdd0c0d72d1a5ce7da90e53f6a` | `a98db4e47a6cc86f8dcc43ceb74294ad9b6d51e666bdc3d7613ef63174379b83` (7) |
| `Toy.Unify.overlapCheckSaysDisjointNoOC_example` | 18 cited | `propext` | `cf1a7f960229231c9d6e6ce68e4f376ab15905fe1257eb519b2429a2ad597ca1` | `dc5adf6e38fb8d40b75ed5697c778965463539419851b9db410e952da96d64d9` (68) |
| `Toy.Unify.overlapCheckSaysDisjointNoOC_false_example` | 18 cited | `propext` | `45d0d3aa29651b8464f3cc3a212fd5e92ec240374c4b2de6353839b0abaae312` | `c06e7e049ae1cb473e8a5f161874805d08eaa76d25215bb29f4b6df3d1647b95` (68) |
| `Toy.Unify.noOC_verdict_sound_of_unify_verdict_sound` | 19 result | `Classical.choice`, `Quot.sound`, `propext` | `90d55010e9123e7565582127b4b5d9213854d20c1348d33da1ea2bf326e5fdc2` | `d1a120e113fad4cfc53b43ef6fcc0f3783d4b399fb4abba5334b0d8f0e4a4536` (62) |
| `Toy.Unify.noOC_verdict_sound_of_unify_verdict_sound_uniform` | 19 result | `Classical.choice`, `Quot.sound`, `propext` | `d1caddc307067524e9e00249fd22f0b6dd926e3cbdf1703a2889a929ad8647f0` | `d1a120e113fad4cfc53b43ef6fcc0f3783d4b399fb4abba5334b0d8f0e4a4536` (62) |
| `Toy.Unify.not_headersOverlap_of_overlapCheckSaysDisjointNoOC` | 19 result | `Classical.choice`, `Quot.sound`, `propext` | `37eb09d85c4b9120f81b81aa7f00192f543fda0c2383491dd0c0b7ba226822e1` | `f5149776c9528aa440e3599358ebc2d23ccd4a66c0b93bed33cd19b08f9031b7` (70) |
| `Toy.Unify.noOC_check_false_disjoint_without_renaming` | 19 positive control; 19 counterexample | `Quot.sound`, `propext` | `c93c888aafb0627cfebe14d9d1010c119dee4eb5740d4eb7894a1e0e4ffdc390` | `ed7dd489294207348fe01413175ff1c8581cb91a193f2fcfc1518ea4cd13f3c4` (75) |
| `Toy.Unify.noOC_disjoint_needs_verdict` | 19 counterexample | `Quot.sound`, `propext` | `d3857191d11d94e1ed761f1121c31bc494baca5f857b3cf9db9bf8d5c2d2b719` | `85b46575386231f980494d011132a5a45356496291386d9a41d18212d3c0dc48` (72) |
| `Toy.Unify.noOC_verdict_sound_of_unify_verdict_sound_nonvacuous` | 19 non-vacuity | `propext` | `cdb6bb34d9632e682bdd221a1009a14f533616caea512d8b2592deb905b5a84a` | `aac365b4e20426de8ccebf9c70f97c8e89e3fd53d37d0efcbbd247d6a24b9033` (73) |
| `Toy.Unify.noOC_verdict_sound_of_unify_verdict_sound_uniform_nonvacuous` | 19 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `b0d56117e5ce0cd3d825a5b4771d234dbb577ceeb25810781041a4c109261f32` | `f1889bfd48f6bd276043da4d242a7c64108e1b3bcb38b8eb0a4132a286765be7` (66) |
| `Toy.Unify.noOC_verdict_transfer_needs_hP` | 19 positive control; 19 counterexample | `Quot.sound`, `propext` | `94f15fc21943753086556474510c807f06a22360d548e9d87ca4c5a9c513f466` | `deb7f823478fe2017898e3bb16f7d1fd22c49ee8bb2850c724cb773d2e06b5b8` (71) |
| `Toy.Unify.noOC_verdict_transfer_needs_hchk` | 19 positive control; 19 counterexample | `propext` | `36aac0b86342a1b72186329f12ca25334db66585cc962a15932618dd8e544b2d` | `02c68d76ed7e9cb202cc41ff8abb97fdf9cccda3d4b321a8bc2783610da2c13c` (63) |
| `Toy.Unify.noOC_verdict_transfer_needs_noOC_verdict` | 19 counterexample | `propext` | `4a854581ab8a27643861ef4c768f3f7cc894472300bcef6edcfafe991673c588` | `02c68d76ed7e9cb202cc41ff8abb97fdf9cccda3d4b321a8bc2783610da2c13c` (63) |
| `Toy.Unify.noOC_verdict_transfer_uniform_needs_hP` | 19 positive control; 19 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `07f41ad62e5a6e522958f1ebbffaeada2b9ebf2f3a69cb0b2af8e86fc93b526e` | `4de08df94e8da6e7b2986416db6491c1ccdfe5eca9cfc8843d00ddc90d9f1494` (63) |
| `Toy.Unify.noOC_verdict_transfer_uniform_needs_hchk` | 19 positive control; 19 counterexample | `propext` | `e7099309268a4c649b949780ea81203b25f228a772d91f884e43a413024fc6a2` | `d1a120e113fad4cfc53b43ef6fcc0f3783d4b399fb4abba5334b0d8f0e4a4536` (62) |
| `Toy.Unify.not_headersOverlap_of_overlapCheckSaysDisjointNoOC_nonvacuous` | 19 non-vacuity | `Quot.sound`, `propext` | `9d1fea52ead23ef16d7e00b93c014fa35f2003cbeb498a3364338905c94974ba` | `55adfb04e43134abd5471c62c562f81ef3568dc4af087f515d6bb76cd3975ed7` (69) |

### Primary sources

Every source cited under Findings, with the record that was checked (bibliographic data, consulted text, or pinned repository revision). Results that cite each source are listed after it.

- J. A. Robinson, "A Machine-Oriented Logic Based on the Resolution Principle", Journal of the ACM 12(1):23-41, 1965, doi:10.1145/321250.321253 (bibliographic data verified via the dblp record journals/jacm/Robinson65; full text not consulted). Standard attribution for syntactic unification and most general unifiers. (Cited by results 1, 2, 3, 5.)
- A. Martelli and U. Montanari, "An Efficient Unification Algorithm", ACM Transactions on Programming Languages and Systems 4(2):258-282, 1982, doi:10.1145/357162.357169 (verified via the dblp record journals/toplas/MartelliM82; full text not consulted). Standard source for unification as the transformation of a set of equations into solved form. This package formalizes the paper's naive equation-transformation rules with eager substitution (which can build exponentially large terms), not its efficient multiequation algorithm. (Cited by results 1, 2, 3, 4.)
- F. Baader and W. Snyder, "Unification Theory", Handbook of Automated Reasoning, vol. I, chapter 8, pp. 445-532, Elsevier, 2001, doi:10.1016/B978-044450813-3/50010-2 (verified via the dblp record books/el/RV01/BaaderS01; full text not consulted). Survey of syntactic unification, most general unifiers and their properties. (Cited by results 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 18, 19.)
- L. C. Paulson, "Verifying the Unification Algorithm in LCF", Science of Computer Programming 5(2):143-169, 1985, doi:10.1016/0167-6423(85)90009-7 (verified via dblp; full text not consulted). An earlier mechanized correctness proof of a unification algorithm. (Cited by result 1.)
- C. Sternagel and R. Thiemann, "First-Order Terms", Archive of Formal Proofs, February 2018 (entry page https://www.isa-afp.org/entries/First_Order_Terms.html consulted: its abstract states that it formalizes matching and a first-order unification algorithm in Isabelle/HOL). (Cited by results 1, 10.)
- J.-L. Lassez, M. J. Maher and K. Marriott, "Unification Revisited", in Foundations of Deductive Databases and Logic Programming, 1988, pp. 587-625, doi:10.1016/B978-0-934613-40-8.50019-1 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Clarifies the notions of most general and idempotent unifiers; the characterization of idempotent most general unifiers by the factor law τ = τ ∘ σ is attributed to it by secondary sources (not checked against the full text). (Cited by results 1, 2.)
- C. McBride, "First-order unification by structural recursion", Journal of Functional Programming 13(6):1061-1075, 2003, doi:10.1017/S0956796803004957 (verified via the Crossref record; its abstract states that the program and its correctness proof were checked in the proof assistant Lego). A structurally recursive unification algorithm whose termination follows from the number of variables in scope. (Cited by results 1, 4.)
- R. Kumar and M. Norrish, "(Nominal) Unification by Recursive Descent with Triangular Substitutions", Interactive Theorem Proving (ITP 2010), Springer, pp. 51-66, doi:10.1007/978-3-642-14052-5_6 (bibliographic data verified via the Crossref record; full text not consulted). A mechanized unification algorithm in HOL4. (Cited by result 1.)
- R. Ribeiro and C. Camarão, "A Mechanized Textbook Proof of a Type Unification Algorithm", Formal Methods: Foundations and Applications (SBMF 2015), Springer, 2016, pp. 127-141, doi:10.1007/978-3-319-29473-5_8 (bibliographic data verified via the Crossref record; full text not consulted). A mechanized unification proof in Coq. (Cited by result 1.)
- G. Huet, "Resolution d'equations dans des langages d'ordre 1, 2, ..., omega", these de doctorat d'Etat, Universite Paris VII, defended 28 September 1976 (author-hosted scan at http://gallium.inria.fr/~huet/PUBLIC/Huet1976.pdf consulted: its introduction states that Chapter 5 treats first-order languages, proves existence of a principal unifier via rational congruences, and extends the existence of a principal solution to solutions among finite or infinite terms, such a solution being rational, i.e. recognizable by a finite automaton). (Cited by results 6, 8.)
- A. Colmerauer, "Prolog and Infinite Trees", in K. L. Clark and S.-A. Tärnlund (eds.), Logic Programming, Academic Press, 1982, pp. 231-251 (bibliographic data taken from secondary indexes, the Computer History Museum Prolog bibliography and a reference list on EuDML; not verified at the publisher; full text not consulted). Solving equations over rational trees. (Cited by results 6, 8.)
- J. Jaffar, "Efficient Unification over Infinite Terms", New Generation Computing 2(3):207-219, 1984, doi:10.1007/BF03037057 (verified via the dblp record journals/ngc/Jaffar84; full text not consulted). (Cited by results 6, 8.)
- D. A. Plaisted, "The occur-check problem in Prolog", New Generation Computing 2(4):309-322, 1984, doi:10.1007/BF03037324 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Analyses the consequences of omitting the occurs check in Prolog unification. (Cited by results 6, 7, 18.)
- A. Martelli and G. Rossi, "Efficient Unification with Infinite Terms in Logic Programming", in Proceedings of the International Conference on Fifth Generation Computer Systems (FGCS 1984), Tokyo, 1984, pp. 202-209 (bibliographic data from the second author's publication list; no DOI; full text not consulted). A unification algorithm over infinite (rational) terms. (Cited by results 6, 8.)
- P. Deransart, G. Ferrand and M. Téguia, "NSTO programs (not subject to occur-check)", in V. A. Saraswat and K. Ueda (eds.), Logic Programming, Proceedings of the 1991 International Symposium, MIT Press, 1991, pp. 533-547 (bibliographic data taken from a secondary source, the bibliography of arXiv:2103.01911v2; not verified at the publisher; full text not consulted). (Cited by result 7.)
- K. R. Apt and A. Pellegrini, "On the occur-check-free PROLOG programs", ACM Transactions on Programming Languages and Systems 16(3):687-726, 1994, doi:10.1145/177492.177673 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Studies when unification without the occurs check is safe, building on the notion of equation systems "not subject to occur-check" (NSTO); the relationship of that notion to results 7 and 19 is stated from secondary descriptions and was not checked against the full text. (Cited by results 7, 19.)
- B. Courcelle, "Fundamental properties of infinite trees", Theoretical Computer Science 25(2):95-169, 1983, doi:10.1016/0304-3975(83)90059-2 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). Standard reference for infinite and rational trees. (Cited by result 8.)
- M. J. Maher, "Complete axiomatizations of the algebras of finite, rational and infinite trees", Proceedings of the Third Annual Symposium on Logic in Computer Science (LICS 1988), Edinburgh, IEEE Computer Society Press, pp. 348-357, doi:10.1109/LICS.1988.5132 (bibliographic data verified via the Crossref record of the DOI; full text not consulted). (Cited by result 8.)
- rustc-dev-guide, chapter "Coherence", file src/coherence.md of https://github.com/rust-lang/rustc-dev-guide at commit 33fa6bef32eee98a8e38c9376645cf6fbcb2ca67 (consulted). It describes overlap checks on pairs of impls that unify the impl headers (its example obtains ?E = &str), the implicit negative impl check impl_intersection_has_impossible_obligation (an overlap is impossible when an obligation cannot hold, using that downstream crates cannot implement a remote trait for a remote type), and the orphan check, which guards against impls that could be added by upstream crates in a backwards-compatible way or by downstream crates. (Cited by results 12, 13, 14, 15, 17, 18, 19.)
- Rust RFC 1023, "Rebalancing coherence" (feature fundamental_attribute, start date 2015-03-27), file text/1023-rebalancing-coherence.md of https://github.com/rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (consulted). It restricts negative reasoning to obey the orphan rules ('we cannot conclude that a proposition like T0: !Trait<T1..Tn> holds unless T0: Trait<T1..Tn> meets the orphan rules'), motivated by letting parent (upstream) crates add impls without breaking children, and introduces #[fundamental]: a fundamental type is one where implementing a blanket impl over it is a breaking change; it is applied to Box so that Box behaves like & and &mut with respect to coherence. (Cited by results 12, 14, 15, 16, 17.)
- R. A. Eisenberg, D. Vytiniotis, S. Peyton Jones and S. Weirich, "Closed type families with overlapping equations", POPL 2014, pp. 671-683, doi:10.1145/2535838.2535856 (bibliographic data verified via the Crossref record; author-hosted full text consulted). Its apartness check (Definition 6) uses ordinary first-order unification; Section 6.1 shows with the pair (a, a) and ([b], b) that an occurs-check-based apartness verdict becomes unsound in the presence of non-terminating type families, Section 6.2 defines unification over infinite types (Definition 19) and conjectures, without proof, that using it restores soundness, and Section 6.3 reports that GHC uses it for the overlap check of open type families. (Cited by results 12, 18, 19.)
- J. G. Morris and M. P. Jones, "Instance chains: type class programming without overlapping instances", ICFP 2010, pp. 375-386, doi:10.1145/1863543.1863596 (bibliographic data verified via the Crossref record; full text not consulted). Type-class design in which negative information about instances is made explicit. (Cited by results 14, 17.)
- S. Peyton Jones, M. Jones and E. Meijer, "Type classes: an exploration of the design space", Haskell Workshop, 1997 (title, authors and venue verified via the publisher page of Microsoft Research; full text not consulted). Discusses overlapping instances and the design space of instance resolution. (Cited by result 14.)
- Rust RFC 2451, "Re-rebalancing coherence" (start date 2018-05-30), file text/2451-re-rebalancing-coherence.md of https://github.com/rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (consulted). It clarifies RFC 1023, allows impl<T> ForeignTrait<LocalType> for ForeignType<T>, defines covered and uncovered type parameters, and states that fundamental types cannot cover other types. (Cited by result 16.)
- rust-lang/chalk, book chapter "Coherence", file book/src/clauses/coherence.md of https://github.com/rust-lang/chalk at commit 5fc7e4564e704ec94747a66affb5ea6bde555d3e (existence of the file at that commit confirmed via the GitHub API; its content was not consulted here). Cited as a reference treatment of Rust's orphan and overlap checks, including restrictions on negative reasoning. (Cited by result 17.)

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, downloading it if needed) and `python3`. No other tool is used, and the package is never modified.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory and checks, in order: (1) `lake build` succeeds; (2) no Lean source contains `sorry`, `admit` or `native_decide` or declares an `axiom`; (3) no declaration of the `ToyUnify` library depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, computed with Lean's `collectAxioms` by a generated audit file; (4) for every name referenced by `results.json` and every name recorded in `audit/statements.json`, the recomputed statement hash, closure hash and closure size equal the recorded ones. It prints one `ok`/`FAIL` line per check and ends with `REVALIDATED` (exit status 0) or `REVALIDATION FAILED`.

**What is hashed.** For a name `n`, the statement hash is the SHA-256 of the UTF-8 text of `repr` of the type of `n` (Lean's `Expr` representation, with fully qualified names). The closure of `n` is the set of package-local constants reachable from the constants used in that type, following the types of the constants reached, the values (bodies) of the definitions reached (theorem proofs are not followed), and the constructors of inductive types; the closure hash is the SHA-256 of the lines `c : repr(type)` or, for definitions, `c : repr(type) := repr(value)`, sorted and joined with newlines. Consequently, changing a definition changes the closure hash of every recorded statement that mentions it, directly or through other definitions (for example, the bodies of `elimBinding` and `Result.toOption` enter the closure hashes of every statement that mentions `step`, `run` or `unify`); changing a proof changes no hash.

**Manual equivalents.** The build and an axiom check for individual theorems:

```sh
cd lean
lake build
printf 'import ToyUnify\n#print axioms Toy.Unify.unifyNoOC_eqUpTo_of_nodup\n#print axioms Toy.Unify.not_headersOverlap_of_overlapCheckSaysDisjointNoOC\n' | lake env lean --stdin
```

Each `#print axioms` line must report a subset of `[propext, Classical.choice, Quot.sound]`. Replace the names to check any other declaration listed under Evidence.

**Cheaper targeted checks.** To decide whether a change to the Lean sources affects a result, rerun the primary check; a hash mismatch names the affected declaration. To check the headline occurs-check claims on another algorithm, the discriminating inputs are recorded in the statements themselves: X =? Box X and (X, (X, (Y, Z))) =? (Box X, (Box Y, (Vec Y, Z))) (result 6), the pair impl<T> Tr for (T, T) / impl<U> Tr for (U, Box<U>) (result 18), and the pair (T, (T, T)) / (U, ((U, U), (U, U))) (`unifyNoOC_outOfFuel_example`). A passing check establishes what it checks and nothing more: the theorems hold of this toy model under the pinned toolchain; nothing about another algorithm or a production checker follows from it.
