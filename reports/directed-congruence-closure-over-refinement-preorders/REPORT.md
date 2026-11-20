# Directed congruence closure over refinement preorders: certificate checking, hash-consing of nondeterministic nodes, and oriented extraction (Lean 4 toy model)

## Summary

This package proves, in a small Lean 4 model (core Lean `v4.34.1`, no Mathlib, standard axioms only), which reasoning principles of e-graphs and congruence closure survive when rewrites are *refinements* (an asymmetric preorder: the target refines the source) rather than equalities, and which fail. Fifteen results, all kernel-checked:

- **checker-soundness** (theorem, T1): In every model whose refinement relation is reflexive and transitive, whose operators are monotone at the argument positions the profile declares `mono` and respect mutual refinement at positions declared `eqOnly`, and in which all given ground directed facts hold, every certificate accepted by the standard checker proves a true refinement (`check_sound`).
- **checker-soundness-admissible-policies** (theorem, T1): The same holds for every checker policy that permits one-sided congruence only at `mono` positions and two-sided (mutual-refinement) congruence only at positions not declared `opaqueArg` (`check_sound_of_admissible`).
- **one-sided-congruence-refutable-at-non-mono-position** (impossibility, T1): At any argument position not declared `mono`, an explicit two-valued model satisfying all four laws makes `x0 <= x1` true and `f(..., x0, ...) <= f(..., x1, ...)` false, so rewriting by refinement under that position is unsound for a checker that relies only on those laws (`monoCong_refuted_at_nonMono`).
- **two-sided-congruence-refutable-at-opaque-position** (impossibility, T1): At any position declared `opaqueArg`, an explicit three-point model that is a preorder but not antisymmetric satisfies all four laws and makes `x0`, `x1` refine each other while `f(..., x0, ...) <= f(..., x1, ...)` fails (`eqCong_refuted_at_opaque`).
- **checker-policy-soundness-characterization** (characterization, T1): Consequently, for a fixed profile, a checker policy is sound for all models satisfying the four laws exactly when it is admissible in the above sense (`policySound_iff_admissibleFor`).
- **committed-choice-operators-in-outcome-semantics** (counterexample, T1): In the set-of-outcomes model, committing to the least outcome is not monotone and committing to the first-listed outcome does not even respect mutual refinement; the permissive checker accepts both unsound steps and the standard checker rejects them (`pickMin_monoCong_counterexample`, `pickFirst_eqCong_counterexample`).
- **hash-consing-nondeterministic-node-false-refinement** (counterexample, T1): Hash-consing `frz x + frz x` (the inlining of `let a := frz x; a + a`) merges the two freeze nodes, and reading the merged node back as the duplicated tree asserts a false refinement when `x` is poison (`dup_vs_let_hashcons_counterexample`).
- **hash-consing-sound-under-unique-instance-tags** (theorem, T1): If every freeze occurrence of a program carries a distinct instance tag, the hash-consed node table of its inlined form has exactly the program's intended (independent-choice) outcomes, in every environment (`hashcons_inline_sound_of_uniqueTags`).
- **hash-consing-faithful-to-per-tag-choice** (theorem, T1): For let-free terms in which freeze occurrences with equal tags have syntactically identical arguments, the hash-consed table has exactly the outcomes of one choice per tag (`hcSem_iff_tagSem_of_letFree_wellTagged`).
- **per-tag-choice-equals-independent-choice-under-unique-tags** (theorem, T1): For terms whose freeze occurrences carry pairwise distinct tags, one choice per tag gives exactly the independent-choice outcomes (`tagSem_iff_indep_of_uniqueTags`).
- **oriented-extraction-sound** (theorem, T1): In a transitive model monotone at `mono` positions, if every chosen e-node refines its class denotation and every argument position of every chosen e-node is declared `mono`, every term the extractor returns refines its class denotation (`extract_refines_of_chosenOriented_mono`).
- **oriented-extraction-sound-egraph-form** (theorem, T1): The same holds when every e-node of every class refines the class denotation and the choice stays inside the classes (`extract_refines_of_oriented_mono`).
- **unoriented-extraction-counterexample** (counterexample, T1): Relating each e-node to its class in either direction, as a symmetric e-class over directed facts does, is not enough: an extracted term can fail to refine its class denotation (`extract_unoriented_counterexample`).
- **well-founded-extraction-terminates-and-is-sound** (theorem, T1): Under the oriented-extraction hypotheses, if the choice is well-founded below a class, extraction from it terminates for some fuel and its result refines the class denotation; well-foundedness of the choice is exactly the termination condition (`extract_total_and_sound_of_wfBelow_oriented_mono`, `extract_isSome_iff_wfBelow`).
- **cyclic-extraction-counterexample** (counterexample, T1): An oriented cyclic class whose chosen e-node follows the cycle yields no term at any fuel, and no finite term solves the cycle equation (`extract_cycle_counterexample`).

All results are about the toy definitions below, not about any production e-graph, compiler or IR; every result's non-claims are listed first under **Boundaries**, and connections to real systems are labelled `derived (modeling bridge)`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity: toy model.** All definitions are small, purpose-built Lean definitions under the namespace `Toy.DirCC` (hash-consing part: `Toy.DirCC.Dup`). They are meant to capture:

- *Directed congruence reasoning* as done by a proof-producing e-graph or rewriting engine over a refinement order (as in compiler IRs with undefined behaviour and poison, where a rewrite is valid when the target refines the source). Terms are first-order over an arbitrary operator type; a model is a carrier with an arbitrary binary relation `le` (`M.le x y` reads "`y` refines `x`") and a list-indexed interpretation of every operator; model laws are separate hypotheses. Each argument position carries one of three modalities (`mono`, `eqOnly`, `opaqueArg`) declared by a profile. Certificates are unshared finite trees with five rules, checked by a total Boolean function.
- *A set-of-outcomes semantics of nondeterminism* (`oModel`): finite outcome lists ordered by reverse inclusion, with binary demonic choice, independent addition, and two committed-choice operators.
- *Freeze and hash-consing* in a separate expression language with poison values and an instance-tagged nondeterministic `frz`, modelled on the LLVM `freeze` instruction (for poison and defined inputs), with `let`, inlining, a hash-consing node table, and three semantics (independent choice, one choice per tag, one choice per table node).
- *Extraction from a directed e-graph*: classes of e-nodes, a class denotation `den`, partial choices of one e-node per class, and fuel-bounded unfolding of a choice into a term.

**Known gaps** (each also stated as a non-claim under Boundaries): there is no congruence-closure or equality-saturation *algorithm* (no union-find, rebuilding, e-matching or rule instantiation), only certificate checking over ground facts and extraction from a given e-graph; operators are functions of argument values, so syntax-inspecting operators are not modelled; contravariant positions are not modelled; the freeze language shares no definitions with the term/model/e-graph development, so freeze inside an e-graph is not modelled; extraction produces unshared trees and costs are not modelled; outcome sets are finite lists of natural numbers, and no LLVM, Cranelift or egg semantics is formalized.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only: no Mathlib, no Lake dependencies (`lakefile.toml` declares one library `ToyDirCC` and no `[[require]]`). Every declaration of the library depends at most on the axioms `propext`, `Classical.choice`, `Quot.sound`.

**Subjects.** The Lean toolchain is the subject that was executed (it kernel-checks every proof). The papers and the refinement e-graph post listed in `REPORT.json` are primary sources for the concepts the toy definitions are meant to capture (rewriting logic and frozen positions, freeze, equality saturation and e-graphs, refinement checking, congruence closure); they were consulted, not formalized, and the package does not claim to restate any of their theorems exactly. Further sources are listed under Evidence.

## Findings

Basis for every theorem below: `execution (Lean kernel check)` of the named declaration under the toolchain above, with the axioms recorded under Evidence. Any sentence relating a result to a real system is a separate claim labelled `derived (modeling bridge)`, with its reasoning.

**Design question informed by every result:** E-graphs and equality saturation assume rewrites are equalities; with undefined behaviour and poison, compiler rewrites are refinements (an asymmetric preorder, target refines source), and some operators (freeze, nondeterministic choice, committed choice) cannot be freely duplicated, merged, or rewritten under. Which congruence-closure, certificate-checking and extraction principles remain sound over a refinement preorder, which need operator-specific context modalities, and which fail?

### Reading convention and definitions

Reading convention used throughout: **`M.le x y` means "`y` refines `x`"** (the relation is
oriented from source to target, as in "poison ⊑ v"). A rewrite `s ⇝ t` is justified by
`le ⟦s⟧ ⟦t⟧`. In the outcome model, `le S T` iff every outcome of `T` is an outcome of `S`.
The same source-first order is used by `OLe` and `Dup.ValLe`; the one exception is
`Dup.Refines tgt src`, which takes the **target first** ("`tgt` refines `src`").

Lean modules of library `ToyDirCC` (in `lean/`):

| Module | Content |
| :--- | :--- |
| `ToyDirCC/Basic.lean` | terms, modalities, profiles, models, `eval`, the model laws, small law examples |
| `ToyDirCC/Cert.lean` | certificates, policies, `concl`, `check`, `FactsHold`, `AdmissibleFor`; checker soundness |
| `ToyDirCC/Outcome.lean` | the set-of-outcomes model `oModel` with `choose`, `add`, `pickMin`, `pickFirst`; profile `oProfile` |
| `ToyDirCC/Necessity.lean` | generic countermodels `flipModel`, `splitModel`; refutations; positive controls; antisymmetric models; `PolicySound` and its characterization; outcome counterexamples |
| `ToyDirCC/Dup.lean` | freeze language; independent, per-tag and hash-consed semantics; inlining; hash-consing; the hash-consing results |
| `ToyDirCC/Extract.lean` | directed e-graphs, choices, extraction, orientation, well-foundedness; extraction results |
| `ToyDirCC/Tightness.lean`, `ToyDirCC/DupTightness.lean` | one counterexample per `tight` hypothesis |
| `ToyDirCC/NonVacuity.lean` | one non-vacuity theorem per main result |
| `ToyDirCC/DefinitionExamples.lean` | direct positive and negative examples of `PolicySound` |

#### Syntax, modalities, profiles, models (`Basic.lean`)

```lean
inductive Term (Op : Type) | var (x : Nat) | app (f : Op) (args : List (Term Op))
inductive Modality | mono | eqOnly | opaqueArg
abbrev Profile (Op : Type) := Op → Nat → Modality
structure Model (Op : Type) where
  C : Type
  le : C → C → Prop            -- le x y : "y refines x"
  interp : Op → List C → C
eval M ρ (.var x) = ρ x
eval M ρ (.app f args) = M.interp f (args.map (eval M ρ))     -- eval_app
```

* `Term` captures the syntax an e-graph stores; there is no arity discipline (models interpret
  every operator on every argument list). `DecidableEq (Term Op)` is defined by hand; `Term`
  and `Cert` derive no `Repr` instance (a derived `Repr` for the nested type `Term` would be
  compiled as an `opaque` constant).
* `Modality` captures what a proof may push through an argument position: `mono`
  (refinement), `eqOnly` (only mutual refinement), `opaqueArg` (no congruence rule of the
  proof system). Because `Model.interp` is a function of argument values, arguments with
  equal values give equal results at every position, `opaqueArg` included
  (`eval_hole_congr_of_eval_eq`); `opaqueArg` blocks only congruence for mutual refinement
  between distinct values.
* `Model` bundles no law; laws are separate propositions.

Model laws (unfolded; the hole position is `pre.length`):

```lean
LeRefl M  := ∀ x, M.le x x
LeTrans M := ∀ x y z, M.le x y → M.le y z → M.le x z
MonoAt P M := ∀ f pre post x y, P f pre.length = .mono → M.le x y →
                M.le (M.interp f (pre ++ x :: post)) (M.interp f (pre ++ y :: post))
KerAt P M  := ∀ f pre post x y, P f pre.length = .eqOnly → M.le x y → M.le y x →
                M.le (M.interp f (pre ++ x :: post)) (M.interp f (pre ++ y :: post))
LeAntisymm M := ∀ x y, M.le x y → M.le y x → x = y           -- Necessity.lean
```

`KerAt` is "congruence for equality" where the equality is mutual refinement (the only
equality the proof system can derive). In a reflexive antisymmetric model `KerAt` holds for
every profile (`kerAt_of_antisymm`); it has content only in non-antisymmetric preorders.

Examples:

| Definition | Positive example | Negative example |
| :--- | :--- | :--- |
| `LeRefl` | `natLeModel_refl` (`≤` on `Nat`), `oModel_refl` | `natLtModel_not_refl` (`<`) |
| `LeTrans` | `natLeModel_trans`, `oModel_trans` | `natNearModel_not_trans` ("differs by ≤ 1") |
| `MonoAt` | `oModel_monoAt` (outcome model, `oProfile`) | `oModel_not_monoAt_allMono` (`pickMin` declared `mono`) |
| `KerAt` | `oModel_kerAt` (`pickMin` declared `eqOnly`) | `oModel_not_kerAt_oProfileEq` (`pickFirst` declared `eqOnly`) |
| `LeAntisymm` | `flipModel_antisymm` | `splitModel_not_antisymm`, `oModel_not_antisymm` |
| (profiles) | `monoAt_allOpaque`, `kerAt_allOpaque`, `kerAt_allMono` (no obligations) | — |

#### Certificates and the checker (`Cert.lean`, `Necessity.lean`)

```lean
inductive Cert (Op : Type)
  | refl (t : Term Op)                                        -- t ≤ t
  | fact (i : Nat)                                            -- facts[i]
  | trans (p q : Cert Op)                                     -- a ≤ b, b ≤ c ⊢ a ≤ c
  | cong (f : Op) (pre post : List (Term Op)) (p : Cert Op)   -- s ≤ t ⊢ f(pre,s,post) ≤ f(pre,t,post)
  | congEq (f : Op) (pre post : List (Term Op)) (p q : Cert Op) -- s ≤ t, t ≤ s ⊢ same
structure Policy where cong : Modality → Bool; congEq : Modality → Bool
Policy.standard   := ⟨fun m => decide (m = .mono), fun m => decide (m ≠ .opaqueArg)⟩
Policy.permissive := ⟨fun _ => true, fun _ => true⟩
concl pol P facts : Cert Op → Option (Term Op × Term Op)     -- computed conclusion, or none
check pol P facts c s t : Bool := decide (concl pol P facts c = some (s, t))
FactsHold M ρ facts := ∀ s t, (s, t) ∈ facts → M.le (eval M ρ s) (eval M ρ t)
pol.AdmissibleFor P := (∀ f i, pol.cong (P f i) = true → P f i = .mono) ∧
                       (∀ f i, pol.congEq (P f i) = true → P f i ≠ .opaqueArg)
PolicySound Op P pol := ∀ (M : Model Op), LeRefl M → LeTrans M → MonoAt P M → KerAt P M →
  ∀ (ρ : Nat → M.C) (facts : List (Term Op × Term Op)), FactsHold M ρ facts →
  ∀ (c : Cert Op) (s t : Term Op), check pol P facts c s t = true → M.le (eval M ρ s) (eval M ρ t)
```

`concl` checks: `trans` — middle terms syntactically equal; `cong` — `pol.cong (P f pre.length)`;
`congEq` — the second premise is exactly the reverse of the first, and
`pol.congEq (P f pre.length)`. `check` is a total `Bool` function (kernel-evaluable by
`decide`). Facts are ground directed facts used verbatim (no instantiation). Certificates are
unshared trees.

Examples: `check_sound_nonvacuous` (accepted certificate using `trans`, `cong` at both
positions of `choose`, `congEq` under `pickMin`); `pickMin_monoCong_counterexample` and
`pickFirst_eqCong_counterexample` (certificates rejected by the standard checker but accepted
by `Policy.permissive`); `check_sound_needs_check` (a rejected certificate);
`factsHold_example` / `not_factsHold_example` (`FactsHold`); `policySound_standard_oProfile` / `not_policySound_permissive_oProfile` (`PolicySound`, positive and negative), and `policySound_permissive_of_empty_op` (over an operator type with no operators every policy is sound).

#### The set-of-outcomes model (`Outcome.lean`)

```lean
inductive OOp | lit (n : Nat) | choose | add | pickMin | pickFirst
OLe S T := ∀ v, v ∈ T → v ∈ S                   -- T refines S (outcome lists, reverse inclusion)
oInterp (.lit n) _   = [n]
oInterp .choose as   = as.getD 0 [] ++ as.getD 1 []                 -- demonic choice (union), binary
oInterp .add as      = sums (as.getD 0 []) (as.getD 1 [])            -- independent sums
oInterp .pickMin as  = (as.getD 0 []).min?.toList                     -- commit to least outcome
oInterp .pickFirst as = (as.getD 0 []).head?.toList                  -- commit to first-listed outcome
oModel := ⟨List Nat, OLe, oInterp⟩
oProfile .pickMin 0 = .eqOnly;  oProfile .pickFirst 0 = .opaqueArg;  otherwise .mono
```

Outcome lists are finite outcome sets (order and multiplicity are representation only), as
in outcome-list semantics of undef/poison models. `OLe` is a preorder that is not
antisymmetric (`oModel_not_antisymm`: `[0,1]` and `[1,0]`), so the three modalities differ in
this model. `choose` and `add` are monotone; `pickMin` depends only on the outcome set but is
not monotone; `pickFirst` depends on the representation and is definable only because lists
are not quotiented to sets. Missing arguments are read as `[]`, which refines every outcome
list (`oLe_nil`, `oLe_nil_example`): `[]` is the top element of the refinement order (no
behaviour), not a model of undefined behaviour.

#### Freeze, inlining and hash-consing (`Dup.lean`, namespace `Toy.DirCC.Dup`)

```lean
abbrev Val := Option Nat                                   -- none = poison
inductive Tm | var (x) | lit (n) | add (a b) | frz (k : Nat) (a) | letE (x : Nat) (e b)
FrzOut none (some _) = True; FrzOut none none = False; FrzOut (some m) w = (w = some m)
indep ρ (.var x) v = (v = ρ x)
indep ρ (.lit n) v = (v = some n)
indep ρ (.add a b) v = ∃ u w, indep ρ a u ∧ indep ρ b w ∧ v = addV u w     -- addV strict in poison
indep ρ (.frz _ a) v = ∃ u, indep ρ a u ∧ FrzOut u v                      -- fresh choice per evaluation
indep ρ (.letE x e b) v = ∃ u, indep ρ e u ∧ indep (update ρ x u) b v    -- one value shared
ValLe none _ = True;  ValLe (some a) w = (w = some a)                       -- w refines u
Refines tgt src := ∀ ρ v, indep ρ tgt v → ∃ u, indep ρ src u ∧ ValLe u v  -- TARGET FIRST
evalT σ ρ (.frz k a) = match evalT σ ρ a with | none => some (σ k) | some m => some m
tagSem ρ t v := ∃ σ : Nat → Nat, evalT σ ρ t = v                           -- one choice per tag
frzOccs t : List (Nat × Tm)                                                 -- (tag, argument) of each frz
UniqueTags t := ((frzOccs t).map Prod.fst).Nodup
WellTagged t := ∀ p ∈ frzOccs t, ∀ q ∈ frzOccs t, p.1 = q.1 → p.2 = q.2      -- syntactic equality
LetFree : Tm → Bool                                                         -- true iff t contains no letE
LetFree (.var _) = true; LetFree (.lit _) = true; LetFree (.letE _ _ _) = false
LetFree (.add a b) = LetFree a && LetFree b; LetFree (.frz _ a) = LetFree a
inline (.letE x e b) = subst x (inline e) (inline b)  (homomorphic otherwise; result let-free)
hashcons tbl t : List DNode × Nat     -- insert t, reusing a syntactically identical node (incl. frz k i)
evalTbl c ρ tbl acc                   -- evaluate nodes front to back; node i's frz choice is c i (tag ignored)
hcSem ρ t v := ∃ c, (evalTbl c ρ (hashcons [] t).1 []).getD (hashcons [] t).2 none = v
```

* `indep` is the intended semantics: every evaluation of a `frz` of poison chooses afresh;
  `letE` shares one value. Tags are ignored.
* `tagSem` is the unique-instance reading: all `frz` nodes with the same tag share a choice.
* `hcSem` is the hash-consed reading: one choice per table node (keyed by slot, not tag), and
  syntactically identical subterms (including identical `frz k a`) share one node.
* The language shares no definitions with `Term`, `Model`, `Profile`, `Cert` or `EGraph`.

Examples: `indep_dupProg_one` / `not_indep_letProg_one`;
`refines_letProg_dupProg` / `not_refines_dupProg_letProg`; `uniqueTags_examples` /
`not_uniqueTags_dupProg`; `wellTagged_dupProg` / `not_wellTagged_mixed`; `inline_letProg`;
`letFree_examples`; `hashcons_dupProg` (merges) / `hashcons_dupProgTagged` (does not merge
different tags); `not_hcSem_dupProg_one` / `hcSem_dupProgTagged_one`;
`tagSem_dupProgTagged_one` / `not_tagSem_dupProg_one`.
Limits of the discipline: `copy_rewrite_breaks_hashcons`,
`one_copy_refinement_breaks_tagged_sharing` (see the hash-consing cards).

Named programs: `letProg = let x₁ := frz₀ x₀; x₁ + x₁`; `dupProg = frz₀ x₀ + frz₀ x₀`;
`dupProgTagged = frz₀ x₀ + frz₁ x₀`; `mixedProg = frz₀ x₀ + frz₀ x₁`;
`letLitProg = let x₀ := 1; x₀`; `shadowProg = let x₀ := 1; (frz₀ x₀ + let x₀ := 2; frz₀ x₀)`;
`letProgPlus0 = let x₁ := frz₀ (x₀ + 0); x₁ + x₁`; `copyRewritten = frz₀ (x₀ + 0) + frz₀ x₀`;
`oneCopyRefined = frz₀ 1 + frz₀ x₀`; `poisonEnv = fun _ => none`.

#### Directed e-graphs and extraction (`Extract.lean`)

```lean
inductive ENode (Op) | var (x : Nat) | app (f : Op) (kids : List Nat)
structure EGraph (Op) where nodes : Nat → List (ENode Op)
abbrev Choice (Op) := Nat → Option (ENode Op)
extract ch 0 c = none
extract ch (fuel+1) c = match ch c with
  | none => none | some (.var x) => some (.var x)
  | some (.app f ks) => (allSome (ks.map (extract ch fuel))).map (.app f)
nodeVal M ρ den (.var x) = ρ x;  nodeVal M ρ den (.app f ks) = M.interp f (ks.map den)
Oriented M ρ G den       := ∀ c n, n ∈ G.nodes c → M.le (den c) (nodeVal M ρ den n)
RelatedEitherWay M ρ G den := ∀ c n, n ∈ G.nodes c → le (den c) (nodeVal ..) ∨ le (nodeVal ..) (den c)
ChoiceIn G ch            := ∀ c n, ch c = some n → n ∈ G.nodes c
ChosenOriented M ρ den ch := ∀ c n, ch c = some n → M.le (den c) (nodeVal M ρ den n)
ChosenMono P ch          := ∀ c f ks, ch c = some (.app f ks) → ∀ i < ks.length, P f i = .mono
inductive WFBelow ch : Nat → Prop
  | var : ch c = some (.var x) → WFBelow ch c
  | app : ch c = some (.app f ks) → (∀ k ∈ ks, WFBelow ch k) → WFBelow ch c
```

* `den` is the class denotation (in practice the value of the source term that created the
  class); `Oriented` says every e-node refines it. `chosenOriented_of_oriented`:
  `Oriented` and `ChoiceIn` imply `ChosenOriented`.
* `WFBelow` is accessibility of the choice graph below `c`: every reachable class has a
  choice and there is no infinite descending path. Class ids are unbounded, so "no cycle" is
  strictly weaker (`chInf_acyclic_total_not_wfBelow`: a choice at every class, every child id
  larger than its parent's, not well-founded); the two agree when finitely many classes are
  reachable. `extract_isSome_iff_wfBelow`: extraction from `c` terminates for some
  fuel iff `WFBelow ch c`.
* `extract` produces an unshared tree.

Examples: `egOriented_oriented` / `egUnoriented_not_oriented`;
`egUnoriented_relatedEitherWay` / `not_relatedEitherWay_example`;
`chChoose_in_egUnoriented` / `chChoose_not_in_egOriented`; `chLit_chosenOriented` / (the
`¬ ChosenOriented` conjunct of `extract_unoriented_counterexample`);
`chChoose_chosenMono` / `chPick_not_chosenMono`; `wfBelow_chAcyclic` / `not_wfBelow_chCycle`,
`chInf_acyclic_total_not_wfBelow`; `extract_chChoose`, `extract_chCycle_none`,
`extract_isSome_iff_wfBelow_examples`.
Named e-graphs and choices (outcome signature; `litN n` is the literal e-node `lit n` with no
children): `egUnoriented` has class 0 = `{lit 0, choose(class 1, class 2)}`, class 1 = `{lit 0}`,
class 2 = `{lit 1}` and no other nodes, with class denotations `denLit = [[0], [0], [1]]` (other
classes `[]`); `egOriented` is `egUnoriented` without the `choose` node (class 0 = `{lit 0}`,
class 1 = `{lit 0}`, class 2 = `{lit 1}`); `chChoose` picks `choose(1, 2)` in class 0, `lit 0` in
class 1 and `lit 1` in class 2; `chLit` picks `lit 0` in class 0 and otherwise agrees with
`chChoose`; `chPick` picks `pickMin(class 1)` in class 0 (`pickMin`'s argument is declared
`eqOnly` in `oProfile`) and `x₁` in class 1; `chCycle` picks `choose(0, 0)` and `chAcyclic` picks
`x₀` in class 0 of `egCycle`; all of these choose nothing at any other class.
The cyclic e-graph `egCycle` has class 0 = `{x₀, choose(class 0, class 0)}`; `choose(S, S)`
has the outcomes of `S`, so `x₀ ≤ f x₀` and `f x₀ ≤ x₀` for `f x = choose(x, x)`.

What each core definition is meant to capture: `Modality`/`Profile` — what a proof may push through each argument position; `MonoAt`/`KerAt` — the semantic facts that justify one-sided and two-sided congruence; `Cert`/`check` — a minimal certificate format for directed congruence reasoning; `PolicySound` — soundness of a checker variant for every lawful model; `oModel` — refinement of nondeterministic programs as reverse inclusion of outcome sets; `Dup.indep` — the intended semantics of freeze (fresh choice per evaluation, sharing through `let`); `Dup.tagSem` and `Dup.hcSem` — the readings induced by instance tags and by a hash-consed table; `Oriented`/`ChosenOriented` — the class invariant that makes extraction refinement-sound; `WFBelow` — termination of unfolding a choice.

### Results

#### `checker-soundness`

- **Lean:** `Toy.DirCC.check_sound`
- **Kind:** theorem
- **Tier:** T1 — Soundness of reflexivity/transitivity/congruence deduction for a directed relation with monotone operators is the soundness of ground unconditional rewriting-logic deduction; frozen positions and per-argument variance are known (rewriting logic, Rocq generalized rewriting, a refinement e-graph prototype). The three-modality profile with a two-sided (mutual-refinement) congruence rule and a Boolean checker with a mechanized soundness proof are a precise, mechanized variant.
- **Plain claim:** For every model whose relation is reflexive (LeRefl) and transitive (LeTrans), whose operators are monotone at the positions the profile P declares mono (MonoAt P) and respect mutual refinement at the positions P declares eqOnly (KerAt P), and every valuation under which all listed directed facts hold (FactsHold), every certificate that the standard Boolean checker `check Policy.standard P facts c s t` accepts proves that t refines s (M.le (eval M ρ s) (eval M ρ t)). It is the specialization of checker-soundness-admissible-policies to the standard policy.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
(in the scope of `variable {Op : Type}`) theorem check_sound [DecidableEq Op] {P : Profile Op} {M : Model Op} (hR : LeRefl M) (hT : LeTrans M) (hMono : MonoAt P M) (hKer : KerAt P M) {ρ : Nat → M.C} {facts : List (Term Op × Term Op)} (hF : FactsHold M ρ facts) {c : Cert Op} {s t : Term Op} (hc : check Policy.standard P facts c s t = true) : M.le (eval M ρ s) (eval M ρ t)
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `[DecidableEq Op]` | needed to compute the checker (term comparison) | harmless |
  | `hR : LeRefl M` | justifies refl certificates | tight: `Toy.DirCC.check_sound_needs_refl` |
  | `hT : LeTrans M` | justifies trans certificates | tight: `Toy.DirCC.check_sound_needs_trans` |
  | `hMono : MonoAt P M` | justifies one-sided congruence at mono positions (only the instances at positions the certificate uses are needed) | tight: `Toy.DirCC.check_sound_needs_monoAt` |
  | `hKer : KerAt P M` | justifies two-sided congruence at eqOnly positions | tight: `Toy.DirCC.check_sound_needs_kerAt` |
  | `hF : FactsHold M ρ facts` | justifies fact leaves | tight: `Toy.DirCC.check_sound_needs_factsHold` |
  | `hc : check Policy.standard P facts c s t = true` | the certificate must be accepted | tight: `Toy.DirCC.check_sound_needs_check` |

- **Depth:** shallow
- **Non-vacuity witness:** Outcome-list model with oProfile; facts x0<=x1, x0<=x2, x2<=x0 under x0=[0,1], x1=[1], x2=[1,0]; certificate proving choose(pickMin x0, x0) <= choose(pickMin x2, x1) using trans, one-sided congruence under choose (both positions) and two-sided congruence under pickMin. (`Toy.DirCC.check_sound_nonvacuous`)
- **Prior art** (full records under Evidence): Meseguer 1992; Bruni and Meseguer 2006; Bloom 1976; Rocq generalized rewriting; Sozeau 2009; Zucker 2026 (blog post and prototype; not peer-reviewed); Nieuwenhuis and Oliveras 2005; Nelson and Oppen 1980; Chew 1980; Selsam and de Moura 2016; Stevens and Ghidini 2025; Morrison and de Moura 2026; Mathlib gcongr.
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `checker-soundness`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). A proof-producing rewriting engine that emits directed certificates built from reflexivity, transitivity, ground facts and per-position congruence steps can be checked with these rules for any IR semantics that presents as a carrier with a reflexive, transitive refinement relation and value-determined operators satisfying `MonoAt P` and `KerAt P` for the declared profile. Reasoning: the theorem quantifies over every such model, so any concrete semantics meeting the laws is an instance. Whether a particular IR operator meets `MonoAt` or `KerAt` at a position must be established separately; nothing here establishes it for any real IR.

#### `checker-soundness-admissible-policies`

- **Lean:** `Toy.DirCC.check_sound_of_admissible`
- **Kind:** theorem
- **Tier:** T1 — The policy-parametric form of checker-soundness: a checker that permits fewer congruence steps than the standard one (at the modalities that occur in P) is sound for the same models. Folklore made precise.
- **Plain claim:** For every checker policy pol admissible for the profile P (one-sided congruence only at positions P declares mono, two-sided congruence only at positions P does not declare opaqueArg; Policy.AdmissibleFor), every model satisfying LeRefl, LeTrans, MonoAt P and KerAt P, and every valuation under which all listed facts hold, every certificate that `check pol P facts c s t` accepts proves that t refines s.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
(in the scope of `variable {Op : Type}`) theorem check_sound_of_admissible [DecidableEq Op] {pol : Policy} {P : Profile Op} {M : Model Op} (hA : pol.AdmissibleFor P) (hR : LeRefl M) (hT : LeTrans M) (hMono : MonoAt P M) (hKer : KerAt P M) {ρ : Nat → M.C} {facts : List (Term Op × Term Op)} (hF : FactsHold M ρ facts) {c : Cert Op} {s t : Term Op} (hc : check pol P facts c s t = true) : M.le (eval M ρ s) (eval M ρ t)  -- where pol.AdmissibleFor P := (∀ f i, pol.cong (P f i) = true → P f i = .mono) ∧ (∀ f i, pol.congEq (P f i) = true → P f i ≠ .opaqueArg)
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `[DecidableEq Op]` | needed to compute the checker (term comparison) | harmless |
  | `hA : pol.AdmissibleFor P` | the policy may only permit congruence steps the model laws justify | tight: `Toy.DirCC.check_sound_of_admissible_needs_admissible` |
  | `hR : LeRefl M` | justifies refl certificates | tight: `Toy.DirCC.check_sound_of_admissible_needs_refl` |
  | `hT : LeTrans M` | justifies trans certificates | tight: `Toy.DirCC.check_sound_of_admissible_needs_trans` |
  | `hMono : MonoAt P M` | justifies one-sided congruence at mono positions (only the instances at positions the certificate uses are needed) | tight: `Toy.DirCC.check_sound_of_admissible_needs_monoAt` |
  | `hKer : KerAt P M` | justifies two-sided congruence at eqOnly positions | tight: `Toy.DirCC.check_sound_of_admissible_needs_kerAt` |
  | `hF : FactsHold M ρ facts` | justifies fact leaves | tight: `Toy.DirCC.check_sound_of_admissible_needs_factsHold` |
  | `hc : check pol P facts c s t = true` | the certificate must be accepted | tight: `Toy.DirCC.check_sound_of_admissible_needs_check` |

- **Depth:** shallow
- **Non-vacuity witness:** As for checker-soundness, with pol = Policy.standard, which is admissible for oProfile (indeed for every profile). (`Toy.DirCC.check_sound_of_admissible_nonvacuous`)
- **Prior art** (full records under Evidence): Meseguer 1992; Bruni and Meseguer 2006; Bloom 1976; Rocq generalized rewriting; Sozeau 2009; Zucker 2026 (blog post and prototype; not peer-reviewed).
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `checker-soundness-admissible-policies`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). As for `checker-soundness`: a checker that permits no more congruence steps than the admissible ones inherits soundness for every IR semantics meeting the four laws for the declared profile. Reasoning: the theorem quantifies over all admissible policies and all lawful models. Which real operators satisfy the laws is not established here.

#### `one-sided-congruence-refutable-at-non-mono-position`

- **Lean:** `Toy.DirCC.monoCong_refuted_at_nonMono`
- **Kind:** impossibility
- **Tier:** T1 — That rewriting is unsound under a non-monotone context is the motivation for frozen positions in rewriting logic; this is the precise, signature-generic form with an explicit countermodel.
- **Plain claim:** For every signature with decidable equality, profile P and context f(pre, _, post) whose hole position pre.length is not declared mono, the explicit Bool model flipModel f pre.length satisfies LeRefl, LeTrans, MonoAt P and KerAt P, makes x0 <= x1 true, and makes f(pre, x0, post) <= f(pre, x1, post) false.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
(in the scope of `variable {Op : Type}`) theorem monoCong_refuted_at_nonMono [DecidableEq Op] (P : Profile Op) (f : Op) (pre post : List (Term Op)) (h : P f pre.length ≠ .mono) : LeRefl (flipModel f pre.length) ∧ LeTrans (flipModel f pre.length) ∧ MonoAt P (flipModel f pre.length) ∧ KerAt P (flipModel f pre.length) ∧ (flipModel f pre.length).le (flipVal 0) (flipVal 1) ∧ ¬ (flipModel f pre.length).le (eval (flipModel f pre.length) flipVal (.app f (pre ++ .var 0 :: post))) (eval (flipModel f pre.length) flipVal (.app f (pre ++ .var 1 :: post)))  -- flipModel f i : carrier Bool, le a b := (a = true → b = true), interp g args := if g = f then !(args.getD i false) else false; flipVal n := (n != 0)
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `[DecidableEq Op]` | the countermodel distinguishes f from other operators | harmless |
  | `h : P f pre.length ≠ .mono` | the hole position must not be declared monotone | tight: `Toy.DirCC.monoCong_refuted_needs_nonMono` |

- **Depth:** shallow
- **Non-vacuity witness:** oProfile, operator pickMin, empty context (pickMin's argument is eqOnly). (`Toy.DirCC.monoCong_refuted_nonvacuous`)
- **Positive control:** `Toy.DirCC.monoCong_sound_at_mono` — a nearby setting (the position declared `mono`) where the refuted step is sound.
- **Prior art** (full records under Evidence): Bruni and Meseguer 2006; Meseguer 1992; Lucas 1996; Rocq generalized rewriting; Sozeau 2009; Mathlib gcongr.
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `one-sided-congruence-refutable-at-non-mono-position`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). A checker for a real IR that relies only on reflexivity, transitivity, monotonicity at `mono` positions and mutual-refinement congruence at `eqOnly` positions cannot justify rewriting by refinement under a position that has not been verified monotone, because some model meeting all those laws refutes the step. Reasoning: the countermodel satisfies every law such a checker may use. It does not show that any particular IR operator is non-monotone (the committed-choice counterexamples give concrete toy operators that are not).

#### `two-sided-congruence-refutable-at-opaque-position`

- **Lean:** `Toy.DirCC.eqCong_refuted_at_opaque`
- **Kind:** impossibility
- **Tier:** T1 — Rewriting under an undeclared (non-morphism) position fails in generalized rewriting; this is the precise statement for mutual refinement, with an explicit three-point countermodel.
- **Plain claim:** For every signature with decidable equality, profile P and context f(pre, _, post) whose hole position is declared opaqueArg, the explicit three-point model splitModel f pre.length satisfies LeRefl, LeTrans, MonoAt P and KerAt P, makes both x0 <= x1 and x1 <= x0 true, and makes f(pre, x0, post) <= f(pre, x1, post) false.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
(in the scope of `variable {Op : Type}`) theorem eqCong_refuted_at_opaque [DecidableEq Op] (P : Profile Op) (f : Op) (pre post : List (Term Op)) (h : P f pre.length = .opaqueArg) : LeRefl (splitModel f pre.length) ∧ LeTrans (splitModel f pre.length) ∧ MonoAt P (splitModel f pre.length) ∧ KerAt P (splitModel f pre.length) ∧ (splitModel f pre.length).le (splitVal 0) (splitVal 1) ∧ (splitModel f pre.length).le (splitVal 1) (splitVal 0) ∧ ¬ (splitModel f pre.length).le (eval (splitModel f pre.length) splitVal (.app f (pre ++ .var 0 :: post))) (eval (splitModel f pre.length) splitVal (.app f (pre ++ .var 1 :: post)))  -- splitModel f i : carrier Tri = {a, a', b}, le relates a and a' to each other and to themselves and b only to itself; interp g args := if g = f then (if args.getD i .a = .a' then .b else .a) else .a; splitVal n := if n = 0 then .a else .a'
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `[DecidableEq Op]` | the countermodel distinguishes f from other operators | harmless |
  | `h : P f pre.length = .opaqueArg` | the hole position must be declared opaque (for eqOnly, KerAt fails in the named model; for mono, MonoAt fails) | tight: `Toy.DirCC.eqCong_refuted_needs_opaque` |

- **Depth:** shallow
- **Non-vacuity witness:** oProfile, operator pickFirst, empty context (pickFirst's argument is opaqueArg). (`Toy.DirCC.eqCong_refuted_nonvacuous`)
- **Positive control:** `Toy.DirCC.eqCong_sound_at_nonOpaque` — a nearby setting (the position not declared `opaqueArg`) where the refuted step is sound.
- **Prior art** (full records under Evidence): Rocq generalized rewriting; Sozeau 2009; Bruni and Meseguer 2006; Zucker 2026 (blog post and prototype; not peer-reviewed).
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `two-sided-congruence-refutable-at-opaque-position`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). In a refinement preorder that is not antisymmetric (two programs refine each other without being identical, as outcome lists that differ only in order do), mutual refinement does not justify rewriting under a position whose operator may observe that difference. Reasoning: the three-point countermodel satisfies all four laws. Where refinement is a partial order the obstacle disappears (`eqCong_sound_of_antisymm`); the known escape hatches are listed under Boundaries.

#### `checker-policy-soundness-characterization`

- **Lean:** `Toy.DirCC.policySound_iff_admissibleFor`
- **Kind:** characterization
- **Tier:** T1 — Combines the soundness theorem with the two refutations into an exact boundary; folklore made precise.
- **Plain claim:** For every signature with decidable equality and profile P, a checker policy (which congruence rule is allowed at which modality) is sound for all models satisfying LeRefl, LeTrans, MonoAt P and KerAt P exactly when it allows one-sided congruence only at positions P declares mono and two-sided congruence only at positions P does not declare opaqueArg.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
(in the scope of `variable {Op : Type}`) theorem policySound_iff_admissibleFor [DecidableEq Op] (P : Profile Op) (pol : Policy) : PolicySound Op P pol ↔ pol.AdmissibleFor P  -- where PolicySound Op P pol := ∀ (M : Model Op), LeRefl M → LeTrans M → MonoAt P M → KerAt P M → ∀ (ρ : Nat → M.C) (facts : List (Term Op × Term Op)), FactsHold M ρ facts → ∀ (c : Cert Op) (s t : Term Op), check pol P facts c s t = true → M.le (eval M ρ s) (eval M ρ t); and pol.AdmissibleFor P := (∀ f i, pol.cong (P f i) = true → P f i = .mono) ∧ (∀ f i, pol.congEq (P f i) = true → P f i ≠ .opaqueArg)
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `[DecidableEq Op]` | needed to compute the checker and build countermodels | harmless |

- **Depth:** shallow
- **Non-vacuity witness:** For oProfile the standard policy is admissible and the permissive policy is not (Toy.DirCC.policySound_nonvacuous); stated directly on PolicySound, the standard policy is sound for oProfile (Toy.DirCC.policySound_standard_oProfile) and the permissive policy is not (Toy.DirCC.not_policySound_permissive_oProfile). Over an operator type with no operators every policy, the permissive one included, is sound (Toy.DirCC.policySound_permissive_of_empty_op). (`Toy.DirCC.policySound_nonvacuous`, `Toy.DirCC.policySound_standard_oProfile`, `Toy.DirCC.not_policySound_permissive_oProfile`, `Toy.DirCC.policySound_permissive_of_empty_op`)
- **Prior art** (full records under Evidence): Meseguer 1992; Bruni and Meseguer 2006; Rocq generalized rewriting; Sozeau 2009.
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `checker-policy-soundness-characterization`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). A checker designer choosing which congruence rules to allow at which operator position can read admissibility as necessary and sufficient relative to the four laws: any additional allowance is refuted by some lawful model. Reasoning: this combines checker soundness with the two refutations. Necessity is relative to quantifying over all lawful models; a checker specialized to one fixed semantics may soundly allow more.

#### `committed-choice-operators-in-outcome-semantics`

- **Lean:** `Toy.DirCC.pickMin_monoCong_counterexample`, `Toy.DirCC.pickFirst_eqCong_counterexample`
- **Kind:** counterexample
- **Tier:** T1 — Concrete instances of the refutations in a set-of-outcomes model.
- **Plain claim:** In the set-of-outcomes model (outcome lists ordered by reverse inclusion: t refines s iff every outcome of t is one of s), which satisfies all four laws for oProfile: committing to the least outcome (pickMin, declared eqOnly) is not monotone — [1] refines [0,1] but pickMin [1] = [1] does not refine pickMin [0,1] = [0] — and committing to the first-listed outcome (pickFirst, declared opaqueArg) does not respect mutual refinement — [0,1] and [1,0] refine each other but [1] does not refine [0]; the permissive checker accepts both steps and the standard checker rejects both.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
theorem pickMin_monoCong_counterexample : LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧ FactsHold oModel oVal [(.var 0, .var 1)] ∧ check Policy.permissive oProfile [(.var 0, .var 1)] (.cong .pickMin [] [] (.fact 0)) (.app .pickMin [.var 0]) (.app .pickMin [.var 1]) = true ∧ check Policy.standard oProfile [(.var 0, .var 1)] (.cong .pickMin [] [] (.fact 0)) (.app .pickMin [.var 0]) (.app .pickMin [.var 1]) = false ∧ ¬ oModel.le (eval oModel oVal (.app .pickMin [.var 0])) (eval oModel oVal (.app .pickMin [.var 1]))
theorem pickFirst_eqCong_counterexample : LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧ FactsHold oModel oVal [(.var 0, .var 2), (.var 2, .var 0)] ∧ check Policy.permissive oProfile [(.var 0, .var 2), (.var 2, .var 0)] (.congEq .pickFirst [] [] (.fact 0) (.fact 1)) (.app .pickFirst [.var 0]) (.app .pickFirst [.var 2]) = true ∧ check Policy.standard oProfile [(.var 0, .var 2), (.var 2, .var 0)] (.congEq .pickFirst [] [] (.fact 0) (.fact 1)) (.app .pickFirst [.var 0]) (.app .pickFirst [.var 2]) = false ∧ ¬ oModel.le (eval oModel oVal (.app .pickFirst [.var 0])) (eval oModel oVal (.app .pickFirst [.var 2]))  -- oVal n := [[0, 1], [1], [1, 0]].getD n []; Policy.permissive allows both rules at every modality
```

- **Hypothesis ledger:** none (a closed statement about concrete instances).
- **Depth:** shallow
- **Non-vacuity witness:** The two counterexample theorems are closed statements about concrete instances. (`Toy.DirCC.pickMin_monoCong_counterexample`, `Toy.DirCC.pickFirst_eqCong_counterexample`)
- **Prior art** (full records under Evidence): Lopes et al. 2015 (Alive); Lopes et al. 2021 (Alive2); Lee et al. 2017.
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `committed-choice-operators-in-outcome-semantics`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). Operators that commit to one outcome of a nondeterministic argument behave like the toy `pickMin` and `pickFirst`: refining the argument (removing outcomes) can change the committed outcome, so rewriting under them by refinement is unsound. Reasoning: in the set-of-outcomes reading of refinement used by Alive and Alive2 (target behaviours included in source behaviours), these operators are concrete instances. Any analogy to a specific LLVM operation, `freeze` included, is informal; LLVM semantics is not modelled by this card.

#### `hash-consing-nondeterministic-node-false-refinement`

- **Lean:** `Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample`
- **Kind:** counterexample
- **Tier:** T1 — LLVM's freeze semantics already forbids duplicating freeze; this mechanizes the hash-consing consequence for a toy freeze over poison.
- **Plain claim:** With x poison, `let a := frz x; a + a` inlines to `frz x + frz x`; hash-consing that term merges the two identical frz nodes into one table node, and the table cannot produce the outcome 1 while `frz x + frz x` read as a tree (independent choices) can. So reading the merged node back as the duplicated tree asserts a false refinement: `frz x + frz x` does not refine `let a := frz x; a + a`. The converse refinement holds, so merging itself only removes nondeterminism.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
theorem dup_vs_let_hashcons_counterexample : inline letProg = dupProg ∧ hashcons [] dupProg = ([.var 0, .frz 0 0, .add 1 1], 2) ∧ indep poisonEnv dupProg (some 1) ∧ ¬ hcSem poisonEnv dupProg (some 1) ∧ ¬ indep poisonEnv letProg (some 1) ∧ ¬ Refines dupProg letProg ∧ Refines letProg dupProg  -- note: Refines tgt src takes the target first
```

- **Hypothesis ledger:** none (a closed statement about concrete instances).
- **Depth:** shallow
- **Non-vacuity witness:** The counterexample is a closed statement about letProg, dupProg and the all-poison environment. (`Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample`)
- **Prior art** (full records under Evidence): Lee et al. 2017; LLVM LangRef, freeze; Cranelift e-graph RFC; Cranelift skeleton instructions; Lopes et al. 2021 (Alive2).
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `hash-consing-nondeterministic-node-false-refinement`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). For poison and defined inputs, the toy `frz` has the semantics the LLVM Language Reference gives `freeze` (all uses of one `freeze` instruction observe the same value; different `freeze` instructions may yield different values), with `letE` playing the role of one instruction with several uses. So an IR that hash-conses two syntactically identical `freeze`-like instructions and reads the merged node back as two independent instructions asserts a false refinement. Reasoning: `Dup.indep` encodes exactly the quoted sentences; `undef`, memory and the rest of LLVM are not modelled, and no claim is made that any shipped compiler performs this identification.

#### `hash-consing-sound-under-unique-instance-tags`

- **Lean:** `Toy.DirCC.Dup.hashcons_inline_sound_of_uniqueTags`
- **Kind:** theorem
- **Tier:** T1 — Giving each nondeterministic instance a unique identity is the discipline LLVM's freeze semantics and Cranelift's non-deduplicated side-effect nodes follow; this states it as a semantics-preservation theorem for hash-consing.
- **Plain claim:** For every program t whose frz occurrences carry pairwise distinct tags (UniqueTags) and every environment, the hash-consed node table of the inlined program `inline t` has exactly the independent-choice outcomes of t.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
theorem hashcons_inline_sound_of_uniqueTags (ρ : Nat → Val) (t : Tm) (hu : UniqueTags t) (v : Val) : hcSem ρ (inline t) v ↔ indep ρ t v  -- where hcSem ρ t v := ∃ c : Nat → Nat, (evalTbl c ρ (hashcons [] t).1 []).getD (hashcons [] t).2 none = v (one choice per table node) and UniqueTags t := ((frzOccs t).map Prod.fst).Nodup
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hu : UniqueTags t` | copies produced by inlining share a tag, distinct source occurrences do not | tight: `Toy.DirCC.Dup.hashcons_inline_sound_needs_uniqueTags` |

- **Depth:** substantive
- **Non-vacuity witness:** letProg (one frz occurrence) has unique tags and inlines to frz0 x + frz0 x. (`Toy.DirCC.Dup.hashcons_inline_sound_nonvacuous`)
- **Prior art** (full records under Evidence): Lee et al. 2017; LLVM LangRef, freeze; Cranelift e-graph RFC; Cranelift skeleton instructions; Flatt et al. 2026 (preprint).
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `hash-consing-sound-under-unique-instance-tags`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). An IR that gives each `freeze`-like instruction its own instance identity, and keys hash-consing on that identity, can represent let-bound sharing as a node DAG without changing the program's outcomes, provided copies arise only by inlining and are never rewritten or refined individually. Reasoning: in the toy language the theorem shows unique tags make the hash-consed reading equal to the intended semantics, and `copy_rewrite_breaks_hashcons` and `one_copy_refinement_breaks_tagged_sharing` show that per-copy changes break it. Whether any compiler maintains such identities is not examined.

#### `hash-consing-faithful-to-per-tag-choice`

- **Lean:** `Toy.DirCC.Dup.hcSem_iff_tagSem_of_letFree_wellTagged`
- **Kind:** theorem
- **Tier:** T1 — Bridge lemma: hash-consing identifies identical nodes, which matches one choice per tag exactly when equal tags mark identical subterms.
- **Plain claim:** For every let-free term t in which frz occurrences with equal tags have identical arguments (WellTagged), the hash-consed node table of t has exactly the outcomes of t under one choice per tag.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
theorem hcSem_iff_tagSem_of_letFree_wellTagged (ρ : Nat → Val) (t : Tm) (hlf : LetFree t = true) (hwt : WellTagged t) (v : Val) : hcSem ρ t v ↔ tagSem ρ t v  -- where tagSem ρ t v := ∃ σ : Nat → Nat, evalT σ ρ t = v (one choice per tag) and WellTagged t := ∀ p ∈ frzOccs t, ∀ q ∈ frzOccs t, p.1 = q.1 → p.2 = q.2
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hlf : LetFree t = true` | hash-consing is defined on let-free terms only (letE is outside its domain) | tight: `Toy.DirCC.Dup.hcSem_iff_tagSem_needs_letFree` |
  | `hwt : WellTagged t` | equal tags must mark copies of one instance | tight: `Toy.DirCC.Dup.hcSem_iff_tagSem_needs_wellTagged` |

- **Depth:** substantive
- **Non-vacuity witness:** dupProgTagged (frz0 x + frz1 x) and dupProg (frz0 x + frz0 x) are let-free and well-tagged. (`Toy.DirCC.Dup.hcSem_iff_tagSem_nonvacuous`)
- **Prior art** (full records under Evidence): Cranelift e-graph RFC; Cranelift skeleton instructions; Lee et al. 2017.
- **Design question:** Reference point: decomposition lemma for hash-consing-sound-under-unique-instance-tags. It informs the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `hash-consing-faithful-to-per-tag-choice`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). A hash-consed table in which identical nondeterministic nodes share one choice behaves exactly like one choice per instance identity, provided equal identities only ever label identical arguments. Reasoning: this is the decomposition lemma behind `hash-consing-sound-under-unique-instance-tags`, with the same scope limits.

#### `per-tag-choice-equals-independent-choice-under-unique-tags`

- **Lean:** `Toy.DirCC.Dup.tagSem_iff_indep_of_uniqueTags`
- **Kind:** theorem
- **Tier:** T1 — Bridge lemma: without loops each syntactic occurrence is evaluated at most once, so per-occurrence and per-tag choices coincide when tags are unique.
- **Plain claim:** For every term t whose frz occurrences carry pairwise distinct tags and every environment, the outcomes under one choice per tag are exactly the independent-choice outcomes.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
theorem tagSem_iff_indep_of_uniqueTags (ρ : Nat → Val) (t : Tm) (hu : UniqueTags t) (v : Val) : tagSem ρ t v ↔ indep ρ t v
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hu : UniqueTags t` | otherwise two occurrences sharing a tag are forced to agree | tight: `Toy.DirCC.Dup.tagSem_iff_indep_needs_uniqueTags` |

- **Depth:** shallow
- **Non-vacuity witness:** dupProgTagged and letProg have unique tags. (`Toy.DirCC.Dup.tagSem_iff_indep_nonvacuous`)
- **Prior art** (full records under Evidence): Lee et al. 2017; LLVM LangRef, freeze.
- **Design question:** Reference point: decomposition lemma for hash-consing-sound-under-unique-instance-tags. It informs the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `per-tag-choice-equals-independent-choice-under-unique-tags`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). Reference point: the second half of the decomposition behind `hash-consing-sound-under-unique-instance-tags`; the modeling bridge is the one given there.

#### `oriented-extraction-sound`

- **Lean:** `Toy.DirCC.extract_refines_of_chosenOriented_mono`
- **Kind:** theorem
- **Tier:** T1 — Oriented (<= / >=) extraction appears in a refinement e-graph prototype; this states the soundness condition precisely, including the requirement that extraction descend only through monotone positions.
- **Plain claim:** If the model is transitive (LeTrans) and monotone at the positions P declares mono (MonoAt P), every chosen e-node refines its class denotation when its children are read as their class denotations (ChosenOriented), and every argument position of every chosen e-node is declared mono (ChosenMono), then every term returned by `extract ch fuel c` refines the denotation of class c.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
(in the scope of `variable {Op : Type}`) theorem extract_refines_of_chosenOriented_mono {P : Profile Op} {M : Model Op} {ρ : Nat → M.C} {den : Nat → M.C} {ch : Choice Op} (hT : LeTrans M) (hMono : MonoAt P M) (hCO : ChosenOriented M ρ den ch) (hCM : ChosenMono P ch) {fuel c : Nat} {t : Term Op} (h : extract ch fuel c = some t) : M.le (den c) (eval M ρ t)  -- where ChosenOriented M ρ den ch := ∀ c n, ch c = some n → M.le (den c) (nodeVal M ρ den n); ChosenMono P ch := ∀ c f ks, ch c = some (.app f ks) → ∀ i, i < ks.length → P f i = .mono; nodeVal M ρ den (.var x) = ρ x, nodeVal M ρ den (.app f ks) = M.interp f (ks.map den)
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hT : LeTrans M` | chains the per-position refinements | tight: `Toy.DirCC.extract_needs_trans` |
  | `hMono : MonoAt P M` | pushes child refinements through parents | tight: `Toy.DirCC.extract_needs_monoAt` |
  | `hCO : ChosenOriented M ρ den ch` | each chosen node must refine (not merely be related to) its class | tight: `Toy.DirCC.extract_unoriented_counterexample` |
  | `hCM : ChosenMono P ch` | extraction may only descend through mono positions | tight: `Toy.DirCC.extract_needs_chosenMono` |
  | `h : extract ch fuel c = some t` | names the extracted term; without it t is an arbitrary term unrelated to the choice (termination is the subject of the well-founded extraction result) | tight: `Toy.DirCC.extract_needs_extract_some` |

- **Depth:** shallow
- **Non-vacuity witness:** Outcome model, egStrict (class 0 = {choose(class 1, class 2)} with denotation [0,1,2], class 1 = {0} with [0,1], class 2 = {2} with [1,2]) and the choice of the only e-nodes; extraction at fuel 2 returns choose(0, 2) (outcomes [0,2]), which strictly refines [0,1,2]; ChosenMono is exercised at a two-argument node. (`Toy.DirCC.extract_refines_nonvacuous`)
- **Prior art** (full records under Evidence): Zucker 2026 (blog post and prototype; not peer-reviewed); Willsey et al. 2021 (egg); Cranelift aegraph; Ramos et al. 2026 (AFP).
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `oriented-extraction-sound`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). In an e-graph whose classes record only refinement-oriented facts relative to each class's source term (every chosen member refines the class denotation), an extractor that descends only through monotone positions returns a refinement of the source. Reasoning: this is the invariant such an extractor needs, and the theorem holds for every lawful model. Production e-graph engines such as egg and Cranelift merge classes symmetrically and do not maintain this invariant; the theorem states what would be needed, not that any engine has it.

#### `oriented-extraction-sound-egraph-form`

- **Lean:** `Toy.DirCC.extract_refines_of_oriented_mono`
- **Kind:** theorem
- **Tier:** T1 — E-graph form of oriented-extraction-sound, obtained through chosenOriented_of_oriented; folklore made precise.
- **Plain claim:** If the model is transitive (LeTrans) and monotone at the positions P declares mono (MonoAt P), every e-node of every class refines the class denotation when its children are read as their class denotations (Oriented), the choice picks e-nodes of their own classes (ChoiceIn), and every argument position of every chosen e-node is declared mono (ChosenMono), then every term returned by `extract ch fuel c` refines the denotation of class c.
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
(in the scope of `variable {Op : Type}`) theorem extract_refines_of_oriented_mono {P : Profile Op} {M : Model Op} {ρ : Nat → M.C} {G : EGraph Op} {den : Nat → M.C} {ch : Choice Op} (hT : LeTrans M) (hMono : MonoAt P M) (hO : Oriented M ρ G den) (hC : ChoiceIn G ch) (hCM : ChosenMono P ch) {fuel c : Nat} {t : Term Op} (h : extract ch fuel c = some t) : M.le (den c) (eval M ρ t)  -- where Oriented M ρ G den := ∀ c n, n ∈ G.nodes c → M.le (den c) (nodeVal M ρ den n) and ChoiceIn G ch := ∀ c n, ch c = some n → n ∈ G.nodes c
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hT : LeTrans M` | chains the per-position refinements | tight: `Toy.DirCC.extract_needs_trans` |
  | `hMono : MonoAt P M` | pushes child refinements through parents | tight: `Toy.DirCC.extract_needs_monoAt` |
  | `hO : Oriented M ρ G den` | every e-node must refine (not merely be related to) its class | tight: `Toy.DirCC.extract_oriented_needs_oriented` |
  | `hC : ChoiceIn G ch` | the choice must pick e-nodes of the class it unfolds | tight: `Toy.DirCC.extract_needs_choiceIn` |
  | `hCM : ChosenMono P ch` | extraction may only descend through mono positions | tight: `Toy.DirCC.extract_needs_chosenMono` |
  | `h : extract ch fuel c = some t` | names the extracted term; without it t is an arbitrary term unrelated to the choice (termination is the subject of the well-founded extraction result) | tight: `Toy.DirCC.extract_needs_extract_some` |

- **Depth:** shallow
- **Non-vacuity witness:** As for oriented-extraction-sound: egStrict is oriented and chStrict picks inside its classes. (`Toy.DirCC.extract_refines_nonvacuous`)
- **Prior art** (full records under Evidence): Zucker 2026 (blog post and prototype; not peer-reviewed); Willsey et al. 2021 (egg); Cranelift aegraph; Ramos et al. 2026 (AFP).
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `oriented-extraction-sound-egraph-form`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). As for `oriented-extraction-sound`, phrased as an invariant on all e-nodes of the e-graph (`Oriented`) plus a choice inside the classes. Reasoning: `Oriented` and `ChoiceIn` imply `ChosenOriented` (`chosenOriented_of_oriented`). No production engine is shown to maintain `Oriented`.

#### `unoriented-extraction-counterexample`

- **Lean:** `Toy.DirCC.extract_unoriented_counterexample`
- **Kind:** counterexample
- **Tier:** T1 — A symmetric e-class over directed facts permits extraction against the refinement direction; known in spirit (symmetric e-classes are unsound for refinements), made concrete.
- **Plain claim:** In the outcome model, class 0 of egUnoriented denotes [0] (the source program 0) and also contains choose(0, 1) (outcomes [0,1]), which is related to the class only in the opposite direction; every node is related to its class in some direction, the choice stays in the classes and descends only through mono positions, and the extracted choose(0, 1) does not refine [0].
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
theorem extract_unoriented_counterexample : LeTrans oModel ∧ MonoAt oProfile oModel ∧ RelatedEitherWay oModel (fun _ => []) egUnoriented denLit ∧ ChoiceIn egUnoriented chChoose ∧ ¬ ChosenOriented oModel (fun _ => []) denLit chChoose ∧ ChosenMono oProfile chChoose ∧ extract chChoose 2 0 = some (.app .choose [.app (.lit 0) [], .app (.lit 1) []]) ∧ ¬ oModel.le (denLit 0) (eval oModel (fun _ => []) (.app .choose [.app (.lit 0) [], .app (.lit 1) []]))  -- egUnoriented: class 0 = {lit 0, choose(1, 2)}, class 1 = {lit 0}, class 2 = {lit 1}; denLit = [[0], [0], [1]]; chChoose picks choose(1, 2) in class 0
```

- **Hypothesis ledger:** none (a closed statement about concrete instances).
- **Depth:** shallow
- **Non-vacuity witness:** The counterexample is a closed statement about egUnoriented and chChoose. (`Toy.DirCC.extract_unoriented_counterexample`)
- **Prior art** (full records under Evidence): Zucker 2026 (blog post and prototype; not peer-reviewed); Lopes et al. 2021 (Alive2); Ramos et al. 2026 (AFP).
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `unoriented-extraction-counterexample`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). A symmetric e-class that mixes directed facts (some members refine the source, others are refined by it) does not make extraction sound for refinement: the extractor can pick a member with more outcomes than the source, adding nondeterminism, which refinement in the sense of Alive2 forbids. Reasoning: the outcome-model instance is concrete; it locates the obstacle in the class invariant, not in any particular merge algorithm.

#### `well-founded-extraction-terminates-and-is-sound`

- **Lean:** `Toy.DirCC.extract_total_and_sound_of_wfBelow_oriented_mono`
- **Kind:** theorem
- **Tier:** T1 — Well-founded (acyclic) extraction is standard practice (the egg implementation's cost fixpoint only costs e-nodes whose children are costed; theta-node well-formedness in PEGs; extraction over topologically ordered acyclic e-class DAGs); stated here together with refinement soundness.
- **Plain claim:** Under LeTrans, MonoAt P, ChosenOriented and ChosenMono, if the choice is well-founded below class c (WFBelow: every class reachable from c by unfolding the choice has a chosen e-node, and there is no infinite descending path of unfoldings — which, when only finitely many classes are reachable, amounts to the absence of cycles), then for some fuel extraction from c returns a term, and that term refines the denotation of c. WFBelow is exactly the condition for extraction from c to terminate (extract_isSome_iff_wfBelow).
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
(in the scope of `variable {Op : Type}`) theorem extract_total_and_sound_of_wfBelow_oriented_mono {P : Profile Op} {M : Model Op} {ρ : Nat → M.C} {den : Nat → M.C} {ch : Choice Op} (hT : LeTrans M) (hMono : MonoAt P M) (hCO : ChosenOriented M ρ den ch) (hCM : ChosenMono P ch) {c : Nat} (hW : WFBelow ch c) : ∃ fuel t, extract ch fuel c = some t ∧ M.le (den c) (eval M ρ t)  -- where WFBelow ch is the inductive predicate with constructors var : ch c = some (.var x) → WFBelow ch c and app : ch c = some (.app f ks) → (∀ k, k ∈ ks → WFBelow ch k) → WFBelow ch c
```

- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hT : LeTrans M` | as for oriented extraction | tight: `Toy.DirCC.extractWF_needs_trans` |
  | `hMono : MonoAt P M` | as for oriented extraction | tight: `Toy.DirCC.extractWF_needs_monoAt` |
  | `hCO : ChosenOriented M ρ den ch` | as for oriented extraction | tight: `Toy.DirCC.extractWF_needs_chosenOriented` |
  | `hCM : ChosenMono P ch` | as for oriented extraction | tight: `Toy.DirCC.extractWF_needs_chosenMono` |
  | `hW : WFBelow ch c` | termination: unfolding the choice from c must reach only classes with a choice and have no infinite descending path (no cycle, and no infinite acyclic chain over unbounded class ids: chInf_acyclic_total_not_wfBelow) | tight: `Toy.DirCC.extractWF_needs_wfBelow` |

- **Depth:** shallow
- **Non-vacuity witness:** Two instances: egStrict with chStrict (depth two, strict refinement), and the cyclic class {x0, choose(class 0, class 0)} of egCycle with the acyclic choice x0. (`Toy.DirCC.extract_wf_nonvacuous`)
- **Prior art** (full records under Evidence): Willsey et al. 2021 (egg); egg extractor; Tate et al. 2009/2011; Arbore et al. 2026; Cranelift aegraph; Ramos et al. 2026 (AFP); Blanqui and Koprowski 2011.
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `well-founded-extraction-terminates-and-is-sound`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). Extractors that choose bottom-up (assigning a choice to a class only once all children of the chosen e-node have one, as egg's extractor does at the cited commit) produce choices that are well-founded below every class they choose for; under the orientation and `mono` hypotheses such choices give terminating, sound extraction. Reasoning: `WFBelow` is exactly termination of unfolding (`extract_isSome_iff_wfBelow`). That bottom-up cost-based choices are well-founded is an informal observation about the cited implementation and is not proved here.

#### `cyclic-extraction-counterexample`

- **Lean:** `Toy.DirCC.extract_cycle_counterexample`
- **Kind:** counterexample
- **Tier:** T1 — Cycles in e-graphs representing infinitely many terms are standard; this makes the failure of cycle-following extraction concrete in a directed setting.
- **Plain claim:** In the outcome model, the cyclic class {x0, choose(class 0, class 0)} is oriented with denotation x0 (x0 <= choose(x0, x0) and choose(x0, x0) <= x0, since choose(S, S) has the outcomes of S), and the choice choose(class 0, class 0) stays in the class and descends through mono positions; yet extraction returns none at every fuel, the choice is not well-founded, and no finite term t satisfies t = choose(t, t).
- **Lean statement** (exact source header; definitions it uses are unfolded in the trailing comment or above):

```lean
theorem extract_cycle_counterexample (ρ : Nat → List Nat) : LeTrans oModel ∧ MonoAt oProfile oModel ∧ Oriented oModel ρ egCycle (fun _ => ρ 0) ∧ ChosenOriented oModel ρ (fun _ => ρ 0) chCycle ∧ oModel.le (nodeVal oModel ρ (fun _ => ρ 0) (.app .choose [0, 0])) (ρ 0) ∧ ChoiceIn egCycle chCycle ∧ ChosenMono oProfile chCycle ∧ ¬ WFBelow chCycle 0 ∧ (∀ fuel, extract chCycle fuel 0 = none) ∧ (∀ t : Term OOp, t ≠ .app .choose [t, t])  -- egCycle: class 0 = {var 0, choose(0, 0)}; chCycle picks choose(0, 0)
```

- **Hypothesis ledger:** none (a closed statement about concrete instances).
- **Depth:** shallow
- **Non-vacuity witness:** The counterexample holds for every valuation; it is a closed statement about egCycle and chCycle. (`Toy.DirCC.extract_cycle_counterexample`)
- **Prior art** (full records under Evidence): Willsey et al. 2021 (egg); Arbore et al. 2026; Tate et al. 2009/2011.
- **Design question:** the package design question stated at the start of Findings.
- **Non-claims:** listed under Boundaries, `cyclic-extraction-counterexample`.
- Basis: execution (Lean kernel check).
- Basis: derived (modeling bridge). Cyclic classes of the kind equality saturation creates (a class containing `f(c, c)` for itself) have no finite term along the cycle, so an extractor into finite trees must avoid cyclic choices. Reasoning: the instance is concrete. IRs that give cycles a meaning (loops as cycles through theta nodes, as in program expression graphs) are outside the setting; see the escape hatch under Boundaries.

### Supporting statements

| Lean name | Status | Role |
| :--- | :--- | :--- |
| `Toy.DirCC.concl_sound_of_admissible` | proved | induction behind `check_sound_of_admissible` |
| `Toy.DirCC.Policy.standard_admissibleFor` | proved | the standard policy is admissible for every profile |
| `Toy.DirCC.monoCong_sound_at_mono`, `eqCong_sound_at_nonOpaque` | proved | positive controls (minimal hypotheses: `MonoAt`, resp. `MonoAt` and `KerAt`) |
| `Toy.DirCC.eval_hole_congr_of_eval_eq` | proved | equal argument values give equal results at every position |
| `Toy.DirCC.kerAt_of_antisymm`, `eqCong_sound_of_antisymm` | proved | in reflexive antisymmetric models `KerAt` holds for every profile and two-sided congruence is sound at every position |
| `Toy.DirCC.flipModel_antisymm`, `splitModel_not_antisymm`, `flipModel_reversed_conclusion` | proved | properties of the two generic countermodels |
| `Toy.DirCC.monoAt_of_mono_imp` | proved | `MonoAt` transfers to profiles with fewer `mono` positions |
| `Toy.DirCC.chosenOriented_of_oriented` | proved | `Oriented ∧ ChoiceIn → ChosenOriented` |
| `Toy.DirCC.extract_isSome_iff_wfBelow` | proved | extraction terminates exactly on well-founded choices |
| `Toy.DirCC.extract_fuel_mono`, `allSome_eq_some_iff` | proved | fuel monotonicity of `extract` |
| `Toy.DirCC.term_ne_app_self_self` | proved | no finite term solves `t = f(t, t)` |
| `Toy.DirCC.Dup.letFree_inline`, `evalT_inline`, `wellTagged_inline_of_uniqueTags` | proved | inlining lemmas (`wellTagged_inline_of_uniqueTags` tight: `wellTagged_inline_needs_uniqueTags`, which also shows `UniqueTags` cannot be weakened to `WellTagged`) |

All supporting statements are kernel-checked with the same axiom bound; they are not cards and their statements are not hashed.

### What the package answers

E-graphs and equality saturation assume rewrites are equalities; with undefined behaviour and
poison, compiler rewrites are refinements (an asymmetric preorder, target refines source), and
some operators cannot be freely duplicated, merged, or rewritten under. Which
congruence-closure, certificate-checking and extraction principles remain sound over a
refinement preorder, which need operator-specific context modalities, and which fail?

| Principle | Status in this package |
| :--- | :--- |
| reflexivity, transitivity, ground facts | sound (`check_sound`, `check_sound_of_admissible`); each law needed |
| congruence (rewrite under `f`) | sound exactly at positions declared and verified `mono` (`policySound_iff_admissibleFor`, `monoCong_refuted_at_nonMono`); the refutation holds in partial-order models too |
| congruence by mutual refinement | sound at `mono` and `eqOnly` positions, refutable at `opaqueArg` positions in non-antisymmetric models (`eqCong_refuted_at_opaque`); sound everywhere in reflexive antisymmetric models (`eqCong_sound_of_antisymm`) |
| committed-choice operators (least / first outcome) | not monotone / not even mutual-refinement-respecting (`pickMin_monoCong_counterexample`, `pickFirst_eqCong_counterexample`) |
| hash-consing identical nondeterministic nodes | unsound as an identification with the duplicated tree (`dup_vs_let_hashcons_counterexample`); faithful under unique instance tags (`hashcons_inline_sound_of_uniqueTags`), but per-copy rewriting or refinement of an inlined tagged freeze is unsound (`copy_rewrite_breaks_hashcons`, `one_copy_refinement_breaks_tagged_sharing`) |
| extraction | sound if each chosen node refines its class and extraction descends only through `mono` positions, each of these hypotheses being tight (`extract_refines_of_chosenOriented_mono`, `extract_refines_of_oriented_mono`; `extract_unoriented_counterexample`) |
| cyclic classes | allowed; the choice must be well-founded, which is exactly termination (`extract_total_and_sound_of_wfBelow_oriented_mono`; `extract_isSome_iff_wfBelow`; `extract_cycle_counterexample`) |

## Boundaries

### Non-claims, per result

Each item is known not to apply or was not examined, as stated in the item itself. Items beginning "Escape hatch" name a hypothesis whose removal or weakening defeats the corresponding refutation; they are collected again below.

#### `checker-soundness`

- The checker is not shown to be complete (it checks certificates; it is not a decision procedure): it is not shown to accept a certificate for every true refinement, nor for every consequence of the facts; there is no congruence-closure algorithm here, only certificate checking.
- Facts are ground (used verbatim under one valuation); rewrite-rule instantiation, e-matching and conditional rules are not modelled.
- Only three modalities exist; anti-monotone (contravariant) positions are not modelled, and nothing is claimed about them.
- Soundness is relative to the stated model laws; nothing is claimed about which operators of a real IR satisfy MonoAt or KerAt.
- Operators of a Model are functions of argument values on the carrier M.C, so at every position, opaqueArg included, arguments with equal values give equal results (Toy.DirCC.eval_hole_congr_of_eval_eq). Syntax-inspecting or optimization-sensitive operators (such as LLVM's llvm.is.constant) over carriers of semantic values are not modelled, and neither is let-shared nondeterminism (see Toy.DirCC.Dup, a separate language).
- Certificates are unshared finite trees: a sub-certificate needed twice is written twice, and Cert.congEq takes separate sub-certificates for s <= t and t <= s. For a depth-d nest g(g(...g(x)...)) of an operator g whose argument is eqOnly, the direct certificate of g^d(s) <= g^d(t) from the facts s <= t and t <= s has 2^d fact leaves. No shared (DAG) certificate format is defined, and no lower bound on certificate size is proved.
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `checker-soundness-admissible-policies`

- Admissibility constrains a policy only at modalities that occur in P; nothing is said about policies for other profiles.
- The checker is not shown to be complete (it checks certificates; it is not a decision procedure): it is not shown to accept a certificate for every true refinement, nor for every consequence of the facts; there is no congruence-closure algorithm here, only certificate checking.
- Facts are ground (used verbatim under one valuation); rewrite-rule instantiation, e-matching and conditional rules are not modelled.
- Operators of a Model are functions of argument values on the carrier M.C, so at every position, opaqueArg included, arguments with equal values give equal results (Toy.DirCC.eval_hole_congr_of_eval_eq). Syntax-inspecting or optimization-sensitive operators (such as LLVM's llvm.is.constant) over carriers of semantic values are not modelled, and neither is let-shared nondeterminism (see Toy.DirCC.Dup, a separate language).
- Certificates are unshared finite trees: a sub-certificate needed twice is written twice, and Cert.congEq takes separate sub-certificates for s <= t and t <= s. For a depth-d nest g(g(...g(x)...)) of an operator g whose argument is eqOnly, the direct certificate of g^d(s) <= g^d(t) from the facts s <= t and t <= s has 2^d fact leaves. No shared (DAG) certificate format is defined, and no lower bound on certificate size is proved.
- Only three modalities exist; anti-monotone (contravariant) positions are not modelled, and nothing is claimed about them.
- Soundness is relative to the stated model laws; nothing is claimed about which operators of a real IR satisfy MonoAt or KerAt.
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `one-sided-congruence-refutable-at-non-mono-position`

- It does not say that every rewrite under a non-mono position is false in every model; it exhibits one model (and one pair of facts) per position.
- It does not say that the operators of a real IR declared equality-only are non-monotone; the countermodel is a two-point Bool model, not a compiler semantics (see pickMin_monoCong_counterexample for an outcome-set instance).
- Positive control: at a position declared mono the one-sided step is sound in every model satisfying MonoAt P, in particular in every model satisfying the four laws (monoCong_sound_at_mono).
- Escape hatch (two-sided rewriting at eqOnly positions): when P f pre.length = .eqOnly and the premise is strengthened from x0 <= x1 to mutual refinement (x0 <= x1 and x1 <= x0), the step is sound in every model satisfying MonoAt P and KerAt P (Toy.DirCC.eqCong_sound_at_nonOpaque).
- Escape hatch (contravariance): the countermodel flipModel negates the hole argument, which is anti-monotone, and in it the reversed conclusion f(pre, x1, post) <= f(pre, x0, post) holds (Toy.DirCC.flipModel_reversed_conclusion). Anti-monotone modalities and a contravariant congruence rule are not modelled; the theorem does not rule out such a rule being sound for operators that satisfy an anti-monotonicity law.
- The countermodel is antisymmetric (Toy.DirCC.flipModel_antisymm): the refutation applies within partial-order models too.
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `two-sided-congruence-refutable-at-opaque-position`

- Escape hatch (partial-order models): the countermodel needs a relation that is not antisymmetric (splitModel_not_antisymm). In a reflexive model, two-sided congruence at an opaqueArg position can fail only if the carrier has distinct mutually refining elements: in a reflexive antisymmetric model the two-sided step is sound at every position (Toy.DirCC.eqCong_sound_of_antisymm). The theorem does not say opaque positions matter in partial-order models.
- At every position, opaqueArg included, arguments with equal values give equal results in every Model (Toy.DirCC.eval_hole_congr_of_eval_eq); what an opaqueArg position blocks is only congruence for mutual refinement between distinct values.
- Positive control: at a position not declared opaqueArg the two-sided step is sound in every model satisfying MonoAt P and KerAt P (eqCong_sound_at_nonOpaque).
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `checker-policy-soundness-characterization`

- Soundness quantifies over all models satisfying the four laws; a policy may be sound for one particular model while not admissible.
- Admissibility depends only on modalities that occur in P; a policy allowing congruence at a modality no position has is admissible.
- Only the five certificate rules of Cert are considered; richer proof systems (anti-monotone steps, conditional rewrites) are not covered.
- Escape hatch (partial-order models): the necessity of forbidding two-sided congruence at opaqueArg positions rests on a non-antisymmetric countermodel (splitModel). If PolicySound quantified only over antisymmetric models, that restriction would not be necessary: in a reflexive antisymmetric model KerAt holds for every profile (Toy.DirCC.kerAt_of_antisymm) and the two-sided step is sound at every position (Toy.DirCC.eqCong_sound_of_antisymm). The restriction of one-sided congruence to mono positions stays necessary there, because the one-sided countermodel flipModel is antisymmetric (Toy.DirCC.flipModel_antisymm). Partial orders such as sets of outcomes ordered by reverse inclusion, or a flat domain with poison below every value, are examples of antisymmetric relations; they are not defined in this package.
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `committed-choice-operators-in-outcome-semantics`

- Genuine (nondeterministic) choice operators in this model — choose (union) and add (independent sums) — are monotone; the failures are for operators that commit to one outcome by a deterministic rule.
- pickMin models a deterministic resolution of nondeterminism of the kind an implementation of freeze might perform; it is not LLVM's freeze, which is nondeterministic and is not modelled in this outcome model.
- The outcome model has no poison, UB, memory or bit widths.
- pickFirst fails two-sided congruence only because oModel represents outcome sets as lists, which are not quotiented ([0, 1] and [1, 0] refine each other but differ); over outcome sets proper, mutual refinement is equality and a representation-dependent operator such as pickFirst is not definable.
- In oModel the empty list [] refines every outcome list (Toy.DirCC.oLe_nil): it is the top element (no behaviour), not a model of undefined behaviour, which in outcome-set semantics is the set of all behaviours, refined by everything, and is not representable by a finite list. Missing operator arguments are read as [].
- Freeze is not an operator of oModel. In the separate language Toy.DirCC.Dup, after a let-shared freeze is inlined into copies that share a tag, refining the argument of one copy only can produce an outcome the shared program cannot (Toy.DirCC.Dup.one_copy_refinement_breaks_tagged_sharing).
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `hash-consing-nondeterministic-node-false-refinement`

- It does not show that hash-consing (merging) freeze nodes is wrong as a compilation step: merging removes nondeterminism, and the merged program refines the duplicated one (Refines letProg dupProg). The failure is identifying the two, i.e. reading the merged node back as the duplicated tree.
- No e-graph rebuild, e-class merging or e-matching is modelled; 'e-graph' here means a hash-consed node table.
- The language has only variables, literals, add, freeze over poison, and let; no undef, UB, memory or bit widths.
- Argument order: Dup.Refines tgt src takes the target program first ('tgt refines src'), whereas Dup.ValLe, OLe and Model.le take the source first.
- The language is a toy (variables, literals, add, freeze over poison values, let) with a set-of-outcomes semantics and a node-table hash-consing function; no result is a theorem about LLVM, Cranelift, egg, egglog, or any production e-graph or IR.

#### `hash-consing-sound-under-unique-instance-tags`

- Tags must be assigned to the source program before inlining; the theorem says nothing about programs whose tags were assigned after duplication.
- It concerns hash-consing only; e-class merging by rewrites is not modelled.
- Only freeze over poison is nondeterministic in the language; other nondeterministic or effectful operators are not covered.
- hcSem evaluates each table node once and shares its value among all uses (DAG semantics). The theorem is about that table semantics and says nothing about code generated from the table. Reading the table back as a tree duplicates shared frz nodes and is unsound even when the source has unique tags: for letProg (unique tags) the table of the inlined program is that of dupProg, and dupProg read as a tree does not refine letProg (Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample). A tree-producing extractor such as Toy.DirCC.extract (on a different, Term-based e-graph type) would do exactly that.
- evalTbl ignores the tag k of a frz node and keys choices by table slot; hashcons merges only syntactically identical nodes. Rewriting the argument of one copy of an inlined tagged freeze, even by an exact identity such as x0 + 0 to x0, makes the term not well-tagged, gives the copies separate slots, and lets the table produce an outcome the source cannot (Toy.DirCC.Dup.copy_rewrite_breaks_hashcons).
- After inlining duplicates a tagged freeze, frz k is not refinement-monotone per copy under either the per-tag reading or the table reading: refining only the first copy's poison argument of frz0 x0 + frz0 x0 to 1 gives frz0 1 + frz0 x0, which can produce 1, while letProg produces only even numbers (Toy.DirCC.Dup.one_copy_refinement_breaks_tagged_sharing). Refinement under a tagged freeze must be applied to all copies at once; soundness of the simultaneous step is not stated here.
- Toy.DirCC.Dup is a standalone expression language with no formal link to Toy.DirCC.Term, Model, Profile, Cert or EGraph.
- The counterexample for UniqueTags refutes the direction indep -> hcSem (independent outcomes are lost by merging). Whether the direction hcSem -> indep holds without UniqueTags is not stated or proved here.
- The language is a toy (variables, literals, add, freeze over poison values, let) with a set-of-outcomes semantics and a node-table hash-consing function; no result is a theorem about LLVM, Cranelift, egg, egglog, or any production e-graph or IR.

#### `hash-consing-faithful-to-per-tag-choice`

- The LetFree counterexample reflects the domain of the hash-consing function, not a semantic phenomenon.
- WellTagged requires syntactic equality of the arguments of frz occurrences that share a tag, not semantic equivalence: semantically equal but syntactically different copies (frz0 (x0 + 0) + frz0 x0) are not merged by hashcons, and the table and per-tag readings then differ (Toy.DirCC.Dup.copy_rewrite_breaks_hashcons).
- A decomposition lemma for hash-consing-sound-under-unique-instance-tags, not an end-to-end e-graph soundness theorem.
- The language is a toy (variables, literals, add, freeze over poison values, let) with a set-of-outcomes semantics and a node-table hash-consing function; no result is a theorem about LLVM, Cranelift, egg, egglog, or any production e-graph or IR.

#### `per-tag-choice-equals-independent-choice-under-unique-tags`

- Relies on the language having no loops or recursion (each occurrence evaluated at most once per run); nothing is claimed for languages with iteration.
- UniqueTags fails as soon as a let-bound freeze used more than once is inlined (inline letProg = dupProg, which repeats tag 0), and on such inlined programs the per-tag and independent readings can differ (Toy.DirCC.Dup.tagSem_iff_indep_needs_uniqueTags on dupProg).
- A decomposition lemma for hash-consing-sound-under-unique-instance-tags.
- The language is a toy (variables, literals, add, freeze over poison values, let) with a set-of-outcomes semantics and a node-table hash-consing function; no result is a theorem about LLVM, Cranelift, egg, egglog, or any production e-graph or IR.

#### `oriented-extraction-sound`

- Extraction through eqOnly positions (even when the child class is two-sided) is not covered.
- No cost model or optimality of the extracted term is considered.
- The class denotation den is an input; the theorem does not say how an e-graph establishes Oriented.
- The e-graph form (extract_refines_of_oriented_mono, card oriented-extraction-sound-egraph-form) additionally needs the choice to stay inside the classes (extract_needs_choiceIn).
- extract unfolds the choice into an unshared Term tree: a class chosen below several parents is unfolded once per use, so the tree can be exponentially larger than the choice graph, and no shared (SSA or let-bound) output is produced. Both nodeVal and eval read a class used twice as two independent evaluations; programs whose meaning depends on sharing one nondeterministic result (such as Toy.DirCC.Dup.letProg) cannot be represented in this e-graph type, and reading a hash-consed Dup table back as a tree is unsound (Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample).
- EGraph has no inter-class inequality edges and no merge or rebuild operation; Oriented requires every e-node of class c to refine the single denotation den c. Merging two classes c1, c2 after learning den c1 <= den c2 preserves Oriented in general neither with denotation den c2 (e-nodes of c1 need not refine den c2) nor with den c1 (parents that read c2 as a child would then read den c1); nothing is proved about e-graph construction or rebuilding.
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `oriented-extraction-sound-egraph-form`

- Extraction through eqOnly positions (even when the child class is two-sided) is not covered.
- No cost model or optimality of the extracted term is considered.
- The class denotation den is an input; the theorem does not say how an e-graph establishes Oriented.
- extract unfolds the choice into an unshared Term tree: a class chosen below several parents is unfolded once per use, so the tree can be exponentially larger than the choice graph, and no shared (SSA or let-bound) output is produced. Both nodeVal and eval read a class used twice as two independent evaluations; programs whose meaning depends on sharing one nondeterministic result (such as Toy.DirCC.Dup.letProg) cannot be represented in this e-graph type, and reading a hash-consed Dup table back as a tree is unsound (Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample).
- EGraph has no inter-class inequality edges and no merge or rebuild operation; Oriented requires every e-node of class c to refine the single denotation den c. Merging two classes c1, c2 after learning den c1 <= den c2 preserves Oriented in general neither with denotation den c2 (e-nodes of c1 need not refine den c2) nor with den c1 (parents that read c2 as a child would then read den c1); nothing is proved about e-graph construction or rebuilding.
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `unoriented-extraction-counterexample`

- It does not show that cost-based extractors in existing tools pick such a node; any extractor that may pick it is unsound.
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `well-founded-extraction-terminates-and-is-sound`

- No bound on the fuel is stated beyond existence.
- Cyclic e-classes are allowed; only the choice must be well-founded.
- No cost model or optimality is considered.
- WFBelow ch c is an assumed hypothesis: no cost function, greedy cost fixpoint or ILP extractor is modelled or proved to produce a well-founded choice. (Unproved informal remark, not formalized or proved here: with zero-cost operators, such as a choose of a class with itself, minimum-cost ties can follow a cycle unless ties are broken by a well-founded order.)
- A choice with no cycle need not be well-founded when class ids are unbounded (Toy.DirCC.chInf_acyclic_total_not_wfBelow); 'no cycle' suffices only when finitely many classes are reachable.
- extract unfolds the choice into an unshared Term tree: a class chosen below several parents is unfolded once per use, so the tree can be exponentially larger than the choice graph, and no shared (SSA or let-bound) output is produced. Both nodeVal and eval read a class used twice as two independent evaluations; programs whose meaning depends on sharing one nondeterministic result (such as Toy.DirCC.Dup.letProg) cannot be represented in this e-graph type, and reading a hash-consed Dup table back as a tree is unsound (Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample).
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

#### `cyclic-extraction-counterexample`

- It does not show that following a cycle yields a false refinement; it yields no finite term at all.
- Escape hatch (cyclic IRs): the failure concerns unfolding into finite first-order Term trees. In cyclic program representations such as the PEGs of Tate et al., cycles that pass through loop operators (theta nodes) have a defined loop semantics; such representations are not modelled here.
- The setting is a toy: first-order terms over an arbitrary operator type, models are a carrier with an arbitrary binary relation and list-indexed operator interpretations; no result is a theorem about egg, egglog, Cranelift, LLVM, or any production e-graph or IR.

### Escape hatches

- `one-sided-congruence-refutable-at-non-mono-position`: Escape hatch (two-sided rewriting at eqOnly positions): when P f pre.length = .eqOnly and the premise is strengthened from x0 <= x1 to mutual refinement (x0 <= x1 and x1 <= x0), the step is sound in every model satisfying MonoAt P and KerAt P (Toy.DirCC.eqCong_sound_at_nonOpaque).
- `one-sided-congruence-refutable-at-non-mono-position`: Escape hatch (contravariance): the countermodel flipModel negates the hole argument, which is anti-monotone, and in it the reversed conclusion f(pre, x1, post) <= f(pre, x0, post) holds (Toy.DirCC.flipModel_reversed_conclusion). Anti-monotone modalities and a contravariant congruence rule are not modelled; the theorem does not rule out such a rule being sound for operators that satisfy an anti-monotonicity law.
- `two-sided-congruence-refutable-at-opaque-position`: Escape hatch (partial-order models): the countermodel needs a relation that is not antisymmetric (splitModel_not_antisymm). In a reflexive model, two-sided congruence at an opaqueArg position can fail only if the carrier has distinct mutually refining elements: in a reflexive antisymmetric model the two-sided step is sound at every position (Toy.DirCC.eqCong_sound_of_antisymm). The theorem does not say opaque positions matter in partial-order models.
- `checker-policy-soundness-characterization`: Escape hatch (partial-order models): the necessity of forbidding two-sided congruence at opaqueArg positions rests on a non-antisymmetric countermodel (splitModel). If PolicySound quantified only over antisymmetric models, that restriction would not be necessary: in a reflexive antisymmetric model KerAt holds for every profile (Toy.DirCC.kerAt_of_antisymm) and the two-sided step is sound at every position (Toy.DirCC.eqCong_sound_of_antisymm). The restriction of one-sided congruence to mono positions stays necessary there, because the one-sided countermodel flipModel is antisymmetric (Toy.DirCC.flipModel_antisymm). Partial orders such as sets of outcomes ordered by reverse inclusion, or a flat domain with poison below every value, are examples of antisymmetric relations; they are not defined in this package.
- `cyclic-extraction-counterexample`: Escape hatch (cyclic IRs): the failure concerns unfolding into finite first-order Term trees. In cyclic program representations such as the PEGs of Tate et al., cycles that pass through loop operators (theta nodes) have a defined loop semantics; such representations are not modelled here.

### Attractive stronger conclusions that are not established

- That any production e-graph engine, compiler or IR (egg, egglog, Cranelift, LLVM, Alive2) satisfies or violates any hypothesis here: not examined. The modeling bridges above are derived arguments, not observations of those systems.
- Completeness of the checker, a congruence-closure or saturation algorithm for refinement, or any complexity bound (including a lower bound on certificate size): not established.
- That hash-consing with unique instance tags remains sound after rewriting or refining individual copies: known not to apply (`copy_rewrite_breaks_hashcons`, `one_copy_refinement_breaks_tagged_sharing`).
- That oriented extraction is optimal, shares subterms, or that any cost-based extractor yields well-founded choices: not established.

### Tightness status `unknown`

None: every hypothesis of every result is either `tight` (with a kernel-checked counterexample in which all other hypotheses hold and the conclusion fails) or `harmless` (the `[DecidableEq Op]` instance, needed to compute the checker or to build countermodels).

### Disproved or dropped statements

None of the fifteen stated results was disproved, weakened or dropped; all are proved as stated. The characterization "extraction terminates exactly on well-founded choices" is not a separate result: it appears as the supporting lemma `extract_isSome_iff_wfBelow`, cited by `well-founded-extraction-terminates-and-is-sound`.

## Evidence

**Toolchain.** `leanprover/lean4:v4.34.1`, tag `v4.34.1` of `leanprover/lean4` pointing to commit `5045d0056413266e57c625dcd7c365b10e377c52` (resolved through the GitHub API on 2026-11-20). The library builds with `lake build` in `lean/`.

**Kernel-check record.** For every Lean name referenced by `results.json` (results, tightness counterexamples, non-vacuity witnesses, positive controls), the table gives its role, the axioms reported by Lean's `collectAxioms` (the same set `#print axioms` prints), the SHA-256 of its statement (the Lean `repr` of its type) and the SHA-256 of its definition closure (for every package constant reachable from the statement: its name, the `repr` of its type and, for non-theorems, of its value; sorted, newline-joined). The same data is in `audit/statements.json` and `audit/axioms.json`; `audit/axioms.json` additionally covers every declaration of the library. A hash changes exactly when the statement or a definition it depends on changes.

| Lean name | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample` | result `hash-consing-nondeterministic-node-false-refinement`; non-vacuity `hash-consing-nondeterministic-node-false-refinement` | Quot.sound, propext | `d4f314c499a25c19010e716f09624f3bfd74d90ab2dc15d4effc0d04c7d9071b` | `2fbccf9a196d606e981d4df3f3bce5a1c0bc11b7f1631a01161b066b3d366aaf` (80) |
| `Toy.DirCC.Dup.hashcons_inline_sound_needs_uniqueTags` | counterexample for `hu` in `hash-consing-sound-under-unique-instance-tags` | Quot.sound, propext | `392067366887a8cfe6f945b37b080ca171bf060460509d1203cfe1abe4c4e6e6` | `c065be11d96dd7b5da5695f4c0cb07aa5fb37ecb019b604efd17439c3a01a8d5` (79) |
| `Toy.DirCC.Dup.hashcons_inline_sound_nonvacuous` | non-vacuity `hash-consing-sound-under-unique-instance-tags` | none | `dd6153eb5510297083edaaf9aa3137f852bd97bf731f05c03b3ea5e692351162` | `4d02b40a3084b658e979720e700057f73818b38c391325492cb138839940647a` (22) |
| `Toy.DirCC.Dup.hashcons_inline_sound_of_uniqueTags` | result `hash-consing-sound-under-unique-instance-tags` | Quot.sound, propext | `1144d97d6758c71e7b04be707e5b1da6ed7aec3fae198ae6df0f8c89a12f4099` | `05dfb6d34d70d60d05b09e06aba4a949bfdbf3999b3c03cb5f00e5105c3f7f28` (77) |
| `Toy.DirCC.Dup.hcSem_iff_tagSem_needs_letFree` | counterexample for `hlf` in `hash-consing-faithful-to-per-tag-choice` | propext | `7f400dd2fdf9ca1a9283584393f8ab71b4cc667cf4cbe004594964f3390dbf32` | `18917cd0906fe0533a64515fc5f3e1545dc350a67ed1b5d5e04625038aab0f49` (76) |
| `Toy.DirCC.Dup.hcSem_iff_tagSem_needs_wellTagged` | counterexample for `hwt` in `hash-consing-faithful-to-per-tag-choice` | Quot.sound, propext | `adda394a2812e602dca1401ba676e59d304df77742c42d9c1fd1f2bf8eafacb2` | `2454f210130a92b1e7d1ce84c624693742e2251cf2940232ac4bbbf5da4e2e7b` (76) |
| `Toy.DirCC.Dup.hcSem_iff_tagSem_nonvacuous` | non-vacuity `hash-consing-faithful-to-per-tag-choice` | none | `32e7547a429b9f43ad88b41198b62f94560d5ef324d4e581ab0f785d66f875f4` | `14f0c1b0ad816346caebe99f267562163795151d9940d914dc91b72b009e0f8e` (19) |
| `Toy.DirCC.Dup.hcSem_iff_tagSem_of_letFree_wellTagged` | result `hash-consing-faithful-to-per-tag-choice` | Quot.sound, propext | `757a3f4de3ac3c3b1aaf994f84f0728a844336b2824733367ead8c1504ff99c3` | `4da6bcf43c1c868fe5e8f037ea2a98d2a03a571fd79f2ba52b4ed35714e9f6db` (74) |
| `Toy.DirCC.Dup.tagSem_iff_indep_needs_uniqueTags` | counterexample for `hu` in `per-tag-choice-equals-independent-choice-under-unique-tags` | Quot.sound, propext | `a1052bade2d2166c6bf3cf133157240fdefdba8607aea27ae079eff9236496fd` | `f4056a39e456b451cc485fb7871e3c70bb247db3c03ddb698896f1491033d59f` (33) |
| `Toy.DirCC.Dup.tagSem_iff_indep_nonvacuous` | non-vacuity `per-tag-choice-equals-independent-choice-under-unique-tags` | none | `5b277ef7d04d5ad76c8cd9a54381646862e0f1b15b5071efc2b890a255bb6d96` | `94cf438cb9ffed286a3ef847c15856bf24bd7273a5069b070e1ee67334f3462f` (17) |
| `Toy.DirCC.Dup.tagSem_iff_indep_of_uniqueTags` | result `per-tag-choice-equals-independent-choice-under-unique-tags` | Quot.sound, propext | `15e7ebdceb60f485be0b66963ce15c668d92a4c8e301b18ee1936f0c57440104` | `c8db6b01b1de57bb0b38f4217b484e9eb7db377658f87a1e7fced085f0ff8564` (31) |
| `Toy.DirCC.check_sound` | result `checker-soundness` | propext | `77a4a0ed09eb01879cc93a8810bba12cafaee81e97c0a5175c116b6def09be1e` | `adb3d2a422f1c69e06b8a2fbd1fef4395067e4a352da0a3323549c46de43b33a` (72) |
| `Toy.DirCC.check_sound_needs_check` | counterexample for `hc` in `checker-soundness` | Classical.choice, Quot.sound, propext | `393d72ccea6724602d0ffda719c1f6edfbd6b40fedc0c1acd5ccf1f34625e5e5` | `d5de96748478da5631ce942355e73f7cbfe41858a995d4ba3f1d91432c0a4cbb` (117) |
| `Toy.DirCC.check_sound_needs_factsHold` | counterexample for `hF` in `checker-soundness` | Classical.choice, Quot.sound, propext | `e438ac633bf82a28a657dee25d9c39b24ac61c0d893f62cce3253da82725a471` | `d5de96748478da5631ce942355e73f7cbfe41858a995d4ba3f1d91432c0a4cbb` (117) |
| `Toy.DirCC.check_sound_needs_kerAt` | counterexample for `hKer` in `checker-soundness` | Quot.sound, propext | `71a180aea7bb4624cfca65aa8221bc9be006d4ba26b511935ffaf19872aa5192` | `2ca77eb860c6b23934eb38b53fa3ddfd2ec3a7617c8bc43e2c42b9c9b66c05c9` (116) |
| `Toy.DirCC.check_sound_needs_monoAt` | counterexample for `hMono` in `checker-soundness` | Quot.sound, propext | `29a959efd29612f3b1815b7291b562390fab56f68264c7d4585e5d5025c193c8` | `e7616e78f920bdf9b8d530181580963fe378a06e0855100a9e55ea854e7888f2` (113) |
| `Toy.DirCC.check_sound_needs_refl` | counterexample for `hR` in `checker-soundness` | propext | `badd26ff3fc6d6f71b408142cfb3cbe6bfe051fea7beb42019e18ee7dbc674d7` | `88736cb5431ad6b65f1f4d5d219c811effcbfb3b2e1914e95e45ad9184be355e` (78) |
| `Toy.DirCC.check_sound_needs_trans` | counterexample for `hT` in `checker-soundness` | propext | `733082dd96eb238a200a9fde9c2bf05a8bead85ccedce680fd41eafc97ff1012` | `a8cd46edefc25453b319f872b4d25ce09658782299600e6d5f7865a0f67043b3` (78) |
| `Toy.DirCC.check_sound_nonvacuous` | non-vacuity `checker-soundness` | Classical.choice, Quot.sound, propext | `0ed91b3d03f8766138ae418eff4aa5e35cc54d7b7a1edbc8389182de85aaf143` | `8643e0b69e3fd0d7beacada2e6adee3f90d1334678ae10864c24f75b1b0ff2a1` (119) |
| `Toy.DirCC.check_sound_of_admissible` | result `checker-soundness-admissible-policies` | propext | `5c83ef0cdbd5635823fe18f0dd54941df7ad17154eb40b7d0e141f2513929708` | `6dec4500577705e4c46bc7ba7cfbd0f4a7d4cea1390108e725411115b6b6676e` (66) |
| `Toy.DirCC.check_sound_of_admissible_needs_admissible` | counterexample for `hA` in `checker-soundness-admissible-policies` | Classical.choice, Quot.sound, propext | `c430017d6488eb2c906d890affaa0bc77b3f171b8237de60ec830458a9bff1e2` | `043a73513bdb4f034da5845984b517f97092552aca444d1cfca24f7d384104a6` (112) |
| `Toy.DirCC.check_sound_of_admissible_needs_check` | counterexample for `hc` in `checker-soundness-admissible-policies` | Classical.choice, Quot.sound, propext | `a155d955f77e69adfbe25c57f63f79f949b716cf055142bcf2acfca75093948c` | `e328fbfcf17955fa4ba8fd79067c3fe9301cd60c4d06631841a47998c89c875f` (118) |
| `Toy.DirCC.check_sound_of_admissible_needs_factsHold` | counterexample for `hF` in `checker-soundness-admissible-policies` | Classical.choice, Quot.sound, propext | `3f95687c36a114832529a66286a20a1c7380f3f9aeedd74bd8e6745c898c6999` | `e328fbfcf17955fa4ba8fd79067c3fe9301cd60c4d06631841a47998c89c875f` (118) |
| `Toy.DirCC.check_sound_of_admissible_needs_kerAt` | counterexample for `hKer` in `checker-soundness-admissible-policies` | Quot.sound, propext | `157cb3de2ed2bd13fdc194141312f3155d96a202f2ddcc0a96b4137c7e36c193` | `88856d8594f9769b30ecc2f87e1a9a5236fd8f78d257c57b1ccb7b545e225e20` (117) |
| `Toy.DirCC.check_sound_of_admissible_needs_monoAt` | counterexample for `hMono` in `checker-soundness-admissible-policies` | Quot.sound, propext | `9ede0a6318788785ed8225628dcc1c70536f5c33ae3cf182fcc7bcd2ce19653c` | `4fd6c55d57b1c8503931cd8dbd11e5280b6e6c8c1a38ff05f05bbb5afdfc9c3e` (114) |
| `Toy.DirCC.check_sound_of_admissible_needs_refl` | counterexample for `hR` in `checker-soundness-admissible-policies` | propext | `ab1e2fa87d32273e0138ea3a84f852e7a6e11327a3600f60975bc32c6b49ec98` | `a8585c4a43bdf4adc761d7a5c987a49c91f1cf431ac1ba309bb5b3d4d09a4633` (79) |
| `Toy.DirCC.check_sound_of_admissible_needs_trans` | counterexample for `hT` in `checker-soundness-admissible-policies` | propext | `3f9fce886d0b3ed6d2cd48ca06c6859ebb33a08e59b74f6efef9408881ae920a` | `f3470d81b36140ba81e8e60dafc83c7c7679c43623c7cba78a26258a97268e06` (79) |
| `Toy.DirCC.check_sound_of_admissible_nonvacuous` | non-vacuity `checker-soundness-admissible-policies` | Classical.choice, Quot.sound, propext | `840b0c110b0263058b04108f585a36c8eaeaa9ff0c443769f7e29c21a20dfa2a` | `12f9583efb686478cd00a9d64585ea63df445050c6114382a9667d0d3e031b14` (120) |
| `Toy.DirCC.eqCong_refuted_at_opaque` | result `two-sided-congruence-refutable-at-opaque-position` | Quot.sound, propext | `b58d7f65b0790c7b5c7c0d9fecf4ce6be63b21913ba69a91915e31d8a4f83c64` | `0331036fdf5ed58399698fef5caf9dc82f955b0b3f8c840dd8bf0255a1c3c48b` (44) |
| `Toy.DirCC.eqCong_refuted_needs_opaque` | counterexample for `h` in `two-sided-congruence-refutable-at-opaque-position` | propext | `378aea13619268a35f402e9acfd67080f178af11e18267b43fcfc48c01482a37` | `e9badc0265fbdd2f990f384732158f3d9831bfebf90b8907cf33585eb685ad95` (36) |
| `Toy.DirCC.eqCong_refuted_nonvacuous` | non-vacuity `two-sided-congruence-refutable-at-opaque-position` | propext | `c5c17b3011c1c949b86508a504c7cc9bd0edf447c35d584e4901d0464070b38b` | `9de27727808272a7a2b45bdd36de746c31900470a36269621be2666278bf0943` (20) |
| `Toy.DirCC.eqCong_sound_at_nonOpaque` | positive control `two-sided-congruence-refutable-at-opaque-position` | propext | `c1d039491f53fa941cfb242090ed18b03b2fffebc65adf9f28f329100209876e` | `0006053a0ffbbf11ee0c0eca3b1ee73db3c5b65e3c0961d09e5185b002f52e63` (27) |
| `Toy.DirCC.extractWF_needs_chosenMono` | counterexample for `hCM` in `well-founded-extraction-terminates-and-is-sound` | Quot.sound, propext | `61d038617761500f788d723ac64fb2fe6f12ef90d0a9fc930f79ffef3a4b9c25` | `3c7901fc75519f2a7d8272b762f745ea307fe5d9be4e17914103973396617ed5` (70) |
| `Toy.DirCC.extractWF_needs_chosenOriented` | counterexample for `hCO` in `well-founded-extraction-terminates-and-is-sound` | Quot.sound, propext | `23406c5dd2645dfb9b92931509185a64560add23fc5ca1c7b331f2ed05d0791a` | `e04826b16f845fe67e7b0ddecde78d5c1523166111322eab57ba7bbd595fbb0b` (70) |
| `Toy.DirCC.extractWF_needs_monoAt` | counterexample for `hMono` in `well-founded-extraction-terminates-and-is-sound` | Quot.sound, propext | `19aa9fcf0ea65cf04d9f4db60a2295cd57c19180e4fc2632f115e2f595de9eb8` | `40b56ed30537e84ef60adfb506a01cc97db8858c7966fbaf91e7392e651dca1e` (67) |
| `Toy.DirCC.extractWF_needs_trans` | counterexample for `hT` in `well-founded-extraction-terminates-and-is-sound` | Quot.sound, propext | `a4e1a0251522f1cc6d2383483afd3a4a802b10bb454eaaebcd79dc9527ebdec8` | `8e806c5db306d31570a7bea83b779dc23293809ff14cb68b87741f6aaf3b1cf9` (53) |
| `Toy.DirCC.extractWF_needs_wfBelow` | counterexample for `hW` in `well-founded-extraction-terminates-and-is-sound` | Quot.sound, propext | `78bc5eb5a48961a1c22df00f1e1d8c11057edee36d174310694d9563f300e879` | `08d428a35b1e14e533830bb4fa9244f7d7816c02af8c0c272076e8c87341f17d` (68) |
| `Toy.DirCC.extract_cycle_counterexample` | result `cyclic-extraction-counterexample`; non-vacuity `cyclic-extraction-counterexample` | Quot.sound, propext | `217cd18f348aa31f3442613d661256788c2841389fbfaaa201b8c80701b725a9` | `867a942729cf2cac80d5e7c2593ce9e668b2c2cba55f8e7873f2a02ee69d3b20` (62) |
| `Toy.DirCC.extract_needs_choiceIn` | counterexample for `hC` in `oriented-extraction-sound-egraph-form` | Quot.sound, propext | `63d78e1fa692465b672a038c207d7e6b451e77e2fef85892fc267ea7a20c7e5d` | `526b2dabefa83557104f8d87fdab135eda96646ced5093c95beb994df761a416` (73) |
| `Toy.DirCC.extract_needs_chosenMono` | counterexample for `hCM` in `oriented-extraction-sound`; counterexample for `hCM` in `oriented-extraction-sound-egraph-form` | Quot.sound, propext | `a2d022df69311777f1a3ea59082aeda35c7a917fd85862bac9d0c891978913fb` | `6fbc0e70b470edff499d8d266bd8787e3064a9b4fc0b2ec654939f105de26ee3` (74) |
| `Toy.DirCC.extract_needs_extract_some` | counterexample for `h` in `oriented-extraction-sound`; counterexample for `h` in `oriented-extraction-sound-egraph-form` | Quot.sound, propext | `668e1e6faab10f0cdee9ccd5f1350ce1d68969b3b74268fcb5e8f8e9758a9187` | `918b6bdbb3b7b5459d2848d03269924ab1457d2d8c353206e97b1e914f9881eb` (73) |
| `Toy.DirCC.extract_needs_monoAt` | counterexample for `hMono` in `oriented-extraction-sound`; counterexample for `hMono` in `oriented-extraction-sound-egraph-form` | Quot.sound, propext | `78fe1fc3264ff0a94cf7af76aa5e259fa4b988c4aae2d577036f2a1e191573d5` | `5561754602848d8e6528d332c045552e91cc574ef97d929f6bf818a75c119009` (71) |
| `Toy.DirCC.extract_needs_trans` | counterexample for `hT` in `oriented-extraction-sound`; counterexample for `hT` in `oriented-extraction-sound-egraph-form` | Quot.sound, propext | `7e4e498e15d540b9a54475aa74c0459505f7cf023d8a147001403386b1997768` | `feebd8e10961af285c89e27afb1ca93f0cd5d85cadfffeefa82960a0a2b308d3` (56) |
| `Toy.DirCC.extract_oriented_needs_oriented` | counterexample for `hO` in `oriented-extraction-sound-egraph-form` | Quot.sound, propext | `edec5d97e60a42b6927d06ab28bbcc6668b45c0ff1af56c71cfeecdd1b42993f` | `99ffdd9f0acba7fe7a0802f4f64d059b82346d9842220f97811d0dd0c2d3c75b` (72) |
| `Toy.DirCC.extract_refines_nonvacuous` | non-vacuity `oriented-extraction-sound`; non-vacuity `oriented-extraction-sound-egraph-form` | Quot.sound, propext | `af865e4e8963e0689a59f0511872f0e3105cbe730079950f2fa39285ac562fe3` | `160db2633b4453fe5353c3407c4cb71c4a5028202843c83ce6f9d3c550dbafd0` (73) |
| `Toy.DirCC.extract_refines_of_chosenOriented_mono` | result `oriented-extraction-sound` | Classical.choice, Quot.sound, propext | `2d1ac4915774f0af6aa81359a8262455f1c9052ec1571ad02e315d2bdbb83e32` | `626765ee3979d28979b60c926d959df70de5a78ec0bf811b0927192523e929fa` (44) |
| `Toy.DirCC.extract_refines_of_oriented_mono` | result `oriented-extraction-sound-egraph-form` | Classical.choice, Quot.sound, propext | `92b9ce57eaceb9173157a53d49fa07453338418535e258aa48a10ede8154e0ea` | `50d3ec9cdae1b6c2d24bb95294ae4849ae1f8f6612cf06d3648c1ee7f0c954d3` (48) |
| `Toy.DirCC.extract_total_and_sound_of_wfBelow_oriented_mono` | result `well-founded-extraction-terminates-and-is-sound` | Classical.choice, Quot.sound, propext | `424ed02839f12db058a68128a7ed86c80f8ec47ec132613eb8e818443ab3eba8` | `e4fc47001ed7bc207ec355cb294e0f5e10dd6f8e444e2ad52ce6cb25f1c3c1aa` (47) |
| `Toy.DirCC.extract_unoriented_counterexample` | counterexample for `hCO` in `oriented-extraction-sound`; result `unoriented-extraction-counterexample`; non-vacuity `unoriented-extraction-counterexample` | Quot.sound, propext | `26367968ce03486aea5ef85fe12b9f81072e50d160811e2bf6bcda1f0ac59d68` | `7bba826a421b288ad4568998f79efe8634339fd25dd784f226ff7643a243e43d` (73) |
| `Toy.DirCC.extract_wf_nonvacuous` | non-vacuity `well-founded-extraction-terminates-and-is-sound` | Quot.sound, propext | `0889252d25ccb7067bde2d5b2e18faa194768a3be9e30c84384fc67d5832ba06` | `4bd3778fa760650fc31ac3d70264df9fb0aaf8a2b80a9eb772ed44095cdeaeee` (66) |
| `Toy.DirCC.monoCong_refuted_at_nonMono` | result `one-sided-congruence-refutable-at-non-mono-position` | Quot.sound, propext | `1d2d2214d7b23040bfb5ae02a2cd0a9f0c63125c16f92ff065d2418c846e83d9` | `2286992259e741576aea3706a638e4530fb16f77713a4c834abd2b433f090918` (31) |
| `Toy.DirCC.monoCong_refuted_needs_nonMono` | counterexample for `h` in `one-sided-congruence-refutable-at-non-mono-position` | propext | `8003254f6d1382678b0a80897cc1448fed27a3fea32b22883bc62c175d10f231` | `02421839a1214078c9762ae781d10fa71f6c59ecc4eb53554e3dd02bad920df9` (21) |
| `Toy.DirCC.monoCong_refuted_nonvacuous` | non-vacuity `one-sided-congruence-refutable-at-non-mono-position` | propext | `760aeb61266fe14a0e6c5c3c6915b9f5612acc85d04da2fa04ecc3f442dcc103` | `9de27727808272a7a2b45bdd36de746c31900470a36269621be2666278bf0943` (20) |
| `Toy.DirCC.monoCong_sound_at_mono` | positive control `one-sided-congruence-refutable-at-non-mono-position` | propext | `99f4dbe14e62705707adbf20fc5d80f1a99e7800d29f5cf0015b807bd781aedb` | `43d0843527f0d4ac6cb37bba98e3095a1f6c310d54ebf6e494c9ea1494a11a6b` (26) |
| `Toy.DirCC.not_policySound_permissive_oProfile` | non-vacuity `checker-policy-soundness-characterization` | Quot.sound, propext | `a4355ab8014a18ff07be87acc36f819da090d7341f553a7ddee6e2384254ec52` | `70e1790f3c93fdbda127a8ba3fbd88421d7b67ad529bf95a603e6ed0f83e9cbe` (104) |
| `Toy.DirCC.pickFirst_eqCong_counterexample` | result `committed-choice-operators-in-outcome-semantics`; non-vacuity `committed-choice-operators-in-outcome-semantics` | Classical.choice, Quot.sound, propext | `f23319344a6d4f78fd2dccbd9c89826538472d28cc114ca616835920d5d5aba7` | `35b8fee2a473f98a83fe78dc754734d314d2b6363cfed0380fb584a898c21813` (118) |
| `Toy.DirCC.pickMin_monoCong_counterexample` | result `committed-choice-operators-in-outcome-semantics`; non-vacuity `committed-choice-operators-in-outcome-semantics` | Classical.choice, Quot.sound, propext | `cc4791ba4955fa643b8972594238184bfbc124af81176c01dea25ed6a4aa422f` | `35b8fee2a473f98a83fe78dc754734d314d2b6363cfed0380fb584a898c21813` (118) |
| `Toy.DirCC.policySound_iff_admissibleFor` | result `checker-policy-soundness-characterization` | Quot.sound, propext | `6036f1eb87a2ed9809ca96bf2f1df4dc248ddb2fbdcf6f34a018b178b0bc2f81` | `a8b62eb3349a96ef1f1b61d21c28c8b911f5c10ffa5c488adbb6641f24b4f647` (67) |
| `Toy.DirCC.policySound_nonvacuous` | non-vacuity `checker-policy-soundness-characterization` | propext | `d4f9b122e66d3e787929cf06711b164e790d4bb698deff35fd70257672c3582b` | `cb80a5bc5812c0ae506c6302557af3354719dc8eef117b08d335c085f26fda8e` (30) |
| `Toy.DirCC.policySound_permissive_of_empty_op` | non-vacuity `checker-policy-soundness-characterization` | Quot.sound, propext | `832e57b91cc8e5b337dcc243560b7ff37b2f3efd9d85627a2ce8134bd2e58552` | `7f2309621e440d587efdd7895b86113c94a434f25b3f99769c4c655bcb1a8326` (67) |
| `Toy.DirCC.policySound_standard_oProfile` | non-vacuity `checker-policy-soundness-characterization` | Quot.sound, propext | `923f7da2e5d28e3e801ddbeb9c58a143bdac82a84651024840a9d2d62f58f45d` | `b619ac48b1c7f17e587f29363e770eb04d174fcf3b045a76a59aa74839620e48` (110) |

Counts: 61 referenced names; 805 library declarations audited, none with an axiom outside `propext`, `Classical.choice`, `Quot.sound`, and no `axiom` or `opaque` declarations. Lean sources contain no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern` or `unsafe`.

**Primary sources.** Bibliographic records with DOIs were checked against Crossref (and dblp where noted) on 2026-11-20; repository commits were resolved through the GitHub API on the same date. Each entry states which parts were consulted; where a full text was not consulted, the entry says so.

- **Meseguer 1992.** J. Meseguer. Conditional rewriting logic as a unified model of concurrency. Theoretical Computer Science 96(1):73-155, 1992. DOI 10.1016/0304-3975(92)90182-F. Deduction rules Reflexivity, Congruence (every argument), Replacement, Transitivity for directed rewrites; rules as quoted in J. Meseguer, Twenty years of rewriting logic, J. Logic and Algebraic Programming 81(7-8):721-781, 2012, DOI 10.1016/j.jlap.2012.06.003 (the 1992 full text was not consulted).
- **Bruni and Meseguer 2006.** R. Bruni, J. Meseguer. Semantic foundations for generalized rewrite theories. Theoretical Computer Science 360(1-3):386-414, 2006. DOI 10.1016/j.tcs.2006.04.012. Generalized rewrite theories carry a frozenness map: argument positions under which no rewrite may be performed while equational reasoning modulo E still applies (definition as stated in Meseguer's 2012 survey, DOI 10.1016/j.jlap.2012.06.003; the 2006 full text was not consulted).
- **Bloom 1976.** S. L. Bloom. Varieties of ordered algebras. Journal of Computer and System Sciences 13(2):200-212, 1976. DOI 10.1016/S0022-0000(76)80030-X (bibliographic record verified at Crossref; full text not consulted): algebras over ordered carriers with monotone operations, the algebraic setting of inequational (directed) reasoning with all positions monotone.
- **Rocq generalized rewriting.** Rocq Reference Manual V9.2.0, Generalized rewriting, https://rocq-prover.org/doc/V9.2.0/refman/addendum/generalized-rewriting.html: a morphism signature gives each argument its own relation instance and n-ary morphisms are required to be monotone in every argument; the arrow --> marks a contravariant argument (covariant for the inverse relation), and ==> is the arrow the manual uses for arguments related by symmetric relation instances, where covariance and contravariance coincide; rewriting under a function that has not been declared a morphism fails. In rocq-prover/rocq at tag V9.0.0, theories/Classes/Morphisms.v defines R ++> R' and R ==> R' as the same term (respectful R R'), so over an asymmetric preorder le the signature le ==> le expresses monotonicity; respecting only mutual refinement needs a separate symmetric relation instance in that argument slot.
- **Sozeau 2009.** M. Sozeau. A New Look at Generalized Rewriting in Type Theory. Journal of Formalized Reasoning 2(1):41-62, 2009. DOI 10.6092/issn.1972-5787/1574 (bibliographic record verified at dblp; full text not consulted): the design of the typeclass-based generalized rewriting of Coq/Rocq described in the manual entry above.
- **Zucker 2026 (blog post and prototype; not peer-reviewed).** P. Zucker. Refinement E-Graphs. Blog post (not peer-reviewed), dated 2026-10-04, https://www.philipzucker.com/refinement_egraph/; the post's source is preserved in the public repository philzook58/philzook58.github.io at commit de5119da6ee25e23d419dd8c95484cf295510031, file _posts/2026-10-04-refinement_egraph.md. Prototype (research software, not peer-reviewed): philzook58/refinement-microegg at commit 95a098d4751fd468a874ddeb5627330240182193. A built-in <= relation that is reflexive, transitive and collapses cycles to =; per-argument variance (monotone, anti-monotone, unknown); 'refinement closure' instead of congruence closure; extraction in <= / >= modes. Functions always respect =, so there is no opaque position kind; freeze and hash-consing of nondeterministic nodes are not discussed.
- **Nieuwenhuis and Oliveras 2005.** R. Nieuwenhuis, A. Oliveras. Proof-Producing Congruence Closure. RTA 2005, LNCS 3467, 453-468. DOI 10.1007/978-3-540-32033-3_33. Incremental congruence closure with an Explain operation, for equalities (the congruence relation satisfies reflexivity, symmetry, transitivity and monotonicity f(x1..xn)=f(y1..yn) whenever xi=yi).
- **Nelson and Oppen 1980.** G. Nelson, D. C. Oppen. Fast Decision Procedures Based on Congruence Closure. J. ACM 27(2):356-364, 1980. DOI 10.1145/322186.322198 (equational congruence closure; full text not consulted).
- **Chew 1980.** P. Chew. An improved algorithm for computing with equations. 21st Annual Symposium on Foundations of Computer Science (FOCS 1980), 108-117. DOI 10.1109/SFCS.1980.11 (bibliographic record verified at Crossref; full text not consulted). The name 'directed congruence closure' is attributed to this paper in secondary sources, for computing normal forms of terms under non-overlapping left-linear rewrite rules; that is a different notion from the refinement-preorder congruence closure of this package.
- **Selsam and de Moura 2016.** D. Selsam, L. de Moura. Congruence Closure in Intensional Type Theory. IJCAR 2016, LNCS, 99-115. DOI 10.1007/978-3-319-40229-1_8 (bibliographic record verified at Crossref; full text not consulted): equational congruence closure in a proof assistant.
- **Stevens and Ghidini 2025.** L. Stevens, R. Ghidini. Simplified and Verified: A Second Look at a Proof-Producing Union-Find Algorithm. CADE-30, LNCS, 2025, 261-279. DOI 10.1007/978-3-031-99984-0_15 (abstract consulted at Crossref): an Isabelle/HOL verification of the union-find with an explain operation of Nieuwenhuis and Oliveras, a step towards verified proof-producing (equational) congruence closure.
- **Morrison and de Moura 2026.** K. Morrison, L. de Moura. grind: An SMT-Inspired Tactic for Lean 4 (short paper). Automated Reasoning, LNCS, 2026, 106-114. DOI 10.1007/978-3-032-32589-1_7 (abstract consulted at Crossref): a Lean 4 tactic combining congruence closure for dependent type theory with E-matching, producing kernel-checkable proofs (equational).
- **Mathlib gcongr.** Mathlib.Tactic.GCongr.Core, leanprover-community/mathlib4 at commit 426b896108cc3d6e923ef7739a302306e0702fc0 (authors M. Carneiro, H. Macbeth, J. Gerbscheid): the gcongr ('generalized congruence') tactic reduces a relational goal between two applications to relations between their 'varying' arguments using lemmas tagged @[gcongr], with the remaining arguments fixed; per-lemma monotonicity rules for Lean's order relations.
- **Lucas 1996.** S. Lucas. Context-sensitive computations in confluent programs. PLILP 1996, LNCS, 408-422. DOI 10.1007/3-540-61756-6_100 (bibliographic record verified at Crossref and dblp; full text not consulted): context-sensitive rewriting, where a replacement map fixes for each operator the argument positions under which rewriting is allowed.
- **Lopes et al. 2015 (Alive).** N. P. Lopes, D. Menendez, S. Nagarakatte, J. Regehr. Provably correct peephole optimizations with Alive. PLDI 2015, 22-32. DOI 10.1145/2737924.2737965: 'The target of an Alive transformation refines the source template if all the behaviors of the target are included in the set of behaviors of the source.'
- **Lopes et al. 2021 (Alive2).** N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr. Alive2: bounded translation validation for LLVM. PLDI 2021, 65-79. DOI 10.1145/3453483.3454030: 'Refinement allows a transformation to remove non-determinism, but not to add it.'
- **Lee et al. 2017.** J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes. Taming Undefined Behavior in LLVM. PLDI 2017, 633-647. DOI 10.1145/3062341.3062343. 'All uses of a given freeze return the same value, but different freezes of a value may return different constants.' Section 5.5: 'Duplicating freeze instructions is not allowed, since each freeze instruction may return a different value if the input is poison.'
- **LLVM LangRef, freeze.** LLVM Language Reference, llvm/llvm-project at commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, llvm/docs/LangRef.md, 'freeze' instruction: an undef or poison argument yields 'an arbitrary, but fixed, value'; 'All uses of a value returned by the same freeze instruction are guaranteed to always observe the same value, while different freeze instructions may yield different values.'
- **Cranelift e-graph RFC.** bytecodealliance/rfcs, accepted/cranelift-egraph.md (at commit b6faa4a4b7de4d0208b2ef72470b01feded00e4c): restricting union to node-creation time gives the acyclic e-graph; side-effecting Inst nodes keep the original instruction 'so that the Insts are not deduplicated: every instance is a logically separate and unique side-effect.'
- **Cranelift skeleton instructions.** bytecodealliance/wasmtime at commit 9e2a9d627d0caf56b9d0c99da1ef989971f016e3, cranelift/codegen/src/egraph/mod.rs (optimize_skeleton_inst): in the shipped implementation, as opposed to the RFC above, side-effecting 'skeleton' instructions stay in the layout rather than in the e-graph; those satisfying is_mergeable_for_egraph are still deduplicated against a dominating identical instance through a scoped GVN map, and other side-effecting instructions are always kept.
- **Flatt et al. 2026 (preprint).** O. Flatt, A. Pal, Y. Zhang, R. Tjoa, K. Graham, A. Fischman, C. Nandi, E. Rosenthal, Z. Tatlock, H. Ni. Efficient Extraction for Effectful E-Graphs. arXiv:2609.31887, 2026 (preprint; abstract consulted): extraction for e-graphs of effectful programs whose memory and I/O operations must respect execution order.
- **Willsey et al. 2021 (egg).** M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock, P. Panchekha. egg: Fast and Extensible Equality Saturation. Proc. ACM Program. Lang. 5(POPL), 1-29, 2021. DOI 10.1145/3434304. Rewrites add the right-hand side and merge it with the matched e-class (equalities); extraction selects a minimum-cost represented term from an e-class.
- **Cranelift aegraph.** bytecodealliance/wasmtime at commit 9e2a9d627d0caf56b9d0c99da1ef989971f016e3: cranelift/codegen/src/ir/dfg.rs (Union values 'used for aegraph (acyclic egraph) representation'); cranelift/codegen/src/egraph/mod.rs (rewrites union all rewritten forms into an eclass, with an opt-in 'subsume'; side-effectful instructions are not added to the egraph); cranelift/codegen/src/egraph/elaborate.rs (best value chosen bottom-up over a topological order, minimum over Union nodes).
- **Ramos et al. 2026 (AFP).** A. F. Ramos, D. B. Hulak, R. J. G. B. de Queiroz. Checking Equality-Saturation Merge and Extraction Certificates. Archive of Formal Proofs, July 14, 2026, https://www.isa-afp.org/entries/Equality_Saturation_Checker.html (entry abstract consulted): an Isabelle/HOL executable checker for egg 0.11.0 flat explanations and, for extraction, a bottom-up dynamic program over a finite e-graph represented as a topologically ordered e-class DAG with a proof of minimum additive cost; soundness targets the (symmetric) conversion relation of the AFP entry First-Order Rewriting.
- **egg extractor.** egraphs-good/egg at commit 73975c9819efb4af2f3c6c1b44fa53f8c5742574, src/extract.rs: the extractor's cost fixpoint (find_costs / make_pass) assigns a cost to an e-node only when every child class already has a cost (node_total_cost returns None otherwise). This is a property of the implementation, not a statement of the POPL 2021 paper.
- **Tate et al. 2009/2011.** R. Tate, M. Stepp, Z. Tatlock, S. Lerner. Equality saturation: a new approach to optimization. POPL 2009, 264-276, DOI 10.1145/1480881.1480915; journal version Logical Methods in Computer Science 7(1:10), 2011, DOI 10.2168/LMCS-7(1:10)2011. Optimizations are equality analyses that merge PEG nodes into equivalence classes (E-PEGs); loops are theta nodes; well-formed PEGs require every cycle to pass through a theta node's second child; global profitability is solved with a pseudo-Boolean solver.
- **Arbore et al. 2026.** R. Arbore, A. Cheung, M. Willsey. Optimism in Equality Saturation. Proc. ACM Program. Lang. 10(PLDI):1383-1406, 2026. DOI 10.1145/3808302 (bibliographic record verified at Crossref). Equality saturation creates cyclic represented graphs to which no concrete execution can be assigned ('ill-formed').
- **Blanqui and Koprowski 2011.** F. Blanqui, A. Koprowski. CoLoR: a Coq library on well-founded rewrite relations and its application to the automated verification of termination certificates. Mathematical Structures in Computer Science 21(4):827-859, 2011. DOI 10.1017/S0960129511000120 (abstract consulted at Crossref): a mechanized library of well-founded (rewrite) relations.

## Revalidation

Requirements: `elan` (so that `lake` picks up the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects Lean sources containing `sorry`, `admit`, `native_decide` or an `axiom` declaration, runs a generated Lean audit program that computes, with `Lean.collectAxioms`, the axioms of every library declaration (failing on anything outside `propext`, `Classical.choice`, `Quot.sound`), and recomputes the statement and closure hashes of every name referenced by `results.json` and recorded in `audit/statements.json`, comparing them with the recorded values. Its docstring describes exactly what is hashed (the same definition as under Evidence). It prints `REVALIDATED` and exits with status 0 iff all checks pass.

Manual equivalent of the build and axiom audit:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is outside the library target; it runs `#print axioms` on every card-referenced declaration and prints its statement with `#check`. Every `#print axioms` line must list only `propext`, `Classical.choice` and `Quot.sound` (or report no axioms).

Cheapest discriminating check after a change to the Lean sources: rerun `python3 support/revalidate.py .`; a statement-hash failure identifies exactly which card's statement or definition closure changed, and a build or axiom failure means the corresponding results are no longer established.
