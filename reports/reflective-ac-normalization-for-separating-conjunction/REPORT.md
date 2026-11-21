# Reflective AC Normalization and Sub-Multiset Frame Cancellation for Separating Conjunction in Lean 4

## Summary

This package is a self-contained, Mathlib-free Lean 4 (`v4.34.1`) toy formalization (namespace `Toy.SepAC`) characterizing the exact algebraic laws, completeness boundaries, frame-cancellation guarantees, and decision-procedure tradeoffs of reflective associative-commutative (AC) and associative-commutative-unital (ACU) normalization for separating conjunction:

- **Exact algebraic law accounting (`R1a`–`R1c`, `R2a`–`R2c`):** Universal flattening to right-nested folds (`denoteAtoms`) is equivalent to `SepAssoc ∧ LeftUnit ∧ RightUnit`; universal `List.isPerm` soundness over arbitrary trees is equivalent to `SepAssoc ∧ SepComm ∧ RightUnit` (`LeftUnit` derived), with 3 elements as the minimal non-associative commutative unital countermodel (`atMostTwo_comm_unital_sepAssoc`); and without any unit law on `emp`, `SepAssoc ∧ SepComm` is equivalent to `List.isPerm` soundness on equal-`unitCount` (or `unitFree`) trees.
- **Free-monoid completeness vs. pointwise-idempotent and conflict incompleteness (`R3a`, `R3b`):** `List.isPerm` is complete relative to the finitely supported multiplicity monoid `Bag` under distinct generators `Bag.single` (equivalently, universal equality across all `Type`-level ACU models), but fails completeness whenever an atom value is pointwise idempotent (`IdemElem`), whenever distinct indices are aliased or mapped to `emp`, and for some environments of non-idempotent ACU models with an absorbing conflict element (`CellModel` at `env = fun _ => owned`, `TwoCellModel` at `env 0 = cellA`, `env 1 = cellB`); an absorbing element does not by itself break completeness for every environment (`Toy.SepAC.optBag_absorbing_but_complete`).
- **Arbitrary sub-multiset frame cancellation and maximal-cancellation non-invertibility (`R4a`–`R4d`):** Under propositional ACU laws, arbitrary common sub-multiset cancellation (with `cancelAtoms` as maximal special case) needs only `SepMonoRight` (no `EntailsRefl`, `EntailsTrans`, or `SepMonoLeft`); weakening propositional `=` to `Bientails entails` makes `EntailsTrans` necessary relative to the other hypotheses (it cannot be dropped; `Toy.SepAC.tagDistLeOne_tight_bientails_commonPerm_trans`) while keeping `EntailsRefl` and `SepMonoLeft` derivable; and maximal cancellation via `cancelAtoms` is non-invertible in both linear (`CellModel`) and affine (`TwoCellModel`) conflict models, whereas non-maximal partial cancellation can succeed where `cancelAtoms` fails.
- **Quasilinear check vs. kernel reduction (`R5`):** Accumulator extraction `atomsFast` plus `List.mergeSort` computes the exact same boolean as structural `List.isPerm` with `atomsFast.length = atomCount ≤ size`, though on Lean `v4.34.1` the kernel does not reduce well-founded `List.mergeSort`, or `checkPermSort`, to `true` on the probed instances, unlike `List.isPerm` and Core Lean's `Lean.Data.AC.sort` (execution observation; probe `support/KernelReductionProbe.lean`).

No novelty claims are made: all equational and complexity results are `T0` re-derivations or exact characterizations, maximal-cancellation non-invertibility in linear/affine conflict models is `T1`, and the generalized unbundled `SepMonoRight` / `Bientails` arbitrary-sub-multiset frame-cancellation theorems are `T2`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (full statements, hypothesis ledgers, witnesses, and non-claims are in **Findings** and **Boundaries**):

- **R1a:** `Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units` — For any `(sep, emp)` satisfying `SepAssoc`, `LeftUnit`, and `RightUnit` (no commutativity assumed), every syntax tree `t` evaluates identically to the right-nested fold `denoteAtoms sep emp env t.atoms`.
- **R1a-iff:** `Toy.SepAC.denote_eq_denoteAtoms_iff_assoc_units` — Universal soundness of flattening `Tree.denote` to `denoteAtoms` over all environments and trees holds if and only if `SepAssoc sep`, `LeftUnit sep emp`, and `RightUnit sep emp` all hold.
- **R1b:** `Toy.SepAC.acu_denote_eq_of_isPerm` — For any `(sep, emp)` satisfying `SepAssoc`, `SepComm`, and `RightUnit` (`LeftUnit` derived), `l.atoms.isPerm r.atoms = true` implies `l.denote sep emp env = r.denote sep emp env` in every environment `env : Nat → P` (covering finite list-backed environments via `listEnv`).
- **R1b-iff:** `Toy.SepAC.acu_denote_eq_of_isPerm_iff` — Universal soundness of the `List.isPerm` reflective kernel over all environments and trees holds if and only if `SepAssoc sep`, `SepComm sep`, and `RightUnit sep emp` all hold.
- **R1c-unit-count:** `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm` (+ `unitCount_eq_and_isPerm_of_forall_ac_denote_eq`) — Without any unit law on `emp`, `SepAssoc` and `SepComm` make `l.atoms.isPerm r.atoms = true` sound whenever `l.unitCount = r.unitCount`, and `l.unitCount = r.unitCount ∧ l.atoms.isPerm r.atoms = true` follows necessarily if `l` and `r` denote equally across all `Type`-level associative-commutative `(P, sep, emp, env)`.
- **R1c-unit-free:** `Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm` — Specializing `R1c-unit-count`, under `SepAssoc` and `SepComm` (no unit law), `l.atoms.isPerm r.atoms = true` implies `l.denote sep emp env = r.denote sep emp env` whenever both `l` and `r` are `unitFree`.
- **R1c-iff:** `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_iff`, `Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm_iff` — Universal `List.isPerm` soundness over equal-`unitCount` trees (equivalently, `unitFree` trees) holds if and only if `SepAssoc sep` and `SepComm sep` hold.
- **R2a:** `Toy.SepAC.listAppend_tight_isPerm_sepComm` — Reference counterexample: `(List Nat, List.append, [])` satisfies `SepAssoc`, `LeftUnit`, and `RightUnit` while violating `SepComm`, breaking `List.isPerm` soundness on `[0, 1]` vs `[1, 0]`.
- **R2b:** `Toy.SepAC.nonAssoc_tight_isPerm_sepAssoc` (+ `atMostTwo_comm_unital_sepAssoc`) — Reference counterexample: the 3-element commutative unital magma `NonAssocCarrier.op` refutes `List.isPerm` even on identical atom lists `[0, 0, 1]`, and 3 elements is minimal because every commutative right-unital magma of size at most 2 is associative.
- **R2c:** `Toy.SepAC.boolAndFalse_tight_isPerm_rightUnit` — Reference counterexample: `(Bool, Bool.and, false)` satisfies `SepAssoc` and `SepComm` while violating `RightUnit`, refuting `List.isPerm` on `atom 0` vs `atom 0 ∗ unit`.
- **R3a:** `Toy.SepAC.isPerm_of_bag_denote_eq` — In the finitely supported multiplicity monoid `(Bag, Bag.sep, Bag.emp)` under the free generator map `Bag.single`, equal denotations imply `l.atoms.isPerm r.atoms = true`.
- **R3a-iff:** `Toy.SepAC.isPerm_iff_bag_denote_eq` (+ `isPerm_iff_forall_acu_denote_eq`) — `l.atoms.isPerm r.atoms = true` holds if and only if `l` and `r` denote equally in `(Bag, Bag.sep, Bag.emp)` under `Bag.single`, and equivalently iff they denote equally in every `Type`-level ACU model and environment.
- **R3b:** `Toy.SepAC.denote_eq_and_isPerm_false_of_idemElem` (+ conflict witnesses) — Any pointwise-idempotent atom `IdemElem sep (env 0)` (`env 0 ∗ env 0 = env 0`) makes `atom 0 ∗ atom 0` and `atom 0` denote equally with `isPerm = false`, and absorbing conflict elements in non-idempotent ACU models break `List.isPerm` completeness for the exhibited environments (`CellModel`, `TwoCellModel`), though not necessarily for every environment (`Toy.SepAC.optBag_absorbing_but_complete`).
- **R4a:** `Toy.SepAC.acu_entails_of_common_perm_of_sepMonoRight` (+ `cancelAtoms` corollary and spec) — Under propositional `SepAssoc`, `SepComm`, `RightUnit`, and `SepMonoRight`, any common sub-multiset `common` (`l.atoms ~ common ++ ls`, `r.atoms ~ common ++ rs`, including maximal `cancelAtoms`) cancels soundly without assuming `EntailsRefl`, `EntailsTrans`, or `SepMonoLeft`.
- **R4b:** `Toy.SepAC.bientails_acu_entails_of_common_perm_of_trans_sepMonoRight` (+ `cancelAtoms` corollary) — When ACU laws hold only up to mutual entailment `Bientails entails`, adding `EntailsTrans entails` alongside `SepMonoRight` suffices for arbitrary sub-multiset frame cancellation (`EntailsRefl` and `SepMonoLeft` remain derivable).
- **R4c:** `Toy.SepAC.capOne_tight_commonPerm_sepMonoRight` — Reference counterexample: on `(Nat, +, 0)`, the reflexive transitive preorder `capOneEntails` violates `SepMonoRight` and turns the false entailment `1 ⊢ 2` into the true residual `0 ⊢ 1` under `cancelAtoms`.
- **R4d:** `Toy.SepAC.cellModel_cancelAtoms_converse_fails` (+ `twoCellModel_affine_cancelAtoms_converse_fails`, `partial_cancellation_succeeds_where_cancelAtoms_fails`) — Maximal syntactic cancellation (`cancelAtoms`) is non-invertible in both linear (`CellModel`) and affine (`TwoCellModel`) ACU preorders with conflict, whereas partial non-maximal cancellation can still succeed where `cancelAtoms` fails.
- **R5:** `Toy.SepAC.checkPermSort_eq_isPerm_and_size_bounds` — Accumulator extraction `atomsFast` equals `atoms`, has length `atomCount ≤ size`, and merge-sort check `checkPermSort l r` equals `l.atoms.isPerm r.atoms` for all trees.

See the **Non-claims** subsection at the top of **Boundaries** before applying any result beyond its stated hypotheses.

## Applicability

**Model fidelity: this is a toy model.** All definitions live in the Lean 4 namespace `Toy.SepAC` (`lean/Toy/SepAC/*.lean`). They represent separating conjunction `∗`, empty-heap assertion `emp`, and entailment `⊢` abstractly as an arbitrary carrier `P : Type u`, an unbundled binary function `sep : P → P → P`, a distinguished constant `emp : P`, and an arbitrary binary relation `entails : P → P → Prop`. No algebraic or order laws are bundled into typeclasses or structures; every theorem names only the independent `Prop` predicates it actually consumes. Model–system relation: none proved (the definitions mirrored from an Aeneas prototype, described in the next paragraph, are transcribed and generalized from it; no theorem here mentions that prototype's definitions or those of the tactics named below). These are statements about the toy model; they neither establish nor refute the corresponding claims about production separation-logic verifiers and reflective normalization tactics, such as that prototype's normalizer, Iris Proof Mode, MirrorShard, or Core Lean's `ac_rfl` and `ac_nf`; the modeling-bridge lines under **Findings** argue the connection separately.

**Provenance of mirrored definitions.** `Toy.SepAC.Tree`, `Toy.SepAC.Tree.atoms`, and `Toy.SepAC.Tree.denote` (together with `listEnv`) mirror the `SepAC.Tree` representation from open, unmerged `AeneasVerif/aeneas` pull request `#1551` (`backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean`, lines 20–33 at pinned commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), generalized from concrete `IProp` and `List IProp` (`env.getD i emp`) to arbitrary `(P, sep, emp)` and `env : Nat → P`. Result `R1b` (`Toy.SepAC.acu_denote_eq_of_isPerm`) is the parametric, hypothesis-minimized form of its `SepAC.Tree.denote_eq` (lines 59–62). Because PR `#1551` is open and unmerged, it is cited as prose context only and is not listed among `REPORT.json` subjects.

**Architectural comparison with Core Lean and MirrorShard.** Core Lean `v4.34.1` (`src/Init/Data/AC.lean`) already ships a mechanized reflective AC normalizer (`Lean.Data.AC`, driving `ac_rfl` and `ac_nf` via `Init/Tactics.lean` and `Lean/Meta/Tactic/AC/Main.lean`) using unit-free syntax `Expr := var | op`, mandatory `Std.Associative`, optional `Std.Commutative` / `Std.IdempotentOp`, neutral-flagged variables (`Std.LawfulIdentity`) eliminated by `removeNeutrals`, structurally recursive insertion sort `Lean.Data.AC.sort`, and `Context.eq_of_norm`. For reflective separation-logic frame cancellation, Malecha, Chlipala & Braibant's MirrorShard (ITP 2014, `doi:10.1007/978-3-319-08970-6_24`) reifies `sexpr := Star | Opaque | Emp` with list-environment denotation `sexprD`, erases `∅` terms, and crosses common terms off both sides via `check_entailment` / `check_entailment_sound` and extensible `Apply_cancel_sound`. This package isolates the algebraic, completeness, and order-theoretic boundaries behind those designs in a single self-contained formalization.

**Known modeling gaps:**

- **Opaque atoms:** `Tree.atom i` treats everything below the `sep`/`emp` spine as an uninterpreted index `i : Nat`. Existential quantifiers (`∃ x, P x`), pure propositions (`⌜φ⌝`), persistence modalities (`□ P`), magic wands (`-∗`), and flexible metavariables sit outside `Tree` and are not modeled.
- **Reification and alias unification:** No meta-level reifier from object-logic expressions to `Tree` is formalized. Soundness assumes `Tree.denote sep emp env t` matches the target assertion, and completeness requires distinct indices (`Bag.single`) unless equal atoms are pre-merged.
- **Propositional `=` vs. `Bientails`:** Results `R1a`–`R4a` assume algebraic laws hold as Lean propositional equalities (`=`), which in real separation logics typically holds only via `propext`/`funext` over heap predicates. Result `R4b` covers intensional logics where ACU laws hold only up to `Bientails entails`.
- **Linear vs. affine logics:** Neither `AffineEntails` nor its negation is assumed globally; `R4a` and `R4b` apply to both linear and affine logics, while `R4d` exhibits separate finite countermodels for linear (`CellModel`) and affine (`TwoCellModel`) conflict behavior. These countermodels are illustrative, not minimal: two-element models already show the same failure (`Toy.SepAC.boolOr_linear_cancelAtoms_converse_fails`, `Toy.SepAC.boolAnd_affine_cancelAtoms_converse_fails`), and so does the three-state `CellModel` under the affine order `affineCellEntails` (`Toy.SepAC.cellModel_affine_cancelAtoms_converse_fails`).
- **Asymptotic cost vs. kernel reduction:** No machine cost model is formalized. Asymptotic comparisons between `Tree.atoms`, `List.isPerm`, `Lean.Data.AC.sort`, and `checkPermSort` are informal, paired with proved size bounds (`atomCount ≤ size`) and an execution observation, specific to Lean `v4.34.1` and to the probed instances, that the kernel does not reduce `List.mergeSort` or `checkPermSort` to `true` (probe `support/KernelReductionProbe.lean`).

**Toolchain and dependencies.** Built and checked under Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`). The Lake project in `lean/` declares one `[[lean_lib]]` (`Toy`), zero `[[require]]` dependencies, and no Mathlib; only Core Lean and `Std` are imported.

**Relationship among `REPORT.json` subjects.** The Lean 4 toolchain is both the verification kernel checking all 492 declarations and an examined source (`Init/Data/AC.lean`, `Init/Data/List/{Basic,Perm,Sort/*}.lean`, `Init/Tactics.lean`, `Lean/Meta/Tactic/AC/Main.lean`). The cited papers, textbooks, and pinned upstream repositories (`agda/agda-stdlib` `v2.1`, `leanprover-community/mathlib4`, and `PrincetonUniversity/VST`) are prior-art reference points documented in **Findings** and **Evidence**; this package does not re-check their source proofs. Every theorem carries `Basis: execution (Lean kernel check)`, while every cross-system claim is labeled separately as `Basis: derived (modeling bridge)`.

## Findings

### Reading conventions

- All Lean declarations live in namespace `Toy.SepAC` across modules `Algebra`, `Syntax`, `Normalization`, `FreeMonoid`, `Entailment`, `Complexity`, and `ScopeWitnesses` under `lean/Toy/SepAC/` (`ScopeWitnesses` holds the concrete witnesses that delimit claims made in the cards, and the counterexamples and non-vacuity witnesses of the supporting-theorem ledgers).
- Statement blocks for theorems are exact `#check` output from the compiled project (paired with `Unfolded:` blocks expanding key predicates). Where the default output leaves an implicit argument to be inferred from the kernel type (for example the element type of `List.append` or the carrier of `Eq`), the entry is printed with `set_option pp.analyze true`, which adds the annotations (such as `(P := List Nat)`) that make the printed type re-elaborate on its own. Recursive definitions quote the exact pattern-matching source alongside non-recursive `#print` output. Inductive types and structures are quoted with their full `#print` output, including the constructor (or field) lines. Theorems that the prose cites only by name are quoted in **Statements of theorems cited by name** at the end of **Findings**.
- Every `tight` hypothesis names a proved counterexample theorem in which all remaining hypotheses hold and the conclusion fails. Every main result has a proved non-vacuity witness; `R3b` also has a proved positive control. Where a card also relies on other Lean names that carry `Prop` hypotheses (`R1c-unit-count`, `R3b`, `R4a`, `R4b`), a **Supporting-theorem ledger** lists those hypotheses under the same rules, with a proved supporting non-vacuity witness. The one-direction theorems listed on the `-iff` cards restate one direction of the quoted equivalence; their only hypothesis is a side of that equivalence, so they have no separate ledger. No hypothesis has tightness `unknown`.
- `Basis: execution (Lean kernel check)` denotes kernel verification under `leanprover/lean4:v4.34.1`; `Basis: derived (modeling bridge)` denotes separate reasoning connecting the toy model to real verification systems. `Basis: execution (Lean v4.34.1, probe support/KernelReductionProbe.lean)` denotes a recorded run of that preserved probe program (see **Evidence** and **Revalidation**).

### Core definitions (with proved positive and negative examples)

#### `SepAssoc` (`Algebra`)

```lean
def Toy.SepAC.SepAssoc.{u} : {P : Type u} → (P → P → P) → Prop :=
fun {P} sep => ∀ (x y z : P), sep (sep x y) z = sep x (sep y z)
```

- **Meant to capture:** Associativity of separating conjunction: `(x ∗ y) ∗ z = x ∗ (y ∗ z)`.
- **Positive examples (proved):** `natAdd_sepAssoc`, `listAppend_sepAssoc`
- **Negative examples (proved):** `nonAssocOp_not_sepAssoc`

#### `SepComm` (`Algebra`)

```lean
def Toy.SepAC.SepComm.{u} : {P : Type u} → (P → P → P) → Prop :=
fun {P} sep => ∀ (x y : P), sep x y = sep y x
```

- **Meant to capture:** Commutativity of separating conjunction: `x ∗ y = y ∗ x`.
- **Positive examples (proved):** `natAdd_sepComm`, `nonAssocOp_sepComm`
- **Negative examples (proved):** `listAppend_not_sepComm`

#### `LeftUnit` (`Algebra`)

```lean
def Toy.SepAC.LeftUnit.{u} : {P : Type u} → (P → P → P) → P → Prop :=
fun {P} sep emp => ∀ (x : P), sep emp x = x
```

- **Meant to capture:** Left unit law: `emp ∗ x = x`.
- **Positive examples (proved):** `listAppend_leftUnit`, `rightProj_leftUnit`
- **Negative examples (proved):** `leftProj_not_leftUnit`, `boolAndFalse_not_leftUnit`

#### `RightUnit` (`Algebra`)

```lean
def Toy.SepAC.RightUnit.{u} : {P : Type u} → (P → P → P) → P → Prop :=
fun {P} sep emp => ∀ (x : P), sep x emp = x
```

- **Meant to capture:** Right unit law: `x ∗ emp = x` (also terminates right-nested `denoteAtoms` folds).
- **Positive examples (proved):** `listAppend_rightUnit`, `leftProj_rightUnit`
- **Negative examples (proved):** `rightProj_not_rightUnit`, `boolAndFalse_not_rightUnit`

#### `IdemElem` (`Algebra`)

```lean
def Toy.SepAC.IdemElem.{u} : {P : Type u} → (P → P → P) → P → Prop :=
fun {P} sep x => sep x x = x
```

- **Meant to capture:** Pointwise idempotence of a single element `x` under `sep`: `sep x x = x` (for example the absorbing `conflict` of `CellModel`; whether a pure or persistent assertion of a real separation logic satisfies it is a modeling question this package does not settle, see the R3b modeling bridge).
- **Positive examples (proved):** `cellModel_conflict_idemElem`, `natAdd_zero_idemElem`
- **Negative examples (proved):** `cellModel_owned_not_idemElem`

#### `SepIdem` (`Algebra`)

```lean
def Toy.SepAC.SepIdem.{u} : {P : Type u} → (P → P → P) → Prop :=
fun {P} sep => ∀ (x : P), sep x x = x
```

- **Meant to capture:** Global idempotence of `sep`: `∀ x, sep x x = x` (violated under exclusive spatial ownership).
- **Positive examples (proved):** `boolOr_sepIdem`
- **Negative examples (proved):** `natAdd_not_sepIdem`, `cellModel_not_sepIdem`

#### `NonAssocCarrier` & `NonAssocCarrier.op` (`Algebra`)

```lean
inductive Toy.SepAC.NonAssocCarrier : Type
number of parameters: 0
constructors:
Toy.SepAC.NonAssocCarrier.emp : NonAssocCarrier
Toy.SepAC.NonAssocCarrier.a : NonAssocCarrier
Toy.SepAC.NonAssocCarrier.b : NonAssocCarrier
def Toy.SepAC.NonAssocCarrier.op : NonAssocCarrier → NonAssocCarrier → NonAssocCarrier :=
fun x x_1 =>
  match x, x_1 with
  | NonAssocCarrier.emp, y => y
  | x, NonAssocCarrier.emp => x
  | NonAssocCarrier.a, NonAssocCarrier.a => NonAssocCarrier.b
  | NonAssocCarrier.b, NonAssocCarrier.b => NonAssocCarrier.b
  | NonAssocCarrier.a, NonAssocCarrier.b => NonAssocCarrier.emp
  | NonAssocCarrier.b, NonAssocCarrier.a => NonAssocCarrier.emp
```

- **Meant to capture:** Minimal 3-element carrier (`emp`, `a`, `b`) admitting a commutative, two-sided unital, non-associative binary operation (minimality proved by `atMostTwo_comm_unital_sepAssoc`).
- **Positive examples (proved):** `nonAssocOp_pos_example`
- **Negative examples (proved):** `nonAssocOp_neg_example`

#### `leftProj` & `rightProj` (`Algebra`)

```lean
def Toy.SepAC.leftProj.{u} : {P : Type u} → P → P → P :=
fun {P} x x_1 => x
def Toy.SepAC.rightProj.{u} : {P : Type u} → P → P → P :=
fun {P} x y => y
```

- **Meant to capture:** Asymmetric projection operators (`fun x _ => x` and `fun _ y => y`) separating `LeftUnit` from `RightUnit` under `SepAssoc`.
- **Positive examples (proved):** `leftProj_pos_example`, `rightProj_pos_example`
- **Negative examples (proved):** `leftProj_neg_example`, `rightProj_neg_example`

#### `CellModel` & `CellModel.sep` (`Algebra`)

```lean
inductive Toy.SepAC.CellModel : Type
number of parameters: 0
constructors:
Toy.SepAC.CellModel.conflict : CellModel
Toy.SepAC.CellModel.empty : CellModel
Toy.SepAC.CellModel.owned : CellModel
def Toy.SepAC.CellModel.sep : CellModel → CellModel → CellModel :=
fun x x_1 =>
  match x, x_1 with
  | CellModel.empty, y => y
  | x, CellModel.empty => x
  | CellModel.owned, CellModel.owned => CellModel.conflict
  | CellModel.conflict, x => CellModel.conflict
  | x, CellModel.conflict => CellModel.conflict
```

- **Meant to capture:** Three-state single-cell disjoint heap assertion algebra (`conflict`, `empty`, `owned`) with `owned ∗ owned = conflict` and absorbing `conflict`.
- **Positive examples (proved):** `cellModel_pos_example`
- **Negative examples (proved):** `cellModel_neg_example`

#### `TwoCellModel` & `TwoCellModel.sep` (`Algebra`)

```lean
inductive Toy.SepAC.TwoCellModel : Type
number of parameters: 0
constructors:
Toy.SepAC.TwoCellModel.conflict : TwoCellModel
Toy.SepAC.TwoCellModel.empty : TwoCellModel
Toy.SepAC.TwoCellModel.cellA : TwoCellModel
Toy.SepAC.TwoCellModel.cellB : TwoCellModel
Toy.SepAC.TwoCellModel.both : TwoCellModel
def Toy.SepAC.TwoCellModel.sep : TwoCellModel → TwoCellModel → TwoCellModel :=
fun x x_1 =>
  match x, x_1 with
  | TwoCellModel.empty, y => y
  | x, TwoCellModel.empty => x
  | TwoCellModel.cellA, TwoCellModel.cellB => TwoCellModel.both
  | TwoCellModel.cellB, TwoCellModel.cellA => TwoCellModel.both
  | x, x_2 => TwoCellModel.conflict
```

- **Meant to capture:** Five-state two-cell disjoint heap assertion algebra (`conflict`, `empty`, `cellA`, `cellB`, `both`) capturing multi-location separation.
- **Positive examples (proved):** `twoCellModel_pos_example`
- **Negative examples (proved):** `twoCellModel_neg_example`

#### `Tree` (`Syntax`)

```lean
inductive Toy.SepAC.Tree : Type
number of parameters: 0
constructors:
Toy.SepAC.Tree.atom : Nat → Tree
Toy.SepAC.Tree.unit : Tree
Toy.SepAC.Tree.node : Tree → Tree → Tree
```

- **Meant to capture:** Reified syntax tree of a separating-conjunction spine (`atom i | unit | node l r`), mirroring the prototype's `SepAC.Tree` (`AeneasVerif/aeneas#1551`, `Normalize.lean` lines 20–23) parameterized over `(P, sep, emp)`.
- **Positive examples (proved):** `denote_pos_example`, `atoms_pos_example`
- **Negative examples (proved):** `denote_neg_example`, `atoms_neg_example`

#### `Tree.unitFree` (`Syntax`)

```lean
def Tree.unitFree : Tree → Bool
  | .atom _ => true
  | .unit => false
  | .node l r => l.unitFree && r.unitFree
```

- **Meant to capture:** Boolean test checking whether `t` contains no `Tree.unit` leaves.
- **Positive examples (proved):** `unitFree_pos_example`
- **Negative examples (proved):** `unitFree_neg_example`

#### `Tree.unitCount` (`Syntax`)

```lean
def Tree.unitCount : Tree → Nat
  | .atom _ => 0
  | .unit => 1
  | .node l r => l.unitCount + r.unitCount
```

- **Meant to capture:** Count of `Tree.unit` leaves in `t`. Together with `l.atoms.isPerm r.atoms = true`, `l.unitCount = r.unitCount` suffices for equal denotations in every AC model (`SepAssoc` + `SepComm`, no unit law), and holds necessarily when quantified over all `Type`-level AC models, `emp`, and environments (not in a single fixed model where `emp` happens to be a unit).
- **Positive examples (proved):** `unitCount_pos_example`
- **Negative examples (proved):** `unitCount_neg_example`

#### `Tree.denote` & `listEnv` (`Syntax`)

```lean
def Tree.denote {P : Type u} (sep : P → P → P) (emp : P) (env : Nat → P) : Tree → P
  | .atom i => env i
  | .unit => emp
  | .node l r => sep (l.denote sep emp env) (r.denote sep emp env)

def Toy.SepAC.listEnv.{u} : {P : Type u} → P → List P → Nat → P :=
fun {P} emp xs i => xs.getD i emp
```

- **Meant to capture:** Recursive semantic evaluation of `Tree` against a total environment `env : Nat → P`, plus list-backed adapter `listEnv emp xs := fun i => xs.getD i emp`.
- **Positive examples (proved):** `denote_pos_example`, `listEnv_pos_example`
- **Negative examples (proved):** `denote_neg_example`, `listEnv_neg_example`

#### `Tree.atoms`, `denoteAtoms`, & `denoteNonEmpty` (`Syntax`)

```lean
def Tree.atoms : Tree → List Nat
  | .atom i => [i]
  | .unit => []
  | .node l r => l.atoms ++ r.atoms

def Toy.SepAC.denoteAtoms.{u} : {P : Type u} → (P → P → P) → P → (Nat → P) → List Nat → P :=
fun {P} sep emp env is => List.foldr (fun i acc => sep (env i) acc) emp is

def denoteNonEmpty {P : Type u} (sep : P → P → P) (env : Nat → P) : Nat → List Nat → P
  | head, [] => env head
  | head, next :: rest => sep (env head) (denoteNonEmpty sep env next rest)
```

- **Meant to capture:** Left-to-right atom-index extraction erasing `Tree.unit`, right-nested fold with trailing `emp` (`denoteAtoms`), and unit-free non-empty fold (`denoteNonEmpty`).
- **Positive examples (proved):** `atoms_pos_example`, `denoteAtoms_pos_example`, `denoteNonEmpty_pos_example`
- **Negative examples (proved):** `atoms_neg_example`, `denoteAtoms_neg_example`, `denoteNonEmpty_neg_example`

#### `FiniteSupport`, `Bag`, `Bag.emp`, `Bag.single`, & `Bag.sep` (`FreeMonoid`)

```lean
def Toy.SepAC.FiniteSupport : (Nat → Nat) → Prop :=
fun f => ∃ bound, ∀ (i : Nat), bound ≤ i → f i = 0
structure Toy.SepAC.Bag : Type
number of parameters: 0
fields:
  Toy.SepAC.Bag.count : Nat → Nat
  Toy.SepAC.Bag.finite : FiniteSupport self.count
constructor:
  Toy.SepAC.Bag.mk (count : Nat → Nat) (finite : FiniteSupport count) : Bag
def Toy.SepAC.Bag.emp : Bag :=
{ count := fun x => 0, finite := finiteSupport_zero }
def Toy.SepAC.Bag.single : Nat → Bag :=
fun k => { count := fun i => if (i == k) = true then 1 else 0, finite := ⋯ }
def Toy.SepAC.Bag.sep : Bag → Bag → Bag :=
fun b₁ b₂ => { count := fun i => b₁.count i + b₂.count i, finite := ⋯ }
```

- **Meant to capture:** Finitely supported multiplicity maps `Nat → Nat` forming the free commutative monoid of finite multisets over atom indices under pointwise addition (`Bag.sep`).
- **Positive examples (proved):** `finiteSupport_zero`, `bag_pos_example`
- **Negative examples (proved):** `not_finiteSupport_const_one`, `bag_neg_example`

#### `dupAtomTree` & `singleAtomTree` (`FreeMonoid`)

```lean
def Toy.SepAC.dupAtomTree : Tree :=
(Tree.atom 0).node (Tree.atom 0)
def Toy.SepAC.singleAtomTree : Tree :=
Tree.atom 0
```

- **Meant to capture:** Canonical witness pair `atom 0 ∗ atom 0` vs. `atom 0` for testing idempotent-element completeness breakdown.
- **Positive examples (proved):** `denote_eq_and_isPerm_false_of_idemElem`
- **Negative examples (proved):** `bag_dupAtomTree_denote_ne_singleAtomTree`

#### `EntailsRefl`, `EntailsTrans`, `SepMonoRight`, `SepMonoLeft`, & `AffineEntails` (`Entailment`)

```lean
def Toy.SepAC.EntailsRefl.{u} : {P : Type u} → (P → P → Prop) → Prop :=
fun {P} entails => ∀ (x : P), entails x x
def Toy.SepAC.EntailsTrans.{u} : {P : Type u} → (P → P → Prop) → Prop :=
fun {P} entails => ∀ (x y z : P), entails x y → entails y z → entails x z
def Toy.SepAC.SepMonoRight.{u} : {P : Type u} → (P → P → P) → (P → P → Prop) → Prop :=
fun {P} sep entails => ∀ (f x y : P), entails x y → entails (sep f x) (sep f y)
def Toy.SepAC.SepMonoLeft.{u} : {P : Type u} → (P → P → P) → (P → P → Prop) → Prop :=
fun {P} sep entails => ∀ (x y f : P), entails x y → entails (sep x f) (sep y f)
def Toy.SepAC.AffineEntails.{u} : {P : Type u} → P → (P → P → Prop) → Prop :=
fun {P} emp entails => ∀ (x : P), entails x emp
```

- **Meant to capture:** Unbundled order, one-sided/two-sided framing monotonicity, and affinity (`x ⊢ emp`) predicates on `entails : P → P → Prop`.
- **Positive examples (proved):** `natLe_entailsRefl`, `natLe_entailsTrans`, `natAdd_le_sepMonoRight`, `natAdd_le_sepMonoLeft`, `twoCellModel_affineEntails`
- **Negative examples (proved):** `natLt_not_entailsRefl`, `tagDistLeOne_not_entailsTrans`, `capOne_not_sepMonoRight`, `parityBiasOp_monoRight_and_not_monoLeft`, `cellModel_not_affineEntails`

#### `Bientails`, `SepAssocBientails`, `SepCommBientails`, `RightUnitBientails`, & `LeftUnitBientails` (`Entailment`)

```lean
def Toy.SepAC.Bientails.{u} : {P : Type u} → (P → P → Prop) → P → P → Prop :=
fun {P} entails x y => entails x y ∧ entails y x
def Toy.SepAC.SepAssocBientails.{u} : {P : Type u} → (P → P → P) → (P → P → Prop) → Prop :=
fun {P} sep entails => ∀ (x y z : P), Bientails entails (sep (sep x y) z) (sep x (sep y z))
def Toy.SepAC.SepCommBientails.{u} : {P : Type u} → (P → P → P) → (P → P → Prop) → Prop :=
fun {P} sep entails => ∀ (x y : P), Bientails entails (sep x y) (sep y x)
def Toy.SepAC.RightUnitBientails.{u} : {P : Type u} → (P → P → P) → P → (P → P → Prop) → Prop :=
fun {P} sep emp entails => ∀ (x : P), Bientails entails (sep x emp) x
def Toy.SepAC.LeftUnitBientails.{u} : {P : Type u} → (P → P → P) → P → (P → P → Prop) → Prop :=
fun {P} sep emp entails => ∀ (x : P), Bientails entails (sep emp x) x
```

- **Meant to capture:** Mutual entailment (`x ⊣⊢ y`), defined as the intersection `entails x y ∧ entails y x` of `entails` with its converse (not the symmetric closure/union; forms an equivalence relation when `entails` is a preorder), plus ACU laws up to `Bientails`.
- **Positive examples (proved):** `bientails_pos_example`, `taggedSep_assocBientails_valLe`, `taggedSep_commBientails_valLe`, `taggedSep_rightUnitBientails_valLe`, `leftUnitBientails_pos_example`
- **Negative examples (proved):** `bientails_neg_example`, `nonAssoc_not_assocBientails_eq`, `listAppend_not_commBientails_eq`, `boolAndFalse_not_rightUnitBientails_eq`, `leftUnitBientails_neg_example`

#### `cancelAtoms` (`Entailment`)

```lean
def cancelAtoms : List Nat → List Nat → List Nat × List Nat
  | [], ys => ([], ys)
  | x :: xs, ys =>
    if ys.contains x then
      cancelAtoms xs (ys.erase x)
    else
      let (xs', ys') := cancelAtoms xs ys
      (x :: xs', ys')
```

- **Meant to capture:** Greedy left-to-right multiset cancellation computing the exact multiset differences `(leftover_xs, leftover_ys)` (`cancelAtoms_spec`, `cancelAtoms_count`, `cancelAtoms_disjoint`). In `cancelAtoms_count` the leftover multiplicity of an atom `a` is `List.count a xs - List.count a ys` (resp. `List.count a ys - List.count a xs`) with truncated `Nat` subtraction: it is `0` whenever the other list has at least as many copies of `a`, which is what makes the leftovers the multiset differences.
- **Positive examples (proved):** `cancelAtoms_pos_example`
- **Negative examples (proved):** `cancelAtoms_neg_example`

#### Countermodel relations (`Entailment`)

```lean
def Toy.SepAC.capOneScore : Nat → Nat :=
fun x =>
  match x with
  | 0 => 0
  | 1 => 1
  | n.succ.succ => 0
def Toy.SepAC.capOneEntails : Nat → Nat → Prop :=
fun x y => capOneScore x ≤ capOneScore y
def Toy.SepAC.parityBiasOp : Nat → Nat → Nat :=
fun x y => 2 * (x % 2) + y
@[reducible] def Toy.SepAC.TaggedNat : Type :=
Nat × Nat
def Toy.SepAC.taggedEmp : TaggedNat :=
(0, 0)
def Toy.SepAC.taggedSep : TaggedNat → TaggedNat → TaggedNat :=
fun x y => (x.fst + y.fst, max x.snd y.snd + 1)
def Toy.SepAC.tagDistLeOne : TaggedNat → TaggedNat → Prop :=
fun x y => x.fst = y.fst ∧ x.snd ≤ y.snd + 1 ∧ y.snd ≤ x.snd + 1
def Toy.SepAC.taggedValLe : TaggedNat → TaggedNat → Prop :=
fun x y => x.fst ≤ y.fst
def Toy.SepAC.CellModel.entails : CellModel → CellModel → Prop :=
fun x x_1 =>
  match x, x_1 with
  | CellModel.conflict, x => True
  | CellModel.empty, CellModel.empty => True
  | CellModel.owned, CellModel.owned => True
  | x, x_2 => False
def Toy.SepAC.affineCellEntails : CellModel → CellModel → Prop :=
fun x x_1 =>
  match x, x_1 with
  | CellModel.conflict, x => True
  | x, CellModel.empty => True
  | CellModel.owned, CellModel.owned => True
  | x, x_2 => False
def Toy.SepAC.TwoCellModel.entailsBool : TwoCellModel → TwoCellModel → Bool :=
fun x x_1 =>
  match x, x_1 with
  | TwoCellModel.conflict, x => true
  | x, TwoCellModel.empty => true
  | TwoCellModel.cellA, TwoCellModel.cellA => true
  | TwoCellModel.cellB, TwoCellModel.cellB => true
  | TwoCellModel.both, TwoCellModel.cellA => true
  | TwoCellModel.both, TwoCellModel.cellB => true
  | TwoCellModel.both, TwoCellModel.both => true
  | x, x_2 => false
def Toy.SepAC.TwoCellModel.entails : TwoCellModel → TwoCellModel → Prop :=
fun x y => x.entailsBool y = true
```

- **Meant to capture:** Concrete relations isolating monotonicity (`capOneEntails`), left/right bias (`parityBiasOp`), non-transitive proximity (`tagDistLeOne`) vs. setoid preorder (`taggedValLe`), non-affine (linear-logic) order (`CellModel.entails`), and affine orders (`affineCellEntails`, `TwoCellModel.entails`).
- **Positive examples (proved):** `cellModel_entailsRefl`, `affineCellEntails_pos_example`, `twoCellModel_entails_pos_example`
- **Negative examples (proved):** `capOne_not_sepMonoRight`, `tagDistLeOne_not_entailsTrans`, `affineCellEntails_neg_example`, `twoCellModel_entails_neg_example`

#### `Tree.size`, `Tree.atomCount`, `Tree.atomsAcc`, `Tree.atomsFast`, `checkPermSort`, & `decideTreePerm` (`Complexity`)

```lean
def Tree.size : Tree → Nat
  | .atom _ => 1
  | .unit => 1
  | .node l r => 1 + l.size + r.size

def Tree.atomCount : Tree → Nat
  | .atom _ => 1
  | .unit => 0
  | .node l r => l.atomCount + r.atomCount

def Tree.atomsAcc : Tree → List Nat → List Nat
  | .atom i, acc => i :: acc
  | .unit, acc => acc
  | .node l r, acc => l.atomsAcc (r.atomsAcc acc)

def Toy.SepAC.Tree.atomsFast : Tree → List Nat :=
fun t => t.atomsAcc []

def Toy.SepAC.checkPermSort : Tree → Tree → Bool :=
fun l r => (l.atomsFast.mergeSort fun x1 x2 => decide (x1 ≤ x2)) == r.atomsFast.mergeSort fun x1 x2 => decide (x1 ≤ x2)

def Toy.SepAC.decideTreePerm : (l r : Tree) → Decidable (l.atoms.Perm r.atoms) :=
fun l r => decidable_of_iff (checkPermSort l r = true) ⋯
```

- **Meant to capture:** Linear-traversal accumulator atom extraction and `List.mergeSort`-based permutation decision procedure (`checkPermSort`), plus tree size/atom counts.
- **Positive examples (proved):** `treeSize_pos_example`, `atomCount_pos_example`, `atomsAcc_pos_example`, `atomsFast_pos_example`, `checkPermSort_pos_example`
- **Negative examples (proved):** `treeSize_neg_example`, `atomCount_neg_example`, `atomsAcc_neg_example`, `atomsFast_neg_example`, `checkPermSort_neg_example`

#### `boolImp` & `optBagSep` (`ScopeWitnesses`)

```lean
def Toy.SepAC.boolImp : Bool → Bool → Prop :=
fun x y => x = true → y = true
def Toy.SepAC.optBagSep : Option Bag → Option Bag → Option Bag :=
fun x x_1 =>
  match x, x_1 with
  | some a, some b => some (a.sep b)
  | x, x_2 => none
```

- **Meant to capture:** Auxiliary definitions used only by scope witnesses. `boolImp` is the implication order on `Bool`, used for the two-element countermodels showing that the `R4d` cell models are not minimal. `optBagSep` adjoins an absorbing element `none` to `Bag`, used to show that an absorbing element does not by itself break `List.isPerm` completeness for every environment (`R3b`).
- **Positive examples (proved):** `boolImp_pos_example` (`false` entails `true`); `optBag_denote` (under `fun i => some (Bag.single i)`, every tree denotes `some` of its `Bag` denotation).
- **Negative examples (proved):** `boolImp_neg_example` (`true` does not entail `false`); the second conjunct of `optBag_absorbing_but_complete` (`some (Bag.single 0)` is not idempotent under `optBagSep`).

### Proved derived-law, structural, and auxiliary scope lemmas

```lean
@leftUnit_of_comm_of_rightUnit : ∀ {P : Type u_1} {sep : P → P → P} {emp : P},
  SepComm sep → RightUnit sep emp → LeftUnit sep emp
@rightUnit_of_comm_of_leftUnit : ∀ {P : Type u_1} {sep : P → P → P} {emp : P},
  SepComm sep → LeftUnit sep emp → RightUnit sep emp
bool_comm_unital_sepAssoc : ∀ (op : Bool → Bool → Bool) (e : Bool), SepComm op → RightUnit op e → SepAssoc op
Tree.unitFree_iff_unitCount_eq_zero : ∀ (t : Tree), t.unitFree = true ↔ t.unitCount = 0
@denoteAtoms_append : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  SepAssoc sep →
    LeftUnit sep emp →
      ∀ (env : Nat → P) (xs ys : List Nat),
        denoteAtoms sep emp env (xs ++ ys) = sep (denoteAtoms sep emp env xs) (denoteAtoms sep emp env ys)
@denoteAtoms_perm : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  SepAssoc sep →
    SepComm sep →
      ∀ (env : Nat → P) {xs ys : List Nat}, xs.Perm ys → denoteAtoms sep emp env xs = denoteAtoms sep emp env ys
bag_sepAssoc : SepAssoc Bag.sep
bag_sepComm : SepComm Bag.sep
bag_rightUnit : RightUnit Bag.sep Bag.emp
bag_not_sepIdem : ¬SepIdem Bag.sep
bag_single_zero_not_idemElem : ¬IdemElem Bag.sep (Bag.single 0)
bag_count_denote : ∀ (t : Tree) (k : Nat), (Tree.denote Bag.sep Bag.emp Bag.single t).count k = List.count k t.atoms
bag_aliased_env_denote_eq_not_isPerm : have env := fun x => Bag.single 0;
have l := Tree.atom 0;
have r := Tree.atom 1;
Tree.denote Bag.sep Bag.emp env l = Tree.denote Bag.sep Bag.emp env r ∧ l.atoms.isPerm r.atoms = false
bag_listEnv_oob_denote_eq_not_isPerm : have env := listEnv Bag.emp [];
have l := Tree.atom 0;
have r := Tree.unit;
Tree.denote Bag.sep Bag.emp env l = Tree.denote Bag.sep Bag.emp env r ∧ l.atoms.isPerm r.atoms = false
boolOr_setCheck_incomplete : SepAssoc or ∧
  SepComm or ∧
    RightUnit or false ∧
      SepIdem or ∧
        have env := fun i => i == 0;
        have l := (Tree.atom 0).node (Tree.atom 1);
        have r := Tree.atom 0;
        Tree.denote or false env l = Tree.denote or false env r ∧ l.atoms.eraseDups.isPerm r.atoms.eraseDups = false
@sepMonoLeft_of_comm_of_monoRight : ∀ {P : Type u_1} {sep : P → P → P} {entails : P → P → Prop},
  SepComm sep → SepMonoRight sep entails → SepMonoLeft sep entails
parityBiasOp_monoRight_and_not_monoLeft : SepMonoRight parityBiasOp Nat.le ∧ ¬SepMonoLeft parityBiasOp Nat.le
@entailsRefl_of_trans_of_rightUnitBientails : ∀ {P : Type u_1} {sep : P → P → P} {emp : P} {entails : P → P → Prop},
  EntailsTrans entails → RightUnitBientails sep emp entails → EntailsRefl entails
@sepMonoLeft_of_trans_of_commBientails_of_monoRight : ∀ {P : Type u_1} {sep : P → P → P} {entails : P → P → Prop},
  EntailsTrans entails → SepCommBientails sep entails → SepMonoRight sep entails → SepMonoLeft sep entails
@leftUnitBientails_of_trans_of_commBientails_of_rightUnitBientails : ∀ {P : Type u_1} {sep : P → P → P} {emp : P}
  {entails : P → P → Prop},
  EntailsTrans entails →
    SepCommBientails sep entails → RightUnitBientails sep emp entails → LeftUnitBientails sep emp entails
totalRelation_cancel_sound_without_laws : ¬SepAssoc NonAssocCarrier.op ∧
  ∀ (env : Nat → NonAssocCarrier) (l r : Tree),
    (fun x x_1 => True) (Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env l)
      (Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env r)
atomsAcc_eq_atoms_append : ∀ (t : Tree) (acc : List Nat), t.atomsAcc acc = t.atoms ++ acc
atomsFast_eq_atoms : ∀ (t : Tree), t.atomsFast = t.atoms
atoms_length_eq_atomCount : ∀ (t : Tree), t.atoms.length = t.atomCount
atomCount_le_size : ∀ (t : Tree), t.atomCount ≤ t.size
mergeSort_beq_eq_isPerm : ∀ (xs ys : List Nat),
  ((xs.mergeSort fun x1 x2 => decide (x1 ≤ x2)) == ys.mergeSort fun x1 x2 => decide (x1 ≤ x2)) = xs.isPerm ys
```

### Result cards

#### R1a (`R1a-monoid-flattening-normal-form`)

- **Kind:** `theorem` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Normalization.lean`
- **Lean:** `Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units`
- **Plain claim:** For any binary operation `sep` and element `emp` satisfying `SepAssoc sep`, `LeftUnit sep emp`, and `RightUnit sep emp` (commutativity not assumed), every syntax tree `t` has the same denotation in environment `env` as the right-nested list fold `denoteAtoms sep emp env t.atoms`.

```lean
@denote_eq_denoteAtoms_of_assoc_units : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  SepAssoc sep →
    LeftUnit sep emp →
      RightUnit sep emp → ∀ (env : Nat → P) (t : Tree), Tree.denote sep emp env t = denoteAtoms sep emp env t.atoms
```

Unfolded (prose):

```text
(∀ x y z : P, sep (sep x y) z = sep x (sep y z)) →
(∀ x : P, sep emp x = x) →
(∀ x : P, sep x emp = x) →
∀ (env : Nat → P) (t : Tree),
  t.denote sep emp env = t.atoms.foldr (fun i acc => sep (env i) acc) emp
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hAssoc : SepAssoc sep` | Distributes `denoteAtoms` across `l.atoms ++ r.atoms` at binary `Tree.node` constructors. | `tight` | `Toy.SepAC.nonAssoc_tight_flattening_sepAssoc` |
| `hLeftUnit : LeftUnit sep emp` | Eliminates empty left subtrees (`Tree.unit` on the left of `Tree.node`, base case of `++` induction). | `tight` | `Toy.SepAC.leftProj_tight_flattening_leftUnit` |
| `hRightUnit : RightUnit sep emp` | Removes the trailing `emp` factor introduced by `foldr` at `Tree.atom` leaves (`sep (env i) emp = env i`). | `tight` | `Toy.SepAC.rightProj_tight_flattening_rightUnit` |
| `P : Type u (arbitrary universe)` | No decidability, finiteness, or commutativity of the carrier is assumed. | `harmless` | — |

- **Depth (`shallow`):** Induction on `t : Tree`, with list-append induction for `denoteAtoms_append`.
- **Non-vacuity witness:** List concatenation on `List Nat` with unit `[]` satisfies `SepAssoc`, `LeftUnit`, and `RightUnit` while violating `SepComm`. (Lean: `Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units_nonvacuous`)
- **Tier justification (`T0`):** Standard reflective monoid-normalization lemma (Boutin 1997; Chlipala 2013 Chapter 15; core Lean `Lean.Data.AC.Context.eval_toList`; Braibant & Pous 2011; AeneasVerif/aeneas#1551 `Tree.denote_eq_foldr`), restated parametrically over unbundled `SepAssoc`, `LeftUnit`, and `RightUnit` without commutativity.
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean`: `Lean.Data.AC.Context.eval_toList` (lines 330-335) flattens unit-free associative syntax trees using `Associative` alone, and `removeNeutrals` (lines 95-106) eliminates `LawfulIdentity`-flagged atoms.
  - Boutin, S., 'Using reflection to build efficient and certified decision procedures', TACS 1997, LNCS 1281, pp. 515-529, doi:10.1007/BFb0014565. Establishes proof by reflection in type theory.
  - Chlipala, A., Certified Programming with Dependent Types, MIT Press, 2013, ISBN 9780262026659, Chapter 15 ('Proof by Reflection', section 'A Monoid Expression Simplifier'). Flattens monoid expressions into lists using `assoc`, `identl`, and `identr` into a right-nested fold with trailing identity.
  - Braibant, T. & Pous, D., 'Tactics for Reasoning Modulo AC in Coq', CPP 2011, LNCS 7086, pp. 167-182, doi:10.1007/978-3-642-25379-9_14. Mechanizes associative-only and neutral-element reflection.
  - Repository `AeneasVerif/aeneas`, open unmerged PR #1551 ('Separation logic over the byte heap', base `cezar/sl-extraction`, head `cezar/seplogic`, pinned commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean`, `Aeneas.SepLogic.SepAC.Tree.denote_eq_foldr` (lines 51-57): relates tree evaluation to a right-nested fold of looked-up atoms over concrete `IProp`.
- **Design question:** Which exact algebraic laws are consumed by flattening and `emp`-unit elimination into a right-nested list fold, prior to any commutative reordering?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Relates tree flattening and `emp`-elimination in an arbitrary monoid-like separation logic to right-nested folds (`denoteAtoms`) without needing commutativity; applies to a concrete logic only once `SepAssoc`, `LeftUnit`, and `RightUnit` are established propositionally and goal reification produces `Tree` with `Tree.denote = goal`.

#### R1a-iff (`R1a-iff-monoid-flattening-characterization`)

- **Kind:** `characterization` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Normalization.lean`
- **Lean:** `Toy.SepAC.denote_eq_denoteAtoms_iff_assoc_units`, `Toy.SepAC.assoc_units_of_denote_eq_denoteAtoms`
- **Plain claim:** For a fixed carrier `P`, binary operation `sep`, and element `emp`, flattening `t.denote sep emp env = denoteAtoms sep emp env t.atoms` holds for all environments `env` and syntax trees `t` if and only if `SepAssoc sep`, `LeftUnit sep emp`, and `RightUnit sep emp` all hold.

```lean
@denote_eq_denoteAtoms_iff_assoc_units : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  (∀ (env : Nat → P) (t : Tree), Tree.denote sep emp env t = denoteAtoms sep emp env t.atoms) ↔
    SepAssoc sep ∧ LeftUnit sep emp ∧ RightUnit sep emp

@assoc_units_of_denote_eq_denoteAtoms : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  (∀ (env : Nat → P) (t : Tree), Tree.denote sep emp env t = denoteAtoms sep emp env t.atoms) →
    SepAssoc sep ∧ LeftUnit sep emp ∧ RightUnit sep emp
```

Unfolded (prose):

```text
(∀ (env : Nat → P) (t : Tree),
    t.denote sep emp env = t.atoms.foldr (fun i acc => sep (env i) acc) emp) ↔
  (∀ x y z : P, sep (sep x y) z = sep x (sep y z)) ∧
  (∀ x : P, sep emp x = x) ∧
  (∀ x : P, sep x emp = x)
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`shallow`):** Forward direction instantiates three fixed trees and environments; backward direction invokes `R1a`.
- **Non-vacuity witness:** List concatenation on `List Nat` with unit `[]` satisfies the right-hand side (`SepAssoc`, `LeftUnit`, `RightUnit`) while violating `SepComm`. (Lean: `Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units_nonvacuous`)
- **Tier justification (`T0`):** Elementary equational adequacy pairing T0 monoid flattening (`denote_eq_denoteAtoms_of_assoc_units`) with the fully proved three-tree converse (`assoc_units_of_denote_eq_denoteAtoms`).
- **Prior art:**
  - Chlipala, A., Certified Programming with Dependent Types, MIT Press, 2013, ISBN 9780262026659, Chapter 15 ('Proof by Reflection').
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean` (`Context.eval_toList`).
- **Design question:** Are `SepAssoc`, `LeftUnit`, and `RightUnit` jointly necessary as well as sufficient for universal monoid-flattening soundness over `(sep, emp)`?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Establishes that any sound universal flattening-and-unit-elimination lemma to `denoteAtoms` for a concrete `(P, sep, emp)` must rest on `SepAssoc`, `LeftUnit`, and `RightUnit`; a concrete tactic restricted to a narrower tree fragment might avoid one of those laws on that fragment.

#### R1b (`R1b-acu-permutation-soundness`)

- **Kind:** `theorem` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Normalization.lean`
- **Lean:** `Toy.SepAC.acu_denote_eq_of_isPerm`
- **Plain claim:** For any binary operation `sep` and element `emp` satisfying `SepAssoc sep`, `SepComm sep`, and `RightUnit sep emp`, if core Lean's boolean check `l.atoms.isPerm r.atoms = true` succeeds, then `l.denote sep emp env = r.denote sep emp env` in every environment `env : Nat → P` (including finite list-backed environments via `listEnv`).

```lean
@acu_denote_eq_of_isPerm : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  SepAssoc sep →
    SepComm sep →
      RightUnit sep emp →
        ∀ (env : Nat → P) {l r : Tree},
          l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r
```

Unfolded (prose):

```text
(∀ x y z : P, sep (sep x y) z = sep x (sep y z)) →
(∀ x y : P, sep x y = sep y x) →
(∀ x : P, sep x emp = x) →
∀ (env : Nat → P) {l r : Tree},
  l.atoms.isPerm r.atoms = true → l.denote sep emp env = r.denote sep emp env
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hAssoc : SepAssoc sep` | Re-associates binary `Tree.node` spines and enables adjacent-element swaps inside right-nested folds. | `tight` | `Toy.SepAC.nonAssoc_tight_isPerm_sepAssoc` |
| `hComm : SepComm sep` | Permutes atom order and derives `LeftUnit sep emp` from `RightUnit sep emp` (`Toy.SepAC.leftUnit_of_comm_of_rightUnit`). | `tight` | `Toy.SepAC.listAppend_tight_isPerm_sepComm` |
| `hRightUnit : RightUnit sep emp` | Makes `Tree.unit` denote a genuine identity of `sep` so erasing `Tree.unit` from `Tree.atoms` preserves denotation. | `tight` | `Toy.SepAC.boolAndFalse_tight_isPerm_rightUnit` |
| `hPerm : l.atoms.isPerm r.atoms = true` | Decidable syntactic side condition ensuring `l` and `r` contain the same multiset of atom indices. | `tight` | `Toy.SepAC.boolAndTrue_tight_isPerm_perm` |

- **Depth (`shallow`):** Flattens both trees via `R1a` (with `LeftUnit` derived from `SepComm` + `RightUnit`) and inducts on `List.Perm`.
- **Non-vacuity witness:** The 3-state disjoint single-cell heap assertion algebra `CellModel` satisfies `SepAssoc`, `SepComm`, and `RightUnit`, and distinct trees `((atom 0 ∗ unit) ∗ atom 1)` and `(atom 1 ∗ atom 0)` satisfy `l.atoms.isPerm r.atoms = true`. (Lean: `Toy.SepAC.acu_denote_eq_of_isPerm_nonvacuous`)
- **Tier justification (`T0`):** Parametric restatement of the reflective ACU equality kernel (Boutin 1997; Braibant & Pous 2011; Agda stdlib `Algebra.Solver.CommutativeMonoid`; Lean 4 core `Lean.Data.AC.Context.eq_of_norm`; AeneasVerif/aeneas#1551 `SepAC.Tree.denote_eq`) with irredundant unbundled hypotheses (`LeftUnit` dropped via `Toy.SepAC.leftUnit_of_comm_of_rightUnit`).
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean` (`Lean.Data.AC.Context.eq_of_norm`, line 342) and `src/Lean/Meta/Tactic/AC/Main.lean` (`ac_rfl` / `ac_nf`, building `Context.eq_of_norm ... (mkEqRefl Bool.true)` at line 128). The pinned prototype's `IProp` already registers `Std.Associative sep`, `Std.Commutative sep`, and `Std.LawfulIdentity sep emp` (`Lemmas.lean`, lines 105, 108, 138), so `ac_rfl` applies directly.
  - Braibant, T. & Pous, D., 'Tactics for Reasoning Modulo AC in Coq', CPP 2011, LNCS 7086, pp. 167-182, doi:10.1007/978-3-642-25379-9_14. Mechanizes reflexive AC decision procedures with neutral elements, associative-only operators, and user-defined setoid equivalences.
  - Agda standard library (`agda/agda-stdlib` v2.1, commit `97bc55e47367c562b3032bf104f2a00b19716f88`), `src/Algebra/Solver/CommutativeMonoid.agda`: reflective solver for commutative monoids with a unit constructor `id` and bag normal forms (`Vec ℕ n`) over a setoid.
  - Boutin, S., 'Using reflection to build efficient and certified decision procedures', TACS 1997, LNCS 1281, pp. 515-529, doi:10.1007/BFb0014565.
  - Gregoire, B. & Mahboubi, A., 'Proving Equalities in a Commutative Ring Done Right in Coq', TPHOLs 2005, LNCS 3603, pp. 98-113, doi:10.1007/11541868_7. Establishes reflective canonical-form normalization with kernel reduction of decidable side conditions (including over setoids).
  - Repository `AeneasVerif/aeneas`, open unmerged PR #1551 (base `cezar/sl-extraction`, head `cezar/seplogic`, pinned commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean`, `Aeneas.SepLogic.SepAC.Tree.denote_eq` (lines 59-62): specialized to `IProp` and `List.getD`, rewrites both sides to right-nested folds of the looked-up atoms and closes by permutation invariance of the fold.
  - Malecha, G., Chlipala, A. & Braibant, T., 'Compositional Computational Reflection', ITP 2014, LNCS 8558, pp. 374-389, doi:10.1007/978-3-319-08970-6_24: MirrorShard's reflective entailment checker (Listing 1) reifies propositional separation logic into `sexpr := Star | Opaque | Emp` with list-environment denotation `sexprD`, erases `Emp` terms and crosses common terms off both sides in `check_entailment`, and proves `check_entailment_sound` (plus extensible `Apply_cancel_sound` for Bedrock) discharged by reflexivity.
  - Krebbers, R., Timany, A. & Birkedal, L., 'Interactive proofs in higher-order concurrent separation logic', POPL 2017, pp. 205-217, doi:10.1145/3009837.3009855: manipulates list-based persistent and spatial assertion contexts reflectively in Iris Proof Mode.
- **Design question:** Which minimal, irredundant set of algebraic laws makes a `List.isPerm`-based reflective equality kernel sound over arbitrary reified `sep`/`emp` syntax trees?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Gives the minimal unbundled kernel soundness obligation for `List.isPerm`-based ACU equality normalization (such as the prototype's `SepAC.Tree.denote_eq` or Core Lean's `ac_rfl`): `SepAssoc`, `SepComm`, and `RightUnit` suffice as propositional equalities (`LeftUnit` is derived), while applying the kernel to a concrete goal still requires a trusted/certifying reifier and alias merger.

#### R1b-iff (`R1b-iff-acu-soundness-characterization`)

- **Kind:** `characterization` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Normalization.lean`
- **Lean:** `Toy.SepAC.acu_denote_eq_of_isPerm_iff`, `Toy.SepAC.acu_laws_of_denote_eq_of_isPerm`
- **Plain claim:** For a fixed carrier `P`, binary operation `sep`, and element `emp`, the `List.isPerm` kernel (`l.atoms.isPerm r.atoms = true → l.denote sep emp env = r.denote sep emp env`) is sound for all environments `env` and syntax trees `l, r` if and only if `SepAssoc sep`, `SepComm sep`, and `RightUnit sep emp` all hold.

```lean
@acu_denote_eq_of_isPerm_iff : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  (∀ (env : Nat → P) (l r : Tree),
      l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r) ↔
    SepAssoc sep ∧ SepComm sep ∧ RightUnit sep emp

@acu_laws_of_denote_eq_of_isPerm : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  (∀ (env : Nat → P) (l r : Tree),
      l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r) →
    SepAssoc sep ∧ SepComm sep ∧ RightUnit sep emp
```

Unfolded (prose):

```text
(∀ (env : Nat → P) (l r : Tree),
    l.atoms.isPerm r.atoms = true → l.denote sep emp env = r.denote sep emp env) ↔
  (∀ x y z : P, sep (sep x y) z = sep x (sep y z)) ∧
  (∀ x y : P, sep x y = sep y x) ∧
  (∀ x : P, sep x emp = x)
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`shallow`):** Forward direction instantiates three 2-atom/unit test trees; backward direction invokes `R1b`.
- **Non-vacuity witness:** `CellModel` satisfies `SepAssoc`, `SepComm`, and `RightUnit` (and exhibits distinct permutation-equivalent trees). (Lean: `Toy.SepAC.acu_denote_eq_of_isPerm_nonvacuous`)
- **Tier justification (`T0`):** Exact equational adequacy characterization combining T0 ACU reflection soundness (`acu_denote_eq_of_isPerm`) with its fully proved three-instance converse (`acu_laws_of_denote_eq_of_isPerm`).
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean`.
  - Braibant, T. & Pous, D., 'Tactics for Reasoning Modulo AC in Coq', CPP 2011, LNCS 7086, pp. 167-182, doi:10.1007/978-3-642-25379-9_14.
- **Design question:** Exactly which algebraic laws are both necessary and sufficient for a `List.isPerm` reflective kernel to be universally sound over `(sep, emp)`?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Shows that dropping any one of `SepAssoc`, `SepComm`, or `RightUnit` breaks universal `List.isPerm` equality soundness over arbitrary trees and environments, separating genuine ACU logics from weaker structures.

#### R1c-unit-count (`R1c-unit-count-ac-soundness`)

- **Kind:** `theorem` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Normalization.lean / FreeMonoid.lean`
- **Lean:** `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm`, `Toy.SepAC.unitCount_eq_and_isPerm_of_forall_ac_denote_eq`, `Toy.SepAC.unitCount_eq_not_necessary_in_fixed_model`
- **Plain claim:** For any associative and commutative operation `sep` (with no unit assumption on `emp`), if `l` and `r` have equal counts of `Tree.unit` leaves (`l.unitCount = r.unitCount`) and `l.atoms.isPerm r.atoms = true`, then `l.denote sep emp env = r.denote sep emp env`; conversely, if `l` and `r` denote equally in every `Type`-level associative-commutative model `(P, sep)` with arbitrary `emp` and `env`, then `l.unitCount = r.unitCount` and `l.atoms.isPerm r.atoms = true` (`Toy.SepAC.unitCount_eq_and_isPerm_of_forall_ac_denote_eq`).

```lean
@ac_denote_eq_of_unitCount_eq_of_isPerm : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  SepAssoc sep →
    SepComm sep →
      ∀ (env : Nat → P) {l r : Tree},
        l.unitCount = r.unitCount →
          l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r

@unitCount_eq_and_isPerm_of_forall_ac_denote_eq : ∀ {l r : Tree},
  (∀ (P : Type) (sep : P → P → P) (emp : P),
      SepAssoc sep → SepComm sep → ∀ (env : Nat → P), Tree.denote sep emp env l = Tree.denote sep emp env r) →
    l.unitCount = r.unitCount ∧ l.atoms.isPerm r.atoms = true

unitCount_eq_not_necessary_in_fixed_model : (Tree.atom 0).unitCount ≠ ((Tree.atom 0).node Tree.unit).unitCount ∧
  ∀ (env : Nat → Nat),
    Tree.denote Nat.add 0 env (Tree.atom 0) = Tree.denote Nat.add 0 env ((Tree.atom 0).node Tree.unit)
```

Unfolded (prose):

```text
Soundness:
  (∀ x y z : P, sep (sep x y) z = sep x (sep y z)) →
  (∀ x y : P, sep x y = sep y x) →
  ∀ (env : Nat → P) {l r : Tree},
    l.unitCount = r.unitCount → l.atoms.isPerm r.atoms = true →
    l.denote sep emp env = r.denote sep emp env

Universal converse (at Type):
  (∀ (P : Type) (sep : P → P → P) (emp : P),
    (∀ x y z, sep (sep x y) z = sep x (sep y z)) → (∀ x y, sep x y = sep y x) →
    ∀ env, l.denote sep emp env = r.denote sep emp env) →
  l.unitCount = r.unitCount ∧ l.atoms.isPerm r.atoms = true
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hAssoc : SepAssoc sep` | Re-associates binary trees with matching leaf multisets without relying on an identity element. | `tight` | `Toy.SepAC.nonAssoc_tight_unitCount_sepAssoc` |
| `hComm : SepComm sep` | Reorders both atom leaves and `Tree.unit` leaves (`emp` behaves as one additional atom). | `tight` | `Toy.SepAC.listAppend_tight_unitCount_sepComm` |
| `hUnitCount : l.unitCount = r.unitCount` | Prevents dropping or duplicating `Tree.unit` leaves when `emp` is not a unit of `sep`. | `tight` | `Toy.SepAC.boolAndFalse_tight_unitCount_eq` |
| `hPerm : l.atoms.isPerm r.atoms = true` | Ensures `l` and `r` contain the same multiset of atom indices. | `tight` | `Toy.SepAC.boolAndFalse_tight_unitCount_perm` |

**Supporting-theorem ledger** (hypotheses of the other Lean names of this card that carry `Prop` hypotheses; same tightness discipline as above):

| Theorem | Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.SepAC.unitCount_eq_and_isPerm_of_forall_ac_denote_eq` | `∀ (P : Type) (sep : P → P → P) (emp : P), SepAssoc sep → SepComm sep → ∀ (env : Nat → P), Tree.denote sep emp env l = Tree.denote sep emp env r` | Converse direction: only equal denotations across every associative-commutative model, `emp`, and environment force equal `unitCount` and `isPerm`; equality in one fixed model does not. | `tight` | `Toy.SepAC.unitCount_eq_not_necessary_in_fixed_model` (The theorem has no other hypotheses. `atom 0` and `atom 0 ∗ unit` have different `unitCount`, while they denote equally for every `env` in the single model `(Nat, Nat.add, 0)`, so the hypothesis also cannot be weakened to one model.) |

- **Supporting non-vacuity witness:** `Toy.SepAC.unitCount_converse_hypothesis_nonvacuous` (the distinct trees `atom 0 ∗ unit` and `unit ∗ atom 0` satisfy the hypothesis).

- **Depth (`shallow`):** Reduces `unitCount`-equal AC trees to unit-free AC via `shiftTree` (mapping `.unit ↦ .atom 0` and `.atom i ↦ .atom (i + 1)`) and adjoins a fresh `none` unit via `Option P`; the universal converse embeds `shiftTree` into `Bag` with `emp ↦ Bag.single 0` and `env i = Bag.single (i + 1)`.
- **Non-vacuity witness:** `(Nat, Nat.add, emp := 99)` satisfies `SepAssoc` and `SepComm` while violating `RightUnit Nat.add 99`, and non-unit-free trees `(atom 0 ∗ unit)` and `(unit ∗ atom 0)` have equal `unitCount = 1`, `isPerm = true`, and equal denotations in every environment. (Lean: `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_nonvacuous`)
- **Tier justification (`T0`):** Unit-law-free commutative-semigroup (AC) reflection treating `Tree.unit` leaves as an unconstrained atom; AC reflection without unit laws is already mechanized in core Lean `Lean.Data.AC` and Braibant & Pous (CPP 2011).
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean`: `Lean.Data.AC.Expr` has only `var` and `op` (no `unit` constructor); neutral elements are represented as `LawfulIdentity`-flagged variables, so AC rearrangement without `LawfulIdentity` treats every non-neutral constant uniformly as an atom.
  - Braibant, T. & Pous, D., 'Tactics for Reasoning Modulo AC in Coq', CPP 2011, LNCS 7086, pp. 167-182, doi:10.1007/978-3-642-25379-9_14. Handles AC symbols without neutral elements.
  - Boutin, S., 'Using reflection to build efficient and certified decision procedures', TACS 1997, LNCS 1281, pp. 515-529, doi:10.1007/BFb0014565.
- **Design question:** When `emp` is not assumed to be a unit of `sep`, what exact syntactic condition on `Tree` makes reflective AC normalization universally sound across all associative-commutative models `(P, sep, emp, env)`?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Shows that reflective AC normalization does not require `emp` to be a unit of `sep` whenever `Tree.unit` leaf counts match (`l.unitCount = r.unitCount`), and that this syntactic side condition cannot be weakened if universal soundness over arbitrary AC models and `emp` is desired.

#### R1c-unit-free (`R1c-unit-free-ac-soundness`)

- **Kind:** `theorem` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Normalization.lean`
- **Lean:** `Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm`
- **Plain claim:** For any associative and commutative operation `sep` (with no unit assumption on `emp`), if both `l` and `r` contain no `Tree.unit` leaves (`l.unitFree = true` and `r.unitFree = true`) and `l.atoms.isPerm r.atoms = true`, then `l.denote sep emp env = r.denote sep emp env`.

```lean
@ac_denote_eq_of_unitFree_of_isPerm : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  SepAssoc sep →
    SepComm sep →
      ∀ (env : Nat → P) {l r : Tree},
        l.unitFree = true →
          r.unitFree = true → l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r
```

Unfolded (prose):

```text
(∀ x y z : P, sep (sep x y) z = sep x (sep y z)) →
(∀ x y : P, sep x y = sep y x) →
∀ (env : Nat → P) {l r : Tree},
  l.unitFree = true → r.unitFree = true → l.atoms.isPerm r.atoms = true →
  l.denote sep emp env = r.denote sep emp env
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hAssoc : SepAssoc sep` | Re-associates unit-free binary trees without appealing to an identity element. | `tight` | `Toy.SepAC.nonAssoc_tight_unitFree_sepAssoc` |
| `hComm : SepComm sep` | Reorders atom indices without appealing to an identity element. | `tight` | `Toy.SepAC.listAppend_tight_unitFree_sepComm` |
| `hUFL : l.unitFree = true` | Rules out `Tree.unit` in `l`, whose evaluation would introduce an unconstrained `emp` when `r` has no `Tree.unit`. | `tight` | `Toy.SepAC.boolAndFalse_tight_unitFree_left` |
| `hUFR : r.unitFree = true` | Rules out `Tree.unit` in `r`; `l.unitFree = true` and `l.atoms.isPerm r.atoms = true` do not imply `r.unitFree = true` because `Tree.atoms` erases `Tree.unit`. | `tight` | `Toy.SepAC.boolAndFalse_tight_unitFree_right` |
| `hPerm : l.atoms.isPerm r.atoms = true` | Ensures `l` and `r` have the same non-empty multiset of atom indices. | `tight` | `Toy.SepAC.boolAndFalse_tight_unitFree_perm` |

- **Depth (`shallow`):** Two-line specialization of `R1c-unit-count` via `Tree.unitFree_iff_unitCount_eq_zero`.
- **Non-vacuity witness:** `(Nat, Nat.add, emp := 99)` satisfies `SepAssoc` and `SepComm` while violating `RightUnit Nat.add 99`, and `((0 ∗ 1) ∗ 2)` vs `(2 ∗ (0 ∗ 1))` are `unitFree` with `isPerm = true`. (Lean: `Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm_nonvacuous`)
- **Tier justification (`T0`):** Unit-free specialization of `ac_denote_eq_of_unitCount_eq_of_isPerm` (`l.unitFree = true ↔ l.unitCount = 0`); unit-free AC reflection is already mechanized in core Lean `Lean.Data.AC` and Braibant & Pous (CPP 2011).
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean`: `Lean.Data.AC.Expr` is unit-free (`var | op`).
  - Braibant, T. & Pous, D., 'Tactics for Reasoning Modulo AC in Coq', CPP 2011, LNCS 7086, pp. 167-182, doi:10.1007/978-3-642-25379-9_14.
  - Repository `AeneasVerif/aeneas`, open unmerged PR #1551 (commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean`: meta-level `mkStar` (lines 113-118) avoids a trailing `emp` on non-empty atom arrays, whereas kernel-level `Tree.denote_eq_foldr` (lines 51-57) folds into `emp` and uses `sep_emp_r_eq` even on unit-free trees.
- **Design question:** Is a unit law needed for reflective AC reordering of unit-free trees, or is it paid solely for `emp` unit elimination?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Clarifies for tactic designers that unit laws (`LeftUnit`, `RightUnit`) are paid solely for `emp`-elimination, not for associative-commutative reordering of unit-free formulas (matching unit-free normalizers such as `Lean.Data.AC` when no `LawfulIdentity` is registered).

#### R1c-iff (`R1c-iff-ac-soundness-characterization`)

- **Kind:** `characterization` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Normalization.lean`
- **Lean:** `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_iff`, `Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm_iff`, `Toy.SepAC.ac_laws_of_unitCount_denote_eq_of_isPerm`, `Toy.SepAC.ac_laws_of_unitFree_denote_eq_of_isPerm`
- **Plain claim:** For a fixed carrier `P`, binary operation `sep`, and arbitrary `emp`, `List.isPerm` soundness over equal-unit-count trees (equivalently, over unit-free trees) holds for all environments and trees if and only if `SepAssoc sep` and `SepComm sep` hold (with no constraint on `emp`).

```lean
@ac_denote_eq_of_unitCount_eq_of_isPerm_iff : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  (∀ (env : Nat → P) (l r : Tree),
      l.unitCount = r.unitCount →
        l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r) ↔
    SepAssoc sep ∧ SepComm sep

@ac_denote_eq_of_unitFree_of_isPerm_iff : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  (∀ (env : Nat → P) (l r : Tree),
      l.unitFree = true →
        r.unitFree = true → l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r) ↔
    SepAssoc sep ∧ SepComm sep

@ac_laws_of_unitCount_denote_eq_of_isPerm : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  (∀ (env : Nat → P) (l r : Tree),
      l.unitCount = r.unitCount →
        l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r) →
    SepAssoc sep ∧ SepComm sep

@ac_laws_of_unitFree_denote_eq_of_isPerm : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  (∀ (env : Nat → P) (l r : Tree),
      l.unitFree = true →
        r.unitFree = true → l.atoms.isPerm r.atoms = true → Tree.denote sep emp env l = Tree.denote sep emp env r) →
    SepAssoc sep ∧ SepComm sep
```

Unfolded (prose):

```text
(∀ (env : Nat → P) (l r : Tree),
    l.unitCount = r.unitCount → l.atoms.isPerm r.atoms = true →
    l.denote sep emp env = r.denote sep emp env) ↔
  (∀ x y z : P, sep (sep x y) z = sep x (sep y z)) ∧ (∀ x y : P, sep x y = sep y x)

(∀ (env : Nat → P) (l r : Tree),
    l.unitFree = true → r.unitFree = true → l.atoms.isPerm r.atoms = true →
    l.denote sep emp env = r.denote sep emp env) ↔
  (∀ x y z : P, sep (sep x y) z = sep x (sep y z)) ∧ (∀ x y : P, sep x y = sep y x)
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`shallow`):** Two-tree forward converses (`assoc` and `comm` test trees) paired with `R1c-unit-count` and `R1c-unit-free`.
- **Non-vacuity witness:** `(Nat, Nat.add, emp := 99)` satisfies `SepAssoc` and `SepComm` while violating `RightUnit Nat.add 99`. (Lean: `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_nonvacuous`)
- **Tier justification (`T0`):** Exact algebraic characterization pairing T0 unit-law-free AC soundness with its fully proved two-tree converses (`ac_laws_of_unitCount_denote_eq_of_isPerm`, `ac_laws_of_unitFree_denote_eq_of_isPerm`).
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean`.
  - Braibant, T. & Pous, D., CPP 2011, LNCS 7086, pp. 167-182, doi:10.1007/978-3-642-25379-9_14.
- **Design question:** Exactly which algebraic laws characterize unit-law-free reflective AC soundness over `(sep, emp)`?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Pinpoints `SepAssoc ∧ SepComm` as the exact algebraic interface for unit-law-free AC reflection (either unit-free or equal-unit-count), independent of any distinguished constant `emp`.

#### R2a (`R2a-noncommutative-append-counterexample`)

- **Kind:** `counterexample` | **Tier:** `T0` | **Depth:** `definitional` | **Module:** `lean/Toy/SepAC/Normalization.lean`
- **Lean:** `Toy.SepAC.listAppend_tight_isPerm_sepComm`
- **Plain claim:** Reference point: over `(List Nat, List.append, [])`, `SepAssoc`, `RightUnit`, and `LeftUnit` all hold while `SepComm` fails, and `(atom 0 ∗ atom 1)` vs `(atom 1 ∗ atom 0)` satisfy `l.atoms.isPerm r.atoms = true`, yet their denotations at `env i = [i]` are `[0, 1] ≠ [1, 0]`.

```lean
listAppend_tight_isPerm_sepComm : SepAssoc (P := List Nat) List.append ∧
  RightUnit (P := List Nat) List.append [] ∧
    LeftUnit (P := List Nat) List.append [] ∧
      ¬SepComm (P := List Nat) List.append ∧
        have env : Nat → List Nat := fun i => [i];
        have l := (Tree.atom 0).node (Tree.atom 1);
        have r := (Tree.atom 1).node (Tree.atom 0);
        l.atoms.isPerm r.atoms = true ∧ Tree.denote List.append [] env l ≠ Tree.denote List.append [] env r
```

Unfolded (prose):

```text
(∀ x y z : List Nat, (x ++ y) ++ z = x ++ (y ++ z)) ∧
(∀ x : List Nat, x ++ [] = x) ∧
(∀ x : List Nat, [] ++ x = x) ∧
¬(∀ x y : List Nat, x ++ y = y ++ x) ∧
([0, 1].isPerm [1, 0] = true ∧ [0] ++ [1] ≠ [1] ++ [0])
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`definitional`):** Direct evaluation on `List.append` over `[0]` and `[1]`.
- **Non-vacuity witness:** Concrete trees `atom 0 ∗ atom 1` and `atom 1 ∗ atom 0` under `env i = [i]`. (Lean: `Toy.SepAC.listAppend_tight_isPerm_sepComm`)
- **Tier justification (`T0`):** Reference point: standard free-monoid witness separating non-commutative monoids (`List` with `++`) from commutative monoids.
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean`: gates `sort` on optional `Commutative` (`Context.comm`, line 31; `norm`, line 111), separating associative-only normalization from AC normalization.
  - Agda standard library (`agda/agda-stdlib` v2.1, commit `97bc55e47367c562b3032bf104f2a00b19716f88`), `src/Algebra/Solver/Monoid.agda` vs `src/Algebra/Solver/CommutativeMonoid.agda`: separate solvers for non-commutative monoids vs commutative monoids.
  - Braibant, T. & Pous, D., 'Tactics for Reasoning Modulo AC in Coq', CPP 2011, LNCS 7086, pp. 167-182, doi:10.1007/978-3-642-25379-9_14. Handles associative-only operations separately from AC operations.
- **Design question:** Reference point: where does `List.isPerm`-based reflective normalization break for ordered / non-commutative associative monoids?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Serves as a concrete sanity witness that ordered separation logics or non-commutative separating operators (like `List.append`) cannot reuse `List.isPerm` normalization and must use associative-only flattening (`R1a`) or non-commutative monoid solvers.

#### R2b (`R2b-nonassociative-three-element-counterexample`)

- **Kind:** `counterexample` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Normalization.lean / Algebra.lean`
- **Lean:** `Toy.SepAC.nonAssoc_tight_isPerm_sepAssoc`, `Toy.SepAC.atMostTwo_comm_unital_sepAssoc`
- **Plain claim:** Reference point: on the 3-element carrier `NonAssocCarrier`, `NonAssocCarrier.op` satisfies `SepComm`, `RightUnit`, and `LeftUnit` with unit `.emp` while violating `SepAssoc`, and `((atom 0 ∗ atom 0) ∗ atom 1)` vs `(atom 0 ∗ (atom 0 ∗ atom 1))` satisfy `l.atoms.isPerm r.atoms = true` (in fact `l.atoms = r.atoms = [0, 0, 1]`) yet denote `.b ≠ .a`; moreover, 3 elements is minimal because every commutative unital magma on a carrier of size at most 2 is associative (`atMostTwo_comm_unital_sepAssoc`).

```lean
nonAssoc_tight_isPerm_sepAssoc : SepComm NonAssocCarrier.op ∧
  RightUnit NonAssocCarrier.op NonAssocCarrier.emp ∧
    LeftUnit NonAssocCarrier.op NonAssocCarrier.emp ∧
      ¬SepAssoc NonAssocCarrier.op ∧
        have env := fun i => if (i == 0) = true then NonAssocCarrier.a else NonAssocCarrier.b;
        have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 1);
        have r := (Tree.atom 0).node ((Tree.atom 0).node (Tree.atom 1));
        l.atoms.isPerm r.atoms = true ∧
          Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env l ≠
            Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env r

@atMostTwo_comm_unital_sepAssoc : ∀ {P : Type u_1} (a b : P),
  (∀ (x : P), x = a ∨ x = b) → ∀ (op : P → P → P) (e : P), SepComm op → RightUnit op e → SepAssoc op
```

Unfolded (prose):

```text
(∀ x y : NonAssocCarrier, op x y = op y x) ∧
(∀ x : NonAssocCarrier, op x .emp = x) ∧
(∀ x : NonAssocCarrier, op .emp x = x) ∧
¬(∀ x y z : NonAssocCarrier, op (op x y) z = op x (op y z)) ∧
([0, 0, 1].isPerm [0, 0, 1] = true ∧ op (op .a .a) .b ≠ op .a (op .a .b))
-- together with: any commutative right-unital op on P with (∀ x, x = a ∨ x = b) satisfies SepAssoc op
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`shallow`):** Finite table evaluation on 3 elements plus case-splitting proof that every commutative right-unital binary op on a ≤2-element carrier is associative (`atMostTwo_comm_unital_sepAssoc`).
- **Non-vacuity witness:** Concrete 3-element table `NonAssocCarrier.op` with `env 0 = .a, env 1 = .b`. (Lean: `Toy.SepAC.nonAssoc_tight_isPerm_sepAssoc`)
- **Tier justification (`T0`):** Reference point: textbook 3-element commutative unital non-associative magma falsifying ACU tree normalization even on identical atom lists `[0, 0, 1]`, paired with the elementary cardinality-≤2 associativity proof `atMostTwo_comm_unital_sepAssoc`.
- **Prior art:**
  - Boutin, S., 'Using reflection to build efficient and certified decision procedures', TACS 1997, LNCS 1281, pp. 515-529, doi:10.1007/BFb0014565.
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean`: `Context.assoc` (line 30) is mandatory, unlike optional `comm` and `idem`.
- **Design question:** Reference point: can commutativity and a two-sided unit ever compensate for missing associativity in reflective tree normalization, and what is the smallest countermodel?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Demonstrates that a 3-element carrier is the exact finite threshold where commutativity and two-sided unit laws fail to force associativity, explaining why every AC/ACU solver requires `SepAssoc` unconditionally.

#### R2c (`R2c-nonunital-boolean-counterexample`)

- **Kind:** `counterexample` | **Tier:** `T0` | **Depth:** `definitional` | **Module:** `lean/Toy/SepAC/Normalization.lean`
- **Lean:** `Toy.SepAC.boolAndFalse_tight_isPerm_rightUnit`
- **Plain claim:** Reference point: over `(Bool, Bool.and, false)`, `SepAssoc` and `SepComm` hold while `RightUnit Bool.and false` fails, and `atom 0` vs `(atom 0 ∗ unit)` satisfy `l.atoms.isPerm r.atoms = true`, yet at `env 0 = true` their denotations are `true ≠ false`.

```lean
boolAndFalse_tight_isPerm_rightUnit : SepAssoc and ∧
  SepComm and ∧
    ¬RightUnit and false ∧
      have env := fun x => true;
      have l := Tree.atom 0;
      have r := (Tree.atom 0).node Tree.unit;
      l.atoms.isPerm r.atoms = true ∧ Tree.denote and false env l ≠ Tree.denote and false env r
```

Unfolded (prose):

```text
(∀ x y z : Bool, Bool.and (Bool.and x y) z = Bool.and x (Bool.and y z)) ∧
(∀ x y : Bool, Bool.and x y = Bool.and y x) ∧
¬(∀ x : Bool, Bool.and x false = x) ∧
([0].isPerm [0] = true ∧ true ≠ Bool.and true false)
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`definitional`):** Direct boolean evaluation on `Bool.and` with `emp = false`.
- **Non-vacuity witness:** Concrete trees `atom 0` and `atom 0 ∗ unit` at `env _ = true`. (Lean: `Toy.SepAC.boolAndFalse_tight_isPerm_rightUnit`)
- **Tier justification (`T0`):** Reference point: elementary 2-element commutative semigroup (`Bool.and` with absorbing element `false` in the `emp` slot) isolating the unit requirement.
- **Prior art:**
  - Repository `AeneasVerif/aeneas`, open unmerged PR #1551 (commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean`: `Tree.atoms` erases `.unit` to `[]`, relying on `emp` being a genuine unit of `sep`.
- **Design question:** Reference point: where does erasing `Tree.unit` in `Tree.atoms` fail if the designated constant `emp` is not a unit for `sep`?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Illustrates on a 2-element semigroup why syntactic erasure of `Tree.unit` in `Tree.atoms` is unsound whenever the distinguished constant `emp` fails `RightUnit sep emp`.

#### R3a (`R3a-free-commutative-monoid-completeness`)

- **Kind:** `theorem` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/FreeMonoid.lean`
- **Lean:** `Toy.SepAC.isPerm_of_bag_denote_eq`
- **Plain claim:** In the free commutative monoid `(Bag, Bag.sep, Bag.emp)` of finitely supported `Nat` multiplicity maps under the free generator environment `Bag.single`, if `l.denote Bag.sep Bag.emp Bag.single = r.denote Bag.sep Bag.emp Bag.single`, then `l.atoms.isPerm r.atoms = true`.

```lean
@isPerm_of_bag_denote_eq : ∀ {l r : Tree},
  Tree.denote Bag.sep Bag.emp Bag.single l = Tree.denote Bag.sep Bag.emp Bag.single r → l.atoms.isPerm r.atoms = true
```

Unfolded (prose):

```text
where Bag := { count : Nat → Nat // ∃ bound, ∀ i, bound ≤ i → count i = 0 },
  Bag.emp.count := fun _ => 0,
  (Bag.single k).count := fun i => if i == k then 1 else 0,
  (Bag.sep b₁ b₂).count := fun i => b₁.count i + b₂.count i:
l.denote Bag.sep Bag.emp Bag.single = r.denote Bag.sep Bag.emp Bag.single →
  l.atoms.isPerm r.atoms = true
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hDenote : l.denote Bag.sep Bag.emp Bag.single = r.denote Bag.sep Bag.emp Bag.single` | Semantic equality in `Bag` under `Bag.single`, implying equal per-index atom multiplicities. | `tight` | `Toy.SepAC.bag_tight_denote_eq` |

- **Depth (`shallow`):** Structural multiplicity homomorphism `bag_count_denote` plus core Lean's `List.perm_iff_count` and `List.isPerm_iff`.
- **Non-vacuity witness:** Distinct trees `((atom 0 ∗ unit) ∗ atom 1)` and `(atom 1 ∗ atom 0)` have equal `Bag` denotations under `Bag.single`. (Lean: `Toy.SepAC.isPerm_of_bag_denote_eq_nonvacuous`)
- **Tier justification (`T0`):** Reduces directly to core Lean's `List.perm_iff_count` (`Init.Data.List.Perm`, line 426) and a tree multiplicity-homomorphism lemma; bag normal forms are mechanized in Agda stdlib (`Algebra.Solver.CommutativeMonoid`) and quotient multisets in Mathlib (`Multiset.coe_eq_coe`).
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/List/Perm.lean`: `List.perm_iff_count` (line 426) and `List.isPerm_iff` (line 448), which form the mathematical core of completeness.
  - Agda standard library (`agda/agda-stdlib` v2.1, commit `97bc55e47367c562b3032bf104f2a00b19716f88`), `src/Algebra/Solver/CommutativeMonoid.agda`: normalizes commutative-monoid expressions to multiplicity vectors (`Normal n = Vec ℕ n`, a bag).
  - Mathlib (`leanprover-community/mathlib4`, commit `4dbecbe2ebe515d6bfb36d0685092eed09f9d1fd`, `Mathlib/Data/Multiset/Defs.lean`), `Multiset.coe_eq_coe` (line 100): quotient-multiset equality iff list permutation.
  - Boutin, S., 'Using reflection to build efficient and certified decision procedures', TACS 1997, LNCS 1281, pp. 515-529, doi:10.1007/BFb0014565.
  - Repository `AeneasVerif/aeneas`, open unmerged PR #1551 (commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean`, `proveEqAC` (doc lines 140-142, def lines 143-162): merges unified atom pairs into a shared index class before checking permutation.
- **Design question:** For which exact algebraic semantics and atom environments is `List.isPerm` a complete decision procedure for `sep`-tree equality, and why must tactics pre-unify aliases and handle non-free laws separately?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Explains why `List.isPerm` is complete precisely for universal ACU identities (the free commutative monoid under distinct generators) and why separation-logic tactics must pre-merge equal/aliased atoms and handle non-free domain rules outside the ACU kernel.

#### R3a-iff (`R3a-iff-bag-characterization`)

- **Kind:** `characterization` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/FreeMonoid.lean`
- **Lean:** `Toy.SepAC.isPerm_iff_bag_denote_eq`, `Toy.SepAC.isPerm_iff_forall_acu_denote_eq`
- **Plain claim:** For all syntax trees `l, r : Tree`, `l.denote Bag.sep Bag.emp Bag.single = r.denote Bag.sep Bag.emp Bag.single` holds if and only if `l.atoms.isPerm r.atoms = true`, and equivalently `l.atoms.isPerm r.atoms = true` holds if and only if `l` and `r` denote equally across all `Type`-level associative, commutative, right-unital models `(P, sep, emp)` and all environments `env : Nat → P` (`Toy.SepAC.isPerm_iff_forall_acu_denote_eq`).

```lean
isPerm_iff_bag_denote_eq : ∀ (l r : Tree),
  Tree.denote Bag.sep Bag.emp Bag.single l = Tree.denote Bag.sep Bag.emp Bag.single r ↔ l.atoms.isPerm r.atoms = true

isPerm_iff_forall_acu_denote_eq : ∀ (l r : Tree),
  l.atoms.isPerm r.atoms = true ↔
    ∀ (P : Type) (sep : P → P → P) (emp : P),
      SepAssoc sep →
        SepComm sep → RightUnit sep emp → ∀ (env : Nat → P), Tree.denote sep emp env l = Tree.denote sep emp env r
```

Unfolded (prose):

```text
(l.denote Bag.sep Bag.emp Bag.single = r.denote Bag.sep Bag.emp Bag.single ↔
  l.atoms.isPerm r.atoms = true)
and
(l.atoms.isPerm r.atoms = true ↔
  ∀ (P : Type) (sep : P → P → P) (emp : P),
    SepAssoc sep → SepComm sep → RightUnit sep emp →
    ∀ env : Nat → P, l.denote sep emp env = r.denote sep emp env)
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`shallow`):** Pairs `R3a` with `R1b` on `(Bag, Bag.sep, Bag.emp)` and specializes/generalizes across all `Type`-level ACU models.
- **Non-vacuity witness:** Distinct trees `((atom 0 ∗ unit) ∗ atom 1)` and `(atom 1 ∗ atom 0)` have equal `Bag` denotations under `Bag.single`. (Lean: `Toy.SepAC.isPerm_of_bag_denote_eq_nonvacuous`)
- **Tier justification (`T0`):** Combines `isPerm_of_bag_denote_eq` (R3a) with the `Bag` instance of `acu_denote_eq_of_isPerm` (R1b).
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/List/Perm.lean` (`List.perm_iff_count`, `List.isPerm_iff`).
  - Mathlib (`leanprover-community/mathlib4`, commit `4dbecbe2ebe515d6bfb36d0685092eed09f9d1fd`, `Mathlib/Data/Multiset/Defs.lean`), `Multiset.coe_eq_coe` (line 100).
- **Design question:** Does `List.isPerm` coincide exactly with semantic equality in the multiplicity-bag model `Bag` under distinct generators?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Connects decidable syntactic `List.isPerm` directly to both `Bag` multiset semantics and universal validity over all `Type`-level ACU models, giving a crisp completeness boundary for ACU kernels.

#### R3b (`R3b-pointwise-idempotent-and-conflict-incompleteness`)

- **Kind:** `impossibility` | **Tier:** `T0` | **Depth:** `definitional` | **Module:** `lean/Toy/SepAC/FreeMonoid.lean`
- **Lean:** `Toy.SepAC.denote_eq_and_isPerm_false_of_idemElem`, `Toy.SepAC.denote_eq_and_isPerm_false_of_sepIdem`, `Toy.SepAC.cellModel_incomplete_without_sepIdem`, `Toy.SepAC.twoCellModel_conflict_distinct_atoms_incomplete`, `Toy.SepAC.optBag_absorbing_but_complete`
- **Plain claim:** Whenever a single atom value satisfies pointwise idempotence `IdemElem sep (env 0)` (`env 0 ∗ env 0 = env 0`) — for example the absorbing element `conflict` of the mixed non-idempotent ACU model `CellModel`, or any value of the globally idempotent model `(Bool, Bool.or, false)` — `dupAtomTree` (`atom 0 ∗ atom 0`) and `singleAtomTree` (`atom 0`) have identical denotations while `dupAtomTree.atoms.isPerm singleAtomTree.atoms = false`; moreover, incompleteness also arises without any idempotent atom value, for specific environments, in non-idempotent ACU models with an absorbing conflict element (`CellModel` at `env = fun _ => owned`; `TwoCellModel` at `env 0 = cellA`, `env 1 = cellB`), although an absorbing element does not by itself break completeness for every environment (`Toy.SepAC.optBag_absorbing_but_complete`).

```lean
@denote_eq_and_isPerm_false_of_idemElem : ∀ {P : Type u_1} (sep : P → P → P) (emp : P) (env : Nat → P),
  IdemElem sep (env 0) →
    Tree.denote sep emp env dupAtomTree = Tree.denote sep emp env singleAtomTree ∧
      dupAtomTree.atoms.isPerm singleAtomTree.atoms = false

@denote_eq_and_isPerm_false_of_sepIdem : ∀ {P : Type u_1} (sep : P → P → P) (emp : P),
  SepIdem sep →
    ∀ (env : Nat → P),
      Tree.denote sep emp env dupAtomTree = Tree.denote sep emp env singleAtomTree ∧
        dupAtomTree.atoms.isPerm singleAtomTree.atoms = false

cellModel_incomplete_without_sepIdem : SepAssoc CellModel.sep ∧
  SepComm CellModel.sep ∧
    RightUnit CellModel.sep CellModel.empty ∧
      ¬SepIdem CellModel.sep ∧
        (have env := fun x => CellModel.conflict;
          Tree.denote CellModel.sep CellModel.empty env dupAtomTree =
              Tree.denote CellModel.sep CellModel.empty env singleAtomTree ∧
            dupAtomTree.atoms.isPerm singleAtomTree.atoms = false) ∧
          have env := fun x => CellModel.owned;
          have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 0);
          have r := (Tree.atom 0).node (Tree.atom 0);
          ¬IdemElem CellModel.sep (env 0) ∧
            Tree.denote CellModel.sep CellModel.empty env l = Tree.denote CellModel.sep CellModel.empty env r ∧
              l.atoms.isPerm r.atoms = false

twoCellModel_conflict_distinct_atoms_incomplete : SepAssoc TwoCellModel.sep ∧
  SepComm TwoCellModel.sep ∧
    RightUnit TwoCellModel.sep TwoCellModel.empty ∧
      ¬SepIdem TwoCellModel.sep ∧
        have env := fun i => if (i == 0) = true then TwoCellModel.cellA else TwoCellModel.cellB;
        have l := (Tree.atom 0).node (Tree.atom 0);
        have r := (Tree.atom 1).node (Tree.atom 1);
        env 0 ≠ env 1 ∧
          ¬IdemElem TwoCellModel.sep (env 0) ∧
            ¬IdemElem TwoCellModel.sep (env 1) ∧
              Tree.denote TwoCellModel.sep TwoCellModel.empty env l =
                  Tree.denote TwoCellModel.sep TwoCellModel.empty env r ∧
                l.atoms.isPerm r.atoms = false

optBag_absorbing_but_complete : (∀ (x : Option Bag), optBagSep none x = none ∧ optBagSep x none = none) ∧
  ¬IdemElem optBagSep (some (Bag.single 0)) ∧
    ∀ (l r : Tree),
      Tree.denote optBagSep (some Bag.emp) (fun i => some (Bag.single i)) l =
          Tree.denote optBagSep (some Bag.emp) (fun i => some (Bag.single i)) r →
        l.atoms.isPerm r.atoms = true
```

Unfolded (prose):

```text
Pointwise idempotence:
  sep (env 0) (env 0) = env 0 →
  sep (env 0) (env 0) = env 0 ∧ [0, 0].isPerm [0] = false
Non-idempotent conflict witnesses:
  in CellModel (¬∀ x, x ∗ x = x), ((owned ∗ owned) ∗ owned) = conflict = (owned ∗ owned) with ¬(owned ∗ owned = owned) and [0, 0, 0].isPerm [0, 0] = false;
  in TwoCellModel (¬∀ x, x ∗ x = x), (cellA ∗ cellA) = conflict = (cellB ∗ cellB) with cellA ≠ cellB and [0, 0].isPerm [1, 1] = false
Scope of the conflict witnesses (absorbing element, complete for one environment):
  in Option Bag with absorbing none (some a ∗ some b = some (a ∗ b)), some (Bag.single 0) is not idempotent and
  l.denote = r.denote → l.atoms.isPerm r.atoms = true at env = fun i => some (Bag.single i)
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hIdem0 : IdemElem sep (env 0)` | Collapses `env 0 ∗ env 0` to `env 0` at atom index `0` while `Tree.atoms` preserves multiplicity (`[0, 0]` vs `[0]`); does not require global `SepIdem sep`. | `tight` | `Toy.SepAC.bag_dupAtomTree_denote_ne_singleAtomTree` |

**Supporting-theorem ledger** (hypotheses of the other Lean names of this card that carry `Prop` hypotheses; same tightness discipline as above):

| Theorem | Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.SepAC.denote_eq_and_isPerm_false_of_sepIdem` | `SepIdem sep` | Global idempotence makes `env 0` pointwise idempotent for every `env`, so the conclusion holds in every environment. | `tight` | `Toy.SepAC.bag_dupAtomTree_denote_ne_singleAtomTree` (The theorem has no other `Prop` hypotheses. In `(Bag, Bag.sep, Bag.emp)` under `Bag.single`, `¬ SepIdem Bag.sep` holds and `dupAtomTree`, `singleAtomTree` denote differently.) |

- **Supporting non-vacuity witness:** `Toy.SepAC.boolOr_sepIdem` (`(Bool, Bool.or)` is globally idempotent (`SepIdem or`)).

- **Depth (`definitional`):** One-step unfolding of `IdemElem` and finite table evaluation on `Bool.or`, `CellModel`, and `TwoCellModel`.
- **Non-vacuity witness:** Satisfied both in the globally idempotent ACU model `(Bool, Bool.or, false)` at `env 0 = true ≠ false` and in the non-idempotent ACU model `CellModel` at `env 0 = .conflict`. (Lean: `Toy.SepAC.idempotent_bool_acu_incomplete`, `Toy.SepAC.cellModel_conflict_idemElem_incomplete`)
- **Positive control:** In the free commutative monoid `(Bag, Bag.sep, Bag.emp)` under `Bag.single`, `¬ IdemElem Bag.sep (Bag.single 0)` holds and `dupAtomTree` and `singleAtomTree` have distinct denotations (Lean: `Toy.SepAC.bag_dupAtomTree_denote_ne_singleAtomTree`).
- **Tier justification (`T0`):** Well-known completeness boundary separating multiset normal forms from idempotent/set normal forms (mechanized in core Lean `Lean.Data.AC.mergeIdem` and Agda stdlib `Algebra.Solver.IdempotentCommutativeMonoid`), stated pointwise via `IdemElem` and paired with non-idempotent conflict witnesses.
- **Prior art:**
  - Lean 4 core (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/Init/Data/AC.lean`: `Context.idem : Option (PLift (IdempotentOp op))` (line 32) and `mergeIdem` (lines 82-93) mechanize the deduplication escape hatch for globally idempotent operations.
  - Agda standard library (`agda/agda-stdlib` v2.1, commit `97bc55e47367c562b3032bf104f2a00b19716f88`), `src/Algebra/Solver/IdempotentCommutativeMonoid.agda`: normalizes idempotent commutative monoids to bit vectors (`Normal n = Vec Bool n`, a set).
  - Krebbers, R., Timany, A. & Birkedal, L., 'Interactive proofs in higher-order concurrent separation logic', POPL 2017, pp. 205-217, doi:10.1145/3009837.3009855. Separates the persistent context (`env persistent`) from the spatial context (`env spatial`) in Iris Proof Mode.
  - Chlipala, A., 'Mostly-automated verification of low-level programs in computational separation logic', PLDI 2011, pp. 234-245, doi:10.1145/1993498.1993526 (ACM SIGPLAN Notices 46(6) reprint doi:10.1145/1993316.1993526). Lifts pure predicates via `[< p >]` and turns pure facts into pure hypotheses.
  - Repository `AeneasVerif/aeneas`, open unmerged PR #1551 (commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean`: `splitPures` (lines 230-251), `introPures` (lines 253-266), and `pullLeft` (lines 289-354) hoist pure facts and existentials into the Lean context rather than contracting duplicates inside `SepAC.Tree.denote_eq`.
- **Design question:** Why is a multiset-permutation ACU kernel incomplete when an atom value is pointwise idempotent (as duplicable assertions such as `⌜P⌝` or `□ P` may be, subject to the qualifications in the modeling bridge) and, for some environments, in non-idempotent conflict models, and what are the limits of set-equality deduplication?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Suggests why real separation-logic tactics (like Iris Proof Mode, Bedrock, or the cited prototype) hoist pure/persistent assertions and handle ownership conflicts (`x ↦ v ∗ x ↦ v ⊢ False`) outside a multiset-permutation ACU kernel, and why naive deduplication is unsound for linear/affine spatial resources: any atom value satisfying `IdemElem` defeats completeness. The package does not prove that any pure or persistent assertion of a real separation logic satisfies `IdemElem`. Unproved commentary: in BI-style logics `P ∗ P` and `P` are at best mutually entailing (`P ∗ P ⊣⊢ P`), which gives the propositional equality `IdemElem` requires only under extensionality (such as `propext`/`funext` over heap predicates); for persistent assertions even `P ∗ P ⊢ P` can depend on further structure such as affinity, and in a linear logic a persistent but non-affine assertion need not satisfy `P ∗ P ⊢ P`.

#### R4a (`R4a-frame-cancellation-extensional-acu`)

- **Kind:** `theorem` | **Tier:** `T2` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Entailment.lean`
- **Lean:** `Toy.SepAC.acu_entails_of_common_perm_of_sepMonoRight`, `Toy.SepAC.acu_entails_of_cancelAtoms_of_sepMonoRight`, `Toy.SepAC.cancelAtoms_spec`, `Toy.SepAC.cancelAtoms_count`, `Toy.SepAC.cancelAtoms_disjoint`
- **Plain claim:** If `sep` satisfies `SepAssoc sep`, `SepComm sep`, and `RightUnit sep emp` (propositional equality), and `entails` satisfies `SepMonoRight sep entails` (`x ⊢ y → f ∗ x ⊢ f ∗ y`), then for any common sub-multiset `common` and residuals `ls, rs` with `l.atoms.Perm (common ++ ls)` and `r.atoms.Perm (common ++ rs)`, `entails (l.denote sep emp env) (r.denote sep emp env)` follows from `entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env rs)` — without assuming `EntailsRefl`, `EntailsTrans`, or `SepMonoLeft` (with maximal `cancelAtoms` cancellation following via `cancelAtoms_spec`).

```lean
@acu_entails_of_common_perm_of_sepMonoRight : ∀ {P : Type u_1} (sep : P → P → P) (emp : P) (entails : P → P → Prop),
  SepAssoc sep →
    SepComm sep →
      RightUnit sep emp →
        SepMonoRight sep entails →
          ∀ (env : Nat → P) {l r : Tree} (common ls rs : List Nat),
            l.atoms.Perm (common ++ ls) →
              r.atoms.Perm (common ++ rs) →
                entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env rs) →
                  entails (Tree.denote sep emp env l) (Tree.denote sep emp env r)

@acu_entails_of_cancelAtoms_of_sepMonoRight : ∀ {P : Type u_1} (sep : P → P → P) (emp : P) (entails : P → P → Prop),
  SepAssoc sep →
    SepComm sep →
      RightUnit sep emp →
        SepMonoRight sep entails →
          ∀ (env : Nat → P) {l r : Tree},
            entails (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).fst)
                (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).snd) →
              entails (Tree.denote sep emp env l) (Tree.denote sep emp env r)

cancelAtoms_spec : ∀ (xs ys : List Nat),
  ∃ common, xs.Perm (common ++ (cancelAtoms xs ys).fst) ∧ ys.Perm (common ++ (cancelAtoms xs ys).snd)

cancelAtoms_count : ∀ (xs ys : List Nat) (a : Nat),
  List.count a (cancelAtoms xs ys).fst = List.count a xs - List.count a ys ∧
    List.count a (cancelAtoms xs ys).snd = List.count a ys - List.count a xs

cancelAtoms_disjoint : ∀ (xs ys : List Nat) (a : Nat), a ∈ (cancelAtoms xs ys).fst → ¬a ∈ (cancelAtoms xs ys).snd
```

Unfolded (prose):

```text
(∀ x y z : P, sep (sep x y) z = sep x (sep y z)) →
(∀ x y : P, sep x y = sep y x) →
(∀ x : P, sep x emp = x) →
(∀ f x y : P, entails x y → entails (sep f x) (sep f y)) →
∀ (env : Nat → P) {l r : Tree} (common ls rs : List Nat),
  l.atoms.Perm (common ++ ls) → r.atoms.Perm (common ++ rs) →
  entails (ls.foldr (fun i acc => sep (env i) acc) emp)
          (rs.foldr (fun i acc => sep (env i) acc) emp) →
  entails (l.denote sep emp env) (r.denote sep emp env)
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hAssoc : SepAssoc sep` | Groups all cancelled atoms in `common` into a single left frame factor `denoteAtoms sep emp env common`. | `tight` | `Toy.SepAC.nonAssoc_tight_commonPerm_sepAssoc` |
| `hComm : SepComm sep` | Reorders atom lists to bring `common` to the front of both `l` and `r`, and makes `SepMonoLeft` derivable (`Toy.SepAC.sepMonoLeft_of_comm_of_monoRight`). | `tight` | `Toy.SepAC.listAppend_tight_commonPerm_sepComm` |
| `hRightUnit : RightUnit sep emp` | Equates empty residuals `[]` with `emp` (`x = sep x emp`, critical even when every atom cancels so `ls = rs = []`). | `tight` | `Toy.SepAC.boolAndFalse_tight_commonPerm_rightUnit` |
| `hMonoRight : SepMonoRight sep entails` | Lifts the residual entailment `denoteAtoms ls ⊢ denoteAtoms rs` across the common cancelled frame `denoteAtoms common`. | `tight` | `Toy.SepAC.capOne_tight_commonPerm_sepMonoRight` |
| `hl : l.atoms.Perm (common ++ ls)` | Certifies that `common` and `ls` partition the atom multiset of `l` (discharged for maximal cancellation by `cancelAtoms_spec`). | `tight` | `Toy.SepAC.natAdd_tight_commonPerm_leftPerm` |
| `hr : r.atoms.Perm (common ++ rs)` | Certifies that `common` and `rs` partition the atom multiset of `r` (discharged for maximal cancellation by `cancelAtoms_spec`). | `tight` | `Toy.SepAC.natAdd_tight_commonPerm_rightPerm` |
| `hResidual : entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env rs)` | Residual proof obligation remaining after removing `common` from both sides. | `tight` | `Toy.SepAC.natAdd_tight_commonPerm_residual` |

**Supporting-theorem ledger** (hypotheses of the other Lean names of this card that carry `Prop` hypotheses; same tightness discipline as above):

| Theorem | Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.SepAC.acu_entails_of_cancelAtoms_of_sepMonoRight` | `SepAssoc sep` | Groups the atoms cancelled by `cancelAtoms` into a single frame factor (the corollary instantiates the primary theorem via `cancelAtoms_spec`). | `tight` | `Toy.SepAC.nonAssoc_tight_cancelAtoms_sepAssoc` |
| `Toy.SepAC.acu_entails_of_cancelAtoms_of_sepMonoRight` | `SepComm sep` | Reorders both atom lists so that the atoms cancelled by `cancelAtoms` come first. | `tight` | `Toy.SepAC.listAppend_tight_cancelAtoms_sepComm` |
| `Toy.SepAC.acu_entails_of_cancelAtoms_of_sepMonoRight` | `RightUnit sep emp` | Equates empty residuals `[]` with `emp` (critical when every atom cancels). | `tight` | `Toy.SepAC.boolAndFalse_tight_cancelAtoms_rightUnit` |
| `Toy.SepAC.acu_entails_of_cancelAtoms_of_sepMonoRight` | `SepMonoRight sep entails` | Lifts the `cancelAtoms` residual entailment across the cancelled frame. | `tight` | `Toy.SepAC.capOne_tight_commonPerm_sepMonoRight` (its last two conjuncts state that the `cancelAtoms` residual holds and the conclusion fails.) |
| `Toy.SepAC.acu_entails_of_cancelAtoms_of_sepMonoRight` | `entails (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).fst) (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).snd)` | Residual proof obligation remaining after maximal cancellation by `cancelAtoms`. | `tight` | `Toy.SepAC.natAdd_tight_cancelAtoms_residual` |

- **Supporting non-vacuity witness:** `Toy.SepAC.acu_entails_of_cancelAtoms_nonvacuous` (`CellModel` with `affineCellEntails`, `l = atom 0 ∗ atom 0`, `r = atom 0`, `env = fun _ => owned`).

- **Depth (`shallow`):** Flattens both sides via `R1a`, permutes along `hl`/`hr` via `denoteAtoms_perm`, distributes `denoteAtoms_append`, and applies `SepMonoRight` once; `cancelAtoms_spec`/`count`/`disjoint` establish maximal cancellation.
- **Non-vacuity witness:** Holds both in `CellModel` (with partial non-maximal cancellation `common = [0]`, `ls = [0, 0]`, `rs = [0]`) and for the non-reflexive, non-transitive relation `x + 2 = y` on `(Nat, +, 0)`. (Lean: `Toy.SepAC.acu_entails_of_common_perm_nonvacuous`, `Toy.SepAC.stepByTwo_nonPreorder_satisfies_cancel_hypotheses`)
- **Tier justification (`T2`):** Generalized parametric form of known reflective and tactic-level frame-cancellation procedures (MirrorShard `check_entailment` / `Apply_cancel_sound`, Malecha, Chlipala & Braibant ITP 2014; Bedrock PLDI 2011; VST `floyd/seplog_tactics.v`; CFML `xsimpl`; Iris `iFrame`; Chargueraud 2020 Remark 3.10 noting one-sided/two-sided monotonicity equivalence): stated over an arbitrary binary relation without reflexivity or transitivity, for any common sub-multiset `common`, with fully proved multiset-difference specification of `cancelAtoms` and maximal cancellation as a corollary.
- **Prior art:**
  - Malecha, G., Chlipala, A. & Braibant, T., 'Compositional Computational Reflection', ITP 2014, LNCS 8558, pp. 374-389, doi:10.1007/978-3-319-08970-6_24: MirrorShard's reflective entailment checker (Listing 1) reifies propositional separation logic into `sexpr := Star | Opaque | Emp` with list-environment denotation `sexprD`, erases `Emp` terms and crosses common terms off both sides in `check_entailment`, and proves `check_entailment_sound` (plus extensible `Apply_cancel_sound` for Bedrock) discharged by reflexivity.
  - Chargueraud, A., 'Separation Logic for Sequential Programs (Functional Pearl)', Proc. ACM Program. Lang. 4(ICFP), Article 116, August 2020, doi:10.1145/3408998 (author PDF: 43 pp.; Crossref: pp. 1-34): Remark 3.10 states that one-sided `star-monotone-r` is provably equivalent to symmetric monotonicity; Appendix K describes the Ltac `xsimpl` cancellation tactic.
  - Chlipala, A., 'Mostly-automated verification of low-level programs in computational separation logic', PLDI 2011, pp. 234-245, doi:10.1145/1993498.1993526: Bedrock's separation-logic tactic performs AC-aware cancellation (step 7, 'Cancellation') with unification of existentials.
  - Krebbers, R., Timany, A. & Birkedal, L., 'Interactive proofs in higher-order concurrent separation logic', POPL 2017, pp. 205-217, doi:10.1145/3009837.3009855: `iFrame` via typeclass-driven `Frame` instances (§4.2).
  - Appel, A. W., 'Verified Software Toolchain', ESOP 2011, LNCS 6602, pp. 1-17, doi:10.1007/978-3-642-19718-5_1 (VST overview); Appel, A. W. et al., Program Logics for Certified Compilers, Cambridge University Press, 2014, ISBN 978-1-107-04801-0 (bibliographic pointer only; chapter contents were not verified at the source, so no content claim is made); repository `PrincetonUniversity/VST`, commit `d50ac1969f9f6586621895eb043ccf08a165f731`, `floyd/seplog_tactics.v`, `Ltac cancel_frame` (line 346) and `Ltac cancel` (initial definition at line 468, redefined via `Ltac cancel ::= new_cancel cancel_local_tac` at line 914).
  - Repository `AeneasVerif/aeneas`, open unmerged PR #1551 (commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/Tactic/Matchers.lean`, `cancelGoal` (doc lines 87-91, def lines 92-117): matches atoms at meta level via unification (`matchAll`) and kernel-checks two `proveEqAC` reorderings plus one `sep_mono` step.
- **Design question:** Which exact laws of `sep` and `⊢` justify removing an arbitrary common sub-multiset of atoms (including maximal `cancelAtoms` as a special case) when `sep` satisfies propositional ACU?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Isolates `SepAssoc`, `SepComm`, `RightUnit`, and `SepMonoRight` as sufficient to justify arbitrary common sub-multiset frame cancellation (and `cancelAtoms` as a special case) in extensional separation logics without assuming reflexivity or transitivity of `⊢`; real tactics with existential unification or non-trivial reification must supply those steps outside this kernel.

#### R4b (`R4b-frame-cancellation-bientails-acu`)

- **Kind:** `theorem` | **Tier:** `T2` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Entailment.lean`
- **Lean:** `Toy.SepAC.bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`, `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`
- **Plain claim:** When `sep` satisfies associativity, commutativity, and right unit only up to mutual entailment `Bientails entails` (`SepAssocBientails`, `SepCommBientails`, `RightUnitBientails`), adding `EntailsTrans entails` alongside `SepMonoRight sep entails` suffices to derive `entails (l.denote sep emp env) (r.denote sep emp env)` from `entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env rs)` for any common sub-multiset `common` with `l.atoms.Perm (common ++ ls)` and `r.atoms.Perm (common ++ rs)` (`EntailsRefl` and `SepMonoLeft` being derivable, and maximal `cancelAtoms` cancellation following via `cancelAtoms_spec`).

```lean
@bientails_acu_entails_of_common_perm_of_trans_sepMonoRight : ∀ {P : Type u_1} (sep : P → P → P) (emp : P)
  (entails : P → P → Prop),
  EntailsTrans entails →
    SepAssocBientails sep entails →
      SepCommBientails sep entails →
        RightUnitBientails sep emp entails →
          SepMonoRight sep entails →
            ∀ (env : Nat → P) {l r : Tree} (common ls rs : List Nat),
              l.atoms.Perm (common ++ ls) →
                r.atoms.Perm (common ++ rs) →
                  entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env rs) →
                    entails (Tree.denote sep emp env l) (Tree.denote sep emp env r)

@bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight : ∀ {P : Type u_1} (sep : P → P → P) (emp : P)
  (entails : P → P → Prop),
  EntailsTrans entails →
    SepAssocBientails sep entails →
      SepCommBientails sep entails →
        RightUnitBientails sep emp entails →
          SepMonoRight sep entails →
            ∀ (env : Nat → P) {l r : Tree},
              entails (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).fst)
                  (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).snd) →
                entails (Tree.denote sep emp env l) (Tree.denote sep emp env r)
```

Unfolded (prose):

```text
(∀ x y z : P, entails x y → entails y z → entails x z) →
(∀ x y z : P, entails (sep (sep x y) z) (sep x (sep y z)) ∧ entails (sep x (sep y z)) (sep (sep x y) z)) →
(∀ x y : P, entails (sep x y) (sep y x) ∧ entails (sep y x) (sep x y)) →
(∀ x : P, entails (sep x emp) x ∧ entails x (sep x emp)) →
(∀ f x y : P, entails x y → entails (sep f x) (sep f y)) →
∀ (env : Nat → P) {l r : Tree} (common ls rs : List Nat),
  l.atoms.Perm (common ++ ls) → r.atoms.Perm (common ++ rs) →
  entails (ls.foldr (fun i acc => sep (env i) acc) emp)
          (rs.foldr (fun i acc => sep (env i) acc) emp) →
  entails (l.denote sep emp env) (r.denote sep emp env)
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hTrans : EntailsTrans entails` | Chains multi-step normal-form bientailments across `SepMonoRight`, and derives `EntailsRefl` (`Toy.SepAC.entailsRefl_of_trans_of_rightUnitBientails`) and `SepMonoLeft` (`Toy.SepAC.sepMonoLeft_of_trans_of_commBientails_of_monoRight`). | `tight` | `Toy.SepAC.tagDistLeOne_tight_bientails_commonPerm_trans` |
| `hAssoc : SepAssocBientails sep entails` | Re-associates syntax trees and normal-form folds up to `Bientails`. | `tight` | `Toy.SepAC.nonAssoc_tight_bientails_commonPerm_sepAssoc` |
| `hComm : SepCommBientails sep entails` | Reorders atom indices up to `Bientails` and derives `SepMonoLeft` and `LeftUnitBientails`. | `tight` | `Toy.SepAC.listAppend_tight_bientails_commonPerm_sepComm` |
| `hRightUnit : RightUnitBientails sep emp entails` | Eliminates `Tree.unit` and trailing `foldr` `emp` factors up to `Bientails`, and together with `EntailsTrans` implies `EntailsRefl`. | `tight` | `Toy.SepAC.boolAndFalse_tight_bientails_commonPerm_rightUnit` |
| `hMonoRight : SepMonoRight sep entails` | Frames the common cancelled prefix `common` onto `hResidual` and enables right `Bientails` congruence. | `tight` | `Toy.SepAC.capOne_tight_bientails_commonPerm_sepMonoRight` |
| `hl : l.atoms.Perm (common ++ ls)` | Certifies that `common` and `ls` partition the atom multiset of `l`. | `tight` | `Toy.SepAC.natAdd_tight_bientails_commonPerm_leftPerm` |
| `hr : r.atoms.Perm (common ++ rs)` | Certifies that `common` and `rs` partition the atom multiset of `r`. | `tight` | `Toy.SepAC.natAdd_tight_bientails_commonPerm_rightPerm` |
| `hResidual : entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env rs)` | Residual entailment after removing `common` from both sides. | `tight` | `Toy.SepAC.natAdd_tight_bientails_commonPerm_residual` |

**Supporting-theorem ledger** (hypotheses of the other Lean names of this card that carry `Prop` hypotheses; same tightness discipline as above):

| Theorem | Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight` | `EntailsTrans entails` | Chains the `Bientails` reassociation, reordering, and unit steps with the lifted residual entailment. | `tight` | `Toy.SepAC.tagDistLeOne_tight_bientails_cancelAtoms_trans` |
| `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight` | `SepAssocBientails sep entails` | Groups the atoms cancelled by `cancelAtoms` into a single frame factor, up to mutual entailment. | `tight` | `Toy.SepAC.nonAssoc_tight_bientails_cancelAtoms_sepAssoc` |
| `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight` | `SepCommBientails sep entails` | Reorders both sides so that the cancelled atoms come first, up to mutual entailment. | `tight` | `Toy.SepAC.listAppend_tight_bientails_cancelAtoms_sepComm` |
| `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight` | `RightUnitBientails sep emp entails` | Relates empty residuals `[]` to `emp`, up to mutual entailment. | `tight` | `Toy.SepAC.boolAndFalse_tight_bientails_cancelAtoms_rightUnit` |
| `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight` | `SepMonoRight sep entails` | Lifts the `cancelAtoms` residual entailment across the cancelled frame. | `tight` | `Toy.SepAC.capOne_tight_bientails_cancelAtoms_sepMonoRight` |
| `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight` | `entails (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).fst) (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).snd)` | Residual proof obligation remaining after maximal cancellation by `cancelAtoms`. | `tight` | `Toy.SepAC.natAdd_tight_bientails_cancelAtoms_residual` |

- **Supporting non-vacuity witness:** `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_nonvacuous` (`CellModel` with `affineCellEntails`, `l = atom 0 ∗ atom 0`, `r = atom 0`, `env = fun _ => owned`).

- **Depth (`shallow`):** Derives `EntailsRefl`, `SepMonoLeft`, and `LeftUnitBientails`, then chains `Bientails`-congruence across `hFlat`, `hPermBi`, and `hApp` via `EntailsTrans` before applying `hMonoRight`.
- **Non-vacuity witness:** `(TaggedNat, taggedSep, taggedEmp, taggedValLe)` satisfies all hypotheses while violating propositional `RightUnit taggedSep taggedEmp` (because `taggedSep` increments a syntax-depth counter). (Lean: `Toy.SepAC.bientails_acu_entails_of_common_perm_nonvacuous`)
- **Tier justification (`T2`):** Generalizes reflective arbitrary-sub-multiset frame cancellation from extensional (`=`) ACU algebras to intensional/setoid (`Bientails`) BI logics without `propext`/`funext` (cf. MoSeL ICFP 2018 for generic BI over setoid `⊣⊢` and Braibant & Pous CPP 2011 for setoid AC equality reflection), showing that `EntailsTrans` cannot be dropped given the remaining hypotheses (`Toy.SepAC.tagDistLeOne_tight_bientails_commonPerm_trans`; relative tightness only, not a characterization) while deriving `EntailsRefl` and `SepMonoLeft`.
- **Prior art:**
  - Krebbers, R., Jourdan, J.-H., Jung, R., Tassarotti, J., Kaiser, J.-O., Timany, A., Chargueraud, A. & Dreyer, D., 'MoSeL: a general, extensible modal framework for interactive proofs in separation logic', Proc. ACM Program. Lang. 2(ICFP), 2018, pp. 1-30, doi:10.1145/3236772. Formulates a generic BI interface (applicable to both affine and linear logics) over a setoid equivalence rather than tying tactics to Iris's `iProp`.
  - Braibant, T. & Pous, D., 'Tactics for Reasoning Modulo AC in Coq', CPP 2011, LNCS 7086, pp. 167-182, doi:10.1007/978-3-642-25379-9_14. Mechanizes reflective AC equality modulo user-defined equivalence relations (setoids).
  - Agda standard library (`agda/agda-stdlib` v2.1, commit `97bc55e47367c562b3032bf104f2a00b19716f88`), `src/Algebra/Solver/CommutativeMonoid.agda`: mechanizes commutative-monoid reflection over a setoid `≈`.
  - Appel, A. W. et al., Program Logics for Certified Compilers, Cambridge University Press, 2014, ISBN 978-1-107-04801-0 (bibliographic pointer only; chapter contents were not verified at the source, so no content claim is made).
- **Design question:** What additional order laws become necessary when moving a reflective sub-multiset frame-cancellation kernel from an extensional assertion type (with `=`) to an intensional BI logic (with `⊣⊢` only)?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Shows precisely how moving from extensional assertion equality (`=`) to intensional BI mutual entailment (`⊣⊢`) adds `EntailsTrans` as a strict requirement while keeping `EntailsRefl` and `SepMonoLeft` derivable, informing setoid-based BI tactic kernels (as in MoSeL).

#### R4c (`R4c-nonmonotone-preorder-cancellation-counterexample`)

- **Kind:** `counterexample` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Entailment.lean`
- **Lean:** `Toy.SepAC.capOne_tight_commonPerm_sepMonoRight`, `Toy.SepAC.capOne_not_sepMonoRight`
- **Plain claim:** Reference point: on `(Nat, +, 0)`, the preorder `capOneEntails` satisfies `EntailsRefl` and `EntailsTrans` while violating `SepMonoRight` (`capOne_not_sepMonoRight`), and cancelling `common = [0]` (matching `cancelAtoms`) from `atom 0 ⊢ atom 0 ∗ atom 0` reduces the false goal `1 ⊢ 2` to the true residual `0 ⊢ 1`.

```lean
capOne_tight_commonPerm_sepMonoRight : EntailsRefl capOneEntails ∧
  EntailsTrans capOneEntails ∧
    SepAssoc Nat.add ∧
      SepComm Nat.add ∧
        RightUnit Nat.add 0 ∧
          ¬SepMonoRight Nat.add capOneEntails ∧
            have env := fun x => 1;
            have l := Tree.atom 0;
            have r := (Tree.atom 0).node (Tree.atom 0);
            l.atoms.Perm ([0] ++ []) ∧
              r.atoms.Perm ([0] ++ [0]) ∧
                capOneEntails (denoteAtoms Nat.add 0 env []) (denoteAtoms Nat.add 0 env [0]) ∧
                  capOneEntails (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).fst)
                      (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).snd) ∧
                    ¬capOneEntails (Tree.denote Nat.add 0 env l) (Tree.denote Nat.add 0 env r)

capOne_not_sepMonoRight : ¬SepMonoRight Nat.add capOneEntails
```

Unfolded (prose):

```text
where capOneScore : 0 ↦ 0, 1 ↦ 1, (n+2) ↦ 0 and capOneEntails x y := capOneScore x ≤ capOneScore y:
(∀ x, capOneEntails x x) ∧ (∀ x y z, capOneEntails x y → capOneEntails y z → capOneEntails x z) ∧
SepAssoc Nat.add ∧ SepComm Nat.add ∧ RightUnit Nat.add 0 ∧ ¬SepMonoRight Nat.add capOneEntails ∧
capOneEntails 0 1 ∧ ¬capOneEntails 1 2
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`shallow`):** Preorder check by `Nat.le` plus finite evaluation of `capOneScore` at `0`, `1`, `2`.
- **Non-vacuity witness:** Concrete capacity-bounded preorder `capOneEntails` on `(Nat, +, 0)` at `env 0 = 1`. (Lean: `Toy.SepAC.capOne_tight_commonPerm_sepMonoRight`)
- **Tier justification (`T0`):** Reference point: concrete non-monotone preorder counterexample on `(Nat, +, 0)` refuting frame-cancellation soundness when `SepMonoRight` is omitted.
- **Prior art:**
  - Chargueraud, A., 'Separation Logic for Sequential Programs (Functional Pearl)', Proc. ACM Program. Lang. 4(ICFP), Article 116, 2020, doi:10.1145/3408998, Section 3.3 (Remark 3.10 on framing monotonicity).
- **Design question:** Reference point: how does frame cancellation fail when `sep` is not monotone for a reflexive, transitive entailment preorder `⊢`?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Warns tactic implementers that checking preorder laws (`EntailsRefl`, `EntailsTrans`) and ACU laws without framing monotonicity (`SepMonoRight`) is unsound for cancellation, illustrated by a capacity-bounded preorder.

#### R4d (`R4d-maximal-cancellation-converse-failure`)

- **Kind:** `counterexample` | **Tier:** `T1` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Entailment.lean`
- **Lean:** `Toy.SepAC.cellModel_cancelAtoms_converse_fails`, `Toy.SepAC.twoCellModel_affine_cancelAtoms_converse_fails`, `Toy.SepAC.partial_cancellation_succeeds_where_cancelAtoms_fails`, `Toy.SepAC.affineCellEntails_residual_holds`, `Toy.SepAC.boolOr_linear_cancelAtoms_converse_fails`, `Toy.SepAC.boolAnd_affine_cancelAtoms_converse_fails`, `Toy.SepAC.cellModel_affine_cancelAtoms_converse_fails`
- **Plain claim:** Even when all ACU, preorder, and monotonicity laws hold, maximal syntactic cancellation (`cancelAtoms`) is not invertible: (1) in the linear 1-cell conflict model `CellModel` (`¬ AffineEntails`), `(owned ∗ owned) ⊢ owned` holds while `cancelAtoms` yields the false residual `owned ⊢ empty` (a residual that becomes valid under affine `affineCellEntails`); (2) in the affine 2-cell conflict model `TwoCellModel` (`AffineEntails`), `(cellA ∗ cellA) ⊢ (cellA ∗ cellB)` holds while `cancelAtoms` yields the false non-`emp` residual `cellA ⊢ cellB`; and (3) on `((0 ∗ 0) ∗ 0) ⊢ (0 ∗ 0)` in `CellModel`, maximal `cancelAtoms` fails whereas partial cancellation (`common = [0]`) leaves the valid residual `conflict ⊢ owned`.

```lean
cellModel_cancelAtoms_converse_fails : EntailsRefl CellModel.entails ∧
  EntailsTrans CellModel.entails ∧
    SepAssoc CellModel.sep ∧
      SepComm CellModel.sep ∧
        RightUnit CellModel.sep CellModel.empty ∧
          SepMonoRight CellModel.sep CellModel.entails ∧
            ¬AffineEntails CellModel.empty CellModel.entails ∧
              have env := fun x => CellModel.owned;
              have l := (Tree.atom 0).node (Tree.atom 0);
              have r := Tree.atom 0;
              (Tree.denote CellModel.sep CellModel.empty env l).entails
                  (Tree.denote CellModel.sep CellModel.empty env r) ∧
                ¬(denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).fst).entails
                    (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).snd)

twoCellModel_affine_cancelAtoms_converse_fails : SepAssoc TwoCellModel.sep ∧
  SepComm TwoCellModel.sep ∧
    RightUnit TwoCellModel.sep TwoCellModel.empty ∧
      EntailsRefl TwoCellModel.entails ∧
        EntailsTrans TwoCellModel.entails ∧
          SepMonoRight TwoCellModel.sep TwoCellModel.entails ∧
            AffineEntails TwoCellModel.empty TwoCellModel.entails ∧
              have env := fun i => if (i == 0) = true then TwoCellModel.cellA else TwoCellModel.cellB;
              have l := (Tree.atom 0).node (Tree.atom 0);
              have r := (Tree.atom 0).node (Tree.atom 1);
              (Tree.denote TwoCellModel.sep TwoCellModel.empty env l).entails
                  (Tree.denote TwoCellModel.sep TwoCellModel.empty env r) ∧
                ¬(denoteAtoms TwoCellModel.sep TwoCellModel.empty env (cancelAtoms l.atoms r.atoms).fst).entails
                    (denoteAtoms TwoCellModel.sep TwoCellModel.empty env (cancelAtoms l.atoms r.atoms).snd)

partial_cancellation_succeeds_where_cancelAtoms_fails : have env := fun x => CellModel.owned;
have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 0);
have r := (Tree.atom 0).node (Tree.atom 0);
¬(denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).fst).entails
      (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).snd) ∧
  l.atoms.Perm ([0] ++ [0, 0]) ∧
    r.atoms.Perm ([0] ++ [0]) ∧
      (denoteAtoms CellModel.sep CellModel.empty env [0, 0]).entails (denoteAtoms CellModel.sep CellModel.empty env [0])

affineCellEntails_residual_holds : EntailsRefl affineCellEntails ∧
  EntailsTrans affineCellEntails ∧
    SepMonoRight CellModel.sep affineCellEntails ∧
      AffineEntails CellModel.empty affineCellEntails ∧
        have env := fun x => CellModel.owned;
        have l := (Tree.atom 0).node (Tree.atom 0);
        have r := Tree.atom 0;
        affineCellEntails (Tree.denote CellModel.sep CellModel.empty env l)
            (Tree.denote CellModel.sep CellModel.empty env r) ∧
          affineCellEntails (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).fst)
            (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).snd)

boolOr_linear_cancelAtoms_converse_fails : EntailsRefl boolImp ∧
  EntailsTrans boolImp ∧
    SepAssoc or ∧
      SepComm or ∧
        RightUnit or false ∧
          SepMonoRight or boolImp ∧
            ¬AffineEntails false boolImp ∧
              have env := fun i => if (i == 0) = true then true else false;
              have l := (Tree.atom 0).node (Tree.atom 0);
              have r := (Tree.atom 0).node (Tree.atom 1);
              boolImp (Tree.denote or false env l) (Tree.denote or false env r) ∧
                ¬boolImp (denoteAtoms or false env (cancelAtoms l.atoms r.atoms).fst)
                    (denoteAtoms or false env (cancelAtoms l.atoms r.atoms).snd)

boolAnd_affine_cancelAtoms_converse_fails : EntailsRefl boolImp ∧
  EntailsTrans boolImp ∧
    SepAssoc and ∧
      SepComm and ∧
        RightUnit and true ∧
          SepMonoRight and boolImp ∧
            AffineEntails true boolImp ∧
              have env := fun i => if (i == 0) = true then false else true;
              have l := (Tree.atom 0).node (Tree.atom 1);
              have r := (Tree.atom 0).node (Tree.atom 0);
              boolImp (Tree.denote and true env l) (Tree.denote and true env r) ∧
                ¬boolImp (denoteAtoms and true env (cancelAtoms l.atoms r.atoms).fst)
                    (denoteAtoms and true env (cancelAtoms l.atoms r.atoms).snd)

cellModel_affine_cancelAtoms_converse_fails : EntailsRefl affineCellEntails ∧
  EntailsTrans affineCellEntails ∧
    SepAssoc CellModel.sep ∧
      SepComm CellModel.sep ∧
        RightUnit CellModel.sep CellModel.empty ∧
          SepMonoRight CellModel.sep affineCellEntails ∧
            AffineEntails CellModel.empty affineCellEntails ∧
              have env := fun x => CellModel.owned;
              have l := (Tree.atom 0).node (Tree.atom 0);
              have r := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 0);
              affineCellEntails (Tree.denote CellModel.sep CellModel.empty env l)
                  (Tree.denote CellModel.sep CellModel.empty env r) ∧
                ¬affineCellEntails (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).fst)
                    (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).snd)
```

Unfolded (prose):

```text
1. Linear CellModel (owned ⊬ empty): (owned ∗ owned) ⊢ owned holds (conflict ⊢ owned),
   while cancelAtoms [0, 0] [0] = ([0], []) gives owned ⊬ empty (valid under affineCellEntails).
2. Affine TwoCellModel (∀ x, x ⊢ empty): (cellA ∗ cellA) ⊢ (cellA ∗ cellB) holds (conflict ⊢ both),
   while cancelAtoms [0, 0] [0, 1] = ([0], [1]) gives cellA ⊬ cellB.
3. Partial vs maximal in CellModel: on ((0 ∗ 0) ∗ 0) ⊢ (0 ∗ 0), cancelAtoms [0, 0, 0] [0, 0] = ([0], [])
   gives owned ⊬ empty, whereas cancelling common = [0] gives valid residual (owned ∗ owned) ⊢ owned.
4. Smaller witnesses (the cell models above are illustrative, not minimal):
   linear (Bool, or, false) with implication order: (0 ∗ 0) ⊢ (0 ∗ 1) at env 0 = true, env 1 = false,
   while cancelAtoms [0, 0] [0, 1] = ([0], [1]) gives true ⊬ false;
   affine (Bool, and, true) with implication order: (0 ∗ 1) ⊢ (0 ∗ 0) at env 0 = false, env 1 = true,
   while cancelAtoms [0, 1] [0, 0] = ([1], [0]) gives true ⊬ false;
   affine CellModel (affineCellEntails): (0 ∗ 0) ⊢ ((0 ∗ 0) ∗ 0) at env = owned (conflict ⊢ conflict),
   while cancelAtoms [0, 0] [0, 0, 0] = ([], [0]) gives empty ⊬ owned.
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`shallow`):** Concrete evaluations in 3-state `CellModel`, 5-state `TwoCellModel`, and `affineCellEntails`.
- **Non-vacuity witness:** Concrete evaluations in `CellModel` (linear, `env 0 = .owned`) and `TwoCellModel` (affine, `env 0 = .cellA`, `env 1 = .cellB`). (Lean: `Toy.SepAC.cellModel_cancelAtoms_converse_fails`, `Toy.SepAC.twoCellModel_affine_cancelAtoms_converse_fails`)
- **Tier justification (`T1`):** Folklore non-invertibility of greedy maximal frame cancellation in separation logics with disjointness conflict (consistent with Charguéraud 2020 Appendix K, which notes generically, without naming specific rules, that some `xsimpl` simplifications are not equivalence-preserving), made precise with illustrative (not minimal) linear (`CellModel`) and affine (`TwoCellModel`) finite countermodels plus a witness separating partial from maximal cancellation; two-element models (`Toy.SepAC.boolOr_linear_cancelAtoms_converse_fails`, `Toy.SepAC.boolAnd_affine_cancelAtoms_converse_fails`) and `CellModel` under `affineCellEntails` (`Toy.SepAC.cellModel_affine_cancelAtoms_converse_fails`) also exhibit the failure.
- **Prior art:**
  - Chargueraud, A., 'Separation Logic for Sequential Programs (Functional Pearl)', Proc. ACM Program. Lang. 4(ICFP), Article 116, August 2020, doi:10.1145/3408998: Lemma 3.11 (`single-conflict`: `(p ↪ v1) ⋆ (p ↪ v2) ⊢ [False]`) and Appendix K (`xsimpl`: the text notes generically, without naming specific rules, that 'there are a number of simplifications that are technically not equivalence-preserving, yet nearly always desirable to perform'; Definition K.1, rule (4), removes a predicate `H` other than `⊤⊤` that occurs on both sides).
  - Krebbers, R., Jourdan, J.-H., Jung, R., Tassarotti, J., Kaiser, J.-O., Timany, A., Chargueraud, A. & Dreyer, D., 'MoSeL: a general, extensible modal framework for interactive proofs in separation logic', Proc. ACM Program. Lang. 2(ICFP), 2018, pp. 1-30, doi:10.1145/3236772 (distinguishes affine and linear separation logics).
  - Malecha, G., Chlipala, A. & Braibant, T., 'Compositional Computational Reflection', ITP 2014, LNCS 8558, pp. 374-389, doi:10.1007/978-3-319-08970-6_24: MirrorShard's reflective entailment checker (Listing 1) reifies propositional separation logic into `sexpr := Star | Opaque | Emp` with list-environment denotation `sexprD`, erases `Emp` terms and crosses common terms off both sides in `check_entailment`, and proves `check_entailment_sound` (plus extensible `Apply_cancel_sound` for Bedrock) discharged by reflexivity.
- **Design question:** Why can eager maximal syntactic cancellation turn a valid separation-logic entailment into an unprovable residual in both linear and affine models, and why does a kernel need arbitrary (partial) sub-multiset cancellation?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: derived (modeling bridge)` — Explains why greedy maximal cancellation (`cancelAtoms`) must not be used unconditionally when proving contradictions or partial-frame goals in separation logics (both linear and affine): preserving an arbitrary common sub-multiset (`common`) leaves room for non-maximal cancellation when maximal cancellation overshoots.

#### R5 (`R5-quasilinear-sort-check-and-size-bounds`)

- **Kind:** `theorem` | **Tier:** `T0` | **Depth:** `shallow` | **Module:** `lean/Toy/SepAC/Complexity.lean`
- **Lean:** `Toy.SepAC.checkPermSort_eq_isPerm_and_size_bounds`
- **Plain claim:** For all trees `l, r : Tree`, the accumulator-plus-merge-sort boolean check `checkPermSort l r` equals `l.atoms.isPerm r.atoms`, `atomsFast` equals `atoms` without `List.append`, and `atomsFast.length = atomCount ≤ size`.

```lean
checkPermSort_eq_isPerm_and_size_bounds : ∀ (l r : Tree),
  checkPermSort l r = l.atoms.isPerm r.atoms ∧
    l.atomsFast = l.atoms ∧
      r.atomsFast = r.atoms ∧
        l.atomsFast.length = l.atomCount ∧
          l.atomCount ≤ l.size ∧ r.atomsFast.length = r.atomCount ∧ r.atomCount ≤ r.size
```

Unfolded (prose):

```text
∀ (l r : Tree),
  ((l.atomsAcc []).mergeSort (· ≤ ·) == (r.atomsAcc []).mergeSort (· ≤ ·)) = l.atoms.isPerm r.atoms ∧
  l.atomsAcc [] = l.atoms ∧ r.atomsAcc [] = r.atoms ∧
  (l.atomsAcc []).length = l.atomCount ∧ l.atomCount ≤ l.size ∧
  (r.atomsAcc []).length = r.atomCount ∧ r.atomCount ≤ r.size
```

**Hypothesis ledger:**

None (closed concrete witness or unconditional over its quantified parameters).

- **Depth (`shallow`):** Structural induction for `atomsFast = atoms` and `atomCount ≤ size`, plus `List.mergeSort_perm`, `List.pairwise_mergeSort`, and `List.Perm.eq_of_pairwise`.
- **Non-vacuity witness:** Distinct trees `((atom 2 ∗ unit) ∗ atom 0)` and `(atom 0 ∗ atom 2)` satisfy `checkPermSort l r = true` and `l.atomCount = 2 < 5 = l.size`. (Lean: `Toy.SepAC.checkPermSort_nonvacuous`)
- **Tier justification (`T0`):** Classical equivalence of multiset permutation and sorted-list equality under a total order, mechanized in core Lean `v4.34.1` via `List.mergeSort_perm`, `List.pairwise_mergeSort`, and `List.Perm.eq_of_pairwise` alongside difference-list flattening `atomsFast`.
- **Prior art:**
  - Lean 4 core library (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`): `Init.Data.List.Basic` (`List.Perm` line 1858, `List.isPerm` line 1886), `Init.Data.List.Perm` (`List.isPerm_iff` line 448, `List.Perm.eq_of_pairwise` line 530), `Init.Data.List.Sort.Basic` (`List.mergeSort` lines 79-87), `Init.Data.List.Sort.Impl` (`@[csimp] mergeSort_eq_mergeSortTR₂` line 240), `Init.Data.List.Sort.Lemmas` (`List.mergeSort_perm` line 280, `List.pairwise_mergeSort` line 305), and `Init.Data.AC` (`Lean.Data.AC.sort` lines 76-80).
  - Repository `AeneasVerif/aeneas`, open unmerged PR #1551 (commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean`: uses `qsort` at meta time (`proveEqAC`, line 157) and structural `List.isPerm` in the kernel (`Tree.denote_eq`, lines 59-62).
- **Design question:** Does core Lean `v4.34.1` already provide `List.isPerm`, what is its algorithmic and kernel-reduction behavior vs accumulator extraction + `List.mergeSort` and core `Lean.Data.AC.sort`, and are `checkPermSort` and `List.isPerm` provably identical?
- `Basis: execution (Lean kernel check)` — Elaborated and verified in Lean `v4.34.1` (exact axioms and hashes in **Evidence**).
- `Basis: execution (Lean v4.34.1, probe support/KernelReductionProbe.lean)` — Asking the Lean `v4.34.1` kernel directly (`Lean.Kernel.whnf`, and `Lean.Kernel.isDefEq` against `true`) reduces the probed `List.isPerm` and `Lean.Data.AC.sort` instances to `true` but not the probed `List.mergeSort` and `checkPermSort` instances, so `Eq.refl true` does not prove those `checkPermSort` goals. The observation is specific to this toolchain and to the probed instances; it is not proved for all trees (recorded output in **Evidence**).
- `Basis: derived (modeling bridge)` — Explains the resulting kernel tradeoff between structural `List.isPerm` ($O(m^2)$ comparisons, kernel-reducible on the probed instance), `Lean.Data.AC.sort` ($O(m^2)$ insertion sort, kernel-reducible on the probed instance), and `checkPermSort` ($O(|t|)$ extraction + $O(m \log m)$ runtime `List.mergeSort`, provably equal to `List.isPerm`, but not reduced by the kernel on the probed instances; `List.mergeSort` is defined by well-founded recursion).

### Statements of theorems cited by name

Exact `#check @name` output (under `open Toy.SepAC`; with `set_option pp.analyze true` for the entries described under **Reading conventions**) for every package theorem that the text above cites by name without quoting its statement, grouped by role and sorted by name. Tightness counterexamples have the form "all other hypotheses hold and the conclusion fails" for the hypothesis named in the ledger row that cites them.

#### Tightness counterexamples

```lean
bag_dupAtomTree_denote_ne_singleAtomTree : SepAssoc Bag.sep ∧
  SepComm Bag.sep ∧
    RightUnit Bag.sep Bag.emp ∧
      ¬SepIdem Bag.sep ∧
        ¬IdemElem Bag.sep (Bag.single 0) ∧
          Tree.denote Bag.sep Bag.emp Bag.single dupAtomTree ≠ Tree.denote Bag.sep Bag.emp Bag.single singleAtomTree

bag_tight_denote_eq : have l := Tree.atom 0;
have r := Tree.atom 1;
Tree.denote Bag.sep Bag.emp Bag.single l ≠ Tree.denote Bag.sep Bag.emp Bag.single r ∧ l.atoms.isPerm r.atoms = false

boolAndFalse_tight_bientails_cancelAtoms_rightUnit : EntailsTrans (P := Bool) Eq ∧
  SepAssocBientails and Eq ∧
    SepCommBientails and Eq ∧
      SepMonoRight and Eq ∧
        have env : Nat → Bool := fun x => true;
        have l := Tree.atom 0;
        have r := (Tree.atom 0).node Tree.unit;
        denoteAtoms and false env (cancelAtoms l.atoms r.atoms).fst =
            denoteAtoms and false env (cancelAtoms l.atoms r.atoms).snd ∧
          Tree.denote and false env l ≠ Tree.denote and false env r

boolAndFalse_tight_bientails_commonPerm_rightUnit : EntailsTrans (P := Bool) Eq ∧
  SepAssocBientails and Eq ∧
    SepCommBientails and Eq ∧
      SepMonoRight and Eq ∧
        have env : Nat → Bool := fun x => true;
        have l := Tree.atom 0;
        have r := (Tree.atom 0).node Tree.unit;
        l.atoms.Perm ([0] ++ []) ∧
          r.atoms.Perm ([0] ++ []) ∧
            denoteAtoms and false env [] = denoteAtoms and false env [] ∧
              Tree.denote and false env l ≠ Tree.denote and false env r

boolAndFalse_tight_cancelAtoms_rightUnit : SepAssoc and ∧
  SepComm and ∧
    SepMonoRight and Eq ∧
      have env := fun x => true;
      have l := Tree.atom 0;
      have r := (Tree.atom 0).node Tree.unit;
      denoteAtoms and false env (cancelAtoms l.atoms r.atoms).fst =
          denoteAtoms and false env (cancelAtoms l.atoms r.atoms).snd ∧
        Tree.denote and false env l ≠ Tree.denote and false env r

boolAndFalse_tight_commonPerm_rightUnit : SepAssoc and ∧
  SepComm and ∧
    SepMonoRight and Eq ∧
      have env := fun x => true;
      have l := Tree.atom 0;
      have r := (Tree.atom 0).node Tree.unit;
      l.atoms.Perm ([0] ++ []) ∧
        r.atoms.Perm ([0] ++ []) ∧
          denoteAtoms and false env [] = denoteAtoms and false env [] ∧
            Tree.denote and false env l ≠ Tree.denote and false env r

boolAndFalse_tight_unitCount_eq : SepAssoc and ∧
  SepComm and ∧
    have env := fun x => true;
    have l := Tree.atom 0;
    have r := (Tree.atom 0).node Tree.unit;
    l.unitCount ≠ r.unitCount ∧
      l.atoms.isPerm r.atoms = true ∧ Tree.denote and false env l ≠ Tree.denote and false env r

boolAndFalse_tight_unitCount_perm : SepAssoc and ∧
  SepComm and ∧
    have env := fun i => i == 0;
    have l := Tree.atom 0;
    have r := Tree.atom 1;
    l.unitCount = r.unitCount ∧
      l.atoms.isPerm r.atoms = false ∧ Tree.denote and false env l ≠ Tree.denote and false env r

boolAndFalse_tight_unitFree_left : SepAssoc and ∧
  SepComm and ∧
    have env := fun x => true;
    have l := (Tree.atom 0).node Tree.unit;
    have r := Tree.atom 0;
    r.unitFree = true ∧ l.atoms.isPerm r.atoms = true ∧ Tree.denote and false env l ≠ Tree.denote and false env r

boolAndFalse_tight_unitFree_perm : SepAssoc and ∧
  SepComm and ∧
    have env := fun i => i == 0;
    have l := Tree.atom 0;
    have r := Tree.atom 1;
    l.unitFree = true ∧
      r.unitFree = true ∧ l.atoms.isPerm r.atoms = false ∧ Tree.denote and false env l ≠ Tree.denote and false env r

boolAndFalse_tight_unitFree_right : SepAssoc and ∧
  SepComm and ∧
    have env := fun x => true;
    have l := Tree.atom 0;
    have r := (Tree.atom 0).node Tree.unit;
    l.unitFree = true ∧ l.atoms.isPerm r.atoms = true ∧ Tree.denote and false env l ≠ Tree.denote and false env r

boolAndTrue_tight_isPerm_perm : SepAssoc and ∧
  SepComm and ∧
    RightUnit and true ∧
      have env := fun i => i == 0;
      have l := Tree.atom 0;
      have r := Tree.atom 1;
      l.atoms.isPerm r.atoms = false ∧ Tree.denote and true env l ≠ Tree.denote and true env r

capOne_tight_bientails_cancelAtoms_sepMonoRight : EntailsTrans capOneEntails ∧
  SepAssocBientails Nat.add capOneEntails ∧
    SepCommBientails Nat.add capOneEntails ∧
      RightUnitBientails Nat.add 0 capOneEntails ∧
        ¬SepMonoRight Nat.add capOneEntails ∧
          have env := fun x => 1;
          have l := Tree.atom 0;
          have r := (Tree.atom 0).node (Tree.atom 0);
          capOneEntails (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).fst)
              (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).snd) ∧
            ¬capOneEntails (Tree.denote Nat.add 0 env l) (Tree.denote Nat.add 0 env r)

capOne_tight_bientails_commonPerm_sepMonoRight : EntailsTrans capOneEntails ∧
  SepAssocBientails Nat.add capOneEntails ∧
    SepCommBientails Nat.add capOneEntails ∧
      RightUnitBientails Nat.add 0 capOneEntails ∧
        ¬SepMonoRight Nat.add capOneEntails ∧
          have env := fun x => 1;
          have l := Tree.atom 0;
          have r := (Tree.atom 0).node (Tree.atom 0);
          l.atoms.Perm ([0] ++ []) ∧
            r.atoms.Perm ([0] ++ [0]) ∧
              capOneEntails (denoteAtoms Nat.add 0 env []) (denoteAtoms Nat.add 0 env [0]) ∧
                ¬capOneEntails (Tree.denote Nat.add 0 env l) (Tree.denote Nat.add 0 env r)

leftProj_tight_flattening_leftUnit : SepAssoc (P := Bool) leftProj ∧
  RightUnit leftProj false ∧
    have env : Nat → Bool := fun x => true;
    have t := Tree.unit.node (Tree.atom 0);
    Tree.denote leftProj false env t ≠ denoteAtoms leftProj false env t.atoms

listAppend_tight_bientails_cancelAtoms_sepComm : EntailsTrans (P := List Nat) Eq ∧
  SepAssocBientails (P := List Nat) List.append Eq ∧
    RightUnitBientails (P := List Nat) List.append [] Eq ∧
      SepMonoRight (P := List Nat) List.append Eq ∧
        have env : Nat → List Nat := fun i => [i];
        have l := (Tree.atom 0).node (Tree.atom 1);
        have r := (Tree.atom 1).node (Tree.atom 0);
        denoteAtoms List.append [] env (cancelAtoms l.atoms r.atoms).fst =
            denoteAtoms List.append [] env (cancelAtoms l.atoms r.atoms).snd ∧
          Tree.denote List.append [] env l ≠ Tree.denote List.append [] env r

listAppend_tight_bientails_commonPerm_sepComm : EntailsTrans (P := List Nat) Eq ∧
  SepAssocBientails (P := List Nat) List.append Eq ∧
    RightUnitBientails (P := List Nat) List.append [] Eq ∧
      SepMonoRight (P := List Nat) List.append Eq ∧
        have env : Nat → List Nat := fun i => [i];
        have l := (Tree.atom 0).node (Tree.atom 1);
        have r := (Tree.atom 1).node (Tree.atom 0);
        l.atoms.Perm ([0, 1] ++ []) ∧
          r.atoms.Perm ([0, 1] ++ []) ∧
            denoteAtoms List.append [] env [] = denoteAtoms List.append [] env [] ∧
              Tree.denote List.append [] env l ≠ Tree.denote List.append [] env r

listAppend_tight_cancelAtoms_sepComm : SepAssoc (P := List Nat) List.append ∧
  RightUnit (P := List Nat) List.append [] ∧
    SepMonoRight (P := List Nat) List.append Eq ∧
      have env : Nat → List Nat := fun i => [i];
      have l := (Tree.atom 0).node (Tree.atom 1);
      have r := (Tree.atom 1).node (Tree.atom 0);
      denoteAtoms List.append [] env (cancelAtoms l.atoms r.atoms).fst =
          denoteAtoms List.append [] env (cancelAtoms l.atoms r.atoms).snd ∧
        Tree.denote List.append [] env l ≠ Tree.denote List.append [] env r

listAppend_tight_commonPerm_sepComm : SepAssoc (P := List Nat) List.append ∧
  RightUnit (P := List Nat) List.append [] ∧
    SepMonoRight (P := List Nat) List.append Eq ∧
      have env : Nat → List Nat := fun i => [i];
      have l := (Tree.atom 0).node (Tree.atom 1);
      have r := (Tree.atom 1).node (Tree.atom 0);
      l.atoms.Perm ([0, 1] ++ []) ∧
        r.atoms.Perm ([0, 1] ++ []) ∧
          denoteAtoms List.append [] env [] = denoteAtoms List.append [] env [] ∧
            Tree.denote List.append [] env l ≠ Tree.denote List.append [] env r

listAppend_tight_unitCount_sepComm : SepAssoc (P := List Nat) List.append ∧
  have env : Nat → List Nat := fun i => [i];
  have l := (Tree.atom 0).node (Tree.atom 1);
  have r := (Tree.atom 1).node (Tree.atom 0);
  l.unitCount = r.unitCount ∧
    l.atoms.isPerm r.atoms = true ∧ Tree.denote List.append [] env l ≠ Tree.denote List.append [] env r

listAppend_tight_unitFree_sepComm : SepAssoc (P := List Nat) List.append ∧
  have env : Nat → List Nat := fun i => [i];
  have l := (Tree.atom 0).node (Tree.atom 1);
  have r := (Tree.atom 1).node (Tree.atom 0);
  l.unitFree = true ∧
    r.unitFree = true ∧
      l.atoms.isPerm r.atoms = true ∧ Tree.denote List.append [] env l ≠ Tree.denote List.append [] env r

natAdd_tight_bientails_cancelAtoms_residual : EntailsTrans Nat.le ∧
  SepAssocBientails Nat.add Nat.le ∧
    SepCommBientails Nat.add Nat.le ∧
      RightUnitBientails Nat.add 0 Nat.le ∧
        SepMonoRight Nat.add Nat.le ∧
          have env := fun i => i + 1;
          have l := Tree.atom 1;
          have r := Tree.atom 0;
          ¬(denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).fst).le
                (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).snd) ∧
            ¬(Tree.denote Nat.add 0 env l).le (Tree.denote Nat.add 0 env r)

natAdd_tight_bientails_commonPerm_leftPerm : EntailsTrans Nat.le ∧
  SepAssocBientails Nat.add Nat.le ∧
    SepCommBientails Nat.add Nat.le ∧
      RightUnitBientails Nat.add 0 Nat.le ∧
        SepMonoRight Nat.add Nat.le ∧
          have env := fun x => 1;
          have l := Tree.atom 0;
          have r := Tree.unit;
          ¬l.atoms.Perm ([] ++ []) ∧
            r.atoms.Perm ([] ++ []) ∧
              (denoteAtoms Nat.add 0 env []).le (denoteAtoms Nat.add 0 env []) ∧
                ¬(Tree.denote Nat.add 0 env l).le (Tree.denote Nat.add 0 env r)

natAdd_tight_bientails_commonPerm_residual : EntailsTrans Nat.le ∧
  SepAssocBientails Nat.add Nat.le ∧
    SepCommBientails Nat.add Nat.le ∧
      RightUnitBientails Nat.add 0 Nat.le ∧
        SepMonoRight Nat.add Nat.le ∧
          have env := fun i => i + 1;
          have l := Tree.atom 1;
          have r := Tree.atom 0;
          l.atoms.Perm ([] ++ [1]) ∧
            r.atoms.Perm ([] ++ [0]) ∧
              ¬(denoteAtoms Nat.add 0 env [1]).le (denoteAtoms Nat.add 0 env [0]) ∧
                ¬(Tree.denote Nat.add 0 env l).le (Tree.denote Nat.add 0 env r)

natAdd_tight_bientails_commonPerm_rightPerm : EntailsTrans Nat.le ∧
  SepAssocBientails Nat.add Nat.le ∧
    SepCommBientails Nat.add Nat.le ∧
      RightUnitBientails Nat.add 0 Nat.le ∧
        SepMonoRight Nat.add Nat.le ∧
          have env := fun x => 1;
          have l := Tree.atom 0;
          have r := Tree.unit;
          l.atoms.Perm ([] ++ [0]) ∧
            ¬r.atoms.Perm ([] ++ [0]) ∧
              (denoteAtoms Nat.add 0 env [0]).le (denoteAtoms Nat.add 0 env [0]) ∧
                ¬(Tree.denote Nat.add 0 env l).le (Tree.denote Nat.add 0 env r)

natAdd_tight_cancelAtoms_residual : SepAssoc Nat.add ∧
  SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
      SepMonoRight Nat.add Nat.le ∧
        have env := fun i => i + 1;
        have l := Tree.atom 1;
        have r := Tree.atom 0;
        ¬(denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).fst).le
              (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).snd) ∧
          ¬(Tree.denote Nat.add 0 env l).le (Tree.denote Nat.add 0 env r)

natAdd_tight_commonPerm_leftPerm : SepAssoc Nat.add ∧
  SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
      SepMonoRight Nat.add Nat.le ∧
        have env := fun x => 1;
        have l := Tree.atom 0;
        have r := Tree.unit;
        ¬l.atoms.Perm ([] ++ []) ∧
          r.atoms.Perm ([] ++ []) ∧
            (denoteAtoms Nat.add 0 env []).le (denoteAtoms Nat.add 0 env []) ∧
              ¬(Tree.denote Nat.add 0 env l).le (Tree.denote Nat.add 0 env r)

natAdd_tight_commonPerm_residual : SepAssoc Nat.add ∧
  SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
      SepMonoRight Nat.add Nat.le ∧
        have env := fun i => i + 1;
        have l := Tree.atom 1;
        have r := Tree.atom 0;
        l.atoms.Perm ([] ++ [1]) ∧
          r.atoms.Perm ([] ++ [0]) ∧
            ¬(denoteAtoms Nat.add 0 env [1]).le (denoteAtoms Nat.add 0 env [0]) ∧
              ¬(Tree.denote Nat.add 0 env l).le (Tree.denote Nat.add 0 env r)

natAdd_tight_commonPerm_rightPerm : SepAssoc Nat.add ∧
  SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
      SepMonoRight Nat.add Nat.le ∧
        have env := fun x => 1;
        have l := Tree.atom 0;
        have r := Tree.unit;
        l.atoms.Perm ([] ++ [0]) ∧
          ¬r.atoms.Perm ([] ++ [0]) ∧
            (denoteAtoms Nat.add 0 env [0]).le (denoteAtoms Nat.add 0 env [0]) ∧
              ¬(Tree.denote Nat.add 0 env l).le (Tree.denote Nat.add 0 env r)

nonAssoc_tight_bientails_cancelAtoms_sepAssoc : EntailsTrans (P := NonAssocCarrier) Eq ∧
  SepCommBientails NonAssocCarrier.op Eq ∧
    RightUnitBientails NonAssocCarrier.op NonAssocCarrier.emp Eq ∧
      SepMonoRight NonAssocCarrier.op Eq ∧
        have env : Nat → NonAssocCarrier := fun i => if (i == 0) = true then NonAssocCarrier.a else NonAssocCarrier.b;
        have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 1);
        have r := (Tree.atom 0).node ((Tree.atom 0).node (Tree.atom 1));
        denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env (cancelAtoms l.atoms r.atoms).fst =
            denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env (cancelAtoms l.atoms r.atoms).snd ∧
          Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env l ≠
            Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env r

nonAssoc_tight_bientails_commonPerm_sepAssoc : EntailsTrans (P := NonAssocCarrier) Eq ∧
  SepCommBientails NonAssocCarrier.op Eq ∧
    RightUnitBientails NonAssocCarrier.op NonAssocCarrier.emp Eq ∧
      SepMonoRight NonAssocCarrier.op Eq ∧
        have env : Nat → NonAssocCarrier := fun i => if (i == 0) = true then NonAssocCarrier.a else NonAssocCarrier.b;
        have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 1);
        have r := (Tree.atom 0).node ((Tree.atom 0).node (Tree.atom 1));
        l.atoms.Perm ([0, 0, 1] ++ []) ∧
          r.atoms.Perm ([0, 0, 1] ++ []) ∧
            denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env [] =
                denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env [] ∧
              Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env l ≠
                Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env r

nonAssoc_tight_cancelAtoms_sepAssoc : SepComm NonAssocCarrier.op ∧
  RightUnit NonAssocCarrier.op NonAssocCarrier.emp ∧
    SepMonoRight NonAssocCarrier.op Eq ∧
      have env := fun i => if (i == 0) = true then NonAssocCarrier.a else NonAssocCarrier.b;
      have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 1);
      have r := (Tree.atom 0).node ((Tree.atom 0).node (Tree.atom 1));
      denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env (cancelAtoms l.atoms r.atoms).fst =
          denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env (cancelAtoms l.atoms r.atoms).snd ∧
        Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env l ≠
          Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env r

nonAssoc_tight_commonPerm_sepAssoc : SepComm NonAssocCarrier.op ∧
  RightUnit NonAssocCarrier.op NonAssocCarrier.emp ∧
    SepMonoRight NonAssocCarrier.op Eq ∧
      have env := fun i => if (i == 0) = true then NonAssocCarrier.a else NonAssocCarrier.b;
      have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 1);
      have r := (Tree.atom 0).node ((Tree.atom 0).node (Tree.atom 1));
      l.atoms.Perm ([0, 0, 1] ++ []) ∧
        r.atoms.Perm ([0, 0, 1] ++ []) ∧
          denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env [] =
              denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env [] ∧
            Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env l ≠
              Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env r

nonAssoc_tight_flattening_sepAssoc : LeftUnit NonAssocCarrier.op NonAssocCarrier.emp ∧
  RightUnit NonAssocCarrier.op NonAssocCarrier.emp ∧
    have env := fun i => if (i == 0) = true then NonAssocCarrier.a else NonAssocCarrier.b;
    have t := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 1);
    Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env t ≠
      denoteAtoms NonAssocCarrier.op NonAssocCarrier.emp env t.atoms

nonAssoc_tight_unitCount_sepAssoc : SepComm NonAssocCarrier.op ∧
  have env := fun i => if (i == 0) = true then NonAssocCarrier.a else NonAssocCarrier.b;
  have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 1);
  have r := (Tree.atom 0).node ((Tree.atom 0).node (Tree.atom 1));
  l.unitCount = r.unitCount ∧
    l.atoms.isPerm r.atoms = true ∧
      Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env l ≠
        Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env r

nonAssoc_tight_unitFree_sepAssoc : SepComm NonAssocCarrier.op ∧
  have env := fun i => if (i == 0) = true then NonAssocCarrier.a else NonAssocCarrier.b;
  have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 1);
  have r := (Tree.atom 0).node ((Tree.atom 0).node (Tree.atom 1));
  l.unitFree = true ∧
    r.unitFree = true ∧
      l.atoms.isPerm r.atoms = true ∧
        Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env l ≠
          Tree.denote NonAssocCarrier.op NonAssocCarrier.emp env r

rightProj_tight_flattening_rightUnit : SepAssoc (P := Bool) rightProj ∧
  LeftUnit rightProj false ∧
    have env : Nat → Bool := fun x => true;
    have t := Tree.atom 0;
    Tree.denote rightProj false env t ≠ denoteAtoms rightProj false env t.atoms

tagDistLeOne_tight_bientails_cancelAtoms_trans : SepAssocBientails taggedSep tagDistLeOne ∧
  SepCommBientails taggedSep tagDistLeOne ∧
    RightUnitBientails taggedSep taggedEmp tagDistLeOne ∧
      SepMonoRight taggedSep tagDistLeOne ∧
        have env := fun x => (1, 0);
        have l := Tree.atom 0;
        have r := ((Tree.atom 0).node Tree.unit).node Tree.unit;
        tagDistLeOne (denoteAtoms taggedSep taggedEmp env (cancelAtoms l.atoms r.atoms).fst)
            (denoteAtoms taggedSep taggedEmp env (cancelAtoms l.atoms r.atoms).snd) ∧
          ¬tagDistLeOne (Tree.denote taggedSep taggedEmp env l) (Tree.denote taggedSep taggedEmp env r)

tagDistLeOne_tight_bientails_commonPerm_trans : EntailsRefl tagDistLeOne ∧
  SepAssocBientails taggedSep tagDistLeOne ∧
    SepCommBientails taggedSep tagDistLeOne ∧
      RightUnitBientails taggedSep taggedEmp tagDistLeOne ∧
        SepMonoRight taggedSep tagDistLeOne ∧
          have env := fun x => (1, 0);
          have l := Tree.atom 0;
          have r := ((Tree.atom 0).node Tree.unit).node Tree.unit;
          l.atoms.Perm ([0] ++ []) ∧
            r.atoms.Perm ([0] ++ []) ∧
              tagDistLeOne (denoteAtoms taggedSep taggedEmp env []) (denoteAtoms taggedSep taggedEmp env []) ∧
                ¬tagDistLeOne (Tree.denote taggedSep taggedEmp env l) (Tree.denote taggedSep taggedEmp env r)
```

#### Non-vacuity witnesses and positive controls

```lean
ac_denote_eq_of_unitCount_eq_of_isPerm_nonvacuous : SepAssoc Nat.add ∧
  SepComm Nat.add ∧
    ¬RightUnit Nat.add 99 ∧
      have l := (Tree.atom 0).node Tree.unit;
      have r := Tree.unit.node (Tree.atom 0);
      l.unitFree = false ∧
        r.unitFree = false ∧
          l.unitCount = r.unitCount ∧
            l.atoms.isPerm r.atoms = true ∧
              ∀ (env : Nat → Nat), Tree.denote Nat.add 99 env l = Tree.denote Nat.add 99 env r

ac_denote_eq_of_unitFree_of_isPerm_nonvacuous : SepAssoc Nat.add ∧
  SepComm Nat.add ∧
    ¬RightUnit Nat.add 99 ∧
      have l := ((Tree.atom 0).node (Tree.atom 1)).node (Tree.atom 2);
      have r := (Tree.atom 2).node ((Tree.atom 0).node (Tree.atom 1));
      l.unitFree = true ∧ r.unitFree = true ∧ l.atoms.isPerm r.atoms = true

acu_denote_eq_of_isPerm_nonvacuous : SepAssoc CellModel.sep ∧
  SepComm CellModel.sep ∧
    RightUnit CellModel.sep CellModel.empty ∧
      have l := ((Tree.atom 0).node Tree.unit).node (Tree.atom 1);
      have r := (Tree.atom 1).node (Tree.atom 0);
      l ≠ r ∧ l.atoms.isPerm r.atoms = true

acu_entails_of_cancelAtoms_nonvacuous : SepAssoc CellModel.sep ∧
  SepComm CellModel.sep ∧
    RightUnit CellModel.sep CellModel.empty ∧
      SepMonoRight CellModel.sep affineCellEntails ∧
        have env := fun x => CellModel.owned;
        have l := (Tree.atom 0).node (Tree.atom 0);
        have r := Tree.atom 0;
        affineCellEntails (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).fst)
          (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).snd)

acu_entails_of_common_perm_nonvacuous : SepAssoc CellModel.sep ∧
  SepComm CellModel.sep ∧
    RightUnit CellModel.sep CellModel.empty ∧
      SepMonoRight CellModel.sep CellModel.entails ∧
        have env := fun x => CellModel.owned;
        have l := ((Tree.atom 0).node (Tree.atom 0)).node (Tree.atom 0);
        have r := (Tree.atom 0).node (Tree.atom 0);
        l.atoms.Perm ([0] ++ [0, 0]) ∧
          r.atoms.Perm ([0] ++ [0]) ∧
            (denoteAtoms CellModel.sep CellModel.empty env [0, 0]).entails
              (denoteAtoms CellModel.sep CellModel.empty env [0])

bientails_acu_entails_of_cancelAtoms_nonvacuous : EntailsTrans affineCellEntails ∧
  SepAssocBientails CellModel.sep affineCellEntails ∧
    SepCommBientails CellModel.sep affineCellEntails ∧
      RightUnitBientails CellModel.sep CellModel.empty affineCellEntails ∧
        SepMonoRight CellModel.sep affineCellEntails ∧
          have env := fun x => CellModel.owned;
          have l := (Tree.atom 0).node (Tree.atom 0);
          have r := Tree.atom 0;
          affineCellEntails (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).fst)
            (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).snd)

bientails_acu_entails_of_common_perm_nonvacuous : EntailsTrans taggedValLe ∧
  SepAssocBientails taggedSep taggedValLe ∧
    SepCommBientails taggedSep taggedValLe ∧
      RightUnitBientails taggedSep taggedEmp taggedValLe ∧
        SepMonoRight taggedSep taggedValLe ∧
          ¬RightUnit taggedSep taggedEmp ∧
            have env := fun i => (i + 1, 0);
            have l := (Tree.atom 0).node (Tree.atom 1);
            have r := (Tree.atom 1).node (Tree.atom 2);
            l.atoms.Perm ([1] ++ [0]) ∧
              r.atoms.Perm ([1] ++ [2]) ∧
                taggedValLe (denoteAtoms taggedSep taggedEmp env [0]) (denoteAtoms taggedSep taggedEmp env [2])

boolOr_sepIdem : SepIdem or

cellModel_conflict_idemElem_incomplete : SepAssoc CellModel.sep ∧
  SepComm CellModel.sep ∧
    RightUnit CellModel.sep CellModel.empty ∧
      ¬SepIdem CellModel.sep ∧
        have env := fun x => CellModel.conflict;
        IdemElem CellModel.sep (env 0) ∧
          Tree.denote CellModel.sep CellModel.empty env dupAtomTree =
              Tree.denote CellModel.sep CellModel.empty env singleAtomTree ∧
            dupAtomTree.atoms.isPerm singleAtomTree.atoms = false

checkPermSort_nonvacuous : have l := ((Tree.atom 2).node Tree.unit).node (Tree.atom 0);
have r := (Tree.atom 0).node (Tree.atom 2);
l ≠ r ∧ checkPermSort l r = true ∧ l.atomCount < l.size

denote_eq_denoteAtoms_of_assoc_units_nonvacuous : SepAssoc (P := List Nat) List.append ∧
  LeftUnit (P := List Nat) List.append [] ∧
    RightUnit (P := List Nat) List.append [] ∧ ¬SepComm (P := List Nat) List.append

idempotent_bool_acu_incomplete : SepAssoc or ∧
  SepComm or ∧
    RightUnit or false ∧
      SepIdem or ∧
        have env := fun x => true;
        env 0 ≠ false ∧
          IdemElem or (env 0) ∧
            Tree.denote or false env dupAtomTree = Tree.denote or false env singleAtomTree ∧
              dupAtomTree.atoms.isPerm singleAtomTree.atoms = false

isPerm_of_bag_denote_eq_nonvacuous : have l := ((Tree.atom 0).node Tree.unit).node (Tree.atom 1);
have r := (Tree.atom 1).node (Tree.atom 0);
l ≠ r ∧ Tree.denote Bag.sep Bag.emp Bag.single l = Tree.denote Bag.sep Bag.emp Bag.single r

stepByTwo_nonPreorder_satisfies_cancel_hypotheses : have entails := fun x y => x + 2 = y;
have env := fun i => i;
have l := (Tree.atom 0).node (Tree.atom 1);
have r := (Tree.atom 1).node (Tree.atom 2);
¬EntailsRefl entails ∧
  ¬EntailsTrans entails ∧
    SepAssoc Nat.add ∧
      SepComm Nat.add ∧
        RightUnit Nat.add 0 ∧
          SepMonoRight Nat.add entails ∧
            l.atoms.Perm ([1] ++ [0]) ∧
              r.atoms.Perm ([1] ++ [2]) ∧
                entails (denoteAtoms Nat.add 0 env [0]) (denoteAtoms Nat.add 0 env [2]) ∧
                  entails (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).fst)
                    (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).snd)

unitCount_converse_hypothesis_nonvacuous : have l := (Tree.atom 0).node Tree.unit;
have r := Tree.unit.node (Tree.atom 0);
l ≠ r ∧
  ∀ (P : Type) (sep : P → P → P) (emp : P),
    SepAssoc sep → SepComm sep → ∀ (env : Nat → P), Tree.denote sep emp env l = Tree.denote sep emp env r
```

#### Positive and negative examples for definitions

```lean
affineCellEntails_neg_example : ¬affineCellEntails CellModel.empty CellModel.owned

affineCellEntails_pos_example : affineCellEntails CellModel.owned CellModel.empty

atomCount_neg_example : Tree.unit.atomCount ≠ 1

atomCount_pos_example : ((Tree.atom 0).node (Tree.unit.node (Tree.atom 2))).atomCount = 2

atomsAcc_neg_example : Tree.unit.atomsAcc [9] ≠ []

atomsAcc_pos_example : ((Tree.atom 0).node (Tree.atom 1)).atomsAcc [9] = [0, 1, 9]

atomsFast_neg_example : ((Tree.atom 0).node (Tree.atom 1)).atomsFast ≠ [1, 0]

atomsFast_pos_example : (((Tree.atom 3).node Tree.unit).node (Tree.atom 1)).atomsFast = [3, 1]

atoms_neg_example : Tree.unit.atoms ≠ [0]

atoms_pos_example : (((Tree.atom 2).node Tree.unit).node (Tree.atom 0)).atoms = [2, 0]

bag_neg_example : (Bag.single 0).sep (Bag.single 0) ≠ Bag.single 0

bag_pos_example : (Bag.single 0).sep (Bag.single 1) = (Bag.single 1).sep (Bag.single 0)

bientails_neg_example : ¬Bientails taggedValLe (2, 0) (3, 0)

bientails_pos_example : Bientails taggedValLe (3, 0) (3, 5)

boolImp_neg_example : ¬boolImp true false

boolImp_pos_example : boolImp false true

cancelAtoms_neg_example : cancelAtoms [0, 0] [1] ≠ ([], [])

cancelAtoms_pos_example : cancelAtoms [0, 1, 0, 2] [2, 0, 3] = ([1, 0], [3])

cellModel_neg_example : CellModel.owned.sep CellModel.owned ≠ CellModel.owned

cellModel_pos_example : CellModel.empty.sep CellModel.owned = CellModel.owned

checkPermSort_neg_example : checkPermSort ((Tree.atom 0).node (Tree.atom 0)) (Tree.atom 0) = false

checkPermSort_pos_example : checkPermSort (((Tree.atom 2).node Tree.unit).node (Tree.atom 0))
    ((Tree.atom 0).node (Tree.atom 2)) =
  true

denoteAtoms_neg_example : denoteAtoms and false (fun x => true) [0] ≠ true

denoteAtoms_pos_example : denoteAtoms Nat.add 0 (fun i => i + 1) [0, 1, 2] = 6

denoteNonEmpty_neg_example : denoteNonEmpty List.append (fun i => [i]) 0 [1] ≠ [1, 0]

denoteNonEmpty_pos_example : denoteNonEmpty Nat.add (fun i => i + 1) 0 [1, 2] = 6

denote_neg_example : Tree.denote List.append [] (fun i => [i]) ((Tree.atom 0).node (Tree.atom 1)) ≠
  Tree.denote List.append [] (fun i => [i]) ((Tree.atom 1).node (Tree.atom 0))

denote_pos_example : Tree.denote Nat.add 0 (fun i => i + 10) (((Tree.atom 0).node Tree.unit).node (Tree.atom 1)) = 21

leftProj_neg_example : leftProj false true ≠ true

leftProj_pos_example : leftProj true false = true

leftUnitBientails_neg_example : ¬LeftUnitBientails leftProj false Eq

leftUnitBientails_pos_example : LeftUnitBientails taggedSep taggedEmp taggedValLe

listEnv_neg_example : listEnv 0 [10, 20] 5 ≠ 10

listEnv_pos_example : listEnv 0 [10, 20, 30] 1 = 20

nonAssocOp_neg_example : (NonAssocCarrier.a.op NonAssocCarrier.a).op NonAssocCarrier.b ≠
  NonAssocCarrier.a.op (NonAssocCarrier.a.op NonAssocCarrier.b)

nonAssocOp_pos_example : NonAssocCarrier.a.op NonAssocCarrier.emp = NonAssocCarrier.a

rightProj_neg_example : rightProj true false ≠ true

rightProj_pos_example : rightProj false true = true

treeSize_neg_example : Tree.unit.size ≠ 0

treeSize_pos_example : ((Tree.atom 0).node Tree.unit).size = 3

twoCellModel_entails_neg_example : ¬TwoCellModel.cellA.entails TwoCellModel.cellB

twoCellModel_entails_pos_example : TwoCellModel.both.entails TwoCellModel.cellA

twoCellModel_neg_example : TwoCellModel.cellA.sep TwoCellModel.cellA ≠ TwoCellModel.cellA

twoCellModel_pos_example : TwoCellModel.cellA.sep TwoCellModel.cellB = TwoCellModel.both

unitCount_neg_example : ((Tree.atom 0).node Tree.unit).unitCount ≠ 0

unitCount_pos_example : (((Tree.atom 0).node Tree.unit).node Tree.unit).unitCount = 2

unitFree_neg_example : ((Tree.atom 0).node Tree.unit).unitFree = false

unitFree_pos_example : ((Tree.atom 0).node (Tree.atom 1)).unitFree = true
```

#### Other cited lemmas

```lean
boolAndFalse_not_leftUnit : ¬LeftUnit and false

boolAndFalse_not_rightUnit : ¬RightUnit and false

boolAndFalse_not_rightUnitBientails_eq : ¬RightUnitBientails and false Eq

boolAndTrue_rightUnit : RightUnit and true

cellModel_conflict_idemElem : IdemElem CellModel.sep CellModel.conflict

cellModel_entailsRefl : EntailsRefl CellModel.entails

cellModel_not_affineEntails : ¬AffineEntails CellModel.empty CellModel.entails

cellModel_not_sepIdem : ¬SepIdem CellModel.sep

cellModel_owned_not_idemElem : ¬IdemElem CellModel.sep CellModel.owned

finiteSupport_zero : FiniteSupport fun x => 0

leftProj_not_leftUnit : ¬LeftUnit leftProj false

leftProj_rightUnit : RightUnit leftProj false

listAppend_leftUnit : LeftUnit (P := List Nat) List.append []

listAppend_not_commBientails_eq : ¬SepCommBientails (P := List Nat) List.append Eq

listAppend_not_sepComm : ¬SepComm (P := List Nat) List.append

listAppend_rightUnit : RightUnit (P := List Nat) List.append []

listAppend_sepAssoc : SepAssoc (P := List Nat) List.append

natAdd_le_sepMonoLeft : SepMonoLeft Nat.add Nat.le

natAdd_le_sepMonoRight : SepMonoRight Nat.add Nat.le

natAdd_not_sepIdem : ¬SepIdem Nat.add

natAdd_sepAssoc : SepAssoc Nat.add

natAdd_sepComm : SepComm Nat.add

natAdd_zero_idemElem : IdemElem Nat.add 0

natLe_entailsRefl : EntailsRefl Nat.le

natLe_entailsTrans : EntailsTrans Nat.le

natLt_not_entailsRefl : ¬EntailsRefl Nat.lt

nonAssocOp_not_sepAssoc : ¬SepAssoc NonAssocCarrier.op

nonAssocOp_sepComm : SepComm NonAssocCarrier.op

nonAssoc_not_assocBientails_eq : ¬SepAssocBientails NonAssocCarrier.op Eq

not_finiteSupport_const_one : ¬FiniteSupport fun x => 1

optBag_denote : ∀ (t : Tree),
  Tree.denote optBagSep (some Bag.emp) (fun i => some (Bag.single i)) t =
    some (Tree.denote Bag.sep Bag.emp Bag.single t)

rightProj_leftUnit : LeftUnit rightProj false

rightProj_not_rightUnit : ¬RightUnit rightProj false

tagDistLeOne_not_entailsTrans : ¬EntailsTrans tagDistLeOne

taggedSep_assocBientails_valLe : SepAssocBientails taggedSep taggedValLe

taggedSep_commBientails_valLe : SepCommBientails taggedSep taggedValLe

taggedSep_rightUnitBientails_valLe : RightUnitBientails taggedSep taggedEmp taggedValLe ∧ ¬RightUnit taggedSep taggedEmp

twoCellModel_affineEntails : AffineEntails TwoCellModel.empty TwoCellModel.entails
```

## Boundaries

### Non-claims (read before citing any result)

**Package-wide boundaries:**

- **Toy abstraction:** The theorems are about `Toy.SepAC`; they neither establish nor refute the corresponding claims about a production separation-logic verifier or tactic, and no theorem establishes properties of one without an external modeling bridge connecting that logic's connectives, equality/entailment relation, and reification pipeline to `Toy.SepAC`.
- **No reification or alias unification:** All theorems take already-reified `Tree` values and environments `env : Nat → P`; matching `Tree.denote` to a source AST and unifying definitionally equal atoms lie outside the formalization.
- **Sufficiency-only entailment cancellation:** Only the equational theorems (`R1a-iff`, `R1b-iff`, `R1c-iff`, `R3a-iff`) yield `↔` algebraic characterizations. Entailment frame cancellation (`R4a`, `R4b`) gives sufficient conditions only (`Toy.SepAC.totalRelation_cancel_sound_without_laws`).
- **No formal cost semantics and no novelty claims:** Complexity statements (`R5`) are informal counts supported by proved structural size bounds (`atomCount ≤ size`) and a kernel-reducibility execution observation (probe `support/KernelReductionProbe.lean`); no result claims novelty.

**Per-result non-claims:**

**R1a (`R1a-monoid-flattening-normal-form`):**

- This result concerns the denotation of a given syntax tree. It does not show that a reifier produces a tree whose denotation is the original goal.
- Each unit law is tight only in the absence of `SepComm`; with `SepComm`, either unit law implies the other (`Toy.SepAC.leftUnit_of_comm_of_rightUnit`, `Toy.SepAC.rightUnit_of_comm_of_leftUnit`).
- Does not reorder atoms: without `SepComm`, trees with distinct permutations of the same atoms can denote distinct elements (`Toy.SepAC.listAppend_tight_isPerm_sepComm`).
- Treats `Tree.atom i` as opaque: if `env i` is itself a compound `sep` expression in the object logic, `Tree.atoms` does not recursively flatten inside `env i`.

**R1a-iff (`R1a-iff-monoid-flattening-characterization`):**

- The necessity (`→`) direction requires universal quantification over all environments `env : Nat → P` and all syntax trees `t : Tree`; flattening can hold on a restricted subset of trees or environments without the algebraic laws holding globally.
- Does not certify reification from object-logic expressions to `Tree`.

**R1b (`R1b-acu-permutation-soundness`):**

- Atoms are compared by index. Atoms that are equal but have distinct indices, or `sep`-expressions hidden inside an atom, are not identified. Merging such atoms is the reifier's job.
- Not a statement about the cited prototype's assertion type. Applying it there requires the modeling bridge that its `sep`/`emp` satisfy associativity, commutativity and right unit as propositional equalities.
- Does not certify reification (that the reified trees denote the original goal). It says nothing about the cost of the check (see R5) or of definitional unfolding against the goal.
- Requires propositional equality (`=`) for the ACU laws; if `sep` is ACU only up to mutual entailment (`Bientails`), use `Toy.SepAC.bientails_acu_entails_of_common_perm_of_trans_sepMonoRight` instead, which additionally assumes `EntailsTrans entails` and `SepMonoRight sep entails`, takes a residual entailment as a hypothesis, and concludes the one-way entailment `entails (l.denote sep emp env) (r.denote sep emp env)`, not equality (for mutual entailment, apply it in both directions, e.g. with an `entails emp emp` residual when every atom cancels).
- Soundness does not imply completeness: in models with pointwise-idempotent atoms, absorbing conflict elements, or aliased environments, `l.denote = r.denote` can hold while `l.atoms.isPerm r.atoms = false` (`Toy.SepAC.denote_eq_and_isPerm_false_of_idemElem`, `Toy.SepAC.cellModel_incomplete_without_sepIdem`, `Toy.SepAC.bag_aliased_env_denote_eq_not_isPerm`).
- `RightUnit` is required only when trees may differ in their count of `Tree.unit` leaves; when `l.unitCount = r.unitCount` (in particular on `unitFree` trees), `RightUnit` can be dropped (`Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm`).

**R1b-iff (`R1b-iff-acu-soundness-characterization`):**

- The necessity (`→`) direction requires soundness across all environments `env : Nat → P` and all trees `l, r : Tree`; soundness on a restricted class of trees (such as unit-free trees, see `R1c-iff`) or fixed environments does not force `RightUnit`.
- Unlike equality reflection, no analogous `↔` characterization holds for one-way entailment frame cancellation (`Toy.SepAC.totalRelation_cancel_sound_without_laws`).

**R1c-unit-count (`R1c-unit-count-ac-soundness`):**

- Not novel: core Lean's reflective AC normalizer (`Lean.Data.AC`, used by `ac_rfl`) already works on unit-free syntax and treats units as flagged atoms.
- Does not permit `emp`-elimination: changing the number of `Tree.unit` leaves between `l` and `r` requires `RightUnit sep emp` (`Toy.SepAC.boolAndFalse_tight_unitCount_eq`).
- Equal `unitCount` is necessary only when quantified universally over all associative-commutative models, `emp`, and environments (`Toy.SepAC.unitCount_eq_and_isPerm_of_forall_ac_denote_eq`, proved at `Type`); in a single fixed model where `emp` happens to be a unit of `sep` (such as `(Nat, Nat.add, 0)`), trees with unequal `unitCount` still denote equally (`Toy.SepAC.unitCount_eq_not_necessary_in_fixed_model`).

**R1c-unit-free (`R1c-unit-free-ac-soundness`):**

- Not novel: core Lean's reflective AC normalizer (`Lean.Data.AC`, used by `ac_rfl`) already works on unit-free syntax and treats units as flagged atoms.
- Unit-freeness is sufficient, not necessary, for unit-law-free AC normalization: equal `Tree.unit` leaf counts suffice (`Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm`, witnessed by `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_nonvacuous`).
- Does not permit `emp`-elimination: if only one side contains `Tree.unit`, `RightUnit sep emp` becomes mandatory (`Toy.SepAC.boolAndFalse_tight_unitFree_left`, `Toy.SepAC.boolAndFalse_tight_unitFree_right`).

**R1c-iff (`R1c-iff-ac-soundness-characterization`):**

- The `→` direction requires universal quantification over all environments and all equal-unit-count (resp. unit-free) trees.
- Does not establish `RightUnit sep emp` or `LeftUnit sep emp`.

**R2a (`R2a-noncommutative-append-counterexample`):**

- This counterexample is the `SepComm` tightness witness of R1b, restated as a reference point.
- Does not refute `Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units` (R1a): when `l.atoms = r.atoms` (equal lists rather than permuted lists), `List.append` satisfies all hypotheses of R1a (`Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units_nonvacuous`) and hence satisfies normal-form equivalence by R1a.

**R2b (`R2b-nonassociative-three-element-counterexample`):**

- This counterexample is the `SepAssoc` tightness witness of R1b, restated as a reference point alongside the proved minimality lemma `Toy.SepAC.atMostTwo_comm_unital_sepAssoc`.
- The failure already occurs for identical atom sequences `[0, 0, 1]` differing only in tree parenthesization, so replacing `List.isPerm` by strict list equality `l.atoms == r.atoms` still fails without `SepAssoc` (`Toy.SepAC.nonAssoc_tight_flattening_sepAssoc`).

**R2c (`R2c-nonunital-boolean-counterexample`):**

- This counterexample is the `RightUnit` tightness witness of R1b, restated as a reference point.
- Does not show that `Bool.and` lacks a unit altogether (`true` is a unit for `Bool.and`, `Toy.SepAC.boolAndTrue_rightUnit`); it shows that the specific constant `emp` interpreted by `Tree.unit` must satisfy `RightUnit sep emp` whenever trees have unequal `Tree.unit` counts (cf. `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm`).

**R3a (`R3a-free-commutative-monoid-completeness`):**

- Non-idempotence does not suffice for completeness. A model with an absorbing (conflict) element can be incomplete for the check at some environments even without idempotent atom values or aliasing (though not necessarily at every environment, `Toy.SepAC.optBag_absorbing_but_complete`): in `CellModel` at `env _ = .owned` (a single non-idempotent atom), `((0 ∗ 0) ∗ 0)` and `(0 ∗ 0)` both denote `.conflict` (`Toy.SepAC.cellModel_incomplete_without_sepIdem`), and in `TwoCellModel` at `env 0 = .cellA`, `env 1 = .cellB` (two distinct, non-aliased, non-idempotent atoms), `(0 ∗ 0)` and `(1 ∗ 1)` both denote `.conflict` (`Toy.SepAC.twoCellModel_conflict_distinct_atoms_incomplete`).
- Completeness holds relative to the free commutative monoid `Bag` under the generator environment `Bag.single` (equivalently, universal equality across all `Type`-level ACU models and environments; see `Toy.SepAC.isPerm_iff_forall_acu_denote_eq` in `R3a-iff`); `List.isPerm` does not decide semantic equality in any particular non-free separation logic.
- The universal property of `Bag` is not proved in the package; 'free' refers to the standard identification of finitely supported multiplicity maps with finite multisets.
- Even inside `Bag`, completeness fails for arbitrary environments `env : Nat → Bag` that alias distinct atom indices (`Toy.SepAC.bag_aliased_env_denote_eq_not_isPerm`) or map an atom index to `Bag.emp` such as out-of-bounds `listEnv` lookups (`Toy.SepAC.bag_listEnv_oob_denote_eq_not_isPerm`).
- In reifiers that assign distinct indices to syntactically distinct but definitionally equal atoms, `isPerm` returns `false` unless those atoms are merged into a single environment slot beforehand (matching the `aliases` table in `AeneasVerif/aeneas#1551` `Normalize.proveEqAC`).

**R3a-iff (`R3a-iff-bag-characterization`):**

- Holds specifically for `Bag` under the free generator map `Bag.single`; replacing `Bag.single` by an arbitrary `env : Nat → Bag` breaks the `→` direction (`Toy.SepAC.bag_aliased_env_denote_eq_not_isPerm`, `Toy.SepAC.bag_listEnv_oob_denote_eq_not_isPerm`).
- The universal property of `Bag` is not proved in the package.

**R3b (`R3b-pointwise-idempotent-and-conflict-incompleteness`):**

- Idempotence breaks completeness, NOT soundness: `Toy.SepAC.acu_denote_eq_of_isPerm` remains sound on both globally idempotent ACU models (`Bool.or`) and mixed models (`CellModel`, `TwoCellModel`) whenever `l.atoms.isPerm r.atoms = true`.
- Incompleteness is not specific to idempotent models or idempotent atom values: non-idempotent models with an absorbing conflict element break completeness for some environments (`Toy.SepAC.cellModel_incomplete_without_sepIdem` at `env _ = .owned`, `Toy.SepAC.twoCellModel_conflict_distinct_atoms_incomplete` at `env 0 = .cellA`, `env 1 = .cellB`). Neither non-freeness nor an absorbing element breaks completeness for every environment: in `Option Bag` with the absorbing element `none` (`Toy.SepAC.optBagSep`), the generator `some (Bag.single 0)` is not pointwise idempotent and `List.isPerm` is complete for the environment `fun i => some (Bag.single i)` (`Toy.SepAC.optBag_absorbing_but_complete`).
- Deduplicating atoms (set equality) is sound for idempotent `sep` and complete relative to the free idempotent commutative monoid under the generator environment (cf. Agda `Algebra.Solver.IdempotentCommutativeMonoid`; core Lean `ac_rfl` with `IdempotentOp`). It is not complete for arbitrary idempotent models or environments (`Toy.SepAC.boolOr_setCheck_incomplete`), and it is unsound for non-idempotent spatial assertions (`Toy.SepAC.bag_neg_example`).
- "(ℓ ↦ v) ∗ (ℓ ↦ v) = False" for the cited prototype is a derived modeling-bridge claim (consistent with `Resource.not_compatible_self` at `Resource.lean:39`), not a lemma of the prototype.
- Do not conflate affine assertions (`x ∗ y ⊢ x`, `AffineEntails emp entails`) with idempotent/duplicable assertions (`IdemElem sep x`): spatial ownership in an affine heap logic is affine without being idempotent. Whether a pure or persistent assertion satisfies `IdemElem` (a propositional equality `x ∗ x = x`) is not proved here; see the R3b modeling bridge for the qualifications (at best `⊣⊢`, extensionality needed for `=`, and no general `P ∗ P ⊢ P` for persistent non-affine assertions in linear logics).

**R4a (`R4a-frame-cancellation-extensional-acu`):**

- Reflective, kernel-checked cancellation over reified separation-logic syntax is not novel (Malecha, Chlipala & Braibant, ITP 2014, MirrorShard `check_entailment` / `Apply_cancel_sound`); this card contributes the parametric statement over arbitrary unbundled `(P, sep, emp, entails)` and arbitrary common sub-multisets together with its irredundant tightness ledger.
- The hypotheses are sufficient, not necessary. Tightness is relative to the other hypotheses; for a particular `(sep, entails)`, cancellation may be sound without some or all of these laws (`Toy.SepAC.totalRelation_cancel_sound_without_laws`). No characterization of cancellation soundness is claimed.
- Not a model of the cited prototype's cancellation tactic, which matches atoms by unification at meta level and kernel-checks only two AC reorderings plus one monotonicity step.
- `hResidual` is stated over `denoteAtoms` normal forms (with a trailing `emp`). Relating it to a tactic's residual goal (often built without a trailing `emp`) uses `RightUnit`.
- Frame cancellation is a one-way reduction (soundness), NOT an equivalence: in disjoint-heap models (`CellModel` linear and `TwoCellModel` affine), maximal `cancelAtoms` can turn a true entailment into a false residual (`Toy.SepAC.cellModel_cancelAtoms_converse_fails`, `Toy.SepAC.twoCellModel_affine_cancelAtoms_converse_fails`).
- Automatically discharging a fully cancelled `([], [])` residual without supplying `hResidual : entails emp emp` additionally requires `entails emp emp`.
- Omitting `EntailsTrans` relies crucially on `SepAssoc`, `SepComm`, and `RightUnit` being propositional equalities (`=`); when they hold only up to mutual entailment (`Bientails`), `EntailsTrans` cannot be dropped from the remaining hypotheses (`Toy.SepAC.tagDistLeOne_tight_bientails_commonPerm_trans`).
- Permutation decomposition cancels equal syntactic atom indices; it does not perform existential witness instantiation or unification of flexible metavariables.
- Holds in both affine and linear separation logics (neither `AffineEntails emp entails` nor its negation is assumed). Leftover left-hand atoms in `ls` are not weakened away automatically: in an affine logic where `AffineEntails emp entails` holds, a residual goal `entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env [])` (`= emp`) follows from `AffineEntails` and must still be supplied as `hResidual`.

**R4b (`R4b-frame-cancellation-bientails-acu`):**

- The hypotheses are sufficient, not necessary. Tightness is relative to the other hypotheses; for a particular `(sep, entails)`, cancellation may be sound without some or all of these laws (`Toy.SepAC.totalRelation_cancel_sound_without_laws`). No characterization of cancellation soundness is claimed.
- Does not yield `l.denote = r.denote` (propositional equality), only `entails (l.denote ...) (r.denote ...)` (and `Bientails` when residuals hold in both directions).
- Because `Bientails` cannot substitute inside arbitrary host-language contexts without explicit congruence lemmas, rewriting deeply nested subformulas still requires monotonicity of each surrounding connective.
- `hResidual` is stated over `denoteAtoms` normal forms (with a trailing `emp`). Relating it to a tactic's residual goal without trailing `emp` uses `RightUnitBientails` and `EntailsTrans`.
- Holds in both affine and linear separation logics (neither `AffineEntails emp entails` nor its negation is assumed). Leftover left-hand atoms in `ls` are not weakened away automatically: in an affine logic where `AffineEntails emp entails` holds, a residual goal `entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env [])` (`= emp`) follows from `AffineEntails` and must still be supplied as `hResidual`.

**R4c (`R4c-nonmonotone-preorder-cancellation-counterexample`):**

- This counterexample is the `SepMonoRight` tightness witness of R4a and R4b, restated as a reference point.
- Exhibits one non-monotone preorder that breaks cancellation. It does not characterize which non-monotone orders do.

**R4d (`R4d-maximal-cancellation-converse-failure`):**

- `CellModel.entails` is linear (`owned ⊬ empty`). In affine logics, where every assertion entails `emp`, the exhibited residual `owned ⊢ empty` is valid (`Toy.SepAC.affineCellEntails_residual_holds`), so the single-cell linear witness does not by itself show incompleteness for affine logics. An affine witness needs a residual whose right-hand side is not `emp` (provided by `Toy.SepAC.twoCellModel_affine_cancelAtoms_converse_fails`, and also by `Toy.SepAC.cellModel_affine_cancelAtoms_converse_fails` and `Toy.SepAC.boolAnd_affine_cancelAtoms_converse_fails`).
- Refutes completeness/invertibility of maximal syntactic cancellation (`cancelAtoms`), NOT soundness (`Toy.SepAC.acu_entails_of_common_perm_of_sepMonoRight`): a non-maximal common sub-multiset cancellation can still succeed where `cancelAtoms` fails (`Toy.SepAC.partial_cancellation_succeeds_where_cancelAtoms_fails`).
- "(ℓ ↦ v) ∗ (ℓ ↦ v) = False" for the cited prototype is a derived modeling-bridge claim (consistent with `Resource.not_compatible_self`), not a lemma of the prototype.
- No minimality claim: `CellModel` (3 states) and `TwoCellModel` (5 states) are illustrative countermodels. Two-element models already exhibit non-invertible maximal cancellation in the linear case (`Toy.SepAC.boolOr_linear_cancelAtoms_converse_fails`, `(Bool, Bool.or, false)` with the implication order) and in the affine case (`Toy.SepAC.boolAnd_affine_cancelAtoms_converse_fails`, `(Bool, Bool.and, true)`), and `CellModel` under the affine order `affineCellEntails` gives an affine witness with the non-`emp` residual `empty ⊢ owned` (`Toy.SepAC.cellModel_affine_cancelAtoms_converse_fails`).

**R5 (`R5-quasilinear-sort-check-and-size-bounds`):**

- Asymptotic time complexity is informal, not formalized in a machine cost model: `atomsFast` visits each `Tree` constructor once ($O(|t|)$, vs $O(|t|^2)$ worst-case for `Tree.atoms` on left-nested spines) and `List.mergeSort (· ≤ ·)` performs $O(m \log m)$ `Nat` comparisons where $m = \text{atomCount} \le \text{size}$ (vs $O(m^2)$ comparisons for core Lean's `List.isPerm`).
- Each `Nat` comparison in Lean's kernel takes time proportional to the bit-length of the index ($O(\log k)$ for `Nat` literals), though reification assigns dense indices $0, \dots, m - 1$.
- Critical Lean `v4.34.1` kernel caveat: core Lean defines `List.mergeSort` (`Init.Data.List.Sort.Basic`, lines 79-87) by well-founded recursion (`termination_by xs => xs.length`), replaced at runtime via the `@[csimp]` theorem `List.mergeSort_eq_mergeSortTR₂` (`Init.Data.List.Sort.Impl`, line 240). The logical definition uses well-founded recursion, and on the instances probed by `support/KernelReductionProbe.lean` the Lean `v4.34.1` kernel neither reduces `checkPermSort l r` to `true` by `whnf` nor accepts `checkPermSort l r ≡ true`, so `Eq.refl true` does not prove `checkPermSort l r = true` there, whereas the probed structurally recursive `List.isPerm` instance reduces (execution observation; not proved for all `l, r`). A reflective kernel closing its side condition via `mkEqRefl` should therefore keep structural `List.isPerm`, use a structurally recursive sort, or rewrite with `Toy.SepAC.checkPermSort_eq_isPerm_and_size_bounds` first.
- Core Lean's own reflective AC tactic sorts with a structurally recursive insertion sort (`Lean.Data.AC.sort`). It is quadratic but kernel-reducible, which is consistent with the caveat above.

### Attractive stronger conclusions not established

- **"`List.isPerm` requires `LeftUnit` independently of `RightUnit` under `SepComm`."** False: `leftUnit_of_comm_of_rightUnit` and `rightUnit_of_comm_of_leftUnit` make either unit law redundant once `SepComm` is present (contrast `R1a`, where both unit laws are tight without `SepComm`).
- **"Dropping `RightUnit` restricts AC reflection to `unitFree` trees."** Stronger than necessary: equal `Tree.unit` counts (`l.unitCount = r.unitCount`) suffice (`ac_denote_eq_of_unitCount_eq_of_isPerm_nonvacuous`), and `l.unitCount = r.unitCount` holds necessarily if quantified across all `Type`-level AC models (`unitCount_eq_and_isPerm_of_forall_ac_denote_eq`), though not in a fixed unital model (`unitCount_eq_not_necessary_in_fixed_model`).
- **"A non-associative commutative unital countermodel can have size 2."** False: `atMostTwo_comm_unital_sepAssoc` proves every commutative right-unital binary operation on a carrier of cardinality at most 2 is associative.
- **"Non-idempotence (`¬ SepIdem`) guarantees completeness of `List.isPerm`."** False: both single-atom non-idempotent conflict (`cellModel_incomplete_without_sepIdem`) and distinct non-aliased atoms (`twoCellModel_conflict_distinct_atoms_incomplete`) collapse distinct atom multisets to `conflict`.
- **"Set-equality deduplication is complete for arbitrary idempotent models."** False: `boolOr_setCheck_incomplete` shows `(atom 0 ∗ atom 1)` and `atom 0` denote equally in `(Bool, Bool.or, false)` when `env 1 = false`, while deduplicated atom lists `[0, 1]` and `[0]` fail `isPerm`.
- **"Frame cancellation requires `EntailsRefl`, `EntailsTrans`, and `SepMonoLeft` under propositional ACU."** False: `stepByTwo_nonPreorder_satisfies_cancel_hypotheses` exhibits cancellation over a non-reflexive, non-transitive relation (`x + 2 = y`), and `sepMonoLeft_of_comm_of_monoRight` derives `SepMonoLeft` from `SepComm` + `SepMonoRight`.
- **"Any valid entailment over an affine ACU separation logic survives maximal `cancelAtoms` cancellation."** False: `twoCellModel_affine_cancelAtoms_converse_fails` exhibits a valid entailment `(cellA ∗ cellA) ⊢ (cellA ∗ cellB)` in an affine ACU preorder whose maximal `cancelAtoms` residual `cellA ⊢ cellB` is false, whereas non-maximal cancellation can still succeed (`partial_cancellation_succeeds_where_cancelAtoms_fails`).
- **"Because `checkPermSort l r = l.atoms.isPerm r.atoms`, `checkPermSort` drops into `mkEqRefl` in Lean `v4.34.1`."** False for the probed instances: `List.mergeSort` is defined by well-founded recursion (`termination_by xs => xs.length`), and the Lean `v4.34.1` kernel does not reduce the probed `checkPermSort l r` to `true`, so `Eq.refl true` is rejected there (execution observation, `support/KernelReductionProbe.lean`).

### Escape hatches for impossibility and counterexample results

- **Escaping `R3b` (`List.isPerm` incompleteness):** Restrict attention to the free commutative monoid `Bag` with unaliased generator environment `Bag.single` (`bag_dupAtomTree_denote_ne_singleAtomTree`, `R3a-iff`), or hoist atoms whose values are known to satisfy `IdemElem` and resolve conflicts outside the ACU multiset kernel (which real assertions qualify, for example which pure or persistent ones, is a modeling question this package does not settle; see the R3b modeling bridge).
- **Escaping `R4d` (maximal `cancelAtoms` converse failure):** Replace eager maximal cancellation (`cancelAtoms`) with arbitrary sub-multiset partial cancellation (`acu_entails_of_common_perm_of_sepMonoRight`, illustrated by `partial_cancellation_succeeds_where_cancelAtoms_fails`), or extract disjointness contradictions (such as `(x ↦ v₁) ∗ (x ↦ v₂) ⊢ False`) before cancelling.

### Hypotheses with `unknown` tightness

None. Every hypothesis across all 18 cards, including the rows of the supporting-theorem ledgers, is either `tight` (with a proved canonical Lean counterexample theorem) or `harmless` (with its justification stated in the ledger).

### Disproved or dropped statements

None. All 18 results (`R1a`–`R5`), their 3 supplementary theorems (`unitCount_eq_and_isPerm_of_forall_ac_denote_eq`, `unitCount_eq_not_necessary_in_fixed_model`, `isPerm_iff_forall_acu_denote_eq`), and the scope witnesses, supporting counterexamples, and supporting non-vacuity witnesses in `lean/Toy/SepAC/ScopeWitnesses.lean` are proved in full; no statements were disproved or omitted.

### Not examined and unsupported

- **Not examined:** Automated reification tactics from Lean `Expr` to `Tree`; existential-quantifier/magic-wand cancellation; machine-checked asymptotic time bounds for `List.mergeSort` or `List.isPerm` inside a formal cost model.
- **Unsupported:** No Mathlib `Multiset` or `[[require]]` dependencies; `Toy.SepAC` runs purely on Core Lean `v4.34.1` and `Std`.

## Evidence

**Kernel check (2026-11-20).** Built cleanly under Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`) with zero errors and zero warnings. The Lean source contains zero occurrences of `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, `unsafe`, `debug.skipKernelTC`, `#exit`, or `ofReduceBool`/`ofReduceNat`. `Lean.collectAxioms` over all **492** non-internal declarations of `Toy.*` (`audit/axioms.json`) reports only subsets of `{propext, Classical.choice, Quot.sound}`.

**Statement and closure hashes (`audit/statements.json`).** Across all **97** Lean declarations referenced by `results.json`, `statement_sha256` is the SHA-256 of `toString (repr ci.type)` and `closure_sha256` is the SHA-256 of the sorted, newline-joined `c.toString ++ " : " ++ toString (repr cc.type)` (appending `" := " ++ toString (repr v)` for non-theorems) across every package-local constant `c` reachable from `ci.type` (theorem proof bodies excluded).

| Lean name | Card / role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm` | R1c-unit-count result | `Classical.choice`, `Quot.sound`, `propext` | `bbb3d67832939425777f74e6bf680203ccadaf7e41aae8fcb201e8d15a0c9365` | `25698eb3ec35e1de130b0066c821d25de8735716abbe69a93cdf27b1e87ef30c` (18) |
| `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_iff` | R1c-iff result | `Classical.choice`, `Quot.sound`, `propext` | `b5f70f90f1d5aca76302b9484ec396a50e1037122eab21fbb78ac1f36fb12a75` | `25698eb3ec35e1de130b0066c821d25de8735716abbe69a93cdf27b1e87ef30c` (18) |
| `Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_nonvacuous` | R1c-unit-count non-vacuity; R1c-iff non-vacuity | none | `0f8558bdaa3f108c5921d5f3d40b68ba95a5f9fa00ee06314bd65dfd61c8b5d1` | `b7f6bf7d6848421e6e0f0c8b44c7dd77f6c8d44e5c326d05fc25a728351fcc05` (21) |
| `Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm` | R1c-unit-free result | `Classical.choice`, `Quot.sound`, `propext` | `edcbd3fa6beb88c904569195eca60d6346bc117dac8ff2f63a97b04983d675dd` | `bcda5985081f83628c7d960c3a87a84fd9948500426f16706ad2347c669041ad` (18) |
| `Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm_iff` | R1c-iff result | `Classical.choice`, `Quot.sound`, `propext` | `c0d9b8cc25f2f322258d52a4b78eb5afe37881d1bde4fa1fe4f2ec679c844636` | `bcda5985081f83628c7d960c3a87a84fd9948500426f16706ad2347c669041ad` (18) |
| `Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm_nonvacuous` | R1c-unit-free non-vacuity | none | `21984d2092d6549e746870b3faba946978f54c50cd2a127735304c5d6470fe03` | `6e09550755ad9afe2bba9ad123a06d34d971c294b36cb9cad77f514222ee3dfb` (17) |
| `Toy.SepAC.ac_laws_of_unitCount_denote_eq_of_isPerm` | R1c-iff result | `propext` | `b5e3e2533a6423d4fdbc388190ac06a05f24df208b0e9434561468514baf7dc3` | `25698eb3ec35e1de130b0066c821d25de8735716abbe69a93cdf27b1e87ef30c` (18) |
| `Toy.SepAC.ac_laws_of_unitFree_denote_eq_of_isPerm` | R1c-iff result | none | `891b99d76f06b28d06455b92853f20f961b4da02cf2ef8d267b1bfb036c0417e` | `bcda5985081f83628c7d960c3a87a84fd9948500426f16706ad2347c669041ad` (18) |
| `Toy.SepAC.acu_denote_eq_of_isPerm` | R1b result | `Classical.choice`, `Quot.sound`, `propext` | `d0225a412d58381e20262f5060ff298eb931b9eb008bcdaf72d8d58a7e2ac94a` | `90398009e27d76d34eca380054436f27cd138943878533155967679c1a430232` (17) |
| `Toy.SepAC.acu_denote_eq_of_isPerm_iff` | R1b-iff result | `Classical.choice`, `Quot.sound`, `propext` | `6cac28c0153c5f076615fef9f488f14e646d58ff4657074258532eb83cd9863f` | `90398009e27d76d34eca380054436f27cd138943878533155967679c1a430232` (17) |
| `Toy.SepAC.acu_denote_eq_of_isPerm_nonvacuous` | R1b non-vacuity; R1b-iff non-vacuity | `propext` | `43bb7ee51a773d36863041ecc934b3ec9409097fbb56089a3ba09610568b77d4` | `d99eabbc57edeba8a37744d2bcfed2456dc528b1b919d65414ae215b63db7077` (25) |
| `Toy.SepAC.acu_entails_of_cancelAtoms_nonvacuous` | R4a supporting non-vacuity | `propext` | `f20aa0b79376a1d495922f12228e64534af80e145f201007327a869f1c299728` | `802bda30ad9b27fe9d8097d629d8ccbad35ac0e4411225ec4a9a3ac99fe75fb9` (36) |
| `Toy.SepAC.acu_entails_of_cancelAtoms_of_sepMonoRight` | R4a result | `Classical.choice`, `Quot.sound`, `propext` | `c86cbe7d0c38ad912b78d3b53884a830269e09bfc495f9a9823ec0257a86d6a2` | `ed8d2ea769b4c7c84ae5a09fa4c093b19a69de6cf153422833abbeac3aab9ff4` (23) |
| `Toy.SepAC.acu_entails_of_common_perm_nonvacuous` | R4a non-vacuity | `propext` | `373ae6e6dff3775d4222c56b07410a1dcc7bf90508bcb5dd42e6d5fe785bda94` | `4fc7e41039e63b5c8c0acb22ca6b5e87286dd98b3170f4081a441b0632d80d86` (31) |
| `Toy.SepAC.acu_entails_of_common_perm_of_sepMonoRight` | R4a result | none | `075a76e9db08e7f1d1b7df4f834ff1bafed2f70b9334dc39c7fcde2d6f472edf` | `5b05948a3285d0b96d2a3f0f0851378ad5ea33a6f621ff53dc9856a5b1dfb147` (19) |
| `Toy.SepAC.acu_laws_of_denote_eq_of_isPerm` | R1b-iff result | none | `021e64443fbd6dc625eea4f4e22e02e382352e294e03f2f5709c01f155e8586b` | `90398009e27d76d34eca380054436f27cd138943878533155967679c1a430232` (17) |
| `Toy.SepAC.affineCellEntails_residual_holds` | R4d result | `propext` | `6aef7af8a44ab7c8a442844dc76241da4e6d7c6948d2371b90170bad2b717c6e` | `d94249ba6feaf35e79e6d6072443258a014749094f6561e7574579c92dc9d5cb` (38) |
| `Toy.SepAC.assoc_units_of_denote_eq_denoteAtoms` | R1a-iff result | none | `89d91a43a6115bcead5654182cdaa34e88d139aa4ddb44b2427c66f3a1be58ea` | `a9c4748c23ca97222d81ffc2e11ed9887a43e795592638c8d06edb2b5c6554f2` (18) |
| `Toy.SepAC.atMostTwo_comm_unital_sepAssoc` | R2b result | none | `2584a8d06d0abda177f61ea0f8fbd059965dac69694cfe4d4fb0e761b93d972c` | `949ef6ef07de8d02d843af1b26a941ed5abc0ce40456bd68ab7cf11e448d6334` (3) |
| `Toy.SepAC.bag_dupAtomTree_denote_ne_singleAtomTree` | R3b positive control; R3b counterexample (hIdem0); R3b supporting counterexample | `Quot.sound`, `propext` | `ceedae2b59c9757aa2026f0b7d53eb597b2ae7d27bf73568901c3f9f4dfe1fb3` | `994fa012bed4d0aab4d558c521dff969b2079ac3bd33720fc3a075f3a3eeafdf` (29) |
| `Toy.SepAC.bag_tight_denote_eq` | R3a counterexample (hDenote) | `Quot.sound`, `propext` | `3af0a8e3d9417ab4689b5139eead52f3869d84aab8ec6a633295f07d37c206cf` | `5d98dc6afec203e6511095ce4a7c9ccdee398ee4d3f7ccf90c69c378869d7f90` (24) |
| `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_nonvacuous` | R4b supporting non-vacuity | `propext` | `3698f0c4a905121254d1ad0b8ad452d127d07489c2b1c0e26b16a4587ff600b5` | `c8b2e8a1d20a1d2797e2fb5360d78960602abc66673dcf0206a317b25db537e8` (38) |
| `Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight` | R4b result | `Classical.choice`, `Quot.sound`, `propext` | `388dfd871e467168c96b31df1639a5e741104cdf4894296ed429291cd7549586` | `c52014ea2d2c86041af4ca4259914c93286ced5dd76bb93d97a2f9d8c8ae0888` (25) |
| `Toy.SepAC.bientails_acu_entails_of_common_perm_nonvacuous` | R4b non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `0b0580aebbdb4408e7b22b6ca580dde20a2d1de3b042ef5100d56d05cb9178ee` | `5d0d918833af251ef8a11b11fca2ff553593af6e38d13131b3f1e63a60f3a7a6` (24) |
| `Toy.SepAC.bientails_acu_entails_of_common_perm_of_trans_sepMonoRight` | R4b result | none | `0b578a4cc60e0cdc69fca9cc4e77289660e2673d353413569b0c8333e8319596` | `73e59dfc26fac713d97ca991a666ca17b3ccaa54d94f4c5633d1f356fc3c12b6` (21) |
| `Toy.SepAC.boolAndFalse_tight_bientails_cancelAtoms_rightUnit` | R4b supporting counterexample | none | `e898d73d29ddfa3057cac335ff607dcebdf14f29f111fb94cb417cca6e7b2f81` | `f6ecf8287bbcf32f3023c55a447b1de904f615505ec689d7dc04180de1c30b8c` (24) |
| `Toy.SepAC.boolAndFalse_tight_bientails_commonPerm_rightUnit` | R4b counterexample (hRightUnit) | none | `21b96ba9cf957af9bb912638b125f05631f3946ecb8e0df66edb116c7033f4a3` | `13f1c5883dfbc09c720810955e318769579f7b1d463d423259cfed545fdaf8f9` (20) |
| `Toy.SepAC.boolAndFalse_tight_cancelAtoms_rightUnit` | R4a supporting counterexample | none | `58576fb0f40eb7bb82bfafca819c5d933f34862513c578a7429776b675b4f8bb` | `a61df80fed4310742bdc224f9022c7da04dbca0141ccf15e21fba3f1459ab9f0` (22) |
| `Toy.SepAC.boolAndFalse_tight_commonPerm_rightUnit` | R4a counterexample (hRightUnit) | none | `61be493c7624f4a2474dff3cf0d418f89e22cf02d8b5c18d6a8249f5b4859d39` | `bf1ff499e106e3e35dfd82ec07b1681281ba6e8a49b3023e5b8879d55dd5fb80` (18) |
| `Toy.SepAC.boolAndFalse_tight_isPerm_rightUnit` | R1b counterexample (hRightUnit); R2c result; R2c non-vacuity | none | `aff402a4c822e07fb9e5f37025389d48c90c3938c520a5f663d6b598c62c8cf9` | `90398009e27d76d34eca380054436f27cd138943878533155967679c1a430232` (17) |
| `Toy.SepAC.boolAndFalse_tight_unitCount_eq` | R1c-unit-count counterexample (hUnitCount) | none | `183c1fd0f2481a72d6d55656c394c2b881ab8e843afc3131676a7675791f6506` | `25698eb3ec35e1de130b0066c821d25de8735716abbe69a93cdf27b1e87ef30c` (18) |
| `Toy.SepAC.boolAndFalse_tight_unitCount_perm` | R1c-unit-count counterexample (hPerm) | none | `9fbb9a930749f7ea575d517c7e434b5181a33e7dc8982982da1c6989ef0753a0` | `25698eb3ec35e1de130b0066c821d25de8735716abbe69a93cdf27b1e87ef30c` (18) |
| `Toy.SepAC.boolAndFalse_tight_unitFree_left` | R1c-unit-free counterexample (hUFL) | none | `0ad4a2be6941c131bfbed17d5d1b78aa000675b5e12c1f5ac0de0b6b5b42e203` | `bcda5985081f83628c7d960c3a87a84fd9948500426f16706ad2347c669041ad` (18) |
| `Toy.SepAC.boolAndFalse_tight_unitFree_perm` | R1c-unit-free counterexample (hPerm) | none | `b28edd5061c766446ade1282ad2248d1230478b6d7e720a7c8744857d7eef9d7` | `bcda5985081f83628c7d960c3a87a84fd9948500426f16706ad2347c669041ad` (18) |
| `Toy.SepAC.boolAndFalse_tight_unitFree_right` | R1c-unit-free counterexample (hUFR) | none | `a6188b270323e3ce28ba44aaba82f2f443846fd6c0219fa3e725f3d519675eb7` | `bcda5985081f83628c7d960c3a87a84fd9948500426f16706ad2347c669041ad` (18) |
| `Toy.SepAC.boolAndTrue_tight_isPerm_perm` | R1b counterexample (hPerm) | none | `4737f8b93e4b417b964a312b91e764116659e62a2a5ff6382739b05cbb2ff446` | `90398009e27d76d34eca380054436f27cd138943878533155967679c1a430232` (17) |
| `Toy.SepAC.boolAnd_affine_cancelAtoms_converse_fails` | R4d scope witness (cell models not minimal) | `propext` | `a6cc1079f46232e008b46883d8320243d1ef08ed732454ccd4393279e85e0b13` | `1aacf1fee487bb8cbf8a3dcd6b9a923ab80c372bd68ccf89a69e7eacd450bac7` (27) |
| `Toy.SepAC.boolOr_linear_cancelAtoms_converse_fails` | R4d scope witness (cell models not minimal) | `propext` | `faebdabfa5ee2b1b8a79bdd01f14fcb17bd93243390adadce09d724015393077` | `1aacf1fee487bb8cbf8a3dcd6b9a923ab80c372bd68ccf89a69e7eacd450bac7` (27) |
| `Toy.SepAC.boolOr_sepIdem` | R3b supporting non-vacuity | none | `2f6b242d92d128ad73c1527a2c4e2fa894b52c9c39c04650399248b092bf945a` | `4d8da670d6ce90762dc2e8c057286d4bca913830e3c0d4d781e6dd808ad5a3f0` (1) |
| `Toy.SepAC.cancelAtoms_count` | R4a result | `Classical.choice`, `Quot.sound`, `propext` | `4c78296148edc9a00830baf1523d6396eb694e028bc0a62460d179b2395d23e9` | `99a7645ce0eb7b0e0ca1ad888d49f52ff3fc94b0d2c7e360ff09b1cfca953c48` (4) |
| `Toy.SepAC.cancelAtoms_disjoint` | R4a result | `Classical.choice`, `Quot.sound`, `propext` | `181f4c564fd8ddb33a258e4231b1a923b76e1872128b5d1ba7fb07eda7c9ca97` | `99a7645ce0eb7b0e0ca1ad888d49f52ff3fc94b0d2c7e360ff09b1cfca953c48` (4) |
| `Toy.SepAC.cancelAtoms_spec` | R4a result | `Classical.choice`, `Quot.sound`, `propext` | `82575a8c5bac40a2f2bbd6b9a80bf1a07242787767935b97472978c1f2d21ea0` | `99a7645ce0eb7b0e0ca1ad888d49f52ff3fc94b0d2c7e360ff09b1cfca953c48` (4) |
| `Toy.SepAC.capOne_not_sepMonoRight` | R4c result | none | `2fcde3513aa681e0c6949dda5612f96d02384aa824aaeef86b9836fa28c94b5f` | `4336d4bde1ce7db1a1f6d96ba516ffdcdf4b4534d77b4bde8743425dc1a75e95` (4) |
| `Toy.SepAC.capOne_tight_bientails_cancelAtoms_sepMonoRight` | R4b supporting counterexample | none | `93b5a2f679b24013f3c645e12cba0373f1d18af7e627ca575338c7d82f9e6bc0` | `cbac0e61fc77437b46272739ab0ff650415a330dd7cc00773bdfc91eec649f85` (28) |
| `Toy.SepAC.capOne_tight_bientails_commonPerm_sepMonoRight` | R4b counterexample (hMonoRight) | none | `a36817041be917951597fb2386585bd497a4432fcdc17137302cb330d6796533` | `cd1bafecac41f186341bc8fcc0d9026af29565575a9c093813231b65506ed52f` (24) |
| `Toy.SepAC.capOne_tight_commonPerm_sepMonoRight` | R4a counterexample (hMonoRight); R4c result; R4c non-vacuity; R4a supporting counterexample | none | `fb6a4fc6a6b8ff0147c7f9b209e60e3bd543b91ca77d7d4f3a8e79a81715fcad` | `82ecf8657e02490d6e6cc9fdb8ecb3db71a7eb69db165d052c5850bf5ecd13f3` (28) |
| `Toy.SepAC.cellModel_affine_cancelAtoms_converse_fails` | R4d scope witness (cell models not minimal) | `Quot.sound`, `propext` | `b756846b194bbd4b4987e08d22858b6ca902675e92d8d0e7ec3595b414d97246` | `e87ee5d3ada7ef0f7f87dcd0585900f9f1cf14c1703393e302ffaba3668900fb` (41) |
| `Toy.SepAC.cellModel_cancelAtoms_converse_fails` | R4d result; R4d non-vacuity | `propext` | `6ec59cf7a6e6d619fdfd92e5e7c64ccd52951583173c0c80c444437a4c2f99a5` | `c8e1a5882309f7954533985cc0ba5acc1db2966bb52a994e9c863fe59be1cbc9` (40) |
| `Toy.SepAC.cellModel_conflict_idemElem_incomplete` | R3b non-vacuity | `propext` | `759231ab0299fde000ebe08fcb48e80ea47347d88a11255bb5f8d507f8d45efb` | `b7ac5b1435267e6730fb01f3dfbcca29a366aef8bc199aa7689918d3221a03d7` (31) |
| `Toy.SepAC.cellModel_incomplete_without_sepIdem` | R3b result | `propext` | `00c994cec97a689eceb7d3be08cb3de0f66cbb66e831da0fbcc271f4bdffc571` | `b7ac5b1435267e6730fb01f3dfbcca29a366aef8bc199aa7689918d3221a03d7` (31) |
| `Toy.SepAC.checkPermSort_eq_isPerm_and_size_bounds` | R5 result | `Classical.choice`, `Quot.sound`, `propext` | `400bd799720b055fc148588c06b2ae42cae0afe3e32f4ec52f529e554d07aa73` | `5d3e28a2109a1a18dbf250e5b50bbe20c5f0d87a32ceb2c0ce1ec523e60144e2` (22) |
| `Toy.SepAC.checkPermSort_nonvacuous` | R5 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `8ff32f9696ad7c36ef16bed46d0af1cc6fddeb4bb08b7565bc061e48b3b0772f` | `e60aecbcd4b7cc2d7c8f8e0e0fa4f664621049151132ad47b5276d0cac980146` (19) |
| `Toy.SepAC.denote_eq_and_isPerm_false_of_idemElem` | R3b result | none | `31b71418ed4751992969b2c28f7722bf4f0b0d58402bdf1b4197e4088fb5e1eb` | `ebdf284ab2971cd596f4b613644a30fb878f2363d37fe205af7d4cc1e1238805` (17) |
| `Toy.SepAC.denote_eq_and_isPerm_false_of_sepIdem` | R3b result | none | `0748d9a1baaecdcba7b26807adc2ce4720cac93c27ed5e8a47e3471e9b4aa70a` | `7c3abae4619c44ee6809c3bd4a3c3f5bb28caf7f1e5214aa9e4c1f62a9b7e619` (17) |
| `Toy.SepAC.denote_eq_denoteAtoms_iff_assoc_units` | R1a-iff result | none | `6ec91214087a4678f1ad5ddbe8be522a479da78a9988ec2795653bbfe45e44d0` | `a9c4748c23ca97222d81ffc2e11ed9887a43e795592638c8d06edb2b5c6554f2` (18) |
| `Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units` | R1a result | none | `cccec1c2bf10bd267bbc2bc9de8fe39b9d500982fb227be5f98860a68ce9a85f` | `a9c4748c23ca97222d81ffc2e11ed9887a43e795592638c8d06edb2b5c6554f2` (18) |
| `Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units_nonvacuous` | R1a non-vacuity; R1a-iff non-vacuity | `propext` | `bafb99545be8879f780c7897bee25177da4092365fbc003758ab882c2c299d57` | `dfe2c244c784ee4fd233547595f68bd13125e3104dfe561a7870730819b89c34` (4) |
| `Toy.SepAC.idempotent_bool_acu_incomplete` | R3b non-vacuity | none | `f5976f9aa855661eb725b218dc094d61e5c4d4865b91dbd763018e4ae3a4f8b8` | `3b8c0e9178c871dd30399fc3e1b550297847baf7fa7dbc5bce79cd8c928b4cdb` (21) |
| `Toy.SepAC.isPerm_iff_bag_denote_eq` | R3a-iff result | `Classical.choice`, `Quot.sound`, `propext` | `f2cca7d7eb588ba7b534a59c4f3a9162f014112af77ec33eb48c006a14295ec2` | `5d98dc6afec203e6511095ce4a7c9ccdee398ee4d3f7ccf90c69c378869d7f90` (24) |
| `Toy.SepAC.isPerm_iff_forall_acu_denote_eq` | R3a-iff result | `Classical.choice`, `Quot.sound`, `propext` | `83c802292ab28cfbd21c793eba06b06e7d742f6a0f84d740dcb4a020cee9ae4a` | `90398009e27d76d34eca380054436f27cd138943878533155967679c1a430232` (17) |
| `Toy.SepAC.isPerm_of_bag_denote_eq` | R3a result | `Classical.choice`, `Quot.sound`, `propext` | `266d862b1b39e05353f2677927f016f4ec97369ac3ab6d8ceb15a88d00f96e3c` | `5d98dc6afec203e6511095ce4a7c9ccdee398ee4d3f7ccf90c69c378869d7f90` (24) |
| `Toy.SepAC.isPerm_of_bag_denote_eq_nonvacuous` | R3a non-vacuity; R3a-iff non-vacuity | `Quot.sound`, `propext` | `3a540a4e78952aa5697c1d4c128e85c42f48fdc207c968eab61423644bf772f6` | `6b69c2376a7df4b5c7750e6ed7bd60d1a563f665a9fd8d9e86a30ed7e6767db3` (22) |
| `Toy.SepAC.leftProj_tight_flattening_leftUnit` | R1a counterexample (hLeftUnit) | none | `3508777d3db1c94e9a3af6efa6be79bf39c35cba72c7f9bc4c5a11ee1e838574` | `c850f70c961f7e81e6be9729ae1e8bb0c6ee9d8ce2a0b377a6a0c6d5cd87e46b` (18) |
| `Toy.SepAC.listAppend_tight_bientails_cancelAtoms_sepComm` | R4b supporting counterexample | `propext` | `4559dcff182cf25aef27b637111d1e6929d5d593c7a27ed02df2bbcf2b34ba1a` | `14d0332737259f13c6f7693fdb1b833f996fc1b2608cfc35a8855ec61195a0e1` (24) |
| `Toy.SepAC.listAppend_tight_bientails_commonPerm_sepComm` | R4b counterexample (hComm) | `propext` | `d3add973e6f5c44f4419e24603c38d2b64bcc0b671e9e009c6680b1a3a476a37` | `6541d708d76b471bcd7104315ad99198a7a62065c1fa090c4c1bfc5034020e8f` (20) |
| `Toy.SepAC.listAppend_tight_cancelAtoms_sepComm` | R4a supporting counterexample | `propext` | `70d7c02a1d03377cbfe318e6990d198b4a5f363e0a1e1188bb60ba7c2710fa9d` | `7488bb0e1eab0d5ec537efdab1f63bb1cd09834d09d5fbc88c8951239f83cf1e` (22) |
| `Toy.SepAC.listAppend_tight_commonPerm_sepComm` | R4a counterexample (hComm) | `propext` | `9b62afbbc4d38d73810ca2a1eb50a54333a476175d22213bfae6c1c4efd4d9cd` | `12791d9a3abafdfd7cde3e52a46ad7333aa4e35dbe6771fc3123a780c5a3220c` (18) |
| `Toy.SepAC.listAppend_tight_isPerm_sepComm` | R1b counterexample (hComm); R2a result; R2a non-vacuity | `propext` | `de57fd87c18594cf9b0d20dfc823beda0101c71f9729fa580c8d665224717a8e` | `cdc5ca721e8f659f3c44868fd121074ed0a08a7b2b14ed568b841e1baeb49758` (18) |
| `Toy.SepAC.listAppend_tight_unitCount_sepComm` | R1c-unit-count counterexample (hComm) | `propext` | `811cd9d7edcb609ef585779450cb86b52219a962d251e65f64a5256b08917832` | `3c4b3621eaa52f6aba6ddbda4cd11ae7a81390620b131453d603ded497320014` (17) |
| `Toy.SepAC.listAppend_tight_unitFree_sepComm` | R1c-unit-free counterexample (hComm) | `propext` | `2932e40abf3d6f1ed890ee7f134ad197c54f331efceefb32d77efa43ada4e79c` | `139033923c1dc5167fb452bd4b7a364ee880863a0c10c707722b9df09ee59a40` (17) |
| `Toy.SepAC.natAdd_tight_bientails_cancelAtoms_residual` | R4b supporting counterexample | none | `926c57f276ac6439066965096fbce27eefb136645f5c41383c49b578ea1a49ca` | `c52014ea2d2c86041af4ca4259914c93286ced5dd76bb93d97a2f9d8c8ae0888` (25) |
| `Toy.SepAC.natAdd_tight_bientails_commonPerm_leftPerm` | R4b counterexample (hl) | `propext` | `9625885db3af65c3400c98e5caa12172a537fb4ccad17d1e319b2a509b9ab881` | `73e59dfc26fac713d97ca991a666ca17b3ccaa54d94f4c5633d1f356fc3c12b6` (21) |
| `Toy.SepAC.natAdd_tight_bientails_commonPerm_residual` | R4b counterexample (hResidual) | none | `e4a1de19ea09d63a2146b9667bc12980041b616d7dd2f9649922e80a5612b648` | `73e59dfc26fac713d97ca991a666ca17b3ccaa54d94f4c5633d1f356fc3c12b6` (21) |
| `Toy.SepAC.natAdd_tight_bientails_commonPerm_rightPerm` | R4b counterexample (hr) | `propext` | `0ee742f2029b1d215e8cc80a715bdd5de3a512458512b44c919b5bbc19e9d024` | `73e59dfc26fac713d97ca991a666ca17b3ccaa54d94f4c5633d1f356fc3c12b6` (21) |
| `Toy.SepAC.natAdd_tight_cancelAtoms_residual` | R4a supporting counterexample | none | `fa9981a4fb10a09b8a00f614481d596367de30e0d78272f83610a5067bf1e7ca` | `ed8d2ea769b4c7c84ae5a09fa4c093b19a69de6cf153422833abbeac3aab9ff4` (23) |
| `Toy.SepAC.natAdd_tight_commonPerm_leftPerm` | R4a counterexample (hl) | `propext` | `c331f3c5ae36aec7f9116f702c9ac14cd656d6f0703ad4242e7e3cd93d826032` | `5b05948a3285d0b96d2a3f0f0851378ad5ea33a6f621ff53dc9856a5b1dfb147` (19) |
| `Toy.SepAC.natAdd_tight_commonPerm_residual` | R4a counterexample (hResidual) | none | `f7c70564cc1db732f0d75438a01482e1d69b3b3a3249f711c799f82f10ce29eb` | `5b05948a3285d0b96d2a3f0f0851378ad5ea33a6f621ff53dc9856a5b1dfb147` (19) |
| `Toy.SepAC.natAdd_tight_commonPerm_rightPerm` | R4a counterexample (hr) | `propext` | `f034a1b487e65aa7eec12b229187bed53213a1c63eb642511b827c748e85e245` | `5b05948a3285d0b96d2a3f0f0851378ad5ea33a6f621ff53dc9856a5b1dfb147` (19) |
| `Toy.SepAC.nonAssoc_tight_bientails_cancelAtoms_sepAssoc` | R4b supporting counterexample | none | `3a918d1dfd1ec041ff78958e218bf6df5540805112a2ef14973614fc7650fb6c` | `5c0e4e6abdc2b67ae57d4a5aefe1255c84f2a4c547b03db67aa5eb3497a75c99` (32) |
| `Toy.SepAC.nonAssoc_tight_bientails_commonPerm_sepAssoc` | R4b counterexample (hAssoc) | none | `f0e7a3c0c20d24424876b35e6d4d689710c5b83fc0e2099d6a451eaef99df0f3` | `68347f9177fb0c38e248901e24c711fda10051bea49498c84eb56fb0f9e3c91c` (28) |
| `Toy.SepAC.nonAssoc_tight_cancelAtoms_sepAssoc` | R4a supporting counterexample | none | `86c94b929913746c16b3251f979c59ea04f9aeb1c0c1c584fc8a663a28f662a4` | `50b5e0bb4b6990bf997f648204ddf1dc98cf3f840710320254ebfee333585527` (30) |
| `Toy.SepAC.nonAssoc_tight_commonPerm_sepAssoc` | R4a counterexample (hAssoc) | none | `d43bd3ca5f6bdcba0b5621b66822e7a2c0dd7c5234ca8d42e9fa68f2a6a988b4` | `5625dc4726daf2ea374bd928f95601cfb6fd8d3a375e8b6fc29a1321e94837a7` (26) |
| `Toy.SepAC.nonAssoc_tight_flattening_sepAssoc` | R1a counterexample (hAssoc) | none | `95bf5435435544ccc019782d00d683d587a7eeed3bbba40895c7d91679cfc15c` | `5658f4d514e0cf29e5408a070b9cad12608e186da2d3d416f28d0481432304af` (25) |
| `Toy.SepAC.nonAssoc_tight_isPerm_sepAssoc` | R1b counterexample (hAssoc); R2b result; R2b non-vacuity | none | `8523027074954d5e74398fb199d3081af42dd6a4fc97b8b7beb7e6a75b4ed353` | `d21ac016c81d023289209ba8c20f379530ec659874f73eafaa0d58b9c1e554d5` (26) |
| `Toy.SepAC.nonAssoc_tight_unitCount_sepAssoc` | R1c-unit-count counterexample (hAssoc) | none | `9dfd005160528041c1fa97aaff3d7fbff7c14b417ca69699c62f7d6ebcc22659` | `b152ebea10c578fa1bbcda8c70368a2c54cb2470ac21e0497239182da647920e` (25) |
| `Toy.SepAC.nonAssoc_tight_unitFree_sepAssoc` | R1c-unit-free counterexample (hAssoc) | none | `bbcafaa6128307280accf4fb619e3e2c39352ba0db45efa2a97e2c6597113c4d` | `61afc9650e5cd4caa21211f8d4703357c5a9d6c9f8e0e309704a64609fa40abc` (25) |
| `Toy.SepAC.optBag_absorbing_but_complete` | R3b scope witness (absorbing element, complete for one environment) | `Classical.choice`, `Quot.sound`, `propext` | `785d24aa562d49cdca763f67470ba16108f9a66e05f255a6bd278ac94baf5333` | `ed406a8c07e4b7196dae37b898672e72c3da856518843d1c798d0d5f8e628100` (28) |
| `Toy.SepAC.partial_cancellation_succeeds_where_cancelAtoms_fails` | R4d result | `propext` | `1004fbc17242095d5255073922484d1e772c310aaac085f7081e4b5470741925` | `5b25c661316cff3a78ac6617c7ff23bd9d53d4dd6a413e95c34dc80066cfa87e` (31) |
| `Toy.SepAC.rightProj_tight_flattening_rightUnit` | R1a counterexample (hRightUnit) | none | `d14ba2b32d09763269ea942269dff933e6a7824561ee9386c194bf70f3428832` | `73c996cae9ba2bec3dca1772cec2c8122411d14fd841e26ab09a11bb158f265b` (18) |
| `Toy.SepAC.stepByTwo_nonPreorder_satisfies_cancel_hypotheses` | R4a non-vacuity | `Quot.sound`, `propext` | `344efac3075f3d5f8f59f520e64bb0e0b8ae7d1e4b72bb7ac4e8c88769b2da25` | `0b125cbe662d5d457cf08af518448382d3fe93d817ad026bfee030cdf2170954` (23) |
| `Toy.SepAC.tagDistLeOne_tight_bientails_cancelAtoms_trans` | R4b supporting counterexample | `Classical.choice`, `Quot.sound`, `propext` | `c076bd6e30d7479e2c38ebb3e060706e76354485641e5440197c3298197734c9` | `915fee9b1e6d04028598b10c08174d83f5ca9859fec839980846dcafc82f4723` (28) |
| `Toy.SepAC.tagDistLeOne_tight_bientails_commonPerm_trans` | R4b counterexample (hTrans) | `Classical.choice`, `Quot.sound`, `propext` | `c6ff09fd76491c1018e579412fc40dfbaf83f2c33a728d9dbecc3b3253e431ad` | `81b856884f5c33b991fdfd6996d84ecd05cbd02c5d7bf1be876b928ec545e862` (25) |
| `Toy.SepAC.twoCellModel_affine_cancelAtoms_converse_fails` | R4d result; R4d non-vacuity | `propext` | `b7d36b59ba6e51376eb8452f586ba501d9ff59c4981f78ff3a3083390eadddf4` | `d103641bed4dd3f421fcdc3b24efc66db87fd8aeb456a0b4a457e3e882705fa0` (49) |
| `Toy.SepAC.twoCellModel_conflict_distinct_atoms_incomplete` | R3b result | `propext` | `d9dbc864ddc4ff6c8a9c94d50c4f25e3f1d6b7d938e34ee77ab789c9b928335c` | `11f0c357c660512f018e0be880fb8f5996ae1c070a28098532a50087a89855b9` (34) |
| `Toy.SepAC.unitCount_converse_hypothesis_nonvacuous` | R1c-unit-count supporting non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `7bb1c54a20a030f05e3cb10f6fe2862d9d5f4fb1611b36de6f834df8e37e05c7` | `c3cf8422cd20c9d6c73a8d5af221ef247104fac92f49a910311e4a1e39663e03` (14) |
| `Toy.SepAC.unitCount_eq_and_isPerm_of_forall_ac_denote_eq` | R1c-unit-count result | `Classical.choice`, `Quot.sound`, `propext` | `694ca54ab532382a71ca07b8569805c88ca10689d9344c5eaa726776366f7f5c` | `25698eb3ec35e1de130b0066c821d25de8735716abbe69a93cdf27b1e87ef30c` (18) |
| `Toy.SepAC.unitCount_eq_not_necessary_in_fixed_model` | R1c-unit-count result; R1c-unit-count supporting counterexample | none | `89d8b98648844510450d3130213855a161739792aeef04bb823ca57da3a6b908` | `199edb03274f0f1ed84ca9e0a0cae9f79860bc4d1f77a4d97d0b410d9f654547` (14) |

**Kernel-reduction probe (2026-11-20).** `support/KernelReductionProbe.lean` elaborates four closed Boolean terms (`([2, 0] : List Nat).isPerm [0, 2]`, `Lean.Data.AC.sort [3, 1, 2] == [1, 2, 3]`, `([3, 1, 2] : List Nat).mergeSort (fun a b => decide (a ≤ b)) == [1, 2, 3]`, and `checkPermSort ((atom 2 ∗ unit) ∗ atom 0) (atom 0 ∗ atom 2)`) and asks the Lean `v4.34.1` kernel directly, without the elaborator's reduction heuristics, whether `Lean.Kernel.whnf` reduces each term to `Bool.true` and whether `Lean.Kernel.isDefEq` accepts it as definitionally equal to `true` (the check behind accepting `Eq.refl true` as a proof of `t = true`). It fails with an error if any answer differs from the expected answer recorded in the file. Run from `lean/` after `lake build` with `lake env lean ../support/KernelReductionProbe.lean`; recorded output:

```text
KERNEL_PROBE List.isPerm: kernel whnf = true: true; kernel isDefEq with true: true; kernel exception: false; expected: true; as expected
KERNEL_PROBE Lean.Data.AC.sort: kernel whnf = true: true; kernel isDefEq with true: true; kernel exception: false; expected: true; as expected
KERNEL_PROBE List.mergeSort: kernel whnf = true: false; kernel isDefEq with true: false; kernel exception: false; expected: false; as expected
KERNEL_PROBE checkPermSort: kernel whnf = true: false; kernel isDefEq with true: false; kernel exception: false; expected: false; as expected
KERNEL_PROBE summary: all answers as expected
true
```

The probe covers only these instances and this toolchain release; it does not show that no instance of `checkPermSort` reduces.

**Primary sources (observed and verified 2026-11-20):**

- **Lean 4 core (`leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`):** Inspected directly at this commit; paths are relative to the root of the `leanprover/lean4` repository (an installed `v4.34.1` toolchain ships the same files under `src/lean/`, e.g. `src/lean/Init/Data/AC.lean`): `src/Init/Data/AC.lean` (`Expr` lines 17–20, `Variable` 24–26, `Context` 28–34, `sort` 76–80, `mergeIdem` 82–93, `removeNeutrals` 95–106, `norm` 108–112, `Context.eval_toList` 330–335, `Context.eq_of_norm` 342–345); `src/Lean/Meta/Tactic/AC/Main.lean` (line 128 `Context.eq_of_norm` with `mkEqRefl (mkConst ``Bool.true)`); `src/Init/Tactics.lean` (`ac_rfl` line 455, `ac_nf` line 1648); `src/Init/Data/List/Basic.lean` (`List.Perm` line 1858, `List.isPerm` line 1886); `src/Init/Data/List/Perm.lean` (`perm_iff_count` line 426, `isPerm_iff` line 448, `Perm.eq_of_pairwise` line 530); `src/Init/Data/List/Sort/Basic.lean` (`mergeSort` lines 79–87); `src/Init/Data/List/Sort/Impl.lean` (`@[csimp] mergeSort_eq_mergeSortTR₂` line 240); `src/Init/Data/List/Sort/Lemmas.lean` (`mergeSort_perm` line 280, `pairwise_mergeSort` line 305).
- **Malecha, G., Chlipala, A., & Braibant, T. (2014):** "Compositional Computational Reflection", *ITP 2014*, LNCS 8558, pp. 374–389, `doi:10.1007/978-3-319-08970-6_24`. Bibliographic record verified and author manuscript PDF inspected directly (Listing 1 `sexpr := Star | Opaque | Emp`, `sexprD`, `check_entailment`, `check_entailment_sound`, prose "erases all ∅ terms and crosses common terms off both sides of the entailment", and `Theorem Apply_cancel_sound`).
- **Boutin, S. (1997):** "Using reflection to build efficient and certified decision procedures", *TACS '97*, LNCS 1281, pp. 515–529, `doi:10.1007/BFb0014565`. Bibliographic record cited; full text not consulted directly.
- **Grégoire, B., & Mahboubi, A. (2005):** "Proving Equalities in a Commutative Ring Done Right in Coq", *TPHOLs 2005*, LNCS 3603, pp. 98–113, `doi:10.1007/11541868_7`. Bibliographic record and abstract cited; full text not consulted directly.
- **Braibant, T., & Pous, D. (2011):** "Tactics for Reasoning Modulo AC in Coq", *CPP 2011*, LNCS 7086, pp. 167–182, `doi:10.1007/978-3-642-25379-9_14`. Bibliographic record and abstract verified (associative-only operators, neutral elements, uninterpreted function symbols, user-defined equivalence relations); full text not consulted directly.
- **Chlipala, A. (2011):** "Mostly-automated verification of low-level programs in computational separation logic", *PLDI 2011*, pp. 234–245, `doi:10.1145/1993498.1993526` (ACM SIGPLAN Notices 46(6) reprint `doi:10.1145/1993316.1993526`). Bibliographic record cited (Step 7 cancellation and `[< p >]` pure predicate lifting); full text not consulted directly.
- **Chlipala, A. (2013):** *Certified Programming with Dependent Types*, MIT Press, ISBN `978-0-262-02665-9`. Chapter 15 ("Proof by Reflection", section "A Monoid Expression Simplifier") cited per the online book table of contents and chapter extract.
- **Appel, A. W. (2011) & Appel, A. W. et al. (2014):** "Verified Software Toolchain", *ESOP 2011*, LNCS 6602, pp. 1–17, `doi:10.1007/978-3-642-19718-5_1` (overview); *Program Logics for Certified Compilers*, Cambridge University Press, ISBN `978-1-107-04801-0`: bibliographic record only; chapter contents were not verified at the source, so the cards cite the book without a chapter-level content claim.
- **Verified Software Toolchain repository (`PrincetonUniversity/VST`, commit `d50ac1969f9f6586621895eb043ccf08a165f731`):** `floyd/seplog_tactics.v` inspected directly at this commit: `Ltac cancel_frame` (line 346), initial `Ltac cancel` (line 468), and effective redefinition `Ltac cancel ::= new_cancel cancel_local_tac` (line 914).
- **Krebbers, R., Timany, A., & Birkedal, L. (2017):** "Interactive proofs in higher-order concurrent separation logic", *POPL 2017*, pp. 205–217, `doi:10.1145/3009837.3009855`. Bibliographic record and published description verified (`env persistent` / `env spatial` in `Record envs`, reflective context management, and `iFrame` §4.2).
- **Krebbers, R. et al. (2018):** "MoSeL: a general, extensible modal framework for interactive proofs in separation logic", *Proc. ACM Program. Lang.* 2(ICFP), pp. 1–30, `doi:10.1145/3236772`. Bibliographic record and abstract verified (generic BI interface supporting both affine and linear separation logics).
- **Charguéraud, A. (2020):** "Separation Logic for Sequential Programs (Functional Pearl)", *Proc. ACM Program. Lang.* 4(ICFP), Article 116, `doi:10.1145/3408998`. Bibliographic record and cited sections verified (Remark 3.10 on one-sided/two-sided monotonicity equivalence, Lemma 3.11 `single-conflict`, Appendix K `xsimpl`). Appendix K was re-read in the author PDF (pp. 116:42–43): it contains the generic sentence that 'there are a number of simplifications that are technically not equivalence-preserving, yet nearly always desirable to perform' and the rule list of Definition K.1, whose rule (4) removes a predicate `H` (other than `⊤⊤`) occurring on both sides; it does not say which rules are not equivalence-preserving.
- **Agda standard library (`agda/agda-stdlib`, tag `v2.1`, commit `97bc55e47367c562b3032bf104f2a00b19716f88`):** `src/Algebra/Solver/Monoid.agda`, `src/Algebra/Solver/CommutativeMonoid.agda` (`Normal n = Vec ℕ n`, bag normal form), and `src/Algebra/Solver/IdempotentCommutativeMonoid.agda` (`Normal n = Vec Bool n`, bit-vector set normal form) inspected directly at this tag.
- **Mathlib4 (`leanprover-community/mathlib4`, commit `4dbecbe2ebe515d6bfb36d0685092eed09f9d1fd`):** `Mathlib/Data/Multiset/Defs.lean` (`Multiset.coe_eq_coe` at line 100) inspected directly at this commit (prior art only; not a dependency).
- **Context only (open, unmerged PR, excluded from `REPORT.json` subjects):** `AeneasVerif/aeneas` PR `#1551` ("Separation logic over the byte heap", head commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), `backends/lean/Aeneas/SepLogic/{Tactic/Normalize.lean, Tactic/Matchers.lean, Lemmas.lean, Resource.lean}` inspected directly at the pinned SHA.

## Revalidation

Requirements: `elan` (which selects the toolchain pinned in `lean/lean-toolchain`) and `python3`.

1. **Primary full revalidation (from the package root directory):**

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` into a temporary directory (leaving the package untouched), runs `lake build`, scans all Lean sources for `sorry`/`admit`/`native_decide`/`axiom`, compiles and runs an axiom-audit program computing `Lean.collectAxioms` on every declaration in the `Toy` library (failing on any axiom outside `{propext, Classical.choice, Quot.sound}`), and recomputes `statement_sha256` (`toString (repr ci.type)`) and `closure_sha256` (the sorted newline-joined `name : repr type` lines, plus ` := repr value` for non-theorems, across every package-local constant reachable from `ci.type`, excluding theorem bodies) for every Lean name referenced in `results.json` and `audit/statements.json`, asserting exact equality with `audit/statements.json` and printing `REVALIDATED` on exit status 0.

2. **Manual `elan` / `lake` / `python3` audit using `lean/RevalidationAudit.lean`:**

`lean/RevalidationAudit.lean` lies outside the `Toy` library target, fails on any `axiom`/`opaque` declaration or non-standard axiom, and prints `AXIOM_JSON ...` plus one `STATEMENT_JSON ...` line per card-referenced declaration:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/sepac_audit.out
python3 - <<'EOF'
import hashlib, json

ax_rec = json.load(open("../audit/axioms.json"))["declarations"]
st_rec = json.load(open("../audit/statements.json"))["statements"]
st_got = {}
ax_got = None

for line in open("/tmp/sepac_audit.out", encoding="utf-8"):
    if line.startswith("AXIOM_JSON "):
        ax_got = json.loads(line[len("AXIOM_JSON "):])["declarations"]
    elif line.startswith("STATEMENT_JSON "):
        s = json.loads(line[len("STATEMENT_JSON "):])
        st_got[s["name"]] = {
            "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
            "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
            "closure_size": len(s["closure"]),
        }

assert ax_got == ax_rec, "axiom mismatch"
bad = [n for n in st_rec if st_got.get(n) != st_rec[n]]
print(f"{len(ax_got)} declarations audited; {len(st_rec)} statements checked; {len(bad)} mismatches: {bad}")
assert not bad
EOF
```

3. **Kernel-reduction probe for the `R5` execution observation:**

```sh
cd lean
lake build
lake env lean ../support/KernelReductionProbe.lean
```

The last `KERNEL_PROBE` line must read `KERNEL_PROBE summary: all answers as expected`; otherwise the command fails with an error naming the unexpected answers. A passing run re-establishes the observation for the probed instances on the selected toolchain only.

4. **Spot-checking a single theorem's axioms without Python:**

```sh
cd lean
printf 'import Toy\n#print axioms Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm\n' > /tmp/SepACSpotCheck.lean
lake env lean /tmp/SepACSpotCheck.lean
```

On another Lean release, `repr`-based statement and closure hashes may differ even when the underlying mathematical statements are unchanged; in that situation rebuild, check axioms, and compare the pretty-printed `#check` output against the blocks recorded in **Findings**. Passing revalidation confirms the Lean kernel checks and recorded statement identities; modeling-bridge claims in **Findings** are revalidated separately by inspecting the recorded revisions and primary sources above.
