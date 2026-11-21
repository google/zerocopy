# Clausal proof certificates: RUP, RAT, and deletion soundness in a toy Lean model

## Summary

This package is a self-contained, Mathlib-free Lean 4 development of a **toy model** of clausal
unsatisfiability certificates (the RUP, DRUP, DRAT, and LRAT styles) and of what each certificate
step preserves. It contains 22 kernel-checked results (13 theorems and 9 concrete counterexamples),
15 secondary theorems attached to them, a canonical-form counterexample for every hypothesis marked
tight, and a non-vacuity witness for every result. The summary sentences below are each result's
plain-language claim with secondary conclusions dropped; hypotheses are kept as stated. Every
result also has **non-claims**, listed first under **Boundaries**; read them before relying on a
result. Model–system relation: none proved. These are statements about the toy model; they
neither establish nor refute the corresponding claims about real certificate checkers
(drat-trim, the Lean 4 core LRAT checker used by `bv_decide`, cake_lpr). Claims about real
checkers (drat-trim, the Lean 4 core LRAT checker) are separate `derived (modeling bridge)`
statements, never theorems.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Distinctions a design should retain (each restates results below with their hypotheses):

- If `RUP F C`, adding `C` to `F` preserves the set of models (`rup-implies-entails`); if `RAT F C` and `F` is satisfiable, `C :: F` is satisfiable (`rat-addition-preserves-satisfiability`), but a RAT addition need not preserve the set of models (`rat-addition-not-equivalence`).
- For every addition check that maps satisfiable formulas to satisfiable formulas and every stateless deletion policy, acceptance by the generic checker `checkGen` implies unsatisfiability (`refutation-checker-sound-generic`; DRAT instance: `drat-checker-sound-unsat`). The SAT checker `naiveSatCheck`, which applies deletions unchecked and tests the claimed assignment against the final formula, is unsound (`naive-sat-check-unsound-with-deletions`); the proved repairs are listed with that result.
- For the toy DRAT checkers, applying versus ignoring unit-clause deletions separates the accepted certificates in both directions (`operational-accepts-specified-rejects`, `specified-accepts-operational-rejects`); for the toy DRUP checker with all-copies syntactic deletion, acceptance by the checker that applies every deletion implies acceptance under every stateless policy (`drup-honor-all-strictest`).
- Acceptance by the toy hint replay `lratRupCheck` implies RUP (`lrat-hint-replay-implies-rup`); the strawman `sloppyHintReplay`, which omits the per-hint uniqueness check, accepts a refutation of a satisfiable formula (`sloppy-hint-replay-unsound`); and if `C` has no complementary pair of literals, no clause of `F` repeats a literal, and `C` is RUP with respect to `F`, then some hint list for `C` is accepted by `lratRupCheck` (`lrat-hint-replay-complete-wellformed`).

Results (plain-language claims):

*What a single certificate step preserves.*

- **`rup-implies-entails`** (`rup_implies_entails`; theorem, T0): If unit propagation over F, started from the trail that assumes every literal of the clause C false, reaches a conflict within some finite budget (RUP F C), then every total assignment that satisfies F satisfies C (Entails F C).
- **`entails-not-implies-rup`** (`entails_not_implies_rup`; counterexample, T0): The unsatisfiable formula fullSquare (all four binary clauses over x1, x2) entails the empty clause, but the empty clause is not RUP with respect to it at any budget.
- **`rat-witness`** (`ratOn_witness_satisfies`; theorem, T0): If p is a literal of C, C is RAT on p with respect to F (for every clause D of F containing the complement of p, the clause C followed by the literals of D other than that complement is RUP with respect to F), and a satisfies F, then ratWitness a C p -- a itself if a satisfies C, otherwise a with p made true -- satisfies C and F together.
- **`rat-addition-preserves-satisfiability`** (`rat_addition_preserves_satisfiability`; theorem, T0): If C is RAT on its first literal with respect to F (RAT F C; in particular C is nonempty) and F is satisfiable, then C :: F is satisfiable.
- **`rat-addition-not-equivalence`** (`rat_addition_not_equivalence`; counterexample, T0): The clause x0 is RAT with respect to the formula x1 (no clause contains not x0), yet the model x1 = true, x0 = false of x1 is not a model of x0 and x1; so RAT addition does not in general preserve equivalence, and a RAT clause need not be entailed.
- **`rup-implies-rat`** (`rup_implies_rat_of_ne_nil`; theorem, T0): If C is nonempty and RUP with respect to F, then C is RAT on its first literal with respect to F.
- **`rat-check-depends-on-pivot-order`** (`rat_check_depends_on_pivot_order`; counterexample, T0): With respect to the formula not x0, the clause x0 or x1 is RAT on its second literal x1 but neither RUP nor RAT on its first literal, while the reordered clause x1 or x0 is RAT; the budgeted first-literal checker ratCheck rejects x0 or x1 at every budget and accepts x1 or x0 at budget 0, so its verdict depends on literal order.

*UNSAT soundness of certificate checkers.*

- **`refutation-checker-sound-generic`** (`checkGen_sound_unsat_of_addCheck_preserves_sat`; theorem, T0): For every addition check addCheck and every deletion policy ignore: if addCheck maps satisfiable formulas to satisfiable formulas (for all F and C, addCheck F C = true and F satisfiable imply C :: F satisfiable), then for every certificate π and formula F, acceptance by the generic checker checkGen addCheck ignore F π (every addition up to and including the first accepted empty clause passes addCheck; deletions are applied as the policy says; later steps are not examined) implies that F is unsatisfiable.
- **`drat-checker-sound-unsat`** (`checkDRAT_sound_unsat`; theorem, T0): For every propagation budget fuel and every deletion policy ignore (in particular honorAll, which applies every deletion, and ignoreUnitDeletions, which ignores deletions of clauses of list length one): if checkDRAT fuel ignore accepts a certificate for F -- every addition up to and including the first accepted empty clause passes rupCheck, or else ratCheck on its first literal, at budget fuel with respect to the current formula -- then F is unsatisfiable.
- **`drat-steps-preserve-satisfiability-forward`** (`addOK_preserves_satisfiability`; theorem, T0): If an addition passes the budgeted DRAT check addOK at some budget (rupCheck succeeds, or ratCheck succeeds on the first literal, with respect to F) and F is satisfiable, then C :: F is satisfiable; contrapositively, if the check passes and C :: F is unsatisfiable, then F is unsatisfiable.

*Deletions and SAT verdicts.*

- **`naive-sat-check-unsound-with-deletions`** (`naiveSatCheck_unsound_with_deletions`; counterexample, T0): The checker naiveSatCheck replays a certificate with the DRAT addition check, applies every deletion without checking it, and then tests the claimed assignment only against the final formula. It is unsound: the certificate 'delete x0' contains a deletion, and for the unsatisfiable formula x0 and not x0 naiveSatCheck accepts the all-false assignment at every budget.
- **`naive-sat-check-sound-without-deletions`** (`naiveSatCheck_sound_of_noDeletions`; theorem, T0): If the certificate contains no deletion step and naiveSatCheck accepts the assignment a, then a satisfies the original formula F (the final formula contains every original clause).
- **`rup-checked-deletions-sat-sound`** (`satCheckRupDel_sound`; theorem, T1): If satCheckRupDel accepts the assignment a for the formula F and the certificate π at some budget -- that is, the replay succeeds, with every deletion of a clause C from the current formula passing rupCheck with respect to that formula with all copies of C removed, every addition passing the DRAT check addOK with respect to the current formula, and a satisfying the final formula -- then a satisfies F.
- **`rat-checked-deletions-sat-backward`** (`replayRatDel_sat_backward`; theorem, T1): If replayRatDel replays the certificate π from F at some budget and ends in G -- every deletion of a clause C from the current formula passing the DRAT addition check addOK with respect to that formula with all copies of C removed, and every addition passing addOK with respect to the current formula -- and G is satisfiable, then F is satisfiable.
- **`rat-after-deletion-not-rat-wrt-original`** (`rat_after_deletion_not_rat_wrt_original`; counterexample, T0): Starting from the satisfiable formula not x0, the certificate 'delete not x0, add x0' replays successfully (x0 is RAT with respect to the empty formula), yet x0 is neither RUP nor RAT with respect to the original formula and the original formula together with x0 is unsatisfiable.

*Specified versus operational deletion semantics.*

- **`operational-accepts-specified-rejects`** (`operational_accepts_specified_rejects`; counterexample, T1): For x0 and not x0 with the certificate 'delete x0, add the empty clause', the operational checkers (DRAT and DRUP, which ignore the deletion of the unit clause x0) accept at budget 1, while the specified checkers (which apply every deletion) reject at every budget; so, for both DRAT and DRUP, operational acceptance does not in general imply specified acceptance.
- **`specified-accepts-operational-rejects`** (`specified_accepts_operational_rejects`; counterexample, T1): For not x0 together with fullSquare and the certificate 'delete not x0, add x0, add x1, add the empty clause', the specified DRAT checker accepts at budget 3 (after the deletion, x0 is RAT because no clause contains not x0), while the operational DRAT checker, which keeps not x0, rejects at every budget; so for DRAT, ignoring unit deletions can reject certificates the specified semantics accepts.
- **`drup-honor-all-strictest`** (`checkDRUP_honorAll_implies_any_policy`; theorem, T1): For the DRUP checker (every addition must pass rupCheck at the given budget) with all-copies syntactic deletion, for every budget, every (stateless) deletion policy, every certificate, and all formulas F and G: if G contains every clause of F (FormulaSub F G) and the checker that applies every deletion accepts the certificate for F, then the checker with that policy accepts it for G.

*Hint-driven (LRAT-style) checking.*

- **`lrat-hint-replay-implies-rup`** (`lrat_hint_replay_implies_rup`; theorem, T0): If replaying the hinted clauses of F in order from the negation of C succeeds -- each hinted clause has exactly one non-falsified literal occurrence, which is pushed on the trail (it may already be there), until a hinted clause has no non-falsified literal occurrence, after which remaining hints are not examined -- then budgeted propagation from the negation of C reaches a conflict within (number of hints) rounds, so C is RUP with respect to F and F entails C.
- **`lrat-hint-order-matters`** (`lrat_hint_order_matters`; counterexample, T0): The empty clause is RUP with respect to chain3 and the hint list [0, 1, 2] is accepted, but the same clauses in the order [1, 0, 2] are rejected because clause 1 is not unit under the empty trail.
- **`sloppy-hint-replay-unsound`** (`sloppy_hint_replay_unsound`; counterexample, T0): A hint replay that assigns the first non-falsified literal of each hinted clause without checking that it is the only one accepts the hints [0, 1] as a refutation of the satisfiable formula (x0 or x1) and not x0, while the unit-checking replay rejects them.
- **`lrat-hint-replay-complete-wellformed`** (`lratRupCheck_complete_of_wellformed`; theorem, T1): If C contains no complementary pair of literals (NonTautological C), no clause of F repeats a literal (DupFreeClauses F), and C is RUP with respect to F, then some hint list is accepted by lratRupCheck F C. Each side condition is tight: dropping either one admits an instance in which C is RUP and every hint list is rejected (lratRupCheck_incomplete_tautology, lratRupCheck_incomplete_dup_lits).

Non-claims for every result are listed first under **Boundaries**.

## Applicability

### Model fidelity

This is a **toy model**, written to make the logical structure of clausal certificate checking
precise, not a model of any particular implementation. Its definitions (quoted verbatim under
**Findings → Definitions**) are:

- Variables are natural numbers; a literal is a variable with a polarity (`Lit`), with no
  "nonzero integer" encoding. Clauses are lists of literals and formulas are lists of clauses, so
  clauses may repeat literals, formulas may repeat clauses, and order is significant wherever a
  definition inspects positions. Assignments are total functions `Nat → Bool`; all semantic notions
  (`Satisfies`, `Satisfiable`, `Entails`, `Equivalent`, `Equisatisfiable`) are over total
  assignments of all variables.
- Unit propagation (`unitProp`) is a round-based propagator with an explicit budget (`fuel`): each
  round adds every literal forced by some clause, and a conflict is a complementary pair on the trail
  or a clause with every literal falsified. `RUP F C` means propagation from the negation of `C`
  reaches a conflict at **some** budget; `rupCheck fuel F C` is the budgeted test. `RAT F C` is RAT on
  the first literal of `C`; `RATOn F C p` is RAT on an arbitrary literal `p` and deliberately does
  not include `p ∈ C`.
- A certificate is a list of `Step.add C` / `Step.del C`. Deletion (`deleteClause`) removes **every**
  syntactically equal copy of the clause (lists compared exactly, so literal order matters). A
  `DeletionPolicy` is a **stateless** function of the current formula and the deleted clause that
  decides whether to ignore the deletion; `honorAll` applies every deletion (the "specified"
  semantics) and `ignoreUnitDeletions` ignores deletions of clauses of list length one (the
  "operational" semantics). The generic UNSAT checker `checkGen` stops at the first accepted addition
  of the empty clause.
- SAT-certificate replays (`naiveSatCheck`, `satCheckRupDel`, `replayRatDel`) and the LRAT-style hint
  replays (`lratRupCheck`, `lratRupCheckDedup`, the strawman `sloppyHintReplay`) are defined in the
  same style. Hint identifiers are positions in the current formula.

**What real systems the definitions are meant to capture, and known gaps.** The definitions are
meant to capture the logical core of DRUP/DRAT checking as performed by drat-trim and of LRAT RUP-hint
checking as performed by the Lean 4 core checker `Std.Tactic.BVDecide.LRAT.check` (used by
`bv_decide`), and of the certificate-checking setting of verified checkers such as cake_lpr. None of
these systems was executed, and none of their code is modeled. Known gaps, each stated again in the
non-claims of the results it affects:

- drat-trim (repository `marijnheule/drat-trim`, `drat-trim.c` at commit
  `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`) sorts the literals of each clause and removes duplicate
  literals on input,
  deletes one matching stored copy per deletion step, skips deletions of unit clauses and of clauses
  that are the reason of a top-level assignment outside its `FORWARD_SAT` mode (a history-dependent
  rule, not a stateless `DeletionPolicy`), and in its default `BACKWARD_UNSAT` mode skips RAT
  candidate clauses not marked active. The toy model has none of these behaviors.
- The Lean 4 core LRAT checker (Lean `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`)
  uses clause identifiers that survive deletions, RAT hints, and clauses with the invariants
  `nodupkey` and `nodup`; the toy hint replay models only RUP hints over positional identifiers.
- Propagation in production checkers uses watched literals and runs to a fixpoint; the toy
  round-based propagator with a budget is intended to derive the same conflicts given enough rounds,
  which is a modeling assumption, not a theorem.
- cake_lpr and the other verified checkers in the prior art are cited by their papers only; no
  source revision of them was examined and no claim is made about them.

### Relationship of the subjects

The Lean 4 toolchain release is the checker of every theorem in this package. The papers listed as
subjects are prior art for the definitions and for the known results restated here (tiers `T0` and
`T1`); citations attribute only what was read, as recorded in each card. The drat-trim commit and the
Lean 4 core sources at the toolchain's commit are compared with the toy definitions only through
`derived (modeling bridge)` statements in **Findings**; they are not dependencies of the Lean project.

### Lean version and project

- Lean `leanprover/lean4:v4.34.1` (pinned in `lean/lean-toolchain`); **no Mathlib**, no Lake
  dependencies (`lean/lakefile.toml` declares one library, `ToyDrat`, and no `[[require]]`).
- Library modules: `ToyDrat/Basic.lean` (syntax and semantics), `ToyDrat/UnitProp.lean`
  (propagation), `ToyDrat/RupRat.lean` (RUP and RAT), `ToyDrat/Certificate.lean` (certificates,
  policies, checkers), `ToyDrat/Lrat.lean` (hint replay), `ToyDrat/Cards.lean` (tightness and
  non-vacuity witnesses), `ToyDrat/Supplement.lean` (further witnesses). All declarations live in the
  namespace `Toy.Drat`; the Findings below omit that prefix.
- `lean/RevalidationAudit.lean` (outside the library target) prints the axioms of every declaration
  that `results.json` references.

## Findings

### Notation

In prose, `x0` is `Lit.p 0` (the positive literal of variable 0) and `not x0` is `Lit.n 0`; a clause
is written as a disjunction (`x0 or not x1` is `[Lit.p 0, Lit.n 1]`) and a formula as a conjunction
of clauses; "the empty clause" is `[]` and "the empty formula" is `[]`. `C :: F` is the formula `F`
with the clause `C` added in front. "All-false" and "all-true" are the assignments `fun _ => false`
and `fun _ => true`. Each result below gives: kind, tier, depth; the plain claim (prose); the Lean
statement quoted verbatim, the first line of each Lean block being a `-- file:line` comment that cites
the quoted source range (paths relative to the package directory); the hypothesis
ledger; the non-vacuity witness; a positive control where one is recorded; secondary theorems with
their own verbatim statements and ledgers; prior art; the design question; and the basis lines.

### Definitions

Every definition below is quoted verbatim from the Lean source, doc comment included (the doc comment states what the definition is meant to capture); the first line of each block is a `-- file:line` comment citing the quoted source range. Proved positive and negative examples are listed where the package has them.

#### Syntax and semantics

`Lit`:

```lean
-- lean/ToyDrat/Basic.lean:13-19
/-- A literal: a propositional variable `var` with polarity `pos` (`true` means the
positive literal `x`, `false` the negative literal `¬x`). This captures the DIMACS
literal `±(var)` without the "nonzero integer" side condition. -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr
```

`Lit.p`:

```lean
-- lean/ToyDrat/Basic.lean:21-22
/-- Positive literal of variable `v`. -/
def Lit.p (v : Nat) : Lit := ⟨v, true⟩
```

`Lit.n`:

```lean
-- lean/ToyDrat/Basic.lean:23-24
/-- Negative literal of variable `v`. -/
def Lit.n (v : Nat) : Lit := ⟨v, false⟩
```

`Lit.neg`:

```lean
-- lean/ToyDrat/Basic.lean:26-27
/-- Complement of a literal (same variable, opposite polarity). -/
def Lit.neg (l : Lit) : Lit := ⟨l.var, !l.pos⟩
```

Examples (proved): `Lit.neg_example`.

`Assignment`:

```lean
-- lean/ToyDrat/Basic.lean:29-30
/-- A total truth assignment. -/
abbrev Assignment := Nat → Bool
```

`Lit.eval`:

```lean
-- lean/ToyDrat/Basic.lean:32-33
/-- Truth value of a literal under a total assignment. -/
def Lit.eval (a : Assignment) (l : Lit) : Bool := a l.var == l.pos
```

Examples (proved): `Lit.eval_example_pos`, `Lit.eval_example_neg`.

`Clause`:

```lean
-- lean/ToyDrat/Basic.lean:35-36
/-- A clause: a disjunction of literals. -/
abbrev Clause := List Lit
```

`Formula`:

```lean
-- lean/ToyDrat/Basic.lean:38-39
/-- A CNF formula: a conjunction of clauses. -/
abbrev Formula := List Clause
```

`Clause.eval`:

```lean
-- lean/ToyDrat/Basic.lean:41-42
/-- Truth value of a clause: some literal is true. The empty clause is false. -/
def Clause.eval (a : Assignment) (C : Clause) : Bool := C.any (Lit.eval a)
```

Examples (proved): `Clause.eval_example_pos`, `Clause.eval_nil`.

`Formula.eval`:

```lean
-- lean/ToyDrat/Basic.lean:44-45
/-- Truth value of a formula: every clause is true. The empty formula is true. -/
def Formula.eval (a : Assignment) (F : Formula) : Bool := F.all (Clause.eval a)
```

`Satisfies`:

```lean
-- lean/ToyDrat/Basic.lean:47-48
/-- `a` is a model of `F`. -/
def Satisfies (a : Assignment) (F : Formula) : Prop := F.eval a = true
```

`Satisfiable`:

```lean
-- lean/ToyDrat/Basic.lean:53-54
/-- `F` has a model. -/
def Satisfiable (F : Formula) : Prop := ∃ a, Satisfies a F
```

Examples (proved): `Satisfiable_example_pos`, `Satisfiable_example_neg`.

`Entails`:

```lean
-- lean/ToyDrat/Basic.lean:56-58
/-- Semantic entailment of a clause: every model of `F` satisfies `C`. -/
def Entails (F : Formula) (C : Clause) : Prop :=
  ∀ a, Satisfies a F → C.eval a = true
```

Examples (proved): `Entails_example_pos`, `Entails_example_neg`.

`Equivalent`:

```lean
-- lean/ToyDrat/Basic.lean:60-61
/-- Logical equivalence of formulas: the same models. -/
def Equivalent (F G : Formula) : Prop := ∀ a, Satisfies a F ↔ Satisfies a G
```

Examples (proved): `Equivalent_example_pos`, `Equivalent_example_neg`.

`Equisatisfiable`:

```lean
-- lean/ToyDrat/Basic.lean:63-64
/-- Equisatisfiability: one is satisfiable iff the other is. -/
def Equisatisfiable (F G : Formula) : Prop := Satisfiable F ↔ Satisfiable G
```

Examples (proved): `Equisatisfiable_example_pos`, `Equisatisfiable_example_neg`.

#### Unit propagation

`Trail`:

```lean
-- lean/ToyDrat/UnitProp.lean:25-26
/-- A trail: literals currently assumed true. -/
abbrev Trail := List Lit
```

`falsified`:

```lean
-- lean/ToyDrat/UnitProp.lean:28-29
/-- `l` is falsified by the trail: its complement is on the trail. -/
def falsified (τ : Trail) (l : Lit) : Bool := decide (l.neg ∈ τ)
```

`forces`:

```lean
-- lean/ToyDrat/UnitProp.lean:31-34
/-- Clause `C` forces `l` under `τ`: every literal of `C` other than `l` is falsified.
(Membership `l ∈ C` is imposed separately by `unitLits`.) -/
def forces (τ : Trail) (C : Clause) (l : Lit) : Bool :=
  C.all (fun m => decide (m = l) || falsified τ m)
```

`unitLits`:

```lean
-- lean/ToyDrat/UnitProp.lean:36-39
/-- The literals of `C` that `C` forces under `τ`. For a clause with exactly one
non-falsified literal this is that literal; for a fully falsified clause it is every
literal (harmless: a fully falsified clause is reported as a conflict first). -/
def unitLits (τ : Trail) (C : Clause) : List Lit := C.filter (forces τ C)
```

Examples (proved): `unitLits_example_pos`, `unitLits_example_neg`.

`hasConflict`:

```lean
-- lean/ToyDrat/UnitProp.lean:41-45
/-- A conflict: the trail contains a complementary pair, or some clause of `F` has every
literal falsified by `τ`. (The first disjunct treats the trail literals as unit clauses,
as in the textbook definition `F ∧ ¬C ⊢₁ ⊥` of RUP; it makes tautological clauses RUP.) -/
def hasConflict (F : Formula) (τ : Trail) : Bool :=
  τ.any (falsified τ) || F.any (fun C => C.all (falsified τ))
```

`upRound`:

```lean
-- lean/ToyDrat/UnitProp.lean:47-49
/-- One propagation round: append every forced literal not already on the trail. -/
def upRound (F : Formula) (τ : Trail) : Trail :=
  τ ++ (F.flatMap (unitLits τ)).filter (fun l => !decide (l ∈ τ))
```

`UPResult`:

```lean
-- lean/ToyDrat/UnitProp.lean:51-56
/-- Outcome of bounded unit propagation: a conflict, or the trail reached when the
budget ran out (which is a fixpoint whenever the budget was large enough). -/
inductive UPResult where
  | conflict
  | trail (τ : Trail)
  deriving DecidableEq, Repr
```

`unitProp`:

```lean
-- lean/ToyDrat/UnitProp.lean:58-61
/-- Unit propagation with a budget of `fuel` rounds, starting from trail `τ`. -/
def unitProp : Nat → Formula → Trail → UPResult
  | 0, F, τ => if hasConflict F τ then .conflict else .trail τ
  | n + 1, F, τ => if hasConflict F τ then .conflict else unitProp n F (upRound F τ)
```

Examples (proved): `unitProp_example_pos`, `unitProp_example_neg`, `unitProp_example_dup_lits`, `unitProp_example_trail`, `unitProp_example_trail_pair`.

`negClause`:

```lean
-- lean/ToyDrat/UnitProp.lean:66-67
/-- The trail obtained by assuming every literal of `C` false. -/
def negClause (C : Clause) : Trail := C.map Lit.neg
```

`FormulaSub`:

```lean
-- lean/ToyDrat/UnitProp.lean:146-147
/-- Formula inclusion (as sets of clauses). -/
def FormulaSub (F G : Formula) : Prop := ∀ C ∈ F, C ∈ G
```

Examples (proved): `FormulaSub_example_pos`, `FormulaSub_example_neg`.

#### RUP and RAT

`RUP`:

```lean
-- lean/ToyDrat/RupRat.lean:19-21
/-- `C` is a reverse-unit-propagation (RUP) consequence of `F`: assuming all literals of
`C` false, unit propagation over `F` reaches a conflict within some finite budget. -/
def RUP (F : Formula) (C : Clause) : Prop := ∃ n, unitProp n F (negClause C) = .conflict
```

Examples (proved): `RUP_example_pos`, `RUP_example_neg`.

`rupCheck`:

```lean
-- lean/ToyDrat/RupRat.lean:23-25
/-- Budgeted RUP checker: propagate for `fuel` rounds from the negation of `C`. -/
def rupCheck (fuel : Nat) (F : Formula) (C : Clause) : Bool :=
  unitProp fuel F (negClause C) == .conflict
```

Examples (proved): `rupCheck_example_pos`, `rupCheck_example_neg`.

`resolventOn`:

```lean
-- lean/ToyDrat/RupRat.lean:27-29
/-- The clause checked against `D` when `C` is RAT on `p`: `C ∪ (D \ {¬p})`
(the pivot `p` itself stays in the clause, following the DRAT literature). -/
def resolventOn (C D : Clause) (p : Lit) : Clause := C ++ D.filter (fun m => decide (m ≠ p.neg))
```

`RATOn`:

```lean
-- lean/ToyDrat/RupRat.lean:31-37
/-- `C` is RAT on literal `p` w.r.t. `F`: every resolution candidate on `p` is RUP.
Membership `p ∈ C` is *not* part of this predicate, unlike the literature definition of
"RAT on `p`", which requires `p ∈ C`. Without `p ∈ C` it does not preserve
satisfiability (`ratOn_without_mem_unsound`); every result using it for satisfiability
assumes `p ∈ C` separately, and `RAT` below fixes `p` to be the first literal of `C`. -/
def RATOn (F : Formula) (C : Clause) (p : Lit) : Prop :=
  ∀ D ∈ F, p.neg ∈ D → RUP F (resolventOn C D p)
```

Examples (proved): `RATOn_example_pos`, `RATOn_example_neg`.

`RAT`:

```lean
-- lean/ToyDrat/RupRat.lean:39-43
/-- `C` is RAT w.r.t. `F` on its first literal, the pivot designated by the DRAT format.
The empty clause has no pivot and is never RAT. -/
def RAT (F : Formula) : Clause → Prop
  | [] => False
  | p :: rest => RATOn F (p :: rest) p
```

Examples (proved): `RAT_example_pos`, `RAT_example_neg`, `RAT_example_pos_not_entailed`.

`ratCheck`:

```lean
-- lean/ToyDrat/RupRat.lean:45-49
/-- Budgeted RAT checker on the first literal. -/
def ratCheck (fuel : Nat) (F : Formula) : Clause → Bool
  | [] => false
  | p :: rest =>
    F.all (fun D => !decide (p.neg ∈ D) || rupCheck fuel F (resolventOn (p :: rest) D p))
```

Examples (proved): `ratCheck_example_pos`, `ratCheck_example_pos_resolvent`, `ratCheck_example_neg`, `ratCheck_example_neg_nonempty`.

`setTrue`:

```lean
-- lean/ToyDrat/RupRat.lean:51-52
/-- Make literal `p` true, leaving all other variables unchanged. -/
def setTrue (a : Assignment) (p : Lit) : Assignment := fun v => if v = p.var then p.pos else a v
```

`ratWitness`:

```lean
-- lean/ToyDrat/RupRat.lean:54-57
/-- The model used for a RAT addition: keep `a` if it already satisfies `C`, otherwise
make the pivot `p` true. -/
def ratWitness (a : Assignment) (C : Clause) (p : Lit) : Assignment :=
  if C.eval a then a else setTrue a p
```

Examples (proved): `ratWitness_example`.

#### Certificates, deletion policies, and checkers

`Step`:

```lean
-- lean/ToyDrat/Certificate.lean:28-32
/-- A certificate step. -/
inductive Step where
  | add (C : Clause)
  | del (C : Clause)
  deriving DecidableEq, Repr
```

`deleteClause`:

```lean
-- lean/ToyDrat/Certificate.lean:34-35
/-- Delete every occurrence of clause `C` (syntactic equality). -/
def deleteClause (F : Formula) (C : Clause) : Formula := F.filter (fun D => decide (D ≠ C))
```

Examples (proved): `deleteClause_example_pos`, `deleteClause_example_neg`.

`DeletionPolicy`:

```lean
-- lean/ToyDrat/Certificate.lean:37-39
/-- A deletion policy: `ignore F C = true` means the checker skips the deletion of `C`
from the current formula `F`. -/
abbrev DeletionPolicy := Formula → Clause → Bool
```

`applyDel`:

```lean
-- lean/ToyDrat/Certificate.lean:41-43
/-- Apply a deletion step under a policy. -/
def applyDel (ignore : DeletionPolicy) (F : Formula) (C : Clause) : Formula :=
  if ignore F C then F else deleteClause F C
```

`checkGen`:

```lean
-- lean/ToyDrat/Certificate.lean:45-54
/-- Generic refutation checker, parameterized by the addition check and the deletion
policy. Accepts iff some addition of the empty clause passes the addition check, every
earlier addition passed it, and deletions were processed according to the policy. Steps
after the first accepted empty clause are not examined, and the empty certificate is
rejected even when `F` already contains the empty clause. -/
def checkGen (addCheck : Formula → Clause → Bool) (ignore : DeletionPolicy) :
    Formula → List Step → Bool
  | _, [] => false
  | F, .del C :: π => checkGen addCheck ignore (applyDel ignore F C) π
  | F, .add C :: π => addCheck F C && (C.isEmpty || checkGen addCheck ignore (C :: F) π)
```

`addOK`:

```lean
-- lean/ToyDrat/Certificate.lean:56-58
/-- DRAT addition check with propagation budget `fuel`: RUP, or else RAT on the first
literal. -/
def addOK (fuel : Nat) (F : Formula) (C : Clause) : Bool := rupCheck fuel F C || ratCheck fuel F C
```

Examples (proved): `addOK_example_pos`, `addOK_example_neg`.

`checkDRAT`:

```lean
-- lean/ToyDrat/Certificate.lean:60-62
/-- DRAT refutation checker. -/
def checkDRAT (fuel : Nat) (ignore : DeletionPolicy) : Formula → List Step → Bool :=
  checkGen (addOK fuel) ignore
```

`checkDRUP`:

```lean
-- lean/ToyDrat/Certificate.lean:64-66
/-- DRUP refutation checker (additions must be RUP). -/
def checkDRUP (fuel : Nat) (ignore : DeletionPolicy) : Formula → List Step → Bool :=
  checkGen (rupCheck fuel) ignore
```

`honorAll`:

```lean
-- lean/ToyDrat/Certificate.lean:68-69
/-- Policy that applies every deletion ("specified" DRAT). -/
def honorAll : DeletionPolicy := fun _ _ => false
```

`ignoreUnitDeletions`:

```lean
-- lean/ToyDrat/Certificate.lean:71-73
/-- Policy that ignores deletions of unit clauses ("operational" DRAT, toy version:
syntactic unit clauses). -/
def ignoreUnitDeletions : DeletionPolicy := fun _ C => decide (C.length = 1)
```

Examples (proved): `ignoreUnitDeletions_example_pos`, `ignoreUnitDeletions_example_neg`, `ignoreUnitDeletions_example_dup`.

`checkSpecified`:

```lean
-- lean/ToyDrat/Certificate.lean:75-76
/-- Specified DRAT checker: every deletion is applied. -/
def checkSpecified (fuel : Nat) : Formula → List Step → Bool := checkDRAT fuel honorAll
```

Examples (proved): `checkSpecified_fullSquare`, `checkSpecified_example_neg`.

`checkOperational`:

```lean
-- lean/ToyDrat/Certificate.lean:78-80
/-- Operational DRAT checker: deletions of unit clauses are ignored. -/
def checkOperational (fuel : Nat) : Formula → List Step → Bool :=
  checkDRAT fuel ignoreUnitDeletions
```

`replay`:

```lean
-- lean/ToyDrat/Certificate.lean:82-88
/-- Replay a certificate without looking for the empty clause; `none` if some addition
fails its check. Returns the formula reached at the end. -/
def replay (addCheck : Formula → Clause → Bool) (ignore : DeletionPolicy) :
    Formula → List Step → Option Formula
  | F, [] => some F
  | F, .del C :: π => replay addCheck ignore (applyDel ignore F C) π
  | F, .add C :: π => if addCheck F C then replay addCheck ignore (C :: F) π else none
```

Examples (proved): `replay_example_pos`, `replay_example_neg`.

`naiveSatCheck`:

```lean
-- lean/ToyDrat/Certificate.lean:90-96
/-- A *naive* satisfiability checker: replay the certificate with the DRAT addition check
and all deletions applied *without any check on the deleted clauses*, then test the claimed
model against the formula reached at the end (not against the original formula). -/
def naiveSatCheck (fuel : Nat) (F : Formula) (π : List Step) (a : Assignment) : Bool :=
  match replay (addOK fuel) honorAll F π with
  | some G => G.eval a
  | none => false
```

Examples (proved): `naiveSatCheck_example_pos`, `naiveSatCheck_example_neg`.

`NoDeletions`:

```lean
-- lean/ToyDrat/Certificate.lean:98-99
/-- The certificate contains no deletion step. -/
def NoDeletions (π : List Step) : Prop := ∀ s ∈ π, ∃ C, s = .add C
```

Examples (proved): `NoDeletions_example_pos`, `NoDeletions_example_neg`.

`replayRupDel`:

```lean
-- lean/ToyDrat/Certificate.lean:249-256
/-- Replay in which every deletion of `C` from the current formula `F` must pass
`rupCheck fuel (deleteClause F C) C` (the deleted clause is RUP w.r.t. the formula without
it) and every addition must pass `addOK fuel`; `none` if some check fails. -/
def replayRupDel (fuel : Nat) : Formula → List Step → Option Formula
  | F, [] => some F
  | F, .del C :: π =>
    if rupCheck fuel (deleteClause F C) C then replayRupDel fuel (deleteClause F C) π else none
  | F, .add C :: π => if addOK fuel F C then replayRupDel fuel (C :: F) π else none
```

`satCheckRupDel`:

```lean
-- lean/ToyDrat/Certificate.lean:258-262
/-- SAT check against the final formula of `replayRupDel` (RUP-checked deletions). -/
def satCheckRupDel (fuel : Nat) (F : Formula) (π : List Step) (a : Assignment) : Bool :=
  match replayRupDel fuel F π with
  | some G => G.eval a
  | none => false
```

`replayRatDel`:

```lean
-- lean/ToyDrat/Certificate.lean:264-271
/-- Replay in which every deletion of `C` from the current formula `F` must pass the DRAT
addition check `addOK fuel (deleteClause F C) C` (RUP, or RAT on the first literal, w.r.t.
the formula without it) and every addition must pass `addOK fuel`. -/
def replayRatDel (fuel : Nat) : Formula → List Step → Option Formula
  | F, [] => some F
  | F, .del C :: π =>
    if addOK fuel (deleteClause F C) C then replayRatDel fuel (deleteClause F C) π else none
  | F, .add C :: π => if addOK fuel F C then replayRatDel fuel (C :: F) π else none
```

`deleteOneCopy`:

```lean
-- lean/ToyDrat/Certificate.lean:493-496
/-- Delete the first copy of `C` (syntactic equality), as in the multiset reading of DRAT. -/
def deleteOneCopy : Formula → Clause → Formula
  | [], _ => []
  | D :: F, C => if D = C then F else D :: deleteOneCopy F C
```

`checkDRUPOneCopy`:

```lean
-- lean/ToyDrat/Certificate.lean:498-502
/-- DRUP checker that applies every deletion, removing one copy per deletion step. -/
def checkDRUPOneCopy (fuel : Nat) : Formula → List Step → Bool
  | _, [] => false
  | F, .del C :: π => checkDRUPOneCopy fuel (deleteOneCopy F C) π
  | F, .add C :: π => rupCheck fuel F C && (C.isEmpty || checkDRUPOneCopy fuel (C :: F) π)
```

#### Hint replay (LRAT style)

`hintReplay`:

```lean
-- lean/ToyDrat/Lrat.lean:27-39
/-- Replay hints: each hinted clause must have no non-falsified literal occurrence (success;
remaining hints are not examined) or exactly one (which is pushed on the trail, whether or
not it is already there); anything else, or a dangling index, fails. -/
def hintReplay (F : Formula) : Trail → List Nat → Bool
  | _, [] => false
  | τ, i :: is =>
    match F[i]? with
    | none => false
    | some D =>
      match D.filter (fun l => !falsified τ l) with
      | [] => true
      | [l] => hintReplay F (l :: τ) is
      | _ => false
```

`lratRupCheck`:

```lean
-- lean/ToyDrat/Lrat.lean:41-43
/-- LRAT-style RUP check of clause `C` with the given hint list. -/
def lratRupCheck (F : Formula) (C : Clause) (hints : List Nat) : Bool :=
  hintReplay F (negClause C) hints
```

Examples (proved): `lratRupCheck_example_pos`, `lratRupCheck_example_neg`, `lratRupCheck_example_satisfied_hint`, `lratRupCheck_example_trailing_hints`.

`sloppyHintReplay`:

```lean
-- lean/ToyDrat/Lrat.lean:45-55
/-- A deliberately *sloppy* hint replay that skips the unit test: it assigns the first
non-falsified literal of each hinted clause even when the clause has several. -/
def sloppyHintReplay (F : Formula) : Trail → List Nat → Bool
  | _, [] => false
  | τ, i :: is =>
    match F[i]? with
    | none => false
    | some D =>
      match D.filter (fun l => !falsified τ l) with
      | [] => true
      | l :: _ => sloppyHintReplay F (l :: τ) is
```

Examples (proved): `sloppyHintReplay_example_pos`, `sloppyHintReplay_example_neg`, `sloppyHintReplay_example_neg_dangling`.

`NonTautological`:

```lean
-- lean/ToyDrat/Lrat.lean:150-151
/-- `C` contains no complementary pair of literals. -/
def NonTautological (C : Clause) : Prop := ∀ l ∈ C, l.neg ∉ C
```

Examples (proved): `NonTautological_example_pos`, `NonTautological_example_neg`.

`DupFreeClauses`:

```lean
-- lean/ToyDrat/Lrat.lean:153-154
/-- No clause of `F` repeats a literal. -/
def DupFreeClauses (F : Formula) : Prop := ∀ D ∈ F, D.Nodup
```

Examples (proved): `DupFreeClauses_example_pos`, `DupFreeClauses_example_neg`.

`dedupLits`:

```lean
-- lean/ToyDrat/Lrat.lean:156-161
/-- Remove repeated literals, keeping the last occurrence of each. -/
def dedupLits : List Lit → List Lit
  | [] => []
  | l :: ls =>
    let r := dedupLits ls
    if decide (l ∈ r) then r else l :: r
```

`hintStepDedup`:

```lean
-- lean/ToyDrat/Lrat.lean:163-173
/-- Hint replay as in `hintReplay`, but on the deduplicated non-falsified literals. -/
def hintStepDedup (F : Formula) : Trail → List Nat → Bool
  | _, [] => false
  | τ, i :: is =>
    match F[i]? with
    | none => false
    | some D =>
      match dedupLits (D.filter (fun l => !falsified τ l)) with
      | [] => true
      | [l] => hintStepDedup F (l :: τ) is
      | _ => false
```

`hintReplayDedup`:

```lean
-- lean/ToyDrat/Lrat.lean:175-178
/-- Hint replay that first checks the trail for a complementary pair (as `hasConflict` does),
then replays hints on deduplicated literals. -/
def hintReplayDedup (F : Formula) (τ : Trail) (hints : List Nat) : Bool :=
  τ.any (falsified τ) || hintStepDedup F τ hints
```

`lratRupCheckDedup`:

```lean
-- lean/ToyDrat/Lrat.lean:180-182
/-- LRAT-style RUP check with the initial trail-pair test and literal deduplication. -/
def lratRupCheckDedup (F : Formula) (C : Clause) (hints : List Nat) : Bool :=
  hintReplayDedup F (negClause C) hints
```

#### Named instances

`fullSquare`:

```lean
-- lean/ToyDrat/RupRat.lean:142-145
/-- Four clauses over variables 1 and 2 forming an unsatisfiable formula without unit
clauses: `(x₁∨x₂) ∧ (x₁∨¬x₂) ∧ (¬x₁∨x₂) ∧ (¬x₁∨¬x₂)`. -/
def fullSquare : Formula :=
  [[Lit.p 1, Lit.p 2], [Lit.p 1, Lit.n 2], [Lit.n 1, Lit.p 2], [Lit.n 1, Lit.n 2]]
```

`x0OrFullSquare`:

```lean
-- lean/ToyDrat/RupRat.lean:160-164
/-- `x₀` added to each clause of `fullSquare`: the four clauses `x₀ ∨ ±x₁ ∨ ±x₂`. Satisfiable
(set `x₀` true), entails `x₀`, and contains no `¬x₀`. -/
def x0OrFullSquare : Formula :=
  [[Lit.p 0, Lit.p 1, Lit.p 2], [Lit.p 0, Lit.p 1, Lit.n 2],
   [Lit.p 0, Lit.n 1, Lit.p 2], [Lit.p 0, Lit.n 1, Lit.n 2]]
```

`unitPlusSquare`:

```lean
-- lean/ToyDrat/Certificate.lean:404-405
/-- `¬x₀` together with `fullSquare` (unsatisfiable, no unit propagation conflict). -/
def unitPlusSquare : Formula := [Lit.n 0] :: fullSquare
```

`unitDeletionThenRAT`:

```lean
-- lean/ToyDrat/Certificate.lean:407-408
/-- The certificate "delete `¬x₀`, add `x₀`, add `x₁`, add the empty clause". -/
def unitDeletionThenRAT : List Step := [.del [Lit.n 0], .add [Lit.p 0], .add [Lit.p 1], .add []]
```

`chain3`:

```lean
-- lean/ToyDrat/Lrat.lean:122-123
/-- A three-clause formula refuted by unit propagation: `x₀ ∧ (¬x₀ ∨ x₁) ∧ ¬x₁`. -/
def chain3 : Formula := [[Lit.p 0], [Lit.n 0, Lit.p 1], [Lit.n 1]]
```

### What a single certificate step preserves

#### `rup-implies-entails`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** If unit propagation over F, started from the trail that assumes every literal of the clause C false, reaches a conflict within some finite budget (RUP F C), then every total assignment that satisfies F satisfies C (Entails F C). Secondary theorems: under the same hypothesis, C :: F and F have the same models (rup_addition_preserves_equivalence); and, for every F and C with no hypothesis, C :: F and F have the same models if and only if F entails C (equivalent_cons_iff_entails).
- **Lean statement** (`rup_implies_entails`, verbatim):

```lean
-- lean/ToyDrat/RupRat.lean:127
theorem rup_implies_entails {F : Formula} {C : Clause} (h : RUP F C) : Entails F C := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `h : RUP F C` | The propagation conflict being certified; a conflict is a complementary pair on the trail or a clause of F with all literals falsified. | tight | `rup_implies_entails_tight_rup` (F = x0 or x1 (one binary clause), C = x0) |

- **Non-vacuity witness:** `rup_implies_entails_nonvacuous` — F = x0 and (not x0 or x1), C = x1: C is RUP with respect to F.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:21
  theorem rup_implies_entails_nonvacuous : RUP [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] :=
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `rup_addition_preserves_equivalence` (verbatim):

  ```lean
  -- lean/ToyDrat/RupRat.lean:136-137
  theorem rup_addition_preserves_equivalence {F : Formula} {C : Clause} (h : RUP F C) :
      Equivalent (C :: F) F := by
  ```

  Plain reading (prose): If RUP F C, then C :: F and F have the same models.

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `h : RUP F C` | As for the main theorem. | tight | `rup_equivalence_tight_rup` (F = x1, C = x0 (a one-clause formula)) |

  Non-vacuity witness: `rup_implies_entails_nonvacuous`.

- `equivalent_cons_iff_entails` (verbatim):

  ```lean
  -- lean/ToyDrat/Basic.lean:118-119
  theorem equivalent_cons_iff_entails (F : Formula) (C : Clause) :
      Equivalent (C :: F) F ↔ Entails F C := by
  ```

  Plain reading (prose): For every F and C (universally quantified, no hypotheses): C :: F and F have the same models if and only if F entails C. The equivalence corollary above is therefore a restatement of the main theorem.

  No hypotheses (concrete instance or universally quantified parameters only).

**Prior art:** [GN03], [VG12], [HJB10], [CHHKS17], [Lean-RupAdd] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What exactly does each certificate step preserve (logical equivalence versus only satisfiability)?

```text
Basis: execution (Lean kernel check)
```

#### `entails-not-implies-rup`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** The unsatisfiable formula fullSquare (all four binary clauses over x1, x2) entails the empty clause, but the empty clause is not RUP with respect to it at any budget. Secondary theorem: the satisfiable formula x0OrFullSquare (the four clauses x0 or ±x1 or ±x2) entails the nonempty clause x0, which is not RUP with respect to it at any budget (entails_not_implies_rup_satisfiable_nonempty).
- **Lean statement** (`entails_not_implies_rup`, verbatim):

```lean
-- lean/ToyDrat/RupRat.lean:156
theorem entails_not_implies_rup : Entails fullSquare [] ∧ ¬ RUP fullSquare [] := by
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `entails_not_implies_rup` — The instances themselves (fullSquare; x0OrFullSquare).
- **Positive control:** `rup_implies_entails_nonvacuous` — Nearby setting where the conclusion fails: x1 is RUP with respect to x0 and (not x0 or x1) (rup_implies_entails_nonvacuous), and hence entailed by it (rup_implies_entails).

**Secondary theorems** (listed in this card's `lean_names`):

- `entails_not_implies_rup_satisfiable_nonempty` (verbatim):

  ```lean
  -- lean/ToyDrat/RupRat.lean:179-181
  theorem entails_not_implies_rup_satisfiable_nonempty :
      Satisfiable x0OrFullSquare ∧ Entails x0OrFullSquare [Lit.p 0] ∧
        ¬ RUP x0OrFullSquare [Lit.p 0] :=
  ```

  Plain reading (prose): The satisfiable formula x0OrFullSquare (the four clauses x0 or ±x1 or ±x2) entails the nonempty clause x0, which is not RUP with respect to it at any budget.

  No hypotheses (concrete instance or universally quantified parameters only).

**Prior art:** [GN03], [CHHKS17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What does a checker have to verify for an UNSAT verdict to be sound?

```text
Basis: execution (Lean kernel check)
```

#### `rat-witness`

- **Kind:** theorem · **Tier:** T0 · **Depth:** substantive
- **Plain claim (prose):** If p is a literal of C, C is RAT on p with respect to F (for every clause D of F containing the complement of p, the clause C followed by the literals of D other than that complement is RUP with respect to F), and a satisfies F, then ratWitness a C p -- a itself if a satisfies C, otherwise a with p made true -- satisfies C and F together.
- **Lean statement** (`ratOn_witness_satisfies`, verbatim):

```lean
-- lean/ToyDrat/RupRat.lean:199-201
theorem ratOn_witness_satisfies {F : Formula} {C : Clause} {p : Lit} {a : Assignment}
    (hp : p ∈ C) (hrat : RATOn F C p) (ha : Satisfies a F) :
    Satisfies (ratWitness a C p) (C :: F) := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `hp : p ∈ C` | If p is not a literal of C, flipping p need not satisfy C. RATOn itself does not include p ∈ C. | tight | `ratOn_witness_tight_mem` (F empty, C = x1, p = x0) |
| `hrat : RATOn F C p` | Keeps the clauses containing the complement of p satisfied after the flip. | tight | `ratOn_witness_tight_rat` (F = not x0, C = x0, p = x0) |
| `ha : Satisfies a F` | The witness is built from a model of F. | tight | `ratOn_witness_tight_model` (F = x1, C = x0, p = x0, a = all-false) |

- **Non-vacuity witness:** `ratOn_witness_nonvacuous` — F = (not x0 or x1), C = (x0 or not x1), p = x0, a = (x0 false, x1 true); a falsifies C, so the flip branch is exercised.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:59-62
  theorem ratOn_witness_nonvacuous :
      Lit.p 0 ∈ [Lit.p 0, Lit.n 1] ∧ RATOn [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] (Lit.p 0) ∧
        Satisfies (fun v => v == 1) [[Lit.n 0, Lit.p 1]] ∧
        Clause.eval (fun v => v == 1) [Lit.p 0, Lit.n 1] = false :=
  ```

**Prior art:** [JHB12], [CHHKS17], [Lean-RatAdd], [WHH13] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What exactly does each certificate step preserve (logical equivalence versus only satisfiability)?

```text
Basis: execution (Lean kernel check)
```

#### `rat-addition-preserves-satisfiability`

- **Kind:** theorem · **Tier:** T0 · **Depth:** definitional
- **Depth note:** Definitional given rat-witness: the proof packs and unpacks the existential around ratOn_witness_satisfies, where the substance lies.
- **Plain claim (prose):** If C is RAT on its first literal with respect to F (RAT F C; in particular C is nonempty) and F is satisfiable, then C :: F is satisfiable. Secondary theorems: if p is a literal of C, C is RAT on p with respect to F (RATOn F C p), and F is satisfiable, then C :: F is satisfiable (ratOn_preserves_satisfiability); and if RAT F C, then C :: F and F are equisatisfiable, with no satisfiability hypothesis (rat_addition_equisatisfiable).
- **Lean statement** (`rat_addition_preserves_satisfiability`, verbatim):

```lean
-- lean/ToyDrat/RupRat.lean:245-246
theorem rat_addition_preserves_satisfiability {F : Formula} {C : Clause}
    (hrat : RAT F C) (hF : Satisfiable F) : Satisfiable (C :: F) := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `hrat : RAT F C` | Without it an added clause can make a satisfiable formula unsatisfiable. | tight | `rat_sat_tight_rat` (F = not x0, C = x0) |
| `hF : Satisfiable F` | The conclusion is about satisfiability being carried forward. | tight | `rat_sat_tight_sat` (F = x0 and not x0, C = x1) |

- **Non-vacuity witness:** `rat_sat_nonvacuous` — F = (not x0 or x1), C = (x0 or not x1): C is RAT on x0 and F is satisfiable. C is not entailed by F (RAT_example_pos_not_entailed), hence not RUP (rup_implies_entails).

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:86-87
  theorem rat_sat_nonvacuous :
      RAT [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] ∧ Satisfiable [[Lit.n 0, Lit.p 1]] :=
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `ratOn_preserves_satisfiability` (verbatim):

  ```lean
  -- lean/ToyDrat/RupRat.lean:239-240
  theorem ratOn_preserves_satisfiability {F : Formula} {C : Clause} {p : Lit}
      (hp : p ∈ C) (hrat : RATOn F C p) (hF : Satisfiable F) : Satisfiable (C :: F) :=
  ```

  Plain reading (prose): If p is a literal of C, RATOn F C p holds, and F is satisfiable, then C :: F is satisfiable: RAT on any literal of C (not only the first) preserves satisfiability when that literal belongs to C.

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `hp : p ∈ C` | RATOn does not include p ∈ C; without it satisfiability can be lost. | tight | `ratOn_sat_tight_mem` (F = not x1, C = x1, p = x0) |
  | `hrat : RATOn F C p` | As in the main theorem. | tight | `ratOn_sat_tight_rat` (F = not x0, C = x0, p = x0) |
  | `hF : Satisfiable F` | As in the main theorem. | tight | `ratOn_sat_tight_sat` (F = x0 and not x0, C = x1, p = x1) |

  Non-vacuity witness: `ratOn_sat_nonvacuous` — Uses the second literal x1 of x0 or x1 as pivot with respect to not x0, where first-literal RAT fails.

- `rat_addition_equisatisfiable` (verbatim):

  ```lean
  -- lean/ToyDrat/RupRat.lean:252-253
  theorem rat_addition_equisatisfiable {F : Formula} {C : Clause} (hrat : RAT F C) :
      Equisatisfiable (C :: F) F :=
  ```

  Plain reading (prose): If RAT F C, then C :: F and F are equisatisfiable. It has no satisfiability hypothesis.

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `hrat : RAT F C` | Without it the formulas need not be equisatisfiable. | tight | `rat_equisat_tight_rat` (F = not x0, C = x0) |

  Non-vacuity witness: `rat_sat_nonvacuous`.

**Prior art:** [JHB12], [CHHKS17], [Lean-RatAdd], [WHH13] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What exactly does each certificate step preserve (logical equivalence versus only satisfiability)?

```text
Basis: execution (Lean kernel check)
```

#### `rat-addition-not-equivalence`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** The clause x0 is RAT with respect to the formula x1 (no clause contains not x0), yet the model x1 = true, x0 = false of x1 is not a model of x0 and x1; so RAT addition does not in general preserve equivalence, and a RAT clause need not be entailed. Secondary theorem: the clause x0 or not x1 is RAT on x0 with respect to F = (not x0 or x1), F has the model x0 = false, x1 = true, and no model of (x0 or not x1) and F agrees with it on x0 and x1 (rat_addition_loses_projected_model).
- **Lean statement** (`rat_addition_not_equivalence`, verbatim):

```lean
-- lean/ToyDrat/RupRat.lean:260-263
theorem rat_addition_not_equivalence :
    RAT [[Lit.p 1]] [Lit.p 0] ∧ Satisfies (fun v => v == 1) [[Lit.p 1]] ∧
      ¬ Satisfies (fun v => v == 1) [[Lit.p 0], [Lit.p 1]] ∧
      ¬ Equivalent [[Lit.p 0], [Lit.p 1]] [[Lit.p 1]] ∧ ¬ Entails [[Lit.p 1]] [Lit.p 0] := by
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `rat_addition_not_equivalence` — The instance itself.
- **Positive control:** `rup_addition_preserves_equivalence` — Nearby setting where the conclusion fails: adding a RUP clause preserves the set of models (rup_addition_preserves_equivalence).

**Secondary theorems** (listed in this card's `lean_names`):

- `rat_addition_loses_projected_model` (verbatim):

  ```lean
  -- lean/ToyDrat/RupRat.lean:279-283
  theorem rat_addition_loses_projected_model :
      RAT [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] ∧
        Satisfies (fun v => v == 1) [[Lit.n 0, Lit.p 1]] ∧
        ∀ b : Assignment, b 0 = false → b 1 = true →
          ¬ Satisfies b [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]] := by
  ```

  Plain reading (prose): The blocked clause x0 or not x1 is RAT on x0 with respect to F = (not x0 or x1), F has the model x0 = false, x1 = true, and no model of (x0 or not x1) and F agrees with it on x0 and x1.

  No hypotheses (concrete instance or universally quantified parameters only).

**Prior art:** [JHB12], [Lean-RupAdd], [Lean-RatAdd] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What exactly does each certificate step preserve (logical equivalence versus only satisfiability)?

```text
Basis: execution (Lean kernel check)
```

#### `rup-implies-rat`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** If C is nonempty and RUP with respect to F, then C is RAT on its first literal with respect to F.
- **Lean statement** (`rup_implies_rat_of_ne_nil`, verbatim):

```lean
-- lean/ToyDrat/RupRat.lean:313-314
theorem rup_implies_rat_of_ne_nil {F : Formula} {C : Clause} (hne : C ≠ []) (h : RUP F C) :
    RAT F C := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `hne : C ≠ []` | RAT requires a pivot: RAT F [] is False by definition, while the empty clause can be RUP. Tight (on F = x0 and not x0, C = []). The corollary rup_implies_ratOn has no such hypothesis. | tight | `rup_nil_not_rat` (F = x0 and not x0, C = []) |
| `h : RUP F C` | Tight (on F = not x0, C = x0): a nonempty clause need not be RAT. | tight | `rup_rat_tight_rup` (F = not x0, C = x0) |

- **Non-vacuity witness:** `rup_rat_nonvacuous` — F = x0 and (not x0 or x1), C = x1.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:141
  theorem rup_rat_nonvacuous : [Lit.p 1] ≠ [] ∧ RUP [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] :=
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `rup_implies_ratOn` (verbatim):

  ```lean
  -- lean/ToyDrat/RupRat.lean:309
  theorem rup_implies_ratOn {F : Formula} {C : Clause} (p : Lit) (h : RUP F C) : RATOn F C p :=
  ```

  Plain reading (prose): For every literal p: if RUP F C, then RATOn F C p. It has no nonemptiness hypothesis and holds for p not in C and for C = [], because RATOn omits the literature requirement that p be a literal of C.

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `h : RUP F C` | As in the main theorem. | tight | `rup_rat_tight_rup` (F = not x0, C = x0, p = x0) |

  Non-vacuity witness: `rup_rat_nonvacuous`.

**Prior art:** [JHB12], [CHHKS17], [Lean-RatAdd] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What does a checker have to verify for an UNSAT verdict to be sound?

```text
Basis: execution (Lean kernel check)
```

#### `rat-check-depends-on-pivot-order`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** With respect to the formula not x0, the clause x0 or x1 is RAT on its second literal x1 but neither RUP nor RAT on its first literal, while the reordered clause x1 or x0 is RAT; the budgeted first-literal checker ratCheck rejects x0 or x1 at every budget and accepts x1 or x0 at budget 0, so its verdict depends on literal order.
- **Lean statement** (`rat_check_depends_on_pivot_order`, verbatim):

```lean
-- lean/ToyDrat/RupRat.lean:329-333
theorem rat_check_depends_on_pivot_order :
    RATOn [[Lit.n 0]] [Lit.p 0, Lit.p 1] (Lit.p 1) ∧ ¬ RAT [[Lit.n 0]] [Lit.p 0, Lit.p 1] ∧
      ¬ RUP [[Lit.n 0]] [Lit.p 0, Lit.p 1] ∧ RAT [[Lit.n 0]] [Lit.p 1, Lit.p 0] ∧
      (∀ fuel, ratCheck fuel [[Lit.n 0]] [Lit.p 0, Lit.p 1] = false) ∧
      ratCheck 0 [[Lit.n 0]] [Lit.p 1, Lit.p 0] = true := by
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `rat_check_depends_on_pivot_order` — The instance itself.

**Prior art:** [Heu16], [CHHKS17], [WHH14] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What does a checker have to verify for an UNSAT verdict to be sound?

```text
Basis: execution (Lean kernel check)
```

### UNSAT soundness of certificate checkers

#### `refutation-checker-sound-generic`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** For every addition check addCheck and every deletion policy ignore: if addCheck maps satisfiable formulas to satisfiable formulas (for all F and C, addCheck F C = true and F satisfiable imply C :: F satisfiable), then for every certificate π and formula F, acceptance by the generic checker checkGen addCheck ignore F π (every addition up to and including the first accepted empty clause passes addCheck; deletions are applied as the policy says; later steps are not examined) implies that F is unsatisfiable.
- **Lean statement** (`checkGen_sound_unsat_of_addCheck_preserves_sat`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:135-138
theorem checkGen_sound_unsat_of_addCheck_preserves_sat
    (addCheck : Formula → Clause → Bool) (ignore : DeletionPolicy)
    (hpres : ∀ F C, addCheck F C = true → Satisfiable F → Satisfiable (C :: F)) :
    ∀ (π : List Step) (F : Formula), checkGen addCheck ignore F π = true → ¬ Satisfiable F := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `hpres : ∀ F C, addCheck F C = true → Satisfiable F → Satisfiable (C :: F)` | Each accepted addition carries satisfiability forward; the induction over the certificate uses this step property. | tight | `checkGen_unchecked_additions_unsound` (addCheck accepting everything, F empty, certificate: add the empty clause) |
| `h : checkGen addCheck ignore F π = true` | The certificate is accepted (contains an added empty clause that passed the check). | tight | `checker_acceptance_tight` (addCheck = addOK 3, F = (x0 or x1) and not x0, certificate: add the empty clause) |
| `addCheck, ignore (arbitrary)` | Universally quantified: any addition check satisfying hpres and any function from the current formula and the deleted clause to keep/delete. | harmless (universally quantified) | — |

- **Non-vacuity witness:** `checkGen_sound_nonvacuous` — addCheck = addOK 3 (DRAT check), F = fullSquare, certificate: add x1, add empty clause.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:160-162
  theorem checkGen_sound_nonvacuous :
      (∀ F C, addOK 3 F C = true → Satisfiable F → Satisfiable (C :: F)) ∧
        checkGen (addOK 3) honorAll fullSquare [.add [Lit.p 1], .add []] = true :=
  ```

**Prior art:** [CHHKS17], [WHH14], [Lean-LRAT], [THM21], [Lam17], [CMS17], [Heu16] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What does a checker have to verify for an UNSAT verdict to be sound?

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Reasoning: in Lean 4 core v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Std/Tactic/BVDecide/LRAT/Checker.lean), check_sound has the same shape of argument (induction over the certificate, an empty-clause case, a deletion case, and RUP/RAT addition cases with satisfiability-preserving soundness lemmas), as described in the cited source; its checker uses clause identifiers and hints and is not the toy checkGen.

#### `drat-checker-sound-unsat`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Depth note:** The instantiation of refutation-checker-sound-generic with addCheck = addOK fuel, using drat-steps-preserve-satisfiability-forward for hpres.
- **Plain claim (prose):** For every propagation budget fuel and every deletion policy ignore (in particular honorAll, which applies every deletion, and ignoreUnitDeletions, which ignores deletions of clauses of list length one): if checkDRAT fuel ignore accepts a certificate for F -- every addition up to and including the first accepted empty clause passes rupCheck, or else ratCheck on its first literal, at budget fuel with respect to the current formula -- then F is unsatisfiable.
- **Lean statement** (`checkDRAT_sound_unsat`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:159-160
theorem checkDRAT_sound_unsat (fuel : Nat) (ignore : DeletionPolicy) (F : Formula)
    (π : List Step) (h : checkDRAT fuel ignore F π = true) : ¬ Satisfiable F :=
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `h : checkDRAT fuel ignore F π = true` | The certificate is accepted. | tight | `checker_acceptance_tight` (F = (x0 or x1) and not x0, certificate: add the empty clause) |
| `fuel, ignore (arbitrary)` | Universally quantified budget and deletion policy. | harmless (universally quantified) | — |

- **Non-vacuity witness:** `checkDRAT_sound_nonvacuous` — x0 and fullSquare with certificate: add x3 (RAT, not RUP), delete x0 (a unit deletion on which the two policies differ), add x1, add the empty clause; accepted by both the specified and the operational checker at budget 3.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:167-174
  theorem checkDRAT_sound_nonvacuous :
      ¬ RUP ([Lit.p 0] :: fullSquare) [Lit.p 3] ∧ ratCheck 3 ([Lit.p 0] :: fullSquare) [Lit.p 3] = true ∧
        checkSpecified 3 ([Lit.p 0] :: fullSquare)
          [.add [Lit.p 3], .del [Lit.p 0], .add [Lit.p 1], .add []] = true ∧
        checkOperational 3 ([Lit.p 0] :: fullSquare)
          [.add [Lit.p 3], .del [Lit.p 0], .add [Lit.p 1], .add []] = true ∧
        applyDel honorAll ([Lit.p 3] :: [Lit.p 0] :: fullSquare) [Lit.p 0] ≠
          applyDel ignoreUnitDeletions ([Lit.p 3] :: [Lit.p 0] :: fullSquare) [Lit.p 0] :=
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `checkOperational_sound_unsat` (verbatim):

  ```lean
  -- lean/ToyDrat/Certificate.lean:383-384
  theorem checkOperational_sound_unsat (fuel : Nat) (F : Formula) (π : List Step)
      (h : checkOperational fuel F π = true) : ¬ Satisfiable F :=
  ```

  Plain reading (prose): If checkOperational fuel F π = true, then F is unsatisfiable (the instance ignore = ignoreUnitDeletions; it has no policy parameter).

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `h : checkOperational fuel F π = true` | As in the main theorem. | tight | `checker_acceptance_tight` (F = (x0 or x1) and not x0, certificate: add the empty clause) |

  Non-vacuity witness: `checkDRAT_sound_nonvacuous`.

**Prior art:** [CHHKS17], [WHH14], [Heu16], [drat-trim], [Lean-LRAT], [THM21], [Lam17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** What does a checker have to verify for an UNSAT verdict to be sound?

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Reasoning: drat-trim's specified-versus-operational behavior differs from the toy policies in the ways listed among this card's non-claims (literal deduplication, reason-clause retention, active-clause filtering in backward RAT checks), all read from the cited source (drat-trim.c at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985).

#### `drat-steps-preserve-satisfiability-forward`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** If an addition passes the budgeted DRAT check addOK at some budget (rupCheck succeeds, or ratCheck succeeds on the first literal, with respect to F) and F is satisfiable, then C :: F is satisfiable; contrapositively, if the check passes and C :: F is unsatisfiable, then F is unsatisfiable. Secondary theorem: if F is satisfiable, then so is the result of a deletion under any policy (applyDel_preserves_satisfiability).
- **Lean statement** (`addOK_preserves_satisfiability`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:121-122
theorem addOK_preserves_satisfiability {fuel : Nat} {F : Formula} {C : Clause}
    (h : addOK fuel F C = true) (hF : Satisfiable F) : Satisfiable (C :: F) := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `h : addOK fuel F C = true` | The addition passes the budgeted RUP-or-RAT check addOK. | tight | `addOK_tight_check` (F = not x0, C = x0) |
| `hF : Satisfiable F` | Satisfiability is what is carried forward. | tight | `addOK_tight_sat` (F = x0 and not x0, C = x1) |
| `fuel (arbitrary)` | Universally quantified budget. | harmless (universally quantified) | — |

- **Non-vacuity witness:** `addOK_nonvacuous` — F = (not x0 or x1), C = (x0 or not x1) passes the check by RAT.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:192-193
  theorem addOK_nonvacuous :
      addOK 2 [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] = true ∧ Satisfiable [[Lit.n 0, Lit.p 1]] :=
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `applyDel_preserves_satisfiability` (verbatim):

  ```lean
  -- lean/ToyDrat/Certificate.lean:115-116
  theorem applyDel_preserves_satisfiability {ignore : DeletionPolicy} {F : Formula} {C : Clause}
      (h : Satisfiable F) : Satisfiable (applyDel ignore F C) :=
  ```

  Plain reading (prose): If F is satisfiable, then applyDel ignore F C is satisfiable: a deletion under any policy maps a satisfiable formula to a satisfiable one.

  Depth: definitional.

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `h : Satisfiable F` | Satisfiability is what is carried forward. | tight | `applyDel_tight_sat` (F = x0 and not x0 and x1, C = x1, both policies) |
  | `ignore, C (arbitrary)` | Any policy, any deleted clause. | harmless (universally quantified) | — |

  Non-vacuity witness: `applyDel_nonvacuous`.

**Prior art:** [CHHKS17], [JHB12], [Lean-RupAdd], [Lean-RatAdd] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Why are deletions harmless for UNSAT verdicts but not for SAT verdicts, and what must a checker re-check?

```text
Basis: execution (Lean kernel check)
```

### Deletions and SAT verdicts

#### `naive-sat-check-unsound-with-deletions`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** The checker naiveSatCheck replays a certificate with the DRAT addition check, applies every deletion without checking it, and then tests the claimed assignment only against the final formula. It is unsound: the certificate 'delete x0' contains a deletion, and for the unsatisfiable formula x0 and not x0 naiveSatCheck accepts the all-false assignment at every budget. Secondary theorem: deleting x0 turns the unsatisfiable formula x0 and not x0 into a satisfiable one (deletion_can_turn_unsat_into_sat).
- **Lean statement** (`naiveSatCheck_unsound_with_deletions`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:204-207
theorem naiveSatCheck_unsound_with_deletions :
    ¬ NoDeletions [.del [Lit.p 0]] ∧
      (∀ fuel, naiveSatCheck fuel [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0]] (fun _ => false) = true) ∧
      ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] := by
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `naiveSatCheck_unsound_with_deletions` — The instance itself.
- **Positive control:** `naiveSatCheck_sound_of_noDeletions`, `satCheckRupDel_sound`, `replayRatDel_sat_backward` — Nearby settings where the conclusion fails, each proved.

**Secondary theorems** (listed in this card's `lean_names`):

- `deletion_can_turn_unsat_into_sat` (verbatim):

  ```lean
  -- lean/ToyDrat/Certificate.lean:196-197
  theorem deletion_can_turn_unsat_into_sat :
      ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] ∧ Satisfiable (deleteClause [[Lit.p 0], [Lit.n 0]] [Lit.p 0]) :=
  ```

  Plain reading (prose): The formula x0 and not x0 is unsatisfiable, and the formula obtained by deleting x0 from it is satisfiable.

  No hypotheses (concrete instance or universally quantified parameters only).

**Prior art:** [CHHKS17], [Heu16], [drat-trim], [Lam17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Why are deletions harmless for UNSAT verdicts but not for SAT verdicts, and what must a checker re-check?

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Reasoning: drat-trim's FORWARD_SAT mode (-S) passes each deletion to the same redundancy routine as additions (drat-trim.c at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985, lines 825-830), the operational counterpart of escape hatch (4); whether that routine performs exactly the toy check is not analyzed here.

#### `naive-sat-check-sound-without-deletions`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** If the certificate contains no deletion step and naiveSatCheck accepts the assignment a, then a satisfies the original formula F (the final formula contains every original clause).
- **Lean statement** (`naiveSatCheck_sound_of_noDeletions`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:230-232
theorem naiveSatCheck_sound_of_noDeletions {fuel : Nat} {F : Formula} {π : List Step}
    {a : Assignment} (hnd : NoDeletions π) (h : naiveSatCheck fuel F π a = true) :
    Satisfies a F := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `hnd : NoDeletions π` | With a deletion the final formula can lose clauses of F. | tight | `naiveSatCheck_noDel_tight_noDel` (F = x0 and not x0, certificate: delete x0, a = all-false) |
| `h : naiveSatCheck fuel F π a = true` | The check accepts. | tight | `naiveSatCheck_noDel_tight_accept` (F = x0, empty certificate, a = all-false) |
| `fuel (arbitrary)` | Universally quantified budget. | harmless (universally quantified) | — |

- **Non-vacuity witness:** `naiveSatCheck_noDel_nonvacuous` — F = x0 and (not x0 or x1), certificate: add x1, a = all-true.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:222-224
  theorem naiveSatCheck_noDel_nonvacuous :
      NoDeletions [.add [Lit.p 1]] ∧
        naiveSatCheck 1 [[Lit.p 0], [Lit.n 0, Lit.p 1]] [.add [Lit.p 1]] (fun _ => true) = true :=
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `replay_model_sound_of_noDeletions` (verbatim):

  ```lean
  -- lean/ToyDrat/Certificate.lean:241-244
  theorem replay_model_sound_of_noDeletions {addCheck : Formula → Clause → Bool}
      {ignore : DeletionPolicy} {π : List Step} {F G : Formula} {a : Assignment}
      (hnd : NoDeletions π) (hrep : replay addCheck ignore F π = some G) (ha : Satisfies a G) :
      Satisfies a F :=
  ```

  Plain reading (prose): For any addition check addCheck and any deletion policy ignore: if the certificate π contains no deletion step, the replay of π from F ends in G, and a satisfies G, then a satisfies F.

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `hnd : NoDeletions π` | With a deletion the final formula can lose clauses of F. | tight | `replay_model_sound_tight_noDel` (addCheck = addOK 0, policy honorAll, F = x0 and not x0, certificate: delete x0, G = not x0, a = all-false) |
  | `hrep : replay addCheck ignore F π = some G` | G is the result of replaying π from F. | tight | `replay_model_sound_tight_replay` (addCheck = addOK 0, policy honorAll, F = x0, empty certificate, G = empty formula (not the replay result), a = all-false) |
  | `ha : Satisfies a G` | The assignment satisfies the final formula. | tight | `replay_model_sound_tight_sat` (addCheck = addOK 0, policy honorAll, F = G = x0, empty certificate, a = all-false) |
  | `addCheck, ignore (arbitrary)` | Universally quantified: any addition check and any deletion policy. | harmless (universally quantified) | — |

  Non-vacuity witness: `replay_model_sound_nonvacuous` — Uses the unchecked addition check fun _ _ => true and the policy ignoreUnitDeletions: F = x0, certificate: add x1, G = x1 and x0, a = all-true.

**Prior art:** [CHHKS17], [Lam17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Why are deletions harmless for UNSAT verdicts but not for SAT verdicts, and what must a checker re-check?

```text
Basis: execution (Lean kernel check)
```

#### `rup-checked-deletions-sat-sound`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Tier note:** Folklore (a RUP clause is entailed, so deleting it preserves the models); no source was located that states it for SAT-certificate checking. Not claimed novel.
- **Plain claim (prose):** If satCheckRupDel accepts the assignment a for the formula F and the certificate π at some budget -- that is, the replay succeeds, with every deletion of a clause C from the current formula passing rupCheck with respect to that formula with all copies of C removed, every addition passing the DRAT check addOK with respect to the current formula, and a satisfying the final formula -- then a satisfies F.
- **Lean statement** (`satCheckRupDel_sound`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:307-308
theorem satCheckRupDel_sound {fuel : Nat} {F : Formula} {π : List Step} {a : Assignment}
    (h : satCheckRupDel fuel F π a = true) : Satisfies a F := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `h : satCheckRupDel fuel F π a = true` | The replay succeeds and the assignment satisfies the final formula. | tight | `satCheckRupDel_tight_accept` (F = x0, empty certificate, a = all-false) |
| `fuel (arbitrary)` | Universally quantified budget. | harmless (universally quantified) | — |

- **Non-vacuity witness:** `satCheckRupDel_nonvacuous` — F = x0 and (not x0 or x1), certificate: add x1, delete (not x0 or x1); the deletion is RUP with respect to x1 and x0; a = all-true.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:246-249
  theorem satCheckRupDel_nonvacuous :
      ¬ NoDeletions [.add [Lit.p 1], .del [Lit.n 0, Lit.p 1]] ∧
        satCheckRupDel 1 [[Lit.p 0], [Lit.n 0, Lit.p 1]] [.add [Lit.p 1], .del [Lit.n 0, Lit.p 1]]
          (fun _ => true) = true := by
  ```

**Prior art:** [CHHKS17], [Lam17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Why are deletions harmless for UNSAT verdicts but not for SAT verdicts, and what must a checker re-check?

```text
Basis: execution (Lean kernel check)
```

#### `rat-checked-deletions-sat-backward`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Tier note:** Folklore (a RAT clause can be re-added without losing satisfiability); drat-trim's FORWARD_SAT mode checks deletions operationally. Not claimed novel.
- **Plain claim (prose):** If replayRatDel replays the certificate π from F at some budget and ends in G -- every deletion of a clause C from the current formula passing the DRAT addition check addOK with respect to that formula with all copies of C removed, and every addition passing addOK with respect to the current formula -- and G is satisfiable, then F is satisfiable.
- **Lean statement** (`replayRatDel_sat_backward`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:319-321
theorem replayRatDel_sat_backward (fuel : Nat) :
    ∀ (π : List Step) (F G : Formula),
      replayRatDel fuel F π = some G → Satisfiable G → Satisfiable F := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `hrep : replayRatDel fuel F π = some G` | The checked replay succeeds and ends in G. | tight | `replayRatDel_tight_replay` (F = x0 and not x0, certificate: delete x0, G = empty formula) |
| `hG : Satisfiable G` | Satisfiability is what is carried backwards. | tight | `replayRatDel_tight_sat` (F = G = x0 and not x0, empty certificate) |
| `fuel (arbitrary)` | Universally quantified budget. | harmless (universally quantified) | — |

- **Non-vacuity witness:** `replayRatDel_nonvacuous` — Deleting the blocked clause x0 or not x1 from (x0 or not x1) and (not x0 or x1): the replay succeeds at budget 0 and the final formula is satisfiable (replayRatDel_nonvacuous); the same deletion fails the RUP deletion check at every budget (replayRatDel_final_model_not_original).

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:262-264
  theorem replayRatDel_nonvacuous :
      replayRatDel 0 [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]] [.del [Lit.p 0, Lit.n 1]] =
          some [[Lit.n 0, Lit.p 1]] ∧ Satisfiable [[Lit.n 0, Lit.p 1]] :=
  ```

**Prior art:** [JHB12], [drat-trim], [CHHKS17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Why are deletions harmless for UNSAT verdicts but not for SAT verdicts, and what must a checker re-check?

```text
Basis: execution (Lean kernel check)
```

#### `rat-after-deletion-not-rat-wrt-original`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** Starting from the satisfiable formula not x0, the certificate 'delete not x0, add x0' replays successfully (x0 is RAT with respect to the empty formula), yet x0 is neither RUP nor RAT with respect to the original formula and the original formula together with x0 is unsatisfiable.
- **Lean statement** (`rat_after_deletion_not_rat_wrt_original`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:372-375
theorem rat_after_deletion_not_rat_wrt_original :
    replay (addOK 0) honorAll [[Lit.n 0]] [.del [Lit.n 0], .add [Lit.p 0]] = some [[Lit.p 0]] ∧
      ¬ RUP [[Lit.n 0]] [Lit.p 0] ∧ ¬ RAT [[Lit.n 0]] [Lit.p 0] ∧
      Satisfiable [[Lit.n 0]] ∧ ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] := by
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `rat_after_deletion_not_rat_wrt_original` — The instance itself.
- **Positive control:** `addOK_preserves_satisfiability` — Nearby setting where the conclusion fails: without the deletion, an addition that passes addOK with respect to the original formula preserves satisfiability (addOK_preserves_satisfiability).

**Prior art:** [CHHKS17], [RB19] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Why are deletions harmless for UNSAT verdicts but not for SAT verdicts, and what must a checker re-check?

```text
Basis: execution (Lean kernel check)
```

### Specified versus operational deletion semantics

#### `operational-accepts-specified-rejects`

- **Kind:** counterexample · **Tier:** T1 · **Depth:** shallow
- **Plain claim (prose):** For x0 and not x0 with the certificate 'delete x0, add the empty clause', the operational checkers (DRAT and DRUP, which ignore the deletion of the unit clause x0) accept at budget 1, while the specified checkers (which apply every deletion) reject at every budget; so, for both DRAT and DRUP, operational acceptance does not in general imply specified acceptance.
- **Lean statement** (`operational_accepts_specified_rejects`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:390-394
theorem operational_accepts_specified_rejects :
    checkOperational 1 [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = true ∧
      (∀ fuel, checkSpecified fuel [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = false) ∧
      checkDRUP 1 ignoreUnitDeletions [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = true ∧
      (∀ fuel, checkDRUP fuel honorAll [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = false) := by
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `operational_accepts_specified_rejects` — The instance itself.
- **Positive control:** None stated: this is a separation instance (a counterexample to one inclusion), not an impossibility result.

**Prior art:** [Heu16], [AR20], [RB19], [drat-trim] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Does ignoring unit-clause deletions (operational DRAT) change soundness or the set of accepted certificates?

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Reasoning: Heule 2016 states informally that ignoring unit deletions can turn a valid DRAT proof into an invalid one and conversely; this card and specified-accepts-operational-rejects give one toy instance of each direction.

#### `specified-accepts-operational-rejects`

- **Kind:** counterexample · **Tier:** T1 · **Depth:** shallow
- **Plain claim (prose):** For not x0 together with fullSquare and the certificate 'delete not x0, add x0, add x1, add the empty clause', the specified DRAT checker accepts at budget 3 (after the deletion, x0 is RAT because no clause contains not x0), while the operational DRAT checker, which keeps not x0, rejects at every budget; so for DRAT, ignoring unit deletions can reject certificates the specified semantics accepts.
- **Lean statement** (`specified_accepts_operational_rejects`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:414-416
theorem specified_accepts_operational_rejects :
    checkSpecified 3 unitPlusSquare unitDeletionThenRAT = true ∧
      ∀ fuel, checkOperational fuel unitPlusSquare unitDeletionThenRAT = false := by
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `specified_accepts_operational_rejects` — The instance itself (unitPlusSquare, unitDeletionThenRAT).
- **Positive control:** `checkDRUP_specified_implies_operational` — Nearby setting where the conclusion fails: for the DRUP checker, specified acceptance implies operational acceptance (checkDRUP_specified_implies_operational).

**Prior art:** [Heu16], [AR20], [RB19], [drat-trim] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Does ignoring unit-clause deletions (operational DRAT) change soundness or the set of accepted certificates?

```text
Basis: execution (Lean kernel check)
```

#### `drup-honor-all-strictest`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Plain claim (prose):** For the DRUP checker (every addition must pass rupCheck at the given budget) with all-copies syntactic deletion, for every budget, every (stateless) deletion policy, every certificate, and all formulas F and G: if G contains every clause of F (FormulaSub F G) and the checker that applies every deletion accepts the certificate for F, then the checker with that policy accepts it for G. In particular (G = F, policy ignoreUnitDeletions; checkDRUP_specified_implies_operational), operational DRUP acceptance includes specified DRUP acceptance.
- **Lean statement** (`checkDRUP_honorAll_implies_any_policy`, verbatim):

```lean
-- lean/ToyDrat/Certificate.lean:455-457
theorem checkDRUP_honorAll_implies_any_policy (fuel : Nat) (ignore : DeletionPolicy) :
    ∀ (π : List Step) (F G : Formula), FormulaSub F G →
      checkDRUP fuel honorAll F π = true → checkDRUP fuel ignore G π = true := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `hFG : FormulaSub F G` | Lets the formula grow, which the induction over the certificate uses; the corollary takes G = F. | tight | `checkDRUP_policy_tight_sub` (F = x0 and not x0, G empty, certificate: add the empty clause) |
| `h : checkDRUP fuel honorAll F π = true` | The specified DRUP checker accepts. | tight | `checkDRUP_policy_tight_accept` (F = G = x0 or x1, certificate: add the empty clause) |
| `fuel, ignore (arbitrary)` | Universally quantified budget and policy. | harmless (universally quantified) | — |

- **Non-vacuity witness:** `checkDRUP_policy_nonvacuous` — F = x0 and fullSquare, G = x3 and F (a strict superset), certificate: add x1, delete x0 (a unit deletion on which the two policies differ), add the empty clause.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:297-302
  theorem checkDRUP_policy_nonvacuous :
      FormulaSub ([Lit.p 0] :: fullSquare) ([Lit.p 3] :: [Lit.p 0] :: fullSquare) ∧
        ¬ FormulaSub ([Lit.p 3] :: [Lit.p 0] :: fullSquare) ([Lit.p 0] :: fullSquare) ∧
        checkDRUP 3 honorAll ([Lit.p 0] :: fullSquare) [.add [Lit.p 1], .del [Lit.p 0], .add []] = true ∧
        applyDel honorAll ([Lit.p 1] :: [Lit.p 0] :: fullSquare) [Lit.p 0] ≠
          applyDel ignoreUnitDeletions ([Lit.p 1] :: [Lit.p 0] :: fullSquare) [Lit.p 0] := by
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `checkDRUP_specified_implies_operational` (verbatim):

  ```lean
  -- lean/ToyDrat/Certificate.lean:487-488
  theorem checkDRUP_specified_implies_operational (fuel : Nat) (F : Formula) (π : List Step)
      (h : checkDRUP fuel honorAll F π = true) : checkDRUP fuel ignoreUnitDeletions F π = true :=
  ```

  Plain reading (prose): If checkDRUP fuel honorAll F π = true, then checkDRUP fuel ignoreUnitDeletions F π = true (the main theorem with G = F and ignore = ignoreUnitDeletions).

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `h : checkDRUP fuel honorAll F π = true` | As in the main theorem. | tight | `checkDRUP_policy_tight_accept` (F = x0 or x1, certificate: add the empty clause) |

  Non-vacuity witness: `checkDRUP_policy_nonvacuous`.

**Prior art:** [HHW13], [Heu16], [AR20], [RB19], [drat-trim] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Does ignoring unit-clause deletions (operational DRAT) change soundness or the set of accepted certificates?

```text
Basis: execution (Lean kernel check)
```

### Hint-driven (LRAT-style) checking

#### `lrat-hint-replay-implies-rup`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim (prose):** If replaying the hinted clauses of F in order from the negation of C succeeds -- each hinted clause has exactly one non-falsified literal occurrence, which is pushed on the trail (it may already be there), until a hinted clause has no non-falsified literal occurrence, after which remaining hints are not examined -- then budgeted propagation from the negation of C reaches a conflict within (number of hints) rounds, so C is RUP with respect to F and F entails C.
- **Lean statement** (`lrat_hint_replay_implies_rup`, verbatim):

```lean
-- lean/ToyDrat/Lrat.lean:111-113
theorem lrat_hint_replay_implies_rup {F : Formula} {C : Clause} {hints : List Nat}
    (h : lratRupCheck F C hints = true) :
    unitProp hints.length F (negClause C) = .conflict ∧ RUP F C :=
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `h : lratRupCheck F C hints = true` | The hint replay succeeds. | tight | `lrat_tight_accept` (F = x0 or x1, C = x0, hints = [0]) |

- **Non-vacuity witness:** `lratRupCheck_chain3` — chain3 = x0, (not x0 or x1), not x1 with hints [0, 1, 2] for the empty clause.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Lrat.lean:126
  theorem lratRupCheck_chain3 : lratRupCheck chain3 [] [0, 1, 2] = true := by decide
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `lrat_hint_replay_implies_entails` (verbatim):

  ```lean
  -- lean/ToyDrat/Lrat.lean:118-119
  theorem lrat_hint_replay_implies_entails {F : Formula} {C : Clause} {hints : List Nat}
      (h : lratRupCheck F C hints = true) : Entails F C :=
  ```

  Plain reading (prose): If lratRupCheck F C hints = true, then F entails C.

  | Hypothesis | Role | Tightness | Counterexample (witness class) |
  | :--- | :--- | :--- | :--- |
  | `h : lratRupCheck F C hints = true` | As in the main theorem. | tight | `lrat_tight_accept` (F = x0 or x1, C = x0, hints = [0]) |

  Non-vacuity witness: `lratRupCheck_chain3`.

**Prior art:** [CHHKS17], [CMS17], [Lean-LRAT], [THM21], [Lam17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Is a hint-driven (LRAT-style) checker, which does no unit-clause search, still sound, and what must it check per hint?

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Reasoning: from the Lean 4 core v4.34.1 source (commit 5045d0056413266e57c625dcd7c365b10e377c52): DefaultClause carries the invariants nodupkey (no variable occurs with both polarities) and nodup (no repeated literal) (Internal/Clause.lean lines 95-98), so its clauses satisfy both side conditions of lratRupCheck_complete_of_wellformed by construction; performRupAdd first inserts the negated clause as units and succeeds if that yields a contradiction (Internal/Formula/Implementation.lean lines 219-225); confirmRupHint stops examining hints once the empty clause is derived and continues without error when a hinted clause reduces to a literal that is already assigned (lines 176-195), as the toy hintReplay does. compactLratChecker skips (does not add) a RAT step whose pivot is not in the clause (Internal/CompactLRATChecker.lean lines 48-56). Whether its verdicts coincide with lratRupCheck on well-formed inputs is not proved here.

#### `lrat-hint-order-matters`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** The empty clause is RUP with respect to chain3 and the hint list [0, 1, 2] is accepted, but the same clauses in the order [1, 0, 2] are rejected because clause 1 is not unit under the empty trail.
- **Lean statement** (`lrat_hint_order_matters`, verbatim):

```lean
-- lean/ToyDrat/Lrat.lean:133-135
theorem lrat_hint_order_matters :
    RUP chain3 [] ∧ lratRupCheck chain3 [] [0, 1, 2] = true ∧
      lratRupCheck chain3 [] [1, 0, 2] = false :=
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `lrat_hint_order_matters` — The instance itself.

**Prior art:** [CHHKS17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Is a hint-driven (LRAT-style) checker, which does no unit-clause search, still sound, and what must it check per hint?

```text
Basis: execution (Lean kernel check)
```

#### `sloppy-hint-replay-unsound`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim (prose):** A hint replay that assigns the first non-falsified literal of each hinted clause without checking that it is the only one accepts the hints [0, 1] as a refutation of the satisfiable formula (x0 or x1) and not x0, while the unit-checking replay rejects them.
- **Lean statement** (`sloppy_hint_replay_unsound`, verbatim):

```lean
-- lean/ToyDrat/Lrat.lean:141-144
theorem sloppy_hint_replay_unsound :
    sloppyHintReplay [[Lit.p 0, Lit.p 1], [Lit.n 0]] (negClause []) [0, 1] = true ∧
      Satisfiable [[Lit.p 0, Lit.p 1], [Lit.n 0]] ∧
      lratRupCheck [[Lit.p 0, Lit.p 1], [Lit.n 0]] [] [0, 1] = false :=
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances (or, for an unconditional theorem, universally quantified parameters only).

- **Non-vacuity witness:** `sloppy_hint_replay_unsound` — The instance itself.
- **Positive control:** `lrat_hint_replay_implies_rup` — Nearby settings where the conclusion fails, each proved.

**Prior art:** [CHHKS17] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Reference point for: Is a hint-driven (LRAT-style) checker, which does no unit-clause search, still sound, and what must it check per hint? It isolates the per-hint test of lrat-hint-replay-implies-rup.

```text
Basis: execution (Lean kernel check)
```

#### `lrat-hint-replay-complete-wellformed`

- **Kind:** theorem · **Tier:** T1 · **Depth:** substantive
- **Tier note:** LRAT is designed so that hints can be produced for RUP steps of well-formed clauses; the precise toy statement, with both side conditions shown tight (each on the witness class recorded in its ledger entry; they are not logically necessary, see lratRupCheck_side_conditions_not_necessary), is not known to be mechanized elsewhere. Not claimed novel.
- **Plain claim (prose):** If C contains no complementary pair of literals (NonTautological C), no clause of F repeats a literal (DupFreeClauses F), and C is RUP with respect to F, then some hint list is accepted by lratRupCheck F C. Each side condition is tight: dropping either one admits an instance in which C is RUP and every hint list is rejected (lratRupCheck_incomplete_tautology, lratRupCheck_incomplete_dup_lits). Secondary theorems: for every F and C, the deduplicating variant lratRupCheckDedup, which also tests the negated clause for a complementary pair, accepts some hint list if and only if C is RUP with respect to F (lratRupCheckDedup_exists_iff_rup); and the tautological resolvent of the blocked clause x0 or not x1 on x0 with not x0 or x1 is RUP with respect to not x0 or x1 while lratRupCheck rejects every hint list for it (lratRupCheck_rejects_blocked_resolvent).
- **Lean statement** (`lratRupCheck_complete_of_wellformed`, verbatim):

```lean
-- lean/ToyDrat/Lrat.lean:495-497
theorem lratRupCheck_complete_of_wellformed {F : Formula} {C : Clause}
    (hC : NonTautological C) (hF : DupFreeClauses F) (h : RUP F C) :
    ∃ hints, lratRupCheck F C hints = true := by
```

**Hypothesis ledger.**

| Hypothesis | Role | Tightness | Counterexample (witness class) |
| :--- | :--- | :--- | :--- |
| `hC : NonTautological C` | lratRupCheck does not test the negated clause for a complementary pair. Tight (on F empty, C = x0 or not x0). | tight | `lratRupCheck_incomplete_tautology` (F empty, C = x0 or not x0) |
| `hF : DupFreeClauses F` | lratRupCheck counts literal occurrences, so x0 or x0 is never unit for it. Tight (on F = (x0 or x0) and (not x0 or not x0), C = []). | tight | `lratRupCheck_incomplete_dup_lits` (F = (x0 or x0) and (not x0 or not x0), C = []) |
| `h : RUP F C` | Accepted hint lists certify RUP (lrat_hint_replay_implies_rup). | tight | `lrat_complete_tight_rup` (F = x0 or x1, C = x0) |

- **Non-vacuity witness:** `lrat_complete_nonvacuous` — chain3 (no clause repeats a literal), C = [] (no complementary pair), C RUP with respect to chain3.

  Statement (verbatim):

  ```lean
  -- lean/ToyDrat/Cards.lean:333-334
  theorem lrat_complete_nonvacuous :
      NonTautological [] ∧ DupFreeClauses chain3 ∧ RUP chain3 [] :=
  ```

**Secondary theorems** (listed in this card's `lean_names`):

- `lratRupCheckDedup_exists_iff_rup` (verbatim):

  ```lean
  -- lean/ToyDrat/Lrat.lean:439-440
  theorem lratRupCheckDedup_exists_iff_rup (F : Formula) (C : Clause) :
      (∃ hints, lratRupCheckDedup F C hints = true) ↔ RUP F C := by
  ```

  Plain reading (prose): For every F and C: some hint list is accepted by lratRupCheckDedup F C if and only if RUP F C, where lratRupCheckDedup first tests the negated clause for a complementary pair and replays hints on deduplicated literals. No hypotheses; the main theorem follows because lratRupCheckDedup and lratRupCheck agree on well-formed inputs (lratRupCheckDedup_eq_of_wellformed).

  No hypotheses (concrete instance or universally quantified parameters only).

- `lratRupCheck_rejects_blocked_resolvent` (verbatim):

  ```lean
  -- lean/ToyDrat/Lrat.lean:553-556
  theorem lratRupCheck_rejects_blocked_resolvent :
      RUP [[Lit.n 0, Lit.p 1]] (resolventOn [Lit.p 0, Lit.n 1] [Lit.n 0, Lit.p 1] (Lit.p 0)) ∧
        ∀ hints, lratRupCheck [[Lit.n 0, Lit.p 1]]
          (resolventOn [Lit.p 0, Lit.n 1] [Lit.n 0, Lit.p 1] (Lit.p 0)) hints = false :=
  ```

  Plain reading (prose): The tautological resolvent x0 or not x1 or x1 of the blocked clause x0 or not x1 (pivot x0) with not x0 or x1 is RUP with respect to not x0 or x1, and lratRupCheck rejects every hint list for it.

  No hypotheses (concrete instance or universally quantified parameters only).

**Prior art:** [CHHKS17], [Heu16], [Lean-LRAT] (full records, with what was read of each, under **Evidence → Primary sources**).

**Design question.** Is a hint-driven (LRAT-style) checker, which does no unit-clause search, still sound, and what must it check per hint?

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Reasoning: from the Lean 4 core v4.34.1 source (commit 5045d0056413266e57c625dcd7c365b10e377c52): DefaultClause carries the invariants nodupkey (no variable occurs with both polarities) and nodup (no repeated literal) (Internal/Clause.lean lines 95-98), so its clauses satisfy both side conditions of lratRupCheck_complete_of_wellformed by construction; performRupAdd first inserts the negated clause as units and succeeds if that yields a contradiction (Internal/Formula/Implementation.lean lines 219-225); confirmRupHint stops examining hints once the empty clause is derived and continues without error when a hinted clause reduces to a literal that is already assigned (lines 176-195), as the toy hintReplay does. compactLratChecker skips (does not add) a RAT step whose pivot is not in the clause (Internal/CompactLRATChecker.lean lines 48-56). Whether its verdicts coincide with lratRupCheck on well-formed inputs is not proved here.

## Boundaries

### Non-claims (per result)

What each result does **not** show. These are part of each result's meaning.

**Every result** (this non-claim is recorded on every card in `results.json`): Toy model: literals are (variable, polarity) pairs, clauses and formulas are lists, unit propagation is a round-based propagator with a budget. The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about production solvers and checkers (drat-trim, cake_lpr, Lean's bv_decide LRAT checker, SMT solvers that emit clausal proofs); any correspondence with them is a derived (modeling bridge) claim, not a theorem.

**`rup-implies-entails`** (`rup_implies_entails`):

- Does not claim the converse: entailment does not imply RUP, because unit propagation is incomplete (entails_not_implies_rup), and this is not limited to unsatisfiable formulas or the empty clause (entails_not_implies_rup_satisfiable_nonempty).
- Adding C preserves logical equivalence if and only if F entails C (equivalent_cons_iff_entails), for every F and C. RUP is sufficient but not necessary: the clause x0 is RAT but not RUP with respect to the satisfiable formula x0OrFullSquare, and adding it preserves equivalence because it is entailed (rat_not_rup_addition_preserves_equivalence). RAT additions in general need not preserve equivalence (rat_addition_not_equivalence).
- Equivalence is over total assignments of all variables.
- The theorem is about the unbudgeted predicate RUP. A passing rupCheck at any budget implies RUP (rupCheck_sound); a failing rupCheck at one budget does not by itself refute RUP, since RUP quantifies over all budgets (no separate theorem; not proved here).
- (and the toy-model non-claim above)

**`entails-not-implies-rup`** (`entails_not_implies_rup`):

- Two instances: no bound is claimed on how far an entailed clause can be from RUP.
- Does not say fullSquare has no short certificate: the two-step certificate 'add x1, add the empty clause' is accepted by checkSpecified at budget 3 (checkSpecified_fullSquare).
- (and the toy-model non-claim above)

**`rat-witness`** (`ratOn_witness_satisfies`):

- Does not say a itself satisfies C and F; the witness can differ from a in the variable of p (as in ratOn_witness_nonvacuous, where a falsifies C).
- The pivot here is any literal of C; the DRAT check fixes the first literal (rat-check-depends-on-pivot-order).
- RAT additions need not preserve the models of F restricted to the variables of F: in rat_addition_loses_projected_model the pivot variable x0 occurs in F = (not x0 or x1), and no model of the extended formula agrees with the model x0 = false, x1 = true of F on x0 and x1.
- RAT is not monotone in the formula: x0 is RAT with respect to x1 but not with respect to (not x0) and x1 (rat_not_monotone_in_formula), so a RAT step valid for F need not stay valid when further clauses (for example assumption clauses) are conjoined.
- ratWitness maps a model forward across one clause addition (from F to C and F). Reconstructing a model of F from a model of a formula from which RAT-checked clauses were deleted is covered here only as satisfiability (replayRatDel_sat_backward) and for one step (replayRatDel_final_model_not_original); iterated reconstruction is not proved here.
- (and the toy-model non-claim above)

**`rat-addition-preserves-satisfiability`** (`rat_addition_preserves_satisfiability`):

- Satisfiability only, not equivalence: models of F can be lost (rat_addition_not_equivalence), even restricted to the variables of F (rat_addition_loses_projected_model).
- Does not say F entails C.
- The empty clause is never RAT (RAT F [] is False by definition: there is no pivot); in addOK, adding the empty clause must pass rupCheck, because ratCheck rejects it at every budget (ratCheck_example_neg).
- RAT is not monotone in the formula (rat_not_monotone_in_formula): validity of a RAT step for F says nothing about F with further clauses.
- RATOn F C p without p ∈ C need not preserve satisfiability (ratOn_without_mem_unsound, ratOn_sat_tight_mem).
- (and the toy-model non-claim above)

**`rat-addition-not-equivalence`** (`rat_addition_not_equivalence`):

- Does not show any satisfiability loss: the formula stays satisfiable (rat-addition-preserves-satisfiability).
- Here the added variable x0 does not occur in F. That does not mean RAT additions preserve models restricted to the variables of F: when the pivot variable occurs in F they can remove such models (rat_addition_loses_projected_model).
- (and the toy-model non-claim above)

**`rup-implies-rat`** (`rup_implies_rat_of_ne_nil`):

- RAT does not imply RUP: x0 is RAT but not RUP with respect to x0OrFullSquare (rat_not_rup_addition_preserves_equivalence); x0 is RAT with respect to x1 without being entailed by it (rat_addition_not_equivalence); and x0 or not x1 is RAT with respect to not x0 or x1 (RAT_example_pos) without being entailed by it (RAT_example_pos_not_entailed).
- The auxiliary predicate RATOn F C p omits the literature requirement p ∈ C, so RATOn [] [] x0 holds vacuously. Unlike RAT F C, RATOn F C p alone need not preserve satisfiability (ratOn_without_mem_unsound, ratOn_sat_tight_mem); together with p ∈ C it does (ratOn_preserves_satisfiability). The corollary rup_implies_ratOn should be read with that in mind: it says nothing about satisfiability for p ∉ C.
- Stated for the unbudgeted predicates RUP and RAT; the analogous statement for the budgeted checkers rupCheck and ratCheck at a fixed budget is not stated (not proved here).
- (and the toy-model non-claim above)

**`rat-check-depends-on-pivot-order`** (`rat_check_depends_on_pivot_order`):

- Does not say a non-first pivot is unsound: RAT on any literal of C preserves satisfiability (ratOn_preserves_satisfiability).
- Does not describe how particular checkers choose pivots beyond the DRAT first-literal convention cited.
- (and the toy-model non-claim above)

**`refutation-checker-sound-generic`** (`checkGen_sound_unsat_of_addCheck_preserves_sat`):

- Says nothing about SAT verdicts or about models of the final formula (naive-sat-check-unsound-with-deletions).
- DeletionPolicy is a stateless function of the current formula and the deleted clause. History-dependent rules, such as drat-trim's skipping of deletions of clauses that are the reason of a top-level assignment ('pseudo-units'), are not policies in this sense; covering them needs a separate argument (for UNSAT soundness: they only keep clauses), which is not given here (not proved here).
- checkGen stops at the first accepted addition of the empty clause and does not examine later steps; any later addition would pass the RUP check anyway, since the formula then contains the empty clause (rupCheck_of_nil_mem). The DRAT format likewise ignores lines after the empty clause (Heule 2016). The empty certificate is rejected even when F already contains the empty clause (checkGen_empty_certificate).
- Says nothing about completeness (accepting all valid certificates).
- (and the toy-model non-claim above)

**`drat-checker-sound-unsat`** (`checkDRAT_sound_unsat`):

- Soundness only: the specified and operational checkers accept different certificates (operational-accepts-specified-rejects, specified-accepts-operational-rejects).
- The toy deletion removes every syntactically equal copy of the clause; the DRAT format removes one copy, matched up to literal order (Heule 2016). UNSAT soundness for that deletion semantics is expected by the same argument (a deletion only removes clauses) but is not proved here.
- DeletionPolicy is a stateless function of the current formula and the deleted clause. History-dependent rules, such as drat-trim's skipping of deletions of clauses that are the reason of a top-level assignment ('pseudo-units'), are not policies in this sense; covering them needs a separate argument (for UNSAT soundness: they only keep clauses), which is not given here (not proved here).
- ignoreUnitDeletions tests the raw list length C.length = 1: the deletion of x0 or x0 is applied, not ignored (ignoreUnitDeletions_example_dup), whereas drat-trim removes duplicate literals on input and treats that clause as a unit.
- drat-trim's default BACKWARD_UNSAT mode also skips RAT candidate clauses that are not marked active (drat-trim.c at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985, lines 565-567), so it may accept RAT additions that both checkSpecified and checkOperational reject; this is read from the source and no instance is constructed here (not proved here).
- An accepted DRAT certificate need not remain accepted for a formula with more clauses: drat_certificate_not_monotone_in_formula gives a certificate accepted for fullSquare and rejected at every budget for not x0 and fullSquare.
- Steps after the first accepted empty clause are not examined (see refutation-checker-sound-generic).
- No claim about the correctness of any production checker or of its parsing, clause identification, or memory management.
- (and the toy-model non-claim above)

**`drat-steps-preserve-satisfiability-forward`** (`addOK_preserves_satisfiability`):

- Deletions do not carry unsatisfiability forward (deletion_can_turn_unsat_into_sat).
- RAT additions need not carry individual models forward (rat_addition_not_equivalence); RUP additions do (rup_addition_preserves_equivalence).
- Neither the check nor its verdict is monotone in the formula (rat_not_monotone_in_formula, drat_certificate_not_monotone_in_formula).
- (and the toy-model non-claim above)

**`naive-sat-check-unsound-with-deletions`** (`naiveSatCheck_unsound_with_deletions`):

- Concerns one checker whose deletions are unchecked; it is not a statement about every SAT checker that accepts certificates with deletions.
- Escape hatches: (1) testing the assignment against the original formula (sound by the definition of Satisfies; no separate theorem is stated); and, each proved: (2) deletion-free certificates (naiveSatCheck_sound_of_noDeletions; for any addition check and policy: replay_model_sound_of_noDeletions); (3) checking each deletion to be RUP with respect to the formula without the deleted clause, after which testing against the final formula alone is sound (satCheckRupDel_sound); (4) checking each deletion with the DRAT addition check with respect to the formula without the deleted clause, which carries satisfiability (not models) backwards (replayRatDel_sat_backward, replayRatDel_final_model_not_original).
- Does not affect UNSAT verdicts, which stay sound under every deletion policy (drat-checker-sound-unsat).
- (and the toy-model non-claim above)

**`naive-sat-check-sound-without-deletions`** (`naiveSatCheck_sound_of_noDeletions`):

- The addition checks play no role: deletion-free replay carries models backwards for any addition check and any policy (replay_model_sound_of_noDeletions).
- Does not say solver-produced certificates are deletion-free, nor that deletion-free certificates are needed (satCheckRupDel_sound allows checked deletions).
- (and the toy-model non-claim above)

**`rup-checked-deletions-sat-sound`** (`satCheckRupDel_sound`):

- Without the deletion check this is naiveSatCheck, which is unsound (naiveSatCheck_unsound_with_deletions).
- A RAT check on deletions does not suffice for this conclusion: replayRatDel_final_model_not_original gives a model of the final formula that is not a model of the original one.
- The deletion check is RUP with respect to the formula after the deletion (all copies of C removed). Checking the deleted clause against the formula that still contains it would accept every deletion, because a clause that occurs in the formula passes rupCheck at every budget (rupCheck_of_mem).
- (and the toy-model non-claim above)

**`rat-checked-deletions-sat-backward`** (`replayRatDel_sat_backward`):

- Satisfiability only: a model of the final formula need not be a model of the original one (replayRatDel_final_model_not_original), so testing the claimed assignment against the final formula alone is not a sound SAT check for this replay; in that one-step instance, ratWitness turns the model of the final formula into a model of the original formula. Iterated model reconstruction is not proved here.
- Correspondence with drat-trim's FORWARD_SAT mode is a derived (modeling bridge) claim; drat-trim's redundancyCheck returns success early for clauses not marked active (drat-trim.c at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985, lines 621-622), which is not modeled.
- (and the toy-model non-claim above)

**`rat-after-deletion-not-rat-wrt-original`** (`rat_after_deletion_not_rat_wrt_original`):

- Does not contradict UNSAT soundness: refutations remain sound under every deletion policy (checkDRAT_sound_unsat).
- Shows, by one instance, that a clause accepted after an unchecked deletion need not be a consequence of the original formula, nor a satisfiability-preserving extension of it; it does not say that this happens for every such clause.
- (and the toy-model non-claim above)

**`operational-accepts-specified-rejects`** (`operational_accepts_specified_rejects`):

- Does not show the operational checker is unsound; the formula is unsatisfiable and operational acceptance is sound (drat-checker-sound-unsat).
- ignoreUnitDeletions tests the raw list length C.length = 1: the deletion of x0 or x0 is applied, not ignored (ignoreUnitDeletions_example_dup), whereas drat-trim removes duplicate literals on input and treats that clause as a unit.
- DeletionPolicy is a stateless function of the current formula and the deleted clause. History-dependent rules, such as drat-trim's skipping of deletions of clauses that are the reason of a top-level assignment ('pseudo-units'), are not policies in this sense; covering them needs a separate argument (for UNSAT soundness: they only keep clauses), which is not given here (not proved here).
- drat-trim's default BACKWARD_UNSAT mode also skips RAT candidate clauses that are not marked active (drat-trim.c at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985, lines 565-567), so it may accept RAT additions that both checkSpecified and checkOperational reject; this is read from the source and no instance is constructed here (not proved here).
- The toy specified checker matches deleted clauses as lists and removes every copy; a deletion whose literals are permuted is ignored (permuted_deletion_is_ignored).
- (and the toy-model non-claim above)

**`specified-accepts-operational-rejects`** (`specified_accepts_operational_rejects`):

- Relies on a RAT step: for the DRUP checker (RUP-only additions), every certificate accepted by the specified checker is accepted by the operational one (checkDRUP_specified_implies_operational).
- Does not claim this pattern occurs in solver-generated proofs. The documented solver-side problem is the other direction: spurious unit deletions that only operational checkers tolerate (Altmanninger and Rebola Pardo 2020, abstract), as in operational-accepts-specified-rejects.
- ignoreUnitDeletions tests the raw list length C.length = 1: the deletion of x0 or x0 is applied, not ignored (ignoreUnitDeletions_example_dup), whereas drat-trim removes duplicate literals on input and treats that clause as a unit.
- DeletionPolicy is a stateless function of the current formula and the deleted clause. History-dependent rules, such as drat-trim's skipping of deletions of clauses that are the reason of a top-level assignment ('pseudo-units'), are not policies in this sense; covering them needs a separate argument (for UNSAT soundness: they only keep clauses), which is not given here (not proved here).
- (and the toy-model non-claim above)

**`drup-honor-all-strictest`** (`checkDRUP_honorAll_implies_any_policy`):

- RUP-only additions are part of the statement (checkDRUP), not a hypothesis. It does not hold for DRAT: specified_accepts_operational_rejects (policy change) and drat_certificate_not_monotone_in_formula (larger formula).
- The inclusion is strict (operational-accepts-specified-rejects uses only RUP steps).
- Depends on all-copies deletion: with one-copy deletion the FormulaSub form is false (one_copy_deletion_breaks_drup_monotonicity: F = x0, x0, not x0 and G = x0, not x0 with 'delete x0, add the empty clause'). A version with multiset inclusion (each clause occurring in G at least as often as in F) is plausible but not proved here.
- Deleted clauses are matched as lists, so a deletion whose literals are permuted relative to the stored clause is ignored and the specified checker can accept certificates that a checker matching up to literal order rejects (permuted_deletion_is_ignored).
- DeletionPolicy is a stateless function of the current formula and the deleted clause. History-dependent rules, such as drat-trim's skipping of deletions of clauses that are the reason of a top-level assignment ('pseudo-units'), are not policies in this sense; covering them needs a separate argument (for UNSAT soundness: they only keep clauses), which is not given here (not proved here).
- (and the toy-model non-claim above)

**`lrat-hint-replay-implies-rup`** (`lrat_hint_replay_implies_rup`):

- Covers RUP hints only; LRAT RAT steps (negative hints) and clause identifiers that survive deletions are not modeled.
- Hint replay is order-sensitive: permuting an accepted hint list can make it rejected (lrat-hint-order-matters). This is not the same as incompleteness, which is treated in lrat-hint-replay-complete-wellformed.
- The per-hint test counts non-falsified literal occurrences: it rejects a clause with a repeated unassigned literal such as x0 or x0 (as in lratRupCheck_incomplete_dup_lits), accepts an already satisfied clause whose only non-falsified literal is true (lratRupCheck_example_satisfied_hint), and stops at the first fully falsified clause without examining or bounds-checking later hints (lratRupCheck_example_trailing_hints).
- Skipping the check that each hinted clause has at most one non-falsified literal occurrence is unsound: sloppy-hint-replay-unsound gives an accepted refutation of a satisfiable formula.
- (and the toy-model non-claim above)

**`lrat-hint-order-matters`** (`lrat_hint_order_matters`):

- Shows order-sensitivity of a fixed hint list, not incompleteness: if C has no complementary pair of literals, no clause of F repeats a literal, and C is RUP with respect to F, then some hint list for C is accepted (lratRupCheck_complete_of_wellformed).
- lratRupCheck is not complete in general: it rejects every hint list for the tautological clause x0 or not x0, which is RUP with respect to the empty formula (lratRupCheck_incomplete_tautology), and for the empty clause with respect to (x0 or x0) and (not x0 or not x0), where it is RUP (lratRupCheck_incomplete_dup_lits).
- (and the toy-model non-claim above)

**`sloppy-hint-replay-unsound`** (`sloppy_hint_replay_unsound`):

- Does not describe any existing checker; sloppyHintReplay is a strawman isolating the per-hint test of lrat-hint-replay-implies-rup.
- (and the toy-model non-claim above)

**`lrat-hint-replay-complete-wellformed`** (`lratRupCheck_complete_of_wellformed`):

- Existence only: no bound on the length of the hint list is stated, and the hint list is not claimed to be computable by any particular procedure (the proof extracts it from a propagation run).
- The side conditions are tight but not logically necessary: each can fail while C is RUP and some hint list is still accepted (lratRupCheck_side_conditions_not_necessary).
- Clause identifiers are positions in the current formula; LRAT identifiers, RAT hints, and deletions of hinted clauses are not modeled.
- The DRAT and LRAT formats exclude tautological clauses and repeated literals (Heule 2016, pp. 2-3; Cruz-Filipe et al. 2017, Section 1), so the side conditions correspond to well-formed input; that correspondence is a derived (modeling bridge) claim.
- (and the toy-model non-claim above)

### Escape hatches

Which hypotheses or modeling choices, if dropped or changed, defeat a negative result or a theorem
(each item cites the proved theorem that shows it):

- `naive-sat-check-unsound-with-deletions`: the unsoundness disappears if the claimed assignment is
  tested against the original formula (by the definition of `Satisfies`; no separate theorem), if the
  certificate has no deletion (`naiveSatCheck_sound_of_noDeletions`, `replay_model_sound_of_noDeletions`),
  if each deletion is checked to be RUP with respect to the formula without the deleted clause
  (`satCheckRupDel_sound`), or, for satisfiability rather than for the claimed model, if each deletion is
  checked with the DRAT addition check (`replayRatDel_sat_backward`; the model itself is not carried
  back: `replayRatDel_final_model_not_original`).
- `drup-honor-all-strictest` depends on RUP-only additions (false for DRAT:
  `specified_accepts_operational_rejects`, `drat_certificate_not_monotone_in_formula`) and on all-copies
  deletion (false for one-copy deletion: `one_copy_deletion_breaks_drup_monotonicity`).
- `rat-addition-preserves-satisfiability` and `rat-witness` depend on the pivot being a literal of the
  clause: `RATOn F C p` without `p ∈ C` need not preserve satisfiability (`ratOn_without_mem_unsound`,
  `ratOn_sat_tight_mem`, `ratOn_witness_tight_mem`).
- `lrat-hint-replay-complete-wellformed`: dropping either side condition admits a RUP clause with no
  accepted hint list (`lratRupCheck_incomplete_tautology`, `lratRupCheck_incomplete_dup_lits`); the
  deduplicating variant needs neither (`lratRupCheckDedup_exists_iff_rup`). The side conditions are not
  logically necessary (`lratRupCheck_side_conditions_not_necessary`).
- `sloppy-hint-replay-unsound`: restoring the per-hint check (at most one non-falsified literal
  occurrence) restores soundness (`lrat_hint_replay_implies_rup`).
- `entails-not-implies-rup`: an entailed clause that is not RUP can still be reached by a certificate
  with intermediate additions; e.g. the two-step certificate 'add x1, add the empty clause' for
  `fullSquare` is accepted by `checkSpecified` at budget 3 (`checkSpecified_fullSquare`).

### Hypotheses with `unknown` tightness

None. Every hypothesis of every result and of every secondary theorem is either `tight`, with a
named, kernel-checked counterexample in which all other hypotheses hold and the conclusion fails, or
`harmless` (a universally quantified parameter such as the budget `fuel`, the deletion policy
`ignore`, or the addition check `addCheck`).

### Stronger or adjacent statements not established here

Each of these is explicitly **not proved** in this package (status: *not examined* unless stated):

- UNSAT soundness for a deletion semantics that removes one copy matched up to literal order (the
  DRAT-format semantics); and a DRUP policy-inclusion theorem under multiset inclusion with one-copy
  deletion (plausible; *unknown*).
- Soundness or completeness statements for history-dependent deletion rules (drat-trim's retention of
  reason clauses), for drat-trim's active-clause filtering of RAT candidates, or for any production
  checker's parsing, clause identification, or memory management.
- Iterated model reconstruction across several RAT-checked deletions (only satisfiability is carried
  back, and one-step reconstruction is exhibited in `replayRatDel_final_model_not_original`).
- The budgeted analogue of `rup-implies-rat` (`rupCheck` implies `ratCheck` at a fixed budget).
- Agreement of the Lean 4 core LRAT checker's verdicts with `lratRupCheck` on well-formed inputs;
  LRAT RAT hints; identifiers that survive deletions; bounds on hint-list length.
- Any quantitative statement: no complexity, size, or model-count claim is made.

### Disproved or dropped draft statements

None: every result and every secondary theorem stated in this package is proved. The following natural stronger statements are **known not to apply**; each is
refuted by a kernel-checked theorem in the package:

- "Every RUP clause has a hint list accepted by `lratRupCheck`": false
  (`lratRupCheck_incomplete_tautology`, `lratRupCheck_incomplete_dup_lits`,
  `lratRupCheck_rejects_blocked_resolvent`).
- "Only RUP additions preserve logical equivalence": false (`rat_not_rup_addition_preserves_equivalence`).
- "Entailment implies RUP", including for satisfiable formulas and nonempty clauses: false
  (`entails_not_implies_rup`, `entails_not_implies_rup_satisfiable_nonempty`).
- "`RATOn F C p` alone preserves satisfiability": false (`ratOn_without_mem_unsound`).
- "RAT, or acceptance of a DRAT certificate, is monotone in the formula": false
  (`rat_not_monotone_in_formula`, `drat_certificate_not_monotone_in_formula`).
- "The DRUP policy inclusion holds with one-copy deletion": false
  (`one_copy_deletion_breaks_drup_monotonicity`).

## Evidence

### Kernel-check record

```text
Basis: execution (Lean kernel check)
```

- Toolchain: `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), no Mathlib, no Lake dependencies. `lake build` of the library `ToyDrat` succeeds with no `sorry` warnings; no Lean source contains `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern`, or `unsafe`.
- Axioms (`Lean.collectAxioms`, recorded in `audit/axioms.json`) over all 442 non-internal declarations of the library: 165 use no axioms; 176 use [propext]; 91 use [Quot.sound, propext]; 10 use [Classical.choice, Quot.sound, propext]. Every set is a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Statement and definition-closure hashes (`audit/statements.json`, 73 names): SHA-256 of the Lean `repr` of each declaration's type, and SHA-256 of its definition closure (the sorted, newline-joined list, over every package-local constant reachable from the statement, of the constant's name, the `repr` of its type, and, for non-theorems, the `repr` of its value). `support/revalidate.py` recomputes both.

| Declaration | Used by | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `rup_implies_entails` | rup-implies-entails: result | Quot.sound, propext | `fba13b406ec17ea26610936faf4f549593ddab6f2719d44ec9caa7592f616134` | `82f6ba723cd2295945411f7ce6b851484b5e0a4c6e59fc06d965139c3b9b2a20` (35) |
| `rup_addition_preserves_equivalence` | rup-implies-entails: secondary theorem; rat-addition-not-equivalence: positive control | Quot.sound, propext | `05efa458e113cd0772ae8d1fb64323d3250d8b2a4fd6e81c773625835cc5e4a6` | `b0054076c02a8c33369c179df30106073c129470c2f14e2c0c64c28103af04c3` (35) |
| `equivalent_cons_iff_entails` | rup-implies-entails: secondary theorem | Quot.sound, propext | `313aa301fb14d082bbd54c10b922ef7a0a864926dc4ab820ab8e92abc8c1a7ad` | `fe429d3fb2093528e495ec673a68b22dfb96530692dc05c286d8fdb352a99491` (13) |
| `rup_implies_entails_tight_rup` | rup-implies-entails: counterexample for `h` | propext | `09927892af0bf983426dbab8815c0cdce8665cdc34e0c2b6a295406adbedae44` | `700895bb7b3e46724d596282d820c4874fae44c1a132bb1a052db67840f3253d` (36) |
| `rup_implies_entails_nonvacuous` | rup-implies-entails: non-vacuity; rup-implies-entails: non-vacuity of `rup_addition_preserves_equivalence`; entails-not-implies-rup: positive control | propext | `510bcdb6a0c2ba557188843f25c441a536546915b4f803973eefb0de48f811be` | `730b68ad075e9938c1ef8373912d408ce840f19b2d3a9ab8cb6062cfc957f272` (31) |
| `entails_not_implies_rup` | entails-not-implies-rup: result; entails-not-implies-rup: non-vacuity | Quot.sound, propext | `68a4cb7e5661677d43cd5cba1041e69205a8150cd23ee3cbd419374fc49a724b` | `10ec3a3e54ecf842b10b6384132c432567374c907788a35fd80851cb85522168` (38) |
| `entails_not_implies_rup_satisfiable_nonempty` | entails-not-implies-rup: secondary theorem | Quot.sound, propext | `57c1bc280b77dd07454cc6f6e9213536e5b173c768822227b0fae29fc9d282b5` | `e4da63c533641a83f7fb182549ccaa20bf8bead3b60405f0e069f43b60d85a6f` (39) |
| `ratOn_witness_satisfies` | rat-witness: result | Quot.sound, propext | `3f945e5c64c834a556ecf82b582f5a0b8bc87a5becd9b986ab40ae933c4e1fc9` | `09ee4945554b1f9361f5b51a97b0bfa94066ae72ea147985546178ab8fb13e96` (38) |
| `ratOn_witness_tight_mem` | rat-witness: counterexample for `hp` | propext | `eb36e9a404b88635778a3c3bb02d93c8010c71958640c6d8e72c599a08b93d58` | `91d1a8820adae72b74c431404a472817055a9c9cc8769c1856eae485744d0691` (39) |
| `ratOn_witness_tight_rat` | rat-witness: counterexample for `hrat` | propext | `5977985a099986cc1dc2a9b17a27af56bfdc29aadf893a06ceeb962a2ce51774` | `11b79051a2ffe5dcd04de544d11a8b3c8253036d926aca380401b81ddd86c402` (40) |
| `ratOn_witness_tight_model` | rat-witness: counterexample for `ha` | propext | `3cc8d74f24c1e64e49b09d9b7ce887d902732f3e321c9f3586720a7ed81fa947` | `91d1a8820adae72b74c431404a472817055a9c9cc8769c1856eae485744d0691` (39) |
| `ratOn_witness_nonvacuous` | rat-witness: non-vacuity | Quot.sound, propext | `6b70a203b8f3e06a0ab4d6472ebfff5f9c423506fb8b9fb11bb4b0569409b8fc` | `916b8e491349cc11e80c6b45d4b33beee9a2360c9efba135d1632428a0bbebbc` (38) |
| `rat_addition_preserves_satisfiability` | rat-addition-preserves-satisfiability: result | Quot.sound, propext | `27f76285a760c783ca9acb02325c47e5a6d07b7e86a4567de4a98bbcea7bbfe3` | `d70c3ef318ef4af45969b86f9b3938bd0116dc5e8b7b83ecce9154bd4d5884f5` (39) |
| `ratOn_preserves_satisfiability` | rat-addition-preserves-satisfiability: secondary theorem | Quot.sound, propext | `40edb2385213e9efb16c1ebfa8c79012285c46fe7d7fa07b1284bf4c71baaecb` | `6457dc1cd95259a4216b359d65f85dec8c528e15be2939b3e853cfeda68b140e` (37) |
| `rat_addition_equisatisfiable` | rat-addition-preserves-satisfiability: secondary theorem | Quot.sound, propext | `aa29d681584d23649e28cedc148b959c9b22648f30f7cc70c869379b15bcf316` | `d252f50620ccfc90fc38e6bb382ef949a8ee96d4e594f1080c09f7eb2f304f54` (40) |
| `rat_sat_tight_rat` | rat-addition-preserves-satisfiability: counterexample for `hrat` | Quot.sound, propext | `b856a032b9dffec5e55b596ce3904ed1661e6d702813104eb195779f0fc47c96` | `b7e98ed9e857d5e79768e390bad4d6a1ddfbdb502b37260ae897bfd8059a02b9` (41) |
| `rat_sat_tight_sat` | rat-addition-preserves-satisfiability: counterexample for `hF` | Quot.sound, propext | `9de4f0d99407ba20b2d3250c2c9774bd92381ab9710d0815a26aaa04deb56975` | `b7e98ed9e857d5e79768e390bad4d6a1ddfbdb502b37260ae897bfd8059a02b9` (41) |
| `rat_sat_nonvacuous` | rat-addition-preserves-satisfiability: non-vacuity; rat-addition-preserves-satisfiability: non-vacuity of `rat_addition_equisatisfiable` | Quot.sound, propext | `11a3cc2f6d5c8f1a4b36daba132e26bfe3170ee2ae87c6c135ca28d20a897983` | `b7e98ed9e857d5e79768e390bad4d6a1ddfbdb502b37260ae897bfd8059a02b9` (41) |
| `rat_addition_not_equivalence` | rat-addition-not-equivalence: result; rat-addition-not-equivalence: non-vacuity | propext | `8b3dc2b7a3ebe45caeafea0d66e6ae7dafd2a412d4dc11f281d386b6a204be85` | `665b1bc1b02de91c6cccb52b3c2cd37746573f7b656f3b3677dac0e519b920de` (41) |
| `rat_addition_loses_projected_model` | rat-addition-not-equivalence: secondary theorem | Quot.sound, propext | `0e6415258b0fda130a6f248775c48793912e2881d3ff89da5ccba4895c402fbb` | `6b7a66ce17ce062882bbd5b6aaa631f74303b24ca859f147509274626fed0260` (40) |
| `rup_implies_rat_of_ne_nil` | rup-implies-rat: result | Quot.sound, propext | `38fea8b1d2cc58a88522c0e6645297414fac844c738d83dd6cabf010a8cfca6f` | `dbf3e61e74e2db1a095a04b771493870fe927a43dc8252538455c57accf4e32a` (33) |
| `rup_implies_ratOn` | rup-implies-rat: secondary theorem | Quot.sound, propext | `504ddbcafabce5e7f78897c4d5a4ea358d29ec8606ec05329580257c36d68d4b` | `9c2a0563a3f01328574fd0c346b198803d1abd4cd969074fd6813423a115f2eb` (31) |
| `rup_nil_not_rat` | rup-implies-rat: counterexample for `hne` | propext | `cfa25a05043f35c0159302e3b630f564be9b3ea5ee6404163238c8d404187fc3` | `4fad7f7037629c606be4ed60d2b3bdf80a07236e39c6910b142df795320d8634` (35) |
| `rup_rat_tight_rup` | rup-implies-rat: counterexample for `h`; rup-implies-rat: counterexample for `h` of `rup_implies_ratOn` | Quot.sound, propext | `6af08c20e1d2fffdfe15dcba6f0180a24ffc2ba6c59e6f2fa3b0c32ec3f59ca1` | `4fad7f7037629c606be4ed60d2b3bdf80a07236e39c6910b142df795320d8634` (35) |
| `rup_rat_nonvacuous` | rup-implies-rat: non-vacuity; rup-implies-rat: non-vacuity of `rup_implies_ratOn` | propext | `9ca97869f72d91d886753f7fa7396e219422dc9e4e639cfc383d796da51ae079` | `730b68ad075e9938c1ef8373912d408ce840f19b2d3a9ab8cb6062cfc957f272` (31) |
| `rat_check_depends_on_pivot_order` | rat-check-depends-on-pivot-order: result; rat-check-depends-on-pivot-order: non-vacuity | Quot.sound, propext | `1e399d60c1aab0a572b3f6f60201097fac4024ae25bb75ec33c2f21e60c6060a` | `c3db9c158e8489658f747bcadd41895111ddad50184cefda1226806198f27b0c` (46) |
| `checkGen_sound_unsat_of_addCheck_preserves_sat` | refutation-checker-sound-generic: result | Quot.sound, propext | `83bca8d0c4214003c8c090ab5e3dcdbb4878f898b11e8576fbe9468dd2f3bd82` | `729fd6b7e8288819aefa6acbf0362d07b533a95d720c4fb3a3a73246b5e0552f` (31) |
| `checkGen_unchecked_additions_unsound` | refutation-checker-sound-generic: counterexample for `hpres` | Quot.sound, propext | `b9f23be170261ef467af866e8ac169826264b22cc47ed701f9ea9225df541de9` | `f246a2782a08345f4df37295dd6f29b32217a8038adcbec9e1a4a2e93948395e` (32) |
| `checker_acceptance_tight` | refutation-checker-sound-generic: counterexample for `h`; drat-checker-sound-unsat: counterexample for `h`; drat-checker-sound-unsat: counterexample for `h` of `checkOperational_sound_unsat` | Quot.sound, propext | `ad4652bb0ee281481da49feef0566101231ed96eeb2c1ab1d8a6dca116b110e7` | `bcba409643a06b0c3d4d9a335274bc378749623e029ee4269221055c1758e573` (66) |
| `checkGen_sound_nonvacuous` | refutation-checker-sound-generic: non-vacuity | Quot.sound, propext | `0d668cea8d2ebfcb73975a8fedeed0d27d64347bab08441870a5ce1e8dbf9954` | `0080cb24ecaec6eb2c183e3879519dc45387b7deeac3c51c14c72b2dbe157cf8` (63) |
| `checkDRAT_sound_unsat` | drat-checker-sound-unsat: result | Quot.sound, propext | `31a8a8ced631ea5801fc434b17433d054e94e263a425cec2c4c91b593b22fb05` | `33a8ae45853f7f2a24b0531f5d1c82eb8ac0c097ba31e3d90966b2987ce27d2f` (60) |
| `checkOperational_sound_unsat` | drat-checker-sound-unsat: secondary theorem | Quot.sound, propext | `e3045e0f800fcecaa6515aff1f69854de6a341a925bc2c9540517d192dd3d2af` | `7a898b80fb472532baf137c3b34c741e8fc59416e518d7ddc779a5a4deb66139` (62) |
| `checkDRAT_sound_nonvacuous` | drat-checker-sound-unsat: non-vacuity; drat-checker-sound-unsat: non-vacuity of `checkOperational_sound_unsat` | propext | `d35042b4001bfd3354004738b125ce0d986cf76185552547eaefc4dab8cdbf3f` | `b017f8d53109dd39d2d2a33f8b5b67b1f81a9db98d05667038f719c558bbd987` (62) |
| `addOK_preserves_satisfiability` | drat-steps-preserve-satisfiability-forward: result; rat-after-deletion-not-rat-wrt-original: positive control | Quot.sound, propext | `13431d2abfbdb5f3a9d53585987093d1b80198dce1f435977eb6a89dc6beabd9` | `36936218cb648c475bf8a8ea5bf3ffc6104f7b6adb064ac395879ee30f1ff590` (48) |
| `applyDel_preserves_satisfiability` | drat-steps-preserve-satisfiability-forward: secondary theorem | Quot.sound, propext | `b9a84155e6e5d6f9431300100682f3a13f8934acf8b0656c313f49680f44986e` | `070714fece661b7ee05d4ff93a71f9b5a8eadc47d9bd560360e1b32d08ee5114` (23) |
| `addOK_tight_check` | drat-steps-preserve-satisfiability-forward: counterexample for `h` | Quot.sound, propext | `19be4a7d13b0bff5fb6c26f31c2b11e84506a088b4886252ef54b298f1e3e31c` | `ac466864b197a5a337553406f7a827a4df7f18969fe9634be254204656c703f3` (50) |
| `addOK_tight_sat` | drat-steps-preserve-satisfiability-forward: counterexample for `hF` | Quot.sound, propext | `75171276b21eb968e3bdcfa92a88907b8131d39cc4cf813ccfb8d474a04066fa` | `ac466864b197a5a337553406f7a827a4df7f18969fe9634be254204656c703f3` (50) |
| `addOK_nonvacuous` | drat-steps-preserve-satisfiability-forward: non-vacuity | propext | `c9523b9d2eb348215d0fd5ac80ce38fe76c58040073f043f4006edf0c662f64b` | `ac466864b197a5a337553406f7a827a4df7f18969fe9634be254204656c703f3` (50) |
| `naiveSatCheck_unsound_with_deletions` | naive-sat-check-unsound-with-deletions: result; naive-sat-check-unsound-with-deletions: non-vacuity | Quot.sound, propext | `217905e39ee400bd3a8581fa88271c09e5128699b2e33a8c16adf9d4e3d60fea` | `72d34b7c99c99d0acc838861db86252f209fa1e1fe282ac6f37894fdc06bafb2` (65) |
| `deletion_can_turn_unsat_into_sat` | naive-sat-check-unsound-with-deletions: secondary theorem | Quot.sound, propext | `9a2ae246a387c0e74528d93c1520755b2340ff6c8b7b33d79f2d94f908348273` | `7f43988494c3a474d67f6cf3323847f0e73d77e06b795138bc4c3161f66879b9` (23) |
| `naiveSatCheck_sound_of_noDeletions` | naive-sat-check-unsound-with-deletions: positive control; naive-sat-check-sound-without-deletions: result | Quot.sound, propext | `ff53ab88ebd0d6624b80013b414fc75ee77d77f6b284236f9fbadf402ccc7da3` | `a20bd784d85bccf62c44f110df45fa51d0ad4f720481fdffb8edd966195a5d08` (62) |
| `satCheckRupDel_sound` | naive-sat-check-unsound-with-deletions: positive control; rup-checked-deletions-sat-sound: result | Quot.sound, propext | `dc08b3c44a3a661eb597ed2a6523dc9876e9da7d3c6bb6139996685b0fa3a7c2` | `dbe8df0fc8b5cc4e98f7528697883cdf84df96e89b5cc5ea5f99b29a8b2acb94` (58) |
| `replayRatDel_sat_backward` | naive-sat-check-unsound-with-deletions: positive control; rat-checked-deletions-sat-backward: result | Quot.sound, propext | `ed377116804574247fb220b16524357ce4be66d1cffe42411c481b4bbf1944b8` | `8a4b83872c9c59b7e091e1481836b41255ef97327935af1181ff35fc81f3cbe0` (57) |
| `replay_model_sound_of_noDeletions` | naive-sat-check-sound-without-deletions: secondary theorem | Quot.sound, propext | `d9264da0064890fd0b68b381d6a12d4a73f655328753f9e9f8e574f181d2d9d2` | `09819febe57ce45f11d8af41b35f9e97892bfcdd407070d7018883aea58a593e` (31) |
| `naiveSatCheck_noDel_tight_noDel` | naive-sat-check-sound-without-deletions: counterexample for `hnd` | Quot.sound, propext | `a911fbd9a592b9f97180e368b9a797afe4482fd3c1a9ae0d5608b5048dc126d8` | `365107eeedb509872fbd9429494867cacb6de7059805279009bce3ff0c2fb28c` (64) |
| `naiveSatCheck_noDel_tight_accept` | naive-sat-check-sound-without-deletions: counterexample for `h` | propext | `2c09ab2db706ce5a615e43130f4122eae58e34dab036582621f56799a16ee333` | `22bbf82ba3ae2a6afe68bb063c6b5a277c53d3197748d34ae96564a7fb065b5c` (63) |
| `naiveSatCheck_noDel_nonvacuous` | naive-sat-check-sound-without-deletions: non-vacuity | propext | `011ab19ee0c8b59bb4ade1e66828029591b415aab9e475c325169d20860cbb94` | `ec248bc1e7b42030b57908223cdd0d246b91d2a9338ef191dcd68291d795aff5` (63) |
| `satCheckRupDel_tight_accept` | rup-checked-deletions-sat-sound: counterexample for `h` | propext | `f78bc8935ea26069b0412a7db6548c863717685f736ffb28cc5e69262c779f0f` | `b04a7b722946e587daa3503d37053d1d8abefaa7b9413490500be02ea634ed86` (59) |
| `satCheckRupDel_nonvacuous` | rup-checked-deletions-sat-sound: non-vacuity | propext | `a0f9640d50e02c4042f2e627c001f030603bfd28efa26e0b4897d2915aff0275` | `00257f4d62cc85d6c7ef3a7bedd25c4e6c1696f2ceb4c99c8186881b755cdb8c` (60) |
| `replayRatDel_tight_replay` | rat-checked-deletions-sat-backward: counterexample for `hrep` | Quot.sound, propext | `8461126982da2a3eb820701103481a29e5733eb79679217dfa26d33204d3c1bc` | `7b5aead64a1b8bfd1e6daf48ec06a3c96bbde741571da11e1328a465f863085a` (59) |
| `replayRatDel_tight_sat` | rat-checked-deletions-sat-backward: counterexample for `hG` | Quot.sound, propext | `745a9639050191cd5f4448e4599a4f59ce85241bd5a6adccc7483658ae0ef11b` | `7b5aead64a1b8bfd1e6daf48ec06a3c96bbde741571da11e1328a465f863085a` (59) |
| `replayRatDel_nonvacuous` | rat-checked-deletions-sat-backward: non-vacuity | Quot.sound, propext | `05580575d01a32b213bd684b05d69048981ba2bf250b3e64368152223560d271` | `7b5aead64a1b8bfd1e6daf48ec06a3c96bbde741571da11e1328a465f863085a` (59) |
| `rat_after_deletion_not_rat_wrt_original` | rat-after-deletion-not-rat-wrt-original: result; rat-after-deletion-not-rat-wrt-original: non-vacuity | Quot.sound, propext | `9d1757d6f517f2a3c83963efaadf39087d47e4fd85fd123a6fca44f8ab0962a2` | `6c674bb4a3bd4a6681bd345454e2d0306ab08f6bf8b892cc79abbf4881493719` (65) |
| `operational_accepts_specified_rejects` | operational-accepts-specified-rejects: result; operational-accepts-specified-rejects: non-vacuity | propext | `17a62353faf72afa97fdddb6f12bd2e96700cb74ec7bb5b31e91393a2988fd67` | `615692fcdd980fcb7dd56e9591b286a43a22dbdcbcc4f2a73b35bebb42df0640` (61) |
| `specified_accepts_operational_rejects` | specified-accepts-operational-rejects: result; specified-accepts-operational-rejects: non-vacuity | Quot.sound, propext | `54fa92db62f37e978549193db134b1bf8732b3fd2b6dcac9c741a471d072ece0` | `f8bca92bfd2fb6d7d056b105edd71cd5851a96de47caea81ae4b88b0e3cfc060` (63) |
| `checkDRUP_specified_implies_operational` | specified-accepts-operational-rejects: positive control; drup-honor-all-strictest: secondary theorem | Quot.sound, propext | `87fec4ed6b02643962cbb80217578ccb509cdbfb6b9b1e836fcde52c881bba35` | `12fe6d5eb51192b79325771d19ed05ae457858e8174614f5b12d5e1c6174e56c` (52) |
| `checkDRUP_honorAll_implies_any_policy` | drup-honor-all-strictest: result | Quot.sound, propext | `cb148e9651d02d859edca71bcff516f8cfc053d153e1861258ed36e986d80a87` | `9d5e879be6eecd1821cfeff009ef10e1f3019636d7f236ec853a1d249e3be6e3` (52) |
| `checkDRUP_policy_tight_sub` | drup-honor-all-strictest: counterexample for `hFG` | propext | `cef3db9bdd11f19e869f50d486adc38b132d33231001815f9f44d3315a848d11` | `b058dd6bf4f11b654aa86930c9b5961b1bb427ec4220086065b4bc6a3edf7017` (55) |
| `checkDRUP_policy_tight_accept` | drup-honor-all-strictest: counterexample for `h`; drup-honor-all-strictest: counterexample for `h` of `checkDRUP_specified_implies_operational` | propext | `2dd3f205084f0643de1b2bc35c7b751ec399943f8bd3b4537005ffec4db68014` | `b6d512ceaf1f6d99162e169cfe064ee3770eb1ad81eb1ddd3596afc38d49993d` (54) |
| `checkDRUP_policy_nonvacuous` | drup-honor-all-strictest: non-vacuity; drup-honor-all-strictest: non-vacuity of `checkDRUP_specified_implies_operational` | propext | `cf7a1364851a1ece2ea4558242f2b6cc55ae03c4bd424b8b62f81f7f6473396a` | `7d1e989b127102aa0e253660971913af5318fdfb5a61c56fece076b36072362d` (56) |
| `lrat_hint_replay_implies_rup` | lrat-hint-replay-implies-rup: result; sloppy-hint-replay-unsound: positive control | Classical.choice, Quot.sound, propext | `bef263f0150bddf8b6a5dade6a4008673d80ec8b864ab65ce6435e7caa1b7dc2` | `fc4e8fc2054f866b8e2596e6b4bb11612940c1846db715597b4f5c72958dc09c` (36) |
| `lrat_hint_replay_implies_entails` | lrat-hint-replay-implies-rup: secondary theorem | Classical.choice, Quot.sound, propext | `ce033163446bc9889399f0b9b3f536f4cd79317075c2dbf057fdaa35ccdcdb22` | `9ba5346e71780b7f15d24c6d34edc7d0a4018c7f7bbcc017cc9f11deb849a381` (31) |
| `lrat_tight_accept` | lrat-hint-replay-implies-rup: counterexample for `h`; lrat-hint-replay-implies-rup: counterexample for `h` of `lrat_hint_replay_implies_entails` | propext | `4770476861f68ecf62170d1305b31b557ada61947a2c93c0342af03b6ef01a16` | `7fe79992e3ba757ebc5f945699eaaaa1125a416101cd5468abb6f759881f38bb` (43) |
| `lratRupCheck_chain3` | lrat-hint-replay-implies-rup: non-vacuity; lrat-hint-replay-implies-rup: non-vacuity of `lrat_hint_replay_implies_entails` | propext | `28235324196838ba437933603fb23b93abefa47d1493b1f00147a056d439d785` | `510c24663eb537c7fb6f2bc73d5655f31e62bb605771df0298fd5fd4ba79992d` (28) |
| `lrat_hint_order_matters` | lrat-hint-order-matters: result; lrat-hint-order-matters: non-vacuity | propext | `e88294013d4dfc2bdd238e353ec0cc73df1d3c39c3bb43d8958b1559ce3f24b0` | `f69859488c131b9f59699100d6826216c32aec4331137e54aa15ed91a32a7ef6` (39) |
| `sloppy_hint_replay_unsound` | sloppy-hint-replay-unsound: result; sloppy-hint-replay-unsound: non-vacuity | propext | `4dc69370bf541d3c70551e79c0332957364771a572986c36c3fb2b24f5e3d63d` | `cd74b51327df32ecf2d6de9a140df0557ae36c3629a9baf4dafed17986a331a0` (36) |
| `lratRupCheck_complete_of_wellformed` | lrat-hint-replay-complete-wellformed: result | Classical.choice, Quot.sound, propext | `2585f8673cc84c91719a8c4667e2aa4920ff7fa335681ba4dcb70f8bb22adc3d` | `e8f855f10572a89f86f88a259e21ffbe4803c27207679c2882829bafb7a9f973` (38) |
| `lratRupCheckDedup_exists_iff_rup` | lrat-hint-replay-complete-wellformed: secondary theorem | Classical.choice, Quot.sound, propext | `698b41af35caa55dfe74291ed09db070880e92e77346cff071f1d8ee64a72737` | `9b58cb52114abd8bdee29fdaf7e5a6559ac7e01abea4be6f59f401a0c2149568` (40) |
| `lratRupCheck_rejects_blocked_resolvent` | lrat-hint-replay-complete-wellformed: secondary theorem | propext | `b042d265a01be27577ce2b223aca802c07cec42d729d1105dafa4eae4c25a3cf` | `1285086468d20e49e70d8ecfaae72fec86b7e54d84a4613129d1ee603f91fab5` (39) |
| `lratRupCheck_incomplete_tautology` | lrat-hint-replay-complete-wellformed: counterexample for `hC` | propext | `3a2ea75f0070dabe80d4c3075827c19b846caa7becce9b1b956bf1ba4ad0a11a` | `0d4c610ba3f30d41b4697bc6ac37a1adfeda75f109726f7734e87dcd32a4908e` (40) |
| `lratRupCheck_incomplete_dup_lits` | lrat-hint-replay-complete-wellformed: counterexample for `hF` | propext | `e30d0ce878a3983b2ef30fc7fbe9ed5f26157086b52d2fdcbf7b4ac129aa9c54` | `0d4c610ba3f30d41b4697bc6ac37a1adfeda75f109726f7734e87dcd32a4908e` (40) |
| `lrat_complete_tight_rup` | lrat-hint-replay-complete-wellformed: counterexample for `h` | Classical.choice, Quot.sound, propext | `acbb72c9967b47899dcc7910469b3d07b26b6cc3b4d9dc14c7e7473778227de3` | `a5a7909cb52c9f6b9c8db0d422645dcf482b6c0aad22473f8212f5c3db69c617` (39) |
| `lrat_complete_nonvacuous` | lrat-hint-replay-complete-wellformed: non-vacuity | propext | `1ef06f17b748f23783ed5a90ea54f2c2814d0932555cc6f4bfe0d2f8cbbe3ab1` | `dfc9438c6e6dc971f0837230fb5e8a8f892ec36e1d7e9132925307cd27a453ea` (34) |

Further referenced declarations, which carry no recorded hash and are checked for existence and axioms: first the 12 counterexample and non-vacuity witnesses inside secondary-theorem ledgers, then, alphabetically, the 20 further lemmas that the prose of `results.json` (non-claims, tier notes, non-vacuity witness descriptions, and plain readings of secondary theorems) cites by name without naming them in a structured field. The positive and negative examples listed under **Definitions** ("Examples (proved)") are not repeated here; like every other declaration of the library, their axioms are recorded in `audit/axioms.json` and rechecked by `support/revalidate.py`.

| Declaration | Used by | Axioms |
| :--- | :--- | :--- |
| `rup_equivalence_tight_rup` | rup-implies-entails: counterexample for `h` of `rup_addition_preserves_equivalence` | Quot.sound, propext |
| `ratOn_sat_tight_mem` | rat-addition-preserves-satisfiability: counterexample for `hp` of `ratOn_preserves_satisfiability` | Quot.sound, propext |
| `ratOn_sat_tight_rat` | rat-addition-preserves-satisfiability: counterexample for `hrat` of `ratOn_preserves_satisfiability` | Quot.sound, propext |
| `ratOn_sat_tight_sat` | rat-addition-preserves-satisfiability: counterexample for `hF` of `ratOn_preserves_satisfiability` | Quot.sound, propext |
| `ratOn_sat_nonvacuous` | rat-addition-preserves-satisfiability: non-vacuity of `ratOn_preserves_satisfiability` | Quot.sound, propext |
| `rat_equisat_tight_rat` | rat-addition-preserves-satisfiability: counterexample for `hrat` of `rat_addition_equisatisfiable` | Quot.sound, propext |
| `applyDel_tight_sat` | drat-steps-preserve-satisfiability-forward: counterexample for `h` of `applyDel_preserves_satisfiability` | Quot.sound, propext |
| `applyDel_nonvacuous` | drat-steps-preserve-satisfiability-forward: non-vacuity of `applyDel_preserves_satisfiability` | none |
| `replay_model_sound_tight_noDel` | naive-sat-check-sound-without-deletions: counterexample for `hnd` of `replay_model_sound_of_noDeletions` | Quot.sound, propext |
| `replay_model_sound_tight_replay` | naive-sat-check-sound-without-deletions: counterexample for `hrep` of `replay_model_sound_of_noDeletions` | propext |
| `replay_model_sound_tight_sat` | naive-sat-check-sound-without-deletions: counterexample for `ha` of `replay_model_sound_of_noDeletions` | propext |
| `replay_model_sound_nonvacuous` | naive-sat-check-sound-without-deletions: non-vacuity of `replay_model_sound_of_noDeletions` | propext |
| `checkGen_empty_certificate` | refutation-checker-sound-generic: non-claim | none |
| `checkSpecified_fullSquare` | entails-not-implies-rup: non-claim | propext |
| `drat_certificate_not_monotone_in_formula` | drat-checker-sound-unsat: non-claim; drat-steps-preserve-satisfiability-forward: non-claim; drup-honor-all-strictest: non-claim | Quot.sound, propext |
| `ignoreUnitDeletions_example_dup` | drat-checker-sound-unsat: non-claim; operational-accepts-specified-rejects: non-claim; specified-accepts-operational-rejects: non-claim | none |
| `lratRupCheck_example_satisfied_hint` | lrat-hint-replay-implies-rup: non-claim | propext |
| `lratRupCheck_example_trailing_hints` | lrat-hint-replay-implies-rup: non-claim | propext |
| `lratRupCheck_side_conditions_not_necessary` | lrat-hint-replay-complete-wellformed: non-claim; lrat-hint-replay-complete-wellformed: tier note | propext |
| `lratRupCheckDedup_eq_of_wellformed` | lrat-hint-replay-complete-wellformed: plain reading of `lratRupCheckDedup_exists_iff_rup` | Quot.sound, propext |
| `one_copy_deletion_breaks_drup_monotonicity` | drup-honor-all-strictest: non-claim | propext |
| `permuted_deletion_is_ignored` | operational-accepts-specified-rejects: non-claim; drup-honor-all-strictest: non-claim | propext |
| `RAT_example_pos` | rup-implies-rat: non-claim | Quot.sound, propext |
| `RAT_example_pos_not_entailed` | rat-addition-preserves-satisfiability: non-vacuity witness description; rup-implies-rat: non-claim | none |
| `rat_not_monotone_in_formula` | rat-witness: non-claim; rat-addition-preserves-satisfiability: non-claim; drat-steps-preserve-satisfiability-forward: non-claim | propext |
| `rat_not_rup_addition_preserves_equivalence` | rup-implies-entails: non-claim; rup-implies-rat: non-claim | Quot.sound, propext |
| `ratCheck_example_neg` | rat-addition-preserves-satisfiability: non-claim | propext |
| `ratOn_without_mem_unsound` | rat-addition-preserves-satisfiability: non-claim; rup-implies-rat: non-claim | Quot.sound, propext |
| `replayRatDel_final_model_not_original` | rat-witness: non-claim; naive-sat-check-unsound-with-deletions: non-claim; rup-checked-deletions-sat-sound: non-claim; rat-checked-deletions-sat-backward: non-claim; rat-checked-deletions-sat-backward: non-vacuity witness description | Quot.sound, propext |
| `rupCheck_of_mem` | rup-checked-deletions-sat-sound: non-claim | Quot.sound, propext |
| `rupCheck_of_nil_mem` | refutation-checker-sound-generic: non-claim | Quot.sound, propext |
| `rupCheck_sound` | rup-implies-entails: non-claim | propext |

### Primary sources (prior art)

Bibliographic records were verified against Crossref or arXiv on the observation date. Each entry states what was read of the source; no statement is attributed to a source whose full text was not consulted. Keys are used in the Findings.

- **[AR20]** J. Altmanninger, A. Rebola Pardo, "Frying the Egg, Roasting the Chicken: Unit Deletions in DRAT Proofs", CPP 2020, pp. 61-70, doi:10.1145/3372885.3373821. The abstract (read) states that state-of-the-art checkers ignore deletions of unit clauses, differing from the standard, that many SAT solvers introduce spurious unit deletions, and that a large fraction of the proofs generated during the preceding SAT competition do not respect the DRAT standard; full text not consulted.
- **[CHHKS17]** L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann, P. Schneider-Kamp, "Efficient Certified RAT Verification", CADE-26 (2017), LNCS 10395, pp. 220-236, doi:10.1007/978-3-319-63046-5_14; preprint arXiv:1612.02353 (read). Section 1 (p. 2): clauses are sorted so that duplicate or complementary literals can be detected, and "Hints are also sorted in such a way that they become unit from left to right". Section 2 (pp. 2-3): AT is unit propagation on F and the negation of C reaching a conflict; C is RAT if there is a literal l in C such that for all D in F containing the complement of l, C or (D minus that complement) is AT; the first literal is the DRAT pivot; the empty clause must be AT; deletion steps need not be checked because they trivially preserve satisfiability. Section 3 introduces LRAT hints. Section 4 (p. 9) states the Coq notion ICNF_reduces (every model of one formula yields a model of the other).
- **[CMS17]** L. Cruz-Filipe, J. Marques-Silva, P. Schneider-Kamp, "Efficient Certified Resolution Proof Checking", TACAS 2017, LNCS 10205, pp. 118-135, doi:10.1007/978-3-662-54577-5_7 (bibliographic record verified via Crossref; full text not consulted, so no specific statement of the paper is attributed here).
- **[drat-trim]** drat-trim source code, repository marijnheule/drat-trim on GitHub, file drat-trim.c at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985 (read): the default mode is BACKWARD_UNSAT (line 1388; -f selects FORWARD_UNSAT and -S selects FORWARD_SAT, lines 1419-1420); the literals of each parsed clause are sorted and duplicate literals removed (lines 1157-1165); in BACKWARD_UNSAT mode deletions of clauses of size at most one after that step are skipped with the warning "backward mode ignores deletion of (pseudo) unit clause" (lines 1168-1173); a deletion removes one matching stored copy (lines 1176-1188); outside FORWARD_SAT mode, deletions of unit clauses (lines 790-799) and of clauses that are the reason of a top-level assignment (lines 806-815) are skipped; in BACKWARD_UNSAT mode the RAT check skips candidate clauses not marked active (lines 565-567); in FORWARD_SAT mode each deletion is passed to redundancyCheck, the routine that also checks additions (lines 825-830), which returns success early for clauses not marked active outside FORWARD_UNSAT mode (lines 621-622).
- **[GN03]** E. Goldberg, Y. Novikov, "Verification of Proofs of Unsatisfiability for CNF Formulas", Design, Automation and Test in Europe (DATE 2003), pp. 886-891, doi:10.1109/DATE.2003.1253718 (bibliographic record verified via Crossref; full text not consulted, so no specific statement of the paper is attributed here).
- **[Heu16]** M. J. H. Heule, "The DRAT format and DRAT-trim checker", arXiv:1610.06229 (2016), read. Pages 2-3: clauses may contain neither complementary nor duplicate literals; formulas are multisets of clauses; lines after the empty clause are ignored; the first literal is the RAT pivot and the empty clause must be AT; "A clause deletion step removes a single clause (if the clause is present)", so k deletion steps are needed to remove k copies; DRAT-trim ignores deletion steps of unit clauses, and "ignoring deletion steps of unit clauses can turn a valid DRAT proof into an invalid one — and the other way around."
- **[HHW13]** M. J. H. Heule, W. A. Hunt Jr., N. Wetzler, "Trimming while Checking Clausal Proofs", FMCAD 2013, pp. 181-188, doi:10.1109/FMCAD.2013.6679408 (bibliographic record verified via Crossref; full text not consulted, so no specific statement of the paper is attributed here).
- **[HJB10]** M. Heule, M. Järvisalo, A. Biere, "Clause Elimination Procedures for CNF Formulas", LPAR-17 (2010), LNCS 6397, pp. 357-371, doi:10.1007/978-3-642-16242-8_26 (author copy read): the abstract presents the asymmetric variants of clause elimination as new; Section 4.2 defines a clause C to be an asymmetric tautology w.r.t. F if asymmetric literal addition makes it a tautology, and Lemma 7 states that this holds iff unit propagation on (F without C) together with the negations of the literals of C derives a conflict.
- **[JHB12]** M. Järvisalo, M. J. H. Heule, A. Biere, "Inprocessing Rules", IJCAR 2012, LNCS 7364, pp. 355-370, doi:10.1007/978-3-642-31365-3_28 (introduces resolution asymmetric tautologies, RAT; asymmetric tautologies predate it, see Heule, Järvisalo, Biere 2010; bibliographic record verified via Crossref; full text not consulted).
- **[Lam17]** P. Lammich, "Efficient Verified (UN)SAT Certificate Checking", CADE-26 (2017), LNCS 10395, pp. 237-254, doi:10.1007/978-3-319-63046-5_15; journal version J. Automated Reasoning 64 (2020), pp. 513-532, doi:10.1007/s10817-019-09525-z (verified checking of satisfiability and unsatisfiability certificates in Isabelle/HOL; bibliographic records verified via Crossref; full text not consulted, so no specific statement of the paper is attributed here).
- **[Lean-LRAT]** Lean 4 core at tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), source read at that commit. src/Std/Tactic/BVDecide/LRAT/Checker.lean: Std.Tactic.BVDecide.LRAT.check runs Std.Tactic.BVDecide.LRAT.Internal.compactLratChecker, and check_sound (a successful check implies the CNF is unsatisfiable) applies compactLratChecker_sound (src/Std/Tactic/BVDecide/LRAT/Internal/CompactLRATCheckerSound.lean). That proof is a functional induction over the checker loop using addEmptyCaseSound (from LRATCheckerSound.lean) for the empty-clause step, Formula.limplies_delete (Internal/CNF.lean) for deletions, and the rupAdd_sound and ratAdd_sound fields of the Formula class (Internal/Formula/Class.lean), proved for DefaultFormula in Internal/Formula/RupAddSound.lean (a successful RUP addition yields a logically equivalent formula) and Internal/Formula/RatAddSound.lean (a successful RAT addition with the pivot in the clause yields an equisatisfiable formula). LRATCheckerSound.lean also proves lratCheckerSound, with addRupCaseSound, addRatCaseSound and delCaseSound, for the list-based lratChecker, which check does not call.
- **[Lean-RatAdd]** Lean 4 core v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Std/Tactic/BVDecide/LRAT/Internal/Formula/RatAddSound.lean: ratAdd_sound (lines 578-582) assumes pivot_in_c (the pivot is a literal of the clause) and concludes Equisat; its proof builds the assignment that sets the pivot true (line 508). Source read.
- **[Lean-RupAdd]** Lean 4 core v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Std/Tactic/BVDecide/LRAT/Internal/Formula/RupAddSound.lean: rupAdd_sound (line 764) concludes Liff (logical equivalence) between the formula before and after a successful RUP addition. Source read.
- **[RB19]** A. Rebola-Pardo, A. Biere, "Two Flavors of DRAT", Proceedings of Pragmatics of SAT 2015 and 2018, EPiC Series in Computing 59 (2019), pp. 94-110, doi:10.29007/lt8r. The abstract (verified) states that the proofs accepted by state-of-the-art DRAT checkers differ from those accepted by the original definition and formalizes the operational definition; the full text was not consulted, so no specific theorem of that paper is attributed here.
- **[THM21]** Y. K. Tan, M. J. H. Heule, M. O. Myreen, "cake_lpr: Verified Propagation Redundancy Checking in CakeML", TACAS 2021, pp. 223-241, doi:10.1007/978-3-030-72013-1_12 (bibliographic record verified at the publisher; full text not consulted).
- **[VG12]** A. Van Gelder, "Producing and verifying extremely large propositional refutations", Annals of Mathematics and Artificial Intelligence 65(4), 2012, pp. 329-372, doi:10.1007/s10472-012-9322-x (bibliographic record verified via Crossref; full text not consulted, so no specific statement of the paper is attributed here).
- **[WHH13]** N. Wetzler, M. J. H. Heule, W. A. Hunt Jr., "Mechanical Verification of SAT Refutations with Extended Resolution", Interactive Theorem Proving (ITP 2013), LNCS 7998, pp. 229-244, doi:10.1007/978-3-642-39634-2_18 (bibliographic record verified via Crossref; full text not consulted, so no specific statement of the paper is attributed here).
- **[WHH14]** N. Wetzler, M. J. H. Heule, W. A. Hunt Jr., "DRAT-trim: Efficient Checking and Trimming Using Expressive Clausal Proofs", SAT 2014, LNCS 8561, pp. 422-429, doi:10.1007/978-3-319-09284-3_31 (bibliographic record verified at the publisher; full text not consulted).

### Source code read for the modeling bridges

- drat-trim, repository `marijnheule/drat-trim`, file `drat-trim.c` at commit
  `2e3b2dc0ecf938addbd779d42877b6ed69d9a985` (committed 2024-11-25): default mode `BACKWARD_UNSAT`
  (line 1388) and mode flags `-f`/`-S` (lines 1419-1420); literal sorting and duplicate removal on input
  (lines 1157-1165); backward-mode skipping of (pseudo) unit deletions on input (lines 1168-1173); a
  deletion removes one matching stored copy (lines 1176-1188); skipping of unit-clause deletions
  (lines 790-799) and of reason-clause deletions (lines 806-815) outside `FORWARD_SAT`; `FORWARD_SAT`
  passes deletions to `redundancyCheck` (lines 825-830), which returns success early for clauses not
  marked active outside `FORWARD_UNSAT` (lines 621-622); backward RAT checks skip clauses not marked
  active (lines 565-567).
- Lean 4 core at tag `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), directory
  `src/Std/Tactic/BVDecide/LRAT/`: `Checker.lean` (`check` runs `compactLratChecker`; `check_sound`
  applies `compactLratChecker_sound`, lines 30-48); `Internal/CompactLRATChecker.lean` (a RAT step whose
  pivot is not in the clause is skipped, lines 48-56); `Internal/Formula/RupAddSound.lean` (`rupAdd_sound`,
  line 764, concludes logical equivalence); `Internal/Formula/RatAddSound.lean` (`ratAdd_sound`, lines
  578-582, assumes the pivot is in the clause and concludes equisatisfiability; the pivot-setting
  assignment at line 508); `Internal/Clause.lean` (`DefaultClause` invariants `nodupkey` and `nodup`,
  lines 95-98); `Internal/Formula/Implementation.lean` (`confirmRupHint`, lines 176-195;
  `performRupAdd`, lines 219-225).

### Observation dates

All evidence recorded here (the kernel check, the axiom and hash audit, the source reads at the pinned commits, and the bibliographic verification) was acquired or revalidated on 2026-11-21.

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is
installed; there are no Lake dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and

1. runs `lake build` (the library `ToyDrat`);
2. rejects any Lean source containing `sorry`, `admit`, `native_decide`, or an `axiom` declaration;
3. computes, with Lean's `collectAxioms`, the axioms of every declaration of the library and fails if
   any is outside `propext`, `Classical.choice`, `Quot.sound`;
4. for every Lean name referenced by `results.json` (fields `lean`, `lean_names`,
   `nonvacuity_witness_lean`, `positive_control_lean`, `corollaries_lean`, and hypothesis
   `counterexample`s) and every name recorded in `audit/statements.json`, recomputes the SHA-256 of the
   statement (the Lean `repr` of the declaration's type) and of its definition closure (for every
   package-local constant reachable from the statement: its name, the `repr` of its type, and, for
   non-theorems, the `repr` of its value, sorted and newline-joined; theorem bodies are excluded) and
   compares both, with the closure size, against `audit/statements.json`.

It prints `REVALIDATED` and exits 0 iff all checks pass. A name that is referenced but has no recorded
hash is only checked for existence and reported in the count of unrecorded names (expected: 0).

**Manual axiom listing.** From `lean/`:

```sh
lake build
lake env lean RevalidationAudit.lean
```

This prints `#print axioms` output for each of the 105 declarations referenced by `results.json`: the
85 named in its structured fields (73 with a recorded hash, plus the 12 secondary-theorem witnesses that
carry none) and the 20 further lemmas cited by name only in its prose, i.e. exactly the declarations
listed in the two tables under **Evidence**. Every line must report either no axioms or a subset of
`propext`, `Classical.choice`, `Quot.sound`.

**What revalidation covers.** These commands re-establish the `execution (Lean kernel check)` claims
and the statement and closure hashes recorded under **Evidence**. They do not revalidate the
`derived (modeling bridge)` statements: to recheck those, re-read the cited lines of `drat-trim.c` at
commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985` and of `src/Std/Tactic/BVDecide/LRAT/` at Lean commit
`5045d0056413266e57c625dcd7c365b10e377c52`, or diff those regions against a newer revision before
applying a bridge to it.
