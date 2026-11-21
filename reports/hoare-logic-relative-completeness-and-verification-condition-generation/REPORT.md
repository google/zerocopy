# Hoare logic in Lean 4: soundness, relative completeness assuming `WlpAdmissibleFor`, incompleteness for divisibility-free linear invariants, and verification-condition generation

## Summary

This package is a kernel-checked Lean 4 formalization (core Lean and `Std` only, no Mathlib) of
partial- and total-correctness Hoare logic for a small deterministic While language over unbounded
integer variables, with semantic assertions, a parameter `L` restricting which assertions a
derivation may invent, and a textbook verification-condition generator. It contains eleven results:

1. **Soundness** (`hoare-soundness`): for every admissibility predicate `L`, every triple
   `{P} c {Q}` derivable in `Deriv L` (skip, assignment, sequencing, conditional, while and
   consequence rules, consequence premises being true semantic implications, sequencing midpoints
   and loop invariants satisfying `L`) is valid in partial correctness.
2. **Relative completeness assuming `WlpAdmissibleFor`** (`hoare-relative-completeness-wlp-admissible`):
   *relative to* the assumed command-local hypothesis `WlpAdmissibleFor L c Q`, i.e. that every
   sequencing midpoint `wlp c₂ S` and loop invariant `wlp (while b do c') S` met when computing
   `wlp c Q` backwards (the set `WlpInvented c Q`) satisfies `L`, every valid partial-correctness
   triple `{P} c {Q}` is derivable in `Deriv L`; unconditionally, `{P} c {Q}` is valid iff it is
   derivable with all invented assertions drawn from `WlpInvented c Q`, and with every semantic
   assertion admissible (`L = AnyAssn`) derivable iff valid.
3. **Incompleteness for divisibility-free linear invariants** (`linear-qf-hoare-incomplete`): the
   valid triple `{x = y + y} while 2 ≤ x do x := x - 2 {x ≠ 1}`, whose pre- and postcondition are
   linear, has no derivation in which every sequencing midpoint and loop invariant is definable in
   divisibility-free quantifier-free linear integer arithmetic (`LinDef`), even though consequence
   premises may be arbitrary true implications; changing the precondition, the postcondition, the
   program text (an auxiliary variable) or the assertion language each removes the obstruction.
4. **The `wlp` of that loop is not linear** (`linear-qf-not-wlp-expressive`): the weakest liberal
   precondition of `while 2 ≤ x do x := x - 2` for `x ≠ 1` (on stores with `x = a`, `y = b`, other
   variables `0`, exactly `a ≤ 0 ∨ a` even) is not `LinDef`.
5. **Eventual constancy on affine lines** (`qf-linear-eventually-constant-on-affine-lines`): along
   any affine line of stores `n ↦ σ n`, every divisibility-free quantifier-free linear formula has
   one truth value for all `n ≥ N` (some `N`); hence an assertion that is true and false beyond
   every bound along an affine line, such as "`x` is even", is not `LinDef`.
6. **VC soundness** (`vcgen-soundness`): for an annotated program `a` and postcondition `Q`, if every
   side condition of `vcgen a Q` holds in every store and `P` implies the generated precondition,
   then `{P} erase a {Q}` is valid.
7. **Reachable but non-inductive annotations fail** (`vcgen-reachable-noninductive-annotation-fails`):
   for the valid `{x = 0} while x < 2 do x := x + 2 {x = 2}`, the annotation `x ≤ 2` holds at every
   reachable loop head and its exit condition is valid, yet its preservation side condition fails at
   the unreachable store `x = 1`, so the generated side conditions are not all valid.
8. **VC generation is complete for the `wlp` annotation** (`vcgen-complete-wlp-annotation`):
   `{P} c {Q}` is valid iff, for the annotation `annotWlp c Q` (each loop annotated with its `wlp`),
   all side conditions are valid and `P` implies the generated precondition; those side conditions
   are always valid and the generated precondition is pointwise `wlp c Q`.
9. **VC generation with divisibility-free linear invariants is incomplete**
   (`vcgen-linear-qf-annotations-incomplete`): the triple of result 3 cannot be verified by `vcgen`
   with any annotation that erases to the loop and has only `LinDef` loop invariants.
10. **Total-correctness soundness with bounded integer variants** (`total-soundness-bounded-variant`):
    every triple derivable in the total-correctness system whose while rule requires an integer
    variant that strictly decreases per iteration and is `≥ 0` under the invariant and guard is
    valid in total correctness.
11. **Unbounded variants are unsound** (`unbounded-variant-unsound`): without the lower-bound
    premise, `[true] while true do x := x - 1 [true]` is derivable (variant `x`), yet the loop never
    terminates, so the triple is not valid in total correctness.

Model–system relation: none proved (the soundness and completeness results relate the package's own
proof systems `Deriv L` and `TDeriv` and VC generator `vcgen` to its own semantics `Valid` and `TValid`).
Every result concerns this toy model; these theorems neither establish nor refute the
corresponding claims about real program verifiers, SMT solvers or intermediate verification
languages (the modeling bridge under **Applicability** argues the connection separately). What
each result does **not** show is listed first under **Boundaries** (non-claims, per result),
followed by escape hatches and boundary theorems.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity: this is a toy model.** All results are theorems about the Lean definitions quoted
under **Findings** (namespace `Toy.Hoare`, library `ToyHoare`), not about any production verifier.
The definitions are meant to capture the textbook setting of Hoare (1969), Cook (1978) and Winskel
(1993, chapter 7), and the loop-invariant-annotated verification-condition generators of Igarashi,
London and Luckham (1975) and Nipkow and Klein (`VCG.thy`). Known gaps between the model and real
program verifiers:

- **Language.** A deterministic While language (`skip`, assignment, sequencing, `if`, `while`) over
  stores `Nat → Int`: unbounded mathematical integers, no overflow, no runtime errors, no heap or
  pointers, no procedures or recursion, no nondeterminism, no concurrency. Expressions include
  multiplication of variables (`AExp.mul`), guards include comparisons of products.
- **Assertions are semantic.** `Assn := Store → Prop`. The rule of consequence takes semantic
  implications as premises (an oracle for the assertion logic; in Lean a premise is a proof). The
  parameter `L : Assn → Prop` of `Deriv L` restricts only the assertions a derivation *invents*: the
  midpoint `R` of each sequencing step and the invariant `I` of each while step. Pre- and
  postconditions, assignment preconditions `Q[e/x]`, guarded preconditions `P ∧ b`, `I ∧ ¬b`, and
  the intermediate assertions of consequence steps remain unrestricted. `Deriv L` is therefore not
  a fully syntactic Hoare logic over `L`.
- **Linear assertion language.** `LinDef R` means `R` is defined by a formula of `LAssn`: `true`,
  `t ≤ u`, `t = u`, `¬`, `∧`, `∨` over linear terms (integer constants, variables, `+`, `-`,
  multiplication by an integer constant). No quantifiers, no divisibility or modulo predicates. This
  is strictly weaker than the SMT-LIB logic `QF_LIA`, whose formulas may use `(_ divisible n)`.
- **VC generation.** `vcgen` computes a precondition backwards and a list of side conditions, each
  of which must hold in *every* store (`VCsValid`): side conditions do not carry the guards of
  enclosing branches or facts about variables a loop does not modify, unlike generators that cut
  loops by havocking only modified variables or that use path conditions. Sequential composition
  and assignments propagate preconditions semantically. Annotations are semantic assertions.
- **Total correctness.** `TDeriv requireBound` adds an `Int`-valued variant to the while rule; the
  lower-bound premise `0 ≤ V` (under invariant and guard) is present iff `requireBound = true`.
  `TValid` uses an existential over final states, which expresses guaranteed termination only
  because `Exec` is deterministic. Well-founded orders other than this bounded-below `Int` measure
  are not formalized, and there is no total-correctness completeness result or VC generator.

Basis: derived (modeling bridge). Consider a verifier for while programs over unbounded integers
whose program semantics agrees with `Exec` on the program at hand, whose implication checks are
sound, and each of whose proofs can be read as a `Deriv LinDef` derivation (every loop invariant
and every assertion cut at a `;` is a divisibility-free quantifier-free linear formula) or as a
`vcgen` run whose loop annotations are such formulas. For such a verifier, results 3 and 9 say it
cannot prove `{x = y + y} while 2 ≤ x do x := x - 2 {x ≠ 1}` for the uninstrumented loop, and the
positive controls say which single changes (a parity atom or other non-`LinDef` invariant, an
auxiliary variable, a different specification) remove that obstruction. The reading of a real
verifier's proofs as `Deriv LinDef` derivations or `vcgen` runs is an argument, not a theorem: no
real verifier, solver or intermediate language is formalized, fixed-width integers would change the
semantics, and verifiers with richer annotations (for example `QF_LIA` formulas using
`(_ divisible 2)`, or quantified formulas) do not satisfy the premise.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`),
core library only; no Mathlib, no Lake dependencies (`lean/lakefile.toml` declares one `lean_lib`,
`ToyHoare`, and no `[[require]]`).

**Relation among the subjects in `REPORT.json`.** The Lean toolchain is the checker of every
theorem. The papers, books, the Isabelle/HOL revision and the Rocq `hoare-tut` revision are prior
art for the restated results
(tier T0) and the background for the instances made precise here (tier T1); none of them is a
dependency of the Lean code, and no statement here is claimed to coincide verbatim with a statement
in a source.

## Findings

All statements below are quoted from the Lean sources in `lean/ToyHoare/` (namespace `Toy.Hoare`;
the namespace prefix is omitted). Variables are natural numbers; in prose `x`, `y`, `g` are
variables `0`, `1`, `2`. Every theorem named in this section is fully proved, and its axioms,
statement hash and definition-closure hash are listed under **Evidence**.

Basis (for every theorem statement in this section): execution (Lean kernel check). The build and
axiom audit are reproducible with the commands under **Revalidation**.

### Core definitions

Language and semantics (`ToyHoare/Basic.lean`):

```lean
abbrev Store := Nat → Int
def upd (s : Store) (x : Nat) (v : Int) : Store := fun y => if y = x then v else s y

inductive AExp where
  | lit : Int → AExp | var : Nat → AExp
  | add : AExp → AExp → AExp | sub : AExp → AExp → AExp | mul : AExp → AExp → AExp
-- AExp.eval: lit n ↦ n, var x ↦ s x, add/sub/mul ↦ +, -, * of the evaluated operands (on Int)

inductive BExp where
  | tt | ff | eq : AExp → AExp → BExp | le : AExp → AExp → BExp | lt : AExp → AExp → BExp
  | not : BExp → BExp | and : BExp → BExp → BExp | or : BExp → BExp → BExp
-- BExp.eval : BExp → Store → Bool (decide of =, ≤, < on Int; !, &&, ||)

inductive Com where
  | skip | assign : Nat → AExp → Com | seq : Com → Com → Com
  | cond : BExp → Com → Com → Com | whileDo : BExp → Com → Com

inductive Exec : Com → Store → Store → Prop where   -- big-step semantics (implicit binders elided)
  | skip (s : Store) : Exec .skip s s
  | assign (x : Nat) (e : AExp) (s : Store) : Exec (.assign x e) s (upd s x (e.eval s))
  | seq : Exec c₁ s s₁ → Exec c₂ s₁ s₂ → Exec (.seq c₁ c₂) s s₂
  | condTrue : b.eval s = true → Exec c₁ s s' → Exec (.cond b c₁ c₂) s s'
  | condFalse : b.eval s = false → Exec c₂ s s' → Exec (.cond b c₁ c₂) s s'
  | whileFalse : b.eval s = false → Exec (.whileDo b c) s s
  | whileTrue : b.eval s = true → Exec c s s₁ → Exec (.whileDo b c) s₁ s₂ →
      Exec (.whileDo b c) s s₂

abbrev Assn := Store → Prop
def Valid (P : Assn) (c : Com) (Q : Assn) : Prop := ∀ s s', P s → Exec c s s' → Q s'
def wlp (c : Com) (Q : Assn) : Assn := fun s => ∀ s', Exec c s s' → Q s'
```

`Exec` is deterministic (`Exec.deterministic`); a diverging run has no final state, so `Valid`
is partial correctness.

Derivability with restricted invented assertions (`ToyHoare/Logic.lean`):

```lean
inductive Deriv (L : Assn → Prop) : Assn → Com → Assn → Prop where
  | skip (P : Assn) : Deriv L P .skip P
  | assign (x : Nat) (e : AExp) (Q : Assn) :
      Deriv L (fun s => Q (upd s x (e.eval s))) (.assign x e) Q
  | seq {P R Q : Assn} {c₁ c₂ : Com} :
      L R → Deriv L P c₁ R → Deriv L R c₂ Q → Deriv L P (.seq c₁ c₂) Q
  | cond {P Q : Assn} {b : BExp} {c₁ c₂ : Com} :
      Deriv L (fun s => P s ∧ b.eval s = true) c₁ Q →
      Deriv L (fun s => P s ∧ b.eval s = false) c₂ Q →
      Deriv L P (.cond b c₁ c₂) Q
  | whileDo {I : Assn} {b : BExp} {c : Com} :
      L I → Deriv L (fun s => I s ∧ b.eval s = true) c I →
      Deriv L I (.whileDo b c) (fun s => I s ∧ b.eval s = false)
  | conseq {P P' Q Q' : Assn} {c : Com} :
      (∀ s, P s → P' s) → Deriv L P' c Q' → (∀ s, Q' s → Q s) → Deriv L P c Q

def AnyAssn : Assn → Prop := fun _ => True

def WlpInvented : Com → Assn → Assn → Prop
  | .skip, _, _ => False
  | .assign _ _, _, _ => False
  | .seq c₁ c₂, Q, R => R = wlp c₂ Q ∨ WlpInvented c₁ (wlp c₂ Q) R ∨ WlpInvented c₂ Q R
  | .cond _ c₁ c₂, Q, R => WlpInvented c₁ Q R ∨ WlpInvented c₂ Q R
  | .whileDo b c, Q, R =>
    R = wlp (.whileDo b c) Q ∨ WlpInvented c (wlp (.whileDo b c) Q) R

def WlpAdmissibleFor (L : Assn → Prop) (c : Com) (Q : Assn) : Prop :=
  ∀ R, WlpInvented c Q R → L R
```

`WlpInvented c Q` is the finite set of assertions that the canonical (Cook-style) derivation of
`{wlp c Q} c {Q}` invents: for each `seq c₁ c₂` reached with postcondition `S`, the midpoint
`wlp c₂ S`; for each loop `while b do c'` reached with postcondition `S`, the invariant
`wlp (while b do c') S`. Examples (`ToyHoare/Examples.lean`): `WlpInvented exLoop exPost
(wlp exLoop exPost)` holds, and the valid inductive invariant "x even" is *not* in
`WlpInvented exLoop exPost` (`wlpInvented_example_neg`); `WlpAdmissibleFor LinDef countdown
(x = 0)` holds (`wlpAdmissibleFor_example_pos`, its only member being `0 ≤ x`) and
`WlpAdmissibleFor LinDef exLoop exPost` fails (`wlpAdmissibleFor_example_neg`).

Linear assertion language (`ToyHoare/Linear.lean`):

```lean
inductive LTerm where
  | lit : Int → LTerm | var : Nat → LTerm | add : LTerm → LTerm → LTerm
  | sub : LTerm → LTerm → LTerm | smul : Int → LTerm → LTerm   -- smul k t = k * t
inductive LAssn where
  | tt | le : LTerm → LTerm → LAssn | eq : LTerm → LTerm → LAssn
  | not : LAssn → LAssn | and : LAssn → LAssn → LAssn | or : LAssn → LAssn → LAssn
-- LTerm.eval and LAssn.eval : LAssn → Store → Bool are the evident evaluations

def LinDef (R : Assn) : Prop := ∃ φ : LAssn, ∀ s, R s ↔ φ.eval s = true
def AffineLine (σ : Int → Store) : Prop := ∀ i : Nat, ∃ a b : Int, ∀ n, σ n i = a * n + b
```

Verification-condition generation (`ToyHoare/VC.lean`):

```lean
inductive ACom where
  | skip | assign : Nat → AExp → ACom | seq : ACom → ACom → ACom
  | cond : BExp → ACom → ACom → ACom | whileDo : Assn → BExp → ACom → ACom
-- ACom.erase forgets the loop annotations

def vcgen : ACom → Assn → Assn × List Assn
  | .skip, Q => (Q, [])
  | .assign x e, Q => (fun s => Q (upd s x (e.eval s)), [])
  | .seq a₁ a₂, Q =>
    ((vcgen a₁ (vcgen a₂ Q).1).1, (vcgen a₁ (vcgen a₂ Q).1).2 ++ (vcgen a₂ Q).2)
  | .cond b a₁ a₂, Q =>
    (fun s => (b.eval s = true → (vcgen a₁ Q).1 s) ∧ (b.eval s = false → (vcgen a₂ Q).1 s),
      (vcgen a₁ Q).2 ++ (vcgen a₂ Q).2)
  | .whileDo I b a, Q =>
    (I, (fun s => I s → b.eval s = true → (vcgen a I).1 s) ::
        (fun s => I s → b.eval s = false → Q s) :: (vcgen a I).2)

def VCsValid (l : List Assn) : Prop := ∀ φ ∈ l, ∀ s, φ s

def annotWlp : Com → Assn → ACom
  | .skip, _ => .skip
  | .assign x e, _ => .assign x e
  | .seq c₁ c₂, Q => .seq (annotWlp c₁ (wlp c₂ Q)) (annotWlp c₂ Q)
  | .cond b c₁ c₂, Q => .cond b (annotWlp c₁ Q) (annotWlp c₂ Q)
  | .whileDo b c, Q => .whileDo (wlp (.whileDo b c) Q) b (annotWlp c (wlp (.whileDo b c) Q))

inductive HeadReach (P : Assn) (b : BExp) (c : Com) : Store → Prop where
  | init {s : Store} : P s → HeadReach P b c s
  | step {s s' : Store} : HeadReach P b c s → b.eval s = true → Exec c s s' → HeadReach P b c s'

def ACom.InvsIn (L : Assn → Prop) : ACom → Prop
  | .skip => True | .assign _ _ => True
  | .seq a₁ a₂ => a₁.InvsIn L ∧ a₂.InvsIn L | .cond _ a₁ a₂ => a₁.InvsIn L ∧ a₂.InvsIn L
  | .whileDo I _ a => L I ∧ a.InvsIn L
```

Total correctness (`ToyHoare/Total.lean`):

```lean
def TValid (P : Assn) (c : Com) (Q : Assn) : Prop := ∀ s, P s → ∃ s', Exec c s s' ∧ Q s'

inductive TDeriv (requireBound : Bool) : Assn → Com → Assn → Prop where
  -- skip, assign, seq (no admissibility predicate), cond, conseq: as in Deriv
  | whileDo {I : Assn} {b : BExp} {c : Com} (V : Store → Int) :
      (∀ n : Int, TDeriv requireBound (fun s => I s ∧ b.eval s = true ∧ V s = n) c
        (fun s => I s ∧ V s < n)) →
      (requireBound = true → ∀ s, I s → b.eval s = true → 0 ≤ V s) →
      TDeriv requireBound I (.whileDo b c) (fun s => I s ∧ b.eval s = false)
```

Concrete programs and assertions used by the examples:

```lean
def exGuard : BExp := .le (.lit 2) (.var 0)                       -- 2 ≤ x
def exBody : Com := .assign 0 (.sub (.var 0) (.lit 2))           -- x := x - 2
def exLoop : Com := .whileDo exGuard exBody                      -- while 2 ≤ x do x := x - 2
def exPre : Assn := fun s => s 0 = s 1 + s 1                     -- x = y + y
def exPost : Assn := fun s => s 0 ≠ 1                            -- x ≠ 1
def exPostWeak : Assn := fun s => s 0 ≤ 1                        -- x ≤ 1
def exParityInv : Assn := fun s => s 0 % 2 = 0                   -- x even
def st2 (a b : Int) : Store := fun i => if i = 0 then a else if i = 1 then b else 0
def countdown : Com :=                                           -- while 0 < x do x := x - 1
  .whileDo (.lt (.lit 0) (.var 0)) (.assign 0 (.sub (.var 0) (.lit 1)))
def exLoopGhost : Com :=                     -- g := y; while 2 ≤ x do (x := x - 2; g := g - 1)
  .seq (.assign 2 (.var 1)) (.whileDo exGuard (.seq exBody (.assign 2 (.sub (.var 2) (.lit 1)))))
def ncGuard : BExp := .lt (.var 0) (.lit 2)                      -- x < 2
def ncBody : Com := .assign 0 (.add (.var 0) (.lit 2))           -- x := x + 2
def ncInv : Assn := fun s => s 0 ≤ 2                             -- x ≤ 2
def ncAnn : ACom := .whileDo ncInv ncGuard (.assign 0 (.add (.var 0) (.lit 2)))
def ncPre : Assn := fun s => s 0 = 0
def ncPost : Assn := fun s => s 0 = 2
def exParityAnn : ACom := .whileDo exParityInv exGuard (.assign 0 (.sub (.var 0) (.lit 2)))
def downBody : Com := .assign 0 (.sub (.var 0) (.lit 1))         -- x := x - 1
def downLoop : Com := .whileDo .tt downBody                      -- while true do x := x - 1
```

Each core definition has proved positive and negative examples in `ToyHoare/Examples.lean`. For
instance, parity is not `LinDef`, and the parity family `n ↦ (fun _ => n % 2)` is not an affine
line; with `L := fun _ => False` the valid triple `{true} skip; skip {true}` is not derivable, so
`L` really constrains sequencing midpoints; and the diverging loop `while true do skip` satisfies
`{true} … {false}` in partial correctness but not `{true} … {true}` in total correctness:

```lean
-- lean/ToyHoare/Examples.lean:152
theorem linDef_example_neg : ¬ LinDef (fun s => s 0 % 2 = 0)
-- lean/ToyHoare/Examples.lean:157
theorem affineLine_example_neg : ¬ AffineLine (fun n : Int => fun _ : Nat => n % 2)
-- lean/ToyHoare/Examples.lean:124-125
theorem deriv_example_neg_empty_L :
    ¬ Deriv (fun _ => False) (fun _ => True) (.seq .skip .skip) (fun _ => True)
-- lean/ToyHoare/Examples.lean:67
theorem valid_example_pos_diverge : Valid (fun _ => True) (.whileDo .tt .skip) (fun _ => False)
-- lean/ToyHoare/Examples.lean:235
theorem tvalid_example_neg : ¬ TValid (fun _ => True) (.whileDo .tt .skip) (fun _ => True)
```

### Result 1 — `hoare-soundness`: soundness of `Deriv L` for every `L`

- **Tier:** T0 (re-derivation). **Kind:** theorem. **Depth:** shallow (induction on the derivation;
  the while case uses the loop-invariant lemma `exec_while_invariant`).
- **Lean statement** (`ToyHoare/Logic.lean`):

  ```lean
  -- lean/ToyHoare/Logic.lean:73-74
  theorem hoare_sound {L : Assn → Prop} {P : Assn} {c : Com} {Q : Assn}
      (h : Deriv L P c Q) : Valid P c Q
  ```

  Unfolded conclusion: `∀ s s', P s → Exec c s s' → Q s'`.
- **Plain claim:** For every admissibility predicate L on assertions, every triple {P} c {Q}
  derivable with the skip, assignment, sequencing, conditional, while and consequence rules
  (consequence premises being true semantic implications, and seq midpoints and loop invariants
  satisfying L) is valid in partial correctness: every terminating run of c from a state satisfying
  P ends in a state satisfying Q.
- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `h : Deriv L P c Q` | the triple must be produced by the rules; without it the conclusion is an arbitrary validity claim | tight: counterexample `hoare_sound_deriv_tight` |
  | `L : Assn → Prop` (arbitrary, no assumption) | soundness does not depend on which assertions a derivation may invent | harmless |

  `hoare_sound_deriv_tight : ¬ Valid (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) ∧
  ∀ L : Assn → Prop, ¬ Deriv L (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0)` — the
  conclusion fails for `{true} x := 1 {x = 0}` (and this triple is derivable for no `L`).
- **Non-vacuity witness:** `nonvacuity_hoare_sound : Deriv LinDef (fun _ => True) exLoop exPostWeak
  ∧ Deriv AnyAssn exPre exLoop exPost`, i.e. `{true} while 2 ≤ x do x := x - 2 {x ≤ 1}` is derivable
  with `L = LinDef` (invariant `true`) and `{x = y + y} while 2 ≤ x do x := x - 2 {x ≠ 1}` with
  `L = AnyAssn` (invariant "x even").
- **Prior art:** rules from Hoare (1969), after Floyd (1967); semantic soundness of Hoare-style
  rules: Hoare and Lauer (1974), Cook (1978); survey: Apt (1981). Mechanized before in Isabelle/HOL
  (Nipkow 1998; Concrete Semantics, `Hoare_Sound_Complete.thy`, theorem `hoare_sound`). Software
  Foundations (volume 2, version 7.1, chapter `Hoare`) proves the individual rules valid; its chapter
  `HoareAsLogic` poses `hoare_sound` for its derivability judgement as an exercise left `Admitted`.
  The Lean 4 course *The Hitchhiker's Guide to Logical Verification* (2025 edition) works with a
  semantic `PartialHoare` triple and rule lemmas. Full records under **Evidence**.
- **Design question:** A verifier built on a Hoare-style program logic must be sound: what exactly
  must hold of the rules (and of the oracle that discharges consequence premises) for every derived
  triple to be valid, and what does a derivation not guarantee (termination, effectiveness)?

### Result 2 — `hoare-relative-completeness-wlp-admissible`: relative completeness assuming `WlpAdmissibleFor L c Q`

This result is **relative**: its main theorem assumes the hypothesis `WlpAdmissibleFor L c Q`
(every assertion in `WlpInvented c Q` satisfies `L`) and does not establish it. Whether it holds
depends on `L`, `c` and `Q`; for `L = LinDef` it fails for the example loop (result 4).

- **Tier:** T0 (Cook-style relative completeness, Cook 1978; Winskel 1993, chapter 7). **Kind:**
  theorem. **Depth:** shallow (the canonical derivation of `{wlp c Q} c {Q}` by induction on `c`,
  followed by monotonicity of `Deriv` in `L`).
- **Lean statements** (`ToyHoare/Logic.lean`):

  ```lean
  -- lean/ToyHoare/Logic.lean:182-183
  theorem hoare_relatively_complete_of_wlpAdmissibleFor {L : Assn → Prop} {P : Assn} {c : Com}
      {Q : Assn} (hwlp : WlpAdmissibleFor L c Q) (hv : Valid P c Q) : Deriv L P c Q
  -- lean/ToyHoare/Logic.lean:167-168
  theorem valid_iff_deriv_wlpInvented {P : Assn} {c : Com} {Q : Assn} :
      Valid P c Q ↔ Deriv (WlpInvented c Q) P c Q
  -- lean/ToyHoare/Logic.lean:174-175
  theorem deriv_wlp_of_wlpAdmissibleFor {L : Assn → Prop} {c : Com} {Q : Assn}
      (hwlp : WlpAdmissibleFor L c Q) : Deriv L (wlp c Q) c Q
  -- lean/ToyHoare/Logic.lean:221-222
  theorem deriv_anyAssn_iff_valid {P : Assn} {c : Com} {Q : Assn} :
      Deriv AnyAssn P c Q ↔ Valid P c Q
  ```

  Unfolded hypothesis: `WlpAdmissibleFor L c Q ≡ ∀ R, WlpInvented c Q R → L R`, where
  `WlpInvented` is quoted under *Core definitions*. `Deriv (WlpInvented c Q)` is `Deriv` whose
  sequencing midpoints and loop invariants are all members of `WlpInvented c Q`.
- **Plain claim:** Relative completeness, relative to the command-local admissibility hypothesis
  WlpAdmissibleFor L c Q, which is assumed and not established by the theorem: for every
  admissibility predicate L, command c and postcondition Q, if WlpAdmissibleFor L c Q holds, i.e.
  every assertion in WlpInvented c Q (the seq midpoints wlp c2 S and the loop invariants
  wlp (while b do c') S met when computing wlp c Q backwards from Q) satisfies L, then every valid
  partial-correctness triple {P} c {Q} is derivable with all seq midpoints and loop invariants in L.
  The invented assertions are exposed: {P} c {Q} is valid if and only if it is derivable with all
  seq midpoints and loop invariants drawn from WlpInvented c Q. In particular, with every semantic
  assertion admissible (L = AnyAssn), a triple is derivable if and only if it is valid; this special
  case carries no admissibility hypothesis.
- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hwlp : WlpAdmissibleFor L c Q` (every member of `WlpInvented c Q` satisfies `L`) | the derivation built by the proof invents exactly these `wlp` assertions as midpoints and invariants | tight: counterexamples `relcomp_wlp_admissible_tight`, `deriv_wlp_needs_admissible` |
  | `hv : Valid P c Q` | only valid triples can be derivable (soundness) | tight: counterexample `relcomp_valid_tight` |
  | `L := AnyAssn` (in `deriv_anyAssn_iff_valid`) | with a restricted `L` the right-to-left direction fails | tight: counterexample `semantic_iff_needs_anyAssn` |

  Counterexample statements (`ToyHoare/Witnesses.lean`):

  ```lean
  -- lean/ToyHoare/Witnesses.lean:66-68
  theorem relcomp_wlp_admissible_tight :
      Valid exPre exLoop exPost ∧ ¬ WlpAdmissibleFor LinDef exLoop exPost ∧
      ¬ Deriv LinDef exPre exLoop exPost
  -- lean/ToyHoare/Witnesses.lean:74-76
  theorem deriv_wlp_needs_admissible :
      ¬ WlpAdmissibleFor LinDef exLoop exPost ∧
      ¬ Deriv LinDef (wlp exLoop exPost) exLoop exPost
  -- lean/ToyHoare/Witnesses.lean:57-60
  theorem relcomp_valid_tight :
      WlpAdmissibleFor AnyAssn (.assign 0 (.lit 1)) (fun s => s 0 = 0) ∧
      ¬ Valid (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) ∧
      ¬ Deriv AnyAssn (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0)
  -- lean/ToyHoare/Witnesses.lean:121-122
  theorem semantic_iff_needs_anyAssn :
      Valid exPre exLoop exPost ∧ ¬ Deriv LinDef exPre exLoop exPost
  ```

- **Non-vacuity witnesses:**

  ```lean
  -- lean/ToyHoare/Witnesses.lean:46-49
  theorem nonvacuity_relcomp :
      (WlpAdmissibleFor LinDef countdown (fun s => s 0 = 0) ∧
        Valid (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) ∧ ¬ ∀ s : Store, s 0 = 0) ∧
      (WlpAdmissibleFor AnyAssn exLoop exPost ∧ Valid exPre exLoop exPost)
  -- lean/ToyHoare/Witnesses.lean:111-115
  theorem nonvacuity_semantic_iff :
      (Deriv AnyAssn exPre exLoop exPost ∧ Deriv (WlpInvented exLoop exPost) exPre exLoop exPost ∧
        Valid exPre exLoop exPost) ∧
      (¬ Deriv AnyAssn (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) ∧
        ¬ Valid (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0))
  ```

  So both hypotheses of the main theorem hold together for `L = LinDef`, the countdown loop
  `while 0 < x do x := x - 1`, the postcondition `x = 0` (which does not hold in every store) and
  `P = (0 ≤ x)` (the only
  invented assertion is `wlp countdown (x = 0)`, which is `0 ≤ x` by `wlp_countdown_iff`), and for
  `L = AnyAssn` with the example triple; the two characterizations have instances on both sides.
- **Related bridge theorems** (quoted with their statements under **Boundaries**, *Boundary and
  bridge theorems*): `wlpAdmissibleFor_of_expressive` (Cook's closure of `L` under `wlp`, together
  with `L Q`, implies `WlpAdmissibleFor L c Q` for every `c`), `wlpAdmissibleFor_of_forall_wlp`,
  `linDef_forall_wlp_iff_tautology` (why the hypothesis is command-local) and
  `wlpAdmissibleFor_not_necessary` (the hypothesis is not necessary for a particular triple).
- **Prior art:** Cook (1978); Winskel (1993, chapter 7, sections 7.2 and 7.4); Bergstra and Tucker
  (1982: expressiveness is sufficient but not necessary for completeness over a first-order
  structure); Apt (1981). Mechanized for semantic assertions in Isabelle/HOL (Nipkow 1998; Concrete
  Semantics, `Hoare_Sound_Complete.thy`: `hoare_complete` via `wp`, corollary
  `hoare_sound_complete`). Software Foundations (volume 2, version 7.1, `HoareAsLogic`) poses
  `hoare_complete` as an `Admitted` exercise and states no derivable-iff-valid theorem. What is
  specific here: the admissibility hypothesis is command-local, and the invented assertion set is
  exposed as `WlpInvented c Q`.
- **Design question:** When a program logic restricts the assertions a derivation may invent (loop
  invariants and intermediate assertions) to a language L, exactly which assertions must L contain
  for every valid triple about a given command and postcondition to be derivable, and is that
  condition necessary?

### Result 3 — `linear-qf-hoare-incomplete`: a valid linear triple with no `Deriv LinDef` derivation

- **Tier:** T1 (folklore made precise: incompleteness for non-expressive assertion languages is
  classical — Cook's expressiveness hypothesis, Wand's structure-specific instance — while
  Bergstra and Tucker show expressiveness is not necessary for completeness in general, so this
  concrete instance needs its own proof; it is stated precisely and mechanized here). **Kind:**
  impossibility. **Depth:** substantive.
- **Lean statements** (`ToyHoare/Incomplete.lean`):

  ```lean
  -- lean/ToyHoare/Incomplete.lean:207-208
  theorem linear_qf_hoare_incomplete :
      LinDef exPre ∧ LinDef exPost ∧ Valid exPre exLoop exPost ∧ ¬ Deriv LinDef exPre exLoop exPost
  -- lean/ToyHoare/Incomplete.lean:173-176
  theorem exLoop_no_linDef_invariant :
      ¬ ∃ I : Assn, LinDef I ∧ (∀ s, exPre s → I s) ∧
        Valid (fun s => I s ∧ exGuard.eval s = true) exBody I ∧
        (∀ s, I s → exGuard.eval s = false → exPost s)
  ```

  Unfolded: `exPre = (x = y + y)`, `exPost = (x ≠ 1)`, `exLoop = while 2 ≤ x do x := x - 2`; `Deriv
  LinDef` requires every sequencing midpoint and loop invariant to be defined by an `LAssn` formula,
  with all other assertions and consequence premises semantic.
- **Plain claim:** The triple {x = y + y} while 2 <= x do x := x - 2 {x != 1}, whose pre- and
  postcondition are quantifier-free linear formulas, is valid but has no derivation in which every
  seq midpoint and loop invariant is definable in divisibility-free quantifier-free linear integer
  arithmetic (LinDef: boolean combinations of <= and = over linear integer terms, without modulo or
  divisibility predicates), even though consequence premises may be arbitrary true semantic
  implications.
- **Proof idea.** Inverting the while rule through consequence steps (`Deriv.whileDo_inv`) gives an
  inductive invariant `I` in `LinDef`. From the precondition at `st2 (4k) (2k)` and the loop body,
  `I` holds at every `st2 (2k) (2k)`; from the exit condition and the body, `I` fails at every
  `st2 (2k+1) b` (`exLoop_invariant_parity`). So `I` alternates beyond every bound along the affine
  diagonal `n ↦ st2 n n`, contradicting result 5.
- **Hypothesis ledger** (the statement is concrete; its "hypotheses" are fixed parameters, and each
  counterexample is a positive control that changes exactly that parameter, keeps the others, and
  makes the triple derivable):

  | Parameter (fixed in the statement) | Why it matters | Tightness |
  | :--- | :--- | :--- |
  | invented assertions restricted to `LinDef` | with semantic assertions the triple is derivable with invariant "x even" | tight: `exLoop_deriv_anyAssn` |
  | postcondition `x ≠ 1` | forces every inductive invariant to exclude all odd `x ≥ 1`; with the linear postcondition `x ≤ 1` (precondition kept) the triple is derivable with invariant `true` | tight: `exLoop_linDef_control_weak_post` |
  | precondition `x = y + y` (x even, witnessed by `y`) | forces every invariant to contain infinitely many even `x` on the diagonal `x = y`; with the linear precondition `x = 0` (postcondition kept) the triple is derivable with invariant `x = 0` | tight: `exLoop_linDef_control_pre_zero` |
  | the program text `while 2 ≤ x do x := x - 2`, with no auxiliary variables | with an auxiliary counter `g := y` decremented in the body, the same linear specification is derivable with the linear invariant `x = g + g` | tight: `exLoopGhost_linDef_control` |

  ```lean
  -- lean/ToyHoare/Incomplete.lean:187
  theorem exLoop_deriv_anyAssn : Deriv AnyAssn exPre exLoop exPost
  -- lean/ToyHoare/Witnesses.lean:134-136
  theorem exLoop_linDef_control_weak_post :
      LinDef exPre ∧ LinDef exPostWeak ∧ Valid exPre exLoop exPostWeak ∧
      Deriv LinDef exPre exLoop exPostWeak
  -- lean/ToyHoare/Witnesses.lean:144-146
  theorem exLoop_linDef_control_pre_zero :
      LinDef (fun s => s 0 = 0) ∧ LinDef exPost ∧ Valid (fun s => s 0 = 0) exLoop exPost ∧
      Deriv LinDef (fun s => s 0 = 0) exLoop exPost
  -- lean/ToyHoare/Witnesses.lean:165-167
  theorem exLoopGhost_linDef_control :
      LinDef exPre ∧ LinDef exPost ∧ Valid exPre exLoopGhost exPost ∧
      Deriv LinDef exPre exLoopGhost exPost
  ```

- **Non-vacuity witness:** the triple is valid and its pre- and postcondition are `LinDef` (the
  first three conjuncts of the statement): `exLoop_valid : Valid exPre exLoop exPost`,
  `exPre_linDef : LinDef exPre`, `exPost_linDef : LinDef exPost`.
- **Positive controls:** the four theorems displayed in the ledger above
  (`exLoop_deriv_anyAssn`, `exLoop_linDef_control_weak_post`, `exLoop_linDef_control_pre_zero`,
  `exLoopGhost_linDef_control`).
- **Prior art:** Cook (1978); Wand (1978: a first-order structure for which Hoare's system for
  while programs is incomplete because the needed invariants are inexpressible — a different
  structure and language); Bergstra and Tucker (1982); Apt (1981); Winskel (1993, chapter 7).
  Software Foundations (volume 2, version 7.1, chapter `Hoare2`, example "Parity", credited there to
  Daniel Cristofani) verifies the same loop over natural numbers with the semantic invariant
  `parity X = parity m`. The mechanizations cited on other results use semantic assertions
  throughout and do not restrict invariants to a syntactic language.
- **Design question:** If a verifier's loop invariants and intermediate assertions must be
  divisibility-free quantifier-free linear formulas, can every valid triple whose specification is
  itself linear be proved, and if not, which change (richer assertion language, different
  specification, or auxiliary program variables) restores provability?

### Result 4 — `linear-qf-not-wlp-expressive`: the `wlp` of the example loop is not `LinDef`

- **Tier:** T1 (instance of the classical non-definability of parity in quantifier-free linear
  arithmetic without divisibility predicates; Marker 2002, section 3.1). **Kind:** impossibility.
  **Depth:** shallow (the `wlp` would be a `LinDef` inductive invariant, contradicting
  `exLoop_no_linDef_invariant` of result 3).
- **Lean statements** (`ToyHoare/Incomplete.lean`, `ToyHoare/Witnesses.lean`):

  ```lean
  -- lean/ToyHoare/Incomplete.lean:216
  theorem linear_qf_not_expressive_wlp_exLoop : ¬ LinDef (wlp exLoop exPost)
  -- lean/ToyHoare/Witnesses.lean:215
  theorem wlp_exLoop_st2_iff (a b : Int) :
      wlp exLoop exPost (st2 a b) ↔ (a ≤ 0 ∨ a % 2 = 0)
  ```

  The second theorem is the exact characterization quoted in the plain claim (on stores with
  `x = a`, `y = b` and all other variables `0`); `%` is Lean's `Int` remainder, which is `0` exactly
  for even `a`. Unfolded: `wlp exLoop exPost s ≡ ∀ s', Exec exLoop s s' → s' 0 ≠ 1`.
- **Plain claim:** The weakest liberal precondition of while 2 <= x do x := x - 2 for the
  postcondition x != 1 (on stores with x = a, y = b and all other variables 0 it holds exactly when
  a <= 0 or a is even) is not definable by any divisibility-free quantifier-free linear integer
  arithmetic formula (boolean combination of <= and = over linear integer terms, without modulo or
  divisibility predicates).
- **Hypothesis ledger:**

  | Parameter (fixed in the statement) | Why it matters | Tightness |
  | :--- | :--- | :--- |
  | postcondition `x ≠ 1` | with the weaker postcondition `x ≤ 1` the `wlp` is `true`, which is definable | tight: `wlp_exLoop_weak_post_linDef : LinDef (wlp exLoop exPostWeak)` |
  | assertion language `LinDef` | with semantic assertions every `wlp` is admissible | tight: `wlp_exLoop_anyAssn : AnyAssn (wlp exLoop exPost)` |

- **Non-vacuity witness:** the `wlp` is a non-trivial assertion:

  ```lean
  -- lean/ToyHoare/Witnesses.lean:201-203
  theorem nonvacuity_wlp_exLoop_nontrivial :
      (∀ s, exPre s → wlp exLoop exPost s) ∧
      (∀ k : Nat, ¬ wlp exLoop exPost (st2 (2 * (k : Int) + 1) 0))
  ```

  together with `wlp_exLoop_st2_iff` above.
- **Positive controls:** `wlp_exLoop_weak_post_linDef`, `wlp_exLoop_anyAssn` (ledger above).
- **Prior art:** Cook (1978); Bergstra and Tucker (1982); Winskel (1993, chapter 7); Marker (2002,
  section 3.1: Presburger arithmetic admits quantifier elimination only after adding divisibility
  predicates); Apt (1981).
- **Design question:** Can a verifier that represents weakest (liberal) preconditions as
  divisibility-free quantifier-free linear formulas compute them exactly for simple constant-stride
  loops, or must it approximate or enrich the language?

### Result 5 — `qf-linear-eventually-constant-on-affine-lines`: eventual constancy of `LAssn` along affine lines

- **Tier:** T0 (textbook fact behind the need for congruence predicates in Presburger quantifier
  elimination; Marker 2002, section 3.1; Presburger-definable sets are the semilinear sets,
  Ginsburg and Spanier 1966; restated for `LAssn` along affine lines of stores). **Kind:** theorem.
  **Depth:** substantive (every linear term is affine in `n` along an affine line; each atom
  `d * n ≤ e` or `d * n = e` stabilizes by a sign/Archimedean argument; boolean combinations take
  the maximum threshold).
- **Lean statements** (`ToyHoare/Linear.lean`):

  ```lean
  -- lean/ToyHoare/Linear.lean:129-130
  theorem LAssn.eventually_const_on_affineLine (φ : LAssn) {σ : Int → Store} (hσ : AffineLine σ) :
      ∃ N : Int, ∃ bv : Bool, ∀ n, N ≤ n → φ.eval (σ n) = bv
  -- lean/ToyHoare/Linear.lean:166-167
  theorem not_linDef_of_alternating_on_affineLine {R : Assn} (σ : Int → Store) (hσ : AffineLine σ)
      (h : ∀ N : Int, ∃ n n', N ≤ n ∧ N ≤ n' ∧ R (σ n) ∧ ¬ R (σ n')) : ¬ LinDef R
  -- lean/ToyHoare/Linear.lean:181
  theorem parity_not_linDef : ¬ LinDef (fun s => s 0 % 2 = 0)
  ```

  Unfolded: `AffineLine σ ≡ ∀ i, ∃ a b : Int, ∀ n, σ n i = a * n + b`; `LinDef R ≡ ∃ φ : LAssn,
  ∀ s, R s ↔ φ.eval s = true`.
- **Plain claim:** Along any affine line of stores n -> sigma n (every variable an affine function
  of the integer n), every divisibility-free quantifier-free linear integer arithmetic formula
  (boolean combination of <= and = over linear terms, without modulo or divisibility predicates)
  has the same truth value for all sufficiently large n (all n >= N for some N); consequently an
  assertion that is true and false beyond every bound along some affine line, such as 'x is even',
  is not definable in that language.
- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hσ : AffineLine σ` (in both theorems) | linear terms become affine functions of `n` only along affine families | tight: `eventually_const_needs_affine`, `alternating_needs_affine` |
  | `h` : the assertion is true and false beyond every bound along `σ` (in `not_linDef_of_alternating_on_affineLine`) | the property contradicting eventual constancy | tight: `alternating_hyp_tight` |

  ```lean
  -- lean/ToyHoare/Witnesses.lean:433-435
  theorem eventually_const_needs_affine :
      ¬ ∃ N : Int, ∃ bv : Bool, ∀ n, N ≤ n →
        (LAssn.eq (.var 0) (.lit 0)).eval ((fun n : Int => fun _ : Nat => n % 2) n) = bv
  -- lean/ToyHoare/Witnesses.lean:459-463
  theorem alternating_needs_affine :
      (∀ N : Int, ∃ n n', N ≤ n ∧ N ≤ n' ∧
        (fun s : Store => s 0 = 0) ((fun n : Int => fun _ : Nat => n % 2) n) ∧
        ¬ (fun s : Store => s 0 = 0) ((fun n : Int => fun _ : Nat => n % 2) n')) ∧
      LinDef (fun s : Store => s 0 = 0)
  -- lean/ToyHoare/Witnesses.lean:448-450
  theorem alternating_hyp_tight :
      AffineLine (fun n => st2 n n) ∧ LinDef exPre ∧
      ¬ (∀ N : Int, ∃ n n', N ≤ n ∧ N ≤ n' ∧ exPre (st2 n n) ∧ ¬ exPre (st2 n' n'))
  ```

  (The family `n ↦ (fun _ => n % 2)` is not affine: `affineLine_example_neg`.)
- **Non-vacuity witness:**

  ```lean
  -- lean/ToyHoare/Witnesses.lean:423-425
  theorem nonvacuity_eventually_const_and_alternating :
      AffineLine (fun n => st2 n n) ∧
      ∀ N : Int, ∃ n n', N ≤ n ∧ N ≤ n' ∧ exParityInv (st2 n n) ∧ ¬ exParityInv (st2 n' n')
  ```

- **Prior art:** Marker (2002, section 3.1); Ginsburg and Spanier (1966).
- **Design question:** Which loop invariants can a verifier restricted to divisibility-free
  quantifier-free linear arithmetic express? The theorem gives a reusable test: an assertion that
  alternates beyond every bound along an affine family of states (for example parity along a
  constant-stride loop) is out of reach.

### Result 6 — `vcgen-soundness`: soundness of VC generation with user-supplied loop invariants

- **Tier:** T0 (Igarashi, London and Luckham 1975; Winskel 1993, section 7.4; Concrete Semantics
  `vc_sound`; hoare-tut). **Kind:** theorem. **Depth:** shallow (valid side conditions yield a
  `Deriv AnyAssn` derivation of `{(vcgen a Q).1} erase a {Q}`, `vcgen_deriv`; then result 1).
- **Lean statement** (`ToyHoare/VC.lean`):

  ```lean
  -- lean/ToyHoare/VC.lean:99-100
  theorem vcgen_sound {a : ACom} {P Q : Assn} (hvc : VCsValid (vcgen a Q).2)
      (hpre : ∀ s, P s → (vcgen a Q).1 s) : Valid P a.erase Q
  ```

  Unfolded: `VCsValid l ≡ ∀ φ ∈ l, ∀ s, φ s` (every side condition holds in every store).
- **Plain claim:** For an annotated program a (every loop carrying an invariant) and postcondition
  Q, if every side condition produced by vcgen a Q holds in every store and P implies the generated
  precondition, then {P} erase a {Q} is valid in partial correctness.
- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `hvc : VCsValid (vcgen a Q).2` | the side conditions carry the inductiveness and exit obligations of each loop annotation | tight: `vcgen_sound_vcs_tight` |
  | `hpre : ∀ s, P s → (vcgen a Q).1 s` | connects the caller's precondition to the computed one | tight: `vcgen_sound_pre_tight` |

  ```lean
  -- lean/ToyHoare/Witnesses.lean:247-248
  /-- `while false do skip` annotated with the invariant `true`. -/
  def falseLoopAnn : ACom := .whileDo (fun _ => True) .ff .skip
  -- lean/ToyHoare/Witnesses.lean:253-255
  theorem vcgen_sound_vcs_tight :
      (∀ s, (fun _ => True) s → (vcgen falseLoopAnn (fun _ => False)).1 s) ∧
      ¬ Valid (fun _ => True) falseLoopAnn.erase (fun _ => False)
  -- lean/ToyHoare/Witnesses.lean:261-263
  theorem vcgen_sound_pre_tight :
      VCsValid (vcgen (.assign 0 (.lit 1)) (fun s => s 0 = 0)).2 ∧
      ¬ Valid (fun _ => True) (ACom.assign 0 (.lit 1)).erase (fun s => s 0 = 0)
  ```

- **Non-vacuity witness:** `nonvacuity_vcgen_sound : VCsValid (vcgen exParityAnn exPost).2 ∧
  ∀ s, exPre s → (vcgen exParityAnn exPost).1 s` (the parity annotation `while[x even] 2 ≤ x do
  x := x - 2` with `P = (x = y + y)`, `Q = (x ≠ 1)`).
- **Prior art:** Igarashi, London and Luckham (1975); Floyd (1967); Winskel (1993, section 7.4);
  Concrete Semantics (`VCG.thy`, `vc_sound`; side conditions checked in every state); Nipkow
  (1998); hoare-tut (Rocq; soundness of a syntactic weakest-precondition generator); the Lean 4
  course *The Hitchhiker's Guide to Logical Verification* (a `vcg` tactic for loops annotated with
  invariants); Software Foundations volume 2, chapter `Hoare2` (fully decorated programs,
  `verification_correct`, soundness only). VC size (Flanagan and Saxe 2001) and unstructured
  programs (Barnett and Leino 2005) are not addressed.
- **Design question:** A verifier generates side conditions from user-supplied loop invariants and
  discharges them with an oracle: under what conditions on the side conditions and the caller's
  precondition is the verified triple valid, and what context (branch conditions, unmodified
  variables) does this generator not use?

### Result 7 — `vcgen-reachable-noninductive-annotation-fails`: an annotation true at every reachable loop head can fail VC generation

- **Tier:** T0 (standard observation that annotations must be inductive, made precise). **Kind:**
  counterexample (concrete; no hypotheses). **Depth:** shallow.
- **Lean statement** (`ToyHoare/VC.lean`):

  ```lean
  -- lean/ToyHoare/VC.lean:229-237
  theorem vcgen_reachable_noninductive_annotation_fails :
      Valid ncPre ncAnn.erase ncPost ∧
      (∀ s, HeadReach ncPre ncGuard ncBody s → ncInv s) ∧
      (∀ s, ncPre s → (vcgen ncAnn ncPost).1 s) ∧
      (∀ s, ncInv s → ncGuard.eval s = false → ncPost s) ∧
      ¬ HeadReach ncPre ncGuard ncBody (st2 1 0) ∧
      (ncInv (st2 1 0) ∧ ncGuard.eval (st2 1 0) = true ∧
        ¬ (vcgen (.assign 0 (.add (.var 0) (.lit 2))) ncInv).1 (st2 1 0)) ∧
      ¬ VCsValid (vcgen ncAnn ncPost).2
  ```

  Unfolded: `ncAnn.erase = while x < 2 do x := x + 2`, `ncPre = (x = 0)`, `ncPost = (x = 2)`,
  `ncInv = (x ≤ 2)`; `(vcgen (x := x + 2) ncInv).1 s` is `ncInv (upd s 0 (s 0 + 2))`, i.e.
  `s 0 + 2 ≤ 2`; `HeadReach` is the set of
  loop-head states reachable from `ncPre`.
- **Plain claim:** For {x = 0} while x < 2 do x := x + 2 {x = 2} with the loop annotated by x <= 2:
  the triple is valid; the annotation holds in every state reachable at the loop head; x = 0
  implies the generated precondition; the exit side condition (x <= 2 and not x < 2 imply x = 2) is
  valid; but the preservation side condition fails at the store with x = 1 (other variables 0),
  which satisfies the annotation and the guard and is not reachable at the loop head; hence not all
  generated side conditions are valid.
- **Hypothesis ledger:** none (concrete instance).
- **Non-vacuity witness:** the statement itself (all parts are proved conjuncts).
- **Positive control:** the same program with the stronger divisibility-free linear annotation
  `x = 0 ∨ x = 2` is verified:

  ```lean
  -- lean/ToyHoare/Witnesses.lean:269-270
  def ncAnnLin : ACom :=
    .whileDo (fun s => s 0 = 0 ∨ s 0 = 2) ncGuard (.assign 0 (.add (.var 0) (.lit 2)))
  -- lean/ToyHoare/Witnesses.lean:275-277
  theorem ncAnnLin_verifies :
      ncAnnLin.erase = ncAnn.erase ∧ ncAnnLin.InvsIn LinDef ∧
      VCsValid (vcgen ncAnnLin ncPost).2 ∧ ∀ s, ncPre s → (vcgen ncAnnLin ncPost).1 s
  ```

- **Prior art:** Concrete Semantics (`VCG.thy`); Winskel (1993, chapter 7); Igarashi, London and
  Luckham (1975).
- **Design question:** If a user annotates a loop with an assertion that holds in every reachable
  loop-head state, will VC generation accept it, or must annotations be inductive, and is a failure
  due to the annotation language?

### Result 8 — `vcgen-complete-wlp-annotation`: VC generation is complete for the `wlp` annotation

- **Tier:** T0 (Concrete Semantics `vc_complete` gives an annotation existentially, starting from a
  derivation; hoare-tut proves completeness of a `wp` generator whose loop case uses the `wlp`;
  here the witness annotation `annotWlp c Q` is exposed and the starting point is validity).
  **Kind:** characterization. **Depth:** shallow (induction on `c`).
- **Lean statements** (`ToyHoare/VC.lean`):

  ```lean
  -- lean/ToyHoare/VC.lean:178-180
  theorem valid_iff_vcs_annotWlp {P : Assn} {c : Com} {Q : Assn} :
      Valid P c Q ↔
        (VCsValid (vcgen (annotWlp c Q) Q).2 ∧ ∀ s, P s → (vcgen (annotWlp c Q) Q).1 s)
  -- lean/ToyHoare/VC.lean:124-125
  theorem vcgen_annotWlp (c : Com) :
      ∀ Q, (∀ s, (vcgen (annotWlp c Q) Q).1 s ↔ wlp c Q s) ∧ VCsValid (vcgen (annotWlp c Q) Q).2
  -- lean/ToyHoare/VC.lean:114
  theorem erase_annotWlp (c : Com) : ∀ Q, (annotWlp c Q).erase = c
  ```

  `annotWlp` (quoted under *Core definitions*) annotates each loop with
  `wlp (while b do c') S` for the postcondition `S` holding after it, computed backwards from `Q`.
- **Plain claim:** For every command c and assertions P, Q: {P} c {Q} is valid iff, for the
  annotation annotWlp c Q (which erases to c and annotates each loop with the wlp of that loop for
  the postcondition holding after it), all generated side conditions are valid and P implies the
  generated precondition; moreover those side conditions are always valid and the generated
  precondition is pointwise equivalent to wlp c Q.
- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | annotations may be arbitrary semantic assertions (`annotWlp` uses `wlp`) | the witness annotation is semantic; with linear annotations completeness fails | tight: `vcgen_linear_qf_annotations_incomplete` (result 9) |

- **Non-vacuity witness:** `nonvacuity_vcs_annotWlp : VCsValid (vcgen (annotWlp exLoop exPost)
  exPost).2 ∧ ∀ s, exPre s → (vcgen (annotWlp exLoop exPost) exPost).1 s`.
- **Prior art:** Concrete Semantics (`VCG.thy`, `vc_complete`); hoare-tut (Rocq, `Theorem
  completeness` of `synt_wp`); Nipkow (1998); Winskel (1993, chapter 7).
- **Design question:** Is VC generation with user-supplied loop invariants complete in principle,
  i.e. does every valid triple have some annotation whose side conditions are valid, and which
  annotation is it?

### Result 9 — `vcgen-linear-qf-annotations-incomplete`: VC generation with `LinDef` loop invariants cannot verify the example triple

- **Tier:** T1 (VC-generation counterpart of result 3; same classical background, Cook 1978 and
  Wand 1978; mechanized here). **Kind:** impossibility. **Depth:** shallow (an annotation erasing to
  the loop has one invariant, which `vcgen_sound` turns into a `LinDef` inductive invariant,
  contradicting `exLoop_no_linDef_invariant`).
- **Lean statement** (`ToyHoare/VC.lean`):

  ```lean
  -- lean/ToyHoare/VC.lean:286-289
  theorem vcgen_linear_qf_annotations_incomplete :
      LinDef exPre ∧ LinDef exPost ∧ Valid exPre exLoop exPost ∧
      ∀ a : ACom, a.erase = exLoop → a.InvsIn LinDef →
        ¬ (VCsValid (vcgen a exPost).2 ∧ ∀ s, exPre s → (vcgen a exPost).1 s)
  ```

- **Plain claim:** The triple {x = y + y} while 2 <= x do x := x - 2 {x != 1}, whose pre- and
  postcondition are quantifier-free linear formulas, is valid but cannot be verified by VC
  generation with any annotation whose loop invariants are definable in divisibility-free
  quantifier-free linear integer arithmetic (without modulo or divisibility predicates): for every
  annotated program a that erases to this loop and has only such invariants, some generated side
  condition is invalid or x = y + y does not imply the generated precondition.
- **Hypothesis ledger:**

  | Hypothesis or parameter | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `ha : a.erase = exLoop` | the annotation must be of this loop; the annotated program `skip` verifies `{x = y + y} skip {x ≠ 1}` | tight: `vcgen_erase_hyp_tight` |
  | `hL : a.InvsIn LinDef` (every loop invariant of `a` is linearly definable) | the semantic invariant "x even" verifies the loop | tight: `vcgen_invsIn_hyp_tight` |
  | parameter (fixed in the statement): postcondition `x ≠ 1` | with the linear postcondition `x ≤ 1` (precondition kept) the invariant `true` verifies the loop | tight: `vcgen_linDef_control_weak_post` |
  | parameter (fixed in the statement): precondition `x = y + y` | with the linear precondition `x = 0` (postcondition kept) the invariant `x = 0` verifies the loop | tight: `vcgen_linDef_control_pre_zero` |
  | parameter (fixed in the statement): the program text, with no auxiliary variables | the loop instrumented with an auxiliary counter `g` is verified with the linear invariant `x = g + g` | tight: `vcgen_ghost_linDef_control` |

  ```lean
  -- lean/ToyHoare/Witnesses.lean:338-340
  theorem vcgen_erase_hyp_tight :
      ACom.skip.erase ≠ exLoop ∧ ACom.skip.InvsIn LinDef ∧
      VCsValid (vcgen .skip exPost).2 ∧ ∀ s, exPre s → (vcgen .skip exPost).1 s
  -- lean/ToyHoare/Witnesses.lean:348-350
  theorem vcgen_invsIn_hyp_tight :
      exParityAnn.erase = exLoop ∧ ¬ exParityAnn.InvsIn LinDef ∧
      VCsValid (vcgen exParityAnn exPost).2 ∧ ∀ s, exPre s → (vcgen exParityAnn exPost).1 s
  -- lean/ToyHoare/Witnesses.lean:355-357
  -- exTrueAnn: exLoop annotated with `true`; exZeroAnn: exLoop annotated with `x = 0`
  theorem vcgen_linDef_control_weak_post :
      LinDef exPre ∧ LinDef exPostWeak ∧ exTrueAnn.erase = exLoop ∧ exTrueAnn.InvsIn LinDef ∧
      VCsValid (vcgen exTrueAnn exPostWeak).2 ∧ ∀ s, exPre s → (vcgen exTrueAnn exPostWeak).1 s
  -- lean/ToyHoare/Witnesses.lean:368-371
  theorem vcgen_linDef_control_pre_zero :
      LinDef (fun s => s 0 = 0) ∧ LinDef exPost ∧ exZeroAnn.erase = exLoop ∧
      exZeroAnn.InvsIn LinDef ∧
      VCsValid (vcgen exZeroAnn exPost).2 ∧ ∀ s, s 0 = 0 → (vcgen exZeroAnn exPost).1 s
  -- lean/ToyHoare/Witnesses.lean:390-392
  -- exGhostAnn: g := y; while[x = g + g] 2 ≤ x do (x := x - 2; g := g - 1)
  theorem vcgen_ghost_linDef_control :
      LinDef exPre ∧ LinDef exPost ∧ exGhostAnn.erase = exLoopGhost ∧ exGhostAnn.InvsIn LinDef ∧
      VCsValid (vcgen exGhostAnn exPost).2 ∧ ∀ s, exPre s → (vcgen exGhostAnn exPost).1 s
  ```

- **Non-vacuity witness:** `nonvacuity_vcgen_linear_qf_incomplete : LinDef exPre ∧ LinDef exPost ∧
  Valid exPre exLoop exPost ∧ exTrueAnn.erase = exLoop ∧ exTrueAnn.InvsIn LinDef` (the hypotheses
  on `a` are jointly satisfiable).
- **Positive controls:** `vcgen_invsIn_hyp_tight`, `vcgen_linDef_control_weak_post`,
  `vcgen_linDef_control_pre_zero`, `vcgen_ghost_linDef_control` (displayed above).
- **Prior art:** Cook (1978); Wand (1978); Bergstra and Tucker (1982); Concrete Semantics
  (`VCG.thy`); Software Foundations volume 2, chapter `Hoare2`, example "Parity".
- **Design question:** If a verifier's user-supplied loop invariants must be divisibility-free
  quantifier-free linear formulas, can it verify every valid loop whose specification is linear, and
  which escape hatches (richer annotation language, auxiliary variables, different specification)
  restore verifiability?

### Result 10 — `total-soundness-bounded-variant`: total-correctness soundness with bounded integer variants

- **Tier:** T0 (Manna and Pnueli 1974; Apt 1981, section 2.8; Concrete Semantics 12.5, mechanized
  with natural-number measures in `Hoare_Total.thy`). **Kind:** theorem. **Depth:** shallow
  (induction on the derivation; the while case by induction on `(V s).toNat + 1`).
- **Lean statement** (`ToyHoare/Total.lean`):

  ```lean
  -- lean/ToyHoare/Total.lean:58-59
  theorem total_sound_of_bounded_variant {P : Assn} {c : Com} {Q : Assn}
      (h : TDeriv true P c Q) : TValid P c Q
  ```

  Unfolded conclusion: `∀ s, P s → ∃ s', Exec c s s' ∧ Q s'`; `TDeriv true` is quoted under *Core
  definitions* (with `requireBound = true` the while rule requires `0 ≤ V s` whenever `I s` and the
  guard hold).
- **Plain claim:** Every triple derivable in the total-correctness system whose while rule requires
  an integer variant that strictly decreases on each iteration and is nonnegative whenever the
  invariant and the guard hold is valid in total correctness: from every state satisfying the
  precondition the program terminates in a state satisfying the postcondition.
- **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness |
  | :--- | :--- | :--- |
  | `h : TDeriv true P c Q` (variant bounded below by `0` under invariant and guard) | a decreasing integer variant without a lower bound does not force termination | tight: `unbounded_variant_unsound` (result 11) |

- **Non-vacuity witness:** `nonvacuity_total_sound : TDeriv true (fun s => 0 ≤ s 0) countdown
  (fun s => s 0 = 0)` (`[0 ≤ x] while 0 < x do x := x - 1 [x = 0]` with invariant `0 ≤ x` and
  variant `x`).
- **Prior art:** Manna and Pnueli (1974); Apt (1981, section 2.8: an integer-valued termination
  function bounded below by `0` that decreases with each iteration); Concrete Semantics section 12.5
  and `Hoare_Total.thy` (`hoaret_sound`, `hoaret_complete`, `hoaret_sound_complete`, with
  natural-number-valued measures, so the bound is built into the type; total validity uses an
  existential over final states, justified there by determinism); Floyd (1967); hoare-tut
  (`totalhoarelogic.v`, well-founded variant); the Lean 4 course *The Hitchhiker's Guide to Logical
  Verification* (`TotalHoare` with natural-number variants, posed as exercises); Schirmer's Simpl
  (Archive of Formal Proofs, 2008: Hoare logics for partial and total correctness, sound and
  complete, for a language with procedures, abrupt termination, heap and unbounded nondeterminism).
- **Design question:** What exactly must a total-correctness loop rule demand of an integer-valued
  variant for termination proofs to be sound, and what does a total-correctness derivation in this
  system guarantee?

### Result 11 — `unbounded-variant-unsound`: dropping the variant's lower bound is unsound

- **Tier:** T0 (standard observation that a decreasing integer measure must be bounded below, made
  precise as a derivation in a system that differs only by the missing premise). **Kind:**
  counterexample (concrete; no hypotheses). **Depth:** shallow.
- **Lean statement** (`ToyHoare/Total.lean`):

  ```lean
  -- lean/ToyHoare/Total.lean:127-133
  theorem unbounded_variant_unsound :
      (∀ n : Int, TDeriv false (fun s => True ∧ BExp.tt.eval s = true ∧ s 0 = n) downBody
        (fun s => True ∧ s 0 < n)) ∧
      ¬ (∀ s : Store, True → BExp.tt.eval s = true → 0 ≤ s 0) ∧
      TDeriv false (fun _ => True) downLoop (fun _ => True) ∧
      (∀ s s' : Store, ¬ Exec downLoop s s') ∧
      ¬ TValid (fun _ => True) downLoop (fun _ => True)
  ```

  Unfolded: `downBody = (x := x - 1)`, `downLoop = while true do x := x - 1`. The first conjunct is
  the per-iteration premise of the while rule for invariant `true` and variant `V := fun s => s 0`;
  the second says the lower-bound premise `0 ≤ x` fails.
- **Plain claim:** In the total-correctness system without the lower-bound premise, the while rule
  applies to while true do x := x - 1 with invariant true and variant x: one iteration from a state
  with x = n ends with x < n, while x is not bounded below; so [true] while true do x := x - 1
  [true] is derivable, yet the loop has no terminating run from any state and the triple is not
  valid in total correctness.
- **Hypothesis ledger:** none (concrete instance).
- **Non-vacuity witness:** the statement itself (all parts are proved conjuncts).
- **Prior art:** Apt (1981, section 2.8); Manna and Pnueli (1974); Concrete Semantics section 12.5
  and `Hoare_Total.thy` (natural-number measures; no counterexample with an unbounded integer
  variant is formalized there).
- **Design question:** Can a total-correctness loop rule omit the lower bound on an integer-valued
  variant without becoming unsound?

## Boundaries

### Non-claims (per result)

These are verbatim from the `non_claims` field of `results.json`. Names in parentheses are Lean
theorems of this package; those not displayed under **Findings** are quoted with their statements
under *Boundary and bridge theorems* below.

**Result 1 — `hoare-soundness`** — non-claims:

- Soundness is relative to the consequence premises being true semantic implications; in Lean they are proofs. Nothing is claimed about a verifier whose implication checker is unsound.
- Partial correctness only: a derivable triple says nothing about termination (see total-soundness-bounded-variant).
- Says nothing about how to find derivations, about decidability, or about proof size.
- Deriv L restricts only sequencing midpoints and while-loop invariants to L; pre- and postconditions, assignment preconditions Q[e/x], branch-guarded preconditions P and b, and the intermediate assertions P', Q' of the consequence rule remain unrestricted semantic predicates.
- Deriv L and verification by vcgen with loop annotations in L (ACom.InvsIn L) do not coincide in general: Deriv.seq requires an L midpoint at every ';', while vcgen propagates preconditions across ';' and assignments semantically (for L = LinDef see vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef).
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 2 — `hoare-relative-completeness-wlp-admissible`** — non-claims:

- Deriv is a proposition: the theorems assert that a derivation exists and expose only the set WlpInvented c Q from which its seq midpoints and loop invariants are drawn (valid_iff_deriv_wlpInvented); they do not say which member is used where, and do not exclude other derivations with other invariants.
- Admissibility of the wlp's along c (WlpAdmissibleFor L c Q) is sufficient but not necessary for deriving a particular valid triple {P} c {Q} in Deriv L: for example, {x = 0} while 2 <= x do x := x - 2 {x != 1} is derivable in Deriv LinDef with the stronger linear invariant x = 0, although the wlp of that loop for x != 1 is not linearly definable (wlpAdmissibleFor_not_necessary). More generally, Cook's wlp-expressiveness is not a necessary condition for completeness of Hoare's logic over a first-order structure (Bergstra and Tucker 1982).
- The hypothesis is command-local on purpose: requiring L (wlp c' Q) for every command c' would hold for L = LinDef only when Q holds in every store (linDef_forall_wlp_iff_tautology). The command-local hypothesis is not claimed to be the weakest possible.
- Relative completeness: consequence premises are semantic facts supplied by an oracle; nothing here gives an effective or decidable proof procedure.
- No syntactic assertion language is shown to be expressive (Cook and Winskel use first-order arithmetic with quantifiers); the only syntactic language studied here (divisibility-free quantifier-free linear arithmetic) is shown not to be expressive for one loop.
- Deriv L is not a fully syntactic Hoare logic over L: a syntactic calculus would also require the assignment preconditions Q[e/x] (programs may multiply variables), the guard conjunctions P and b, I and not b (guards may compare products), and the intermediate assertions P', Q' of consequence steps to belong to L; Deriv L restricts only seq midpoints and loop invariants.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 3 — `linear-qf-hoare-incomplete`** — non-claims:

- Concerns this one triple; it does not characterize which triples are derivable with linear invariants.
- Applies only to the fixed, uninstrumented command while 2 <= x do x := x - 2: adding an auxiliary variable g initialized to y and decremented by 1 in each iteration (g := y; while 2 <= x do (x := x - 2; g := g - 1)) makes the same specification derivable in Deriv LinDef with the divisibility-free linear invariant x = g + g and body midpoint x = g + g - 2 (exLoopGhost_linDef_control).
- Depends on both the precondition x = y + y and the postcondition x != 1: with precondition x = 0 (invariant x = 0) or with the weaker postcondition x <= 1 (invariant true) the uninstrumented loop is derivable with linear invariants (exLoop_linDef_control_pre_zero, exLoop_linDef_control_weak_post).
- LinDef covers only boolean combinations of <= and = over linear terms with integer coefficients, without modulo or divisibility predicates. It is strictly weaker than the SMT-LIB logic QF_LIA, whose formulas may use the predicates (_ divisible n) of the Ints theory: there '(_ divisible 2) x' is a quantifier-free invariant that verifies the loop. Adding a divisibility (parity) atom or an existential quantifier to LinDef would likewise define the needed invariant 'x even'.
- The obstruction is expressiveness, not decidability: the consequence rule here accepts every true implication, which is stronger than any decision procedure.
- A fully syntactic Hoare logic over the linear formulas (assignment by syntactic substitution) is not formalized; that it also cannot derive the triple follows because each of its derivations is a Deriv LinDef derivation (an argument, not mechanized).
- Deriv LinDef is strictly more restrictive than VC generation with linear loop annotations (ACom.InvsIn LinDef) on sequential composition: Deriv.seq requires a LinDef midpoint at every ';', whereas vcgen propagates preconditions across ';' and assignments semantically. For example, the loop-free triple {true} x := y * y; x := x - y * y {x = 0} is verified by vcgen but not derivable in Deriv LinDef (vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef). For the one-loop program here both fail.
- The program uses only linear arithmetic; multiplication in programs plays no role in this example.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 4 — `linear-qf-not-wlp-expressive`** — non-claims:

- Not a claim about first-order (quantified) Presburger arithmetic or about linear arithmetic with divisibility predicates, both of which define this wlp (x <= 0 or 2 divides x).
- LinDef excludes modulo and divisibility predicates; in the SMT-LIB logic QF_LIA, which allows the predicates (_ divisible n), this wlp is definable without quantifiers as (x <= 0) or ((_ divisible 2) x).
- Non-definability of wlp c Q in LinDef does not mean that no valid triple {P} c {Q} is derivable in Deriv LinDef or verifiable by vcgen with a linear loop invariant: for the precondition x = 0 the stronger linear invariant x = 0 suffices (exLoop_linDef_control_pre_zero, vcgen_linDef_control_pre_zero). It rules out only the uniform wlp-based (Cook-style) construction for this loop and postcondition; in general Cook's expressiveness is not necessary for completeness (Bergstra and Tucker 1982).
- Shows non-expressiveness for one command and postcondition; no classification of which wlp's are linear.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 5 — `qf-linear-eventually-constant-on-affine-lines`** — non-claims:

- Covers only the language LAssn (true, <=, =, not, and, or over linear terms with integer coefficients); a divisibility atom such as 2 | x breaks eventual constancy, and formulas of the SMT-LIB logic QF_LIA that use (_ divisible n) are eventually periodic rather than eventually constant along affine lines.
- Eventual constancy is one-sided: it is stated for n -> +infinity (all n >= N). The analogous statement for n -> -infinity (by reversing the line) is not stated here, and the two eventual truth values can differ: along the diagonal, 0 <= x is true for all n >= 0 and false for all n <= -1 (lassn_eventually_const_one_sided). Nothing is said about n < N.
- Says nothing about decidability or quantifier elimination.

**Result 6 — `vcgen-soundness`** — non-claims:

- Side conditions are semantic predicates whose validity is assumed checked by an oracle; they are not syntactic formulas and their decidability is not addressed.
- vcgen collects loop preservation and exit obligations into one list checked in every store (VCsValid), without the guards of enclosing conditionals and without facts about variables the loop does not modify. Unlike verifiers that cut loops by havocking only the modified variables, a loop inside a branch that is never taken still yields globally checked side conditions ({x = 0} if x = 1 then (while[true] false do skip) else skip {x = 0} is valid, yet its side conditions are not all valid: vcgen_side_conditions_ignore_branch_guards), and facts about unmodified variables must be repeated in the loop invariant.
- Restricting loop annotations to LinDef (ACom.InvsIn LinDef) with linear pre- and postconditions does not keep the generated precondition or side conditions in linear arithmetic when the program multiplies variables, and vcgen with linear loop annotations is not equivalent to Deriv LinDef (vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef).
- Nothing about VC size or sharing (the concern of Flanagan and Saxe 2001).
- Partial correctness only.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 7 — `vcgen-reachable-noninductive-annotation-fails`** — non-claims:

- Does not say reachable-state invariants are useless: the exact set of reachable loop-head states is always inductive; the failure is for a strictly larger annotation.
- The failure is due to the specific weak annotation x <= 2, not to the expressiveness of linear arithmetic: the same triple is verified by vcgen with the stronger divisibility-free linear annotation x = 0 or x = 2 (ncAnnLin_verifies).
- Concerns 1-inductive VC generation. The annotation x <= 2 is not k-inductive for any k either (ncInv_not_k_inductive), so k-induction does not rescue it; bounded unrolling would succeed here only because the loop runs at most once from x = 0, which is not formalized.
- Side conditions are checked in every store, without path conditions (see vcgen-soundness).
- Covers a single top-level loop; HeadReach is defined only for that shape.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 8 — `vcgen-complete-wlp-annotation`** — non-claims:

- annotWlp is not computable from program text in general: wlp is a semantic object and may be inexpressible in a syntactic language (vcgen-linear-qf-annotations-incomplete).
- Does not show that annotations can be inferred automatically, nor that the resulting side conditions are easy to discharge.
- This does not follow from Hoare-logic relative completeness by itself; it is proved directly from properties of wlp.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 9 — `vcgen-linear-qf-annotations-incomplete`** — non-claims:

- About this single loop; no characterization of loops verifiable with linear annotations.
- Applies only to annotations erasing to the uninstrumented loop while 2 <= x do x := x - 2: instrumenting the program with an auxiliary variable g := y decremented by 1 in the loop body makes the specification verifiable by vcgen with the divisibility-free linear invariant x = g + g (vcgen_ghost_linDef_control).
- Depends on both the precondition x = y + y and the postcondition x != 1: with precondition x = 0 (invariant x = 0) or the weaker postcondition x <= 1 (invariant true), the uninstrumented loop is verifiable by vcgen with linear annotations (vcgen_linDef_control_pre_zero, vcgen_linDef_control_weak_post).
- LinDef covers only boolean combinations of <= and = over linear terms with integer coefficients, without modulo or divisibility predicates. It is strictly weaker than the SMT-LIB logic QF_LIA, whose formulas may use the predicates (_ divisible n) of the Ints theory: there '(_ divisible 2) x' is a quantifier-free invariant that verifies the loop. Adding a divisibility (parity) atom or an existential quantifier to LinDef would likewise define the needed invariant 'x even'.
- VC verifiability with linear loop annotations is not equivalent to derivability in Deriv LinDef for general programs: vcgen composes sequential statements semantically without requiring a LinDef midpoint at ';', whereas Deriv.seq requires one (vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef). For this one-loop program both fail.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 10 — `total-soundness-bounded-variant`** — non-claims:

- No total-correctness completeness is claimed.
- Variants are Int-valued with an explicit lower bound 0 under invariant and guard; general well-founded orders are not formalized (Isabelle's Hoare_Total.thy uses nat-valued measures, which build the bound into the type).
- In TDeriv, invariants, intermediate assertions and variants are arbitrary semantic predicates and functions on stores, not syntactic expressions, and there is no admissibility predicate L; no total-correctness VC generator is formalized.
- TValid P c Q (from every state satisfying P some run terminates in a state satisfying Q) expresses guaranteed termination only because Exec is deterministic; for a nondeterministic language this existential definition would express possible termination only. Nondeterminism is not formalized.
- Other forms of the lower-bound premise are not formalized. A fixed bound c0 <= V with c0 independent of the store reduces to this rule with the shifted variant V - c0 (an argument, not mechanized); a store-dependent bound B s <= V s is no restriction in general (take B := V - 1) and gives no termination guarantee, as the derivation in unbounded_variant_unsound illustrates.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.

**Result 11 — `unbounded-variant-unsound`** — non-claims:

- Shows only that the lower-bound premise cannot simply be dropped; other ways to restore soundness (nat-valued variants, well-founded orders, a fixed constant bound) are not formalized here.
- In TDeriv, invariants, intermediate assertions and variants are arbitrary semantic predicates and functions on stores, not syntactic expressions, and there is no admissibility predicate L; no total-correctness VC generator is formalized.
- TValid P c Q (from every state satisfying P some run terminates in a state satisfying Q) expresses guaranteed termination only because Exec is deterministic; for a nondeterministic language this existential definition would express possible termination only. Nondeterminism is not formalized.
- Toy model: unbounded Int variables, no heap, no procedures, no runtime errors, no overflow, deterministic big-step semantics. These theorems neither establish nor refute the corresponding claims about real program verifiers, SMT solvers or intermediate verification languages; the modeling bridge under Applicability argues the connection separately.
### Boundary and bridge theorems

The following fully proved theorems delimit the results above and are cited by name in the
non-claims. They are not result statements of any card; their axioms and statement and closure
hashes (computed exactly as for the card statements) are listed under **Evidence**, *Boundary and
bridge theorems*.

Why the relative-completeness hypothesis is command-local (`ToyHoare/Boundaries.lean`,
`ToyHoare/Logic.lean`):

```lean
-- lean/ToyHoare/Boundaries.lean:140-141
-- Requiring LinDef (wlp c' Q) for *every* command c' holds only for postconditions Q that hold
-- in every store.
theorem linDef_forall_wlp_iff_tautology (Q : Assn) :
    (∀ c' : Com, LinDef (wlp c' Q)) ↔ (∀ s : Store, Q s)
-- lean/ToyHoare/Logic.lean:189-190
-- The global form implies the command-local hypothesis.
theorem wlpAdmissibleFor_of_forall_wlp {L : Assn → Prop} (c : Com) :
    ∀ Q : Assn, (∀ c' : Com, L (wlp c' Q)) → WlpAdmissibleFor L c Q
-- lean/ToyHoare/Logic.lean:214-216
-- Cook's expressiveness (L closed under wlp) together with L Q implies the hypothesis for every c.
theorem wlpAdmissibleFor_of_expressive {L : Assn → Prop} {Q : Assn}
    (hexp : ∀ (c : Com) (R : Assn), L R → L (wlp c R)) (hQ : L Q) (c : Com) :
    WlpAdmissibleFor L c Q
```

The hypothesis is sufficient, not necessary, for a particular triple (`ToyHoare/Witnesses.lean`):

```lean
-- lean/ToyHoare/Witnesses.lean:102-104
theorem wlpAdmissibleFor_not_necessary :
    ¬ WlpAdmissibleFor LinDef exLoop exPost ∧ LinDef (fun s => s 0 = 0) ∧
    Deriv LinDef (fun s => s 0 = 0) exLoop exPost
```

`vcgen` with linear loop annotations differs from `Deriv LinDef` even without loops
(`ToyHoare/Boundaries.lean`):

```lean
-- lean/ToyHoare/Boundaries.lean:193-196
/-- `x := y * y; x := x - y * y`. -/
def quadSeqCom : Com :=
  .seq (.assign 0 (.mul (.var 1) (.var 1)))
       (.assign 0 (.sub (.var 0) (.mul (.var 1) (.var 1))))
-- lean/ToyHoare/Boundaries.lean:198-201
/-- `quadSeqCom` as an annotated command (it has no loops). -/
def quadSeqAnn : ACom :=
  .seq (.assign 0 (.mul (.var 1) (.var 1)))
       (.assign 0 (.sub (.var 0) (.mul (.var 1) (.var 1))))
-- lean/ToyHoare/Boundaries.lean:371-378
theorem vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef :
    LinDef (fun _ => True) ∧
    LinDef (fun s => s 0 = 0) ∧
    quadSeqAnn.erase = quadSeqCom ∧
    quadSeqAnn.InvsIn LinDef ∧
    VCsValid (vcgen quadSeqAnn (fun s => s 0 = 0)).2 ∧
    (∀ s, (fun _ : Store => True) s → (vcgen quadSeqAnn (fun s => s 0 = 0)).1 s) ∧
    ¬ Deriv LinDef (fun _ => True) quadSeqCom (fun s => s 0 = 0)
```

(Every valid midpoint must separate `x = y * y` from `x = y * y + 1`, which no `LAssn` formula does
for large `y`, by `lassnEvalParabolaNeighborEq`.)

`vcgen` side conditions are checked in every store, even for a loop in a branch that is never
taken (`ToyHoare/Boundaries.lean`):

```lean
-- lean/ToyHoare/Boundaries.lean:408-411
/-- `if x = 1 then (while[true] false do skip) else skip`: a loop, annotated with `true`, inside a
branch that is never taken from `x = 0`. -/
def deadBranchAnn : ACom :=
  .cond (.eq (.var 0) (.lit 1)) (.whileDo (fun _ => True) .ff .skip) .skip
-- lean/ToyHoare/Boundaries.lean:417-421
theorem vcgen_side_conditions_ignore_branch_guards :
    Valid (fun s => s 0 = 0) deadBranchAnn.erase (fun s => s 0 = 0) ∧
    deadBranchAnn.InvsIn LinDef ∧
    (∀ s, s 0 = 0 → (vcgen deadBranchAnn (fun s => s 0 = 0)).1 s) ∧
    ¬ VCsValid (vcgen deadBranchAnn (fun s => s 0 = 0)).2
```

Eventual constancy is one-sided (`ToyHoare/Boundaries.lean`):

```lean
-- lean/ToyHoare/Boundaries.lean:438-440
theorem lassn_eventually_const_one_sided :
    (∀ n : Int, 0 ≤ n → (LAssn.le (.lit 0) (.var 0)).eval (st2 n n) = true) ∧
    (∀ n : Int, n ≤ -1 → (LAssn.le (.lit 0) (.var 0)).eval (st2 n n) = false)
```

The non-inductive annotation `x ≤ 2` of result 7 is not `k`-inductive for any `k` either
(`ToyHoare/Witnesses.lean`):

```lean
-- lean/ToyHoare/Witnesses.lean:295-300
theorem ncInv_not_k_inductive (k : Nat) :
    ∃ x₀ : Int,
      (∀ i : Nat, i < k →
        ncInv (st2 (x₀ + 2 * i) 0) ∧ ncGuard.eval (st2 (x₀ + 2 * i) 0) = true ∧
        Exec ncBody (st2 (x₀ + 2 * i) 0) (st2 (x₀ + 2 * ((i + 1 : Nat) : Int)) 0)) ∧
      ¬ ncInv (st2 (x₀ + 2 * k) 0)
```

(For every `k` there is a run of `k` iterations, starting at the unreachable `x = 3 - 2k`, through
stores satisfying the annotation and the guard, whose next store violates the annotation. This
covers runs along the stores `st2 _ 0`; it is not a general theory of `k`-induction.)

### Escape hatches for the impossibility results

Each of results 3, 4 and 9 concerns one fixed triple. The following single changes defeat the
impossibility; the mechanized ones are the positive controls displayed under **Findings**.

- **Assertion language.** Allowing semantic assertions: `exLoop_deriv_anyAssn`,
  `wlp_exLoop_anyAssn`, `vcgen_invsIn_hyp_tight` (mechanized). Allowing a parity or divisibility
  atom (as in SMT-LIB `QF_LIA` with `(_ divisible 2)`) or an existential quantifier would define
  "x even" and hence an inductive invariant (an argument, not mechanized: no such language is
  defined here).
- **Postcondition.** Weakening `x ≠ 1` to the linear `x ≤ 1` with the precondition kept:
  `exLoop_linDef_control_weak_post`, `vcgen_linDef_control_weak_post`, `wlp_exLoop_weak_post_linDef`
  (mechanized).
- **Precondition.** Replacing `x = y + y` by `x = 0` with the postcondition kept:
  `exLoop_linDef_control_pre_zero`, `vcgen_linDef_control_pre_zero` (mechanized). Note that for this
  precondition the `wlp` of result 4 is still not `LinDef`, so the derivation does not use the `wlp`
  (`wlpAdmissibleFor_not_necessary`).
- **Program text.** Instrumenting the loop with an auxiliary counter
  (`g := y; while 2 ≤ x do (x := x - 2; g := g - 1)`) and the invariant `x = g + g`:
  `exLoopGhost_linDef_control`, `vcgen_ghost_linDef_control` (mechanized).

For result 5 the escape hatches are the hypotheses themselves: off affine lines eventual constancy
fails (`eventually_const_needs_affine`), and an assertion that does not alternate beyond every bound
may be `LinDef` (`alternating_hyp_tight`).

### Attractive stronger conclusions that are not established

- That verification with linear invariants is incomplete for "most" or "typical" programs: only one
  triple and one program text are shown (results 3 and 9), and four single changes each restore
  provability.
- That `WlpAdmissibleFor L c Q`, or Cook's expressiveness, is necessary for deriving a particular
  triple in `Deriv L` (refuted by `wlpAdmissibleFor_not_necessary`; Bergstra and Tucker 1982 show
  expressiveness is not necessary for completeness in general).
- That `WlpAdmissibleFor` is the weakest sufficient command-local hypothesis (not claimed).
- That derivability in `Deriv LinDef` and verifiability by `vcgen` with `LinDef` annotations
  coincide (refuted for a loop-free program by
  `vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef`).
- That any real verifier, SMT solver or intermediate verification language behaves like `Deriv
  LinDef` or `vcgen`; this is only the modeling bridge stated under **Applicability**.
- That `TValid` would express guaranteed termination for a nondeterministic language, or that any
  total-correctness completeness theorem holds here (neither is formalized).

### Hypotheses with `unknown` tightness

None. Every hypothesis in every hypothesis ledger is `tight`, with a fully proved counterexample
named in **Findings**, except the arbitrary admissibility predicate `L` of result 1, which is
`harmless` (soundness holds for every `L`).

### Disproved or dropped statements

None. All 54 hashed statements of this package (listed under **Evidence**) are fully proved; no
statement was found false and none was removed.

### Not examined

Nondeterminism and concurrency; procedures, recursion and the heap; runtime errors, fixed-width
integers and overflow; a fully syntactic Hoare logic over `LAssn` (assignment by syntactic
substitution); assertion languages with divisibility predicates or quantifiers; decidability,
quantifier elimination and proof search; VC size and sharing; unstructured programs; completeness
of the total-correctness system; general well-founded variants; the behaviour of linear formulas as
`n → -∞` beyond the one example in `lassn_eventually_const_one_sided`.

## Evidence

### Kernel-check record

Toolchain: Lean `leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`
(the commit of the GitHub tag `v4.34.1` of `leanprover/lean4`, and the commit reported by
`lean --version` for the toolchain used), core library only. Observed 2026-11-20: a fresh build of
`lean/` with Lake's artifact cache disabled succeeded with no `sorry` warnings, and the audit
program found 682 non-internal declarations in the `ToyHoare` library, every one depending on at
most the axioms `propext`, `Classical.choice`, `Quot.sound` (full list: `audit/axioms.json`). No
Lean source contains `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations,
`implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`.

Statement hash = SHA-256 of Lean's `repr` of the theorem's type. Closure hash = SHA-256 of the
sorted lines `name : repr(type)` (plus ` := repr(value)` for non-theorem constants) of every
`ToyHoare` constant reachable from the type, joined by newlines; the closure size is the number
of such constants. Any change to a statement or to a definition it depends on changes these
hashes. The values below are those recorded in `audit/statements.json`.

Roles: `R<i>` is result *i* of **Findings**.

| Theorem | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `hoare_sound` | R1 result | none | `cfabd716cdb43ef264b64acd87a6ae80601e28b3e61c0db0e3852da7b7590538` | `236ef2ec644c603cf64176b88169564f78fe991b0e7f4218791ff6cc4032f584` (56) |
| `hoare_relatively_complete_of_wlpAdmissibleFor` | R2 result | none | `3a5d28d415f05eedde8e89c18d61c446a169375f4966d140fa30551afa3332f3` | `308ae0149a5155eb2a5acf3138a5e274449ec4052be9fe4faa334ce705fa0076` (66) |
| `valid_iff_deriv_wlpInvented` | R2 result | none | `cb60f16ef236430664b3435800ddd191e6cdc931adbbec2415fd206861c965c6` | `0cf7a42eb6e410fb20e3257250cc81246c4b38433cc9496b6353fc8ed21d4dee` (65) |
| `deriv_wlp_of_wlpAdmissibleFor` | R2 result | none | `2d7d75690c0d3b12b49817ca48a109704c579c1b200248a40bcae4daad0972a3` | `07edbca42ccb35876a308ad0373e3c207d9cb3092b5b99ed77029544213c8458` (65) |
| `deriv_anyAssn_iff_valid` | R2 result | none | `11bfc2c9e2ae1bf3da4102cfe100f4a859f06dd33a5b3b09f915840bd2181a62` | `520ce4f161aebe6380dda7fef1240e5f516f6b2567f8859cffe6d449a143a45e` (57) |
| `linear_qf_hoare_incomplete` | R3 result | `Classical.choice`, `Quot.sound`, `propext` | `e7b79314d19fd7cdadabde4a2143feff2b8443ba6e6310552fb0154b504c6a5c` | `02fd5e3ab2ec82fe60fb4b1f9afb87f8c9a80330fea36ca7891c668f875b087e` (91) |
| `exLoop_no_linDef_invariant` | R3 result | `Classical.choice`, `Quot.sound`, `propext` | `c16921666333c15ba5c22099aa970a70aec7c2e35fa097ac26d439f7e7230793` | `ab89ed48baf69f706f2301f417a98b524c4db58fb2de1f7d3ce61ee56e20c6f1` (83) |
| `linear_qf_not_expressive_wlp_exLoop` | R4 result | `Classical.choice`, `Quot.sound`, `propext` | `23d9dedb0fcd5edaba388f89803ad552928a97c53f442d235d229daa14486b1d` | `37cceb912b00c6cd8baee5f0fb07dd848a2b9f74a7d9c858a10054c4214d1a34` (83) |
| `wlp_exLoop_st2_iff` | R4 result; R4 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `4e80823924e26dd8ec953e0c48d9aec340ec5984f53fd2d831f34f1470741aa4` | `5673ef44addb08005775f862200fa91b84f3711cbba98205db405be5fc01a75b` (54) |
| `LAssn.eventually_const_on_affineLine` | R5 result | `Classical.choice`, `Quot.sound`, `propext` | `7ea0027621a0060cfe6728b9d6d60290de4c40586e2416a94705108a25df2c95` | `99e85f950b99382236a2f918d82b24263ca59223f205b29248ddb42a8d452ddf` (31) |
| `not_linDef_of_alternating_on_affineLine` | R5 result | `Classical.choice`, `Quot.sound`, `propext` | `ef87b02b2b8187353ae7fcdc4acb630bc949b313939846d3f3f9e39655652266` | `a51ac53a01e4182ac4751a6cf9040a5152578ec05bf19e94d83a6c8e99ef40c9` (33) |
| `parity_not_linDef` | R5 result | `Classical.choice`, `Quot.sound`, `propext` | `304e02f079f89ef2a5a9f8169a5cdccabe66e28a5bb25c82a92f276e88bef6a6` | `7cfc77bbd2d67c30d1452e8089a4e9d179a57115100bdd7ee1c45aeafd20ab08` (32) |
| `vcgen_sound` | R6 result | `Quot.sound`, `propext` | `8f43ccd167bf72bce471210ce76b4968ea20aa9578c6e0c65eaf625bb22a5916` | `442ea5b3956eb33bb9e6389799d40ce4993115cebfa1b6bb6cb1ec51009110da` (67) |
| `vcgen_reachable_noninductive_annotation_fails` | R7 result; R7 non-vacuity | `Quot.sound`, `propext` | `2ef75b0c5406e499ded57c16eec8e24038471f24e034eb64e1cb16cb52e98c51` | `7c4134a8e17e01975778fb1088af7984b2fcaf477f5de98a6ace841638960c03` (77) |
| `valid_iff_vcs_annotWlp` | R8 result | `Quot.sound`, `propext` | `26c5099adbb7fe35311f732e138e7a015a260a68968672e869932a246a117479` | `deb4fae58a44fa75bab55f3dcabef72d838dec13860ca306186a2b8f208504bc` (73) |
| `vcgen_annotWlp` | R8 result | `Quot.sound`, `propext` | `821204433b772276def12ccc4818abfbaf280ceb6c18748fd4d7154ce0ab865d` | `9f7568e8cd7e1663888f24473a39e2498325fce65c96a67ed35b7e470d50570e` (72) |
| `erase_annotWlp` | R8 result | `propext` | `c78d181c7b6911b3be6e6a600ab13e512535c40ee668457eabe18ca86202b186` | `6581e0db5e9f74a91ce8e0e8ad47356e135c454cc14f103856829aa3c97e08e7` (71) |
| `vcgen_linear_qf_annotations_incomplete` | R8 counterexample; R9 result | `Classical.choice`, `Quot.sound`, `propext` | `1d1113fbb56ac5927872e3433d4436f0ee8c84e39ea8092faad615f8083a6849` | `dd251f4ea4be5e76e775eb09b8f1ae2b61f7bf29435706692368df45c2581fda` (104) |
| `total_sound_of_bounded_variant` | R10 result | `Classical.choice`, `Quot.sound`, `propext` | `7de4bd16b50983ead6e91bbc55116f8d08a53b135e048ebf4454e3fe850e68aa` | `04344132cb0f7ee3b74f8ef40f940f9fd09001909a89121ce7d43bc2e653234e` (56) |
| `unbounded_variant_unsound` | R10 counterexample; R11 result; R11 non-vacuity | `Quot.sound`, `propext` | `e293acaa943f21101a1d45e67206049240774df8be0d865b98392da55485f1f6` | `4e53e184af6c8b429b6c63ec7a25efc353909fe604172255556b6fb45e41518e` (58) |
| `alternating_hyp_tight` | R5 counterexample | `Quot.sound`, `propext` | `8127d2f54057c3cb054b7a062e84fb026bd2caed1a471ffcd97fd4a3fe2ab29a` | `cb95e2977fc39f57a02235033b1f633639684906055a0db8bd0119d5c5131266` (35) |
| `alternating_needs_affine` | R5 counterexample | `Quot.sound`, `propext` | `a0f0eb979720966bd29e19d0e34d824cee2431e1f58d6732053620eb6ce3518a` | `7cfc77bbd2d67c30d1452e8089a4e9d179a57115100bdd7ee1c45aeafd20ab08` (32) |
| `deriv_wlp_needs_admissible` | R2 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `5ed99cd40e2e44f77b12b13e13b9f4366b511b7f3fa2548feaab5273694d2cdf` | `a449c087cb0b125ef02fd2676782a7e7f9e3c8845ba0d39717a38632ce27dc40` (99) |
| `eventually_const_needs_affine` | R5 counterexample | `Quot.sound`, `propext` | `658afaa0135b30796d813c0abb2eb27903680b8b7fd57482b07b7cfdb15fd096` | `01c91328d5a614ee93da75983623eedbe8da993f233f5648d842c26e5cfc4895` (30) |
| `exLoopGhost_linDef_control` | R3 positive control; R3 counterexample | `Quot.sound`, `propext` | `0928de60da767b20bff05152531de8eefb043c9ea8e111a9635dd6f6a1a86d0b` | `b1b3be9c47dbe8aced7697de37af7a65b94b957afb57cf23e0536c8dc7a08684` (91) |
| `exLoop_deriv_anyAssn` | R3 positive control; R3 counterexample | `Quot.sound`, `propext` | `2016d2b3c5d5cbd98962eb3af8e2858f242d1ed2ebd82378c9b2f9b22d72942c` | `c6aab4a30b2e7417bedabaac54643aa31d4a0bb8cf7dc3a90908cd6a039c098a` (53) |
| `exLoop_linDef_control_pre_zero` | R3 positive control; R3 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `14a9f3725aa21f8586fa8360611913bdbe11d3ef560cfdf11b0c209a52e785ff` | `09ff1d9fbaadff0ab1fa886d6a1e8ae3dbc55c3d25f3a72c4b29e36468992f9e` (90) |
| `exLoop_linDef_control_weak_post` | R3 positive control; R3 counterexample | `Quot.sound`, `propext` | `18ae8df31e70a1d0b708a82284267bf2fe3c0e754c82b84bf2903ab860697f0c` | `33bad6565b9020f78cc13a8477346fc0f8550f0b7fe49eb6b2f25443f2e9879a` (91) |
| `exLoop_valid` | R3 non-vacuity | `Quot.sound`, `propext` | `336f2998e7a5e4e167b8ec0c6ca15028368e4100ffbcec49feb857bd93a4a9fc` | `5364ea30b4e67e9dc1b39b1f20e64b1ab85c469f8a1b570860adf8e52954854e` (54) |
| `exPost_linDef` | R3 non-vacuity | `propext` | `7c640c1c6fff143ecbbfb9bd0d8e6a22232c08c29431d90d4ab71e78c0961cea` | `6e96444abf423e6e0cb6584f1154d6157e5ff2eb7117c9bbfef5f6a8b012426e` (33) |
| `exPre_linDef` | R3 non-vacuity | `propext` | `57504b4f521fcbbaacfa278762b151ddc7bb6d336287b45a3df33efbb75f8221` | `a2616ad7d08680d38c69f2c6e8e60613f35018f157f4706ea8ca53848ead9564` (33) |
| `hoare_sound_deriv_tight` | R1 counterexample | `propext` | `e98aa83f0220e0213aab5232e7ecd52c31ea59a52e5fa82253d1485d0b17cb43` | `236ef2ec644c603cf64176b88169564f78fe991b0e7f4218791ff6cc4032f584` (56) |
| `ncAnnLin_verifies` | R7 positive control | `Quot.sound`, `propext` | `704f457839e986ea21ced880c6dc1257a43b2406eb4a394fc40c4e10da7294d8` | `c46a19e97811246b3cfbe5984e7f99fa1bcc14ba25f8c10d059e54e6b3a76407` (96) |
| `nonvacuity_eventually_const_and_alternating` | R5 non-vacuity | `Quot.sound`, `propext` | `86c828cd5e64b3a2a25b401d2ca9dbaf566b72da40a543f0ef27428b7eb9925b` | `1da4f8f410fd1d5bdffd5b65cf33635e9594bbffaa0b9eac65022dd23597aca6` (5) |
| `nonvacuity_hoare_sound` | R1 non-vacuity | `Quot.sound`, `propext` | `2151d57ebdd2cb7e4068d80db2bbced8f4aa7142263e410649ceeda755e65c09` | `fc11874cdc940d479422238636cefee0f4c356e5be45f3ebea58a85d6356edd7` (84) |
| `nonvacuity_relcomp` | R2 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `9254ad18fe2c32f1d99b9d9892ec9122c7dc897d52b6b5166bb42bc62c065545` | `005dede620da048194f781b2b14e74744f2c2e70fbddd152014006475e4ad7e7` (96) |
| `nonvacuity_semantic_iff` | R2 non-vacuity | `Quot.sound`, `propext` | `8c1510aa8eadb95f480f2401570e4a3143ab7833045fc1fb1269616b5450f761` | `aaa5c0f0a8fe4c51457c455f835cb7420de851a79b32708416eb18c81c8e5ea9` (71) |
| `nonvacuity_total_sound` | R10 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `ceaccb516b0bbc14215cdbeb4eead5cf0f94f60c852599de128be11b7dd81ed0` | `f969dce6030e301359328fe1c6cbdf37574fb73696ada3838f248481fc8ddf77` (48) |
| `nonvacuity_vcgen_linear_qf_incomplete` | R9 non-vacuity | `Quot.sound`, `propext` | `740b85ba52bee06c4945311e76e2bbce8dd26275161e56c89a6cc643e0976799` | `1016d1e52357cc69d0567e038fc4af0f997d9bf1d175e221106327d2f6f20463` (101) |
| `nonvacuity_vcgen_sound` | R6 non-vacuity | `Quot.sound`, `propext` | `45a9594fad502c7e989e3f1aaceae5b152bec299d870780dcd5164cf266f3a19` | `302ca63a0c395fe8ee9e1810cae677e97de0732411aaeafd4ce6f415f9806d5b` (54) |
| `nonvacuity_vcs_annotWlp` | R8 non-vacuity | `Quot.sound`, `propext` | `903e4661e14f40ea189196a23dd8d82c7515bc3e14c95de545aacb9e7364ef97` | `8fc8c6bc800e9cb76cdb32dd1b445309d09c68298c16880761eea1bc82925482` (77) |
| `nonvacuity_wlp_exLoop_nontrivial` | R4 non-vacuity | `Quot.sound`, `propext` | `920f819987b5f71f42f105da2dd05daf12ee0a2f77d2684081c8eb22ea9501a0` | `508429a9ae28c710c9f1aee90ef66ff12b370e49e006588f2b68ff344ab3a711` (55) |
| `relcomp_valid_tight` | R2 counterexample | `propext` | `90bea0030cc6a10639b11e7f23a87b7e8cf17a3605a40cffb96c76e99b49bc62` | `8594ab8f73f614a74d9537c19c9f702cf93322b379af168091b086c1653b216a` (67) |
| `relcomp_wlp_admissible_tight` | R2 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `21bd091cbb5969a324cee39e2fa580afbe12f9929c7b199119237d8b9477221b` | `fd9d8d709f63973d99fec35e1b884bd9b736ba610f65b03a5b0fda6e68e29f76` (101) |
| `semantic_iff_needs_anyAssn` | R2 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `a2ea5ecb50ef491a4d27bd054f01c622b982837fd63d53e995a3e287fa351b93` | `02fd5e3ab2ec82fe60fb4b1f9afb87f8c9a80330fea36ca7891c668f875b087e` (91) |
| `vcgen_erase_hyp_tight` | R9 counterexample | `Quot.sound`, `propext` | `0bbe9e77174f44817547f6505c35466f3a59d3dbddec3bee46f9a83bd4402161` | `7d1b6da0f143ce9f133b7c827c3c8964da1e9ffa9d45f003b0e249f0bbc670fb` (95) |
| `vcgen_ghost_linDef_control` | R9 positive control; R9 counterexample | `Quot.sound`, `propext` | `f6b4a24ae45deade950b68615494754bb859799dc7c49e2449e71685719d1cc7` | `6e6b8f0ab6bd9e46cedcea6d90618e7f7f4b8fdff4c0433525e5b392310b2270` (97) |
| `vcgen_invsIn_hyp_tight` | R9 positive control; R9 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `405bfb7598e40317b612da1f4bbf23ee41aa773665fa8203d06982d87218df0e` | `78c3a122baa0696b1c6d6e6aea4c3d0cafb804d66515dafd7147ef99a119d841` (97) |
| `vcgen_linDef_control_pre_zero` | R9 positive control; R9 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `c2c4131df2321d3194b83e1847429048488c4f4944e7e1415a60594fafd55dfa` | `fc9baecd70c3289b58687ed9b8616b0c61d803cddaa6e8bd918f0037bb259d2e` (95) |
| `vcgen_linDef_control_weak_post` | R9 positive control; R9 counterexample | `Quot.sound`, `propext` | `0085fe172876e32be7b9fe430d5dc97d3b7a04b6ce8981173b08bf04cc2dcf93` | `5f22479a7a9a621f532b30f00acac316f3e4eb126eb5f8cab991f5455028403e` (96) |
| `vcgen_sound_pre_tight` | R6 counterexample | `Quot.sound`, `propext` | `b5395aac117a7a9bd54a26019deaf2af7caaf823ff9bd7be52beb5419ab7870f` | `442ea5b3956eb33bb9e6389799d40ce4993115cebfa1b6bb6cb1ec51009110da` (67) |
| `vcgen_sound_vcs_tight` | R6 counterexample | none | `44277166c3bf326918e7da4d042d33d89fa3afe8145a3bcc84f2b54f7a7dbe66` | `3cd4bedf1156a82101fdb31dc093c5fa56a9169a0dc47d9088351b243a215a82` (67) |
| `wlp_exLoop_anyAssn` | R4 positive control; R4 counterexample | none | `e60e77aaf9317786822bfd22bd1c089165f488f44a7eabd646ad2c9373872742` | `4caaf2fdbfb67e37df46b2f4d064d09405665491fb03dc4ebfe8edb0ee1a8d48` (54) |
| `wlp_exLoop_weak_post_linDef` | R4 positive control; R4 counterexample | `Quot.sound`, `propext` | `47f6fee56a749617e998b295adc84be6086ec82e5e49cfd5b175847088881b76` | `8464cc82d337a39e369848c078e5c952c1e6ffc6b82ea60e1b5c2cbc9f53bedd` (83) |

All names are in the namespace `Toy.Hoare` (prefix omitted).

### Boundary and bridge theorems

These eight theorems are quoted under **Boundaries**. They are not referenced by any field of
`results.json` and therefore are not in `audit/statements.json`; their hashes below were computed
by `lean/RevalidationAudit.lean` with the same algorithm and are reproducible with the commands
under **Revalidation**.

| Theorem | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- |
| `lassn_eventually_const_one_sided` | `Quot.sound`, `propext` | `341082b8f69e759a4283e777df02321311f120c7ab7e3c194cf2cb29f3966cc3` | `8e094ac80bda650dfa3fedf6d0a6ee8bd73295fe5376bc7dac5ea908109fe275` (31) |
| `linDef_forall_wlp_iff_tautology` | `Classical.choice`, `Quot.sound`, `propext` | `e07e75f9538b3d61b00508bb157892ee690eb3aa047f7a26cfcf7bff65624142` | `1f3502f939e7d33a2f6715c79a13c3ef935f52b7236520a243437275ca93cd94` (79) |
| `ncInv_not_k_inductive` | `Quot.sound`, `propext` | `ee23b45ca9b649464fbcd6062be35d117ee0aecc90d3e17fdff34f5d12a9bde8` | `b1d3a5a3e53d20f837c01b19b9e965fd2f0f03d470ed6f101b90fb3533fb43dc` (52) |
| `vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef` | `Classical.choice`, `Quot.sound`, `propext` | `c82c266ddbd0d56a2812a7a9b7a72d1eb40e61028ec284398fa6f3c36a5575b7` | `d86e3170c4d9dcb9899133de76a5a483c11b1853e18524d5fb14ba2d20fd7704` (99) |
| `vcgen_side_conditions_ignore_branch_guards` | `Quot.sound`, `propext` | `fa027af9428be39b20e2756d45c14d35fc931e20dbc3bb56d31128255d9b6a42` | `c616a05259ec3d372384c905bd222ec40c34db9a6019a66b311cf40e474c26cd` (100) |
| `wlpAdmissibleFor_not_necessary` | `Classical.choice`, `Quot.sound`, `propext` | `bf71e9c73b78168bb7e361b14dc75fbdad9d2b4c89769e1c28da663cde46b51a` | `a449c087cb0b125ef02fd2676782a7e7f9e3c8845ba0d39717a38632ce27dc40` (99) |
| `wlpAdmissibleFor_of_expressive` | `Quot.sound`, `propext` | `d5342f0b856c2b446e6e27a9cef2cf9e50e9d4bdb45f2f89c483fe1aa782a62c` | `abf62113cac306e5c797b77771d4ec8963d25951e9a28f04d91777f822041d9b` (58) |
| `wlpAdmissibleFor_of_forall_wlp` | `Quot.sound`, `propext` | `190bd3ba1cca64671ad8b5bc3b6b01f0faaa6042398aeb0e4b54b6f8ded995bc` | `abf62113cac306e5c797b77771d4ec8963d25951e9a28f04d91777f822041d9b` (58) |

### Primary sources

Bibliographic records, one bullet per work (from the `prior_art` fields of `results.json`; where
several results cite different aspects of the same work, their descriptions are joined under that
work's single bullet). The
DOIs were checked against the Crossref registry records; on 2026-11-20 the bibliographic data of
Cook (1978), Wand (1978) and Bergstra and Tucker (1982) were re-confirmed, and the files
`src/HOL/IMP/Hoare_Total.thy` of `isabelle-prover/mirror-isabelle` at
`20d6a3f7ffbaaa82e77f341d90db5070b3428fbe`, `lean/LoVe/LoVe10_HoareLogic_Demo.lean` of
`lean-forward/logical_verification_2025` at `76421700cb010aeddeb2b2a4a93e538b92b0e585`, and
`totalhoarelogic.v` of `rocq-community/hoare-tut` at `66dfb255c9e8bb49269d83b3577b285288f39928`
were re-confirmed to exist at those revisions. Also on 2026-11-20, the DOIs of Hoare and Lauer
(1974), Nipkow (1998) and Ginsburg and Spanier (1966) were confirmed as registered at the DOI
handle registry (doi.org), and the publisher pages for these DOIs (Springer Link for the first two,
Mathematical Sciences Publishers for the third) show the cited titles, authors, volumes and pages;
commit `66dfb255c9e8bb49269d83b3577b285288f39928` of `rocq-community/hoare-tut` was confirmed to
contain `partialhoarelogic.v` and `totalhoarelogic.v`. Descriptions of the content of
access-controlled publications rest on their abstracts and secondary summaries; the Isabelle,
Rocq and Lean sources and the Software Foundations chapters were read directly.

- A. Baanen, A. Bentkamp, J. Blanchette, X. Généreux, J. Hölzl and J. Limperg, The Hitchhiker's Guide to Logical Verification (2025 edition), Lean 4 sources in repository lean-forward/logical_verification_2025, commit 76421700cb010aeddeb2b2a4a93e538b92b0e585: lean/LoVe/LoVe10_HoareLogic_Demo.lean (PartialHoare as a semantic triple, rule lemmas, and a vcg tactic for loops annotated with invariants via Stmt.invWhileDo) and lean/LoVe/LoVe10_HoareLogic_ExerciseSheet.lean (TotalHoare with Nat-valued variants, posed as exercises).
- B. C. Pierce et al., Software Foundations, volume 2: Programming Language Foundations, version 7.1 (2026-08-24), Rocq. (a) Semantic (shallow-embedded) assertions over natural-number variables. Chapter Hoare proves the individual rules valid (hoare_skip, hoare_asgn, hoare_seq, hoare_consequence, ...); chapter HoareAsLogic defines an inductive derivability judgement and wp, and poses both hoare_sound and hoare_complete as exercises whose proofs are left Admitted (it states no derivable-iff-valid theorem). (b) Chapter Hoare2: fully decorated programs (an assertion after every command) whose local verification conditions are proved sound (Theorem verification_correct); there is no completeness theorem, and decorations are not loop-only annotations with backward precondition computation as here. (c) Chapter Hoare2, example "Parity" (credited there to Daniel Cristofani): the same loop while 2 <= X do X := X - 2, over natural numbers, verified with the semantic invariant parity X = parity m.
- C. A. R. Hoare and P. E. Lauer, "Consistent and complementary formal theories of the semantics of programming languages", Acta Informatica 3(2):135-153, 1974, doi:10.1007/BF00264034. Shows an axiomatic definition of a simple language consistent with an interpretive (operational) one, i.e. semantic soundness of Hoare-style rules.
- C. A. R. Hoare, "An axiomatic basis for computer programming", Communications of the ACM 12(10):576-580, 583, October 1969, doi:10.1145/363235.363259. Introduces the triple notation, the assignment axiom and the rules of consequence, composition and iteration for structured programs; it defines no operational semantics and proves no soundness theorem.
- C. Flanagan and J. B. Saxe, "Avoiding exponential explosion: generating compact verification conditions", POPL 2001, pp. 193-205, doi:10.1145/360204.360220. VC generation for guarded commands with attention to VC size; size is not addressed here.
- D. Marker, Model Theory: An Introduction, Graduate Texts in Mathematics 217, Springer, 2002, doi:10.1007/b98860; section 3.1: Presburger arithmetic admits quantifier elimination only after adding divisibility (congruence) predicates, since quantifier-free formulas of ordered additive groups cannot express properties such as "x is even".
- G. Winskel, The Formal Semantics of Programming Languages: An Introduction, MIT Press, 1993, chapter 7 "Completeness of the Hoare rules" (7.2 Weakest preconditions and expressiveness; 7.4 Verification conditions). Relative completeness for IMP via weakest preconditions expressed in a first-order arithmetic assertion language.
- J. A. Bergstra and J. V. Tucker, "Expressiveness and the completeness of Hoare's logic", Journal of Computer and System Sciences 25(3):267-284, 1982, doi:10.1016/0022-0000(82)90013-7. Shows that Cook's expressiveness condition is sufficient but not necessary for completeness of Hoare's logic over a first-order structure: there are non-expressive structures whose Hoare logic is complete.
- K. R. Apt, "Ten years of Hoare's logic: a survey - part I", ACM Transactions on Programming Languages and Systems 3(4):431-483, October 1981, doi:10.1145/357146.357150. Survey of soundness, relative completeness and expressiveness for while programs. Section 2.8 treats total correctness of while programs with a while rule based on an integer-valued termination function that is bounded below by 0 and decreases with each iteration.
- M. Barnett and K. R. M. Leino, "Weakest-precondition of unstructured programs", PASTE 2005, pp. 82-87, doi:10.1145/1108792.1108813. Weakest-precondition VC generation for unstructured programs; not addressed here.
- M. Wand, "A new incompleteness result for Hoare's system", Journal of the ACM 25(1):168-175, 1978, doi:10.1145/322047.322062. Exhibits a first-order structure for which Hoare's system for while programs is incomplete because the needed invariants are not expressible in the assertion language; the structure and language differ from the ones used here.
- N. Schirmer, "A Sequential Imperative Programming Language Syntax, Semantics, Hoare Logics and Verification Environment", Archive of Formal Proofs, February 2008, https://www.isa-afp.org/entries/Simpl.html. Isabelle/HOL; Hoare logics for partial and total correctness proved sound and complete for a language with procedures, abrupt termination, heap and unbounded nondeterminism, with an integrated verification environment.
- R. W. Floyd, "Assigning meanings to programs", in Mathematical Aspects of Computer Science, Proceedings of Symposia in Applied Mathematics 19, American Mathematical Society, 1967, pp. 19-32, doi:10.1090/psapm/019/0235771. Inductive assertions attached to flowcharts, verification conditions along control-flow paths, and termination by decreasing functions into a well-founded set.
- S. A. Cook, "Soundness and completeness of an axiom system for program verification", SIAM Journal on Computing 7(1):70-90, 1978, doi:10.1137/0207005. Soundness and relative completeness of a Hoare system for an ALGOL-like language, relative to an expressive assertion language and an oracle for true assertions.
- S. Boulmé, "hoare-tut" (tutorial on Hoare logic, Rocq), repository rocq-community/hoare-tut, commit 66dfb255c9e8bb49269d83b3577b285288f39928: partialhoarelogic.v and totalhoarelogic.v prove soundness and completeness (Theorem soundness, Theorem completeness) of a syntactically defined weakest-precondition generator synt_wp with respect to semantic triples; in partial correctness the loop case uses wlp (Iwhile cond p) post, in total correctness a well-founded variant.
- S. Ginsburg and E. H. Spanier, "Semigroups, Presburger formulas, and languages", Pacific Journal of Mathematics 16(2):285-296, 1966, doi:10.2140/pjm.1966.16.285. Characterizes the sets definable in Presburger arithmetic as the semilinear sets.
- S. Igarashi, R. L. London and D. C. Luckham, "Automatic program verification I: A logical basis and its implementation", Acta Informatica 4(2):145-182, 1975, doi:10.1007/BF00288746. Logical basis of an early verification-condition generator for programs annotated with loop invariants.
- T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL, Springer, 2014, doi:10.1007/978-3-319-10542-0; (a) chapter 12 "Hoare Logic" (doi:10.1007/978-3-319-10542-0_12). Mechanized in the Isabelle sources src/HOL/IMP/Hoare_Sound_Complete.thy (hoare_sound; hoare_complete via wp over semantic assertions; corollary hoare_sound_complete, derivable iff valid) and src/HOL/IMP/VCG.thy (vc_sound; vc_complete: from a derivation of {P}c{Q} there exists an annotation C with strip C = c, vc C Q and P implying pre C Q; side conditions are checked in every state), repository isabelle-prover/mirror-isabelle at commit 20d6a3f7ffbaaa82e77f341d90db5070b3428fbe. (b) Section 12.5 "Hoare Logic for Total Correctness" of the same chapter. Mechanized in src/HOL/IMP/Hoare_Total.thy (same repository and commit): hoaret_sound, hoaret_complete and corollary hoaret_sound_complete, for a While rule whose termination measure is a natural-number-valued relation T :: state => nat => bool (functional form While_fun with f :: state => nat), so the lower bound is built into the type nat; total validity uses an existential over final states, and the theory notes that this definition only works because execution is deterministic. No counterexample with an unbounded integer variant is formalized there.
- T. Nipkow, "Winskel is (almost) right: Towards a mechanized semantics textbook", Formal Aspects of Computing 10(2):171-186, 1998, doi:10.1007/s001650050009. Isabelle/HOL mechanization of semantics material from Winskel's textbook, including Hoare logic for IMP.
- Z. Manna and A. Pnueli, "Axiomatic approach to total correctness of programs", Acta Informatica 3(3):243-263, 1974, doi:10.1007/BF00288637. Hoare-style proof rules for total correctness.

## Revalidation

Requirements: `elan` (so that `lake` and `lean` use the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No other dependency is needed; the Lean project has no
Lake dependencies.

**Primary check** (from the package directory):

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and
then (1) runs `lake build`; (2) scans every Lean source for `sorry`, `admit`, `native_decide` and
`axiom` declarations; (3) runs an audit program that lists every declaration of the `ToyHoare`
library with the axioms it depends on (Lean's `collectAxioms`) and fails if any axiom other than
`propext`, `Classical.choice`, `Quot.sound` occurs; (4) for every Lean name referenced by
`results.json` (fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean` and hypothesis
`counterexample`s) and every name in `audit/statements.json`, recomputes the statement hash
(SHA-256 of `repr` of the type) and the definition-closure hash (SHA-256 of the sorted lines
`name : repr(type)`, plus ` := repr(value)` for non-theorem constants, of every `ToyHoare` constant
reachable from the type, joined by newlines) and compares them with `audit/statements.json`. It
prints `REVALIDATED` and exits with status 0 iff all checks pass. If Lake's shared artifact cache
is enabled in your environment, set `LAKE_ARTIFACT_CACHE=false` so that every proof is
re-elaborated rather than restored from the cache.

**Manual check with the included audit program** (also covers the eight boundary and bridge
theorems, whose hashes are listed under **Evidence**):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/hoare-revalidation.txt
cd ..
python3 - <<'EOF'
import hashlib, json, re
txt = open('/tmp/hoare-revalidation.txt').read()
audit = json.loads(re.search(r'REVALIDATION_AUDIT_JSON (\{.*\})', txt).group(1))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [d['name'] for d in audit['decls'] if set(d['axioms']) - allowed]
print('declarations:', len(audit['decls']), 'with other axioms:', bad)
recorded = json.load(open('audit/statements.json'))['statements']
for s in audit['stmts']:
    assert not s.get('missing'), s['name']
    h = {'statement_sha256': hashlib.sha256(s['type_repr'].encode()).hexdigest(),
         'closure_sha256': hashlib.sha256('\n'.join(s['closure']).encode()).hexdigest(),
         'closure_size': len(s['closure'])}
    rec = recorded.get(s['name'])
    status = 'boundary (compare with Evidence)' if rec is None else ('ok' if rec == h else 'MISMATCH')
    print(status, s['name'], h['statement_sha256'], h['closure_sha256'], h['closure_size'])
EOF
```

`lean/RevalidationAudit.lean` is outside the library target (it is not built by `lake build`); it
imports `ToyHoare`, prints one line `REVALIDATION_AUDIT_JSON {...}` with the axioms of every
library declaration and the type and closure text of the 54 card-referenced names and the eight
boundary and bridge theorems, and its header comment describes exactly what is printed. Expected
output: 682 declarations, none with other axioms, 54 lines `ok`, and 8 `boundary` lines whose
hashes equal the *Boundary and bridge theorems* table under **Evidence**.

**What a passing run establishes.** The Lean kernel of the pinned toolchain accepts every proof,
only the three standard axioms are used, and the theorem statements and the definitions they depend
on are exactly those recorded here. It does not re-check the prose of this report, the prior-art
descriptions, or the modeling bridge under **Applicability**. A change of toolchain may change
`repr` output and hence the hashes without any change in meaning; in that case compare the
statements with the ones quoted under **Findings** and **Boundaries**.
