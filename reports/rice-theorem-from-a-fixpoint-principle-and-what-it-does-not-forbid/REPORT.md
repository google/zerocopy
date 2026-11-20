# Rice's theorem from a fixpoint principle, and what it does not forbid

## Summary

This package states and kernel-checks, in Lean 4 without Mathlib, an abstract form of Rice's theorem in which Kleene's recursion theorem is an assumption (the *fixpoint principle*) about an abstract programming system, together with the diagonal arguments that produce such fixpoint principles and a set of toy systems that mark exactly which checker designs the theorem rules out and which it leaves open. Every result is a kernel-checked theorem (`execution (Lean kernel check)`); every claim connecting a result to a real programming language is stated separately and labeled `derived (modeling bridge)`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Design question.** Arguments about automated checkers often appeal to Rice's theorem, sometimes too broadly. Exactly which checker designs does a Rice-style argument rule out, under which hypotheses about the programming system, and which designs remain possible (sound-but-incomplete checkers, syntactic checks, checkers for total sublanguages, checkers for restricted fragments)?

**Retain this distinction.** The decision impossibilities (R1, R2, R4, R6, and the concrete N2) rule out only *internal deciders*: total two-sided Boolean checkers that decide an *extensional* (behavioural) predicate and all of whose switches `c ↦ if chk c then a else b` are admissible transformers of a system that has the fixpoint principle (for R6: of the restricted system, when the full system can test code equality). W5, W6 and W7 do not forbid any checker; they constrain how the verdicts of a switch-admissible checker split across codes with the same behaviour. None of these results forbids partial or one-sided (semi-decision-style) procedures (W8), checkers for decidable fragments or total sublanguages (N1, W4; R6 gives the condition under which restricting does not help), sound but incomplete checkers (W1, W2; W5 describes their unavoidable incompleteness), syntactic checks (W3), or certificate checking.

**Two notions of deciding.** *Decided inside* (`DecidedInside`) is this package's internal notion: some Boolean checker decides the predicate and every switch on that checker is admissible. *Not decided inside* never means *no Boolean function decides it*: `Decides` carries no effectiveness, and for example `Toy.Rice.Flat.haltCheck` decides halting on the flat domain (`Toy.Rice.Flat.haltCheck_decides`) although halting is not decided inside that system (N2). The unqualified words *decidable* and *undecidable* refer only to classical computability (decidable by a total computable procedure); they occur only in modeling bridges, prior-art descriptions and commentary, and no theorem here states that anything is classically decidable or undecidable. *Checkers for decidable fragments* means checkers that decide a property inside a restricted system (N1, W4).

**Concrete results are existence statements.** N1, N2, N3, W2, W3, W4 and W8 are closed statements about one named toy system each. Each shows that a system with the stated combination of properties exists (the named one); none says that every system of that kind, or any real language, has those properties.

One sentence per result (plain claims, with their key hypotheses):

- **R1.** In any programming system satisfying the fixpoint principle (every admissible transformer f has a code c with sem (f c) = sem c), no nontrivial extensional predicate P on codes is decided inside the system: there is no checker that decides P and all of whose switches c ↦ if chk c then a else b are admissible.
- **R2.** In a system with the fixpoint principle, if chk decides an extensional predicate P, a satisfies P and b violates P, then the swapped switch c ↦ if chk c then b else a is not admissible.
- **R4.** In a system with the fixpoint principle whose admissible class contains every constant transformer, an extensional predicate is decided inside the system if and only if it holds of every code or of no code.
- **R6.** Let S have the fixpoint principle, let its admissible transformers be closed under literal code-equality tests (for admissible f and codes k, a, b, the transformer c ↦ if f c = k then a else b is admissible), and let F be a fragment of codes closed under same behaviour. Then no predicate that is extensional and nontrivial on F is decided inside the restricted system S.restrict F, whose admissible transformers are the fragment maps that agree literally on F with some admissible transformer of S.
- **F1.** Let φ : A → A → Y represent every map in a class G (each g in G equals φ a pointwise for some a), and let t : Y → Y be such that the diagonal map x ↦ t (φ x x) is in G. Then some a represents that diagonal map, and for every such a, φ a a is a fixed point of t.
- **F2.** For types and arbitrary functions, if φ : A → A → Y represents every map A → Y, then Y has exactly one element.
- **F3.** If every admissible transformer is computed by some code under a partial application app (Represents), d is a diagonal transformer (whenever app x x halts with output z, the code d x behaves like z), and precomposition with d preserves admissibility, then for every admissible f some code e computes f ∘ d, and for every such e the code d e is a semantic fixed point of f (sem (f (d e)) = sem (d e)). In particular the system has the fixpoint principle.
- **F4.** If a system has the fixpoint principle and every switch on every Boolean checker is admissible, then all codes have the same behaviour; consequently, when every transformer is admissible and the code type is nonempty, the fixpoint principle holds exactly when the semantics is constant.
- **N1.** In the lookup-table system (codes: finite tables; behaviours: total functions ℕ → ℕ; admissible transformers: those expressible in the total language TProg of constant tables, identity, two table edits, composition, and conditionals on the tests of a small test language TTest), the fixpoint principle fails and the nontrivial extensional predicate 'computes the zero function' is decided inside the system by zeroCheck, which is itself a TTest test.
- **N2.** In the flat-domain system (codes and behaviours are the three denotations 'diverges', 'returns true', 'returns false'; sem is the identity; admissible transformers are the monotone maps), the fixpoint principle holds, halting is extensional and nontrivial, and halting is not decided inside the system.
- **N3.** The system on ℕ with identity semantics whose admissible transformers are the constants and the shifts n ↦ n + k contains every constant, is closed under composition, and lacks the fixpoint principle, and yet decides no nontrivial predicate inside (every predicate is extensional here).
- **W1.** If every constant transformer is admissible, the checker that rejects every code is sound for every predicate and is switch-admissible.
- **W2.** In the padded system, which has the fixpoint principle, the predicate 'the behaviour is true' is extensional, nontrivial and not decided inside the system; yet the checker 'the code is a literal true program' is switch-admissible and sound for it, accepts the infinitely many codes lit true n, and rejects every hidden code hid true n although those satisfy the predicate.
- **W3.** In the padded system, which has the fixpoint principle, the nontrivial non-extensional predicate 'the padding is even' is decided inside the system by evenPadCheck.
- **W4.** In the lifted lookup-table system (codes: table programs plus one divergent program; admissible transformers: constants and strict extensions of TProg programs), which has the fixpoint principle and is not closed under literal code-equality tests, the halting fragment is closed under same behaviour, has a proper admissible class and no fixpoint principle, and decides inside it, by fragCheck (which runs zeroCheck on the underlying table), the property 'halts and computes the zero function', which is extensional and nontrivial on the fragment; in the full system that property is extensional, nontrivial and not decided inside.
- **W5.** In a system with the fixpoint principle, let chk be switch-admissible and sound for an extensional predicate P that some code violates. Then every realizable behaviour (the behaviour of some code) has a code that chk rejects: for every code a there is a code c with sem c = sem a and chk c = false. In particular every code satisfying P, and every accepted code, has a rejected code with the same behaviour.
- **W6.** In a system with the fixpoint principle, every switch-admissible checker chk has the following property: for any codes a and b, chk rejects some code with the behaviour of a or accepts some code with the behaviour of b. Consequently (and, classically, equivalently) no realizable behaviour (the behaviour of some code) has all its codes accepted while a realizable behaviour has all its codes rejected.
- **W7.** In a system with the fixpoint principle, a switch-admissible checker that is sound for an extensional predicate P, accepts some code and rejects some code gives different verdicts on two codes with the same behaviour, both satisfying P.
- **W8.** In the flat-domain system, which has the fixpoint principle, the one-sided switch 'if the program halts then return true, else diverge' is admissible, while halting is not decided inside the system.

**Non-claims first:** nothing about semi-decision (Rice-Shapiro is not formalized), nothing about time or space, nothing about properties of code text, nothing about randomized or approximate checkers, nothing about any real language unless its fixpoint principle is established, and "not decided inside" never means "no Boolean function decides it". The full non-claims, global and per result, are the first part of Boundaries.

## Applicability

**Model fidelity: this is a toy model.**

- **Abstract interface.** `System` consists of codes, behaviours, a semantics map, and a class `Adm` of admissible code transformers. All effectiveness assumptions live in `Adm`; nothing else mentions computability. Intended reading: `Code` = indices of an acceptable numbering, `Beh` = partial computable functions, `sem` = the numbering, `Adm` = total computable transformers. That reading is a modeling bridge (stated per result under Findings with the label `derived (modeling bridge)`), not a theorem here.
- **Concrete toy systems.** `Tables` (finite lookup tables; admissible = programs of a small total language `TProg` with conditionals on tests of a test language `TTest`); `Lifted` (tables plus one divergent code; admissible = constants and strict extensions of `TProg` programs; only constant checkers are switch-admissible in the full system, and its halting fragment is the non-degenerate object); `Flat` (three-point flat domain of Boolean denotations; admissible = monotone maps); `Padded` and `PaddedDiv` (literal and hidden codes with padding, two and three behaviours; admissible = identity or visible-part-only off a finite set); `Models` (small models for the diagonal arguments: the tag model `tagSys` on `Bool × ℕ`, the Boolean models `boolSys adm1`, `boolSys adm2`, `boolSys adm3` with applications `app1`, `app2`, `app3`, and the maps `phiConst`, `phiTrue`); `allAdm sem` (every transformer admissible) and `Examples.emptyAdmSys` (no transformer admissible); `Controls.twinSys`, `Controls.natShiftSys`, `Controls.nonSurjSys`, `Controls.paddedOptSys` and the map `Controls.emptySem` (counterexample and boundary systems). None is a model of a real language. Each of them, and every predicate, checker and auxiliary definition that appears in a quoted statement, is quoted verbatim under Findings, *Toy systems (unfolded)*.
- **What real systems the definitions are meant to capture.** The abstract results are meant to apply to any programming system whose admissible transformers satisfy the fixpoint principle, such as an acceptable numbering of the partial computable functions with total computable transformers. `SwitchAdmissible` captures what "the checker is computable" buys there (closure under definition by cases with constant branches); `EqTestClosed` captures that total computable transformers on natural-number codes can test literal code equality; `System.restrict` captures a sublanguage whose admissible transformers agree literally on the sublanguage with transformers of the full system.
- **Known gaps.** No acceptable-numbering model is built, so the fixpoint principle is never derived for a real language (Mathlib's `ComputablePred.rice` covers that concrete case; cited in prose only, not a dependency). There is no cost model and no notion of semi-decision. `Decides` is a set-theoretic relation; effectiveness enters only through `Adm`.
- **Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); core Lean and `Std` only, **no Mathlib**, no `[[require]]` dependencies. The Lake project in `lean/` has one library, `ToyRice` (namespace `Toy.Rice`).
- **Subjects.** `REPORT.json` lists the Lean toolchain release, which kernel-checked every statement, and the primary papers whose results are restated here (Rice 1953; Kleene 1938 and 1950; Lawvere 1969; Yanofsky 2003) or whose scope is explicitly excluded (Asperti 2008, complexity-aware Rice). The papers are prior art for the statements; nothing in this package was executed against them. Kleene (1950) has no DOI; it is identified by its print coordinates (Proceedings of the KNAW 53 (1950), 800-802; Indagationes Mathematicae 12 (1950), 244-246) and by the KNAW Digital Library record `PU00014670`, a scan of the whole of volume 53, Nos. 6-10, whose retrieved file is pinned by SHA-256 under Evidence.

## Findings

Every result below is a theorem of the `ToyRice` library checked by the Lean kernel; each carries the line `Basis: execution (Lean kernel check)`. A claim about a real system is never part of a theorem: where one is made, it is a separate line `Basis: derived (modeling bridge)` with its reasoning, and nothing in it is formalized. Axioms per theorem and statement hashes are listed under Evidence.

### Core definitions (unfolded)

All definitions are in `ToyRice/Basic.lean` (with `variable (S : System)` in scope). Each has proved positive and negative examples in `ToyRice/Examples.lean` (names `<def>_pos*`, `<def>_neg*`).

```lean
structure System where
  Code : Type u
  Beh : Type v
  sem : Code → Beh
  Adm : (Code → Code) → Prop

def FixpointPrinciple : Prop :=
  ∀ f : S.Code → S.Code, S.Adm f → ∃ c, S.sem (f c) = S.sem c

def Extensional (P : S.Code → Prop) : Prop :=
  ∀ c d, S.sem c = S.sem d → (P c ↔ P d)

def NontrivialPred {α : Type w} (P : α → Prop) : Prop :=
  (∃ a, P a) ∧ (∃ b, ¬ P b)

def Decides {α : Type w} (chk : α → Bool) (P : α → Prop) : Prop :=
  ∀ c, chk c = true ↔ P c

def switch {α : Type w} (chk : α → Bool) (a b : α) : α → α :=
  fun c => cond (chk c) a b

def SwitchAdmissible (chk : S.Code → Bool) : Prop :=
  ∀ a b, S.Adm (switch chk a b)

def DecidedInside (P : S.Code → Prop) : Prop :=
  ∃ chk : S.Code → Bool, Decides chk P ∧ SwitchAdmissible S chk

def SoundFor {α : Type w} (chk : α → Bool) (P : α → Prop) : Prop :=
  ∀ c, chk c = true → P c

def CompleteFor {α : Type w} (chk : α → Bool) (P : α → Prop) : Prop :=
  ∀ c, P c → chk c = true

def ConstClosed : Prop :=
  ∀ k : S.Code, S.Adm (fun _ => k)

def CompClosed : Prop :=
  ∀ f g : S.Code → S.Code, S.Adm f → S.Adm g → S.Adm (f ∘ g)

def SwitchClosed (K : (S.Code → Bool) → Prop) : Prop :=
  ∀ chk, K chk → SwitchAdmissible S chk

def DecidedBy (K : (S.Code → Bool) → Prop) (P : S.Code → Prop) : Prop :=
  ∃ chk, K chk ∧ Decides chk P

def System.restrict (S : System.{u, v}) (F : S.Code → Prop) : System.{u, v} :=
  ⟨{c // F c}, S.Beh, fun x => S.sem x.val,
    fun g => ∃ f, S.Adm f ∧ ∀ x, (g x).val = f x.val⟩

def EqTestClosed : Prop :=
  ∀ f : S.Code → S.Code, S.Adm f → ∀ k a b : S.Code,
    S.Adm (fun c => @ite _ (f c = k) (Classical.propDecidable _) a b)
```

In `ToyRice/Recursion.lean`:

```lean
def Represents (S : System.{u, v}) (app : S.Code → S.Code → Option S.Code) : Prop :=
  ∀ f : S.Code → S.Code, S.Adm f → ∃ e, ∀ x, app e x = some (f x)

def IsDiagonal (S : System.{u, v}) (app : S.Code → S.Code → Option S.Code)
    (d : S.Code → S.Code) : Prop :=
  ∀ x z, app x x = some z → S.sem (d x) = S.sem z

def PrecompClosed (S : System.{u, v}) (d : S.Code → S.Code) : Prop :=
  ∀ f : S.Code → S.Code, S.Adm f → S.Adm (f ∘ d)
```

**Intent.** `FixpointPrinciple`: the conclusion of Kleene's recursion theorem, as an assumption. `Extensional`: a behavioural (semantic) property. `Decides`: a set-theoretic decision relation, with no effectiveness. `SwitchAdmissible`: what "the checker is computable" buys in a computability model (closure of total computable maps under definition by cases with constant branches). `DecidedInside`: some checker decides `P` and all its switches are admissible. `EqTestClosed`: admissible transformers can be followed by a literal code-equality test (true of total computable transformers on natural-number codes). `System.restrict F`: the sublanguage `F`, whose admissible transformers are the fragment maps that agree literally on `F` with some admissible transformer of the full system.

**Definition adequacy** (`Toy.Rice.decidedInside_iff_ite_admissible`, a lemma, not a result card). `DecidedInside S P` says exactly that every transformer `c ↦ if P c then a else b` is admissible, where the `if` uses the classical-logic instance `Classical.propDecidable` (not a computability notion), so that no effectiveness enters through the Boolean checker:

```lean
theorem decidedInside_iff_ite_admissible (P : S.Code → Prop) :
    DecidedInside S P ↔
      ∀ a b : S.Code,
        S.Adm (fun c => @ite _ (P c) (Classical.propDecidable (P c)) a b)
```

| Definition | Positive example(s) | Negative example(s) |
| :--- | :--- | :--- |
| `FixpointPrinciple` | fixpointPrinciple_pos_flat, fixpointPrinciple_pos_padded | fixpointPrinciple_neg_tables, fixpointPrinciple_neg_total (lifted halting fragment) |
| `Extensional` | extensional_pos, extensional_pos_tables | extensional_neg (EvenPad), extensional_neg_litTrue (near miss) |
| `NontrivialPred` | nontrivialPred_pos | nontrivialPred_neg_true, nontrivialPred_neg_false |
| `Decides` | decides_pos | decides_neg (sound but not complete: near miss) |
| `SwitchAdmissible` | switchAdmissible_pos, switchAdmissible_pos_tables | switchAdmissible_neg (haltCheck decides halting but is not switch-admissible) |
| `DecidedInside` | decidedInside_pos_tables, decidedInside_pos_padded | decidedInside_neg_direct |
| `SoundFor / CompleteFor` | soundFor_pos, completeFor_pos | soundFor_neg, completeFor_neg |
| `ConstClosed / CompClosed` | constClosed_pos(_tables), compClosed_pos(_tables) | constClosed_neg, compClosed_neg |
| `SwitchClosed` | switchClosed_pos | switchClosed_neg |
| `EqTestClosed` | eqTestClosed_pos (padded), eqTestClosed_pos_div | eqTestClosed_neg (flat), eqTestClosed_neg_lifted |
| `DecidedBy` | decidedBy_pos (K = switch-admissible checkers, EvenPad) | decidedBy_neg (same K, BehTrue) |
| `System.restrict` | restrict_adm_pos, restrict_example | restrict_adm_neg (a fragment map that is not admissible); restrict_degenerate_flat records a degenerate case |
| `Represents / IsDiagonal / PrecompClosed` | represents_pos, isDiagonal_pos, precompClosed_pos (tag model: non-identity, non-admissible diagonal), precompClosed_pos_padded | represents_neg, isDiagonal_neg, precompClosed_neg |

### Toy systems (unfolded)

Every concrete system, predicate, checker and counterexample model that appears in a quoted statement (main results, tightness counterexamples, non-vacuity witnesses, positive controls and boundary facts) is quoted below verbatim from the Lean sources (declaration doc comments omitted; constructor doc comments kept). Names are given relative to the namespace stated before each block.

`Tables` (`ToyRice/Tables.lean`, namespace `Toy.Rice.Tables`):

```lean
abbrev Table := List (Nat × Nat)
def eval : Table → Nat → Nat
  | [], _ => 0
  | (k, v) :: t, n => if n = k then v else eval t n
def IsZeroFn (t : Table) : Prop := ∀ n, eval t n = 0
def zeroCheck (t : Table) : Bool := t.all (fun p => eval t p.1 == 0)
def allOutputsZero (t : Table) : Bool := t.all (fun p => p.2 == 0)
inductive EntryTest where
  /-- The listed output equals `n`: `v = n`. -/
  | valEq (n : Nat)
  /-- The table's value at the entry's key equals `n`: `eval t k = n`. -/
  | evalAtKeyEq (n : Nat)
  /-- Negation. -/
  | not (e : EntryTest)
  /-- Conjunction. -/
  | and (e f : EntryTest)
def EntryTest.run (t : Table) (e : Nat × Nat) : EntryTest → Bool
  | .valEq n => e.2 == n
  | .evalAtKeyEq n => eval t e.1 == n
  | .not p => !(p.run t e)
  | .and p q => p.run t e && q.run t e
inductive TTest where
  /-- The table's value at input `k` equals `n`. -/
  | evalAtEq (k n : Nat)
  /-- Every entry of the table passes the entry test. -/
  | allEntries (e : EntryTest)
  /-- Negation. -/
  | not (p : TTest)
  /-- Conjunction. -/
  | and (p q : TTest)
def TTest.run (t : Table) : TTest → Bool
  | .evalAtEq k n => eval t k == n
  | .allEntries e => t.all (fun p => e.run t p)
  | .not p => !(p.run t)
  | .and p q => p.run t && q.run t
inductive TProg where
  /-- The constant transformer with output `t`. -/
  | const (t : Table)
  /-- The identity. -/
  | ident
  /-- Set the value at input `k` to `n` (prepend the entry `(k, n)`). -/
  | setAt (k n : Nat)
  /-- Increment the value at input `k` (prepend the entry `(k, eval x k + 1)`). -/
  | incrAt (k : Nat)
  /-- `branch p q r` runs `q` on inputs passing the test `p` and `r` on the others. -/
  | branch (p : TTest) (q r : TProg)
  /-- `comp p q` runs `q`, then `p`. -/
  | comp (p q : TProg)
def TProg.run : TProg → Table → Table
  | .const t, _ => t
  | .ident, x => x
  | .setAt k n, x => (k, n) :: x
  | .incrAt k, x => (k, eval x k + 1) :: x
  | .branch p q r, x => cond (p.run x) (q.run x) (r.run x)
  | .comp p q, x => p.run (q.run x)
def Admissible (f : Table → Table) : Prop := ∃ p : TProg, ∀ x, p.run x = f x
def sys : System := ⟨Table, Nat → Nat, eval, Admissible⟩
```

`eval t n` returns the value of the first entry of `t` with key `n`, and `0` if there is none. `zeroCheck` and `allOutputsZero` are themselves `TTest` tests: `zeroCheck t = TTest.run t (.allEntries (.evalAtKeyEq 0))` and `allOutputsZero t = TTest.run t (.allEntries (.valEq 0))` hold by `rfl` (`Toy.Rice.Tables.zeroCheck_eq_test`, `Toy.Rice.Tables.allOutputsZero_eq_test`). `zeroCheck` evaluates the table at each of its own keys (an extensional check, since keys not in the table evaluate to `0`); `allOutputsZero` inspects the stored values (a syntactic check: it is sound but not complete for `IsZeroFn`, `Toy.Rice.Tables.allOutputsZero_sound_not_complete`; for example `[(0, 0), (0, 5)]` computes the zero function, `zeroCheck` accepts it and `allOutputsZero` rejects it, as checked by `decide` in `ToyRice/Tables.lean`).

`Lifted` (`ToyRice/Lifted.lean`, namespace `Toy.Rice.Lifted`, with `Toy.Rice.Tables` open):

```lean
def Admissible (f : Option Table → Option Table) : Prop :=
  (∃ k, f = fun _ => k) ∨ (f none = none ∧ ∃ p : TProg, ∀ t, f (some t) = some (p.run t))
abbrev sys : System := ⟨Option Table, Option (Nat → Nat), Option.map eval, Admissible⟩
abbrev Halts (c : Option Table) : Prop := c.isSome = true
abbrev totalSys : System := sys.restrict Halts
def HaltsZero (c : Option Table) : Prop := ∃ t, c = some t ∧ IsZeroFn t
def fragCheck (x : totalSys.Code) : Bool :=
  match x with
  | ⟨some t, _⟩ => zeroCheck t
  | ⟨none, h⟩ => absurd h (by decide)
```

`fragCheck` runs `zeroCheck` on the underlying table of a code in the halting fragment; the `none` branch is unreachable because every fragment code satisfies `Halts`. In the full system `Lifted.sys` only the two constant checkers are switch-admissible (`Toy.Rice.Lifted.switchAdmissible_const`), so it decides no nontrivial predicate inside, syntactic or not. The halting fragment `totalSys` is the non-degenerate object: its admissible class is proper and contains the non-constant switch-admissible checker `fragCheck` (W4).

`Flat` (`ToyRice/Flat.lean`, namespace `Toy.Rice.Flat`):

```lean
inductive Flat where
  | bot
  | tt
  | ff
  deriving DecidableEq, Repr
def le (x y : Flat) : Prop := x = .bot ∨ x = y
def Monotone (f : Flat → Flat) : Prop := ∀ x y, le x y → le (f x) (f y)
abbrev sys : System := ⟨Flat, Flat, id, Monotone⟩
def Halts (c : Flat) : Prop := c ≠ .bot
def ReturnsTt (c : Flat) : Prop := c = .tt
def haltCheck (c : Flat) : Bool := decide (c ≠ .bot)
def IsTotal (c : Flat) : Prop := c ≠ .bot
abbrev totalSys : System := sys.restrict IsTotal
```

`haltCheck` decides `Halts` (`Toy.Rice.Flat.haltCheck_decides`) but is not switch-admissible (`Toy.Rice.Examples.switchAdmissible_neg`).

`Padded` (`ToyRice/Padded.lean`, namespace `Toy.Rice.Padded`; the first three functions are in the sub-namespace `Code`, so `c.beh`, `c.pad` and `c.erase` are `Code.beh c`, `Code.pad c` and `Code.erase c`):

```lean
inductive Code where
  | lit (b : Bool) (n : Nat)
  | hid (b : Bool) (n : Nat)
  deriving DecidableEq, Repr
namespace Code
def beh : Code → Bool
  | lit b _ => b
  | hid b _ => b
def pad : Code → Nat
  | lit _ n => n
  | hid _ n => n
def erase : Code → Code
  | lit b n => lit b n
  | hid _ n => hid false n
end Code
def IdOffFinite (f : Code → Code) : Prop :=
  ∃ F : List Code, ∀ c, c ∉ F → f c = c
def VisOnlyOffFinite (f : Code → Code) : Prop :=
  ∃ (F : List Code) (h : Code → Code), ∀ c, c ∉ F → f c = h c.erase
def Admissible (f : Code → Code) : Prop := IdOffFinite f ∨ VisOnlyOffFinite f
abbrev sys : System := ⟨Code, Bool, Code.beh, Admissible⟩
def BehTrue (c : Code) : Prop := c.beh = true
def EvenPad (c : Code) : Prop := c.pad % 2 = 0
def evenPadCheck (c : Code) : Bool := c.pad % 2 == 0
def litTrueCheck : Code → Bool
  | lit b _ => b
  | hid _ _ => false
def IsLit : Code → Prop
  | lit _ _ => True
  | hid _ _ => False
```

So `erase (lit b n) = lit b n` and `erase (hid b n) = hid false n`: a transformer of the second kind cannot read the behaviour bit of a hidden code outside its finite exception list. `litTrueCheck` accepts exactly the codes `lit true n`.

`PaddedDiv` (`ToyRice/PaddedDiv.lean`, namespace `Toy.Rice.PaddedDiv`; behaviours `Option Bool`, with `none` = diverges):

```lean
inductive Code where
  | lit (b : Option Bool) (n : Nat)
  | hid (b : Option Bool) (n : Nat)
  deriving DecidableEq
namespace Code
def beh : Code → Option Bool
  | lit b _ => b
  | hid b _ => b
def pad : Code → Nat
  | lit _ n => n
  | hid _ n => n
def erase : Code → Code
  | lit b n => lit b n
  | hid _ n => hid none n
end Code
def IdOffFinite (f : Code → Code) : Prop :=
  ∃ F : List Code, ∀ c, c ∉ F → f c = c
def VisOnlyOffFinite (f : Code → Code) : Prop :=
  ∃ (F : List Code) (h : Code → Code), ∀ c, c ∉ F → f c = h c.erase
def Admissible (f : Code → Code) : Prop := IdOffFinite f ∨ VisOnlyOffFinite f
abbrev sys : System := ⟨Code, Option Bool, Code.beh, Admissible⟩
def Halts (c : Code) : Prop := c.beh ≠ none
def ReturnsTrue (c : Code) : Prop := c.beh = some true
```

Here `erase (hid b n) = hid none n` (not `hid false n` as in `Padded`).

`Models` (`ToyRice/Models.lean`, namespace `Toy.Rice.Models`): the tag model used as the non-vacuity witness of F3, the Boolean models used as the tightness counterexamples of F3, and the maps used for F1 and F2.

```lean
def tagAdm (f : Bool × Nat → Bool × Nat) : Prop :=
  (∃ k, f = fun _ => k) ∨ (∃ m, f = fun x => (x.1, m))
abbrev tagSys : System := ⟨Bool × Nat, Bool, Prod.fst, tagAdm⟩
def tagApp (e x : Bool × Nat) : Option (Bool × Nat) :=
  if e.2 % 2 = 0 then some (e.1, e.2 / 2) else some (x.1, e.2 / 2)
def tagDiag (x : Bool × Nat) : Bool × Nat := (x.1, x.2 + 1)
abbrev boolSys (A : (Bool → Bool) → Prop) : System := ⟨Bool, Bool, id, A⟩
def DiagConclusion (S : System) (app : S.Code → S.Code → Option S.Code) (d : S.Code → S.Code) :
    Prop :=
  ∀ f : S.Code → S.Code, S.Adm f →
    (∃ e, ∀ x, app e x = some (f (d x))) ∧
    (∀ e, (∀ x, app e x = some (f (d x))) → S.sem (f (d e)) = S.sem (d e))
def adm1 (f : Bool → Bool) : Prop := f = not ∨ f = fun _ => false
def app1 : Bool → Bool → Option Bool
  | true, x => some (!x)
  | false, _ => some false
def adm2 (_ : Bool → Bool) : Prop := True
def app2 : Bool → Bool → Option Bool := fun _ _ => none
def adm3 (f : Bool → Bool) : Prop := f = id ∨ f = not
def app3 : Bool → Bool → Option Bool
  | true, x => some (!x)
  | false, x => some x
def IsConst (g : Bool → Bool) : Prop := ∃ k, g = fun _ => k
def phiConst (a _ : Bool) : Bool := a
def phiTrue (_ _ : Unit) : Bool := true
def LawvereConclusion {A : Type} {Y : Type} (φ : A → A → Y) (t : Y → Y) : Prop :=
  (∃ a, ∀ x, φ a x = t (φ x x)) ∧ (∀ a, (∀ x, φ a x = t (φ x x)) → t (φ a a) = φ a a)
```

`DiagConclusion S app d` is, verbatim, the conclusion of F3 (`Toy.Rice.diagonalFixedPoint_of_represents_diagonal_precompClosed`) for the given `app` and `d`, and `LawvereConclusion φ t` is, verbatim, the conclusion of F1 (`Toy.Rice.lawvere_fixedPoint_of_represents_diagonal`) with `A Y : Type`. In each Boolean model `boolSys admN` the codes and behaviours are `Bool` with `sem = id`; `appN e x` is the output of code `e` on input `x` (`app2` never halts). `phiConst a` is the constant map with value `a`, so `phiConst` represents exactly the constant maps `Bool → Bool`; `phiTrue` on `Unit` represents only the constant-`true` map.

Systems built from arbitrary data (`ToyRice/Abstract.lean`, namespace `Toy.Rice`; `ToyRice/Examples.lean`, namespace `Toy.Rice.Examples`):

```lean
def allAdm {C : Type u} {B : Type v} (sem : C → B) : System.{u, v} :=
  ⟨C, B, sem, fun _ => True⟩
```
```lean
abbrev emptyAdmSys : System := ⟨Bool, Bool, id, fun _ => False⟩
```

`allAdm sem` admits every transformer; `emptyAdmSys` admits none.

Counterexample and boundary systems (`ToyRice/Controls.lean`, namespace `Toy.Rice.Controls`):

```lean
def tagOr (c : Bool × Bool) : Bool := c.1 || c.2
def twinAdm (f : Bool × Bool → Bool × Bool) : Prop := ∃ a b, f = switch tagOr a b
abbrev twinSys : System := ⟨Bool × Bool, Bool, Prod.fst, twinAdm⟩
abbrev natShiftSys : System :=
  ⟨Nat, Nat, id, fun f => (∃ k, f = fun _ => k) ∨ (∃ k, f = fun n => n + k)⟩
def nonSurjSys : System := ⟨Unit, Bool, fun _ => true, fun _ => True⟩
def paddedOptSys : System := ⟨Padded.Code, Option Bool, fun c => some c.beh, Padded.Admissible⟩
def emptySem (e : Empty) : Unit := nomatch e
```

In `twinSys` the admissible transformers are exactly the switches on `tagOr`; in `natShiftSys` they are the constants and the shifts `n ↦ n + k`; `nonSurjSys` has one code `()` with behaviour `true`, so its semantics is not surjective onto `Bool`; in `paddedOptSys` the behaviour `none` is the behaviour of no code; `emptySem` is the unique map out of the empty type.

### R1. `Toy.Rice.not_decidedInside_of_fixpointPrinciple_extensional_nontrivial`

Basis: execution (Lean kernel check)

- **Kind:** impossibility. **Tier:** T0. Re-derivation of Rice's theorem (Rice 1953) by the standard recursion-theorem argument with a swapped case split (as in Yanofsky 2003, the Coq development coq-synthetic-computability, and Mathlib's ComputablePred.rice), restated over an abstract system in which the recursion theorem is an assumption.
- **Plain claim:** In any programming system satisfying the fixpoint principle (every admissible transformer f has a code c with sem (f c) = sem c), no nontrivial extensional predicate P on codes is decided inside the system: there is no checker that decides P and all of whose switches c ↦ if chk c then a else b are admissible.
- **Note:** No global closure law on Adm is assumed as a separate hypothesis; the only admissibility the proof uses is that of one switch on the checker, which is part of DecidedInside (see R2). The class form, for any class K of checkers all of whose switches are admissible (K ⊆ SwitchAdmissible S), is the corollary Toy.Rice.not_decidedBy_of_fixpointPrinciple_switchClosed_extensional_nontrivial.

```lean
theorem not_decidedInside_of_fixpointPrinciple_extensional_nontrivial
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    (hnt : NontrivialPred P) : ¬ DecidedInside S P
```

With the definitions unfolded: assuming `hfix : ∀ f, S.Adm f → ∃ c, S.sem (f c) = S.sem c`, `hext : ∀ c d, S.sem c = S.sem d → (P c ↔ P d)` and `hnt : (∃ a, P a) ∧ (∃ b, ¬ P b)`, the conclusion is `¬ ∃ chk : S.Code → Bool, (∀ c, chk c = true ↔ P c) ∧ ∀ a b, S.Adm (fun c => cond (chk c) a b)`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfix : FixpointPrinciple S` | Supplies a semantic fixed point of the swapped switch. | tight: counterexample `Toy.Rice.Controls.rice_tight_fixpointPrinciple` |
| `hext : Extensional S P` | Transfers P across the equation sem (f c) = sem c. | tight: counterexample `Toy.Rice.Controls.rice_tight_extensional` |
| `hnt.1 : ∃ a, P a` | A branch of the swapped switch satisfying P. | tight: counterexample `Toy.Rice.Controls.rice_tight_nontrivial_hasMember` |
| `hnt.2 : ∃ b, ¬ P b` | A branch of the swapped switch violating P. | tight: counterexample `Toy.Rice.Controls.rice_tight_nontrivial_hasNonMember` |

- **Depth:** shallow. Apply the fixpoint principle to the swapped switch and case on the checker's verdict at the fixed point.
- **Non-vacuity witness:** The padded system with BehTrue and the flat domain with Halts satisfy all hypotheses. (`Toy.Rice.Controls.rice_nonvacuous`)
- **Positive control:** `Toy.Rice.Controls.rice_tight_fixpointPrinciple`: the lookup-table system, which lacks the fixpoint principle, decides the extensional nontrivial predicate `IsZeroFn` inside.
- **Relation to Lawvere's theorem:** Lawvere's theorem: if every map in a class is represented by a point, every endomorphism whose diagonal lies in the class has a fixed point. Here the fixpoint principle plays the role of that conclusion, and the swapped switch on a decider of a nontrivial extensional P moves every code to a code of the other P-status, acting on the two P-classes like Boolean negation, which has no fixed point. F3 shows the fixpoint principle itself is a Lawvere-style diagonal consequence of representability.
- **Does not forbid**: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers: these are switch-admissible in systems with the fixpoint principle (W1, W2), and W5 states the incompleteness every such checker of a nontrivial extensional predicate has.
- **Non-claims:** 10 items, listed under Boundaries, *Non-claims by result*, R1.
- **Prior art:**
  - H. G. Rice, "Classes of recursively enumerable sets and their decision problems", Transactions of the American Mathematical Society 74(2) (1953), 358-366, DOI 10.1090/S0002-9947-1953-0053041-6. The original theorem: an index set of r.e. sets is recursive only if it is trivial.
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
  - N. S. Yanofsky, "A universal approach to self-referential paradoxes, incompleteness and fixed points", Bulletin of Symbolic Logic 9(3) (2003), 362-386, DOI 10.2178/bsl/1058448677 (arXiv:math/0305282). Derives the recursion theorem from Lawvere's scheme (Theorem 5 in the arXiv text) and proves Rice's theorem with the swapped case split h(x) = a if x is not in A, b if x is in A.
  - Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Computability/Halting.lean: ComputablePred.rice (line 32), proved from Nat.Partrec.Code.fixed_point₂ with a swapped Partrec.cond, and ComputablePred.rice₂ (line 42): a predicate on codes that respects eval is computable iff it is empty or everything. Described in prose only; not a dependency.
  - uds-psl/coq-synthetic-computability, theories/Basic/Rice.v at commit 7e019a047314a75d90f33899a6ff023a22e9d618: Lemma FP (line 97: every f has e with Θ e ≡ Θ (f e), from an abstract enumerability principle) and Lemma Rice_Theorem' (line 112; the swapped case split is at line 118). The closest existing mechanization of Rice's theorem from an abstract fixed-point lemma; it does not separate an admissible class from the ambient function space. Associated thesis: Y. Forster, Computability in Constructive Type Theory, Saarland University, 2021, DOI 10.22028/D291-35758.
  - Y. Forster and G. Smolka, "Weak call-by-value lambda calculus as a model of computation in Coq", ITP 2017, LNCS 10499, 189-206, DOI 10.1007/978-3-319-66107-0_13; uds-psl/coq-library-undecidability, theories/L/Computability/Scott.v at commit 138245ce9172b45d91ec49eda1cc67ef155bc14e: Theorem Scott (line 6), proved from SecondFixedPoint with a swapped case split.
  - M. Norrish, "Mechanised computability theory", ITP 2011, LNCS 6898, 297-311, DOI 10.1007/978-3-642-22863-6_22. HOL4 mechanization including the recursion theorem, an s-m-n instance and Rice's theorem.
  - M. Nedzelsky, "Recursion Theory I", Archive of Formal Proofs, April 2008, https://isa-afp.org/entries/Recursion-Theory-I.html; F. J. Balbach, "Some classical results in inductive inference of recursive functions", Archive of Formal Proofs, August 2020, https://www.isa-afp.org/entries/Inductive_Inference.html. Isabelle/HOL mechanizations that include Rice's theorem (Balbach also s-m-n and recursion theorems of Kleene, Rogers and Smullyan).
  - M. Carneiro, "Formalizing computability theory via partial recursive functions", ITP 2019, LIPIcs 141, 12:1-12:17, DOI 10.4230/LIPIcs.ITP.2019.12. The reference for Mathlib's computability library.
  - A. Asperti, "The intensional content of Rice's theorem", in: Proceedings of the 35th Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '08), San Francisco, ACM, 2008, 113-119, DOI 10.1145/1328438.1328455. Replaces extensional index sets by complexity cliques (sets of indices closed under same behaviour and similar complexity) and proves, under weak complexity assumptions, that every recursive complexity clique is trivial and every r.e. complexity clique is extensional. Cited only for the cost-model non-claim; no statement here models complexity.
- **Design question:** addresses which checker designs are ruled out (internal deciders of nontrivial behavioural properties) and under which single hypothesis about the system (the fixpoint principle). (Instance of the package design question stated in Summary.)

Basis: derived (modeling bridge). For an acceptable numbering of the partial computable functions (Code = indices, sem = the numbering, Adm = total computable transformers), FixpointPrinciple holds and every computable checker is switch-admissible, so R1 yields Rice's theorem for that numbering. *Reasoning:* The fixpoint principle is the conclusion of Kleene's (second) recursion theorem in Rogers' form; Mathlib's Nat.Partrec.Code.fixed_point states exactly this for its code type. Total computable functions are closed under definition by cases on a computable Boolean with constant branches. Neither step is formalized in this package.

### R2. `Toy.Rice.swappedSwitch_not_admissible_of_fixpointPrinciple_extensional_decides`

Basis: execution (Lean kernel check)

- **Kind:** impossibility. **Tier:** T0. The single case split at the heart of the standard proof (Yanofsky 2003; Rice_Theorem' in coq-synthetic-computability; ComputablePred.rice in Mathlib), isolated as a statement.
- **Plain claim:** In a system with the fixpoint principle, if chk decides an extensional predicate P, a satisfies P and b violates P, then the swapped switch c ↦ if chk c then b else a is not admissible.

```lean
theorem swappedSwitch_not_admissible_of_fixpointPrinciple_extensional_decides
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    {chk : S.Code → Bool} (hdec : Decides chk P) {a b : S.Code} (ha : P a) (hb : ¬ P b) :
    ¬ S.Adm (switch chk b a)
```

With the definitions unfolded: `hfix : ∀ f, S.Adm f → ∃ c, S.sem (f c) = S.sem c`, `hext : ∀ c d, S.sem c = S.sem d → (P c ↔ P d)`, `hdec : ∀ c, chk c = true ↔ P c`, `ha : P a`, `hb : ¬ P b`; the conclusion is `¬ S.Adm (fun c => cond (chk c) b a)`: the swapped switch sends accepted codes to `b`, which violates `P`, and rejected codes to `a`, which satisfies `P`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfix : FixpointPrinciple S` | Semantic fixed point of the swapped switch. | tight: counterexample `Toy.Rice.Controls.riceSharp_tight_fixpointPrinciple` |
| `hext : Extensional S P` | Transfers P across the semantic equation. | tight: counterexample `Toy.Rice.Controls.riceSharp_tight_extensional` |
| `hdec : Decides chk P` | Links the checker's verdict at the fixed point to P in both directions. | tight: counterexample `Toy.Rice.Controls.riceSharp_tight_decides` |
| `ha : P a` | The branch taken on rejection satisfies P. | tight: counterexample `Toy.Rice.Controls.riceSharp_tight_member` |
| `hb : ¬ P b` | The branch taken on acceptance violates P. | tight: counterexample `Toy.Rice.Controls.riceSharp_tight_nonmember` |

- **Depth:** shallow. One application of the fixpoint principle and a case split.
- **Non-vacuity witness:** Flat domain, haltCheck, a = tt, b = bot. (`Toy.Rice.Controls.riceSharp_nonvacuous`)
- **Positive control:** `Toy.Rice.Controls.riceSharp_tight_fixpointPrinciple`: in the lookup-table system `zeroCheck` decides `IsZeroFn`, `[]` satisfies it, `[(0, 1)]` violates it, and the swapped switch `switch zeroCheck [(0, 1)] []` is admissible.
- **Does not forbid**: (i) partial or one-sided procedures: the unswapped switch c ↦ if chk c then a else b can be admissible (Toy.Rice.Flat.unswappedSwitch_admissible), and a one-sided switch that diverges on rejected codes can be admissible while the predicate is not decided inside (W8); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers: these are switch-admissible in systems with the fixpoint principle (W1, W2), and W5 states the incompleteness every such checker of a nontrivial extensional predicate has.
- **Non-claims:** 4 items, listed under Boundaries, *Non-claims by result*, R2.
- **Prior art:**
  - N. S. Yanofsky, "A universal approach to self-referential paradoxes, incompleteness and fixed points", Bulletin of Symbolic Logic 9(3) (2003), 362-386, DOI 10.2178/bsl/1058448677 (arXiv:math/0305282). Derives the recursion theorem from Lawvere's scheme (Theorem 5 in the arXiv text) and proves Rice's theorem with the swapped case split h(x) = a if x is not in A, b if x is in A.
  - uds-psl/coq-synthetic-computability, theories/Basic/Rice.v at commit 7e019a047314a75d90f33899a6ff023a22e9d618: Lemma FP (line 97: every f has e with Θ e ≡ Θ (f e), from an abstract enumerability principle) and Lemma Rice_Theorem' (line 112; the swapped case split is at line 118). The closest existing mechanization of Rice's theorem from an abstract fixed-point lemma; it does not separate an admissible class from the ambient function space. Associated thesis: Y. Forster, Computability in Constructive Type Theory, Saarland University, 2021, DOI 10.22028/D291-35758.
  - Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Computability/Halting.lean: ComputablePred.rice (line 32), proved from Nat.Partrec.Code.fixed_point₂ with a swapped Partrec.cond, and ComputablePred.rice₂ (line 42): a predicate on codes that respects eval is computable iff it is empty or everything. Described in prose only; not a dependency.
- **Design question:** addresses the minimal piece of 'being internal' that the impossibility actually uses (one swapped switch). (Instance of the package design question stated in Summary.)

### R4. `Toy.Rice.decidedInside_iff_trivial_of_fixpointPrinciple_constClosed_extensional`

Basis: execution (Lean kernel check)

- **Kind:** characterization. **Tier:** T0. The 'decidable iff trivial' form of Rice's theorem (compare ComputablePred.rice₂ in Mathlib), restated over an abstract system.
- **Plain claim:** In a system with the fixpoint principle whose admissible class contains every constant transformer, an extensional predicate is decided inside the system if and only if it holds of every code or of no code.

```lean
theorem decidedInside_iff_trivial_of_fixpointPrinciple_constClosed_extensional
    (hfix : FixpointPrinciple S) (hconst : ConstClosed S) {P : S.Code → Prop}
    (hext : Extensional S P) :
    DecidedInside S P ↔ (∀ c, P c) ∨ (∀ c, ¬ P c)
```

With the definitions unfolded: `hfix : ∀ f, S.Adm f → ∃ c, S.sem (f c) = S.sem c`, `hconst : ∀ k, S.Adm (fun _ => k)`, `hext : ∀ c d, S.sem c = S.sem d → (P c ↔ P d)`; the conclusion is `(∃ chk, (∀ c, chk c = true ↔ P c) ∧ ∀ a b, S.Adm (fun c => cond (chk c) a b)) ↔ (∀ c, P c) ∨ (∀ c, ¬ P c)`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfix : FixpointPrinciple S` | Forward direction (via R1). | tight: counterexample `Toy.Rice.Controls.riceChar_tight_fixpointPrinciple` |
| `hconst : ConstClosed S` | Backward direction: trivial predicates are decided by constant checkers, whose switches are constant transformers. | tight: counterexample `Toy.Rice.Controls.riceChar_tight_constClosed` |
| `hext : Extensional S P` | Forward direction (via R1). | tight: counterexample `Toy.Rice.Controls.riceChar_tight_extensional` |

- **Depth:** shallow. R1 plus a classical case split; the converse uses constant checkers.
- **Non-vacuity witness:** Padded system: the trivial predicate True (decided inside, trivial) and the nontrivial BehTrue (not decided inside, not trivial) exercise both sides. (`Toy.Rice.Controls.riceChar_nonvacuous`)
- **Does not forbid**: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers: these are switch-admissible in systems with the fixpoint principle (W1, W2), and W5 states the incompleteness every such checker of a nontrivial extensional predicate has.
- **Non-claims:** 4 items, listed under Boundaries, *Non-claims by result*, R4.
- **Prior art:**
  - Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Computability/Halting.lean: ComputablePred.rice (line 32), proved from Nat.Partrec.Code.fixed_point₂ with a swapped Partrec.cond, and ComputablePred.rice₂ (line 42): a predicate on codes that respects eval is computable iff it is empty or everything. Described in prose only; not a dependency.
  - H. G. Rice, "Classes of recursively enumerable sets and their decision problems", Transactions of the American Mathematical Society 74(2) (1953), 358-366, DOI 10.1090/S0002-9947-1953-0053041-6. The original theorem: an index set of r.e. sets is recursive only if it is trivial.
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
- **Design question:** addresses the exact boundary for internal deciders of behavioural properties, given constants. (Instance of the package design question stated in Summary.)

### R6. `Toy.Rice.not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial`

Basis: execution (Lean kernel check)

- **Kind:** impossibility. **Tier:** T1. Abstract form of the classical recursive-inseparability obstruction (Kleene 1950): with code-equality tests available, restricting to a behaviour-closed fragment such as the halting programs does not make a nontrivial extensional property decided inside the restricted system. We did not find this abstract formulation, with an explicit code-equality closure law, in the sources checked; no novelty is claimed.
- **Plain claim:** Let S have the fixpoint principle, let its admissible transformers be closed under literal code-equality tests (for admissible f and codes k, a, b, the transformer c ↦ if f c = k then a else b is admissible), and let F be a fragment of codes closed under same behaviour. Then no predicate that is extensional and nontrivial on F is decided inside the restricted system S.restrict F, whose admissible transformers are the fragment maps that agree literally on F with some admissible transformer of S.

```lean
theorem not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial
    (hfix : FixpointPrinciple S) (heq : EqTestClosed S) {F : S.Code → Prop}
    (hF : Extensional S F) {P : S.Code → Prop}
    (hext : Extensional (S.restrict F) (fun x => P x.val))
    (hnt : NontrivialPred (fun x : {c // F c} => P x.val)) :
    ¬ DecidedInside (S.restrict F) (fun x => P x.val)
```

With the definitions unfolded: `hfix : ∀ f, S.Adm f → ∃ c, S.sem (f c) = S.sem c`; `heq : ∀ f, S.Adm f → ∀ k a b, S.Adm (fun c => if f c = k then a else b)` (the `if` uses the classical-logic instance `Classical.propDecidable`); `hF : ∀ c d, S.sem c = S.sem d → (F c ↔ F d)`; `hext : ∀ x y : {c // F c}, S.sem x.val = S.sem y.val → (P x.val ↔ P y.val)`; `hnt : (∃ x : {c // F c}, P x.val) ∧ (∃ x : {c // F c}, ¬ P x.val)`. The conclusion says there is no `chk : {c // F c} → Bool` with `∀ x, chk x = true ↔ P x.val` such that for all fragment codes `a b` some `f` with `S.Adm f` satisfies `∀ x, (cond (chk x) a b).val = f x.val`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfix : FixpointPrinciple S` | Semantic fixed point of the full-system transformer built from the fragment switch and a code-equality test. | tight: counterexample `Toy.Rice.Controls.restrict_tight_fixpointPrinciple` |
| `heq : EqTestClosed S` | Turns the full-system extension f of the fragment switch into the swap c ↦ if f c = a then b else a. | tight: counterexample `Toy.Rice.Controls.restrict_tight_eqTestClosed` |
| `hF : Extensional S F` | Forces the fixed point, which behaves like a fragment code, into the fragment. | tight: counterexample `Toy.Rice.Controls.restrict_tight_extensionalFragment` |
| `hext : Extensional (S.restrict F) (fun x => P x.val)` | Transfers P across the semantic equation inside the fragment. | tight: counterexample `Toy.Rice.Controls.restrict_tight_extensional` |
| `hnt.1 : ∃ x : {c // F c}, P x.val` | A fragment code satisfying P (a branch). | tight: counterexample `Toy.Rice.Controls.restrict_tight_hasMember` |
| `hnt.2 : ∃ x : {c // F c}, ¬ P x.val` | A fragment code violating P (the other branch). | tight: counterexample `Toy.Rice.Controls.restrict_tight_hasNonMember` |

- **Depth:** shallow. One fixpoint application to a code-equality test composed with the full-system extension of an unswapped fragment switch, then a four-way case split.
- **Non-vacuity witness:** The padded system with divergence (three behaviours), the halting fragment, and 'returns true'. (`Toy.Rice.Controls.restrict_nonvacuous`)
- **Positive control:** `Toy.Rice.Controls.restrict_tight_eqTestClosed`: the lifted system has the fixpoint principle, and its halting fragment decides `HaltsZero`, extensional and nontrivial on the fragment, inside; the lifted system is not closed under code-equality tests (`Toy.Rice.Lifted.not_eqTestClosed`), which is the hypothesis this control drops.
- **Does not forbid**: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for other kinds of fragment: R6 covers only fragments closed under same behaviour in systems closed under code-equality tests; a syntactically delimited fragment (Toy.Rice.Controls.restrict_tight_extensionalFragment), a separate total language (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality (W4) can each decide a nontrivial property inside; (iii) sound but incomplete checkers: R6 constrains only checkers that decide the predicate on the fragment; sound but incomplete checkers are switch-admissible in systems with the fixpoint principle (W1, W2).
- **Non-claims:** 5 items, listed under Boundaries, *Non-claims by result*, R6.
- **Prior art:**
  - S. C. Kleene, "A symmetric form of Gödel's theorem", Proceedings of the KNAW 53 (1950), 800-802; also Indagationes Mathematicae 12 (1950), 244-246; no DOI; KNAW Digital Library record PU00014670, https://dwc.knaw.nl/DL/publications/PU00014670.pdf (a scan of Proceedings volume 53, Nos. 6-10, pp. 685-1656, containing the article at pp. 800-802). Constructs two disjoint r.e. sets that no recursive set separates (recursive inseparability).
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
- **Design question:** addresses checkers for restricted fragments: restricting to a behaviour-closed fragment does not help when the system can test code equality. (Instance of the package design question stated in Summary.)

Basis: derived (modeling bridge). For an acceptable numbering with Adm = total computable transformers, take F = the indices of programs that halt on input 0 and P = 'outputs 1 on input 0'. Then no total computable transformer agrees literally, on every index in F, with a switch on a checker deciding P on F. *Reasoning:* Codes are natural numbers, so total computable transformers are closed under code-equality tests; F is closed under same behaviour; the fixpoint principle is Kleene's recursion theorem. This is the abstract shadow of the recursive inseparability of {e : φ_e(0) = 1} and {e : φ_e(0) = 0} (Kleene 1950). Not formalized here.

### F1. `Toy.Rice.lawvere_fixedPoint_of_represents_diagonal`

Basis: execution (Lean kernel check)

- **Kind:** theorem. **Tier:** T0. Lawvere's fixed-point theorem (1969, Theorem 1.1) for types and functions, relativized to a class of maps; the unrelativized form is Mathlib's Function.exists_fixed_point_of_surjective.
- **Plain claim:** Let φ : A → A → Y represent every map in a class G (each g in G equals φ a pointwise for some a), and let t : Y → Y be such that the diagonal map x ↦ t (φ x x) is in G. Then some a represents that diagonal map, and for every such a, φ a a is a fixed point of t.

```lean
theorem lawvere_fixedPoint_of_represents_diagonal {A : Type u} {Y : Type v} (φ : A → A → Y)
    (G : (A → Y) → Prop) (hrep : ∀ g, G g → ∃ a, ∀ x, φ a x = g x) (t : Y → Y)
    (hdiag : G (fun x => t (φ x x))) :
    (∃ a, ∀ x, φ a x = t (φ x x)) ∧ (∀ a, (∀ x, φ a x = t (φ x x)) → t (φ a a) = φ a a)
```

The statement uses no package definitions; it is displayed fully unfolded.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hrep : ∀ g, G g → ∃ a, ∀ x, φ a x = g x` | Every map in the class has a representing point. | tight: counterexample `Toy.Rice.Models.lawvere_tight_represents` |
| `hdiag : G (fun x => t (φ x x))` | The diagonal map lies in the class. | tight: counterexample `Toy.Rice.Models.lawvere_tight_diagonal` |

- **Depth:** definitional. Instantiate hrep at the diagonal; the fixed-point equation is hrep's equation at a itself.
- **Non-vacuity witness:** A = Y = Bool, φ = phiConst representing the constant maps, t = const true. (`Toy.Rice.Models.lawvere_nonvacuous`)
- **Related lemmas:** `Toy.Rice.exists_fixedPoint_of_represents_diagonal` (same hypotheses as F1; concludes only ∃ y, t y = y (t has a fixed point))
- **Does not forbid** any checker design: it is a fixed-point existence statement about represented maps. In particular it says nothing against partial or semi-decision procedures (W8), checkers for decidable fragments (N1, W4), or sound but incomplete checkers (W1, W2).
- **Non-claims:** 4 items, listed under Boundaries, *Non-claims by result*, F1.
- **Prior art:**
  - F. W. Lawvere, "Diagonal arguments and cartesian closed categories", in Category Theory, Homology Theory and their Applications II, Lecture Notes in Mathematics 92, Springer, 1969, 134-145, DOI 10.1007/BFb0080769; reprinted with commentary in Reprints in Theory and Applications of Categories No. 15 (2006), 1-13. Theorem 1.1 (checked in the reprint): in any cartesian closed category, if there is a weakly point-surjective morphism A -> Y^A then Y has the fixed point property; Cantor's theorem follows with Y = 2.
  - N. S. Yanofsky, "A universal approach to self-referential paradoxes, incompleteness and fixed points", Bulletin of Symbolic Logic 9(3) (2003), 362-386, DOI 10.2178/bsl/1058448677 (arXiv:math/0305282). Derives the recursion theorem from Lawvere's scheme (Theorem 5 in the arXiv text) and proves Rice's theorem with the swapped case split h(x) = a if x is not in A, b if x is in A.
  - Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Logic/Function/Basic.lean: Function.exists_fixed_point_of_surjective (lines 367-368; documented as Lawvere's fixed-point theorem for types and functions) and Function.cantor_surjective (line 374). Prose only.
- **Design question:** addresses where fixpoint principles come from (the diagonal pattern). (Instance of the package design question stated in Summary.)

### F2. `Toy.Rice.nonempty_subsingleton_of_weaklyPointSurjective`

Basis: execution (Lean kernel check)

- **Kind:** impossibility. **Tier:** T0. Cantor's theorem in Lawvere's form (Lawvere 1969, Corollary 1.2 setting); compare Mathlib's Function.cantor_surjective.
- **Plain claim:** For types and arbitrary functions, if φ : A → A → Y represents every map A → Y, then Y has exactly one element.

```lean
theorem nonempty_subsingleton_of_weaklyPointSurjective {A : Type u} {Y : Type v} (φ : A → A → Y)
    (hsurj : ∀ g : A → Y, ∃ a, ∀ x, φ a x = g x) : Nonempty Y ∧ ∀ y y' : Y, y = y'
```

The statement uses no package definitions; it is displayed fully unfolded.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hsurj : ∀ g : A → Y, ∃ a, ∀ x, φ a x = g x` | Weak point-surjectivity: every map is represented. | tight: counterexample `Toy.Rice.Controls.cantor_tight_surjective` |

- **Depth:** shallow. Lawvere's theorem applied to a fixed-point-free swap of two distinct elements (classical); nonemptiness because A must be nonempty to represent the empty-domain map.
- **Non-vacuity witness:** A = Y = Unit. (`Toy.Rice.Controls.cantor_nonvacuous`)
- **Positive control:** `Toy.Rice.Controls.cantor_tight_surjective`: for `Y = Bool`, which has two elements, the map `phiConst` does not represent every map `Bool → Bool`.
- **Related lemmas:** `Toy.Rice.subsingleton_of_weaklyPointSurjective` (same hypothesis as F2; concludes only ∀ y y' : Y, y = y' (the subsingleton half of F2))
- **Does not forbid** any checker design: it concerns a function space that contains every map A → Y. In particular it says nothing against partial or semi-decision procedures (W8), checkers for decidable fragments (N1, W4), or sound but incomplete checkers (W1, W2).
- **Non-claims:** 3 items, listed under Boundaries, *Non-claims by result*, F2.
- **Prior art:**
  - F. W. Lawvere, "Diagonal arguments and cartesian closed categories", in Category Theory, Homology Theory and their Applications II, Lecture Notes in Mathematics 92, Springer, 1969, 134-145, DOI 10.1007/BFb0080769; reprinted with commentary in Reprints in Theory and Applications of Categories No. 15 (2006), 1-13. Theorem 1.1 (checked in the reprint): in any cartesian closed category, if there is a weakly point-surjective morphism A -> Y^A then Y has the fixed point property; Cantor's theorem follows with Y = 2.
  - Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Logic/Function/Basic.lean: Function.exists_fixed_point_of_surjective (lines 367-368; documented as Lawvere's fixed-point theorem for types and functions) and Function.cantor_surjective (line 374). Prose only.
  - D. Scott, "Continuous lattices", in Toposes, Algebraic Geometry and Logic, Lecture Notes in Mathematics 274, Springer, 1972, 97-136, DOI 10.1007/BFb0073967. Constructs a continuous lattice isomorphic to its own function space (a model of the lambda calculus).
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2) (1955), 285-309, DOI 10.2140/pjm.1955.5.285. Every monotone map on a complete lattice has a fixed point.
- **Design question:** addresses why the admissible class must be restricted for a fixpoint principle to say anything. (Instance of the package design question stated in Summary.)

### F3. `Toy.Rice.diagonalFixedPoint_of_represents_diagonal_precompClosed`

Basis: execution (Lean kernel check)

- **Kind:** theorem. **Tier:** T0. Abstract form of Kleene's (second) recursion theorem via a diagonal (as in Yanofsky 2003 and Lemma FP of coq-synthetic-computability), with the closure hypothesis weakened to closure under precomposition with the diagonal.
- **Plain claim:** If every admissible transformer is computed by some code under a partial application app (Represents), d is a diagonal transformer (whenever app x x halts with output z, the code d x behaves like z), and precomposition with d preserves admissibility, then for every admissible f some code e computes f ∘ d, and for every such e the code d e is a semantic fixed point of f (sem (f (d e)) = sem (d e)). In particular the system has the fixpoint principle.

```lean
theorem diagonalFixedPoint_of_represents_diagonal_precompClosed
    (app : S.Code → S.Code → Option S.Code) (d : S.Code → S.Code)
    (hrep : Represents S app) (hdiag : IsDiagonal S app d) (hpre : PrecompClosed S d) :
    ∀ f : S.Code → S.Code, S.Adm f →
      (∃ e, ∀ x, app e x = some (f (d x))) ∧
      (∀ e, (∀ x, app e x = some (f (d x))) → S.sem (f (d e)) = S.sem (d e))
```

With the definitions unfolded: `hrep : ∀ f, S.Adm f → ∃ e, ∀ x, app e x = some (f x)`; `hdiag : ∀ x z, app x x = some z → S.sem (d x) = S.sem z`; `hpre : ∀ f, S.Adm f → S.Adm (f ∘ d)`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hrep : Represents S app` | A code e computing f ∘ d. | tight: counterexample `Toy.Rice.Models.kleene_tight_represents` |
| `hdiag : IsDiagonal S app d` | d e behaves like the output of e on itself. | tight: counterexample `Toy.Rice.Models.kleene_tight_diagonal` |
| `hpre : PrecompClosed S d` | f ∘ d is admissible, so hrep applies to it. | tight: counterexample `Toy.Rice.Models.kleene_tight_precompClosed` |

- **Depth:** definitional. Instantiate hrep at f ∘ d and hdiag at e; the same two-step pattern as F1.
- **Non-vacuity witness:** Tag model: codes (b, n), sem = first component, admissible = constants and x ↦ (x.1, m); the diagonal x ↦ (x.1, x.2 + 1) moves every code and is not admissible, and the fixed point produced for x ↦ (x.1, 0) is semantic but not literal. (`Toy.Rice.Models.kleene_nonvacuous`)
- **Related lemmas:** `Toy.Rice.fixpointPrinciple_of_represents_diagonal_precompClosed` (same hypotheses as F3; concludes FixpointPrinciple S (the 'in particular' part of F3)); `Toy.Rice.fixpointPrinciple_of_compClosed_represents_diagonal` (the textbook form: from CompClosed S, Represents S app, IsDiagonal S app d and S.Adm d, concludes FixpointPrinciple S)
- **Does not forbid** any checker design by itself: it derives the fixpoint principle from representability. What follows for checkers follows through R1, R2, R4, R6 and W5 to W7, and partial or one-sided procedures (W8), checkers for decidable fragments (N1, W4), and sound but incomplete checkers (W1, W2) remain possible under those results.
- **Non-claims:** 4 items, listed under Boundaries, *Non-claims by result*, F3.
- **Prior art:**
  - S. C. Kleene, "On notation for ordinal numbers", Journal of Symbolic Logic 3(4) (1938), 150-155, DOI 10.2307/2267778. The first published statement and proof of the (second) recursion theorem, according to Moschovakis (2010).
  - S. C. Kleene, Introduction to Metamathematics, Van Nostrand / North-Holland, 1952. States and proves the recursion theorem and the first recursion theorem (least fixed points of monotone recursive operators); cited without section numbers.
  - Y. N. Moschovakis, "Kleene's amazing second recursion theorem", Bulletin of Symbolic Logic 16(2) (2010), 189-239, DOI 10.2178/bsl/1286889124. Survey of the second recursion theorem and its uses.
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
  - N. S. Yanofsky, "A universal approach to self-referential paradoxes, incompleteness and fixed points", Bulletin of Symbolic Logic 9(3) (2003), 362-386, DOI 10.2178/bsl/1058448677 (arXiv:math/0305282). Derives the recursion theorem from Lawvere's scheme (Theorem 5 in the arXiv text) and proves Rice's theorem with the swapped case split h(x) = a if x is not in A, b if x is in A.
  - uds-psl/coq-synthetic-computability, theories/Basic/Rice.v at commit 7e019a047314a75d90f33899a6ff023a22e9d618: Lemma FP (line 97: every f has e with Θ e ≡ Θ (f e), from an abstract enumerability principle) and Lemma Rice_Theorem' (line 112; the swapped case split is at line 118). The closest existing mechanization of Rice's theorem from an abstract fixed-point lemma; it does not separate an admissible class from the ambient function space. Associated thesis: Y. Forster, Computability in Constructive Type Theory, Saarland University, 2021, DOI 10.22028/D291-35758.
  - Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Computability/PartrecCode.lean: Nat.Partrec.Code.fixed_point (line 1021; documented as "Roger's fixed-point theorem": every total computable f : Code -> Code has c with eval (f c) = eval c) and fixed_point₂ (line 1039; Kleene's second recursion theorem). Prose only.
  - M. Nedzelsky, "Recursion Theory I", Archive of Formal Proofs, April 2008, https://isa-afp.org/entries/Recursion-Theory-I.html; F. J. Balbach, "Some classical results in inductive inference of recursive functions", Archive of Formal Proofs, August 2020, https://www.isa-afp.org/entries/Inductive_Inference.html. Isabelle/HOL mechanizations that include Rice's theorem (Balbach also s-m-n and recursion theorems of Kleene, Rogers and Smullyan).
- **Design question:** addresses which properties of a programming system yield the fixpoint principle. (Instance of the package design question stated in Summary.)

Basis: derived (modeling bridge). For an acceptable numbering φ with Adm = total computable transformers and app e x = the output of φ_e on x, Represents holds, and the s-m-n theorem gives a total computable d with φ_{d x} = φ_{φ_x(x)} when φ_x(x) halts, so the theorem yields Kleene's recursion theorem. *Reasoning:* Standard textbook construction (Rogers 1967; Kleene 1952); not formalized here.

### F4. `Toy.Rice.sem_constant_of_fixpointPrinciple_allSwitchesAdmissible` (and `Toy.Rice.fixpointPrinciple_allAdm_iff_sem_constant_of_nonempty`)

Basis: execution (Lean kernel check)

- **Kind:** theorem. **Tier:** T0. A Cantor/Lawvere-style collapse, immediate from R1; recorded because it explains why Adm must be restricted.
- **Plain claim:** If a system has the fixpoint principle and every switch on every Boolean checker is admissible, then all codes have the same behaviour; consequently, when every transformer is admissible and the code type is nonempty, the fixpoint principle holds exactly when the semantics is constant.

```lean
theorem sem_constant_of_fixpointPrinciple_allSwitchesAdmissible
    (hfix : FixpointPrinciple S) (hall : ∀ chk : S.Code → Bool, SwitchAdmissible S chk) :
    ∀ c d, S.sem c = S.sem d
```

```lean
theorem fixpointPrinciple_allAdm_iff_sem_constant_of_nonempty {C : Type u} {B : Type v}
    (sem : C → B) (hne : Nonempty C) :
    FixpointPrinciple (allAdm sem) ↔ ∀ c d : C, sem c = sem d
```

With the definitions unfolded: `hfix : ∀ f, S.Adm f → ∃ c, S.sem (f c) = S.sem c`; `hall : ∀ chk a b, S.Adm (fun c => cond (chk c) a b)`. In the second theorem `allAdm sem := ⟨C, B, sem, fun _ => True⟩`, so `FixpointPrinciple (allAdm sem)` is `∀ f : C → C, True → ∃ c, sem (f c) = sem c`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfix : FixpointPrinciple S (first theorem)` | Feeds R1. | tight: counterexample `Toy.Rice.Controls.semConst_tight_fixpointPrinciple` |
| `hall : ∀ chk, SwitchAdmissible S chk (first theorem)` | Makes 'same behaviour as c' decided inside. | tight: counterexample `Toy.Rice.Controls.semConst_tight_allSwitches` |
| `hne : Nonempty C (second theorem)` | Constant semantics gives a fixed point only if some code exists. | tight: counterexample `Toy.Rice.Controls.allAdm_tight_nonempty` |

- **Depth:** shallow. R1 applied to the predicate 'same behaviour as c'.
- **Non-vacuity witness:** Constant semantics on Bool with every transformer admissible (both theorems); identity semantics on Bool exercises the false side of the equivalence. (`Toy.Rice.Controls.semConst_nonvacuous`, `Toy.Rice.Controls.allAdm_nonvacuous`)
- **Does not forbid** partial or one-sided procedures, checkers for decidable fragments, or sound but incomplete checkers in systems whose admissible class is restricted: its hypothesis hall makes every switch on every checker admissible, and systems with the fixpoint principle and a restricted admissible class admit one-sided switches (W8), fragment deciders (W4) and sound syntactic checkers (W2, W3).
- **Non-claims:** 3 items, listed under Boundaries, *Non-claims by result*, F4.
- **Prior art:**
  - F. W. Lawvere, "Diagonal arguments and cartesian closed categories", in Category Theory, Homology Theory and their Applications II, Lecture Notes in Mathematics 92, Springer, 1969, 134-145, DOI 10.1007/BFb0080769; reprinted with commentary in Reprints in Theory and Applications of Categories No. 15 (2006), 1-13. Theorem 1.1 (checked in the reprint): in any cartesian closed category, if there is a weakly point-surjective morphism A -> Y^A then Y has the fixed point property; Cantor's theorem follows with Y = 2.
  - Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Logic/Function/Basic.lean: Function.exists_fixed_point_of_surjective (lines 367-368; documented as Lawvere's fixed-point theorem for types and functions) and Function.cantor_surjective (line 374). Prose only.
- **Design question:** addresses why the admissible class must be restricted for a fixpoint principle to say anything. (Instance of the package design question stated in Summary.)

### N1. `Toy.Rice.Tables.tables_no_fixpointPrinciple_and_isZeroFn_decidedInside`

Basis: execution (Lean kernel check)

- **Kind:** counterexample. **Tier:** T1. Folklore (Rice-style arguments need the recursion theorem; weak total formalisms escape them) made precise in a concrete toy system.
- **Plain claim:** In the lookup-table system (codes: finite tables; behaviours: total functions ℕ → ℕ; admissible transformers: those expressible in the total language TProg of constant tables, identity, two table edits, composition, and conditionals on the tests of a small test language TTest), the fixpoint principle fails and the nontrivial extensional predicate 'computes the zero function' is decided inside the system by zeroCheck, which is itself a TTest test.
- **Model:** Codes: List (ℕ × ℕ), first entry wins, default 0. Behaviours: ℕ → ℕ. Adm f := ∃ p : TProg, ∀ x, p.run x = f x. zeroCheck t = TTest.run t (TTest.allEntries (EntryTest.evalAtKeyEq 0)), by rfl (Toy.Rice.Tables.zeroCheck_eq_test).
- **Note:** Existence statement about one concrete system: Tables.sys witnesses that a system can lack the fixpoint principle and decide a nontrivial extensional predicate inside. Nothing follows for other total languages (see the non-claims).

```lean
theorem tables_no_fixpointPrinciple_and_isZeroFn_decidedInside :
    ¬ FixpointPrinciple sys ∧ Extensional sys IsZeroFn ∧ NontrivialPred IsZeroFn ∧
      Decides zeroCheck IsZeroFn ∧ SwitchAdmissible sys zeroCheck
```

The statement is closed. The systems, predicates and checkers it mentions are quoted under *Toy systems (unfolded)* and the generic predicates under *Core definitions (unfolded)*.

Hypotheses: none (a closed statement about concrete systems).

- **Depth:** shallow. The fixpoint failure is immediate (incrAt 0 changes the value at 0); correctness of zeroCheck is a short induction. Toy.Rice.Tables.tail_not_admissible shows the admissible class is proper. Further checkers and predicates are covered by Toy.Rice.Tables.allOutputsZero_switchAdmissible (every switch on the syntactic checker allOutputsZero t = t.all (fun p => p.2 == 0), 'every stored value is 0', is admissible), Toy.Rice.Tables.evalAtZero_decidedInside (the pointwise predicate 'the value at 0 is 0' is decided inside) and Toy.Rice.Tables.isNil_decidedInside (the syntactic predicate 'the table is empty' is decided inside).
- **Non-vacuity witness:** The statement is closed and concrete. (`Toy.Rice.Tables.tables_no_fixpointPrinciple_and_isZeroFn_decidedInside`)
- **What it does not forbid:** Is itself an example of what Rice-style results do not forbid: an internal decider for a nontrivial extensional predicate in a total language without the fixpoint principle. It does not show that such a decider exists for an expressive total language (see the primitive-recursive modeling bridge), and it says nothing for or against partial or semi-decision procedures or sound but incomplete checkers, which are not needed here because the predicate is decided.
- **Non-claims:** 5 items, listed under Boundaries, *Non-claims by result*, N1.
- **Prior art:**
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
  - S. C. Kleene, Introduction to Metamathematics, Van Nostrand / North-Holland, 1952. States and proves the recursion theorem and the first recursion theorem (least fixed points of monotone recursive operators); cited without section numbers.
  - A. R. Meyer and D. M. Ritchie, "The complexity of loop programs", Proceedings of the ACM National Conference 1967, 465-469, DOI 10.1145/800196.806014. Theorem 7: the functions computable by Loop programs are exactly the primitive recursive functions. (Cited only for that fact.)
- **Design question:** addresses checkers for total sublanguages: dropping the fixpoint principle can make a nontrivial behavioural property decided inside the system. (Instance of the package design question stated in Summary.)

Basis: derived (modeling bridge). For primitive-recursive programs, 'computes the zero function' is not decidable in the classical sense: no total computable procedure decides it on program indices. *Reasoning:* By Kleene's normal form theorem the predicate T(e, x, s) ('machine e on input x halts within s steps') is primitive recursive, so f_e(s) = 1 if T(e, e, s) else 0 is primitive recursive, uniformly in e, and f_e is the zero function iff machine e does not halt on input e. A decider for 'computes the zero function' on primitive-recursive programs would therefore decide the complement of the halting problem (standard; see Kleene 1952 and Rogers 1967). Not formalized here.

### N2. `Toy.Rice.Flat.flat_fixpointPrinciple_and_halts_not_decidedInside`

Basis: execution (Lean kernel check)

- **Kind:** impossibility. **Tier:** T0. A concrete instance of R1 in a three-point flat domain; the fixpoint principle there is the least-fixed-point argument behind Kleene's first recursion theorem.
- **Plain claim:** In the flat-domain system (codes and behaviours are the three denotations 'diverges', 'returns true', 'returns false'; sem is the identity; admissible transformers are the monotone maps), the fixpoint principle holds, halting is extensional and nontrivial, and halting is not decided inside the system.
- **Note:** Existence statement about one concrete system: Flat.sys witnesses that the fixpoint principle, a nontrivial extensional predicate, and the failure to decide it inside occur together. It is not a statement about other systems.

```lean
theorem flat_fixpointPrinciple_and_halts_not_decidedInside :
    FixpointPrinciple sys ∧ Extensional sys Halts ∧ NontrivialPred Halts ∧
      ¬ DecidedInside sys Halts
```

The statement is closed. The systems, predicates and checkers it mentions are quoted under *Toy systems (unfolded)* and the generic predicates under *Core definitions (unfolded)*.

Hypotheses: none (a closed statement about concrete systems).

- **Depth:** shallow. Every monotone map on the three-point flat domain has a fixed point (iterate from bot); then R1.
- **Non-vacuity witness:** Closed concrete statement. (`Toy.Rice.Flat.flat_fixpointPrinciple_and_halts_not_decidedInside`)
- **Positive control:** `Toy.Rice.Tables.tables_no_fixpointPrinciple_and_isZeroFn_decidedInside`: N1: without the fixpoint principle, the lookup-table system decides a nontrivial extensional predicate inside.
- **Does not forbid**: (i) partial or one-sided procedures: in this same system the one-sided switch 'if the program halts then return true, else diverge' is admissible (W8); semi-decision itself is not formalized; (ii) checkers for decidable fragments: the two-element total fragment of this system decides every predicate (Toy.Rice.Flat.totalSys_decides_every_predicate), a degenerate case recorded as Toy.Rice.Examples.restrict_degenerate_flat; (iii) sound but incomplete checkers: the statement concerns deciders only; because the only switch-admissible checkers here are constant (Toy.Rice.Flat.switchAdmissible_const), a sound switch-admissible checker for halting can only be the one that rejects everything.
- **Non-claims:** 6 items, listed under Boundaries, *Non-claims by result*, N2.
- **Prior art:**
  - S. C. Kleene, Introduction to Metamathematics, Van Nostrand / North-Holland, 1952. States and proves the recursion theorem and the first recursion theorem (least fixed points of monotone recursive operators); cited without section numbers.
  - H. G. Rice, "Classes of recursively enumerable sets and their decision problems", Transactions of the American Mathematical Society 74(2) (1953), 358-366, DOI 10.1090/S0002-9947-1953-0053041-6. The original theorem: an index set of r.e. sets is recursive only if it is trivial.
- **Design question:** addresses a concrete system where the hypotheses of R1 hold. (Instance of the package design question stated in Summary.)

### N3. `Toy.Rice.Controls.converse_fails_constClosed_compClosed_noFixpoint_nothingNontrivialDecided`

Basis: execution (Lean kernel check)

- **Kind:** counterexample. **Tier:** T0. Elementary boundary fact recorded to block the converse reading of R1.
- **Plain claim:** The system on ℕ with identity semantics whose admissible transformers are the constants and the shifts n ↦ n + k contains every constant, is closed under composition, and lacks the fixpoint principle, and yet decides no nontrivial predicate inside (every predicate is extensional here).
- **Note:** Existence statement about one concrete system: natShiftSys witnesses that ConstClosed, CompClosed and the failure of the fixpoint principle are consistent with deciding nothing nontrivial inside. It does not characterize such systems.

```lean
theorem converse_fails_constClosed_compClosed_noFixpoint_nothingNontrivialDecided :
    ConstClosed natShiftSys ∧ CompClosed natShiftSys ∧ ¬ FixpointPrinciple natShiftSys ∧
      (∀ P : Nat → Prop, Extensional natShiftSys P) ∧
      ∀ P : Nat → Prop, NontrivialPred P → ¬ DecidedInside natShiftSys P
```

The statement is closed. The systems, predicates and checkers it mentions are quoted under *Toy systems (unfolded)* and the generic predicates under *Core definitions (unfolded)*.

Hypotheses: none (a closed statement about concrete systems).

- **Depth:** shallow. The shift by one has no fixed point; a switch with branches 0 and 1 is neither constant nor a shift unless the checker is constant.
- **Non-vacuity witness:** Closed concrete statement. (`Toy.Rice.Controls.converse_fails_constClosed_compClosed_noFixpoint_nothingNontrivialDecided`)
- **Does not forbid** anything: it shows that losing the fixpoint principle does not by itself make anything nontrivial decided inside. It says nothing about partial or semi-decision procedures, checkers for decidable fragments, or sound but incomplete checkers.
- **Non-claims:** 3 items, listed under Boundaries, *Non-claims by result*, N3.
- **Prior art:**
  - None cited: an elementary boundary fact.
- **Design question:** addresses why the converse reading ('no fixpoint principle, so something nontrivial is decided inside') is wrong. (Instance of the package design question stated in Summary.)

### W1. `Toy.Rice.rejectAll_sound_switchAdmissible_of_constClosed`

Basis: execution (Lean kernel check)

- **Kind:** theorem. **Tier:** T0. Trivial reference point for the sound-but-incomplete checkers part of the design question.
- **Plain claim:** If every constant transformer is admissible, the checker that rejects every code is sound for every predicate and is switch-admissible.

```lean
theorem rejectAll_sound_switchAdmissible_of_constClosed (hconst : ConstClosed S)
    (P : S.Code → Prop) :
    SoundFor (fun _ : S.Code => false) P ∧ SwitchAdmissible S (fun _ : S.Code => false)
```

With the definitions unfolded: `hconst : ∀ k, S.Adm (fun _ => k)`; the conclusion is `(∀ c, false = true → P c) ∧ ∀ a b, S.Adm (fun c => cond false a b)`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hconst : ConstClosed S` | The switches of a constant checker are constant transformers. | tight: counterexample `Toy.Rice.Controls.rejectAll_tight_constClosed` |

- **Depth:** definitional. Unfolding.
- **Non-vacuity witness:** Padded system (which also has the fixpoint principle). (`Toy.Rice.Controls.rejectAll_nonvacuous`)
- **What it does not forbid:** Is itself a (trivially) sound but incomplete checker, which Rice-style results do not forbid. It does not show that useful sound checkers exist (W2 does, for a syntactic subclass), and it says nothing about partial or semi-decision procedures (W8) or checkers for decidable fragments (N1, W4).
- **Non-claims:** 4 items, listed under Boundaries, *Non-claims by result*, W1.
- **Prior art:**
  - P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, 238-252, DOI 10.1145/512950.512973. Foundational framework for sound but incomplete static analyzers; cited as context for the design space, not for any statement here.
- **Design question:** addresses the fact that sound-but-incomplete checkers always exist (base case). (Instance of the package design question stated in Summary.)

### W2. `Toy.Rice.Padded.padded_litTrueCheck_sound_infinite_incomplete`

Basis: execution (Lean kernel check)

- **Kind:** theorem. **Tier:** T1. Folklore (sound checkers for syntactic subclasses exist despite Rice) made precise in a toy system where Rice applies.
- **Plain claim:** In the padded system, which has the fixpoint principle, the predicate 'the behaviour is true' is extensional, nontrivial and not decided inside the system; yet the checker 'the code is a literal true program' is switch-admissible and sound for it, accepts the infinitely many codes lit true n, and rejects every hidden code hid true n although those satisfy the predicate.
- **Note:** Existence statement about one concrete system: Padded.sys witnesses that the fixpoint principle is consistent with a sound, switch-admissible checker that accepts infinitely many codes but is incomplete for a predicate that is not decided inside. It is not a statement about other systems.

```lean
theorem padded_litTrueCheck_sound_infinite_incomplete :
    FixpointPrinciple sys ∧ Extensional sys BehTrue ∧ NontrivialPred BehTrue ∧
      ¬ DecidedInside sys BehTrue ∧
      SoundFor litTrueCheck BehTrue ∧ SwitchAdmissible sys litTrueCheck ∧
      (∀ n, litTrueCheck (lit true n) = true) ∧
      (∀ n, BehTrue (hid true n) ∧ litTrueCheck (hid true n) = false)
```

The statement is closed. The systems, predicates and checkers it mentions are quoted under *Toy systems (unfolded)* and the generic predicates under *Core definitions (unfolded)*.

Hypotheses: none (a closed statement about concrete systems).

- **Depth:** shallow. The fixpoint principle holds by a fresh-padding obliviousness argument (hidden codes outside a finite exception set are seen only through their visible part); the rest is unfolding.
- **Non-vacuity witness:** Closed concrete statement. (`Toy.Rice.Padded.padded_litTrueCheck_sound_infinite_incomplete`)
- **What it does not forbid:** Is itself a sound but incomplete checker that accepts infinitely many codes, which Rice-style results do not forbid. It says nothing about partial or semi-decision procedures (W8) or checkers for decidable fragments (N1, W4).
- **Non-claims:** 5 items, listed under Boundaries, *Non-claims by result*, W2.
- **Prior art:**
  - P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, 238-252, DOI 10.1145/512950.512973. Foundational framework for sound but incomplete static analyzers; cited as context for the design space, not for any statement here.
- **Design question:** addresses the fact that nontrivial sound checkers for a syntactic subclass exist despite Rice. (Instance of the package design question stated in Summary.)

### W3. `Toy.Rice.Padded.padded_fixpointPrinciple_and_evenPad_decidedInside`

Basis: execution (Lean kernel check)

- **Kind:** theorem. **Tier:** T1. Folklore (syntactic properties are not covered by Rice) made precise in a toy system where Rice applies.
- **Plain claim:** In the padded system, which has the fixpoint principle, the nontrivial non-extensional predicate 'the padding is even' is decided inside the system by evenPadCheck.
- **Note:** Existence statement about one concrete system: Padded.sys witnesses that a nontrivial non-extensional predicate can be decided inside a system with the fixpoint principle. It is not a statement about other systems.

```lean
theorem padded_fixpointPrinciple_and_evenPad_decidedInside :
    FixpointPrinciple sys ∧ ¬ Extensional sys EvenPad ∧ NontrivialPred EvenPad ∧
      Decides evenPadCheck EvenPad ∧ SwitchAdmissible sys evenPadCheck
```

The statement is closed. The systems, predicates and checkers it mentions are quoted under *Toy systems (unfolded)* and the generic predicates under *Core definitions (unfolded)*.

Hypotheses: none (a closed statement about concrete systems).

- **Depth:** shallow. evenPadCheck reads only the visible part of a code, so its switches are admissible.
- **Non-vacuity witness:** Closed concrete statement. (`Toy.Rice.Padded.padded_fixpointPrinciple_and_evenPad_decidedInside`)
- **What it does not forbid:** Is itself a decider for a non-extensional (syntactic) predicate, which Rice-style results do not forbid. It says nothing about partial or semi-decision procedures (W8), checkers for decidable fragments (N1, W4), or sound but incomplete checkers for extensional predicates (W1, W2, W5).
- **Non-claims:** 4 items, listed under Boundaries, *Non-claims by result*, W3.
- **Prior art:**
  - None cited: a toy construction.
- **Design question:** addresses why syntactic checks are outside Rice's scope. (Instance of the package design question stated in Summary.)

### W4. `Toy.Rice.Lifted.lifted_haltsZero_decidedInside_haltingFragment_not_full`

Basis: execution (Lean kernel check)

- **Kind:** theorem. **Tier:** T1. Folklore (checkers for total sublanguages escape Rice) made precise, together with the condition under which the escape works (see R6).
- **Plain claim:** In the lifted lookup-table system (codes: table programs plus one divergent program; admissible transformers: constants and strict extensions of TProg programs), which has the fixpoint principle and is not closed under literal code-equality tests, the halting fragment is closed under same behaviour, has a proper admissible class and no fixpoint principle, and decides inside it, by fragCheck (which runs zeroCheck on the underlying table), the property 'halts and computes the zero function', which is extensional and nontrivial on the fragment; in the full system that property is extensional, nontrivial and not decided inside.
- **Model:** Codes: Option Table (none = the divergent program). Behaviours: Option (ℕ → ℕ), sem = Option.map eval. Adm f: f is constant, or f none = none and f (some t) = some (p.run t) for some TProg program p. totalSys = sys.restrict Halts is the halting fragment {c // c.isSome = true}. fragCheck ⟨some t, _⟩ = zeroCheck t: on a fragment code it runs zeroCheck on the underlying table (the none case is unreachable). All definitions are quoted under Toy systems (unfolded).
- **Note:** Existence statement about one concrete system: Lifted.sys and its halting fragment Lifted.totalSys witness that there is a system with the fixpoint principle, not closed under code-equality tests, whose behaviour-closed halting fragment decides inside a property that is extensional and nontrivial on the fragment and is not decided inside the full system. It does not say that every such system, or every behaviour-closed fragment, behaves this way.

```lean
theorem lifted_haltsZero_decidedInside_haltingFragment_not_full :
    FixpointPrinciple sys ∧ ¬ FixpointPrinciple totalSys ∧
      ¬ (∀ g : totalSys.Code → totalSys.Code, totalSys.Adm g) ∧
      Extensional sys Halts ∧
      Extensional totalSys (fun x => HaltsZero x.val) ∧
      NontrivialPred (fun x : totalSys.Code => HaltsZero x.val) ∧
      Decides fragCheck (fun x => HaltsZero x.val) ∧ SwitchAdmissible totalSys fragCheck ∧
      Extensional sys HaltsZero ∧ NontrivialPred HaltsZero ∧ ¬ DecidedInside sys HaltsZero ∧
      ¬ EqTestClosed sys
```

The statement is closed. The systems, predicates and checkers it mentions are quoted under *Toy systems (unfolded)* and the generic predicates under *Core definitions (unfolded)*.

Hypotheses: none (a closed statement about concrete systems).

- **Depth:** shallow. The full-system extension of each fragment switch is strict (maps the divergent code to itself), hence admissible.
- **Non-vacuity witness:** Closed concrete statement. (`Toy.Rice.Lifted.lifted_haltsZero_decidedInside_haltingFragment_not_full`)
- **Related lemmas:** `Toy.Rice.Lifted.switchAdmissible_const` (every switch-admissible checker of the full system Lifted.sys is constant: SwitchAdmissible sys chk → (∀ c, chk c = true) ∨ (∀ c, chk c = false)); `Toy.Rice.Lifted.not_decidedInside_of_nontrivial` (every nontrivial predicate on Option Table is not decided inside the full system Lifted.sys); `Toy.Rice.Lifted.isEmptyTable_not_decidedInside` (the syntactic predicate fun c => c = some [] ('the code is the empty table') is not decided inside Lifted.sys); `Toy.Rice.Lifted.not_eqTestClosed` (¬ EqTestClosed Lifted.sys, the last conjunct of W4 as a separate lemma)
- **What it does not forbid:** Is itself a checker for a decidable fragment, which Rice-style results do not forbid when the system's transformers cannot test code equality (compare R6). It says nothing about partial or semi-decision procedures (not formalized; compare W8) or about sound but incomplete checkers on the full system beyond the degeneracy that only constant checkers are switch-admissible there (Toy.Rice.Lifted.switchAdmissible_const).
- **Non-claims:** 6 items, listed under Boundaries, *Non-claims by result*, W4.
- **Prior art:**
  - S. C. Kleene, "A symmetric form of Gödel's theorem", Proceedings of the KNAW 53 (1950), 800-802; also Indagationes Mathematicae 12 (1950), 244-246; no DOI; KNAW Digital Library record PU00014670, https://dwc.knaw.nl/DL/publications/PU00014670.pdf (a scan of Proceedings volume 53, Nos. 6-10, pp. 685-1656, containing the article at pp. 800-802). Constructs two disjoint r.e. sets that no recursive set separates (recursive inseparability).
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
- **Design question:** addresses checkers for restricted fragments, and the mechanism that makes them possible. (Instance of the package design question stated in Summary.)

### W5. `Toy.Rice.forall_exists_sameSem_rejected_of_fixpointPrinciple_extensional_violated_sound_switchAdmissible`

Basis: execution (Lean kernel check)

- **Kind:** impossibility. **Tier:** T1. Folklore ('every sound analyzer is incomplete') made precise. The per-behaviour form (every realizable behaviour contains a rejected code) follows from the same single switch; we did not locate it stated in this form in the sources checked and claim no novelty.
- **Plain claim:** In a system with the fixpoint principle, let chk be switch-admissible and sound for an extensional predicate P that some code violates. Then every realizable behaviour (the behaviour of some code) has a code that chk rejects: for every code a there is a code c with sem c = sem a and chk c = false. In particular every code satisfying P, and every accepted code, has a rejected code with the same behaviour.

```lean
theorem forall_exists_sameSem_rejected_of_fixpointPrinciple_extensional_violated_sound_switchAdmissible
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    (hviol : ∃ b, ¬ P b) {chk : S.Code → Bool} (hsound : SoundFor chk P)
    (hsw : SwitchAdmissible S chk) :
    ∀ a, ∃ c, S.sem c = S.sem a ∧ chk c = false
```

With the definitions unfolded: `hfix : ∀ f, S.Adm f → ∃ c, S.sem (f c) = S.sem c`, `hext : ∀ c d, S.sem c = S.sem d → (P c ↔ P d)`, `hviol : ∃ b, ¬ P b`, `hsound : ∀ c, chk c = true → P c`, `hsw : ∀ a b, S.Adm (fun c => cond (chk c) a b)`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfix : FixpointPrinciple S` | Semantic fixed point of the switch c ↦ if chk c then b else a. | tight: counterexample `Toy.Rice.Controls.incompleteAll_tight_fixpointPrinciple` |
| `hext : Extensional S P` | Transfers P from the fixed point to b. | tight: counterexample `Toy.Rice.Controls.incompleteAll_tight_extensional` |
| `hviol : ∃ b, ¬ P b` | The branch taken on acceptance. | tight: counterexample `Toy.Rice.Controls.incompleteAll_tight_violated` |
| `hsound : SoundFor chk P` | An accepted fixed point would satisfy P. | tight: counterexample `Toy.Rice.Controls.incompleteAll_tight_sound` |
| `hsw : SwitchAdmissible S chk` | Admissibility of the switch. | tight: counterexample `Toy.Rice.Controls.incompleteAll_tight_switchAdmissible` |

- **Depth:** shallow. One switch per behaviour, one fixpoint application, one case split; no classical reasoning (axiom audit: propext only).
- **Non-vacuity witness:** Padded system, BehTrue, litTrueCheck. (`Toy.Rice.Controls.incompleteAll_nonvacuous`)
- **Positive control:** `Toy.Rice.Controls.incompleteAll_tight_fixpointPrinciple`: in the lookup-table system `zeroCheck` is sound and switch-admissible for the extensional `IsZeroFn`, which some code violates, yet the behaviour of some code has no rejected code.
- **Related lemmas:** `Toy.Rice.exists_satisfying_rejected_of_fixpointPrinciple_extensional_nontrivial_sound_switchAdmissible` (from FixpointPrinciple S, Extensional S P, NontrivialPred P, SoundFor chk P and SwitchAdmissible S chk, concludes ∃ c, P c ∧ chk c = false (some code satisfying P is rejected)); `Toy.Rice.exists_sameSem_rejected_of_fixpointPrinciple_extensional_sound_swappedSwitch` (the single-switch core of W5: from FixpointPrinciple S, Extensional S P, SoundFor chk P, ¬ P b and S.Adm (switch chk b a), concludes ∃ c, S.sem c = S.sem a ∧ chk c = false); `Toy.Rice.forall_exists_sameSem_accepted_of_fixpointPrinciple_extensional_satisfied_complete_switchAdmissible` (the dual of W5 for complete checkers: from FixpointPrinciple S, Extensional S P, ∃ a, P a, CompleteFor chk P and SwitchAdmissible S chk, concludes ∀ b, ∃ c, S.sem c = S.sem b ∧ chk c = true)
- **Does not forbid**: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers themselves: W5 presupposes such a checker and describes its incompleteness; such checkers exist (W1, W2).
- **Non-claims:** 7 items, listed under Boundaries, *Non-claims by result*, W5.
- **Prior art:**
  - H. G. Rice, "Classes of recursively enumerable sets and their decision problems", Transactions of the American Mathematical Society 74(2) (1953), 358-366, DOI 10.1090/S0002-9947-1953-0053041-6. The original theorem: an index set of r.e. sets is recursive only if it is trivial.
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
  - P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, 238-252, DOI 10.1145/512950.512973. Foundational framework for sound but incomplete static analyzers; cited as context for the design space, not for any statement here.
- **Design question:** addresses the precise incompleteness of every sound internal checker. (Instance of the package design question stated in Summary.)

### W6. `Toy.Rice.exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible`

Basis: execution (Lean kernel check)

- **Kind:** impossibility. **Tier:** T1. Folklore (internal checkers cannot be exactly behavioural) made precise in a localized form; not located in this form in the sources checked; no novelty claimed.
- **Plain claim:** In a system with the fixpoint principle, every switch-admissible checker chk has the following property: for any codes a and b, chk rejects some code with the behaviour of a or accepts some code with the behaviour of b. Consequently (and, classically, equivalently) no realizable behaviour (the behaviour of some code) has all its codes accepted while a realizable behaviour has all its codes rejected.

```lean
theorem exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible
    (hfix : FixpointPrinciple S) {chk : S.Code → Bool} (hsw : SwitchAdmissible S chk) :
    ∀ a b, (∃ c, S.sem c = S.sem a ∧ chk c = false) ∨ (∃ c, S.sem c = S.sem b ∧ chk c = true)
```

With the definitions unfolded: `hfix : ∀ f, S.Adm f → ∃ c, S.sem (f c) = S.sem c`, `hsw : ∀ a b, S.Adm (fun c => cond (chk c) a b)`. The conclusion uses no package definitions.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfix : FixpointPrinciple S` | Semantic fixed point of the switch c ↦ if chk c then b else a. | tight: counterexample `Toy.Rice.Controls.splitAll_tight_fixpointPrinciple` |
| `hsw : SwitchAdmissible S chk` | Admissibility of that switch. | tight: counterexample `Toy.Rice.Controls.splitAll_tight_switchAdmissible` |

- **Depth:** shallow. One fixpoint application per pair of codes; no classical reasoning.
- **Non-vacuity witness:** Padded system, litTrueCheck, which takes both verdicts. (`Toy.Rice.Controls.splitAll_nonvacuous`)
- **Positive control:** `Toy.Rice.Controls.splitAll_tight_fixpointPrinciple`: in the lookup-table system `zeroCheck` is switch-admissible, yet for some codes `a b` it rejects no code with the behaviour of `a` and accepts no code with the behaviour of `b`.
- **Related lemmas:** `Toy.Rice.exists_sameSem_accepted_rejected_of_fixpointPrinciple_switchAdmissible` (from FixpointPrinciple S, SwitchAdmissible S chk, ∃ c, chk c = true and ∃ d, chk d = false, concludes ∃ c d, S.sem c = S.sem d ∧ chk c = true ∧ chk d = false); `Toy.Rice.not_forall_sameSem_accepted_and_forall_sameSem_rejected_of_fixpointPrinciple_switchAdmissible` (the negative form of W6: from FixpointPrinciple S and SwitchAdmissible S chk, for all codes a b, ¬ ((∀ c, S.sem c = S.sem a → chk c = true) ∧ (∀ c, S.sem c = S.sem b → chk c = false))); `Toy.Rice.sameSem_split_iff_not_forall_sameSem_accepted_and_forall_sameSem_rejected` (for every chk, a, b (no hypotheses), W6's disjunction is equivalent, using classical logic, to that negative form)
- **Does not forbid**: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers: W6 constrains only how verdicts split across behaviours; sound but incomplete checkers exist in systems with the fixpoint principle (W1, W2).
- **Non-claims:** 6 items, listed under Boundaries, *Non-claims by result*, W6.
- **Prior art:**
  - H. G. Rice, "Classes of recursively enumerable sets and their decision problems", Transactions of the American Mathematical Society 74(2) (1953), 358-366, DOI 10.1090/S0002-9947-1953-0053041-6. The original theorem: an index set of r.e. sets is recursive only if it is trivial.
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
- **Design question:** addresses why internal checkers cannot be exactly behavioural. (Instance of the package design question stated in Summary.)

### W7. `Toy.Rice.exists_sameSem_satisfying_accepted_rejected_of_fixpointPrinciple_extensional_sound_switchAdmissible`

Basis: execution (Lean kernel check)

- **Kind:** impossibility. **Tier:** T0. Immediate from W6 and soundness.
- **Plain claim:** In a system with the fixpoint principle, a switch-admissible checker that is sound for an extensional predicate P, accepts some code and rejects some code gives different verdicts on two codes with the same behaviour, both satisfying P.

```lean
theorem exists_sameSem_satisfying_accepted_rejected_of_fixpointPrinciple_extensional_sound_switchAdmissible
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    {chk : S.Code → Bool} (hsound : SoundFor chk P) (hsw : SwitchAdmissible S chk)
    (hacc : ∃ c, chk c = true) (hrej : ∃ d, chk d = false) :
    ∃ c d, S.sem c = S.sem d ∧ P c ∧ P d ∧ chk c = true ∧ chk d = false
```

With the definitions unfolded: `hfix : ∀ f, S.Adm f → ∃ c, S.sem (f c) = S.sem c`, `hext : ∀ c d, S.sem c = S.sem d → (P c ↔ P d)`, `hsound : ∀ c, chk c = true → P c`, `hsw : ∀ a b, S.Adm (fun c => cond (chk c) a b)`, `hacc : ∃ c, chk c = true`, `hrej : ∃ d, chk d = false`.

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfix : FixpointPrinciple S` | Via W6. | tight: counterexample `Toy.Rice.Controls.soundSplit_tight_fixpointPrinciple` |
| `hext : Extensional S P` | Transfers P to the rejected code. | tight: counterexample `Toy.Rice.Controls.soundSplit_tight_extensional` |
| `hsound : SoundFor chk P` | The accepted code satisfies P. | tight: counterexample `Toy.Rice.Controls.soundSplit_tight_sound` |
| `hsw : SwitchAdmissible S chk` | Via W6. | tight: counterexample `Toy.Rice.Controls.soundSplit_tight_switchAdmissible` |
| `hacc : ∃ c, chk c = true` | An accepted code (the reject-all checker is sound and never splits). | tight: counterexample `Toy.Rice.Controls.soundSplit_tight_accepts` |
| `hrej : ∃ d, chk d = false` | A rejected code. | tight: counterexample `Toy.Rice.Controls.soundSplit_tight_rejects` |

- **Depth:** definitional. W6 plus soundness and extensionality.
- **Non-vacuity witness:** Padded system, BehTrue, litTrueCheck. (`Toy.Rice.Controls.soundSplit_nonvacuous`)
- **Positive control:** `Toy.Rice.Controls.soundSplit_tight_fixpointPrinciple`: in the lookup-table system `zeroCheck` is sound for `IsZeroFn`, switch-admissible, accepts some code and rejects some code, yet no two codes with the same behaviour that both satisfy `IsZeroFn` receive different verdicts.
- **Does not forbid**: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers themselves: W7 presupposes such a checker and describes how it splits a behaviour; such checkers exist (W1, W2).
- **Non-claims:** 4 items, listed under Boundaries, *Non-claims by result*, W7.
- **Prior art:**
  - H. G. Rice, "Classes of recursively enumerable sets and their decision problems", Transactions of the American Mathematical Society 74(2) (1953), 358-366, DOI 10.1090/S0002-9947-1953-0053041-6. The original theorem: an index set of r.e. sets is recursive only if it is trivial.
  - H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
- **Design question:** addresses the form of incompleteness for sound checkers without nontriviality. (Instance of the package design question stated in Summary.)

### W8. `Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside`

Basis: execution (Lean kernel check)

- **Kind:** theorem. **Tier:** T0. Toy counterpart of the classical fact that halting is semi-decidable but not decidable, in the classical computability sense, which is not formalized here (Mathlib: ComputablePred.halting_problem_re, ComputablePred.halting_problem).
- **Plain claim:** In the flat-domain system, which has the fixpoint principle, the one-sided switch 'if the program halts then return true, else diverge' is admissible, while halting is not decided inside the system.
- **Note:** Existence statement about one concrete system: Flat.sys witnesses that a one-sided switch can be admissible in a system with the fixpoint principle while the predicate is not decided inside. It is not a statement about other systems.

```lean
theorem halts_unswappedSwitch_admissible_not_decidedInside :
    FixpointPrinciple sys ∧ sys.Adm (switch haltCheck .tt .bot) ∧ ¬ DecidedInside sys Halts
```

The statement is closed. The systems, predicates and checkers it mentions are quoted under *Toy systems (unfolded)* and the generic predicates under *Core definitions (unfolded)*.

Hypotheses: none (a closed statement about concrete systems).

- **Depth:** definitional. The one-sided switch maps bot to bot, hence is monotone.
- **Non-vacuity witness:** Closed concrete statement. (`Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside`)
- **What it does not forbid:** Shows that one-sided procedures are not forbidden here: the one-sided halting switch is admissible in a system with the fixpoint principle. It does not define or characterize semi-decision, and it says nothing about checkers for decidable fragments (N1, W4) or sound but incomplete checkers (W1, W2).
- **Non-claims:** 3 items, listed under Boundaries, *Non-claims by result*, W8.
- **Prior art:**
  - Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Computability/Halting.lean: ComputablePred.halting_problem_re (line 60: the halting predicate is r.e.) and ComputablePred.halting_problem (line 64: it is not computable). Prose only.
  - H. G. Rice, "On completely recursively enumerable classes and their key arrays", Journal of Symbolic Logic 21(3) (1956), 304-308, DOI 10.2307/2269105. With Myhill and Shepherdson (1955), the source of the Rice-Shapiro characterization of semi-decidable extensional properties, which this package does not formalize.
  - J. Myhill and J. C. Shepherdson, "Effective operations on partial recursive functions", Zeitschrift für mathematische Logik und Grundlagen der Mathematik 1(4) (1955), 310-317, DOI 10.1002/malq.19550010407.
- **Design question:** addresses why semi-decision is a different question. (Instance of the package design question stated in Summary.)

### Statements of the tightness counterexamples, non-vacuity witnesses and positive controls


Each section lists the tightness counterexamples, then the non-vacuity witness. A positive control that is also a tightness counterexample of the same result is listed once.

#### For R1

```lean
theorem rice_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ NontrivialPred Tables.IsZeroFn ∧
      DecidedInside Tables.sys Tables.IsZeroFn
```

```lean
theorem rice_tight_extensional :
    FixpointPrinciple Padded.sys ∧ NontrivialPred Padded.EvenPad ∧
      DecidedInside Padded.sys Padded.EvenPad
```

```lean
theorem rice_tight_nontrivial_hasMember :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => False) ∧
      (∃ _ : Padded.Code, ¬ False) ∧ DecidedInside Padded.sys (fun _ => False)
```

```lean
theorem rice_tight_nontrivial_hasNonMember :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => True) ∧
      (∃ _ : Padded.Code, True) ∧ DecidedInside Padded.sys (fun _ => True)
```

```lean
theorem rice_nonvacuous :
    (FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      NontrivialPred Padded.BehTrue) ∧
    (FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧ NontrivialPred Flat.Halts)
```

#### For R2

```lean
theorem riceSharp_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ Decides Tables.zeroCheck Tables.IsZeroFn ∧
      Tables.IsZeroFn [] ∧ ¬ Tables.IsZeroFn [(0, 1)] ∧
      Tables.sys.Adm (switch Tables.zeroCheck [(0, 1)] [])
```

```lean
theorem riceSharp_tight_extensional :
    FixpointPrinciple Padded.sys ∧ Decides Padded.evenPadCheck Padded.EvenPad ∧
      Padded.EvenPad (.hid true 0) ∧ ¬ Padded.EvenPad (.hid true 1) ∧
      Padded.sys.Adm (switch Padded.evenPadCheck (.hid true 1) (.hid true 0))
```

```lean
theorem riceSharp_tight_decides :
    FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧
      Flat.Halts Flat.Flat.tt ∧ ¬ Flat.Halts Flat.Flat.bot ∧
      Flat.sys.Adm (switch (fun _ => false) Flat.Flat.bot Flat.Flat.tt)
```

```lean
theorem riceSharp_tight_member :
    FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧
      Decides Flat.haltCheck Flat.Halts ∧ ¬ Flat.Halts Flat.Flat.bot ∧
      Flat.sys.Adm (switch Flat.haltCheck Flat.Flat.bot Flat.Flat.bot)
```

```lean
theorem riceSharp_tight_nonmember :
    FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧
      Decides Flat.haltCheck Flat.Halts ∧ Flat.Halts Flat.Flat.tt ∧
      Flat.sys.Adm (switch Flat.haltCheck Flat.Flat.tt Flat.Flat.tt)
```

```lean
theorem riceSharp_nonvacuous :
    FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧
      Decides Flat.haltCheck Flat.Halts ∧ Flat.Halts Flat.Flat.tt ∧
      ¬ Flat.Halts Flat.Flat.bot
```

#### For R4

```lean
theorem riceChar_tight_fixpointPrinciple :
    ConstClosed Tables.sys ∧ Extensional Tables.sys Tables.IsZeroFn ∧
      ¬ (DecidedInside Tables.sys Tables.IsZeroFn ↔
          (∀ c, Tables.IsZeroFn c) ∨ (∀ c, ¬ Tables.IsZeroFn c))
```

```lean
theorem riceChar_tight_constClosed :
    FixpointPrinciple emptyAdmSys ∧ Extensional emptyAdmSys (fun _ => True) ∧
      ¬ (DecidedInside emptyAdmSys (fun _ => True) ↔
          (∀ _ : Bool, True) ∨ (∀ _ : Bool, ¬ True))
```

```lean
theorem riceChar_tight_extensional :
    FixpointPrinciple Padded.sys ∧ ConstClosed Padded.sys ∧
      ¬ (DecidedInside Padded.sys Padded.EvenPad ↔
          (∀ c, Padded.EvenPad c) ∨ (∀ c, ¬ Padded.EvenPad c))
```

```lean
theorem riceChar_nonvacuous :
    FixpointPrinciple Padded.sys ∧ ConstClosed Padded.sys ∧
      (Extensional Padded.sys (fun _ => True) ∧ DecidedInside Padded.sys (fun _ => True) ∧
        ((∀ _ : Padded.Code, True) ∨ (∀ _ : Padded.Code, ¬ True))) ∧
      (Extensional Padded.sys Padded.BehTrue ∧ ¬ DecidedInside Padded.sys Padded.BehTrue ∧
        ¬ ((∀ c, Padded.BehTrue c) ∨ (∀ c, ¬ Padded.BehTrue c)))
```

#### For R6

```lean
theorem restrict_tight_fixpointPrinciple :
    EqTestClosed (allAdm (id : Bool → Bool)) ∧
      Extensional (allAdm (id : Bool → Bool)) (fun _ => True) ∧
      Extensional ((allAdm (id : Bool → Bool)).restrict (fun _ => True)) (fun x => x.val = true) ∧
      NontrivialPred (fun x : Subtype (fun _ : Bool => True) => x.val = true) ∧
      DecidedInside ((allAdm (id : Bool → Bool)).restrict (fun _ => True)) (fun x => x.val = true)
```

```lean
theorem restrict_tight_eqTestClosed :
    FixpointPrinciple Lifted.sys ∧ Extensional Lifted.sys Lifted.Halts ∧
      Extensional Lifted.totalSys (fun x => Lifted.HaltsZero x.val) ∧
      NontrivialPred (fun x : Lifted.totalSys.Code => Lifted.HaltsZero x.val) ∧
      DecidedInside Lifted.totalSys (fun x => Lifted.HaltsZero x.val)
```

```lean
theorem restrict_tight_extensionalFragment :
    FixpointPrinciple Padded.sys ∧ EqTestClosed Padded.sys ∧
      Extensional (Padded.sys.restrict Padded.IsLit) (fun x => Padded.BehTrue x.val) ∧
      NontrivialPred (fun x : {c // Padded.IsLit c} => Padded.BehTrue x.val) ∧
      DecidedInside (Padded.sys.restrict Padded.IsLit) (fun x => Padded.BehTrue x.val)
```

```lean
theorem restrict_tight_extensional :
    FixpointPrinciple Padded.sys ∧ EqTestClosed Padded.sys ∧
      Extensional Padded.sys (fun _ => True) ∧
      NontrivialPred (fun x : Subtype (fun _ : Padded.Code => True) => Padded.EvenPad x.val) ∧
      DecidedInside (Padded.sys.restrict (fun _ => True)) (fun x => Padded.EvenPad x.val)
```

```lean
theorem restrict_tight_hasMember :
    FixpointPrinciple Padded.sys ∧ EqTestClosed Padded.sys ∧
      Extensional Padded.sys (fun _ => True) ∧
      Extensional (Padded.sys.restrict (fun _ => True)) (fun _ => False) ∧
      (∃ _ : Subtype (fun _ : Padded.Code => True), ¬ False) ∧
      DecidedInside (Padded.sys.restrict (fun _ => True)) (fun _ => False)
```

```lean
theorem restrict_tight_hasNonMember :
    FixpointPrinciple Padded.sys ∧ EqTestClosed Padded.sys ∧
      Extensional Padded.sys (fun _ => True) ∧
      Extensional (Padded.sys.restrict (fun _ => True)) (fun _ => True) ∧
      (∃ _ : Subtype (fun _ : Padded.Code => True), True) ∧
      DecidedInside (Padded.sys.restrict (fun _ => True)) (fun _ => True)
```

```lean
theorem restrict_nonvacuous :
    FixpointPrinciple PaddedDiv.sys ∧ EqTestClosed PaddedDiv.sys ∧
      Extensional PaddedDiv.sys PaddedDiv.Halts ∧ NontrivialPred PaddedDiv.Halts ∧
      Extensional (PaddedDiv.sys.restrict PaddedDiv.Halts) (fun x => PaddedDiv.ReturnsTrue x.val) ∧
      NontrivialPred (fun x : {c // PaddedDiv.Halts c} => PaddedDiv.ReturnsTrue x.val)
```

#### For F1

```lean
theorem lawvere_tight_represents :
    (fun _ : Unit → Bool => True) (fun x => !(phiTrue x x)) ∧
      ¬ (∀ g : Unit → Bool, (fun _ => True) g → ∃ a, ∀ x, phiTrue a x = g x) ∧
      ¬ LawvereConclusion phiTrue not
```

```lean
theorem lawvere_tight_diagonal :
    (∀ g, IsConst g → ∃ a, ∀ x, phiConst a x = g x) ∧
      ¬ IsConst (fun x => !(phiConst x x)) ∧ ¬ LawvereConclusion phiConst not
```

```lean
theorem lawvere_nonvacuous :
    (∀ g, IsConst g → ∃ a, ∀ x, phiConst a x = g x) ∧
      IsConst (fun x => (fun _ : Bool => true) (phiConst x x))
```

#### For F2

```lean
theorem cantor_tight_surjective :
    ¬ (∀ g : Bool → Bool, ∃ a, ∀ x, Models.phiConst a x = g x) ∧
      ¬ (Nonempty Bool ∧ ∀ y y' : Bool, y = y')
```

```lean
theorem cantor_nonvacuous : ∀ g : Unit → Unit, ∃ a : Unit, ∀ x, (fun _ _ => ()) a x = g x
```

#### For F3

```lean
theorem kleene_tight_represents :
    IsDiagonal (boolSys adm2) app2 id ∧ PrecompClosed (boolSys adm2) id ∧
      ¬ DiagConclusion (boolSys adm2) app2 id
```

```lean
theorem kleene_tight_diagonal :
    Represents (boolSys adm3) app3 ∧ PrecompClosed (boolSys adm3) id ∧
      ¬ DiagConclusion (boolSys adm3) app3 id
```

```lean
theorem kleene_tight_precompClosed :
    Represents (boolSys adm1) app1 ∧ IsDiagonal (boolSys adm1) app1 (fun _ => false) ∧
      ¬ DiagConclusion (boolSys adm1) app1 (fun _ => false)
```

```lean
theorem kleene_nonvacuous :
    Represents tagSys tagApp ∧ IsDiagonal tagSys tagApp tagDiag ∧
      PrecompClosed tagSys tagDiag ∧ ¬ tagSys.Adm tagDiag ∧ (∀ x, tagDiag x ≠ x) ∧
      ConstClosed tagSys ∧ CompClosed tagSys ∧
      (tagSys.Adm (fun x => (x.1, 0)) ∧
        (∀ x, tagApp (true, 1) x = some ((fun x : Bool × Nat => (x.1, 0)) (tagDiag x))) ∧
        (fun x : Bool × Nat => (x.1, 0)) (tagDiag (true, 1)) ≠ tagDiag (true, 1))
```

#### For F4

```lean
theorem semConst_tight_fixpointPrinciple :
    (∀ chk : Bool → Bool, SwitchAdmissible (allAdm (id : Bool → Bool)) chk) ∧
      ¬ ∀ c d : Bool, (allAdm (id : Bool → Bool)).sem c = (allAdm (id : Bool → Bool)).sem d
```

```lean
theorem semConst_tight_allSwitches :
    FixpointPrinciple Flat.sys ∧ ¬ ∀ c d : Flat.Flat, Flat.sys.sem c = Flat.sys.sem d
```

```lean
theorem allAdm_tight_nonempty :
    ¬ (FixpointPrinciple (allAdm emptySem) ↔ ∀ c d : Empty, emptySem c = emptySem d)
```

```lean
theorem semConst_nonvacuous :
    FixpointPrinciple (allAdm (fun _ : Bool => ())) ∧
      ∀ chk : Bool → Bool, SwitchAdmissible (allAdm (fun _ : Bool => ())) chk
```

```lean
theorem allAdm_nonvacuous :
    Nonempty Bool ∧ FixpointPrinciple (allAdm (fun _ : Bool => ())) ∧
      ¬ FixpointPrinciple (allAdm (id : Bool → Bool))
```

#### For N2

```lean
theorem tables_no_fixpointPrinciple_and_isZeroFn_decidedInside :
    ¬ FixpointPrinciple sys ∧ Extensional sys IsZeroFn ∧ NontrivialPred IsZeroFn ∧
      Decides zeroCheck IsZeroFn ∧ SwitchAdmissible sys zeroCheck
```

#### For W1

```lean
theorem rejectAll_tight_constClosed :
    ¬ (SoundFor (fun _ : Bool => false) (fun _ : Bool => True) ∧
        SwitchAdmissible emptyAdmSys (fun _ => false))
```

```lean
theorem rejectAll_nonvacuous : ConstClosed Padded.sys ∧ FixpointPrinciple Padded.sys
```

#### For W5

```lean
theorem incompleteAll_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ (∃ b, ¬ Tables.IsZeroFn b) ∧
      SoundFor Tables.zeroCheck Tables.IsZeroFn ∧ SwitchAdmissible Tables.sys Tables.zeroCheck ∧
      ¬ ∀ a, ∃ c, Tables.sys.sem c = Tables.sys.sem a ∧ Tables.zeroCheck c = false
```

```lean
theorem incompleteAll_tight_extensional :
    FixpointPrinciple twinSys ∧ (∃ b, ¬ tagOr b = true) ∧
      SoundFor tagOr (fun c => tagOr c = true) ∧ SwitchAdmissible twinSys tagOr ∧
      ¬ ∀ a, ∃ c, twinSys.sem c = twinSys.sem a ∧ tagOr c = false
```

```lean
theorem incompleteAll_tight_violated :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => True) ∧
      SoundFor (fun _ : Padded.Code => true) (fun _ => True) ∧
      SwitchAdmissible Padded.sys (fun _ => true) ∧
      ¬ ∀ a : Padded.Code, ∃ c, Padded.sys.sem c = Padded.sys.sem a ∧
          (fun _ : Padded.Code => true) c = false
```

```lean
theorem incompleteAll_tight_sound :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      (∃ b, ¬ Padded.BehTrue b) ∧ SwitchAdmissible Padded.sys (fun _ => true) ∧
      ¬ ∀ a : Padded.Code, ∃ c, Padded.sys.sem c = Padded.sys.sem a ∧
          (fun _ : Padded.Code => true) c = false
```

```lean
theorem incompleteAll_tight_switchAdmissible :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      (∃ b, ¬ Padded.BehTrue b) ∧ SoundFor Padded.Code.beh Padded.BehTrue ∧
      ¬ ∀ a : Padded.Code, ∃ c, Padded.sys.sem c = Padded.sys.sem a ∧ Padded.Code.beh c = false
```

```lean
theorem incompleteAll_nonvacuous :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      (∃ b, ¬ Padded.BehTrue b) ∧ SoundFor Padded.litTrueCheck Padded.BehTrue ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck
```

#### For W6

```lean
theorem splitAll_tight_fixpointPrinciple :
    SwitchAdmissible Tables.sys Tables.zeroCheck ∧
      ¬ ∀ a b, (∃ c, Tables.sys.sem c = Tables.sys.sem a ∧ Tables.zeroCheck c = false) ∨
          (∃ c, Tables.sys.sem c = Tables.sys.sem b ∧ Tables.zeroCheck c = true)
```

```lean
theorem splitAll_tight_switchAdmissible :
    FixpointPrinciple Padded.sys ∧
      ¬ ∀ a b, (∃ c, Padded.sys.sem c = Padded.sys.sem a ∧ Padded.Code.beh c = false) ∨
          (∃ c, Padded.sys.sem c = Padded.sys.sem b ∧ Padded.Code.beh c = true)
```

```lean
theorem splitAll_nonvacuous :
    FixpointPrinciple Padded.sys ∧ SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      Padded.litTrueCheck (.lit true 0) = true ∧ Padded.litTrueCheck (.hid true 0) = false
```

#### For W7

```lean
theorem soundSplit_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ SoundFor Tables.zeroCheck Tables.IsZeroFn ∧
      SwitchAdmissible Tables.sys Tables.zeroCheck ∧ (∃ c, Tables.zeroCheck c = true) ∧
      (∃ d, Tables.zeroCheck d = false) ∧
      ¬ ∃ c d, Tables.sys.sem c = Tables.sys.sem d ∧ Tables.IsZeroFn c ∧ Tables.IsZeroFn d ∧
          Tables.zeroCheck c = true ∧ Tables.zeroCheck d = false
```

```lean
theorem soundSplit_tight_extensional :
    FixpointPrinciple Padded.sys ∧
      SoundFor Padded.litTrueCheck (fun c => Padded.litTrueCheck c = true) ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      (∃ c, Padded.litTrueCheck c = true) ∧ (∃ d, Padded.litTrueCheck d = false) ∧
      ¬ ∃ c d, Padded.sys.sem c = Padded.sys.sem d ∧ Padded.litTrueCheck c = true ∧
          Padded.litTrueCheck d = true ∧ Padded.litTrueCheck c = true ∧
          Padded.litTrueCheck d = false
```

```lean
theorem soundSplit_tight_sound :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => False) ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      (∃ c, Padded.litTrueCheck c = true) ∧ (∃ d, Padded.litTrueCheck d = false) ∧
      ¬ ∃ c d, Padded.sys.sem c = Padded.sys.sem d ∧ False ∧ False ∧
          Padded.litTrueCheck c = true ∧ Padded.litTrueCheck d = false
```

```lean
theorem soundSplit_tight_switchAdmissible :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      SoundFor Padded.Code.beh Padded.BehTrue ∧
      (∃ c, Padded.Code.beh c = true) ∧ (∃ d, Padded.Code.beh d = false) ∧
      ¬ ∃ c d, Padded.sys.sem c = Padded.sys.sem d ∧ Padded.BehTrue c ∧ Padded.BehTrue d ∧
          Padded.Code.beh c = true ∧ Padded.Code.beh d = false
```

```lean
theorem soundSplit_tight_accepts :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      SoundFor (fun _ : Padded.Code => false) Padded.BehTrue ∧
      SwitchAdmissible Padded.sys (fun _ => false) ∧
      (∃ d : Padded.Code, (fun _ : Padded.Code => false) d = false) ∧
      ¬ ∃ c d : Padded.Code, Padded.sys.sem c = Padded.sys.sem d ∧ Padded.BehTrue c ∧
          Padded.BehTrue d ∧ (fun _ : Padded.Code => false) c = true ∧
          (fun _ : Padded.Code => false) d = false
```

```lean
theorem soundSplit_tight_rejects :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => True) ∧
      SoundFor (fun _ : Padded.Code => true) (fun _ => True) ∧
      SwitchAdmissible Padded.sys (fun _ => true) ∧
      (∃ c : Padded.Code, (fun _ : Padded.Code => true) c = true) ∧
      ¬ ∃ c d : Padded.Code, Padded.sys.sem c = Padded.sys.sem d ∧ True ∧ True ∧
          (fun _ : Padded.Code => true) c = true ∧ (fun _ : Padded.Code => true) d = false
```

```lean
theorem soundSplit_nonvacuous :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      SoundFor Padded.litTrueCheck Padded.BehTrue ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      (∃ c, Padded.litTrueCheck c = true) ∧ (∃ d, Padded.litTrueCheck d = false)
```

#### Boundary facts cited by the non-claims of W4, W5, W6

```lean
theorem switchAdmissible_const (chk : Option Table → Bool) (hsw : SwitchAdmissible sys chk) :
    (∀ c, chk c = true) ∨ (∀ c, chk c = false)
```

```lean
theorem not_decidedInside_of_nontrivial {P : Option Table → Prop} (hnt : NontrivialPred P) :
    ¬ DecidedInside sys P
```

```lean
theorem verdictSplit_unrealizableBehaviour :
    FixpointPrinciple nonSurjSys ∧ SwitchAdmissible nonSurjSys (fun _ => true) ∧
      ∃ b₁ b₂ : nonSurjSys.Beh, b₁ ≠ b₂ ∧
        (∀ c, nonSurjSys.sem c = b₁ → (fun _ : Unit => true) c = true) ∧
        (∀ c, nonSurjSys.sem c = b₂ → (fun _ : Unit => true) c = false)
```

```lean
theorem incompleteAll_unrealizableBehaviour :
    FixpointPrinciple paddedOptSys ∧ Extensional paddedOptSys Padded.BehTrue ∧
      (∃ b, ¬ Padded.BehTrue b) ∧ SoundFor Padded.litTrueCheck Padded.BehTrue ∧
      SwitchAdmissible paddedOptSys Padded.litTrueCheck ∧
      ∃ b : paddedOptSys.Beh, ¬ ∃ c, paddedOptSys.sem c = b ∧ Padded.litTrueCheck c = false
```

```lean
theorem not_forall_sameSem_accepted_and_forall_sameSem_rejected_of_fixpointPrinciple_switchAdmissible
    (hfix : FixpointPrinciple S) {chk : S.Code → Bool} (hsw : SwitchAdmissible S chk)
    (a b : S.Code) :
    ¬ ((∀ c, S.sem c = S.sem a → chk c = true) ∧ (∀ c, S.sem c = S.sem b → chk c = false))
```

```lean
theorem sameSem_split_iff_not_forall_sameSem_accepted_and_forall_sameSem_rejected
    (chk : S.Code → Bool) (a b : S.Code) :
    ((∃ c, S.sem c = S.sem a ∧ chk c = false) ∨ (∃ c, S.sem c = S.sem b ∧ chk c = true)) ↔
      ¬ ((∀ c, S.sem c = S.sem a → chk c = true) ∧ (∀ c, S.sem c = S.sem b → chk c = false))
```

## Boundaries

**Non-claims first.**

### What these results do not forbid (known not to apply)

- **Partial or one-sided procedures.** `DecidedInside` is two-sided. In the flat-domain system, which has the fixpoint principle, the one-sided switch 'if the program halts then return true, else diverge' is admissible while halting is not decided inside (W8; `Toy.Rice.Flat.unswappedSwitch_admissible`). No notion of semi-decision is formalized and the Rice-Shapiro theorem is not covered (not examined).
- **Checkers for decidable fragments and total sublanguages.** A separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1). A behaviour-closed fragment of a system whose transformers cannot test code equality decides one inside (W4). A syntactically delimited fragment can too (`Toy.Rice.Controls.restrict_tight_extensionalFragment`). Restriction does not help for behaviour-closed fragments of systems closed under code-equality tests (R6).
- **Sound but incomplete checkers.** Soundness alone is never forbidden (W1), and nontrivial sound checkers for a syntactic subclass exist in a system with the fixpoint principle (W2). W5, W6 and W7 describe the incompleteness such checkers must have; they do not forbid them.
- **Syntactic checks and certificate checking.** Predicates that are not extensional can be decided inside a system with the fixpoint principle (W3); a checker that reads a certificate visible in the code text is consistent with it (W2).

### Global non-claims

- Semi-decision: no notion is formalized; the Rice-Shapiro theorem is not covered. In the flat-domain toy the one-sided halting switch is admissible while halting is not decided inside (W8).
- Time and space: there is no cost model; complexity-aware versions are not covered, for example the complexity cliques of A. Asperti, "The intensional content of Rice's theorem", POPL '08, ACM, 2008, 113-119, DOI 10.1145/1328438.1328455 (full entry under R1, Prior art).
- Properties of code text: only extensional predicates are covered; syntactic predicates can be decided inside a system with the fixpoint principle (W3), and certificate checking is consistent with it (W2).
- Randomized, approximate, or bounded-input checkers: not covered; all statements quantify deterministically over every code.
- Real languages: nothing follows for a real language unless its fixpoint principle is established; see the `derived (modeling bridge)` lines under Findings.
- 'Not decided inside' does not imply 'no Boolean function decides it' (the external notion). `Decides` is a set-theoretic relation with no effectiveness: in the flat-domain system `haltCheck` decides `Halts` (`Toy.Rice.Flat.haltCheck_decides`) while `Halts` is not decided inside (N2; directly, `Toy.Rice.Examples.decidedInside_neg_direct`). The obstruction is the admissibility of switches. No theorem here proves that any predicate is classically undecidable (not decided by any total computable procedure); classical undecidability enters only through the `derived (modeling bridge)` lines.
- The converse of R1 fails: without the fixpoint principle nothing nontrivial need become decided inside (N3).
- The fixpoint principle alone carries little information: it holds vacuously for an empty admissible class (Toy.Rice.Controls.emptyAdm_fixpointPrinciple_nothingDecided), and it holds in tiny systems without any encoding of computation (N2, W4, the padded systems).
- Total languages: N1 decides 'computes the zero function' only because finite tables have finite support; for primitive-recursive programs that property is not decidable in the classical sense (modeling bridge of N1, not formalized).
- Fragments: restricting to a behaviour-closed fragment escapes Rice only when the system's transformers cannot test code equality (W4 versus R6).
- Concrete results are existence statements: N1, N2, N3, W2, W3, W4 and W8 each concern one named toy system. They show that a system with the stated properties exists, not that every system of that kind, or any real language, has them.

### Non-claims by result

Each list starts with what the result does not forbid; it is copied from the `non_claims` field of `results.json`.

#### R1. `Toy.Rice.not_decidedInside_of_fixpointPrinciple_extensional_nontrivial`

- Does not forbid: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers: these are switch-admissible in systems with the fixpoint principle (W1, W2), and W5 states the incompleteness every such checker of a nontrivial extensional predicate has.
- 'Not decided inside the system' is not 'no Boolean function decides P'. Decides is a set-theoretic relation that classical logic always satisfies; the impossibility concerns the admissibility of the switches on such a function. For example Toy.Rice.Flat.haltCheck decides halting on the flat domain but is not switch-admissible (Toy.Rice.Examples.switchAdmissible_neg).
- The strength of the conclusion depends entirely on how rich Adm is. The fixpoint principle becomes easier to satisfy as Adm shrinks; with no admissible transformers it holds vacuously and then nothing at all is decided inside (Toy.Rice.Controls.emptyAdm_fixpointPrinciple_nothingDecided). The result rules out only checkers whose switches are admissible.
- The converse fails: a system without the fixpoint principle need not decide anything nontrivial, even if it contains all constants and is closed under composition (N3).
- Says nothing about semi-decision: DecidedInside is two-sided, and a one-sided switch can be admissible while the two-sided decision is impossible (W8). The Rice-Shapiro theorem is not formalized.
- Says nothing about time or space: Adm is a bare membership predicate with no cost model. It neither shows nor refutes complexity-aware versions (for example Asperti 2008, listed under Prior art), which are not covered.
- Applies only to extensional predicates, relative to the chosen semantics sem. Properties of code text can be decided inside a system with the fixpoint principle (W3). Which predicates count as extensional depends on sem.
- Does not forbid certificate checking (proof-carrying or annotation-assisted verification): deciding 'the attached certificate is valid' for a code that carries a certificate is a property of the text, not of the behaviour alone, and such checks can be switch-admissible in a system with the fixpoint principle (compare W2). Such a checker is sound for P but complete only for codes carrying a valid certificate, not for P itself.
- Decides and DecidedInside quantify deterministically over every code. Says nothing about randomized checkers, classifiers that are accurate on a distribution or benchmark, or checkers verified only on bounded inputs.
- Says nothing about any particular real language unless that language's fixpoint principle is established; the connection to acceptable numberings is a modeling bridge, not a theorem here.

#### R2. `Toy.Rice.swappedSwitch_not_admissible_of_fixpointPrinciple_extensional_decides`

- Does not forbid: (i) partial or one-sided procedures: the unswapped switch c ↦ if chk c then a else b can be admissible (Toy.Rice.Flat.unswappedSwitch_admissible), and a one-sided switch that diverges on rejected codes can be admissible while the predicate is not decided inside (W8); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers: these are switch-admissible in systems with the fixpoint principle (W1, W2), and W5 states the incompleteness every such checker of a nontrivial extensional predicate has.
- Says nothing about the unswapped switch c ↦ if chk c then a else b, which can be admissible (Toy.Rice.Flat.unswappedSwitch_admissible); this is why nothing follows about semi-decision.
- Requires chk to decide P. A checker that is only sound for P can have an admissible swapped switch: Toy.Rice.Padded.litTrueCheck_swappedSwitch_admissible exhibits litTrueCheck, sound for BehTrue in the padded system, with c ↦ if litTrueCheck c then hid false 0 else hid true 0 admissible.
- Does not say that switches with other branch pairs are inadmissible: with both branches satisfying P, or both violating it, the swapped switch can be admissible (Toy.Rice.Controls.riceSharp_tight_member, Toy.Rice.Controls.riceSharp_tight_nonmember).

#### R4. `Toy.Rice.decidedInside_iff_trivial_of_fixpointPrinciple_constClosed_extensional`

- Does not forbid: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers: these are switch-admissible in systems with the fixpoint principle (W1, W2), and W5 states the incompleteness every such checker of a nontrivial extensional predicate has.
- The forward direction uses classical logic (Classical.byContradiction; the axiom audit shows Classical.choice), unlike R1, whose proof uses only propext.
- ConstClosed is used only for the backward direction; without it even trivial predicates can fail to be decided inside (Toy.Rice.Controls.riceChar_tight_constClosed).
- Inherits every scope limit of R1: extensional predicates only, no semi-decision, no cost model, no real language without its fixpoint principle.

#### R6. `Toy.Rice.not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial`

- Does not forbid: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for other kinds of fragment: R6 covers only fragments closed under same behaviour in systems closed under code-equality tests; a syntactically delimited fragment (Toy.Rice.Controls.restrict_tight_extensionalFragment), a separate total language (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality (W4) can each decide a nontrivial property inside; (iii) sound but incomplete checkers: R6 constrains only checkers that decide the predicate on the fragment; sound but incomplete checkers are switch-admissible in systems with the fixpoint principle (W1, W2).
- Does not cover fragments that are not closed under same behaviour, such as syntactically delimited sublanguages (the literal programs of the padded system, Toy.Rice.Controls.restrict_tight_extensionalFragment) or a separate total language with its own system (N1). Restricting to those can escape Rice.
- Does not cover systems whose transformers cannot test code equality. Strict (domain-theoretic) transformers, which model analyzers allowed to diverge outside the fragment, do escape (W4; Toy.Rice.Controls.restrict_tight_eqTestClosed).
- S.restrict requires literal agreement on the fragment. Says nothing about full-system transformers that agree with the fragment switch only up to behaviour (for example 'run the program, then branch'); that is a different notion of deciding on a fragment.
- Says nothing about semi-decision on the fragment, about cost, or about non-extensional predicates.

#### F1. `Toy.Rice.lawvere_fixedPoint_of_represents_diagonal`

- Does not forbid any checker design: it is a fixed-point existence statement about represented maps. In particular it says nothing against partial or semi-decision procedures (W8), checkers for decidable fragments (N1, W4), or sound but incomplete checkers (W1, W2).
- Stated for types and functions with a class restriction; does not formalize cartesian closed categories.
- The second conjunct (φ a a is a fixed point whenever a represents the diagonal) holds without either hypothesis; the hypotheses are needed only to obtain such an a.
- Says nothing about computability; it supplies the diagonal pattern that F3 instantiates.

#### F2. `Toy.Rice.nonempty_subsingleton_of_weaklyPointSurjective`

- Does not forbid any checker design: it concerns a function space that contains every map A → Y. In particular it says nothing against partial or semi-decision procedures (W8), checkers for decidable fragments (N1, W4), or sound but incomplete checkers (W1, W2).
- Holds for types with all functions and uses classical logic. Does not say that weak point-surjectivity forces a one-element Y in other cartesian closed categories: Scott (1972) constructs a continuous lattice isomorphic to its own function space, and there every endomorphism has a fixed point (Tarski 1955), as Lawvere's theorem requires.
- Says nothing about computability. It shows why a fixpoint principle is informative only for a restricted admissible class (see F4).

#### F3. `Toy.Rice.diagonalFixedPoint_of_represents_diagonal_precompClosed`

- Does not forbid any checker design by itself: it derives the fixpoint principle from representability. What follows for checkers follows through R1, R2, R4, R6 and W5 to W7, and partial or one-sided procedures (W8), checkers for decidable fragments (N1, W4), and sound but incomplete checkers (W1, W2) remain possible under those results.
- Does not construct an acceptable numbering; Represents, IsDiagonal and PrecompClosed are assumptions. Establishing them for a real language needs a universal function and the s-m-n theorem (a modeling bridge).
- The fixpoint principle does not require Turing-completeness, universal programs, or self-reference: the flat-domain, padded and lifted systems satisfy it without encoding computation (and without this theorem's hypotheses).
- PrecompClosed S d is strictly weaker than the textbook pair CompClosed S and Adm d: in the tag model PrecompClosed holds while Adm d fails. The textbook corollary is kept as Toy.Rice.fixpointPrinciple_of_compClosed_represents_diagonal.

#### F4. `Toy.Rice.sem_constant_of_fixpointPrinciple_allSwitchesAdmissible` / `Toy.Rice.fixpointPrinciple_allAdm_iff_sem_constant_of_nonempty`

- Does not forbid partial or one-sided procedures, checkers for decidable fragments, or sound but incomplete checkers in systems whose admissible class is restricted: its hypothesis hall makes every switch on every checker admissible, and systems with the fixpoint principle and a restricted admissible class admit one-sided switches (W8), fragment deciders (W4) and sound syntactic checkers (W2, W3).
- Requires every checker on codes, including extensional ones, to be switch-admissible. Does not rule out nonconstant semantics in a system with the fixpoint principle in which many syntactic checkers are switch-admissible (the padded system: W2, W3).
- Not a statement about any real language; it shows that a fixpoint principle carries information only for a restricted admissible class.

#### N1. `Toy.Rice.Tables.tables_no_fixpointPrinciple_and_isZeroFn_decidedInside`

- Is itself an example of what Rice-style results do not forbid: an internal decider for a nontrivial extensional predicate in a total language without the fixpoint principle. It does not show that such a decider exists for an expressive total language (see the primitive-recursive modeling bridge), and it says nothing for or against partial or semi-decision procedures or sound but incomplete checkers, which are not needed here because the predicate is decided.
- 'Computes the zero function' is decided inside this system because a finite table has finite support, so 'zero everywhere' reduces to finitely many evaluations. This is not a property of total languages in general: for primitive-recursive programs (equivalently Loop programs, Meyer and Ritchie 1967, Theorem 7), 'computes the zero function' is not decidable by any total computable procedure (classical undecidability; see the modeling bridge, which is not formalized).
- Pointwise behavioural properties, such as 'the value at 0 is 0' (Toy.Rice.Tables.evalAtZero_decidedInside), can be decided by evaluating the program at finitely many inputs in any total language whose programs can be run (decidability in the classical computability sense; commentary, not formalized beyond this system); universally quantified properties such as 'computes the zero function' or program equivalence are a different matter (previous item).
- Does not claim that every total language decides every extensional property, nor that totality is the only way to lose the fixpoint principle.
- TProg and TTest are a deliberately small language over a deliberately weak code type; the system shows that deciding this predicate inside is consistent once the fixpoint principle is dropped, not that a comparable checker exists for an expressive language.

#### N2. `Toy.Rice.Flat.flat_fixpointPrinciple_and_halts_not_decidedInside`

- Does not forbid: (i) partial or one-sided procedures: in this same system the one-sided switch 'if the program halts then return true, else diverge' is admissible (W8); semi-decision itself is not formalized; (ii) checkers for decidable fragments: the two-element total fragment of this system decides every predicate (Toy.Rice.Flat.totalSys_decides_every_predicate), a degenerate case recorded as Toy.Rice.Examples.restrict_degenerate_flat; (iii) sound but incomplete checkers: the statement concerns deciders only; because the only switch-admissible checkers here are constant (Toy.Rice.Flat.switchAdmissible_const), a sound switch-admissible checker for halting can only be the one that rejects everything.
- 'Halting is not decided inside' is not 'no Boolean function decides halting': haltCheck decides Halts on the flat domain (Toy.Rice.Flat.haltCheck_decides); what fails is the admissibility of its swapped switch (Toy.Rice.Examples.switchAdmissible_neg). No classical undecidability of halting is claimed or formalized here; the classical fact is cited in prose only (W8).
- Codes are denotations (sem = id), so every predicate is extensional; this system cannot separate syntactic from semantic predicates (see the padded system, W2 and W3).
- Only the two constant checkers are switch-admissible here (Toy.Rice.Flat.switchAdmissible_const), so every nontrivial predicate fails to be decided inside for a blunt reason. The system is a positive control for R1's hypotheses, not a model of a programming language.
- The fixpoint principle holds here by a least-fixed-point argument on a pointed poset, with no encoding of computation, universal program, or self-reference: the fixpoint principle does not imply Turing-completeness.
- The flat domain is not a lattice (Toy.Rice.Flat.no_upper_bound_tt_ff), so this is not an instance of Tarski's lattice fixed-point theorem.

#### N3. `Toy.Rice.Controls.converse_fails_constClosed_compClosed_noFixpoint_nothingNontrivialDecided`

- Does not forbid anything: it shows that losing the fixpoint principle does not by itself make anything nontrivial decided inside. It says nothing about partial or semi-decision procedures, checkers for decidable fragments, or sound but incomplete checkers.
- Shows only that the fixpoint principle is not necessary for the conclusion of R1; it does not characterize the systems in which nothing nontrivial is decided.
- A degenerate variant, in which not even constant switches are admissible, is Toy.Rice.Controls.converse_fails_noFixpoint_nothingDecided.

#### W1. `Toy.Rice.rejectAll_sound_switchAdmissible_of_constClosed`

- Is itself a (trivially) sound but incomplete checker, which Rice-style results do not forbid. It does not show that useful sound checkers exist (W2 does, for a syntactic subclass), and it says nothing about partial or semi-decision procedures (W8) or checkers for decidable fragments (N1, W4).
- Reject-all is sound but useless; it shows only that soundness alone is never forbidden.
- Symmetrically, accept-all is complete for every predicate and switch-admissible under the same hypothesis (Toy.Rice.acceptAll_complete_switchAdmissible_of_constClosed): completeness alone is never forbidden either.
- No fixpoint hypothesis is involved; the statement holds with or without the fixpoint principle.

#### W2. `Toy.Rice.Padded.padded_litTrueCheck_sound_infinite_incomplete`

- Is itself a sound but incomplete checker that accepts infinitely many codes, which Rice-style results do not forbid. It says nothing about partial or semi-decision procedures (W8) or checkers for decidable fragments (N1, W4).
- The padded system's admissible class is deliberately small: outside a finite set its transformers cannot read the behaviour of hidden codes. It shows that this checker is consistent with the fixpoint principle; it is not a model of a real language.
- The accepted class is syntactic (literal codes). Does not say that any natural class of real programs is accepted by a sound internal checker.
- The checker remains incomplete on every behaviour: both behaviours of the padded system are realizable, and each has rejected codes (W5).
- litTrueCheck reads a certificate that is visible in the code text; this is the pattern of certificate checking (proof-carrying code). Such a checker is sound for the property but complete only for codes that carry the certificate.

#### W3. `Toy.Rice.Padded.padded_fixpointPrinciple_and_evenPad_decidedInside`

- Is itself a decider for a non-extensional (syntactic) predicate, which Rice-style results do not forbid. It says nothing about partial or semi-decision procedures (W8), checkers for decidable fragments (N1, W4), or sound but incomplete checkers for extensional predicates (W1, W2, W5).
- Does not say that every non-extensional predicate is decided inside a system with the fixpoint principle; which syntactic predicates are decided depends on Adm.
- Whether a predicate is extensional depends on the chosen semantics sem; changing sem changes the scope of R1.
- The padded system is a toy, not a model of a real language.

#### W4. `Toy.Rice.Lifted.lifted_haltsZero_decidedInside_haltingFragment_not_full`

- Is itself a checker for a decidable fragment, which Rice-style results do not forbid when the system's transformers cannot test code equality (compare R6). It says nothing about partial or semi-decision procedures (not formalized; compare W8) or about sound but incomplete checkers on the full system beyond the degeneracy that only constant checkers are switch-admissible there (Toy.Rice.Lifted.switchAdmissible_const).
- The escape relies on strictness: the full-system transformer that agrees with a fragment switch sends the divergent code to the divergent code, which models an analyzer allowed to diverge outside the fragment. Under closure under code-equality tests the escape is impossible for every behaviour-closed fragment (R6). In particular, for a Turing-complete language with total computable code transformers, restricting to the halting programs does not make 'returns true' decidable in the classical sense, by a total computable procedure on the halting programs (modeling bridge of R6, not formalized; Kleene 1950).
- In the full system Toy.Rice.Lifted.sys only the two constant checkers are switch-admissible (Toy.Rice.Lifted.switchAdmissible_const): a switch whose two branches are halting codes does not send the divergent code to itself, so it is admissible only if it is constant. Hence every nontrivial predicate on the full system, syntactic ones included, fails to be decided inside it (Toy.Rice.Lifted.not_decidedInside_of_nontrivial; for example 'the code is the empty table', Toy.Rice.Lifted.isEmptyTable_not_decidedInside), for the same strictness reason as in the flat-domain system (N2, Toy.Rice.Flat.switchAdmissible_const). The full-system conjunct ¬ DecidedInside sys HaltsZero therefore carries no information beyond this degeneracy. The content of W4 lies in the halting fragment Lifted.totalSys, whose admissible class is proper (it excludes the tail map) and contains the non-constant switch-admissible checker fragCheck.
- Deciding on the fragment does not give a decider on the full system: membership in the fragment (halting) is extensional and nontrivial in the full system, hence not decided inside it (R1).
- The full system's fixpoint principle holds for a domain-theoretic reason (every admissible transformer is constant or fixes the divergent code); the system is not Turing-complete and not a model of a real language.
- The two-element total fragment of the flat-domain system admits every map and decides every predicate (Toy.Rice.Examples.restrict_degenerate_flat); it is recorded as a degenerate example and not used as evidence.

#### W5. `Toy.Rice.forall_exists_sameSem_rejected_of_fixpointPrinciple_extensional_violated_sound_switchAdmissible`

- Does not forbid: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers themselves: W5 presupposes such a checker and describes its incompleteness; such checkers exist (W1, W2).
- Requires a total two-sided Boolean checker whose switches are admissible. Says nothing against one-sided procedures that accept the codes satisfying P and diverge on the others; semi-decision is not formalized (W8).
- Uses soundness only. The dual for complete checkers (the behaviour of every code contains an accepted code, so the behaviour of every code violating P contains a false positive) is the lemma Toy.Rice.forall_exists_sameSem_accepted_of_fixpointPrinciple_extensional_satisfied_complete_switchAdmissible.
- Speaks only about realizable behaviours, the behaviours of codes. If sem is not surjective, an element of the behaviour type that no code has contains no code, hence no rejected code (Toy.Rice.Controls.incompleteAll_unrealizableBehaviour: all hypotheses hold in the padded system with behaviours embedded in Option Bool, and the behaviour none has no rejected code).
- The rejected code is obtained as a semantic fixed point of a switch, a self-referential construction in a real language. Does not say that small, natural, or frequently occurring programs are rejected, nor how many codes are rejected.
- Deterministic and over all codes; says nothing about randomized checkers, classifiers that are accurate on a distribution, or checkers verified only on bounded inputs.
- Does not apply to checkers of non-extensional predicates or to checkers whose switches are not admissible (see the counterexamples).

#### W6. `Toy.Rice.exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible`

- Does not forbid: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers: W6 constrains only how verdicts split across behaviours; sound but incomplete checkers exist in systems with the fixpoint principle (W1, W2).
- Does not say which of the two behaviours is split, nor that every behaviour is split: a constant checker splits no behaviour (and satisfies the statement trivially).
- Speaks only about realizable behaviours. If sem is not surjective, a behaviour that no code has vacuously has all its (zero) codes both accepted and rejected, so the unqualified paraphrase 'no behaviour has all its codes accepted while another behaviour has all its codes rejected' is false (Toy.Rice.Controls.verdictSplit_unrealizableBehaviour).
- The statement is constructive (its only axiom is propext), and so is its negative consequence for realizable behaviours (Toy.Rice.not_forall_sameSem_accepted_and_forall_sameSem_rejected_of_fixpointPrinciple_switchAdmissible). Recovering the positive disjunction from the negative form uses classical logic (Toy.Rice.sameSem_split_iff_not_forall_sameSem_accepted_and_forall_sameSem_rejected).
- Involves no predicate; it constrains the verdicts of the checker only. For sound checkers of a nontrivial extensional predicate, W5 gives the stronger per-behaviour statement.
- Same scope as W5: deterministic, total two-sided checkers with admissible switches.

#### W7. `Toy.Rice.exists_sameSem_satisfying_accepted_rejected_of_fixpointPrinciple_extensional_sound_switchAdmissible`

- Does not forbid: (i) partial or one-sided procedures: a one-sided switch that answers on the codes satisfying the predicate and diverges on the others can be admissible while the predicate is not decided inside (W8, Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside, in the flat-domain system); semi-decision itself is not formalized; (ii) checkers for decidable fragments: a separate total language without the fixpoint principle decides a nontrivial extensional predicate inside (N1), and a behaviour-closed fragment of a system whose transformers cannot test code equality does as well (W4); R6 states when restricting to a behaviour-closed fragment does not help; (iii) sound but incomplete checkers themselves: W7 presupposes such a checker and describes how it splits a behaviour; such checkers exist (W1, W2).
- hacc is essential: the reject-all checker is sound for every P and never accepts. P need not be nontrivial: the statement holds for P = True whenever chk takes both verdicts.
- Existential; for nontrivial P the per-behaviour statement is W5.
- Same scope as W5: deterministic, total two-sided checkers with admissible switches, extensional P.

#### W8. `Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside`

- Shows that one-sided procedures are not forbidden here: the one-sided halting switch is admissible in a system with the fixpoint principle. It does not define or characterize semi-decision, and it says nothing about checkers for decidable fragments (N1, W4) or sound but incomplete checkers (W1, W2).
- No notion of semi-decision is defined. The statement shows only that DecidedInside, which needs both switches, is strictly stronger than admissibility of the unswapped switch. The Rice-Shapiro theorem is not formalized.
- Toy flat domain with sem = id; not a model of a real language.

### Escape hatches (hypotheses whose removal defeats an impossibility result)

- Drop the fixpoint principle: N1 (a nontrivial extensional predicate decided inside); positive controls of R1, R2, W5, W6, W7.
- Drop extensionality: W3 (syntactic predicate decided inside a system with the fixpoint principle); W2 (sound checker for a syntactic subclass).
- Weaken 'decides' to 'sound': the swapped switch can be admissible (Toy.Rice.Padded.litTrueCheck_swappedSwitch_admissible), and sound checkers exist (W1, W2), though the behaviour of every code keeps a rejected code (W5).
- Two-sided versus one-sided: the unswapped switch can be admissible (W8).
- Restrict to a fragment: escapes when the system is not closed under code-equality tests (W4) or the fragment is not closed under same behaviour (Toy.Rice.Controls.restrict_tight_extensionalFragment); not otherwise (R6).

### Tightness `unknown`

None. Every hypothesis marked `tight` has a fully proved counterexample in canonical form (all other hypotheses hold and the conclusion fails); their statements are quoted at the end of Findings.

### Disproved or dropped statements

None. All 19 results, and every counterexample, non-vacuity witness and positive control they reference (74 declarations in total), are proved exactly as stated; their statement and closure hashes are recorded under Evidence.

## Evidence

### Kernel-check record

- **Toolchain:** `leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (read from the tag with `git ls-remote https://github.com/leanprover/lean4 refs/tags/v4.34.1` and from `lean --version` of the installed toolchain).
- **Build and axiom audit (2026-11-20):** `lake build` of `lean/` succeeds; `Lean.collectAxioms` over all 658 declarations of the `ToyRice` library finds no axiom other than `propext`, `Classical.choice`, `Quot.sound`. Per-declaration axioms are recorded in `audit/axioms.json`. No Lean source contains `sorry`, `admit`, `native_decide`, or an `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe` declaration.
- **Hashes:** the statement hash is the SHA-256 of `repr` of the declaration's type. The closure hash is the SHA-256 of the sorted, newline-joined list of entries `<name> : <repr of type>` (followed by ` := <repr of value>` for non-theorems) over every `ToyRice` constant reachable from the statement through types, definition values and inductive constructors; theorem bodies are not followed, so proofs can change without changing either hash. The number in parentheses is the closure size. Both are recorded in `audit/statements.json`.

#### Results

| Result | Theorem | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| R1 | `Toy.Rice.not_decidedInside_of_fixpointPrinciple_extensional_nontrivial` | `propext` | `c48ee5c369cff7d0c1210efa215b674995f944196359091079f808ad2e596f5f` | `18ee21cb2e0f92eedc93b9045f0cb6b227fbc31b483768c4ccd038330637dee3` (13) |
| R2 | `Toy.Rice.swappedSwitch_not_admissible_of_fixpointPrinciple_extensional_decides` | `propext` | `f4ab51545e6b52470a893fce4f3bbf1727e3547b09336105ed82cb0ab5a9ca31` | `0f9d2bdc273dcdc7a131045d008db987bae570735768ae76b5fec55745136975` (10) |
| R4 | `Toy.Rice.decidedInside_iff_trivial_of_fixpointPrinciple_constClosed_extensional` | `Classical.choice`, `Quot.sound`, `propext` | `459d8ec565e4374b82ddc39d2373cd6bf89943e51fd2f23f06a55d1502630019` | `bbbbb0d1d92420c17e987e14cf26aebe2e0e6e6e31f5629cf07d9de386cd9833` (13) |
| R6 | `Toy.Rice.not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial` | `Classical.choice`, `Quot.sound`, `propext` | `8ee993df17804f1259307218fe1f320b1024314ff1ef71d9fa0edfc92762358c` | `3a368ffefbcf554ecd10b47024df883fa1c3a77248d883a2cce0e98c218ab958` (15) |
| F1 | `Toy.Rice.lawvere_fixedPoint_of_represents_diagonal` | none | `8326ddfd7ce4210017f7a793c42ff7f33c51bf386f10f660afd306127b0e0685` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| F2 | `Toy.Rice.nonempty_subsingleton_of_weaklyPointSurjective` | `Classical.choice`, `Quot.sound`, `propext` | `e704af0dc94a95eac39f433bc9abbcca024a4900cfc08755c581c6c0a073fa29` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| F3 | `Toy.Rice.diagonalFixedPoint_of_represents_diagonal_precompClosed` | none | `5721642a5d58868b51ba3b4d931fe59f0c75bde244b1e3293a669986626df42f` | `1b1c40bf2cdab0460dd84b3685047575e92caea9b86a7be1846339072797542c` (9) |
| F4 | `Toy.Rice.sem_constant_of_fixpointPrinciple_allSwitchesAdmissible` | `Classical.choice`, `Quot.sound`, `propext` | `814e65a544b66b0c234c56dd2f59ea983acbfd51cd94c6bd070375f5c51e4ed9` | `3844effbe8f4b6c305654e8fe2a2bd3b2ca41b0bda82a1f53305138427deaef0` (9) |
| F4 | `Toy.Rice.fixpointPrinciple_allAdm_iff_sem_constant_of_nonempty` | `Classical.choice`, `Quot.sound`, `propext` | `97ffb05cf77e24f4c658fb5fda4e24fb3eb8ec92454e9a11a04729af40664574` | `646860a3d3b67b6de9e717502646ed1bb308f6bf1ba37ac21e342f44d34a9ee7` (8) |
| N1 | `Toy.Rice.Tables.tables_no_fixpointPrinciple_and_isZeroFn_decidedInside` | `Classical.choice`, `Quot.sound`, `propext` | `efbd4632fa7245e6965a6ac28ce473671531a71624f76e12948d060098263f28` | `ff7b616cf08c320802206143dd833a6c411c21f2ba904d1f160c904e9d4d843a` (61) |
| N2 | `Toy.Rice.Flat.flat_fixpointPrinciple_and_halts_not_decidedInside` | `propext` | `549bdf55fed9f2ca2091bf6d24065fbe283ff23f6bd3ccb74883b1b1a87ccdb7` | `802eea5b622d52752ab7113f5166a96a82bef2bbffaf691159a8daa9f75b90cf` (21) |
| N3 | `Toy.Rice.Controls.converse_fails_constClosed_compClosed_noFixpoint_nothingNontrivialDecided` | `Quot.sound`, `propext` | `09712facf3e796c53fa896b1306ed3c6cc2eaf13ea370f32bdf08611d0f9eb47` | `0cb3c398231c711e40e8a17494b90c4c1e7335da7eba4d4f8cba3e49653badad` (16) |
| W1 | `Toy.Rice.rejectAll_sound_switchAdmissible_of_constClosed` | none | `f11b06269e644206325f6b7da44b63ba9d0ce6250bd65bef0c2dc3743eb0072b` | `6d17b8a40d135036201fa37ecef33d2537e1a2cc762ce252af8000067d4564a5` (8) |
| W2 | `Toy.Rice.Padded.padded_litTrueCheck_sound_infinite_incomplete` | `propext` | `e94a46b861f5b88e4da59fe792d8c140ec37c575a1596355cfb6a3e7410c9d23` | `2301c18d9ab7d34239717e138da6ff4e8429fc09209eb0b3a7a86d49d60ef9b1` (28) |
| W3 | `Toy.Rice.Padded.padded_fixpointPrinciple_and_evenPad_decidedInside` | `Quot.sound`, `propext` | `857b526239f22591f8338fffe30aeb5fd00c78ac617790f5de9ec2ce4616ec4c` | `d27dbeecbf12fce0551276a1a1a5e35d27cee31eb0f20c95bc06621380727b19` (27) |
| W4 | `Toy.Rice.Lifted.lifted_haltsZero_decidedInside_haltingFragment_not_full` | `Classical.choice`, `Quot.sound`, `propext` | `00881837657e2b3c478346a075faf50c0e049a3bed822329a377e6694d3139e4` | `0e0eb1e666032214d2e477df31cc2dcdf452f0a408aac988b6009761e9601d0d` (70) |
| W5 | `Toy.Rice.forall_exists_sameSem_rejected_of_fixpointPrinciple_extensional_violated_sound_switchAdmissible` | `propext` | `8e713ad5d115e295ae91be72769a1351bdac4952dd64c9c2b1fff2075e9b60fa` | `aa27d46a0a0beae5697718b8d804a024a536a3c2091a243a3d91b55470719614` (11) |
| W6 | `Toy.Rice.exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible` | `propext` | `aa12c2e44fac570bc0a181d86ea04cbc226dbd7779e89cd262fc71a7db538310` | `3844effbe8f4b6c305654e8fe2a2bd3b2ca41b0bda82a1f53305138427deaef0` (9) |
| W7 | `Toy.Rice.exists_sameSem_satisfying_accepted_rejected_of_fixpointPrinciple_extensional_sound_switchAdmissible` | `propext` | `7f9c7dc7842c71fe483583a2dc5656c9bf1f224347686be4999363b284b29e5a` | `aa27d46a0a0beae5697718b8d804a024a536a3c2091a243a3d91b55470719614` (11) |
| W8 | `Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside` | `propext` | `19458dbad073f0865ecba7ff82ae3eccb7703ab03e611d57ed036dbd43b9d416` | `6268d0bec8b0a375a35e051d4a45af4f9a2efb6ae6ba182d393d84cc6bf49c60` (26) |

#### Tightness counterexamples, non-vacuity witnesses and positive controls

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Rice.Controls.allAdm_nonvacuous` | F4 non-vacuity | none | `5025c061db41fbe0e2a28644b1952a33b92a9aff001e9247848a9b69a9092655` | `646860a3d3b67b6de9e717502646ed1bb308f6bf1ba37ac21e342f44d34a9ee7` (8) |
| `Toy.Rice.Controls.allAdm_tight_nonempty` | F4 counterexample (hne) | none | `c2d05f8eb7a8ef0b6ec90dae801728ba9fa1e745111904db0de2e20448b47460` | `1f6baa076efe66d099aa612ebea5c2ff03998141ba67d38bb01ae5afd48efd93` (10) |
| `Toy.Rice.Controls.cantor_nonvacuous` | F2 non-vacuity | none | `824e1ba491aacf6600d52816329ebe8c7e7271c1846c1965eb0b2b8d5640fb2e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Rice.Controls.cantor_tight_surjective` | F2 positive control; F2 counterexample (hsurj) | none | `175f252353e7f8a9a292f68dc8cf781f427c16d905505bd4b9193a348c276a12` | `216488f373b0b04a847abf3df3fc9f8b75e99cf14d001ec925f75f3840d98c34` (1) |
| `Toy.Rice.Controls.incompleteAll_nonvacuous` | W5 non-vacuity | `propext` | `07e6b3477a0ffb2c7b537d19211263d27fe23c4b45bbb0969dc373dbf4b78319` | `320a9abca32983afec7f8bb8de6c36b87d8f110f4d43b3dc01d23e3e6f3c7407` (25) |
| `Toy.Rice.Controls.incompleteAll_tight_extensional` | W5 counterexample (hext) | none | `94c137ce21c2d4534d26ca21206f500cc95afd581ce2a614582ad6457a543ec0` | `62209ad14fa3b6b33406053484d9d37cc185563156fe2cb7f5f92d981fe846a1` (13) |
| `Toy.Rice.Controls.incompleteAll_tight_fixpointPrinciple` | W5 positive control; W5 counterexample (hfix) | `Classical.choice`, `Quot.sound`, `propext` | `290c27756a0630df13a41ea1a9a00951d352b1fefa8629536ba5c49c87e40f76` | `a6af86f93a9a9598380570e318ea3ced739c5102a19b54b75c350af73959d8f0` (59) |
| `Toy.Rice.Controls.incompleteAll_tight_sound` | W5 counterexample (hsound) | `propext` | `89acdf1ce6e4126874d3149820b05e0d89324323f2a402f47781542a90204040` | `35c70f3b548122920a793c954130f45b3b314af6e602c1325782e3e57c2c9913` (23) |
| `Toy.Rice.Controls.incompleteAll_tight_switchAdmissible` | W5 counterexample (hsw) | `propext` | `b3140d3a735019feaa2b40f6dd15a64d6d26c566cdc441b9369050a75f130602` | `004b7f50f96e30df6f90e2b3afef1fd7e778401931ead3a9e1cc68c315e57380` (22) |
| `Toy.Rice.Controls.incompleteAll_tight_violated` | W5 counterexample (hviol) | `propext` | `b60e16be31ecdff8db8eae37502516d18b65a4cd4f1a1c9ca9aca098e822d542` | `2592217c4b06065d3cc1804b1ad055017a7f21c3b668d621037cc26b98227ae4` (23) |
| `Toy.Rice.Controls.rejectAll_nonvacuous` | W1 non-vacuity | `propext` | `0e308e1c04b4bea21d3f1d38d09b6f46a7dba855d25154a53141d13dd5a873e6` | `731dbda7166c4856e7f63d8a57226f3033a3e3dc7f53d3d4539d33f24e76c21b` (20) |
| `Toy.Rice.Controls.rejectAll_tight_constClosed` | W1 counterexample (hconst) | none | `5e1547a9f070e8e0bef6418c0693128f2e107e0f32ddbd52d6e6a7163e0bd8d8` | `97ad4f5a14f53fda0511efe049525a97bce3b2c719398144b0c3c0f40c6c649f` (8) |
| `Toy.Rice.Controls.restrict_nonvacuous` | R6 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `9787799c5acca78a26a2a54fed2dfbf3d063fe5fd4dbce73b8a08ff63ecfa100` | `681356d9f9e9f55d51dfce29544dd73e81a61a04a76ffc9551f4fc231484ec0e` (25) |
| `Toy.Rice.Controls.restrict_tight_eqTestClosed` | R6 positive control; R6 counterexample (heq) | `Classical.choice`, `Quot.sound`, `propext` | `d015a73b4a3af164539f9fe376ee421784a495dd38b75fe7844f6e6138e89480` | `a555d0e0036a569414bb1fbb7cb6405af5ab8a2eb2a9bcc6c030757fb1469786` (65) |
| `Toy.Rice.Controls.restrict_tight_extensional` | R6 counterexample (hext) | `Classical.choice`, `Quot.sound`, `propext` | `7fbab3d8fb05488d55c5c647f59d398ba1028d82aa7707dc408dd8e9e100f04f` | `1513780a7aadb4c9a7d5331bd2bb46808b70886112d1cbd5b259d973c97069c1` (29) |
| `Toy.Rice.Controls.restrict_tight_extensionalFragment` | R6 counterexample (hF) | `Classical.choice`, `Quot.sound`, `propext` | `4dc7332e04c605de19016af7ad6511a412c8e59e2ce80cfe7807677016303c58` | `4f28f11ff7d93d60f23e4ba939825b8992f2bb76da42e05de780ed1d58d840aa` (29) |
| `Toy.Rice.Controls.restrict_tight_fixpointPrinciple` | R6 counterexample (hfix) | `Classical.choice`, `Quot.sound`, `propext` | `0139aaeaa2a2a61ce54ce386052682d9b2a6c37026b5d04604f39b47830c62b2` | `369d45f681ccb4ac56c27576553cc19b3d279ab59258caa0aeaea8c947ba926b` (15) |
| `Toy.Rice.Controls.restrict_tight_hasMember` | R6 counterexample (hnt.1) | `Classical.choice`, `Quot.sound`, `propext` | `09007a6d40a7e16e22763d43e857ca934147cbb7c7e13421650556a060112a6f` | `7736c0108ecc34454c599417a1c0a83d4ccdfb1d7867f3ca6176cdcfbfdd234a` (26) |
| `Toy.Rice.Controls.restrict_tight_hasNonMember` | R6 counterexample (hnt.2) | `Classical.choice`, `Quot.sound`, `propext` | `78a8567a80bf4a5d6fe0661ee287a834ff9869d2ac5f8dd8abce3c5570da9901` | `7736c0108ecc34454c599417a1c0a83d4ccdfb1d7867f3ca6176cdcfbfdd234a` (26) |
| `Toy.Rice.Controls.riceChar_nonvacuous` | R4 non-vacuity | `propext` | `fcedd905fcdb7b03ce4a6e0623844456836b3afb3786209db59c6fc1ffda03db` | `5628a1c783962b0fe7b4ab315392b0e81ddc04926591e482cf9c2140b0673a16` (26) |
| `Toy.Rice.Controls.riceChar_tight_constClosed` | R4 counterexample (hconst) | none | `ddb68a19438b7d7579b9fdbaac99eea20b17ea5276a557b4c2b6d03a7001c59a` | `6bf67d420a528ce047106a66f4c46ccfacce8390bd4401061ce188482c078ee0` (13) |
| `Toy.Rice.Controls.riceChar_tight_extensional` | R4 counterexample (hext) | `Quot.sound`, `propext` | `86c31893df42014ab1d5cf07d25b94e74855c765881dd1fc361f93f3d7c0719c` | `0ed23badb6282adde1ec09bf7cdabe501fbadc7a05442322778316b18efb22ef` (26) |
| `Toy.Rice.Controls.riceChar_tight_fixpointPrinciple` | R4 counterexample (hfix) | `Classical.choice`, `Quot.sound`, `propext` | `46cef16b616e78a971eb05be9f329e8efa45cb7287c034549b8bfb88827fde54` | `7b0012efd776728ac7f02fb919c997663f10cc49da01c7ad5820d8f7bda1c148` (60) |
| `Toy.Rice.Controls.riceSharp_nonvacuous` | R2 non-vacuity | `propext` | `c7304af40224dc35e4a9751d907d8ee88c8c27be8e16aba01c928da718c932b8` | `a605bc7af17027fa81a6d96ae09c15d2046c060c5d37a4bb1cbc805c8fc7ffbd` (24) |
| `Toy.Rice.Controls.riceSharp_tight_decides` | R2 counterexample (hdec) | none | `c7742fcea61ebb86e8787d25e429e44083115ee9dad8028d5d9d7047cad4e878` | `b3278433f9723144007ecfbe0066e1392c1cfb1328de9dd01be952a636be50b9` (17) |
| `Toy.Rice.Controls.riceSharp_tight_extensional` | R2 counterexample (hext) | `Quot.sound`, `propext` | `7acc6a3090acdd68895cabfa831b187e10dfca732044448cbf34ff40c80ee816` | `b057d60065e9197133f1a3b6313f912a71c1fcb68575a71d56397e6b28ff5b63` (24) |
| `Toy.Rice.Controls.riceSharp_tight_fixpointPrinciple` | R2 positive control; R2 counterexample (hfix) | `Classical.choice`, `Quot.sound`, `propext` | `327328e9f63436e839cde6535cc525596c0e0313eb31a3f5341d5468c17b6836` | `24caa05d4af9bca69f852b85ff0e6cbe7cc2f2b75a9bec2b009da27a9cf1cbe0` (58) |
| `Toy.Rice.Controls.riceSharp_tight_member` | R2 counterexample (ha) | `propext` | `60ac756a43af3f23de10440457eff63e6c1b4ced6bad2d070e94f3768a16eb8f` | `22271efe3f5448c4b475c19a0a9fd502b40510d0c34899410cde44ecce34a7bf` (25) |
| `Toy.Rice.Controls.riceSharp_tight_nonmember` | R2 counterexample (hb) | `propext` | `cc4c707a8b5784648089d40360a711842b88fc735da33dca29a2c65c7a5e1993` | `22271efe3f5448c4b475c19a0a9fd502b40510d0c34899410cde44ecce34a7bf` (25) |
| `Toy.Rice.Controls.rice_nonvacuous` | R1 non-vacuity | `propext` | `7443fae9a60199b519f9ce8f732c9be9010330fcb9ebb75788d3b4f26d86fbb2` | `e41e39ec69ca968056a40aa6aa5779cf1ffcd9f7ab6ec438cfc943e289865d1f` (30) |
| `Toy.Rice.Controls.rice_tight_extensional` | R1 counterexample (hext) | `Quot.sound`, `propext` | `238ea94a8d67b4db90781db717c127dead0ceceb605b69df28c8826bbdecb6ce` | `f2a42943322a3a603b3be22ba3bdbb83bd134b747ef91460704b806f5488fd1b` (26) |
| `Toy.Rice.Controls.rice_tight_fixpointPrinciple` | R1 positive control; R1 counterexample (hfix) | `Classical.choice`, `Quot.sound`, `propext` | `7e8bfa18b356ed766f9ae12c9cf70365e1840568152a5b80aebdde423ccd522f` | `a1f3deb327a5a916d6d451ee406462e1fa7bbdb9a8edcf442fe74f29894e6046` (60) |
| `Toy.Rice.Controls.rice_tight_nontrivial_hasMember` | R1 counterexample (hnt.1) | `propext` | `0bc10be242b5d3edd2b31d62fde5aa40b3c1ed77b3baff7c09dbcd246f569661` | `90c5281522fc5767ec90b586c6612684c4cf0060a7565062b25101d0ae271f74` (24) |
| `Toy.Rice.Controls.rice_tight_nontrivial_hasNonMember` | R1 counterexample (hnt.2) | `propext` | `8b01268dd341aed368ff99d07d51b7abc41083dc029b4f18ee3ff345e282f49d` | `90c5281522fc5767ec90b586c6612684c4cf0060a7565062b25101d0ae271f74` (24) |
| `Toy.Rice.Controls.semConst_nonvacuous` | F4 non-vacuity | none | `2cf8b8bcdeff5dcaf00c11b514e2fea8d3a98973a30e6c8390c4099453c327fe` | `7af01e7f1d477d8761afaf53f6d4e08aaeb5ee8a1df88d3cb4e00582ed1a7ce3` (10) |
| `Toy.Rice.Controls.semConst_tight_allSwitches` | F4 counterexample (hall) | none | `c71e50ad0de87eb6c97b77418c8574bed11bfd8fba3de07876a963d0d9c81ffb` | `33a9a3e27b473ee4f4be29c2b1187b50e7164f6f4d52c463322b583c9a249b67` (14) |
| `Toy.Rice.Controls.semConst_tight_fixpointPrinciple` | F4 counterexample (hfix) | none | `8f93b4256a38da482b6fd801f5343583bdfa13b2cd6b0300093081522495bc40` | `488a8c4b14f4edff8e47ab8571990ebdf88e3ec7eff7a7cc54ee7c2c620ce5f5` (9) |
| `Toy.Rice.Controls.soundSplit_nonvacuous` | W7 non-vacuity | `propext` | `4b25ee127589740b5b04faf61dad23fdaa9887f0c4f44c1210dc372c8feaaf01` | `320a9abca32983afec7f8bb8de6c36b87d8f110f4d43b3dc01d23e3e6f3c7407` (25) |
| `Toy.Rice.Controls.soundSplit_tight_accepts` | W7 counterexample (hacc) | `propext` | `25b503911f6d38378cd71c32cfd54c05e99ad92a201d578d413f2589f3528d58` | `f3ce384c66002fbf8fb23fa7ab94d758936e3f9f212e64237b3f827af5411740` (24) |
| `Toy.Rice.Controls.soundSplit_tight_extensional` | W7 counterexample (hext) | `propext` | `546216e56cb30fdc83a369a753044fc4e80c00e53436459fd60d3fa2d5104245` | `ff246b4ae2f22b9c85acce4259ea52cc6bd0397b6abb57aec6286b4a54fcf829` (23) |
| `Toy.Rice.Controls.soundSplit_tight_fixpointPrinciple` | W7 positive control; W7 counterexample (hfix) | `Classical.choice`, `Quot.sound`, `propext` | `aeac5daac66300b1c31f4ef57d031939ff2bbcc45f7b614e0b6a0a4f466c6b3c` | `a6af86f93a9a9598380570e318ea3ced739c5102a19b54b75c350af73959d8f0` (59) |
| `Toy.Rice.Controls.soundSplit_tight_rejects` | W7 counterexample (hrej) | `propext` | `4e4da598b9f8fa82e485262dea55d9a8efee5534fbeaaa514431be3be3ec83bf` | `2592217c4b06065d3cc1804b1ad055017a7f21c3b668d621037cc26b98227ae4` (23) |
| `Toy.Rice.Controls.soundSplit_tight_sound` | W7 counterexample (hsound) | `propext` | `47c7f616d9a8ecc0d634c07dc98952c381d6059ce8fcbd60e49ca899ebb9168c` | `a9b50e0243a403b5d0c5f4c786e87b28bdb1fa93942eec17d1d161fac22fe8b3` (23) |
| `Toy.Rice.Controls.soundSplit_tight_switchAdmissible` | W7 counterexample (hsw) | `propext` | `c791ac03e6d2390f58ec313405d1c1328a589a29fad1cae428c1f03022a7b2c6` | `004b7f50f96e30df6f90e2b3afef1fd7e778401931ead3a9e1cc68c315e57380` (22) |
| `Toy.Rice.Controls.splitAll_nonvacuous` | W6 non-vacuity | `propext` | `4146344918fd2929ebfe09af86b8aa492db08d983b586b71a8bc35edcde77850` | `9ab6d3e9ff284e4b787d9be0d803d386fcb888564b88c4569e35139d2d1c1e69` (22) |
| `Toy.Rice.Controls.splitAll_tight_fixpointPrinciple` | W6 positive control; W6 counterexample (hfix) | `Classical.choice`, `Quot.sound`, `propext` | `8ddbd8ca97d492db9e94bc2e365125763b81640b12c4bbe1e15d62166eecbbd4` | `a03be30e9460f44f4cd705afb3be3e55b5809e09f95f970c0eb2c0d8cdfae495` (56) |
| `Toy.Rice.Controls.splitAll_tight_switchAdmissible` | W6 counterexample (hsw) | `propext` | `db629a64afe3172adba5f3abb198b64d56ea5dc74c20df3158d2c83d289c86cd` | `403f31e95797736e5d77a6cb7777a6289ff2bfc32471c1539388e6294d85355e` (19) |
| `Toy.Rice.Models.kleene_nonvacuous` | F3 non-vacuity | `Quot.sound`, `propext` | `c1fca5e41e124bcd0375909a0a76c3fa778e8b8369930b6d06480e27512ea852` | `96a468101ed16e6bb96640dc403e9ce1cb287d641190e0757b283c2844be8d2c` (15) |
| `Toy.Rice.Models.kleene_tight_diagonal` | F3 counterexample (hdiag) | none | `13bc54e26b29c8e78c46198033edfd2777e73c0c59d45d5a0d2a76d698c86f1c` | `0cc925399867d711884acc336450abc91b6077924de50d63bfc6269177cb4d6c` (13) |
| `Toy.Rice.Models.kleene_tight_precompClosed` | F3 counterexample (hpre) | `propext` | `f8eb0a588bf0c379ffda5f3beec386e0014e4f589549b7e28e0f821fcd25cf38` | `b76156bc6ef303ebf3f31dacbf8ec8ddb98908af0e7d87044834615f02e7287a` (13) |
| `Toy.Rice.Models.kleene_tight_represents` | F3 counterexample (hrep) | `propext` | `25fc52fe7b61ddea8e269f05cafa1de801932e066beb826f7f17eed07afed78b` | `e57dd757e251d6031026e6738d8643a94554d8bc8ce02a19bc3ab07dc08aab4b` (12) |
| `Toy.Rice.Models.lawvere_nonvacuous` | F1 non-vacuity | none | `45021e52a6370378ab7cc3602058b149f4cbf4e73bb13e01d6f9ebec07903f67` | `b4eaa80213f52ae738c93ca66ada4e8345e9e25d351775e932c38fed4499fc09` (2) |
| `Toy.Rice.Models.lawvere_tight_diagonal` | F1 counterexample (hdiag) | `propext` | `792b039d2d4f72d1d524bf8b9884500458fd7256dec76e0cee259d316b1d4f4f` | `2c2a7fd84deb4141a8c89aa92084ead3e2aaa2a641e06a02adff3984ab57eb28` (3) |
| `Toy.Rice.Models.lawvere_tight_represents` | F1 counterexample (hrep) | none | `99d71017a86ac683cfbd0ec0efcfd46d4c4cdba739ca98974cb02166776c8e83` | `e471d4eeafa0b5c16e756ad9cfdc44dedc20102bfa302a8ffc4ffcd26167c0f4` (2) |

#### Related lemmas (axioms; not hashed)

| Lemma | Axioms |
| :--- | :--- |
| `Toy.Rice.decidedInside_iff_ite_admissible` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.Rice.not_decidedBy_of_fixpointPrinciple_switchClosed_extensional_nontrivial` | `propext` |
| `Toy.Rice.exists_fixedPoint_of_represents_diagonal` | none |
| `Toy.Rice.subsingleton_of_weaklyPointSurjective` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.Rice.fixpointPrinciple_of_represents_diagonal_precompClosed` | none |
| `Toy.Rice.exists_satisfying_rejected_of_fixpointPrinciple_extensional_nontrivial_sound_switchAdmissible` | `propext` |
| `Toy.Rice.forall_exists_sameSem_accepted_of_fixpointPrinciple_extensional_satisfied_complete_switchAdmissible` | `propext` |
| `Toy.Rice.exists_sameSem_accepted_rejected_of_fixpointPrinciple_switchAdmissible` | `propext` |
| `Toy.Rice.not_forall_sameSem_accepted_and_forall_sameSem_rejected_of_fixpointPrinciple_switchAdmissible` | `propext` |
| `Toy.Rice.sameSem_split_iff_not_forall_sameSem_accepted_and_forall_sameSem_rejected` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.Rice.Lifted.switchAdmissible_const` | none |
| `Toy.Rice.Lifted.not_decidedInside_of_nontrivial` | none |
| `Toy.Rice.Lifted.isEmptyTable_not_decidedInside` | none |
| `Toy.Rice.Controls.verdictSplit_unrealizableBehaviour` | none |
| `Toy.Rice.Controls.incompleteAll_unrealizableBehaviour` | `propext` |
| `Toy.Rice.fixpointPrinciple_of_compClosed_represents_diagonal` | none |
| `Toy.Rice.Lifted.not_eqTestClosed` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.Rice.exists_sameSem_rejected_of_fixpointPrinciple_extensional_sound_swappedSwitch` | `propext` |

### Primary sources

Every prior-art record cited in Findings, once each:

- H. G. Rice, "Classes of recursively enumerable sets and their decision problems", Transactions of the American Mathematical Society 74(2) (1953), 358-366, DOI 10.1090/S0002-9947-1953-0053041-6. The original theorem: an index set of r.e. sets is recursive only if it is trivial.
- H. Rogers, Jr., Theory of Recursive Functions and Effective Computability, McGraw-Hill, New York, 1967; reprinted MIT Press, Cambridge, MA, 1987, ISBN 978-0-262-68052-3. Standard textbook treatment of acceptable numberings, the recursion theorem, index sets, recursive inseparability, Rice's theorem and the Rice-Shapiro theorem; cited as a general reference, no page or theorem number is claimed.
- N. S. Yanofsky, "A universal approach to self-referential paradoxes, incompleteness and fixed points", Bulletin of Symbolic Logic 9(3) (2003), 362-386, DOI 10.2178/bsl/1058448677 (arXiv:math/0305282). Derives the recursion theorem from Lawvere's scheme (Theorem 5 in the arXiv text) and proves Rice's theorem with the swapped case split h(x) = a if x is not in A, b if x is in A.
- Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Computability/Halting.lean: ComputablePred.rice (line 32), proved from Nat.Partrec.Code.fixed_point₂ with a swapped Partrec.cond, and ComputablePred.rice₂ (line 42): a predicate on codes that respects eval is computable iff it is empty or everything. Described in prose only; not a dependency.
- uds-psl/coq-synthetic-computability, theories/Basic/Rice.v at commit 7e019a047314a75d90f33899a6ff023a22e9d618: Lemma FP (line 97: every f has e with Θ e ≡ Θ (f e), from an abstract enumerability principle) and Lemma Rice_Theorem' (line 112; the swapped case split is at line 118). The closest existing mechanization of Rice's theorem from an abstract fixed-point lemma; it does not separate an admissible class from the ambient function space. Associated thesis: Y. Forster, Computability in Constructive Type Theory, Saarland University, 2021, DOI 10.22028/D291-35758.
- Y. Forster and G. Smolka, "Weak call-by-value lambda calculus as a model of computation in Coq", ITP 2017, LNCS 10499, 189-206, DOI 10.1007/978-3-319-66107-0_13; uds-psl/coq-library-undecidability, theories/L/Computability/Scott.v at commit 138245ce9172b45d91ec49eda1cc67ef155bc14e: Theorem Scott (line 6), proved from SecondFixedPoint with a swapped case split.
- M. Norrish, "Mechanised computability theory", ITP 2011, LNCS 6898, 297-311, DOI 10.1007/978-3-642-22863-6_22. HOL4 mechanization including the recursion theorem, an s-m-n instance and Rice's theorem.
- M. Nedzelsky, "Recursion Theory I", Archive of Formal Proofs, April 2008, https://isa-afp.org/entries/Recursion-Theory-I.html; F. J. Balbach, "Some classical results in inductive inference of recursive functions", Archive of Formal Proofs, August 2020, https://www.isa-afp.org/entries/Inductive_Inference.html. Isabelle/HOL mechanizations that include Rice's theorem (Balbach also s-m-n and recursion theorems of Kleene, Rogers and Smullyan).
- M. Carneiro, "Formalizing computability theory via partial recursive functions", ITP 2019, LIPIcs 141, 12:1-12:17, DOI 10.4230/LIPIcs.ITP.2019.12. The reference for Mathlib's computability library.
- A. Asperti, "The intensional content of Rice's theorem", in: Proceedings of the 35th Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '08), San Francisco, ACM, 2008, 113-119, DOI 10.1145/1328438.1328455. Replaces extensional index sets by complexity cliques (sets of indices closed under same behaviour and similar complexity) and proves, under weak complexity assumptions, that every recursive complexity clique is trivial and every r.e. complexity clique is extensional. Cited only for the cost-model non-claim; no statement here models complexity.
- S. C. Kleene, "A symmetric form of Gödel's theorem", Proceedings of the KNAW 53 (1950), 800-802; also Indagationes Mathematicae 12 (1950), 244-246; no DOI; KNAW Digital Library record PU00014670, https://dwc.knaw.nl/DL/publications/PU00014670.pdf (a scan of Proceedings volume 53, Nos. 6-10, pp. 685-1656, containing the article at pp. 800-802). Constructs two disjoint r.e. sets that no recursive set separates (recursive inseparability).
- F. W. Lawvere, "Diagonal arguments and cartesian closed categories", in Category Theory, Homology Theory and their Applications II, Lecture Notes in Mathematics 92, Springer, 1969, 134-145, DOI 10.1007/BFb0080769; reprinted with commentary in Reprints in Theory and Applications of Categories No. 15 (2006), 1-13. Theorem 1.1 (checked in the reprint): in any cartesian closed category, if there is a weakly point-surjective morphism A -> Y^A then Y has the fixed point property; Cantor's theorem follows with Y = 2.
- Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Logic/Function/Basic.lean: Function.exists_fixed_point_of_surjective (lines 367-368; documented as Lawvere's fixed-point theorem for types and functions) and Function.cantor_surjective (line 374). Prose only.
- D. Scott, "Continuous lattices", in Toposes, Algebraic Geometry and Logic, Lecture Notes in Mathematics 274, Springer, 1972, 97-136, DOI 10.1007/BFb0073967. Constructs a continuous lattice isomorphic to its own function space (a model of the lambda calculus).
- A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2) (1955), 285-309, DOI 10.2140/pjm.1955.5.285. Every monotone map on a complete lattice has a fixed point.
- S. C. Kleene, "On notation for ordinal numbers", Journal of Symbolic Logic 3(4) (1938), 150-155, DOI 10.2307/2267778. The first published statement and proof of the (second) recursion theorem, according to Moschovakis (2010).
- S. C. Kleene, Introduction to Metamathematics, Van Nostrand / North-Holland, 1952. States and proves the recursion theorem and the first recursion theorem (least fixed points of monotone recursive operators); cited without section numbers.
- Y. N. Moschovakis, "Kleene's amazing second recursion theorem", Bulletin of Symbolic Logic 16(2) (2010), 189-239, DOI 10.2178/bsl/1286889124. Survey of the second recursion theorem and its uses.
- Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Computability/PartrecCode.lean: Nat.Partrec.Code.fixed_point (line 1021; documented as "Roger's fixed-point theorem": every total computable f : Code -> Code has c with eval (f c) = eval c) and fixed_point₂ (line 1039; Kleene's second recursion theorem). Prose only.
- A. R. Meyer and D. M. Ritchie, "The complexity of loop programs", Proceedings of the ACM National Conference 1967, 465-469, DOI 10.1145/800196.806014. Theorem 7: the functions computable by Loop programs are exactly the primitive recursive functions. (Cited only for that fact.)
- P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, 238-252, DOI 10.1145/512950.512973. Foundational framework for sound but incomplete static analyzers; cited as context for the design space, not for any statement here.
- Mathlib (leanprover-community/mathlib4, commit e237a521d16607fe82439145293b89fbd0e74678), Mathlib/Computability/Halting.lean: ComputablePred.halting_problem_re (line 60: the halting predicate is r.e.) and ComputablePred.halting_problem (line 64: it is not computable). Prose only.
- H. G. Rice, "On completely recursively enumerable classes and their key arrays", Journal of Symbolic Logic 21(3) (1956), 304-308, DOI 10.2307/2269105. With Myhill and Shepherdson (1955), the source of the Rice-Shapiro characterization of semi-decidable extensional properties, which this package does not formalize.
- J. Myhill and J. C. Shepherdson, "Effective operations on partial recursive functions", Zeitschrift für mathematische Logik und Grundlagen der Mathematik 1(4) (1955), 310-317, DOI 10.1002/malq.19550010407.

Verification of the records (2026-11-20 unless stated): DOIs, venues and pages were checked by bibliographic lookup. Line-numbered repository citations were re-read from the raw files at the stated commits: Mathlib `Mathlib/Computability/Halting.lean` lines 32, 42, 60, 64; `Mathlib/Computability/PartrecCode.lean` lines 1021 and 1039; `Mathlib/Logic/Function/Basic.lean` lines 367-368 and 374; coq-synthetic-computability `theories/Basic/Rice.v` lines 97, 112 and 118; coq-library-undecidability `theories/L/Computability/Scott.v` line 6. Meyer and Ritchie's Theorem 7 was checked in the authors' text. Kleene (1950) has no assigned DOI (a Crossref bibliographic search on 2026-11-20 found only a 1951 review of it in the Journal of Symbolic Logic, DOI 10.2307/2266709); it is identified by its dual print pagination and by the KNAW Digital Library record `PU00014670`. That record is a scan of the whole of Proceedings volume 53, Nos. 6-10 (pp. 685-1656); the PDF retrieved from https://dwc.knaw.nl/DL/publications/PU00014670.pdf on 2026-11-20 had SHA-256 `573d04d5448a7293142ee953175e7697165a986fc1f155b2aea8707601de8c82`, its index lists the article at p. 800, and the article's title page appears in the scan. The URL is not guaranteed to serve the same file in future; the print coordinates are the durable identity. Lawvere's Theorem 1.1 was checked in the 2006 reprint and Yanofsky's Theorem 5 and Rice application in the arXiv text. None of these sources is a Lean dependency; they are prior art for the statements.

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The package has no Lean dependencies.

**Primary check**, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects Lean sources containing `sorry`, `admit`, `native_decide` or an `axiom` declaration, applies `Lean.collectAxioms` to every declaration of the `ToyRice` library (allowed: `propext`, `Classical.choice`, `Quot.sound`), and recomputes, for every Lean name referenced by `results.json`, the statement hash and closure hash exactly as defined under Evidence, comparing them with `audit/statements.json`. It prints `REVALIDATED` and exits with status 0 iff every check passes.

**Equivalent manual check** with the included audit program `lean/RevalidationAudit.lean` (outside the library target, so `lake build` does not build it). For every name referenced by `results.json` it prints a line `STMT {json}` with the name, its axioms, the `repr` of its type and its closure entries; it ends with `DECLS <n> OUTSIDE_ALLOWED <m>`. Run from the package directory:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/toyrice_audit.txt
grep -E '^(MISSING|OUTSIDE_ALLOWED|DECLS)' /tmp/toyrice_audit.txt
python3 - <<'EOF'
import hashlib, json
rec = json.load(open("../audit/statements.json"))["statements"]
seen, bad = set(), []
for line in open("/tmp/toyrice_audit.txt", encoding="utf-8"):
    if line.startswith("STMT "):
        s = json.loads(line[5:])
        got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
               "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
               "closure_size": len(s["closure"])}
        seen.add(s["name"])
        if rec.get(s["name"]) != got:
            bad.append(s["name"])
print("hashed:", len(seen), "recorded:", len(rec), "mismatched:", bad,
      "unrecorded or missing:", sorted(set(rec) ^ seen))
EOF
```

Expected output: the `grep` prints only `DECLS 658 OUTSIDE_ALLOWED 0`, and the Python snippet prints `hashed: 74 recorded: 74 mismatched: [] unrecorded or missing: []`. The axioms of each card name are in the `axioms` field of its `STMT` line; `#print axioms <name>` after `import ToyRice` gives the same answer for a single declaration.

**What a pass establishes.** The statements, with their definition closures, are unchanged and kernel-checked under the pinned toolchain using only the standard axioms. It does not re-check the plain-language claims, the non-claims, the modeling bridges or the citations, which are prose. Under a different Lean version `repr` output can change, so the hashes may differ even if the statements are unchanged; in that case compare the printed statements with the Lean blocks quoted under Findings.
