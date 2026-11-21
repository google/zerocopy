# Frame-rule locality and precise assertions: formalized results in Lean 4

## Summary

This package mechanizes, in Lean 4 without Mathlib, the exact relationship between the
frame rule of separation logic and the locality of commands, which plausible commands are
not local and why, how precision of a frame relates to the conjunction-distribution law,
and what frame-quantified ("baked-in frame") triples need from the state model. All
results are stated over a deliberately weak abstract *separation structure* (a carrier
with a disjointness relation and a total union, no laws) and over a finite-heap model;
every algebraic law a result uses appears as an explicit, named hypothesis.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (identifiers are the result ids used throughout; the Lean names
are under **Findings**):

* **R1** — In any separation structure (no laws), a command that is safety-monotone and has the frame property satisfies the frame rule {P} c {Q} ⟹ {P * R} c {Q * R} for fault-avoiding partial-correctness triples and every assertion R.
* **R2a** — In any separation structure, if the frame rule holds for c at every singleton instance (precondition {h}, strongest postcondition of c from h, frame {h'}), then c is safety-monotone and has the frame property.
* **R2b** — In any separation structure, the frame rule is sound for c for all assertions iff c is safety-monotone and has the frame property (assertions range over all predicates; triples are fault-avoiding).
* **R2c** — In any separation structure, the frame rule restricted to precise frames already forces safety monotonicity and the frame property.
* **R3a** — In the heap model, the allocation test isAllocTest k r (record in cell r whether cell k is allocated) is safety-monotone but, for k ≠ r, violates the frame property and the frame rule.
* **R3b** — In the heap model, fixed-address allocation that faults when the address is taken (allocAt k v) has the frame property but violates safety monotonicity and the frame rule; the variant that blocks instead of faulting (allocAtBlock) is local.
* **R3c** — In the heap model, least-free-address allocation (allocLeast v) is safety-monotone but violates the frame property and the frame rule.
* **R3d** — In the heap model, a command that is safe at some heap hb, allocates a fixed address a free in hb on every normal run from hb, and still has a normal run when a frame occupies a, violates the frame property; so do every total deterministic single-cell writer detAlloc f v and fresh deterministic pointer-recording allocation.
* **R3e** — With non-fault-avoiding partial-correctness triples the frame rule fails even for a local command (assertAlloc 0).
* **R4a** — In any separation structure, the distribution law (P * R) ∧ (Q * R) ⊢ (P ∧ Q) * R holds for all P, Q exactly when R has unique frames (not exactly when R is precise).
* **R4b** — In a right-cancellative separation structure (no other laws), every precise R satisfies the distribution law.
* **R4c** — In a left-cancellative separation structure (no other laws), every R satisfying the distribution law is precise.
* **R4d** — In the finite-heap model, R is precise (equivalently, every heap has at most one subheap satisfying R) iff R satisfies the distribution law.
* **R4e** — In the heap model, 'exactly one cell, at some address' and 'some cell is allocated' are imprecise and violate the distribution law.
* **R4f** — In unital partial commutative monoids that are not cancellative, precision and the distribution law are incomparable (OrAlg: precise but not distributing; Fork: distributing but not precise).
* **R4g** — With symmetric disjointness and commutative union, left and right cancellativity are equivalent (reference point used by R4b–R4d).
* **R5** — In the heap model, lookup, mutation, allocation at a nondeterministically chosen fresh address (with or without recording it) and deallocation are each safety-monotone and have the frame property.
* **R6a** — In any separation structure with both directions of partial associativity (no locality, commutativity, unit or cancellativity), frame-quantified triples FQTriple P c Q := ∀ R, {P * R} c {Q * R} satisfy the frame rule for every command; with the explicit hypothesis hs : DisjSymm S (symmetric disjointness), the left-to-right direction (UnionAssoc) alone also suffices, but without DisjSymm it does not, even together with commutativity of union (UnionComm).
* **R6b** — In any separation structure with a right unit, a frame-quantified triple implies the plain triple, for every command.
* **R6c** — For the non-local allocLeast, {emp} allocLeast 1 {0 ↦ 1} holds as a plain triple but not frame-quantified, while {emp} allocLeast 1 {∃ k. k ↦ 1} holds frame-quantified.
* **R7** — Boundary witnesses: the Hoare conjunction rule needs no precision; locality does not preserve termination; with empty disjointness every command is local and every assertion precise, and without a unit even the always-true assertion can be precise; right- and left-handed precision (and distribution) coincide under symmetric disjointness and commutative union and can differ when either is missing; a heap command safe on emp that faults somewhere is not safety-monotone; over an uninhabited value type every command is local.

What these results do **not** show is listed first under **Boundaries** (per result), and
again in each result's `non_claims` in `results.json`. In particular: everything is
partial correctness with no termination guarantee; the model has no variable store,
no address arithmetic and no concurrency; and "proved" means proved about these Lean
definitions, not about any particular program logic or verifier.
Model–system relation: none proved. These are statements about the toy model; they neither
establish nor refute the corresponding claims about real separation logics or the
mechanized frameworks and verifiers built on them (such as HOL4's separation-logic
framework, VST's `msl` and Isabelle's `Separation_Algebra`).

## Applicability

### Model fidelity

This is a **toy model**, not a mirror of any production definitions.

* **Separation structure.** `SepStruct S` is a carrier `S` with a relation
  `disj : S → S → Prop` and a total function `union : S → S → S` (meaningful only on
  disjoint arguments). No law is bundled: symmetry of disjointness (`DisjSymm`),
  commutativity (`UnionComm`), the two directions of partial associativity
  (`UnionAssoc`, `UnionAssocRev`), left and right units (`UnitLaw`, `RightUnitLaw`) and
  left and right cancellativity (`LeftCancel`, `RightCancel`) are separate `Prop`s.
  It is meant to capture the separation algebras / partial commutative monoids of
  abstract separation logic (Calcagno, O'Hearn and Yang 2007) and of mechanized
  frameworks (HOL4's separation-logic framework, VST's `msl`, Isabelle's
  `Separation_Algebra`). Known gaps: union is a *total function* rather than a
  relation (no non-functional joins as in Dockins, Hobor and Appel 2009); a single
  global unit (no multi-unit algebras); no positivity law; no step-indexing, no
  ownership/permission accounting beyond what a carrier encodes.
* **Commands.** `Cmd S := S → Outcome S → Prop` with `Outcome S = fault | ok s`:
  arbitrary relations, so nondeterminism, divergence and blocking are all allowed.
  This is the relational reading of "local actions" (Calcagno, O'Hearn and Yang 2007,
  with `fault` as top). No syntax, sequencing, loops or concurrency are modeled.
* **Triples.** `Triple P c Q` is fault-avoiding partial correctness: from every state
  satisfying `P`, `c` cannot fault and every normal final state satisfies `Q`.
  Divergence is permitted; termination is never guaranteed. Assertions are arbitrary
  predicates on states (not restricted to upward-closed / intuitionistic ones).
* **Heap model.** `Heap V`: finite partial maps `Nat → Option V`; disjointness means no
  common allocated address; union takes each cell from whichever side has it. It is a
  cancellative partial commutative monoid with two-sided unit `emp`. There is no
  variable store (program-variable writes are modeled by heap cells), no address
  arithmetic, no block structure or pointer provenance, and no memory bound (R7 only
  records that a command which is safe on `emp` but faults from some heap, as an
  out-of-memory fault would, is not safety-monotone).
* **Heap commands.** `lookup`, `mutate`, `alloc`, `allocInto`, `free` follow the
  standard small-axiom commands of separation logic; `allocAt`, `allocAtBlock`,
  `allocLeast`, `isAllocTest`, `assertAlloc`, `detAlloc`, `detAllocInto`,
  `detAllocOnEmp`, `faultOrSet0`, `skipOnEmp` are purpose-built witnesses. Their
  definitions are quoted under **Findings**.

### Toolchain and dependencies

* Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`),
  core Lean only: **no Mathlib**, no Lake dependencies (`lean/lakefile.toml` has one
  `[[lean_lib]]` named `Toy` and no `[[require]]`).
* All proofs use only the axioms `propext`, `Classical.choice`, `Quot.sound` (most use a
  subset; see **Evidence**).

### How the subjects relate

The Lean toolchain is the checker of every `execution (Lean kernel check)` finding. The
cited papers are the sources of the known results that this package restates (tiers
T0/T1); the HOL4 and VST repository revisions listed in `REPORT.json` were inspected as
source for specific prior-art claims (which theorems exist there and with which premises).
The package does not claim anything about the behaviour of those systems beyond the
quoted source facts.

### Related unpublished work (credited as context only)

Prototype separation-logic support for the Aeneas Rust verification toolchain, proposed
upstream but not merged at the time of observation, uses frame-quantified weakest
preconditions and upward-closed assertions over a partial commutative monoid. R6a and R6b
describe the algebraic requirements of that frame-quantified style; R2a and R4a do not
apply directly to upward-closed assertion languages, which cannot express singletons.
Nothing in this package depends on that work, and it is not a subject of this report.

### Exact observation versus broader applicability

Every theorem is a statement about the Lean definitions in `lean/Toy/Sep/`. Claims about
real program logics or verifiers appear only as separate lines labelled
`Basis: derived (modeling bridge)`, with their reasoning; they hold only insofar as the
target system's notions of separation structure, command, triple and assertion match
the definitions quoted here.

## Findings

All Lean code is in `lean/Toy/Sep/` (namespace `Toy.Sep`). Module map: `Basic.lean`
(separation structures, laws, commands, triples, locality, precision), `Heap.lean`
(finite heaps), `Commands.lean` (heap commands and their safety characterizations),
`Algebras.lean` (non-cancellative `OrAlg`, `Fork`), `Frame.lean` (R1–R2c),
`NonLocal.lean` (R3a–R3e), `Precision.lean` (R4a–R4g), `HeapLocal.lean` (R5),
`FrameQuantified.lean` (R6a–R6c), `Examples.lean` (proved positive and negative examples
for every definition, and admitted and excluded transitions for every command),
`NonVacuity.lean` (non-vacuity theorems), `Boundaries.lean` (R7), `Supplement.lean`
(the associativity simplification for R6a, the fresh-allocator witness for R3d, premise and
corollary tightness for R6a/R6b, tightness of `DisjSymm` and `UnionAssoc` in the `DisjSymm`
theorems of R6a, tightness and non-vacuity of the conjunction rule in R7, and the
uninhabited-value-type edge case).

Notation used in the unfolded readings: `a ⊥ b` is `disj a b`, `a ∘ b` is `union a b`,
`h k` is `h.val k`, `h[k ↦ v]` is `h.set k (some v)`, `(k ↦ v)` is `Heap.pt k v`,
`P * R` is `sep P R`, `{x}` is `sing x`.

Every theorem below was checked by the Lean kernel (`lake build` of the package, no
`sorry`); its axioms and statement hashes are listed under **Evidence**. Each result
records, in order: tier; plain claim; design question; the Lean statement(s); an unfolded
reading; the hypothesis ledger (each hypothesis, why it is needed, and its tightness —
`tight` with a Lean theorem stating that all other hypotheses hold and the conclusion
fails, or `harmless`); depth; non-vacuity witness; positive controls for the impossibility
result; prior art; and the two evidence-basis lines.

### Key definitions (quoted from the Lean sources)

From `lean/Toy/Sep/Basic.lean`:

```lean
class SepStruct (S : Type u) where
  /-- Disjointness: `disj a b` means `a` and `b` may be combined. -/
  disj : S → S → Prop
  /-- Combination; meaningful only on disjoint arguments. -/
  union : S → S → S

def DisjSymm (S : Type u) [SepStruct S] : Prop :=
  ∀ a b : S, disj a b → disj b a

def UnionComm (S : Type u) [SepStruct S] : Prop :=
  ∀ a b : S, disj a b → union a b = union b a

def UnionAssoc (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj a b → disj (union a b) c →
    disj b c ∧ disj a (union b c) ∧ union (union a b) c = union a (union b c)

def UnionAssocRev (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj b c → disj a (union b c) →
    disj a b ∧ disj (union a b) c ∧ union a (union b c) = union (union a b) c

def UnitLaw [SepStruct S] (e : S) : Prop :=
  ∀ a : S, disj e a ∧ union e a = a

def RightUnitLaw [SepStruct S] (e : S) : Prop :=
  ∀ a : S, disj a e ∧ union a e = a

def RightCancel (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj a c → disj b c → union a c = union b c → a = b

def LeftCancel (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj c a → disj c b → union c a = union c b → a = b

structure IsSepAlgebra (S : Type u) [SepStruct S] (e : S) : Prop where
  disjSymm : DisjSymm S
  comm : UnionComm S
  assoc : UnionAssoc S
  unit : UnitLaw e

inductive Outcome (S : Type u) where
  /-- The command faulted (e.g. accessed an unallocated cell). -/
  | fault : Outcome S
  /-- The command terminated normally in the given state. -/
  | ok : S → Outcome S

abbrev Cmd (S : Type u) := S → Outcome S → Prop

abbrev Assn (S : Type u) := S → Prop

def sep [SepStruct S] (P Q : Assn S) : Assn S :=
  fun h => ∃ h₁ h₂, disj h₁ h₂ ∧ h = union h₁ h₂ ∧ P h₁ ∧ Q h₂

def conj (P Q : Assn S) : Assn S := fun h => P h ∧ Q h

def sing (x : S) : Assn S := fun h => h = x

def post (c : Cmd S) (h : S) : Assn S := fun h' => c h (.ok h')

def Safe (c : Cmd S) (h : S) : Prop := ¬ c h .fault

def Triple (P : Assn S) (c : Cmd S) (Q : Assn S) : Prop :=
  ∀ h, P h → Safe c h ∧ ∀ h', c h (.ok h') → Q h'

def WeakTriple (P : Assn S) (c : Cmd S) (Q : Assn S) : Prop :=
  ∀ h, P h → ∀ h', c h (.ok h') → Q h'

def SafetyMono [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' : S, disj h h' → Safe c h → Safe c (union h h')

def FrameProp [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' h'' : S, disj h h' → Safe c h → c (union h h') (.ok h'') →
    ∃ h₀, c h (.ok h₀) ∧ disj h₀ h' ∧ h'' = union h₀ h'

def Local [SepStruct S] (c : Cmd S) : Prop :=
  SafetyMono c ∧ FrameProp c

def FrameRuleSound [SepStruct S] (c : Cmd S) : Prop :=
  ∀ P Q R : Assn S, Triple P c Q → Triple (sep P R) c (sep Q R)

def FrameRuleAtSingletons [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' : S, Triple (sing h) c (post c h) →
    Triple (sep (sing h) (sing h')) c (sep (post c h) (sing h'))

def Precise [SepStruct S] (R : Assn S) : Prop :=
  ∀ f₁ r₁ f₂ r₂ : S, disj f₁ r₁ → disj f₂ r₂ → union f₁ r₁ = union f₂ r₂ →
    R r₁ → R r₂ → r₁ = r₂

def FrameRuleForPreciseFrames [SepStruct S] (c : Cmd S) : Prop :=
  ∀ P Q R : Assn S, Precise R → Triple P c Q → Triple (sep P R) c (sep Q R)

def UniqueFrame [SepStruct S] (R : Assn S) : Prop :=
  ∀ f₁ r₁ f₂ r₂ : S, disj f₁ r₁ → disj f₂ r₂ → union f₁ r₁ = union f₂ r₂ →
    R r₁ → R r₂ → f₁ = f₂

def ConjDistrib [SepStruct S] (R : Assn S) : Prop :=
  ∀ (P Q : Assn S) (h : S), sep P R h → sep Q R h → sep (conj P Q) R h

def skip : Cmd S := fun h o => o = .ok h

def diverge : Cmd S := fun _ _ => False

def abort : Cmd S := fun _ o => o = .fault
```

From `lean/Toy/Sep/Heap.lean`:

```lean
structure Heap (V : Type) where
  /-- The contents of each address (`none` = unallocated). -/
  val : Nat → Option V
  /-- Only finitely many addresses are allocated. -/
  finite : ∃ n, ∀ k, n ≤ k → val k = none

def emp : Heap V := ⟨fun _ => none, ⟨0, fun _ _ => rfl⟩⟩

def pt (k : Nat) (v : V) : Heap V := emp.set k (some v)

def Disj (h₁ h₂ : Heap V) : Prop := ∀ k, h₁.val k = none ∨ h₂.val k = none

instance (V : Type) : SepStruct (Heap V) where
  disj := Heap.Disj
  union := Heap.join

def Sub (r h : Heap V) : Prop := ∀ k, r.val k ≠ none → h.val k = r.val k
```

```lean
-- Toy/Sep/Heap.lean (finiteness proofs elided as ⋯)
def set (h : Heap V) (k : Nat) (o : Option V) : Heap V :=
  ⟨fun j => if j = k then o else h.val j, ⋯⟩
def join (h₁ h₂ : Heap V) : Heap V :=
  ⟨fun k => (h₁.val k).or (h₂.val k), ⋯⟩
```

From `lean/Toy/Sep/Commands.lean`:

```lean
def assertAlloc (k : Nat) : Cmd (Heap V) := fun h o =>
  (h.val k = none ∧ o = .fault) ∨ (h.val k ≠ none ∧ o = .ok h)

def lookup (k r : Nat) : Cmd (Heap V) := fun h o =>
  ((h.val k = none ∨ h.val r = none) ∧ o = .fault) ∨
  (h.val k ≠ none ∧ h.val r ≠ none ∧ o = .ok (h.set r (h.val k)))

def mutate (k : Nat) (v : V) : Cmd (Heap V) := fun h o =>
  (h.val k = none ∧ o = .fault) ∨ (h.val k ≠ none ∧ o = .ok (h.set k (some v)))

def alloc (v : V) : Cmd (Heap V) := fun h o =>
  ∃ k, h.val k = none ∧ o = .ok (h.set k (some v))

def allocInto (r : Nat) (v : Nat) : Cmd (Heap Nat) := fun h o =>
  (h.val r = none ∧ o = .fault) ∨
  (h.val r ≠ none ∧ ∃ k, h.val k = none ∧ o = .ok ((h.set k (some v)).set r (some k)))

def free (k : Nat) : Cmd (Heap V) := fun h o =>
  (h.val k = none ∧ o = .fault) ∨ (h.val k ≠ none ∧ o = .ok (h.set k none))

def allocAt (k : Nat) (v : V) : Cmd (Heap V) := fun h o =>
  (h.val k ≠ none ∧ o = .fault) ∨ (h.val k = none ∧ o = .ok (h.set k (some v)))

def allocLeast (v : V) : Cmd (Heap V) := fun h o =>
  ∃ k, h.val k = none ∧ (∀ j, j < k → h.val j ≠ none) ∧ o = .ok (h.set k (some v))

def isAllocTest (k r : Nat) : Cmd (Heap Nat) := fun h o =>
  (h.val r = none ∧ o = .fault) ∨
  (h.val r ≠ none ∧ h.val k ≠ none ∧ o = .ok (h.set r (some 1))) ∨
  (h.val r ≠ none ∧ h.val k = none ∧ o = .ok (h.set r (some 0)))

def detAlloc (f : Heap V → Nat) (v : V) : Cmd (Heap V) := fun h o =>
  o = .ok (h.set (f h) (some v))

def detAllocInto (f : Heap Nat → Nat) (r v : Nat) : Cmd (Heap Nat) := fun h o =>
  (h.val r = none ∧ o = .fault) ∨
  (h.val r ≠ none ∧ o = .ok ((h.set (f h) (some v)).set r (some (f h))))

def detAllocOnEmp (v : V) : Cmd (Heap V) := fun h o =>
  h = Heap.emp ∧ o = .ok (Heap.pt 0 v)

def allocAtBlock (k : Nat) (v : V) : Cmd (Heap V) := fun h o =>
  h.val k = none ∧ o = .ok (h.set k (some v))
```

From `lean/Toy/Sep/NonLocal.lean`:

```lean
def AlwaysAllocatesAt (c : Cmd (Heap V)) (hb : Heap V) (a : Nat) : Prop :=
  ∀ h₀, c hb (.ok h₀) → h₀.val a ≠ none

def RunsWhenOccupied (c : Cmd (Heap V)) (hb : Heap V) (a : Nat) (w : V) : Prop :=
  ∃ h'', c (union hb (Heap.pt a w)) (.ok h'')

def faultOrSet0 (v : V) : Cmd (Heap V) := fun h o => o = .fault ∨ o = .ok (h.set 0 (some v))
```

From `lean/Toy/Sep/FrameQuantified.lean`:

```lean
def FQTriple {S : Type u} [SepStruct S] (P : Assn S) (c : Cmd S) (Q : Assn S) : Prop :=
  ∀ R : Assn S, Triple (sep P R) c (sep Q R)

@[reducible] def emptyDisjSepStruct : SepStruct Unit := ⟨fun _ _ => False, fun a _ => a⟩

inductive AssocGap where
  | p | r | s | m | t
  deriving DecidableEq

namespace AssocGap

def disjB : AssocGap → AssocGap → Bool
  | .p, .r => true
  | .m, .s => true
  | _, _ => false

def unionG : AssocGap → AssocGap → AssocGap
  | .p, .r => .m
  | .m, .s => .t
  | _, _ => .p

end AssocGap

instance : SepStruct AssocGap where
  disj x y := AssocGap.disjB x y = true
  union := AssocGap.unionG

def AssocGap.faultAtT : Cmd AssocGap := fun x o => x = .t ∧ o = .fault

inductive OneWayAssoc where
  | s0 | s1 | s2
  deriving DecidableEq

namespace OneWayAssoc

def disjB : OneWayAssoc → OneWayAssoc → Bool
  | .s0, .s0 => true
  | .s0, .s2 => true
  | .s1, .s2 => true
  | _, _ => false

def op : OneWayAssoc → OneWayAssoc → OneWayAssoc
  | _, .s2 => .s2
  | _, _ => .s0

end OneWayAssoc

instance : SepStruct OneWayAssoc where
  disj x y := OneWayAssoc.disjB x y = true
  union := OneWayAssoc.op

def OneWayAssoc.step2 : Cmd OneWayAssoc
  | .s2, o => o = .ok .s2
  | _, _ => False
```

In words: `AssocGap` has `p ⊥ r` with `p ∘ r = m` and `m ⊥ s` with `m ∘ s = t`, and no other
pair is disjoint (so `UnionAssocRev` holds vacuously and `UnionAssoc` fails at `(p, r, s)`);
`OneWayAssoc` has `s0 ⊥ s0`, `s0 ⊥ s2`, `s1 ⊥ s2` (and no other pair), `x ∘ s2 = s2` and
`x ∘ y = s0` otherwise (so `UnionAssoc` holds and `UnionAssocRev` fails at `(s1, s0, s2)`).
Neither has symmetric disjointness. Union values on non-disjoint arguments are junk.

From `lean/Toy/Sep/Precision.lean`:

```lean
@[reducible] def projRightSepStruct : SepStruct Nat := ⟨fun _ _ => True, fun _ b => b⟩

@[reducible] def projLeftSepStruct : SepStruct Nat := ⟨fun _ _ => True, fun a _ => a⟩

@[reducible] def orDisjRightSepStruct : SepStruct Bool := ⟨fun _ y => y = true, fun x y => x || y⟩

@[reducible] def orDisjLeftSepStruct : SepStruct Bool := ⟨fun x _ => x = true, fun x y => x || y⟩

def oneCell : Assn (Heap Nat) := fun h => ∃ k v, h = Heap.pt k v

def someCellAllocated : Assn (Heap Nat) := fun h => ∃ k, h.val k ≠ none
```

From `lean/Toy/Sep/Algebras.lean`:

```lean
structure OrAlg where
  /-- The underlying bit. -/
  bit : Bool
  deriving DecidableEq

instance : SepStruct OrAlg where
  disj _ _ := True
  union x y := ⟨x.bit || y.bit⟩

def OrAlg.unit : OrAlg := ⟨false⟩

inductive Fork where
  | e | p | a | b | t
  deriving DecidableEq

namespace Fork

def disjB : Fork → Fork → Bool
  | .e, _ => true
  | _, .e => true
  | .p, .a => true
  | .a, .p => true
  | .p, .b => true
  | .b, .p => true
  | _, _ => false

def unionF : Fork → Fork → Fork
  | .e, x => x
  | x, .e => x
  | .p, .a => .t
  | .a, .p => .t
  | .p, .b => .t
  | .b, .p => .t
  | _, _ => .e

end Fork

instance : SepStruct Fork where
  disj x y := Fork.disjB x y = true
  union := Fork.unionF

def forkR : Assn Fork := fun x => x = .a ∨ x = .b
```

In words: in `OrAlg` every two states are disjoint and union is boolean `or` on the bit,
with unit `OrAlg.unit = ⟨false⟩`. In `Fork`, `e` is a two-sided unit disjoint from every
state, `p ⊥ a` and `p ⊥ b` (in both orders) with `p ∘ a = p ∘ b = t`, and no other pair
is disjoint (union is the junk value `e` there).

From `lean/Toy/Sep/Boundaries.lean`:

```lean
def skipOnEmp {V : Type} : Cmd (Heap V) := fun h o => h = Heap.emp ∧ o = .ok Heap.emp

@[reducible] def onePairSepStruct : SepStruct Nat := ⟨fun a b => a = 1 ∧ b = 1, fun a b => a + b⟩

def PreciseLeft {S : Type u} [SepStruct S] (R : Assn S) : Prop :=
  ∀ r₁ f₁ r₂ f₂ : S, disj r₁ f₁ → disj r₂ f₂ → union r₁ f₁ = union r₂ f₂ →
    R r₁ → R r₂ → r₁ = r₂

def ConjDistribLeft {S : Type u} [SepStruct S] (R : Assn S) : Prop :=
  ∀ (P Q : Assn S) (h : S), sep R P h → sep R Q h → sep R (conj P Q) h
```

From `lean/Toy/Sep/Examples.lean`:

```lean
def ptAny (k : Nat) : Assn (Heap Nat) := fun h => ∃ v, h = Heap.pt k v
```

(`ptAny k` is `k ↦ -`: cell `k` is the only allocated cell, with any value.)

From `lean/Toy/Sep/Supplement.lean`:

```lean
inductive SymmAssocGap where
  | p | r | s | m | t
  deriving DecidableEq

namespace SymmAssocGap

def disjB : SymmAssocGap → SymmAssocGap → Bool
  | .p, .r => true
  | .r, .p => true
  | .m, .s => true
  | .s, .m => true
  | _, _ => false

def unionG : SymmAssocGap → SymmAssocGap → SymmAssocGap
  | .p, .r => .m
  | .r, .p => .m
  | .m, .s => .t
  | .s, .m => .t
  | _, _ => .p

def faultAtT : Cmd SymmAssocGap := fun x o => x = .t ∧ o = .fault

end SymmAssocGap

instance : SepStruct SymmAssocGap where
  disj x y := SymmAssocGap.disjB x y = true
  union := SymmAssocGap.unionG

inductive CommOneWay where
  | s0 | s1 | s2
  deriving DecidableEq

namespace CommOneWay

def disjB : CommOneWay → CommOneWay → Bool
  | .s0, .s0 => true
  | .s0, .s2 => true
  | .s1, .s2 => true
  | _, _ => false

def op : CommOneWay → CommOneWay → CommOneWay
  | .s2, _ => .s2
  | _, .s2 => .s2
  | _, _ => .s0

def step2 : Cmd CommOneWay
  | .s2, o => o = .ok .s2
  | _, _ => False

end CommOneWay

instance : SepStruct CommOneWay where
  disj x y := CommOneWay.disjB x y = true
  union := CommOneWay.op
```

In words: `SymmAssocGap` is the symmetric, commutative version of `AssocGap` (`DisjSymm` and
`UnionComm` hold; `UnionAssoc` and `UnionAssocRev` both fail). `CommOneWay` has the
disjointness table of `OneWayAssoc` (not symmetric) with a commutative union in which `s2`
absorbs on either side (`UnionComm` and `UnionAssoc` hold; `DisjSymm` and `UnionAssocRev`
fail). These four small structures are finite carriers built only for the tightness
counterexamples of R6a.

`Toy/Sep/Examples.lean` proves intended positive and negative examples for each of these
definitions, and admitted and excluded transitions for every heap command. The examples and
helper lemmas cited in this report's text are quoted here (pretty-printed by Lean; namespace
`Toy.Sep` opened; `skip_local`, `diverge_local`, `assertAlloc_safetyMono` and `assertAlloc_frameProp`
printed as `name : type` with `set_option pp.analyze true`, because their default signatures leave
the state type of `skip`, `diverge` or `assertAlloc` undetermined; the entry preceded by a
`-- file:lines` citation is quoted verbatim from those source lines): `skip` and `diverge` are local
while `allocAt` is not; singletons are
precise; `assertAlloc k` is local (R3a non-claims); `0 ↦ -` is precise (R4e non-claims); the heap
model is right- and left-cancellative (R4d ledger scope); and a non-commutative structure has
`DisjSymm`, `UnionAssoc` and `UnionAssocRev` (R6a ledger).

```lean
Toy.Sep.skip_local.{u_1} : ∀ {S : Type u_1} [inst : SepStruct S], Local.{u_1} (S := S) skip

Toy.Sep.diverge_local.{u_1} : ∀ {S : Type u_1} [inst : SepStruct S], Local.{u_1} (S := S) diverge

Toy.Sep.allocAt_not_local : ¬Local (allocAt 0 1)

Toy.Sep.sing_precise.{u_1} {S : Type u_1} [SepStruct S] (x : S) : Precise (sing x)

Toy.Sep.assertAlloc_safetyMono : ∀ {V : Type} (k : Nat), SafetyMono (S := Heap V) (assertAlloc k)

Toy.Sep.assertAlloc_frameProp : ∀ {V : Type} (k : Nat), FrameProp (S := Heap V) (assertAlloc k)

Toy.Sep.ptAny_precise (k : Nat) : Precise (ptAny k)

Toy.Sep.heap_rightCancel (V : Type) : RightCancel (Heap V)

Toy.Sep.heap_leftCancel (V : Type) : LeftCancel (Heap V)

-- lean/Toy/Sep/Supplement.lean:68-72
-- source statement, verbatim; instance arguments shown explicitly
theorem projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm :
    @DisjSymm Nat projLeftSepStruct ∧
    @UnionAssoc Nat projLeftSepStruct ∧
    @UnionAssocRev Nat projLeftSepStruct ∧
    ¬ @UnionComm Nat projLeftSepStruct
```

The six lemmas cited in card fields (`assertAlloc_safetyMono`, `assertAlloc_frameProp`,
`ptAny_precise`, `heap_rightCancel`, `heap_leftCancel`,
`projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm`) are registered in the `lean_names`
field of their cards in `results.json`, so their statement and closure hashes are recorded in
`audit/statements.json` and listed under **Evidence**. The four definition examples
`skip_local`, `diverge_local`, `allocAt_not_local` and `sing_precise` are cited only in this
section; they are covered by the build and the axiom audit (`audit/axioms.json`) but carry no
recorded statement hash.

### R1: `R1-frame-rule-from-locality`

* **Kind / tier:** theorem, **T0**. Yang-O'Hearn 2002 Lemmas 1-2 and Theorem 1 (store-and-heap model); stated relationally for separation algebras in Calcagno-O'Hearn-Yang 2007 Section 3; mechanized without algebraic laws in HOL4 (ASL_IS_LOCAL_ACTION___HOARE_TRIPLE with LOCALITY_CHARACTERISATION_REL).
* **Plain claim:** In any separation structure (no algebraic laws assumed), if a command c is safety-monotone and has the frame property, then every fault-avoiding partial-correctness triple {P} c {Q} implies {P * R} c {Q * R} for every assertion R.
* **Design question:** Which exact properties of commands make the frame rule sound, and which plausible commands violate them?

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.frame_rule_of_safetyMono_of_frameProp.{u} {S : Type u} [SepStruct S] {c : Cmd S} (hsm : SafetyMono c)
  (hfp : FrameProp c) {P Q R : Assn S} (ht : Triple P c Q) : Triple (sep P R) c (sep Q R)
```

Unfolded: assume (SafetyMono) ∀ h h', h ⊥ h' → ¬ c h fault → ¬ c (h ∘ h') fault; (FrameProp) ∀ h h' h'', h ⊥ h' → ¬ c h fault → c (h ∘ h') (ok h'') → ∃ h₀, c h (ok h₀) ∧ h₀ ⊥ h' ∧ h'' = h₀ ∘ h'; and (Triple P c Q) ∀ h, P h → ¬ c h fault ∧ ∀ h', c h (ok h') → Q h'. Conclude: ∀ h, (∃ h₁ h₂, h₁ ⊥ h₂ ∧ h = h₁ ∘ h₂ ∧ P h₁ ∧ R h₂) → ¬ c h fault ∧ ∀ h', c h (ok h') → ∃ q r, q ⊥ r ∧ h' = q ∘ r ∧ Q q ∧ R r.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hsm : SafetyMono c` | Gives safety (no fault) from the framed precondition P * R. | tight: counterexample `Toy.Sep.allocAt_frameProp_and_framed_triple_fails` |
| `hfp : FrameProp c` | Gives the framed postcondition Q * R for every normal run from P * R. | tight: counterexample `Toy.Sep.isAllocTest_safetyMono_and_framed_triple_fails`, `Toy.Sep.allocLeast_safetyMono_and_framed_triple_fails` |
| `ht : Triple P c Q` | Premise of the frame rule. | tight: counterexample `Toy.Sep.skip_local_and_framed_triple_fails` |
| `(definition) Triple is fault-avoiding` | With non-fault-avoiding triples the frame rule fails even for a local command. | tight: counterexample `Toy.Sep.assertAlloc_local_and_framed_weakTriple_fails` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** assertAlloc 0 (fault unless cell 0 is allocated) is safety-monotone, has the frame property, and satisfies {0 |-> 1} assertAlloc 0 {0 |-> 1}. (Lean: `Toy.Sep.frame_rule_of_safetyMono_of_frameProp_nonvacuous`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf). Definition 1: a separation algebra is a cancellative partial commutative monoid. Definition 3: p is precise if every state has at most one substate in p. Section 2, Examples of Predicates: the two-cell disjunction l0 |-> rv0 or l1 |-> rv1 is not precise. Lemma 4: every singleton is precise; p is precise iff for all nonempty X, (meet X) * p = meet{x * p | x in X}; the remark after it says injectivity of sigma . (-) is equivalent to that distribution for singleton frames {sigma}. Section 3: a relation satisfies Safety Monotonicity and the Frame Property 'iff the frame rule is sound for it' (stated without proof).
  * HOL4 theory examples/separationLogic/src/separationLogicScript.sml in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e; the framework is described in Tuerk, T., 'A separation logic framework for HOL', University of Cambridge Computer Laboratory Technical Report UCAM-CL-TR-799, June 2011, doi:10.48456/tr-799 (based on the author's PhD dissertation). ASL_IS_LOCAL_ACTION f op (lines 2457-2462): for all separate s1, s2, op(s1 . s2) is below (op s1) * {s2} in the order with fault on top, i.e. locality stated at singleton frames against the outcome set (strongest postcondition) op s1. LOCALITY_CHARACTERISATION_REL (lines 2490-2495): for every f and relation R, ASL_IS_LOCAL_ACTION f (TRANS_REL_TO_TRANS_FUNC R) iff TRANS_REL_SAFETY_MONOTONICITY f R and TRANS_REL_FRAME_PROPERTY f R. ASL_IS_LOCAL_ACTION___HOARE_TRIPLE (lines 2699-2703): for every f and action a, a is local iff for all P, Q, HOARE_TRIPLE P a Q implies HOARE_TRIPLE (P * x) a (Q * x) for every frame set x, where HOARE_TRIPLE is fault-avoiding with no termination requirement; the backward direction is proved by instantiating a singleton precondition, the outcome set and a singleton frame. Neither theorem has an IS_SEPARATION_COMBINATOR f premise: f is an arbitrary partial binary operation, with no algebraic laws.
  * Reynolds, J. C., 'Separation Logic: A Logic for Shared Mutable Data Structures', LICS 2002, pp. 55-74, doi:10.1109/LICS.2002.1029817. End of Section 2: the 'restricting the heap' formulation of locality. Section 3 defines intuitionistic assertions and states the distributive law for 'domain-exact' q; 'precise' is not used as a technical term. Section 4: frame rule soundness, citing Yang and O'Hearn.
  * Ishtiaq, S. S. & O'Hearn, P. W., 'BI as an Assertion Language for Mutable Data Structures', POPL 2001, pp. 14-26, doi:10.1145/360204.375719. Section 8 introduces the frame rule ('Frame Axiom Introduction'); the soundness argument is only sketched.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

A program logic whose state model is a separation structure, whose triples are fault-avoiding partial-correctness triples over arbitrary predicates, and whose primitive commands are safety-monotone and have the frame property, may adopt the frame rule for those primitives without any algebraic law on the state model. The reasoning is that the Lean statement quantifies over every SepStruct, every relational command and every predicate; a concrete logic is an instance once its notions are shown to coincide with these definitions. Composite commands are not covered (closure under sequencing etc. is not examined).

### R2a: `R2a-locality-from-frame-rule-at-singletons`

* **Kind / tier:** theorem, **T0**. Mechanized without algebraic laws in HOL4: ASL_IS_LOCAL_ACTION is locality stated at singleton frames against the strongest postcondition, and LOCALITY_CHARACTERISATION_REL proves it equivalent to safety monotonicity plus the frame property for an arbitrary partial operation. Stated without proof in Calcagno-O'Hearn-Yang 2007 Section 3.
* **Plain claim:** In any separation structure (no algebraic laws assumed), if for all states h, h' the frame rule holds for c at the single instance with precondition {h}, postcondition 'some final state of c from h', and frame {h'}, then c is safety-monotone and has the frame property.
* **Design question:** How much of the frame rule must a logic validate before it is forced to admit only local commands? Just the singleton instances.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.safetyMono_and_frameProp_of_frameRuleAtSingletons.{u} {S : Type u} [SepStruct S] {c : Cmd S}
  (H : FrameRuleAtSingletons c) : SafetyMono c ∧ FrameProp c
```

Unfolded: the hypothesis FrameRuleAtSingletons c is ∀ h h', Triple {h} c (post c h) → Triple ({h} * {h'}) c (post c h * {h'}), where post c h := fun h' => c h (ok h') is the strongest postcondition and {x} := fun y => y = x. The conclusion is SafetyMono c ∧ FrameProp c as unfolded under R1.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `H : FrameRuleAtSingletons c` | The only use of the frame rule; with it dropped the conclusion fails for a non-local command. | tight: counterexample `Toy.Sep.allocLeast_not_safetyMono_and_frameProp` |
| `(setting) frames range over at least the singleton assertions` | If the only admitted frame is emp, every command satisfies the restricted frame rule, so no locality follows. | tight: counterexample `Toy.Sep.allocLeast_frame_rule_for_emp_frame_and_not_local` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** assertAlloc 0 satisfies the frame rule at all singleton instances (proved directly). (Lean: `Toy.Sep.frameRuleAtSingletons_assertAlloc`).
* **Prior art:**
  * HOL4 theory examples/separationLogic/src/separationLogicScript.sml in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e; the framework is described in Tuerk, T., 'A separation logic framework for HOL', University of Cambridge Computer Laboratory Technical Report UCAM-CL-TR-799, June 2011, doi:10.48456/tr-799 (based on the author's PhD dissertation). ASL_IS_LOCAL_ACTION f op (lines 2457-2462): for all separate s1, s2, op(s1 . s2) is below (op s1) * {s2} in the order with fault on top, i.e. locality stated at singleton frames against the outcome set (strongest postcondition) op s1. LOCALITY_CHARACTERISATION_REL (lines 2490-2495): for every f and relation R, ASL_IS_LOCAL_ACTION f (TRANS_REL_TO_TRANS_FUNC R) iff TRANS_REL_SAFETY_MONOTONICITY f R and TRANS_REL_FRAME_PROPERTY f R. ASL_IS_LOCAL_ACTION___HOARE_TRIPLE (lines 2699-2703): for every f and action a, a is local iff for all P, Q, HOARE_TRIPLE P a Q implies HOARE_TRIPLE (P * x) a (Q * x) for every frame set x, where HOARE_TRIPLE is fault-avoiding with no termination requirement; the backward direction is proved by instantiating a singleton precondition, the outcome set and a singleton frame. Neither theorem has an IS_SEPARATION_COMBINATOR f premise: f is an arbitrary partial binary operation, with no algebraic laws.
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf). Definition 1: a separation algebra is a cancellative partial commutative monoid. Definition 3: p is precise if every state has at most one substate in p. Section 2, Examples of Predicates: the two-cell disjunction l0 |-> rv0 or l1 |-> rv1 is not precise. Lemma 4: every singleton is precise; p is precise iff for all nonempty X, (meet X) * p = meet{x * p | x in X}; the remark after it says injectivity of sigma . (-) is equivalent to that distribution for singleton frames {sigma}. Section 3: a relation satisfies Safety Monotonicity and the Frame Property 'iff the frame rule is sound for it' (stated without proof).
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).
  * Reynolds, J. C., 'Separation Logic: A Logic for Shared Mutable Data Structures', LICS 2002, pp. 55-74, doi:10.1109/LICS.2002.1029817. End of Section 2: the 'restricting the heap' formulation of locality. Section 3 defines intuitionistic assertions and states the distributive law for 'domain-exact' q; 'precise' is not used as a technical term. Section 4: frame rule soundness, citing Yang and O'Hearn.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

In a logic that can state singleton preconditions, strongest postconditions and singleton frames, any primitive for which the frame rule is sound is necessarily safety-monotone with the frame property; a logic whose assertions cannot express singletons (e.g. upward-closed assertions) does not get this converse from this theorem.

### R2b: `R2b-frame-rule-iff-locality`

* **Kind / tier:** characterization, **T0**. Stated without proof in Calcagno-O'Hearn-Yang 2007 Section 3. Mechanized without algebraic laws in HOL4 by composing LOCALITY_CHARACTERISATION_REL with ASL_IS_LOCAL_ACTION___HOARE_TRIPLE.
* **Plain claim:** In any separation structure (no algebraic laws assumed), the frame rule is sound for a command c (for all assertions P, Q, R, {P} c {Q} implies {P * R} c {Q * R}) if and only if c is safety-monotone and has the frame property. It is the conjunction of R1 and R2a.
* **Design question:** Is 'local' the right side condition for the frame rule? Yes: it is exactly equivalent.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp.{u} {S : Type u} [SepStruct S] (c : Cmd S) :
  FrameRuleSound c ↔ SafetyMono c ∧ FrameProp c
```

Unfolded: FrameRuleSound c := ∀ P Q R : S → Prop, Triple P c Q → Triple (P * R) c (Q * R), with P * R := fun h => ∃ h₁ h₂, h₁ ⊥ h₂ ∧ h = h₁ ∘ h₂ ∧ P h₁ ∧ R h₂.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `(setting) assertions range over all predicates` | The forward direction instantiates singleton preconditions, strongest postconditions and singleton frames. | tight: counterexample `Toy.Sep.allocLeast_frame_rule_for_emp_frame_and_not_local` |
| `(setting) triples are fault-avoiding` | The backward direction fails for non-fault-avoiding triples. | tight: counterexample `Toy.Sep.assertAlloc_local_and_framed_weakTriple_fails` |

* **Depth:** `shallow`. Given R1 and R2a the proof is one line; the label reflects the content of the equivalence, which needs both of those unfoldings, not only the definitions involved.
* **Non-vacuity witness:** Both sides hold for skip; both sides fail for allocAt 0 1. (Lean: `Toy.Sep.frameRuleSound_iff_nonvacuous`).
* **Prior art:**
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf). Definition 1: a separation algebra is a cancellative partial commutative monoid. Definition 3: p is precise if every state has at most one substate in p. Section 2, Examples of Predicates: the two-cell disjunction l0 |-> rv0 or l1 |-> rv1 is not precise. Lemma 4: every singleton is precise; p is precise iff for all nonempty X, (meet X) * p = meet{x * p | x in X}; the remark after it says injectivity of sigma . (-) is equivalent to that distribution for singleton frames {sigma}. Section 3: a relation satisfies Safety Monotonicity and the Frame Property 'iff the frame rule is sound for it' (stated without proof).
  * HOL4 theory examples/separationLogic/src/separationLogicScript.sml in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e; the framework is described in Tuerk, T., 'A separation logic framework for HOL', University of Cambridge Computer Laboratory Technical Report UCAM-CL-TR-799, June 2011, doi:10.48456/tr-799 (based on the author's PhD dissertation). ASL_IS_LOCAL_ACTION f op (lines 2457-2462): for all separate s1, s2, op(s1 . s2) is below (op s1) * {s2} in the order with fault on top, i.e. locality stated at singleton frames against the outcome set (strongest postcondition) op s1. LOCALITY_CHARACTERISATION_REL (lines 2490-2495): for every f and relation R, ASL_IS_LOCAL_ACTION f (TRANS_REL_TO_TRANS_FUNC R) iff TRANS_REL_SAFETY_MONOTONICITY f R and TRANS_REL_FRAME_PROPERTY f R. ASL_IS_LOCAL_ACTION___HOARE_TRIPLE (lines 2699-2703): for every f and action a, a is local iff for all P, Q, HOARE_TRIPLE P a Q implies HOARE_TRIPLE (P * x) a (Q * x) for every frame set x, where HOARE_TRIPLE is fault-avoiding with no termination requirement; the backward direction is proved by instantiating a singleton precondition, the outcome set and a singleton frame. Neither theorem has an IS_SEPARATION_COMBINATOR f premise: f is an arbitrary partial binary operation, with no algebraic laws.
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

For the same class of logics as R1/R2a, 'the frame rule is sound for c' and 'c is local' are interchangeable obligations.

### R2c: `R2c-locality-from-frame-rule-for-precise-frames`

* **Kind / tier:** theorem, **T1**. Follows from R2a because singleton assertions are precise (Calcagno-O'Hearn-Yang 2007 Lemma 4(1), used there in the proof of Lemma 9); this consequence is not stated in the cited sources.
* **Plain claim:** In any separation structure (no algebraic laws assumed), if the frame rule holds for c for all P, Q and every precise frame R (precise in the right-handed sense of Toy.Sep.Precise), then c is safety-monotone and has the frame property.
* **Design question:** If a logic restricts its frame rule to precise frames (e.g. to keep the conjunction rule), does it gain room for non-local commands? No.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.safetyMono_and_frameProp_of_frameRuleForPreciseFrames.{u} {S : Type u} [SepStruct S] {c : Cmd S}
  (H : FrameRuleForPreciseFrames c) : SafetyMono c ∧ FrameProp c
```

Unfolded: FrameRuleForPreciseFrames c := ∀ P Q R, Precise R → Triple P c Q → Triple (P * R) c (Q * R), where Precise R := ∀ f₁ r₁ f₂ r₂, f₁ ⊥ r₁ → f₂ ⊥ r₂ → f₁ ∘ r₁ = f₂ ∘ r₂ → R r₁ → R r₂ → r₁ = r₂.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `H : FrameRuleForPreciseFrames c` | The only use of the frame rule. | tight: counterexample `Toy.Sep.allocLeast_not_safetyMono_and_frameProp` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** skip satisfies the frame rule for all precise frames. (Lean: `Toy.Sep.frameRuleForPreciseFrames_nonvacuous`).
* **Prior art:**
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf). Definition 1: a separation algebra is a cancellative partial commutative monoid. Definition 3: p is precise if every state has at most one substate in p. Section 2, Examples of Predicates: the two-cell disjunction l0 |-> rv0 or l1 |-> rv1 is not precise. Lemma 4: every singleton is precise; p is precise iff for all nonempty X, (meet X) * p = meet{x * p | x in X}; the remark after it says injectivity of sigma . (-) is equivalent to that distribution for singleton frames {sigma}. Section 3: a relation satisfies Safety Monotonicity and the Frame Property 'iff the frame rule is sound for it' (stated without proof).
  * O'Hearn, P. W., Yang, H. & Reynolds, J. C., 'Separation and Information Hiding', POPL 2004, pp. 268-280, doi:10.1145/964001.964024: Section 9, Lemma 3: p is precise iff p * - distributes over conjunction, p * (q and r) = (p * q) and (p * r), in the store-and-heap model with p on the left; Theorem 5: the hypothetical frame rule is sound for fixed preconditions (resp. a fixed resource invariant) iff they are precise; Section 10.3, Theorem 11: soundness also holds for 'supported' preconditions or invariants with intuitionistic (closed under heap extension) postconditions. Journal version: ACM TOPLAS 31(3), Article 11, pp. 11:1-11:50, 2009, doi:10.1145/1498926.1498929; in the authors' 2008 preprint of it, Lemma 6 is the Distribution Lemma and Section 9 notes that (q * r) and (q' * r) does not imply (q and q') * r in general, with q = emp, q' = x |-> - and r = true.
  * Gotsman, A., Berdine, J. & Cook, B., 'Precision and the Conjunction Rule in Concurrent Separation Logic', MFPS XXVII, ENTCS 276:171-190, 2011, doi:10.1016/j.entcs.2011.09.021. Definition 2.1: a separation algebra is a partial commutative monoid with unit, omitting (as the paper notes) the cancellativity required by Calcagno-O'Hearn-Yang 2007. Section 2.2: the 'command' that disposes cell 10 if it is allocated and is a no-op otherwise is not local; 'the requirement of locality rules out commands that can check if a cell is allocated in the heap other than by trying to access it and faulting if it is not allocated'. Theorem 4.1: concurrent separation logic is sound if resource invariants are precise and * is cancellative, or if the conjunction rule is not used.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Restricting a logic's frame rule to precise frames does not make any additional non-local primitive sound, provided singleton assertions are available as frames (every singleton is precise).

### R3a: `R3a-allocation-test-violates-frame-property`

* **Kind / tier:** counterexample, **T1**. Gotsman-Berdine-Cook 2011 Section 2.2 give a similar allocation-checking non-local example; Yang-O'Hearn 2002 Section 4.1 discuss fault trapping. The concrete statement and triple are made precise here.
* **Plain claim:** In the heap model, the command isAllocTest k r that records in cell r whether a different cell k is allocated is safety-monotone (for all k, r) but violates the frame property when k != r: {0 |-> 0} isAllocTest 1 0 {0 |-> 0} holds, but framing it with 1 |-> 7 fails because cell 0 becomes 1.
* **Design question:** Which plausible commands violate locality? Commands that observe the absence of memory.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.isAllocTest_not_frameProp {k r : Nat} (hkr : k ≠ r) : ¬FrameProp (isAllocTest k r)

Toy.Sep.isAllocTest_safetyMono (k r : Nat) : SafetyMono (isAllocTest k r)

Toy.Sep.isAllocTest_safetyMono_and_framed_triple_fails :
  SafetyMono (isAllocTest 1 0) ∧
    Triple (sing (Heap.pt 0 0)) (isAllocTest 1 0) (sing (Heap.pt 0 0)) ∧
      ¬Triple (sep (sing (Heap.pt 0 0)) (sing (Heap.pt 1 7))) (isAllocTest 1 0)
          (sep (sing (Heap.pt 0 0)) (sing (Heap.pt 1 7)))
```

Unfolded: isAllocTest k r h o := (h r = none ∧ o = fault) ∨ (h r ≠ none ∧ h k ≠ none ∧ o = ok h[r ↦ 1]) ∨ (h r ≠ none ∧ h k = none ∧ o = ok h[r ↦ 0]).

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hkr : k != r` | If the tested cell is the result cell, the answer is always 'allocated' and the command has the frame property. | tight: counterexample `Toy.Sep.isAllocTest_self_frameProp` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** Concrete instance k = 1, r = 0. (Lean: `Toy.Sep.isAllocTest_safetyMono_and_framed_triple_fails`).
* **Supporting lemmas cited in the non-claims** (`lean_names`; quoted under Key definitions): `Toy.Sep.assertAlloc_safetyMono`, `Toy.Sep.assertAlloc_frameProp`.
* **Prior art:**
  * Gotsman, A., Berdine, J. & Cook, B., 'Precision and the Conjunction Rule in Concurrent Separation Logic', MFPS XXVII, ENTCS 276:171-190, 2011, doi:10.1016/j.entcs.2011.09.021. Definition 2.1: a separation algebra is a partial commutative monoid with unit, omitting (as the paper notes) the cancellativity required by Calcagno-O'Hearn-Yang 2007. Section 2.2: the 'command' that disposes cell 10 if it is allocated and is a no-op otherwise is not local; 'the requirement of locality rules out commands that can check if a cell is allocated in the heap other than by trying to access it and faulting if it is not allocated'. Theorem 4.1: concurrent separation logic is sound if resource invariants are precise and * is cancellative, or if the conjunction rule is not used.
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

A primitive that observes whether a location is allocated, without faulting on it, cannot be given a sound frame rule in a logic of the R1/R2 kind; this models allocation queries, 'is-valid-pointer' tests and similar footprint-dependent probes.

### R3b: `R3b-fixed-address-allocation-violates-safety-monotonicity`

* **Kind / tier:** counterexample, **T1**. Yang-O'Hearn 2002 Section 4.1 give the analogous capacity-1 Petri-net transition that is disabled when its output place is already marked, and Section 5.1 another safety-monotonicity violator; the heap instance and its framed triple are made precise here.
* **Plain claim:** In the heap model, allocating at a fixed address k and faulting if k is already allocated (allocAt k v) has the frame property (for all k, v) but violates safety monotonicity: {emp} allocAt 0 1 {0 |-> 1} holds, but framing it with 0 |-> 2 fails because the command faults. The variant allocAtBlock k v that blocks (has no outcome) instead of faulting when k is taken is safety-monotone and has the frame property.
* **Design question:** Which plausible commands violate locality? Commands that fault on the presence of memory.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.allocAt_not_safetyMono {V : Type} (k : Nat) (v : V) : ¬SafetyMono (allocAt k v)

Toy.Sep.allocAt_frameProp {V : Type} (k : Nat) (v : V) : FrameProp (allocAt k v)

Toy.Sep.allocAt_frameProp_and_framed_triple_fails :
  FrameProp (allocAt 0 1) ∧
    Triple (sing Heap.emp) (allocAt 0 1) (sing (Heap.pt 0 1)) ∧
      ¬Triple (sep (sing Heap.emp) (sing (Heap.pt 0 2))) (allocAt 0 1) (sep (sing (Heap.pt 0 1)) (sing (Heap.pt 0 2)))

Toy.Sep.allocAtBlock_safetyMono_and_frameProp {V : Type} (k : Nat) (v : V) :
  SafetyMono (allocAtBlock k v) ∧ FrameProp (allocAtBlock k v)

Toy.Sep.allocAtBlock_local_and_blocks_when_taken : Local (allocAtBlock 0 1) ∧ ¬∃ o, allocAtBlock 0 1 (Heap.pt 0 2) o
```

Unfolded: allocAt k v h o := (h k ≠ none ∧ o = fault) ∨ (h k = none ∧ o = ok h[k ↦ v]); allocAtBlock k v h o := h k = none ∧ o = ok h[k ↦ v] (no outcome when k is taken).

**Hypothesis ledger:**

No hypotheses (empty ledger).

Ledger scope: No hypotheses: allocAt_not_safetyMono, allocAt_frameProp and allocAtBlock_safetyMono_and_frameProp hold for every value type V, address k and value v, without conditions; allocAt_frameProp_and_framed_triple_fails and allocAtBlock_local_and_blocks_when_taken are closed instances (k = 0, v = 1 in Heap Nat).

* **Depth:** `shallow`.
* **Non-vacuity witness:** Concrete instance k = 0, v = 1, frame 0 |-> 2. (Lean: `Toy.Sep.allocAt_frameProp_and_framed_triple_fails`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).
  * Costanzo, D. & Shao, Z., 'A Case for Behavior-Preserving Actions in Separation Logic', APLAS 2012, LNCS 7705, pp. 332-349, doi:10.1007/978-3-642-35182-2_24 (author PDF https://flint.cs.yale.edu/flint/publications/bpsl.pdf). Section 5.1 (Footprints and Smallest Safe States): under standard locality a specification of a command on its smallest safe states need not be complete (example x := cons(0); free(x)). Section 5.3: the frame rule of relational separation logic is sound for deterministic but not for nondeterministic programs (citing Yang, TCS 2007). Section 5.4 (Finite Memory): a state-growing command that faults when memory is full is safe on the empty state but unsafe on the full state, so it violates Safety Monotonicity; diverging instead requires allowing divergence on any state to keep Termination Monotonicity.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

A primitive that allocates at a caller-chosen fixed address and reports an error when the address is in use is not safety-monotone; blocking (or treating the in-use case as no outcome) restores locality in the partial-correctness reading.

### R3c: `R3c-deterministic-allocation-violates-frame-property`

* **Kind / tier:** counterexample, **T1**. Yang-O'Hearn 2002 Section 4.1 make the point informally for least-free-address allocation with address arithmetic.
* **Plain claim:** In the heap model, allocating at the least free address (allocLeast v) is safety-monotone (for all v) but violates the frame property: {emp} allocLeast 1 {0 |-> 1} holds, but framing it with 0 |-> 2 fails because the new cell lands at address 1. It is a special case of R3d.
* **Design question:** Must allocation be nondeterministic? See R3d.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.allocLeast_not_frameProp {V : Type} (v : V) : ¬FrameProp (allocLeast v)

Toy.Sep.allocLeast_safetyMono {V : Type} (v : V) : SafetyMono (allocLeast v)

Toy.Sep.allocLeast_safetyMono_and_framed_triple_fails :
  SafetyMono (allocLeast 1) ∧
    Triple (sing Heap.emp) (allocLeast 1) (sing (Heap.pt 0 1)) ∧
      ¬Triple (sep (sing Heap.emp) (sing (Heap.pt 0 2))) (allocLeast 1) (sep (sing (Heap.pt 0 1)) (sing (Heap.pt 0 2)))
```

Unfolded: allocLeast v h o := ∃ k, h k = none ∧ (∀ j < k, h j ≠ none) ∧ o = ok h[k ↦ v].

**Hypothesis ledger:**

No hypotheses (empty ledger).

Ledger scope: No hypotheses: allocLeast_not_frameProp and allocLeast_safetyMono hold for every value type V and value v, without conditions; allocLeast_safetyMono_and_framed_triple_fails is a closed instance (v = 1 in Heap Nat).

* **Depth:** `shallow`.
* **Non-vacuity witness:** Concrete instance v = 1, frame 0 |-> 2. (Lean: `Toy.Sep.allocLeast_safetyMono_and_framed_triple_fails`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Deterministic least-free allocation, as in simple bump or first-fit allocators whose result is a function of the current heap, cannot be specified with an address-revealing postcondition in a logic with a frame rule.

### R3d: `R3d-predictable-allocation-violates-frame-property`

* **Kind / tier:** impossibility, **T1**. Makes precise and generalizes the informal remark of Yang-O'Hearn 2002 Section 4.1 (least-free allocation breaks the Frame Rule) to every command whose allocated address is predictable from some base heap; not claimed novel.
* **Plain claim:** In the heap model, let c be a command, hb a heap, a an address and w a value. If c is safe at hb, a is free in hb, every normal outcome of c from hb has a allocated (AlwaysAllocatesAt c hb a), and c has at least one normal outcome from hb extended by the cell a |-> w (RunsWhenOccupied c hb a w), then c violates the frame property. Corollaries: for every address-choice function f and value v (so the value type is inhabited) the total deterministic single-cell writer h |-> h[f h |-> v] (detAlloc f v) violates it; and deterministic pointer-recording allocation [r] := det_cons(v) (detAllocInto f r v) violates it whenever f h is fresh in h for every h in which r is allocated.
* **Design question:** How must allocation be specified for a frame-rule logic to be sound? Not by any policy whose address is predictable from some base heap and that still runs when a frame occupies that address; nondeterministic choice works (or, not examined here, a renaming-invariant logic).

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied {V : Type} {c : Cmd (Heap V)} {hb : Heap V} {a : Nat}
  {w : V} (hs : Safe c hb) (hfree : hb.val a = none) (hpred : AlwaysAllocatesAt c hb a)
  (hrun : RunsWhenOccupied c hb a w) : ¬FrameProp c

Toy.Sep.detAlloc_not_frameProp {V : Type} (f : Heap V → Nat) (v : V) : ¬FrameProp (detAlloc f v)

Toy.Sep.detAllocInto_not_frameProp_of_fresh {f : Heap Nat → Nat} {r : Nat} (v : Nat)
  (hfresh : ∀ (h : Heap Nat), h.val r ≠ none → h.val (f h) = none) : ¬FrameProp (detAllocInto f r v)
```

Unfolded: AlwaysAllocatesAt c hb a := ∀ h₀, c hb (ok h₀) → h₀ a ≠ none; RunsWhenOccupied c hb a w := ∃ h'', c (hb ∘ (a ↦ w)) (ok h''); detAlloc f v h o := o = ok h[f h ↦ v]; detAllocInto f r v h o := (h r = none ∧ o = fault) ∨ (h r ≠ none ∧ o = ok h[f h ↦ v][r ↦ f h]). The conclusion ¬ FrameProp c negates the FrameProp formula unfolded under R1.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hs : Safe c hb` | The frame property only constrains runs from states that are safe at the smaller heap. | tight: counterexample `Toy.Sep.faultOrSet0_not_safe_and_frameProp` |
| `hfree : hb.val a = none` | Needed for hb and the frame a |-> w to be disjoint. | tight: counterexample `Toy.Sep.skip_occupied_base_and_frameProp` |
| `hpred : AlwaysAllocatesAt c hb a` | Predictability: every run from hb uses address a. Nondeterministic choice among fresh addresses restores the frame property. | tight: counterexample `Toy.Sep.alloc_not_alwaysAllocatesAt_and_frameProp` |
| `hrun : RunsWhenOccupied c hb a w` | The command still terminates normally when a frame occupies a. A deterministic allocator that blocks on every non-empty heap has the frame property. | tight: counterexample `Toy.Sep.detAllocOnEmp_not_runsWhenOccupied_and_frameProp` |
| `hfresh (detAllocInto_not_frameProp_of_fresh) : f h fresh whenever r is allocated in h` | With the non-fresh choice f _ = r, pointer-recording allocation degenerates to the mutation [r] := r, which is local. | tight: counterexample `Toy.Sep.detAllocInto_self_frameProp` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** All four hypotheses hold for detAlloc (fun _ => 0) 1 with base emp, address 0, frame value 1. A genuinely fresh deterministic allocator also meets them: leastFree h, the least unallocated address of h (defined by well-founded recursion on the finiteness of heaps, without Classical.choice), satisfies hfresh for every r, and detAlloc leastFree 1 satisfies all four hypotheses with base emp, address 0, frame value 1 (Toy.Sep.detAllocInto_fresh_nonvacuous). (Lean: `Toy.Sep.not_frameProp_of_alwaysAllocatesAt_nonvacuous`, `Toy.Sep.detAllocInto_fresh_nonvacuous`).
* **Positive controls** (nearby settings where the conclusion fails): `Toy.Sep.alloc_not_alwaysAllocatesAt_and_frameProp`, `Toy.Sep.detAllocOnEmp_not_runsWhenOccupied_and_frameProp`, `Toy.Sep.alloc_frameProp`, `Toy.Sep.detAllocOnEmp_frameProp`. Nondeterministic `alloc 1` from `emp` meets every hypothesis except `AlwaysAllocatesAt` and has the frame property; the partial deterministic allocator `detAllocOnEmp 1` (runs only from `emp`) meets every hypothesis except `RunsWhenOccupied` and has the frame property. Each is a nearby predictable- or deterministic-allocation setting in which the conclusion `¬ FrameProp c` fails.
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).
  * Costanzo, D. & Shao, Z., 'A Case for Behavior-Preserving Actions in Separation Logic', APLAS 2012, LNCS 7705, pp. 332-349, doi:10.1007/978-3-642-35182-2_24 (author PDF https://flint.cs.yale.edu/flint/publications/bpsl.pdf). Section 5.1 (Footprints and Smallest Safe States): under standard locality a specification of a command on its smallest safe states need not be complete (example x := cons(0); free(x)). Section 5.3: the frame rule of relational separation logic is sound for deterministic but not for nondeterministic programs (citing Yang, TCS 2007). Section 5.4 (Finite Memory): a state-growing command that faults when memory is full is safe on the empty state but unsafe on the full state, so it violates Safety Monotonicity; diverging instead requires allowing divergence on any state to keep Termination Monotonicity.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Any allocator whose chosen address is predictable from some base heap and that still succeeds when a frame occupies that address breaks the frame property; this covers deterministic allocators whose capacity is at least two cells. Real logics avoid this by nondeterministic (or renaming-invariant) allocation specifications, by blocking, or by hiding the address.

### R3e: `R3e-frame-rule-needs-fault-avoidance`

* **Kind / tier:** counterexample, **T1**. Folklore; fault avoidance is built into all cited frame-rule soundness proofs.
* **Plain claim:** For non-fault-avoiding partial-correctness triples the frame rule fails even for a local command: {emp} assertAlloc 0 {false} holds vacuously (every run faults), but adding the frame 0 |-> 1 produces a normal run.
* **Design question:** What must triples mean for the frame rule to be sound? They must exclude faults.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened; `assertAlloc_local_and_framed_weakTriple_fails` printed as `name : type` with `set_option pp.analyze true`):

```lean
Toy.Sep.assertAlloc_local_and_framed_weakTriple_fails : SafetyMono (S := Heap Nat) (assertAlloc 0) ∧
  FrameProp (S := Heap Nat) (assertAlloc 0) ∧
    (WeakTriple (S := Heap Nat) (sing Heap.emp) (assertAlloc 0) fun x => False) ∧
      ¬WeakTriple (sep (sing Heap.emp) (sing (Heap.pt 0 1))) (assertAlloc 0) (sep (fun x => False) (sing (Heap.pt 0 1)))
```

Unfolded: WeakTriple P c Q := ∀ h, P h → ∀ h', c h (ok h') → Q h' (faults allowed); assertAlloc k h o := (h k = none ∧ o = fault) ∨ (h k ≠ none ∧ o = ok h).

**Hypothesis ledger:**

No hypotheses (empty ledger).

Ledger scope: No hypotheses: assertAlloc_local_and_framed_weakTriple_fails is a closed statement about the specific command assertAlloc 0 in Heap Nat.

* **Depth:** `shallow`.
* **Non-vacuity witness:** Concrete instance with assertAlloc 0 and frame 0 |-> 1. (Lean: `Toy.Sep.assertAlloc_local_and_framed_weakTriple_fails`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).
  * Reynolds, J. C., 'Separation Logic: A Logic for Shared Mutable Data Structures', LICS 2002, pp. 55-74, doi:10.1109/LICS.2002.1029817. End of Section 2: the 'restricting the heap' formulation of locality. Section 3 defines intuitionistic assertions and states the distributive law for 'domain-exact' q; 'precise' is not used as a technical term. Section 4: frame rule soundness, citing Yang and O'Hearn.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

A logic that wants a frame rule must use fault-avoiding (safety-guaranteeing) triples; with triples that permit faults, framing can create normal runs from a faulting command.

### R4a: `R4a-distribution-iff-unique-frame`

* **Kind / tier:** characterization, **T2**. A law-free version of the precision/distribution correspondence, related to the remark after Lemma 4 of Calcagno-O'Hearn-Yang 2007 (in a commutative cancellative setting, injectivity of sigma . (-) is equivalent to distribution for the singleton frame {sigma}). Not claimed novel.
* **Plain claim:** In any separation structure (no algebraic laws assumed), (P * R) and (Q * R) |- (P and Q) * R holds for all P, Q exactly when any two decompositions of a state whose right parts satisfy R have the same left part ('unique frames', which is not precision).
* **Design question:** Which algebraic properties of assertions (precision) and of the state model (cancellativity) are needed for the law (P * R) and (Q * R) |- (P and Q) * R, which is used when a frame or invariant R must be pushed inside a conjunction (hypothetical frame rules, resource invariants with the conjunction rule)?

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.conjDistrib_iff_uniqueFrame.{u} {S : Type u} [SepStruct S] (R : Assn S) : ConjDistrib R ↔ UniqueFrame R
```

Unfolded: ConjDistrib R := ∀ P Q h, (P * R) h → (Q * R) h → ((fun x => P x ∧ Q x) * R) h; UniqueFrame R := ∀ f₁ r₁ f₂ r₂, f₁ ⊥ r₁ → f₂ ⊥ r₂ → f₁ ∘ r₁ = f₂ ∘ r₂ → R r₁ → R r₂ → f₁ = f₂ (same left parts, whereas Precise demands the same right parts).

**Hypothesis ledger:**

No hypotheses (empty ledger).

Ledger scope: conjDistrib_iff_uniqueFrame has no hypotheses: it holds for every type S with any SepStruct S (no algebraic law is assumed: no symmetry of disjointness, commutativity, associativity, unit or cancellativity) and every assertion R : Assn S. It is a universally quantified characterization, not a statement about a fixed instance. ConjDistrib R itself quantifies over all predicates P, Q : Assn S (Assn S is S -> Prop: all predicates on states, not only upward-closed ones), and UniqueFrame R over all pairs of decompositions.

* **Depth:** `shallow`.
* **Non-vacuity witness:** Both sides hold for forkR = {a, b} in Fork; both fail for oneCell in the heap model. (Lean: `Toy.Sep.conjDistrib_iff_uniqueFrame_nonvacuous`).
* **Prior art:**
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf). Definition 1: a separation algebra is a cancellative partial commutative monoid. Definition 3: p is precise if every state has at most one substate in p. Section 2, Examples of Predicates: the two-cell disjunction l0 |-> rv0 or l1 |-> rv1 is not precise. Lemma 4: every singleton is precise; p is precise iff for all nonempty X, (meet X) * p = meet{x * p | x in X}; the remark after it says injectivity of sigma . (-) is equivalent to that distribution for singleton frames {sigma}. Section 3: a relation satisfies Safety Monotonicity and the Frame Property 'iff the frame rule is sound for it' (stated without proof).
  * O'Hearn, P. W., Yang, H. & Reynolds, J. C., 'Separation and Information Hiding', POPL 2004, pp. 268-280, doi:10.1145/964001.964024: Section 9, Lemma 3: p is precise iff p * - distributes over conjunction, p * (q and r) = (p * q) and (p * r), in the store-and-heap model with p on the left; Theorem 5: the hypothetical frame rule is sound for fixed preconditions (resp. a fixed resource invariant) iff they are precise; Section 10.3, Theorem 11: soundness also holds for 'supported' preconditions or invariants with intuitionistic (closed under heap extension) postconditions. Journal version: ACM TOPLAS 31(3), Article 11, pp. 11:1-11:50, 2009, doi:10.1145/1498926.1498929; in the authors' 2008 preprint of it, Lemma 6 is the Distribution Lemma and Section 9 notes that (q * r) and (q' * r) does not imply (q and q') * r in general, with q = emp, q' = x |-> - and r = true.
  * Klein, G., Kolanski, R. & Boyton, A., 'Separation Algebra', Archive of Formal Proofs, May 2012, https://www.isa-afp.org/entries/Separation_Algebra.html; companion paper Klein, Kolanski & Boyton, 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22. Class sep_algebra (unit 0, commutativity, associativity, disjointness laws; no cancellativity); class cancellative_sep_algebra adds x + z = y + z ==> x ## z ==> y ## z ==> x = y, with the comment that the results on precise assertions (distributivity over separating conjunction) require it; lemma precise_distribute: precise P = (forall Q R. ((Q and R) ** P) = ((Q ** P) and (R ** P))), P on the right.
  * Coq, Verified Software Toolchain: PrincetonUniversity/VST tag v2.14 (commit e1db53a4e22ddd3f8223532ba73127b706faf1b3), file msl/predicates_sa.v, lines 78-122: Definition precise (at most one join_sub substate in P) and Lemma precise_eq, proved under Join, Perm_alg, Sep_alg and Canc_alg (the cancellation class of msl/sepalg.v, join a1 b c -> join a2 b c -> a1 = a2): precise = fun P => forall Q R, P * (Q && R) = (P * Q) && (P * R), the binary form with P on the left. Book: Appel, A. W., Dockins, R., Hobor, A., Beringer, L., Dodds, J., Stewart, G., Blazy, S. & Leroy, X., 'Program Logics for Certified Compilers', Cambridge University Press, 2014, doi:10.1017/CBO9781107256552.
  * HOL4 theory examples/separationLogic/src/separationLogicScript.sml in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e (Tuerk, UCAM-CL-TR-799, 2011, doi:10.48456/tr-799). IS_PRECISE___CHARACTERISATION (lines 1690-1697): assuming IS_SEPARATION_COMBINATOR f (commutativity, associativity, a unit for each element, left cancellativity), ASL_IS_PRECISE f p iff for every nonempty set X of predicates, asl_star f (BIGINTER X) p = BIGINTER (IMAGE (\x. asl_star f x p) X): the infinitary form, with the precise p on the right of *.
  * Reynolds, J. C., 'Separation Logic: A Logic for Shared Mutable Data Structures', LICS 2002, pp. 55-74, doi:10.1109/LICS.2002.1029817. End of Section 2: the 'restricting the heap' formulation of locality. Section 3 defines intuitionistic assertions and states the distributive law for 'domain-exact' q; 'precise' is not used as a technical term. Section 4: frame rule soundness, citing Yang and O'Hearn.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

In a logic over an arbitrary separation structure, the conjunction rule for framed specifications (used e.g. for resource invariants) needs unique frames of the invariant, which coincides with precision only under cancellativity.

### R4b: `R4b-precise-implies-distribution-under-right-cancellation`

* **Kind / tier:** theorem, **T2**. Refines the cancellative results (Isabelle AFP precise_distribute; VST precise_eq; HOL4 IS_PRECISE___CHARACTERISATION; O'Hearn-Yang-Reynolds 2004 Lemma 3 for heaps) by identifying which cancellation law this direction uses, without commutativity or associativity.
* **Plain claim:** In a right-cancellative separation structure (no other laws assumed), every precise R (right-handed precision) satisfies (P * R) and (Q * R) |- (P and Q) * R for all P, Q.
* **Design question:** Which algebraic properties of assertions (precision) and of the state model (cancellativity) are needed for the law (P * R) and (Q * R) |- (P and Q) * R, which is used when a frame or invariant R must be pushed inside a conjunction (hypothetical frame rules, resource invariants with the conjunction rule)?

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.conjDistrib_of_precise_of_rightCancel.{u} {S : Type u} [SepStruct S] (hrc : RightCancel S) {R : Assn S}
  (hp : Precise R) : ConjDistrib R
```

Unfolded: RightCancel S := ∀ a b c, a ⊥ c → b ⊥ c → a ∘ c = b ∘ c → a = b; Precise and ConjDistrib as under R2c and R4a.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hrc : RightCancel S` | Turns 'same R-part' into 'same frame'. Can be weakened to cancellation at elements of R (not formalized). | tight: counterexample `Toy.Sep.orAlg_true_precise_and_not_conjDistrib` |
| `hp : Precise R` | Two R-decompositions of a state have the same R-part. | tight: counterexample `Toy.Sep.heap_rightCancel_and_oneCell_not_conjDistrib` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** Heap model (right-cancellative) with R = 0 |-> - (cell 0 is the only allocated cell, any value), which is precise. (Lean: `Toy.Sep.conjDistrib_of_precise_of_rightCancel_nonvacuous`).
* **Prior art:**
  * O'Hearn, P. W., Yang, H. & Reynolds, J. C., 'Separation and Information Hiding', POPL 2004, pp. 268-280, doi:10.1145/964001.964024: Section 9, Lemma 3: p is precise iff p * - distributes over conjunction, p * (q and r) = (p * q) and (p * r), in the store-and-heap model with p on the left; Theorem 5: the hypothetical frame rule is sound for fixed preconditions (resp. a fixed resource invariant) iff they are precise; Section 10.3, Theorem 11: soundness also holds for 'supported' preconditions or invariants with intuitionistic (closed under heap extension) postconditions. Journal version: ACM TOPLAS 31(3), Article 11, pp. 11:1-11:50, 2009, doi:10.1145/1498926.1498929; in the authors' 2008 preprint of it, Lemma 6 is the Distribution Lemma and Section 9 notes that (q * r) and (q' * r) does not imply (q and q') * r in general, with q = emp, q' = x |-> - and r = true.
  * Klein, G., Kolanski, R. & Boyton, A., 'Separation Algebra', Archive of Formal Proofs, May 2012, https://www.isa-afp.org/entries/Separation_Algebra.html; companion paper Klein, Kolanski & Boyton, 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22. Class sep_algebra (unit 0, commutativity, associativity, disjointness laws; no cancellativity); class cancellative_sep_algebra adds x + z = y + z ==> x ## z ==> y ## z ==> x = y, with the comment that the results on precise assertions (distributivity over separating conjunction) require it; lemma precise_distribute: precise P = (forall Q R. ((Q and R) ** P) = ((Q ** P) and (R ** P))), P on the right.
  * Coq, Verified Software Toolchain: PrincetonUniversity/VST tag v2.14 (commit e1db53a4e22ddd3f8223532ba73127b706faf1b3), file msl/predicates_sa.v, lines 78-122: Definition precise (at most one join_sub substate in P) and Lemma precise_eq, proved under Join, Perm_alg, Sep_alg and Canc_alg (the cancellation class of msl/sepalg.v, join a1 b c -> join a2 b c -> a1 = a2): precise = fun P => forall Q R, P * (Q && R) = (P * Q) && (P * R), the binary form with P on the left. Book: Appel, A. W., Dockins, R., Hobor, A., Beringer, L., Dodds, J., Stewart, G., Blazy, S. & Leroy, X., 'Program Logics for Certified Compilers', Cambridge University Press, 2014, doi:10.1017/CBO9781107256552.
  * HOL4 theory examples/separationLogic/src/separationLogicScript.sml in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e (Tuerk, UCAM-CL-TR-799, 2011, doi:10.48456/tr-799). IS_PRECISE___CHARACTERISATION (lines 1690-1697): assuming IS_SEPARATION_COMBINATOR f (commutativity, associativity, a unit for each element, left cancellativity), ASL_IS_PRECISE f p iff for every nonempty set X of predicates, asl_star f (BIGINTER X) p = BIGINTER (IMAGE (\x. asl_star f x p) X): the infinitary form, with the precise p on the right of *.
  * Gotsman, A., Berdine, J. & Cook, B., 'Precision and the Conjunction Rule in Concurrent Separation Logic', MFPS XXVII, ENTCS 276:171-190, 2011, doi:10.1016/j.entcs.2011.09.021. Definition 2.1: a separation algebra is a partial commutative monoid with unit, omitting (as the paper notes) the cancellativity required by Calcagno-O'Hearn-Yang 2007. Section 2.2: the 'command' that disposes cell 10 if it is allocated and is a no-op otherwise is not local; 'the requirement of locality rules out commands that can check if a cell is allocated in the heap other than by trying to access it and faulting if it is not allocated'. Theorem 4.1: concurrent separation logic is sound if resource invariants are precise and * is cancellative, or if the conjunction rule is not used.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

In right-cancellative state models, precise resource invariants distribute over conjunction.

### R4c: `R4c-distribution-implies-precise-under-left-cancellation`

* **Kind / tier:** theorem, **T2**. As R4b, for the other direction.
* **Plain claim:** In a left-cancellative separation structure (no other laws assumed), every R satisfying (P * R) and (Q * R) |- (P and Q) * R for all P, Q is precise (right-handed precision).
* **Design question:** Which algebraic properties of assertions (precision) and of the state model (cancellativity) are needed for the law (P * R) and (Q * R) |- (P and Q) * R, which is used when a frame or invariant R must be pushed inside a conjunction (hypothetical frame rules, resource invariants with the conjunction rule)?

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.precise_of_conjDistrib_of_leftCancel.{u} {S : Type u} [SepStruct S] (hlc : LeftCancel S) {R : Assn S}
  (hd : ConjDistrib R) : Precise R
```

Unfolded: LeftCancel S := ∀ a b c, c ⊥ a → c ⊥ b → c ∘ a = c ∘ b → a = b.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hlc : LeftCancel S` | Turns 'same frame' into 'same R-part'. | tight: counterexample `Toy.Sep.forkR_conjDistrib_and_not_precise` |
| `hd : ConjDistrib R` | Distribution for all P, Q (instantiated at singletons). | tight: counterexample `Toy.Sep.heap_leftCancel_and_oneCell_not_precise` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** Heap model (left-cancellative) with R = 0 |-> -, which satisfies the distribution law (proved directly). (Lean: `Toy.Sep.precise_of_conjDistrib_of_leftCancel_nonvacuous`).
* **Prior art:**
  * O'Hearn, P. W., Yang, H. & Reynolds, J. C., 'Separation and Information Hiding', POPL 2004, pp. 268-280, doi:10.1145/964001.964024: Section 9, Lemma 3: p is precise iff p * - distributes over conjunction, p * (q and r) = (p * q) and (p * r), in the store-and-heap model with p on the left; Theorem 5: the hypothetical frame rule is sound for fixed preconditions (resp. a fixed resource invariant) iff they are precise; Section 10.3, Theorem 11: soundness also holds for 'supported' preconditions or invariants with intuitionistic (closed under heap extension) postconditions. Journal version: ACM TOPLAS 31(3), Article 11, pp. 11:1-11:50, 2009, doi:10.1145/1498926.1498929; in the authors' 2008 preprint of it, Lemma 6 is the Distribution Lemma and Section 9 notes that (q * r) and (q' * r) does not imply (q and q') * r in general, with q = emp, q' = x |-> - and r = true.
  * Klein, G., Kolanski, R. & Boyton, A., 'Separation Algebra', Archive of Formal Proofs, May 2012, https://www.isa-afp.org/entries/Separation_Algebra.html; companion paper Klein, Kolanski & Boyton, 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22. Class sep_algebra (unit 0, commutativity, associativity, disjointness laws; no cancellativity); class cancellative_sep_algebra adds x + z = y + z ==> x ## z ==> y ## z ==> x = y, with the comment that the results on precise assertions (distributivity over separating conjunction) require it; lemma precise_distribute: precise P = (forall Q R. ((Q and R) ** P) = ((Q ** P) and (R ** P))), P on the right.
  * Coq, Verified Software Toolchain: PrincetonUniversity/VST tag v2.14 (commit e1db53a4e22ddd3f8223532ba73127b706faf1b3), file msl/predicates_sa.v, lines 78-122: Definition precise (at most one join_sub substate in P) and Lemma precise_eq, proved under Join, Perm_alg, Sep_alg and Canc_alg (the cancellation class of msl/sepalg.v, join a1 b c -> join a2 b c -> a1 = a2): precise = fun P => forall Q R, P * (Q && R) = (P * Q) && (P * R), the binary form with P on the left. Book: Appel, A. W., Dockins, R., Hobor, A., Beringer, L., Dodds, J., Stewart, G., Blazy, S. & Leroy, X., 'Program Logics for Certified Compilers', Cambridge University Press, 2014, doi:10.1017/CBO9781107256552.
  * HOL4 theory examples/separationLogic/src/separationLogicScript.sml in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e (Tuerk, UCAM-CL-TR-799, 2011, doi:10.48456/tr-799). IS_PRECISE___CHARACTERISATION (lines 1690-1697): assuming IS_SEPARATION_COMBINATOR f (commutativity, associativity, a unit for each element, left cancellativity), ASL_IS_PRECISE f p iff for every nonempty set X of predicates, asl_star f (BIGINTER X) p = BIGINTER (IMAGE (\x. asl_star f x p) X): the infinitary form, with the precise p on the right of *.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

In left-cancellative state models, any invariant that distributes over conjunction is precise.

### R4d: `R4d-heap-precise-iff-distribution`

* **Kind / tier:** characterization, **T0**. O'Hearn-Yang-Reynolds 2004 Lemma 3 (store-and-heap model, precise assertion on the left); Brookes 2007 Definition 11 remark; mechanized for cancellative separation algebras in Isabelle AFP (precise_distribute), VST (precise_eq) and, infinitary, HOL4 (IS_PRECISE___CHARACTERISATION).
* **Plain claim:** For finite heaps, an assertion R is precise, equivalently every heap has at most one subheap satisfying R (heap_precise_iff_atMostOneSubheap, proved), if and only if (P * R) and (Q * R) |- (P and Q) * R for all P, Q.
* **Design question:** In the plain heap model, are 'precise' and 'distributes over conjunction' the same notion? Yes.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.heap_precise_iff_conjDistrib {V : Type} (R : Assn (Heap V)) : Precise R ↔ ConjDistrib R

Toy.Sep.heap_precise_iff_atMostOneSubheap {V : Type} (R : Assn (Heap V)) :
  Precise R ↔ ∀ (h r₁ r₂ : Heap V), r₁.Sub h → r₂.Sub h → R r₁ → R r₂ → r₁ = r₂
```

Unfolded: in Heap V, h₁ ⊥ h₂ := ∀ k, h₁ k = none ∨ h₂ k = none and (h₁ ∘ h₂) k := (h₁ k).or (h₂ k); Heap.Sub r h := ∀ k, r k ≠ none → h k = r k.

**Hypothesis ledger:**

No hypotheses (empty ledger).

Ledger scope: heap_precise_iff_conjDistrib and heap_precise_iff_atMostOneSubheap have no hypotheses: they hold for every value type V : Type and every assertion R : Assn (Heap V) (all predicates on heaps). They are universally quantified characterizations, not statements about a fixed instance. They are specific to the heap model, which supplies what R4b and R4c take as hypotheses: Heap V is right- and left-cancellative (heap_rightCancel, heap_leftCancel), and the proof of heap_precise_iff_conjDistrib combines conjDistrib_of_precise_of_rightCancel and precise_of_conjDistrib_of_leftCancel with these two facts. ConjDistrib R quantifies over all predicates P, Q.

* **Depth:** `shallow`.
* **Non-vacuity witness:** Both sides hold for 0 |-> -; both fail for oneCell. (Lean: `Toy.Sep.heap_precise_iff_conjDistrib_nonvacuous`).
* **Supporting lemmas cited in the ledger scope** (`lean_names`; quoted under Key definitions): `Toy.Sep.heap_rightCancel`, `Toy.Sep.heap_leftCancel`.
* **Prior art:**
  * O'Hearn, P. W., Yang, H. & Reynolds, J. C., 'Separation and Information Hiding', POPL 2004, pp. 268-280, doi:10.1145/964001.964024: Section 9, Lemma 3: p is precise iff p * - distributes over conjunction, p * (q and r) = (p * q) and (p * r), in the store-and-heap model with p on the left; Theorem 5: the hypothetical frame rule is sound for fixed preconditions (resp. a fixed resource invariant) iff they are precise; Section 10.3, Theorem 11: soundness also holds for 'supported' preconditions or invariants with intuitionistic (closed under heap extension) postconditions. Journal version: ACM TOPLAS 31(3), Article 11, pp. 11:1-11:50, 2009, doi:10.1145/1498926.1498929; in the authors' 2008 preprint of it, Lemma 6 is the Distribution Lemma and Section 9 notes that (q * r) and (q' * r) does not imply (q and q') * r in general, with q = emp, q' = x |-> - and r = true.
  * Brookes, S., 'A Semantics for Concurrent Separation Logic', Theoretical Computer Science 375(1-3):227-270, 2007, doi:10.1016/j.tcs.2006.12.034 (CONCUR 2004 version doi:10.1007/978-3-540-28644-8_2). Definition 11 defines precise formulas in the concrete store-and-heap model and remarks that for precise R, (p and q) * R and (p * R) and (q * R) are logically equivalent.
  * Klein, G., Kolanski, R. & Boyton, A., 'Separation Algebra', Archive of Formal Proofs, May 2012, https://www.isa-afp.org/entries/Separation_Algebra.html; companion paper Klein, Kolanski & Boyton, 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22. Class sep_algebra (unit 0, commutativity, associativity, disjointness laws; no cancellativity); class cancellative_sep_algebra adds x + z = y + z ==> x ## z ==> y ## z ==> x = y, with the comment that the results on precise assertions (distributivity over separating conjunction) require it; lemma precise_distribute: precise P = (forall Q R. ((Q and R) ** P) = ((Q ** P) and (R ** P))), P on the right.
  * Coq, Verified Software Toolchain: PrincetonUniversity/VST tag v2.14 (commit e1db53a4e22ddd3f8223532ba73127b706faf1b3), file msl/predicates_sa.v, lines 78-122: Definition precise (at most one join_sub substate in P) and Lemma precise_eq, proved under Join, Perm_alg, Sep_alg and Canc_alg (the cancellation class of msl/sepalg.v, join a1 b c -> join a2 b c -> a1 = a2): precise = fun P => forall Q R, P * (Q && R) = (P * Q) && (P * R), the binary form with P on the left. Book: Appel, A. W., Dockins, R., Hobor, A., Beringer, L., Dodds, J., Stewart, G., Blazy, S. & Leroy, X., 'Program Logics for Certified Compilers', Cambridge University Press, 2014, doi:10.1017/CBO9781107256552.
  * HOL4 theory examples/separationLogic/src/separationLogicScript.sml in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e (Tuerk, UCAM-CL-TR-799, 2011, doi:10.48456/tr-799). IS_PRECISE___CHARACTERISATION (lines 1690-1697): assuming IS_SEPARATION_COMBINATOR f (commutativity, associativity, a unit for each element, left cancellativity), ASL_IS_PRECISE f p iff for every nonempty set X of predicates, asl_star f (BIGINTER X) p = BIGINTER (IMAGE (\x. asl_star f x p) X): the infinitary form, with the precise p on the right of *.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

For logics whose state model is the standard finite-heap model, 'precise' (at most one sub-heap satisfies R) and 'distributes over conjunction' are interchangeable requirements on frames.

### R4e: `R4e-imprecise-assertions-violate-distribution`

* **Kind / tier:** counterexample, **T0**. Concrete heap counterexamples of this kind are in the literature: O'Hearn-Yang-Reynolds (journal version, r = true with q = emp, q' = x |-> -) and Calcagno-O'Hearn-Yang 2007 Section 2 (an imprecise two-cell disjunction). Restated here with explicit witnesses.
* **Plain claim:** The heap assertions 'exactly one cell is allocated, at some address' and 'some cell is allocated' are imprecise, and for each the distribution law fails with P = {0 |-> 1}, Q = {1 |-> 2} on the heap (0 |-> 1) o (1 |-> 2).
* **Design question:** Which natural frames break the distribution law?

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.oneCell_conjDistrib_fails :
  sep (sing (Heap.pt 0 1)) oneCell (SepStruct.union (Heap.pt 0 1) (Heap.pt 1 2)) ∧
    sep (sing (Heap.pt 1 2)) oneCell (SepStruct.union (Heap.pt 0 1) (Heap.pt 1 2)) ∧
      ¬sep (conj (sing (Heap.pt 0 1)) (sing (Heap.pt 1 2))) oneCell (SepStruct.union (Heap.pt 0 1) (Heap.pt 1 2))

Toy.Sep.someCellAllocated_conjDistrib_fails :
  sep (sing (Heap.pt 0 1)) someCellAllocated (SepStruct.union (Heap.pt 0 1) (Heap.pt 1 2)) ∧
    sep (sing (Heap.pt 1 2)) someCellAllocated (SepStruct.union (Heap.pt 0 1) (Heap.pt 1 2)) ∧
      ¬sep (conj (sing (Heap.pt 0 1)) (sing (Heap.pt 1 2))) someCellAllocated
          (SepStruct.union (Heap.pt 0 1) (Heap.pt 1 2))

Toy.Sep.oneCell_not_precise : ¬Precise oneCell

Toy.Sep.someCellAllocated_not_precise : ¬Precise someCellAllocated
```

Unfolded: oneCell h := ∃ k v, h = (k ↦ v); someCellAllocated h := ∃ k, h k ≠ none.

**Hypothesis ledger:**

No hypotheses (empty ledger).

Ledger scope: No hypotheses: all four statements are closed statements about the specific assertions oneCell and someCellAllocated in Heap Nat.

* **Depth:** `shallow`.
* **Non-vacuity witness:** Concrete heap (0 |-> 1) o (1 |-> 2). (Lean: `Toy.Sep.oneCell_conjDistrib_fails`).
* **Supporting lemma cited in the non-claims** (`lean_names`; quoted under Key definitions): `Toy.Sep.ptAny_precise`.
* **Prior art:**
  * O'Hearn, P. W., Yang, H. & Reynolds, J. C., 'Separation and Information Hiding', POPL 2004, pp. 268-280, doi:10.1145/964001.964024: Section 9, Lemma 3: p is precise iff p * - distributes over conjunction, p * (q and r) = (p * q) and (p * r), in the store-and-heap model with p on the left; Theorem 5: the hypothetical frame rule is sound for fixed preconditions (resp. a fixed resource invariant) iff they are precise; Section 10.3, Theorem 11: soundness also holds for 'supported' preconditions or invariants with intuitionistic (closed under heap extension) postconditions. Journal version: ACM TOPLAS 31(3), Article 11, pp. 11:1-11:50, 2009, doi:10.1145/1498926.1498929; in the authors' 2008 preprint of it, Lemma 6 is the Distribution Lemma and Section 9 notes that (q * r) and (q' * r) does not imply (q and q') * r in general, with q = emp, q' = x |-> - and r = true.
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf). Definition 1: a separation algebra is a cancellative partial commutative monoid. Definition 3: p is precise if every state has at most one substate in p. Section 2, Examples of Predicates: the two-cell disjunction l0 |-> rv0 or l1 |-> rv1 is not precise. Lemma 4: every singleton is precise; p is precise iff for all nonempty X, (meet X) * p = meet{x * p | x in X}; the remark after it says injectivity of sigma . (-) is equivalent to that distribution for singleton frames {sigma}. Section 3: a relation satisfies Safety Monotonicity and the Frame Property 'iff the frame rule is sound for it' (stated without proof).

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Existentially quantified single-cell or nonemptiness assertions cannot be used where precision or distribution is required.

### R4f: `R4f-precision-and-distribution-incomparable-without-cancellativity`

* **Kind / tier:** counterexample, **T1**. The sources state that the precision/distribution correspondence needs cancellativity (Isabelle AFP comment on cancellative_sep_algebra; Gotsman-Berdine-Cook 2011 omit cancellativity on purpose). The two separating structures make this precise. Not claimed novel.
* **Plain claim:** In partial commutative monoids with a unit that are not cancellative (IsSepAlgebra without RightCancel or LeftCancel; separation algebras in the sense of Gotsman-Berdine-Cook 2011 and the Isabelle AFP class sep_algebra, but not in the cancellative sense of Calcagno-O'Hearn-Yang 2007 and Dockins-Hobor-Appel 2009), neither precision nor the distribution law implies the other: in OrAlg the frame {true} is precise but does not distribute; in Fork the frame {a, b} distributes but is not precise.
* **Design question:** Can a resource model without cancellativity (e.g. idempotent permissions) keep 'precise frames give the distribution law'? Not in general.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened; `orAlg_true_precise_and_not_conjDistrib` with `set_option pp.structureInstanceTypes true`):

```lean
Toy.Sep.orAlg_true_precise_and_not_conjDistrib :
  Precise (sing { bit := true : OrAlg }) ∧ ¬ConjDistrib (sing { bit := true : OrAlg })

Toy.Sep.forkR_conjDistrib_and_not_precise : ConjDistrib forkR ∧ ¬Precise forkR

Toy.Sep.orAlg_isSepAlgebra : IsSepAlgebra OrAlg OrAlg.unit

Toy.Sep.fork_isSepAlgebra : IsSepAlgebra Fork Fork.e

Toy.Sep.orAlg_not_rightCancel : ¬RightCancel OrAlg

Toy.Sep.orAlg_not_leftCancel : ¬LeftCancel OrAlg

Toy.Sep.fork_not_rightCancel : ¬RightCancel Fork

Toy.Sep.fork_not_leftCancel : ¬LeftCancel Fork
```

Unfolded: IsSepAlgebra S e bundles DisjSymm S, UnionComm S, UnionAssoc S and UnitLaw e (no cancellativity).

**Hypothesis ledger:**

No hypotheses (empty ledger).

Ledger scope: No hypotheses: all eight statements are closed statements about the specific structures OrAlg and Fork (quoted under Key definitions) and the assertions sing { bit := true } and forkR.

* **Depth:** `shallow`.
* **Non-vacuity witness:** OrAlg and Fork satisfy IsSepAlgebra and fail both cancellation laws (all proved). (Lean: `Toy.Sep.orAlg_isSepAlgebra`, `Toy.Sep.fork_isSepAlgebra`).
* **Prior art:**
  * Klein, G., Kolanski, R. & Boyton, A., 'Separation Algebra', Archive of Formal Proofs, May 2012, https://www.isa-afp.org/entries/Separation_Algebra.html; companion paper Klein, Kolanski & Boyton, 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22. Class sep_algebra (unit 0, commutativity, associativity, disjointness laws; no cancellativity); class cancellative_sep_algebra adds x + z = y + z ==> x ## z ==> y ## z ==> x = y, with the comment that the results on precise assertions (distributivity over separating conjunction) require it; lemma precise_distribute: precise P = (forall Q R. ((Q and R) ** P) = ((Q ** P) and (R ** P))), P on the right.
  * Gotsman, A., Berdine, J. & Cook, B., 'Precision and the Conjunction Rule in Concurrent Separation Logic', MFPS XXVII, ENTCS 276:171-190, 2011, doi:10.1016/j.entcs.2011.09.021. Definition 2.1: a separation algebra is a partial commutative monoid with unit, omitting (as the paper notes) the cancellativity required by Calcagno-O'Hearn-Yang 2007. Section 2.2: the 'command' that disposes cell 10 if it is allocated and is a no-op otherwise is not local; 'the requirement of locality rules out commands that can check if a cell is allocated in the heap other than by trying to access it and faulting if it is not allocated'. Theorem 4.1: concurrent separation logic is sound if resource invariants are precise and * is cancellative, or if the conjunction rule is not used.
  * Dockins, R., Hobor, A. & Appel, A. W., 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, doi:10.1007/978-3-642-10672-9_13. Separation algebras as a join relation with functionality, commutativity, associativity and cancellation as core axioms, and possibly multiple units; positivity and disjointness are optional extra axioms.
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf). Definition 1: a separation algebra is a cancellative partial commutative monoid. Definition 3: p is precise if every state has at most one substate in p. Section 2, Examples of Predicates: the two-cell disjunction l0 |-> rv0 or l1 |-> rv1 is not precise. Lemma 4: every singleton is precise; p is precise iff for all nonempty X, (meet X) * p = meet{x * p | x in X}; the remark after it says injectivity of sigma . (-) is equivalent to that distribution for singleton frames {sigma}. Section 3: a relation satisfies Safety Monotonicity and the Frame Property 'iff the frame rule is sound for it' (stated without proof).
  * Coq, Verified Software Toolchain: PrincetonUniversity/VST tag v2.14 (commit e1db53a4e22ddd3f8223532ba73127b706faf1b3), file msl/predicates_sa.v, lines 78-122: Definition precise (at most one join_sub substate in P) and Lemma precise_eq, proved under Join, Perm_alg, Sep_alg and Canc_alg (the cancellation class of msl/sepalg.v, join a1 b c -> join a2 b c -> a1 = a2): precise = fun P => forall Q R, P * (Q && R) = (P * Q) && (P * R), the binary form with P on the left. Book: Appel, A. W., Dockins, R., Hobor, A., Beringer, L., Dodds, J., Stewart, G., Blazy, S. & Leroy, X., 'Program Logics for Certified Compilers', Cambridge University Press, 2014, doi:10.1017/CBO9781107256552.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Logics whose resource model is a non-cancellative partial commutative monoid (for example, with idempotent or saturating composition) must choose between precision and distribution explicitly; neither implies the other there.

### R4g: `R4g-cancellation-laws-coincide-under-commutativity`

* **Kind / tier:** theorem, **T0**. Standard algebra; HOL4 derives right from left cancellativity under commutativity.
* **Plain claim:** If disjointness is symmetric and union is commutative, left and right cancellativity are equivalent (an iff, and each direction separately).
* **Design question:** Reference point: in commutative structures with symmetric disjointness, R4b and R4c combine with a single cancellation law (as in R4d).

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.leftCancel_iff_rightCancel_of_disjSymm_of_unionComm.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S)
  (hc : UnionComm S) : LeftCancel S ↔ RightCancel S

Toy.Sep.rightCancel_of_disjSymm_of_unionComm_of_leftCancel.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S)
  (hc : UnionComm S) (hl : LeftCancel S) : RightCancel S

Toy.Sep.leftCancel_of_disjSymm_of_unionComm_of_rightCancel.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S)
  (hc : UnionComm S) (hr : RightCancel S) : LeftCancel S
```

Unfolded: DisjSymm S := ∀ a b, a ⊥ b → b ⊥ a; UnionComm S := ∀ a b, a ⊥ b → a ∘ b = b ∘ a; LeftCancel and RightCancel as under R4b and R4c.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hc : UnionComm S` | Moves the shared element from one side to the other. | tight: counterexample `Toy.Sep.projRight_disjSymm_leftCancel_not_rightCancel`, `Toy.Sep.projLeft_disjSymm_rightCancel_not_leftCancel` |
| `hs : DisjSymm S` | Moves disjointness facts to the other side. | tight: counterexample `Toy.Sep.orDisjRight_unionComm_leftCancel_not_rightCancel`, `Toy.Sep.orDisjLeft_unionComm_rightCancel_not_leftCancel` |
| `hl : LeftCancel S (resp. hr : RightCancel S), directional lemmas only` | The cancellation law being transported. | tight: counterexample `Toy.Sep.orAlg_disjSymm_unionComm_not_rightCancel`, `Toy.Sep.orAlg_disjSymm_unionComm_not_leftCancel` |

* **Depth:** `definitional`.
* **Non-vacuity witness:** Heap model: symmetric, commutative, left- and right-cancellative. (Lean: `Toy.Sep.cancel_coincide_nonvacuous`).
* **Prior art:**
  * HOL4 theory examples/separationLogic/src/separationLogicScript.sml in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e: IS_SEPARATION_COMBINATOR assumes commutativity and only left cancellativity (OPTION_IS_LEFT_CANCELLATIVE, lines 19-22 and 39-45); IS_SEPARATION_COMBINATOR_EXPAND_THM (lines 286-303) derives right cancellativity as well.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

In commutative state models only one cancellation law needs to be checked.

### R5: `R5-standard-heap-commands-local`

* **Kind / tier:** theorem, **T0**. Yang-O'Hearn 2002 Lemmas 1-2 for their language; frame lemmas for similar primitives are mechanized for total correctness in Coq (SLF) and Lean 4 (SPLean).
* **Plain claim:** In the heap model, lookup [r] := [k], mutation [k] := v, allocation at a nondeterministically chosen fresh address without recording it (alloc v) or recording it in cell r (allocInto r v, with heap values in Nat so that an address fits in a cell), and deallocation free k are each safety-monotone and have the frame property. lookup, mutate, alloc and free are stated for every value type V.
* **Design question:** Which primitive heap operations can a frame-rule logic admit? All the standard ones, provided allocation is nondeterministic.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened; `lookup_safetyMono_and_frameProp` and `free_safetyMono_and_frameProp` printed as `name : type` with `set_option pp.analyze true`):

```lean
Toy.Sep.lookup_safetyMono_and_frameProp : ∀ {V : Type} (k r : Nat), SafetyMono (S := Heap V) (lookup k r) ∧ FrameProp (S := Heap V) (lookup k r)

Toy.Sep.mutate_safetyMono_and_frameProp {V : Type} (k : Nat) (v : V) : SafetyMono (mutate k v) ∧ FrameProp (mutate k v)

Toy.Sep.alloc_safetyMono_and_frameProp {V : Type} (v : V) : SafetyMono (alloc v) ∧ FrameProp (alloc v)

Toy.Sep.allocInto_safetyMono_and_frameProp (r v : Nat) : SafetyMono (allocInto r v) ∧ FrameProp (allocInto r v)

Toy.Sep.free_safetyMono_and_frameProp : ∀ {V : Type} (k : Nat), SafetyMono (S := Heap V) (free k) ∧ FrameProp (S := Heap V) (free k)
```

Unfolded: lookup k r h o := ((h k = none ∨ h r = none) ∧ o = fault) ∨ (h k ≠ none ∧ h r ≠ none ∧ o = ok h[r ↦ h k]); mutate k v h o := (h k = none ∧ o = fault) ∨ (h k ≠ none ∧ o = ok h[k ↦ v]); alloc v h o := ∃ k, h k = none ∧ o = ok h[k ↦ v]; allocInto r v h o := (h r = none ∧ o = fault) ∨ (h r ≠ none ∧ ∃ k, h k = none ∧ o = ok h[k ↦ v][r ↦ k]); free k h o := (h k = none ∧ o = fault) ∨ (h k ≠ none ∧ o = ok h[k ↦ none]).

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `(definition) allocation chooses its fresh address nondeterministically` | Every predictable allocation policy that still runs when its address is occupied violates the frame property. | tight: counterexample `Toy.Sep.allocLeast_not_frameProp`, `Toy.Sep.detAlloc_not_frameProp` |

* **Depth:** `shallow`. alloc_safetyMono_and_frameProp is proved: alloc never faults, and its frame property is alloc_frameProp (the positive control of R3d).
* **Non-vacuity witness:** For each of the five commands, a disjoint pair h, h' with h' non-empty, the command safe at h, and a normal run from h o h', so the antecedents of both properties are met. (Lean: `Toy.Sep.heap_commands_framed_runs_nonvacuous`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).
  * Reynolds, J. C., 'Separation Logic: A Logic for Shared Mutable Data Structures', LICS 2002, pp. 55-74, doi:10.1109/LICS.2002.1029817. End of Section 2: the 'restricting the heap' formulation of locality. Section 3 defines intuitionistic assertions and states the distributive law for 'domain-exact' q; 'precise' is not used as a technical term. Section 4: frame rule soundness, citing Yang and O'Hearn.
  * Coq: Chargueraud, A., Separation Logic Foundations (Software Foundations series, https://softwarefoundations.cis.upenn.edu/slf-current/), chapter Triples: lemma eval_frame (eval h1 t Q -> Fmap.disjoint h1 h2 -> eval (h1 \u h2) t (Q \*+ (= h2))) for an omni-big-step, total-correctness evaluation judgment over finite-map heaps, including allocation, read, write and free.
  * Lean 4: verse-lab/splean at commit e24286f51bd9ee207197d47ec587d592cdfb0ddc (Apache-2.0), SPLean/Theories/SepLog.lean lines 475-478: eval_frame for a postcondition-indexed big-step (total-correctness) evaluation judgment over finite-map heaps; its language has scoped allocation, read and write but no free.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

The standard small-axiom heap primitives of separation logic (lookup, mutation, nondeterministic allocation, deallocation) satisfy the locality obligations of R1, in this heap model without store or address arithmetic.

### R6a: `R6a-fq-triple-frame-rule-from-two-sided-associativity`

* **Kind / tier:** theorem, **T0**. Frame-quantified ('baked-in frame') triples and the derivation of framing from associativity of * are in Birkedal-Torp-Smith-Yang 2005/2006 and Chargueraud 2020 (Definition 5.2, Appendix C.1), with mechanizations in Coq (Appel-Blazy 2007; Separation Logic Foundations) and HOL4 (Myreen-Gordon 2007). The law-minimal form here is not claimed as T2.
* **Plain claim:** In any separation structure with two-sided partial associativity (ha : UnionAssoc S and har : UnionAssocRev S; no commutativity, unit, cancellativity or locality), frame-quantified triples FQTriple P c Q := for all R, {P * R} c {Q * R} satisfy the frame rule for every command c: FQTriple P c Q implies FQTriple (P * R) c (Q * R). The heap model is an instance (no hypotheses). The other four theorems on this card take the explicit hypothesis hs : DisjSymm S (symmetric disjointness) in place of har: under hs : DisjSymm S, hc : UnionComm S and ha : UnionAssoc S, UnionAssocRev S and the frame rule hold; commutativity is not needed for this step, so hs : DisjSymm S and ha : UnionAssoc S alone already give UnionAssocRev S and the frame rule. The hypothesis hs : DisjSymm S cannot be dropped from these four theorems: UnionAssoc alone, or UnionAssoc together with UnionComm, gives neither UnionAssocRev nor the frame rule.
* **Design question:** Separate frame rule with locality obligations on primitives, versus frame baked into the specification? The second makes the frame rule free for every command, at the cost of two-sided associativity of the state model and of proving each primitive's specification under all frames.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.fqTriple_frame_of_unionAssoc_of_unionAssocRev.{u} {S : Type u} [SepStruct S] (ha : UnionAssoc S)
  (har : UnionAssocRev S) (c : Cmd S) {P Q R : Assn S} (ht : FQTriple P c Q) : FQTriple (sep P R) c (sep Q R)

Toy.Sep.fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S)
  (hc : UnionComm S) (ha : UnionAssoc S) (c : Cmd S) {P Q R : Assn S} (ht : FQTriple P c Q) :
  FQTriple (sep P R) c (sep Q R)

Toy.Sep.heap_fqTriple_frame {V : Type} (c : Cmd (Heap V)) {P Q R : Assn (Heap V)} (ht : FQTriple P c Q) :
  FQTriple (sep P R) c (sep Q R)

Toy.Sep.unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S)
  (hc : UnionComm S) (ha : UnionAssoc S) : UnionAssocRev S

Toy.Sep.fqTriple_frame_of_disjSymm_of_unionAssoc.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S) (ha : UnionAssoc S)
  (c : Cmd S) {P Q R : Assn S} (ht : FQTriple P c Q) : FQTriple (sep P R) c (sep Q R)

Toy.Sep.unionAssocRev_of_disjSymm_of_unionAssoc.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S) (ha : UnionAssoc S) :
  UnionAssocRev S
```

Unfolded: FQTriple P c Q := ∀ R, Triple (P * R) c (Q * R); UnionAssoc S := ∀ a b c, a ⊥ b → (a ∘ b) ⊥ c → b ⊥ c ∧ a ⊥ (b ∘ c) ∧ (a ∘ b) ∘ c = a ∘ (b ∘ c); UnionAssocRev S := ∀ a b c, b ⊥ c → a ⊥ (b ∘ c) → a ⊥ b ∧ (a ∘ b) ⊥ c ∧ a ∘ (b ∘ c) = (a ∘ b) ∘ c.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `ha : UnionAssoc S` | Re-associates the framed precondition (P * R) * R' into P * (R * R'). In the four DisjSymm theorems it is also the source of UnionAssocRev. | tight: counterexample `Toy.Sep.assocGap_unionAssocRev_and_fqTriple_frame_fails`, `Toy.Sep.symmAssocGap_disjSymm_unionComm_and_fqTriple_frame_fails` |
| `har : UnionAssocRev S` | Re-associates the postcondition Q * (R * R') into (Q * R) * R'. | tight: counterexample `Toy.Sep.oneWayAssoc_unionAssoc_and_fqTriple_frame_fails` |
| `hs : DisjSymm S (the four theorems fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc, unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc, fqTriple_frame_of_disjSymm_of_unionAssoc, unionAssocRev_of_disjSymm_of_unionAssoc)` | Takes the place of har: three cyclic applications of UnionAssoc, with DisjSymm moving disjointness facts to the other side between them, give UnionAssocRev, which re-associates the postcondition. | tight: counterexample `Toy.Sep.oneWayAssoc_unionAssoc_and_fqTriple_frame_fails`, `Toy.Sep.commOneWay_unionComm_unionAssoc_and_fqTriple_frame_fails` |
| `ht : FQTriple P c Q` | Premise of the frame rule. | tight: counterexample `Toy.Sep.fqTriple_frame_premise_tight` |
| `hc : UnionComm S (only fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc and unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc)` | Not needed: DisjSymm and UnionAssoc already give UnionAssocRev (Toy.Sep.unionAssocRev_of_disjSymm_of_unionAssoc), hence the frame rule (Toy.Sep.fqTriple_frame_of_disjSymm_of_unionAssoc); a non-commutative structure with DisjSymm, UnionAssoc and UnionAssocRev is Toy.Sep.projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm. The two corollaries keep UnionComm so that their hypotheses are exactly the partial-commutative-monoid laws of IsSepAlgebra. | harmless |

Ledger scope: The entries ha and har refer to the primary, law-minimal theorem fqTriple_frame_of_unionAssoc_of_unionAssocRev. hs is a hypothesis of the four DisjSymm theorems, where it takes the place of har; its counterexample oneWayAssoc_unionAssoc_and_fqTriple_frame_fails covers the two theorems without hc (UnionAssoc holds; UnionAssocRev and the framed triple fail), and commOneWay_unionComm_unionAssoc_and_fqTriple_frame_fails covers the two with hc (UnionComm and UnionAssoc hold; DisjSymm, UnionAssocRev and the framed triple fail). ha is also a hypothesis of the four DisjSymm theorems: assocGap_unionAssocRev_and_fqTriple_frame_fails witnesses its tightness in the primary theorem, and symmAssocGap_disjSymm_unionComm_and_fqTriple_frame_fails (DisjSymm and UnionComm hold; UnionAssoc, UnionAssocRev and the framed triple fail) in the four DisjSymm theorems. ht is the premise of the four frame-rule theorems (fqTriple_frame_of_unionAssoc_of_unionAssocRev, fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc, fqTriple_frame_of_disjSymm_of_unionAssoc, heap_fqTriple_frame); the two unionAssocRev_of_... theorems have no ht. Its counterexample is in the heap model, which also satisfies DisjSymm and UnionComm (boundary_witnesses_nonvacuous). heap_fqTriple_frame has no algebraic hypotheses (the heap model satisfies both associativity directions); hc is listed only for the two partial-commutative-monoid corollaries.

* **Depth:** `shallow`.
* **Non-vacuity witness:** The heap model has both associativity directions, and FQTriple {emp} allocLeast 1 {exists k. k |-> 1} holds for the non-local command allocLeast. (Lean: `Toy.Sep.fqTriple_frame_nonvacuous`).
* **Supporting lemma cited in the hypothesis ledger** (`lean_names`; quoted under Key definitions): `Toy.Sep.projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm`.
* **Prior art:**
  * Chargueraud, A., 'Separation Logic for Sequential Programs (Functional Pearl)', Proc. ACM Program. Lang. 4(ICFP), Article 116, 2020, doi:10.1145/3408998 (author PDF https://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf). Definition 5.1: total-correctness Hoare triple HOARE{H} t {Q}. Definition 5.2: {H} t {Q} == forall H', HOARE{H * H'} t {Q * H'}, which 'bakes in the frame rule'. Lemma 5.4 lists the structural rules including frame; Appendix C.1 (author PDF) proves the combined consequence-frame rule (Lemma 5.5) using associativity of * (star-assoc, Lemma 3.9). Section 10 attributes the idea to Birkedal, Torp-Smith and Yang. The paper describes an accompanying course in the style of the Software Foundations series with all statements and proofs formalized in Coq (published as Software Foundations Volume 6, Separation Logic Foundations).
  * Birkedal, L., Torp-Smith, N. & Yang, H., 'Semantics of Separation-Logic Typing and Higher-Order Frame Rules', LICS 2005, pp. 260-269, doi:10.1109/LICS.2005.47; journal version 'Semantics of Separation-Logic Typing and Higher-order Frame Rules for Algol-like Languages', Logical Methods in Computer Science 2(5:1), 2006, doi:10.2168/LMCS-2(5:1)2006, arXiv:cs/0610081. In the journal version (Section 4.1) a triple object [p, q] contains, for each frame p0, the commands satisfying {p * p0} - {q * p0}; invariant extension inv(-, p) adds a frame, and Lemmas 4.4-4.5 use associativity of *. Their base commands are themselves required to satisfy safety monotonicity and the frame property.
  * Appel, A. W. & Blazy, S., 'Separation Logic for Small-Step Cminor', TPHOLs 2007, LNCS 4732, pp. 5-21, doi:10.1007/978-3-540-74591-4_3 (arXiv:0707.4389). Hoare sextuples are defined by quantifying over every frame A (and continuation), for partial correctness, mechanized in Coq (Definition 8 in the arXiv version).
  * Myreen, M. O. & Gordon, M. J. C., 'Hoare Logic for Realistically Modelled Machine Code', TACAS 2007, LNCS 4424, pp. 568-582, doi:10.1007/978-3-540-71209-1_44, mechanized in HOL4. The frame-quantified specification form is attested here only by the HOL4 sources, not by the paper text: in HOL-Theorem-Prover/HOL at commit c2b475d585febe0e718f87ab51959c0a73fc924e, examples/machine-code/hoare-triple/progScript.sml lines 24-39, RUN_def states RUN p q := for all state and r, if SEP_REFINE (p * r) less to_set state or allow state, then for every execution sequence seq from state there is an i with SEP_REFINE (q * r) less to_set (seq i) or allow (seq i); SPEC p c q is RUN (CODE_POOL instr c * p) (CODE_POOL instr c * q). The frame r is universally quantified, and the postcondition must be reached at some point of every execution sequence.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

A program logic that bakes the frame into its specifications (FQTriple) gets the frame rule for every command, local or not, provided the state model has two-sided partial associativity; the cost moves into proving every primitive's specification under all frames.

### R6b: `R6b-fq-triple-implies-plain-triple-given-right-unit`

* **Kind / tier:** theorem, **T0**. Instantiating the frame with the unit recovers the plain triple, as in Chargueraud 2020 (Definitions 5.1-5.2) and the other cited baked-in-frame logics.
* **Plain claim:** In any separation structure with a right unit e (every state is disjoint from e and a o e = a), FQTriple P c Q implies the plain triple {P} c {Q}, for every command. A left unit with symmetric disjointness and commutative union suffices; the heap model, with e = emp, is an instance.
* **Design question:** Do frame-quantified specifications still give ordinary triples? Yes, given a right unit (which is necessary).

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.triple_of_fqTriple_of_rightUnitLaw.{u} {S : Type u} [SepStruct S] {e : S} (hu : RightUnitLaw e) (c : Cmd S)
  {P Q : Assn S} (ht : FQTriple P c Q) : Triple P c Q

Toy.Sep.triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw.{u} {S : Type u} [SepStruct S] {e : S} (hs : DisjSymm S)
  (hc : UnionComm S) (hu : UnitLaw e) (c : Cmd S) {P Q : Assn S} (ht : FQTriple P c Q) : Triple P c Q

Toy.Sep.heap_triple_of_fqTriple {V : Type} (c : Cmd (Heap V)) {P Q : Assn (Heap V)} (ht : FQTriple P c Q) : Triple P c Q

Toy.Sep.rightUnitLaw_of_disjSymm_of_unionComm_of_unitLaw.{u} {S : Type u} [SepStruct S] {e : S} (hs : DisjSymm S)
  (hc : UnionComm S) (hu : UnitLaw e) : RightUnitLaw e
```

Unfolded: RightUnitLaw e := ∀ a, a ⊥ e ∧ a ∘ e = a; UnitLaw e := ∀ a, e ⊥ a ∧ e ∘ a = a.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hu : RightUnitLaw e` | Instantiates the frame with {e}. | tight: counterexample `Toy.Sep.emptyDisj_no_rightUnit_and_fqTriple_adequacy_fails` |
| `ht : FQTriple P c Q` | Premise of the adequacy theorem. | tight: counterexample `Toy.Sep.triple_of_fqTriple_premise_tight` |
| `hs : DisjSymm S (left-unit corollary triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw)` | Turns e ⊥ a (from the left unit) into a ⊥ e. | tight: counterexample `Toy.Sep.leftDisjCommUnit_unionComm_unitLaw_and_fqTriple_adequacy_fails` |
| `hc : UnionComm S (left-unit corollary)` | Turns e ∘ a = a into a ∘ e = a. | tight: counterexample `Toy.Sep.projRight_disjSymm_unitLaw_and_fqTriple_adequacy_fails` |
| `hu : UnitLaw e (left-unit corollary)` | Supplies the unit used as the frame. | tight: counterexample `Toy.Sep.emptyDisj_disjSymm_unionComm_no_unit_and_fqTriple_adequacy_fails` |

Ledger scope: The entry hu : RightUnitLaw e refers to the primary theorem triple_of_fqTriple_of_rightUnitLaw; ht is the premise of the three triple theorems on this card (rightUnitLaw_of_disjSymm_of_unionComm_of_unitLaw, the algebraic lemma behind the left-unit corollary, has no ht and takes the same hs, hc and hu : UnitLaw e as that corollary); the entries marked 'left-unit corollary' refer to triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw; heap_triple_of_fqTriple has no algebraic hypotheses.

* **Depth:** `shallow`.
* **Non-vacuity witness:** emp is a right unit of the heap model, and FQTriple {emp} allocLeast 1 {exists k. k |-> 1} holds. (Lean: `Toy.Sep.triple_of_fqTriple_nonvacuous`).
* **Prior art:**
  * Chargueraud, A., 'Separation Logic for Sequential Programs (Functional Pearl)', Proc. ACM Program. Lang. 4(ICFP), Article 116, 2020, doi:10.1145/3408998 (author PDF https://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf). Definition 5.1: total-correctness Hoare triple HOARE{H} t {Q}. Definition 5.2: {H} t {Q} == forall H', HOARE{H * H'} t {Q * H'}, which 'bakes in the frame rule'. Lemma 5.4 lists the structural rules including frame; Appendix C.1 (author PDF) proves the combined consequence-frame rule (Lemma 5.5) using associativity of * (star-assoc, Lemma 3.9). Section 10 attributes the idea to Birkedal, Torp-Smith and Yang. The paper describes an accompanying course in the style of the Software Foundations series with all statements and proofs formalized in Coq (published as Software Foundations Volume 6, Separation Logic Foundations).
  * Birkedal, L., Torp-Smith, N. & Yang, H., 'Semantics of Separation-Logic Typing and Higher-Order Frame Rules', LICS 2005, pp. 260-269, doi:10.1109/LICS.2005.47; journal version 'Semantics of Separation-Logic Typing and Higher-order Frame Rules for Algol-like Languages', Logical Methods in Computer Science 2(5:1), 2006, doi:10.2168/LMCS-2(5:1)2006, arXiv:cs/0610081. In the journal version (Section 4.1) a triple object [p, q] contains, for each frame p0, the commands satisfying {p * p0} - {q * p0}; invariant extension inv(-, p) adds a frame, and Lemmas 4.4-4.5 use associativity of *. Their base commands are themselves required to satisfy safety monotonicity and the frame property.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Such a logic still yields ordinary triples if its state model has a right unit (instantiate the frame with the unit).

### R6c: `R6c-fq-triples-strictly-stronger-for-nonlocal-commands`

* **Kind / tier:** counterexample, **T1**. An immediate consequence of R3c, recorded because it delimits R6a-R6b.
* **Plain claim:** In the heap model, {emp} allocLeast 1 {0 |-> 1} holds as a plain triple but not as a frame-quantified one, while the frame-quantified triple {emp} allocLeast 1 {exists k. k |-> 1} holds: under frame quantification this specification of the non-local allocLeast survives only without the address.
* **Design question:** What does baking in the frame cost for non-local commands? Specifications that depend on the frame-sensitive behaviour are lost.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened):

```lean
Toy.Sep.allocLeast_triple_and_not_fqTriple :
  Triple (sing Heap.emp) (allocLeast 1) (sing (Heap.pt 0 1)) ∧
    ¬FQTriple (sing Heap.emp) (allocLeast 1) (sing (Heap.pt 0 1))

Toy.Sep.allocLeast_fqTriple_someCell : FQTriple (sing Heap.emp) (allocLeast 1) fun h => ∃ k, h = Heap.pt k 1
```

Unfolded: allocLeast as under R3c; FQTriple as under R6a.

**Hypothesis ledger:**

No hypotheses (empty ledger).

Ledger scope: No hypotheses: both statements are closed statements about the specific command allocLeast 1 in Heap Nat and specific assertions.

* **Depth:** `shallow`.
* **Non-vacuity witness:** Concrete command allocLeast 1 from emp. (Lean: `Toy.Sep.allocLeast_triple_and_not_fqTriple`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).
  * Chargueraud, A., 'Separation Logic for Sequential Programs (Functional Pearl)', Proc. ACM Program. Lang. 4(ICFP), Article 116, 2020, doi:10.1145/3408998 (author PDF https://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf). Definition 5.1: total-correctness Hoare triple HOARE{H} t {Q}. Definition 5.2: {H} t {Q} == forall H', HOARE{H * H'} t {Q * H'}, which 'bakes in the frame rule'. Lemma 5.4 lists the structural rules including frame; Appendix C.1 (author PDF) proves the combined consequence-frame rule (Lemma 5.5) using associativity of * (star-assoc, Lemma 3.9). Section 10 attributes the idea to Birkedal, Torp-Smith and Yang. The paper describes an accompanying course in the style of the Software Foundations series with all statements and proofs formalized in Coq (published as Software Foundations Volume 6, Separation Logic Foundations).

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

In a baked-in-frame logic a non-local allocator such as least-free allocation can only be given address-hiding specifications.

### R7: `R7-scope-boundary-witnesses`

* **Kind / tier:** counterexample, **T1**. Small folklore facts made precise to delimit R1-R4; not claimed novel.
* **Plain claim:** (i) The Hoare conjunction rule holds for every command without precision or cancellativity. (ii) A local heap command can terminate from emp and have no outcome from every non-empty heap. (iii) With empty disjointness every command is local and every assertion precise, with unique frames and the distribution law; without a unit even the always-true assertion can be precise. (iv) Right- and left-handed precision and distribution coincide under symmetric disjointness and commutative union, and can differ without them, even in cancellative structures. (v) A heap command that is safe on emp and faults from some heap is not safety-monotone. (vi) Over the uninhabited value type Empty the only heap is emp, so every heap command is safety-monotone and has the frame property; the non-locality results need an inhabited value type.
* **Design question:** Reference point: which tempting readings of R1-R4 are ruled out.

**Lean statement(s)** (pretty-printed by Lean; namespace `Toy.Sep` opened; `skipOnEmp_local_and_no_outcome_on_nonempty` printed as `name : type` with `set_option pp.analyze true`; entries preceded by a `-- file:lines` citation are quoted verbatim from those source lines):

```lean
Toy.Sep.triple_conj.{u} {S : Type u} {P₁ P₂ Q₁ Q₂ : Assn S} {c : Cmd S} (h₁ : Triple P₁ c Q₁) (h₂ : Triple P₂ c Q₂) :
  Triple (conj P₁ P₂) c (conj Q₁ Q₂)

Toy.Sep.skipOnEmp_local_and_no_outcome_on_nonempty : Local (S := Heap Nat) skipOnEmp ∧
  skipOnEmp (V := Nat) Heap.emp (Outcome.ok Heap.emp) ∧
    ∀ (h : Heap Nat), h ≠ Heap.emp → ∀ (o : Outcome (Heap Nat)), ¬skipOnEmp h o

-- lean/Toy/Sep/Boundaries.lean:76-79
-- source statement, verbatim; instance arguments shown explicitly
theorem emptyDisj_degenerate (c : Cmd Unit) (R : Assn Unit) :
    @SafetyMono Unit emptyDisjSepStruct c ∧ @FrameProp Unit emptyDisjSepStruct c ∧
    @FrameRuleSound Unit emptyDisjSepStruct c ∧ @Precise Unit emptyDisjSepStruct R ∧
    @UniqueFrame Unit emptyDisjSepStruct R ∧ @ConjDistrib Unit emptyDisjSepStruct R

-- lean/Toy/Sep/Boundaries.lean:91-94
-- source statement, verbatim; instance arguments shown explicitly
theorem onePair_true_precise :
    @DisjSymm Nat onePairSepStruct ∧ @UnionComm Nat onePairSepStruct ∧
    @UnionAssoc Nat onePairSepStruct ∧ (¬ ∃ e, @UnitLaw Nat onePairSepStruct e) ∧
    @Precise Nat onePairSepStruct (fun _ => True)

-- lean/Toy/Sep/Boundaries.lean:160-165
-- source statement, verbatim; instance arguments shown explicitly
theorem projLeft_rightCancel_precise_not_conjDistribLeft :
    @RightCancel Nat projLeftSepStruct ∧
    @Precise Nat projLeftSepStruct (sing 0) ∧
    ¬ @ConjDistribLeft Nat projLeftSepStruct (sing 0) ∧
    @PreciseLeft Nat projLeftSepStruct (fun _ => True) ∧
    ¬ @Precise Nat projLeftSepStruct (fun _ => True)

-- lean/Toy/Sep/Boundaries.lean:181-185
-- source statement, verbatim; instance arguments shown explicitly
theorem projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft :
    @LeftCancel Nat projRightSepStruct ∧
    @Precise Nat projRightSepStruct (fun _ => True) ∧
    ¬ @ConjDistrib Nat projRightSepStruct (fun _ => True) ∧
    ¬ @PreciseLeft Nat projRightSepStruct (fun _ => True)

Toy.Sep.precise_iff_preciseLeft_of_disjSymm_of_unionComm.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S)
  (hc : UnionComm S) (R : Assn S) : Precise R ↔ PreciseLeft R

Toy.Sep.conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm.{u} {S : Type u} [SepStruct S] (hs : DisjSymm S)
  (hc : UnionComm S) (R : Assn S) : ConjDistrib R ↔ ConjDistribLeft R

Toy.Sep.not_safetyMono_of_safe_emp_of_faults {V : Type} {c : Cmd (Heap V)} {h : Heap V} (hs : Safe c Heap.emp)
  (hf : c h Outcome.fault) : ¬SafetyMono c

Toy.Sep.heap_empty_all_commands_local (c : Cmd (Heap Empty)) : SafetyMono c ∧ FrameProp c
```

Unfolded: PreciseLeft R and ConjDistribLeft R are the mirror images of Precise R and ConjDistrib R with R on the left of *; skipOnEmp h o := h = emp ∧ o = ok emp.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `h₁ : Triple P₁ c Q₁ (triple_conj)` | Premise of the conjunction rule; supplies safety and the first conjunct of the postcondition. | tight: counterexample `Toy.Sep.triple_conj_premise1_tight` |
| `h₂ : Triple P₂ c Q₂ (triple_conj)` | Premise of the conjunction rule; supplies the second conjunct of the postcondition. | tight: counterexample `Toy.Sep.triple_conj_premise2_tight` |
| `hs : DisjSymm S (orientation equivalences)` | Swaps disjointness facts between the two sides. | tight: counterexample `Toy.Sep.orDisjRight_unionComm_and_not_precise_iff_preciseLeft`, `Toy.Sep.orDisjRight_unionComm_and_not_conjDistrib_iff_conjDistribLeft` |
| `hc : UnionComm S (orientation equivalences)` | Swaps the two sides of a union. | tight: counterexample `Toy.Sep.projLeft_disjSymm_and_not_precise_iff_preciseLeft`, `Toy.Sep.projRight_disjSymm_and_not_conjDistrib_iff_conjDistribLeft` |
| `hs : Safe c Heap.emp (not_safetyMono_of_safe_emp_of_faults)` | Without safety on emp, a command may fault everywhere it is unsafe and still be safety-monotone. | tight: counterexample `Toy.Sep.assertAlloc_faults_and_safetyMono` |
| `hf : c h Outcome.fault (not_safetyMono_of_safe_emp_of_faults)` | Without a faulting run there is nothing to contradict. | tight: counterexample `Toy.Sep.skip_safe_emp_and_safetyMono` |

Ledger scope: The ledger lists the Prop hypotheses of the theorems on this card: h₁ and h₂ of triple_conj (item (i)), hs and hc of the two orientation equivalences precise_iff_preciseLeft_of_disjSymm_of_unionComm and conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm (item (iv)), and hs and hf of not_safetyMono_of_safe_emp_of_faults (item (v)); the binder name hs is used by both of the latter theorems, with different types. The remaining statements (items (ii), (iii), the counterexamples of item (iv), and item (vi)) have no Prop hypotheses; their parameters (a command, an assertion) are universally quantified without conditions.

* **Depth:** `shallow`.
* **Non-vacuity witness:** Items (ii)-(iv) are concrete witnesses; the hypotheses of the orientation equivalences hold in the heap model, and allocAt 0 1 is safe on emp and faults from 0 |-> 2. For triple_conj, both premises hold in the heap model for c = skip with the different preconditions ptAny 0 and {0 |-> 1}, whose conjunction holds of 0 |-> 1 (triple_conj_nonvacuous). (Lean: `Toy.Sep.boundary_witnesses_nonvacuous`, `Toy.Sep.triple_conj_nonvacuous`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (the Frame Rule is sound for both partial and total correctness), in a store-and-heap model. Section 4.1: always choosing the smallest free address for cons would invalidate the Frame Rule (detectable with address arithmetic; without address arithmetic, invariance under location renaming could be used instead of nondeterminism); trapping memory faults would allow branching on whether a cell is active, contradicting Safety Monotonicity; in Petri nets with capacity 1 a transition with pre(t) = {a}, post(t) = {b} is enabled in {a} but not in {a, b} and violates Safety Monotonicity. Section 5.1: a command that faults when more than 3 heap cells are active and skips otherwise violates Safety Monotonicity. Section 5.2, Proposition 2: wp(C) and wlp(C) both satisfy locality for X iff C satisfies Safety and Termination Monotonicity, the Frame Property and a locality property for variables (a joint characterization with a store and termination, not a partial-correctness-only converse).
  * Costanzo, D. & Shao, Z., 'A Case for Behavior-Preserving Actions in Separation Logic', APLAS 2012, LNCS 7705, pp. 332-349, doi:10.1007/978-3-642-35182-2_24 (author PDF https://flint.cs.yale.edu/flint/publications/bpsl.pdf). Section 5.1 (Footprints and Smallest Safe States): under standard locality a specification of a command on its smallest safe states need not be complete (example x := cons(0); free(x)). Section 5.3: the frame rule of relational separation logic is sound for deterministic but not for nondeterministic programs (citing Yang, TCS 2007). Section 5.4 (Finite Memory): a state-growing command that faults when memory is full is safe on the empty state but unsafe on the full state, so it violates Safety Monotonicity; diverging instead requires allowing divergence on any state to keep Termination Monotonicity.
  * O'Hearn, P. W., Yang, H. & Reynolds, J. C., 'Separation and Information Hiding', POPL 2004, pp. 268-280, doi:10.1145/964001.964024: Section 9, Lemma 3: p is precise iff p * - distributes over conjunction, p * (q and r) = (p * q) and (p * r), in the store-and-heap model with p on the left; Theorem 5: the hypothetical frame rule is sound for fixed preconditions (resp. a fixed resource invariant) iff they are precise; Section 10.3, Theorem 11: soundness also holds for 'supported' preconditions or invariants with intuitionistic (closed under heap extension) postconditions. Journal version: ACM TOPLAS 31(3), Article 11, pp. 11:1-11:50, 2009, doi:10.1145/1498926.1498929; in the authors' 2008 preprint of it, Lemma 6 is the Distribution Lemma and Section 9 notes that (q * r) and (q' * r) does not imply (q and q') * r in general, with q = emp, q' = x |-> - and r = true.
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf). Definition 1: a separation algebra is a cancellative partial commutative monoid. Definition 3: p is precise if every state has at most one substate in p. Section 2, Examples of Predicates: the two-cell disjunction l0 |-> rv0 or l1 |-> rv1 is not precise. Lemma 4: every singleton is precise; p is precise iff for all nonempty X, (meet X) * p = meet{x * p | x in X}; the remark after it says injectivity of sigma . (-) is equivalent to that distribution for singleton frames {sigma}. Section 3: a relation satisfies Safety Monotonicity and the Frame Property 'iff the frame rule is sound for it' (stated without proof).

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

The conjunction rule of Hoare logic needs no precision; the precision/distribution results are about framed conjunctions only. Out-of-memory faulting is incompatible with safety monotonicity for a command that is safe on the empty heap.

## Boundaries

### Non-claims (per result)

**R1** (`R1-frame-rule-from-locality`):

* Partial correctness only: nothing about termination or total correctness; the command with no outcomes (diverge) is local and satisfies every triple.
* Does not preserve termination under framing: skipOnEmp terminates normally from emp and has no outcome from any non-empty heap, yet satisfies SafetyMono and FrameProp (Toy.Sep.skipOnEmp_local_and_no_outcome_on_nonempty). A total-correctness frame rule additionally needs termination monotonicity (Yang-O'Hearn 2002, Lemma 1(2)).
* FrameProp maps every run from a framed state back to a run from the unframed state, not conversely: adding a frame can remove nondeterministic outcomes (alloc cannot pick an address that the frame occupies). So a local command's behaviour is not determined by its behaviour on its smallest safe states, and specifications on those states need not be complete (Costanzo-Shao 2012, Section 5.1); frame rules for relational (two-run) specifications of nondeterministic local commands are not covered (Costanzo-Shao 2012, Section 5.3).
* In degenerate separation structures the result says little: with empty disjointness every command satisfies SafetyMono, FrameProp and the frame rule vacuously (Toy.Sep.emptyDisj_degenerate). The statement is informative for structures with enough disjoint pairs, such as the heap model.
* Does not show that locality is preserved by sequencing, nondeterministic choice, or loops (not examined).
* Frames are added on the right of *. For separation structures whose union is not commutative, framing on the left ({R * P} c {R * Q}) is not covered.
* The model has no variable store, so the result says nothing about 'modifies' side conditions on program variables.
* Locality does not make any particular triple true; it only lets true triples be framed.

**R2a** (`R2a-locality-from-frame-rule-at-singletons`):

* Does not apply to logics whose assertion language cannot express exact singleton states {h} and strongest postconditions post c h, such as intuitionistic (affine) logics whose assertions are all upward-closed (h a subheap of h' and P h imply P h'); such logics are not examined.
* Specific to this relational command model with an explicit fault outcome.
* In degenerate separation structures the result says little: with empty disjointness every command satisfies SafetyMono, FrameProp and the frame rule vacuously (Toy.Sep.emptyDisj_degenerate). The statement is informative for structures with enough disjoint pairs, such as the heap model.

**R2b** (`R2b-frame-rule-iff-locality`):

* Not a statement about the syntax or proof rules of any concrete program logic.
* Partial correctness only.
* Does not preserve termination under framing: skipOnEmp terminates normally from emp and has no outcome from any non-empty heap, yet satisfies SafetyMono and FrameProp (Toy.Sep.skipOnEmp_local_and_no_outcome_on_nonempty). A total-correctness frame rule additionally needs termination monotonicity (Yang-O'Hearn 2002, Lemma 1(2)).
* FrameProp maps every run from a framed state back to a run from the unframed state, not conversely: adding a frame can remove nondeterministic outcomes (alloc cannot pick an address that the frame occupies). So a local command's behaviour is not determined by its behaviour on its smallest safe states, and specifications on those states need not be complete (Costanzo-Shao 2012, Section 5.1); frame rules for relational (two-run) specifications of nondeterministic local commands are not covered (Costanzo-Shao 2012, Section 5.3).
* In degenerate separation structures the result says little: with empty disjointness every command satisfies SafetyMono, FrameProp and the frame rule vacuously (Toy.Sep.emptyDisj_degenerate). The statement is informative for structures with enough disjoint pairs, such as the heap model.
* Does not say that non-local commands cannot be specified at all: frame-quantified triples (R6a-R6c) admit them, at the price of stronger per-command obligations.

**R2c** (`R2c-locality-from-frame-rule-for-precise-frames`):

* Shows only that restricting the ordinary sequential frame rule to precise frames admits no additional non-local commands. It does not deny the role of precision in the soundness of the hypothetical frame rule (O'Hearn-Yang-Reynolds 2004, Theorem 5) or of concurrent separation logic with resource invariants and the conjunction rule (Gotsman-Berdine-Cook 2011, Theorem 4.1).
* Does not claim that restricting the frame rule to precise frames is harmless for completeness.
* Precise R, UniqueFrame R and ConjDistrib R place R on the right of *. Without DisjSymm and UnionComm they do not coincide with the left-handed notions used by O'Hearn-Yang-Reynolds and Calcagno-O'Hearn-Yang (r1 . f1 = r2 . f2 -> r1 = r2, and (R * P) and (R * Q) |- R * (P and Q)), even in cancellative structures (Toy.Sep.projLeft_rightCancel_precise_not_conjDistribLeft, Toy.Sep.projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft); with both laws they coincide (Toy.Sep.precise_iff_preciseLeft_of_disjSymm_of_unionComm, Toy.Sep.conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm).
* Without a unit a state need not be a decomposition of itself, so precision can hold for trivial reasons: in onePairSepStruct (symmetric, commutative, associative, no unit) even the always-true assertion is precise (Toy.Sep.onePair_true_precise); with empty disjointness every assertion is precise, has unique frames and distributes (Toy.Sep.emptyDisj_degenerate).

**R3a** (`R3a-allocation-test-violates-frame-property`):

* Not every allocation check is non-local: assertAlloc (fault unless allocated) is local (assertAlloc_safetyMono, assertAlloc_frameProp). A test whose answer is discarded is equivalent to skip (not formalized).
* In formulations where the test traps a fault rather than reading allocation status, the violated property can be safety monotonicity instead (Yang-O'Hearn 2002 Section 4.1); not modelled here.

**R3b** (`R3b-fixed-address-allocation-violates-safety-monotonicity`):

* Does not say fixed-address allocation is unusable: given a precondition that owns the address it behaves as a mutation of an owned cell.
* Only faulting makes fixed-address allocation non-local here. The variant that blocks when the address is taken is local in this partial-correctness model (Toy.Sep.allocAtBlock_safetyMono_and_frameProp), because blocking is modelled exactly like divergence; it would violate termination monotonicity, which this model does not track.
* allocAt k is the capacity-one instance of an allocator that faults when memory is exhausted; any heap command that is safe on emp and faults from some heap violates safety monotonicity (Toy.Sep.not_safetyMono_of_safe_emp_of_faults; Costanzo-Shao 2012, Section 5.4).

**R3c** (`R3c-deterministic-allocation-violates-frame-property`):

* The failing triple mentions a concrete address (0 |-> 1). Whether deterministic allocation becomes admissible in a logic whose assertions are invariant under address renaming (Yang-O'Hearn 2002 Section 4.1), and whether that remedy survives when assertions can retain and compare dangling pointers, is not examined.

**R3d** (`R3d-predictable-allocation-violates-frame-property`):

* Escape hatches are exactly the dropped hypotheses: a command escapes this impossibility only if, for every base heap and address, it is unsafe there, may leave that address unallocated (e.g. nondeterministic choice, as alloc), or has no normal outcome when a frame occupies the address. Blocking rescues a deterministic allocator only in the last way, as detAllocOnEmp does by having no outcome from any non-empty heap. Any deterministic allocator that terminates normally from emp at some address a and also from the one-cell heap a |-> w is covered, whatever it does on larger heaps.
* Modelling memory exhaustion as a fault is not an escape either: a heap command that is safe on emp and faults from some heap violates safety monotonicity, whether or not its address choice is deterministic (Toy.Sep.not_safetyMono_of_safe_emp_of_faults; Costanzo-Shao 2012, Section 5.4).
* The frame property uses exact heap equality and assertions may name addresses. Models that quotient states by address renaming are not covered, and renaming invariance as an alternative remedy (Yang-O'Hearn 2002 Section 4.1) is not examined.
* For pointer-recording allocation the freshness of the chosen address matters: with f _ = r, [r] := det_cons(v) has the frame property (Toy.Sep.detAllocInto_self_frameProp).

**R3e** (`R3e-frame-rule-needs-fault-avoidance`):

* Total-correctness triples that require normal termination exclude faulting runs as well, so they avoid this failure; their frame rule additionally needs termination monotonicity (Yang-O'Hearn 2002, Lemma 1(2) and Theorem 1). Not formalized here.

**R4a** (`R4a-distribution-iff-unique-frame`):

* Does not say that unique frames and precision coincide; they do under cancellativity (R4b, R4c) and are incomparable without it (R4f).
* Binary conjunction only; the infinitary-meet version (Calcagno-O'Hearn-Yang 2007 Lemma 4(2); HOL4 IS_PRECISE___CHARACTERISATION) is not covered.
* P and Q range over all predicates on states. In intuitionistic (affine) logics where assertions are restricted to upward-closed predicates (h a subheap of h' and P h imply P h'), the distribution law can hold for upward-closed frames that are neither precise nor have unique frames over arbitrary predicates; such restricted classes are not examined here (compare the supported/intuitionistic relaxation of precision in O'Hearn-Yang-Reynolds 2004, Section 10.3; intuitionistic assertions are defined in Reynolds 2002, Section 3).
* Precise R, UniqueFrame R and ConjDistrib R place R on the right of *. Without DisjSymm and UnionComm they do not coincide with the left-handed notions used by O'Hearn-Yang-Reynolds and Calcagno-O'Hearn-Yang (r1 . f1 = r2 . f2 -> r1 = r2, and (R * P) and (R * Q) |- R * (P and Q)), even in cancellative structures (Toy.Sep.projLeft_rightCancel_precise_not_conjDistribLeft, Toy.Sep.projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft); with both laws they coincide (Toy.Sep.precise_iff_preciseLeft_of_disjSymm_of_unionComm, Toy.Sep.conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm).
* Without a unit a state need not be a decomposition of itself, so precision can hold for trivial reasons: in onePairSepStruct (symmetric, commutative, associative, no unit) even the always-true assertion is precise (Toy.Sep.onePair_true_precise); with empty disjointness every assertion is precise, has unique frames and distributes (Toy.Sep.emptyDisj_degenerate).
* Neither Precise R nor ConjDistrib R is needed for the ordinary sequential frame rule (R1) or for the Hoare conjunction rule {P1} c {Q1}, {P2} c {Q2} |- {P1 and P2} c {Q1 and Q2}, which holds for every command (Toy.Sep.triple_conj). ConjDistrib R is about pushing a frame R inside a conjunction, (Q1 * R) and (Q2 * R) |- (Q1 and Q2) * R, as needed by the hypothetical frame rule (O'Hearn-Yang-Reynolds 2004, Theorem 5) and by concurrent separation logic with resource invariants and the conjunction rule (Gotsman-Berdine-Cook 2011, Theorem 4.1).

**R4b** (`R4b-precise-implies-distribution-under-right-cancellation`):

* Does not give the converse; that is R4c and uses the other cancellation law.
* P and Q range over all predicates; nothing is claimed about restricted assertion classes.
* Precise R, UniqueFrame R and ConjDistrib R place R on the right of *. Without DisjSymm and UnionComm they do not coincide with the left-handed notions used by O'Hearn-Yang-Reynolds and Calcagno-O'Hearn-Yang (r1 . f1 = r2 . f2 -> r1 = r2, and (R * P) and (R * Q) |- R * (P and Q)), even in cancellative structures (Toy.Sep.projLeft_rightCancel_precise_not_conjDistribLeft, Toy.Sep.projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft); with both laws they coincide (Toy.Sep.precise_iff_preciseLeft_of_disjSymm_of_unionComm, Toy.Sep.conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm).
* Without a unit a state need not be a decomposition of itself, so precision can hold for trivial reasons: in onePairSepStruct (symmetric, commutative, associative, no unit) even the always-true assertion is precise (Toy.Sep.onePair_true_precise); with empty disjointness every assertion is precise, has unique frames and distributes (Toy.Sep.emptyDisj_degenerate).
* Neither Precise R nor ConjDistrib R is needed for the ordinary sequential frame rule (R1) or for the Hoare conjunction rule {P1} c {Q1}, {P2} c {Q2} |- {P1 and P2} c {Q1 and Q2}, which holds for every command (Toy.Sep.triple_conj). ConjDistrib R is about pushing a frame R inside a conjunction, (Q1 * R) and (Q2 * R) |- (Q1 and Q2) * R, as needed by the hypothetical frame rule (O'Hearn-Yang-Reynolds 2004, Theorem 5) and by concurrent separation logic with resource invariants and the conjunction rule (Gotsman-Berdine-Cook 2011, Theorem 4.1).

**R4c** (`R4c-distribution-implies-precise-under-left-cancellation`):

* In commutative structures with symmetric disjointness the two cancellation laws are interderivable (R4g), so the left/right distinction matters only without those laws.
* Precise R, UniqueFrame R and ConjDistrib R place R on the right of *. Without DisjSymm and UnionComm they do not coincide with the left-handed notions used by O'Hearn-Yang-Reynolds and Calcagno-O'Hearn-Yang (r1 . f1 = r2 . f2 -> r1 = r2, and (R * P) and (R * Q) |- R * (P and Q)), even in cancellative structures (Toy.Sep.projLeft_rightCancel_precise_not_conjDistribLeft, Toy.Sep.projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft); with both laws they coincide (Toy.Sep.precise_iff_preciseLeft_of_disjSymm_of_unionComm, Toy.Sep.conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm).
* Without a unit a state need not be a decomposition of itself, so precision can hold for trivial reasons: in onePairSepStruct (symmetric, commutative, associative, no unit) even the always-true assertion is precise (Toy.Sep.onePair_true_precise); with empty disjointness every assertion is precise, has unique frames and distributes (Toy.Sep.emptyDisj_degenerate).
* Neither Precise R nor ConjDistrib R is needed for the ordinary sequential frame rule (R1) or for the Hoare conjunction rule {P1} c {Q1}, {P2} c {Q2} |- {P1 and P2} c {Q1 and Q2}, which holds for every command (Toy.Sep.triple_conj). ConjDistrib R is about pushing a frame R inside a conjunction, (Q1 * R) and (Q2 * R) |- (Q1 and Q2) * R, as needed by the hypothetical frame rule (O'Hearn-Yang-Reynolds 2004, Theorem 5) and by concurrent separation logic with resource invariants and the conjunction rule (Gotsman-Berdine-Cook 2011, Theorem 4.1).

**R4d** (`R4d-heap-precise-iff-distribution`):

* Says nothing about other resource models (permissions, fractional shares, ghost state) where cancellativity may fail; there the two notions can come apart (R4f).
* P and Q range over all predicates on heaps.
* Neither Precise R nor ConjDistrib R is needed for the ordinary sequential frame rule (R1) or for the Hoare conjunction rule {P1} c {Q1}, {P2} c {Q2} |- {P1 and P2} c {Q1 and Q2}, which holds for every command (Toy.Sep.triple_conj). ConjDistrib R is about pushing a frame R inside a conjunction, (Q1 * R) and (Q2 * R) |- (Q1 and Q2) * R, as needed by the hypothetical frame rule (O'Hearn-Yang-Reynolds 2004, Theorem 5) and by concurrent separation logic with resource invariants and the conjunction rule (Gotsman-Berdine-Cook 2011, Theorem 4.1).

**R4e** (`R4e-imprecise-assertions-violate-distribution`):

* Does not show all existential assertions are imprecise: 0 |-> - is precise (ptAny_precise).

**R4f** (`R4f-precision-and-distribution-incomparable-without-cancellativity`):

* Does not identify conditions weaker than cancellativity that suffice, beyond the exact law-free condition of R4a.
* IsSepAlgebra assumes a single global unit and a total, functional union; multi-unit algebras (as in Dockins-Hobor-Appel 2009 and VST), relational joins, and positivity laws are not examined.

**R4g** (`R4g-cancellation-laws-coincide-under-commutativity`):

* A reference point that lets R4b and R4c be combined with a single cancellation law in commutative structures; it informs no design question on its own.
* Each tightness counterexample for hc and hs exhibits one cancellation law without the other, so it also refutes the iff.

**R5** (`R5-standard-heap-commands-local`):

* No variable store; variable-writing commands are modelled by writing heap cells.
* No address arithmetic.
* Locality of compositions of these commands is not examined.
* Models flat single-cell allocation and deallocation with natural-number addresses; does not cover block allocation, free of interior pointers, alignment, or pointer-provenance memory models.

**R6a** (`R6a-fq-triple-frame-rule-from-two-sided-associativity`):

* Does not say that one direction of associativity suffices on its own: the four DisjSymm theorems on this card need the explicit hypothesis hs : DisjSymm S. UnionAssoc alone gives neither UnionAssocRev nor the frame rule (Toy.Sep.oneWayAssoc_unionAssoc_and_fqTriple_frame_fails), and neither does UnionAssoc together with UnionComm (Toy.Sep.commOneWay_unionComm_unionAssoc_and_fqTriple_frame_fails).
* Does not say that frame-quantified specifications are as convenient as plain ones: each primitive's specification must be proved under all frames, which rules out natural plain specifications of non-local commands (R6c).
* Not a statement about any particular weakest-precondition calculus or program logic. The cited baked-in-frame logics differ in detail: Chargueraud's triples are total-correctness, the HOL4 machine-code RUN/SPEC definitions require the postcondition to be reached on every execution sequence, and Birkedal-Torp-Smith-Yang additionally require their base commands to be local.
* Uses demonic, fault-avoiding triples that allow divergence. Frame-quantified weakest preconditions that also demand successor existence (progress), or that are angelic (some run succeeds), are not covered.
* Says nothing about concurrency: frame quantification does not make non-local commands sound under parallel composition (not examined).

**R6b** (`R6b-fq-triple-implies-plain-triple-given-right-unit`):

* A single global right unit is assumed; whether a per-element (multi-unit) condition suffices is not examined.
* The converse fails for non-local commands (R6c); for local commands it is R1.

**R6c** (`R6c-fq-triples-strictly-stronger-for-nonlocal-commands`):

* Does not characterize all frame-quantified specifications of allocLeast; only the two triples named are shown.
* For local commands plain and frame-quantified triples coincide (R1 with R6b); no separate theorem states this.

**R7** (`R7-scope-boundary-witnesses`):

* These witnesses only delimit the main results; they are not design results on their own.

### Attractive stronger conclusions that are not established

* **"R is precise iff R distributes over conjunction" in every separation algebra** —
  *known not to apply*. In the non-cancellative unital partial commutative monoids
  `OrAlg` and `Fork`, `{true}` is precise but does not distribute
  (`orAlg_true_precise_and_not_conjDistrib`) and `{a, b}` distributes but is not precise
  (`forkR_conjDistrib_and_not_precise`). The exact law-free characterization of
  distribution is unique frames (R4a); precision ⇒ distribution needs right
  cancellativity (R4b) and distribution ⇒ precision needs left cancellativity (R4c).
* **"Blocking fixed-address allocation is non-local"** — *known not to apply*:
  `allocAtBlock` is safety-monotone and has the frame property
  (`allocAtBlock_safetyMono_and_frameProp`); only the faulting `allocAt` is non-local
  (R3b). Blocking trades a fault for the absence of an outcome, which partial correctness
  does not see.
* **"Locality is determined by behaviour on the smallest safe states"** — not
  established; adding a frame can remove nondeterministic outcomes (R1 non-claims).
* **"The frame rule for frame-quantified triples holds iff the structure is two-sided
  associative"** — not established: only the sufficiency of `UnionAssoc ∧ UnionAssocRev`
  and the necessity of each direction (with the other kept) are proved (R6a).
* **"One direction of partial associativity suffices for the frame rule of frame-quantified
  triples"** — false without symmetric disjointness: `UnionAssoc` alone, and `UnionAssoc`
  together with `UnionComm`, admit structures in which the frame rule fails
  (`oneWayAssoc_unionAssoc_and_fqTriple_frame_fails`,
  `commOneWay_unionComm_unionAssoc_and_fqTriple_frame_fails`). It holds under the explicit
  hypothesis `hs : DisjSymm S` (R6a).
* **"Frame quantification forces every specification of a non-local command to hide
  addresses"** — not established; R6c proves only the two stated triples for
  `allocLeast 1`.

### Escape hatches (which hypotheses, if dropped or weakened, defeat a negative result)

* **R3d (predictable allocation):** drop predictability (choose among fresh addresses
  nondeterministically: `alloc`, positive control); make the command block whenever a frame
  occupies the address (`detAllocOnEmp`, positive control); make it unsafe at the base heap
  (`faultOrSet0`); or start from a base heap that already occupies the address (`skip`
  from `0 ↦ 1`). For pointer-recording allocation, a non-fresh choice `f _ = r` degenerates
  to the local mutation `[r] := r` (`detAllocInto_self_frameProp`).
* **R3a (allocation test):** the test of the cell it writes (`k = r`) is local
  (`isAllocTest_self_frameProp`).
* **R3b (fixed-address allocation):** blocking instead of faulting restores locality
  (`allocAtBlock`).
* **R3e (fault avoidance):** with fault-avoiding triples the frame rule holds for every
  local command (R1).
* **R4e/R4f (precision versus distribution):** cancellativity restores the implications
  (R4b, R4c); in the heap model they are equivalent (R4d).
* **R6c:** for local commands, plain triples frame (R1), so the gap between plain and
  frame-quantified triples is specific to non-local commands.
* **Degenerate structures:** with empty disjointness every command is local and every
  assertion precise (`emptyDisj_degenerate`); over the uninhabited value type `Empty`
  every heap command is local (`heap_empty_all_commands_local`), so every non-locality
  result needs an inhabited value type.

### Tightness status `unknown` and `harmless`

* No hypothesis in this package has tightness `unknown`.
* One hypothesis is `harmless`: `UnionComm` in the two partial-commutative-monoid corollaries
  `fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc` and
  `unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc` (R6a). It is not needed:
  `DisjSymm` and `UnionAssoc` already imply `UnionAssocRev`
  (`unionAssocRev_of_disjSymm_of_unionAssoc`), so `unionAssocRev_of_disjSymm_of_unionAssoc` and
  `fqTriple_frame_of_disjSymm_of_unionAssoc` prove the same conclusions without it; `projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm`
  exhibits a non-commutative structure with `DisjSymm`, `UnionAssoc` and `UnionAssocRev`.
  The corollaries keep `UnionComm` only so that their hypotheses are exactly the laws of
  `IsSepAlgebra`. (`DisjSymm`, by contrast, is `tight` in these corollaries: see R6a.)
* Setting-level hypotheses ("(setting) …", "(definition) …" entries in the ledgers) are
  properties of the definitions rather than Lean binders; their tightness witnesses
  change the definition (non-fault-avoiding `WeakTriple`, frames restricted to `{emp}`,
  deterministic allocation).

### Disproved or dropped statements

* No frozen statement was found false and none was dropped: every result listed here is
  fully proved.
* Draft formulations that are false and were replaced before the statements were fixed:
  the unconditional "precise iff distributes" law (see above); and a claim that blocking
  fixed-address allocation is non-local (see above). Both are recorded as *known not to
  apply*, with the Lean counterexamples named above.

### Not examined

* Closure of locality under sequencing, nondeterministic choice and loops.
* Relational (non-functional) joins and multi-unit separation algebras (Dockins, Hobor and
  Appel 2009); whether a per-element unit suffices for R6b.
* Infinite heaps, address arithmetic, block-structured memory and pointer provenance.
* Infinitary distribution laws (Calcagno, O'Hearn and Yang 2007, Lemma 4 form).
* Restricted assertion classes (upward-closed / intuitionistic, supported assertions),
  for which R2a and R4a do not apply as stated.
* Total correctness, termination monotonicity, and concurrency.

## Evidence

### Kernel-check record

* Toolchain: `leanprover/lean4:v4.34.1`, tag commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (the tag ref points directly at this
  commit; it is also the commit reported by `lean --version`). No Mathlib, no other
  dependencies.
* `lake build` of `lean/` succeeds with no `sorry` warnings; the sources contain no
  `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or
  `unsafe`.
* `audit/axioms.json` records `Lean.collectAxioms` for every one of the package's
  declarations: each depends only on a subset of `propext`, `Classical.choice`,
  `Quot.sound`.
* `audit/statements.json` records, for every Lean name a card references, the SHA-256 of
  the statement (`toString (repr type)`) and of its definition closure (the sorted,
  newline-joined list of `name : repr type` — plus ` := repr value` for non-theorems —
  over every package constant reachable from the statement; theorem bodies excluded).
  The table below reproduces those values with the axioms of each name.

| Lean name | Used by | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Sep.allocAtBlock_local_and_blocks_when_taken` | R3b result | Quot.sound, propext | `c538b2f0057b1bc5ec0ad647e464bcd822ac45c3ca579d46aad9b82750aed657` | `d95da3026828c09295ea6114aa526c566d5f00cf077f5626f756bc7df0508949` (25) |
| `Toy.Sep.allocAtBlock_safetyMono_and_frameProp` | R3b result | Quot.sound, propext | `72c718e4eceb921063b4d3dbd7d118bb2cbaf92b2d84c866a000c00c713f97c5` | `1e33eef61263bd1ba6fb47a761f032288949c1a7f42003df2425f5a9bf2a028c` (21) |
| `Toy.Sep.allocAt_frameProp` | R3b result | Quot.sound, propext | `392c5213342c933428e1a28b5dafc6c77701da0538749b4b2c7f45a778a7892a` | `e84c5a55029d9f0d5732b18c70613f0d2709c4e6fc57377750fc571904e3ac76` (20) |
| `Toy.Sep.allocAt_frameProp_and_framed_triple_fails` | R1 counterexample; R3b result; R3b non-vacuity | Quot.sound, propext | `0e27bf3cd467f5a202e9769c4d642d3e2807874e6b9f1c4a62cf7832e599bd41` | `86d0592f76eb47902e4d55fc1f526689e0e763f5df4f30be25a53ffa289a3aa4` (27) |
| `Toy.Sep.allocAt_not_safetyMono` | R3b result | Quot.sound, propext | `9f2a827d1e21cc3fc2350f682c6fbb4dd02d3bb8fd2e7470bd8b75977a41dd1b` | `8bdd5006a6820757074f3f296b45f5bfc88dc0a624266c8863a620e8c3a48a20` (20) |
| `Toy.Sep.allocInto_safetyMono_and_frameProp` | R5 result | Quot.sound, propext | `c4194585133d7d4e00215de7c6b655805a8b12ffcb605786ac80d13d42664bf9` | `455624830239317aa5edae4a85f39dc2c633baf0ae6a0981c77f3bcce3f77ea6` (21) |
| `Toy.Sep.allocLeast_fqTriple_someCell` | R6c result | Quot.sound, propext | `7c8fef3c19515f97942e67bf0db6e8260a984396b08c6dc44ea0ab8842f95802` | `d05db3b4023d8c8a7084f30ee22e43e40af55bb026b274674e0560aa0e31a8e3` (27) |
| `Toy.Sep.allocLeast_frame_rule_for_emp_frame_and_not_local` | R2a counterexample; R2b counterexample | Quot.sound, propext | `e774c4f6969698a1a9d5e886bf34bb4c46a8adb012f7bb4f9daf45381f9f7f3c` | `cd51afa2e6570fc2d32ec4c5261d01f73550431abb859fcee6d797db9fe9b942` (27) |
| `Toy.Sep.allocLeast_not_frameProp` | R3c result; R5 counterexample | Quot.sound, propext | `3002bbb1f20c757695e6be087892fcb35d4d4b1fc362470989a9f91617a3349e` | `3df54e801a1d9444975024b498d0a46ba862c10dec54d4f4a33415aa9da518f9` (20) |
| `Toy.Sep.allocLeast_not_safetyMono_and_frameProp` | R2a counterexample; R2c counterexample | Quot.sound, propext | `5a12be6d83e24b33048d12c2130541334f246231c1d82582f922087a9c569207` | `cbf4bb33a91d82503d473646fb366bc439d321466d59e01cfdb36d972cb1d4c7` (21) |
| `Toy.Sep.allocLeast_safetyMono` | R3c result | Quot.sound, propext | `a882f69b0e9543660a61c519d1220a5dd8ac88cb91d220582b094d42613ff0b9` | `5bc3e1e12b3ffb6814116dad9e7f489d09dc64dd9ade05799d21457f4c6fa130` (20) |
| `Toy.Sep.allocLeast_safetyMono_and_framed_triple_fails` | R1 counterexample; R3c result; R3c non-vacuity | Quot.sound, propext | `d97fa7062a3f7835411d56819cc6cc08f817fce1aebc8827fd13772371b90728` | `3690b578591ae30151304352e21bac791f4839619d00e2a9236ad062bd18ab1c` (27) |
| `Toy.Sep.allocLeast_triple_and_not_fqTriple` | R6c result; R6c non-vacuity | Quot.sound, propext | `3953cd7df176f19ed2df17c36987c752ffc5315dbdfe5ce19db9cb2aa07cac5e` | `d05db3b4023d8c8a7084f30ee22e43e40af55bb026b274674e0560aa0e31a8e3` (27) |
| `Toy.Sep.alloc_frameProp` | R3d positive control | Quot.sound, propext | `d306fe8ce0deb66c91589cfd6fc8af693492ca997f5f525169fa72f38f3a1bfc` | `067079fbb0522e0dd4421c6d29fd7f168f0bd6f16afc2dca6e163adb4548be70` (20) |
| `Toy.Sep.alloc_not_alwaysAllocatesAt_and_frameProp` | R3d positive control; R3d counterexample | Quot.sound, propext | `f26995e86b285e17d29123be4d6384c1ce806db0a1ae2f508c7c7cd22a7b3fd5` | `ede51af39220d86d239dfa0bb02215d915a38fbaf6cccfd675ae34d7201fe9c8` (25) |
| `Toy.Sep.alloc_safetyMono_and_frameProp` | R5 result | Quot.sound, propext | `a07cb7abd76b3b4d1a8e5b09c601d95dcc32a27c08e4fd072bc8e5e3712af286` | `b1daa954a4bb900bcf89dd75d457d11a033a3d166243eb9606ed47a135451e84` (21) |
| `Toy.Sep.assertAlloc_faults_and_safetyMono` | R7 counterexample | Quot.sound, propext | `48915b0b04fb60c81fe4d7422079f5c4180266a554b8c92571bfb887941e47c6` | `be002055a4eb5e7dff31e3000026582aefc86e0a5affdffb0e6183125215bc73` (20) |
| `Toy.Sep.assertAlloc_frameProp` | R3a supporting lemma | Quot.sound, propext | `f7ad2f8f7ce7cb18fed889919b62a1c868dbfcffe68d3db8173590c4db7d45e5` | `0a4b4f45f8ed163e04a1882482edc7109fb985a30239c3ee31075c362daca353` (18) |
| `Toy.Sep.assertAlloc_local_and_framed_weakTriple_fails` | R1 counterexample; R2b counterexample; R3e result; R3e non-vacuity | Quot.sound, propext | `d7c3d7f55efb1504de85b4dada7aa697d5d72f49aa641cf9a81e04c0fda3ab7c` | `eb3c4d61c33265bb520824567d69ae9eafa3c2c14dde00a5a3ed0333308a4b4c` (28) |
| `Toy.Sep.assertAlloc_safetyMono` | R3a supporting lemma | Quot.sound, propext | `8c2b44cf0981f9c831fccea431ccb39e63acec06b4c25121f165b535be1bcb56` | `26efe99a40df8efb79ca24f85882d4241ebd01da121812e500a7942c3fc8857c` (18) |
| `Toy.Sep.assocGap_unionAssocRev_and_fqTriple_frame_fails` | R6a counterexample | propext | `5423fddd9faaec6dbf21d8bddd0a3cf63a1ca9b5758771dc30b1165e8522ba18` | `c4b1001ece917a87706a25f9f20ad3b3ebb582d7eed280ee3dff5c0294a36316` (33) |
| `Toy.Sep.boundary_witnesses_nonvacuous` | R7 non-vacuity | Quot.sound, propext | `3c5c1b4e55456fe7571cd6fe30051a5536b09132c9e60ad3f9aa57c4111d2529` | `ad66b1bf41b4e27d9b9e94228e93a1ba0b64bcd6376a69f77c93a594e86c0575` (24) |
| `Toy.Sep.cancel_coincide_nonvacuous` | R4g non-vacuity | Quot.sound, propext | `cc5f78709599914b98ff56d9776fa693d938ba7dcc87707394eeca592b714952` | `ad2c4a1992f47ab80f536af555d583d0fc38dc6668ea67ad45c2f8ce466f669b` (15) |
| `Toy.Sep.commOneWay_unionComm_unionAssoc_and_fqTriple_frame_fails` | R6a counterexample | propext | `da9877e9f285bb37fc62d0dad73de5da25143d7e6962ab5936d9db243f021eb7` | `3f79afdcdfbc110eeb2a2d8f4236183d15e9bc75e86a2424c09a18458e279b8e` (35) |
| `Toy.Sep.conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm` | R7 result | (none) | `2b0ca3b69eb2cf35f7ca29258693eb327c090570921f17dcd1a369d4540b4a68` | `f2da0e5fd98f187d90fc87646cf102d351eaa03a19f2adebd0d30e3880d465e5` (11) |
| `Toy.Sep.conjDistrib_iff_uniqueFrame` | R4a result | (none) | `5db0e0c99a8a250990737714be1fbdb66e5463e78352e06dbae960279cec4a3f` | `bbdb43fdf00c58f4d2d58127c3d73ef81bb3dfe38a1d20389b2c2e955b9a4609` (9) |
| `Toy.Sep.conjDistrib_iff_uniqueFrame_nonvacuous` | R4a non-vacuity | Quot.sound, propext | `470bb9a012787e682dd54e4b96e74db9daa6ce798aaa271d5dfb0f1083e17599` | `551e3627b4db5689d6642e6009bffcca8982f8ae5a88ffa7825cce6187939be1` (40) |
| `Toy.Sep.conjDistrib_of_precise_of_rightCancel` | R4b result | (none) | `6b489745e544c10f88170a64c37741e2be4e833761b92b594a648e5f90a4acdc` | `663946dfb69e5c5d031b01b5bcbdd85e68c680bd49024ad196e60a013fde2125` (10) |
| `Toy.Sep.conjDistrib_of_precise_of_rightCancel_nonvacuous` | R4b non-vacuity | Quot.sound, propext | `0211ca4b6af1d8454482a472bc68c49b5115a1eb08d0665fa2327bec77176bc7` | `bb09c733cab71f9aca224b811bfaf3aa5f1c8c4dc31d8e174487a2ef2dbd0a5f` (20) |
| `Toy.Sep.detAllocInto_fresh_nonvacuous` | R3d non-vacuity | Quot.sound, propext | `fb9fb5f326b3bb657435fb8b80ecdaaddeb7b43f3e8f704a163bb845f87a2248` | `450ed4bb3351a89b5df6fa286602dbf73d5db1e98a984710caf1686a5edc1da2` (30) |
| `Toy.Sep.detAllocInto_not_frameProp_of_fresh` | R3d result | Quot.sound, propext | `d8847a75eb9dfa53006a18d42198009ee807668c9d38bdcd9814403839e5d710` | `8f9caeb8066d2ae7eafb703d50d8f1b488b717fa70d96ccb04f33b3ad165edb7` (20) |
| `Toy.Sep.detAllocInto_self_frameProp` | R3d counterexample | Quot.sound, propext | `68aeef814a18f6ed8bf2e795ab3aef01d4183cd343f29d54f7d3d8a763fb8579` | `8f9caeb8066d2ae7eafb703d50d8f1b488b717fa70d96ccb04f33b3ad165edb7` (20) |
| `Toy.Sep.detAllocOnEmp_frameProp` | R3d positive control | Quot.sound, propext | `8c08c39334d9d229607f016dd32278bcce08d85147d31963397c974c844015dc` | `5cc5309e25044a46d6acd5ffec7cba286bf36f1d8ed83b88ea1b6d737b209e95` (23) |
| `Toy.Sep.detAllocOnEmp_not_runsWhenOccupied_and_frameProp` | R3d positive control; R3d counterexample | Quot.sound, propext | `f4fac943c1909f307f7f21414f30a50bc3ba9310e4f515229c142ad6c44982e4` | `24dff6a442ec04e7dac6adebc42ef738ca8202871e8f1648bc866f5d21d4f805` (25) |
| `Toy.Sep.detAlloc_not_frameProp` | R3d result; R5 counterexample | Quot.sound, propext | `ebbdc28711122ce7f4e773fcde151d47d425de952c707f61dd3733cc4d66e1c5` | `ebac220e92f006a6e5416b68ffe738c26ff0e491678467577f3fdd3907dff6d9` (20) |
| `Toy.Sep.emptyDisj_degenerate` | R7 result | (none) | `295ea69e3084800f8ab70b19fafdac3f61c8e59ee90a31e4afeaab381a7a0912` | `27413b914d4d9956abc5fd918d33a58989bac91cc4841f5df671037ff0f34211` (20) |
| `Toy.Sep.emptyDisj_disjSymm_unionComm_no_unit_and_fqTriple_adequacy_fails` | R6b counterexample | (none) | `d81a21475af8f6e2c6033f282116f2a356ebe7762d75e268e886470072a7870c` | `3df9ac3098d824b7256b45038b26a96b8324c69dc96f0a9cb118856d81276585` (18) |
| `Toy.Sep.emptyDisj_no_rightUnit_and_fqTriple_adequacy_fails` | R6b counterexample | (none) | `781f14805722baa6321ed099b908329d8762da28c292b64b72dde61a9b37a300` | `e8ab768d5510d1117bae46230aa7368a372bc86485a80d8276079df3d69a18eb` (22) |
| `Toy.Sep.faultOrSet0_not_safe_and_frameProp` | R3d counterexample | Quot.sound, propext | `8a9e8554a283016de74411d0c9612144f30207f7439e22a1b0d070e4005ab5c5` | `6e641aaf3bc0a86f1f4f8af043b29779c6342e302f42b7903d803cb5af7ab896` (25) |
| `Toy.Sep.forkR_conjDistrib_and_not_precise` | R4c counterexample; R4f result | propext | `4d5dab67bb09f4f0a00ee47cc76c9e9691ac5fd2c05c2e9ecdd36a0196dc736a` | `a7c7f482ddc91e31b21eec41b7801a0cc8f28ad8603903ccee6f016765dd7787` (27) |
| `Toy.Sep.fork_isSepAlgebra` | R4f result; R4f non-vacuity | propext | `d8e10f7ee4360a6c604c011722a04e4fd305e19aa755c84be8d24a546207f39c` | `cad91c96ddadae7712f8e4f9fecf71bb2cfd49add1ad61962b939529bce0bbec` (27) |
| `Toy.Sep.fork_not_leftCancel` | R4f result | propext | `697c050c93e6bf7ca30be716ef77a770eee389b13c2cabc52487cd6780567bae` | `157290ae611f713fcb295f3a98fb9c0d82d9881f2cf9cf51e8ab034c8aa3485c` (22) |
| `Toy.Sep.fork_not_rightCancel` | R4f result | propext | `f2d8133b12d89353af809ae8b6e596bf7e97e8c2426d288b33546d7aa4a61248` | `af546f33f41b9275cc90d78b2ce3b8024f2f53f7e882d92f102abcf1a31c4258` (22) |
| `Toy.Sep.fqTriple_frame_nonvacuous` | R6a non-vacuity | Quot.sound, propext | `5b872960cacf2ffcebac46a594718f1ad4cbc9484207c5be5a4d95e91a1a4e30` | `10362ce89f183c84b7a5cf4f0cd945335433f14ebe95cceb763077e00b0f6bd3` (29) |
| `Toy.Sep.fqTriple_frame_of_disjSymm_of_unionAssoc` | R6a result | (none) | `0b72b10d5768a8d6d36a6c9e24717120cd30a69aad0c8a94e3f9197238ffd04f` | `eeb81a1962d51de2144c0fee0d405edd43e52fd21fb73988b03ee5cab758063c` (15) |
| `Toy.Sep.fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc` | R6a result | (none) | `cd4f41dbafa0e2bc74ad7e437815bc6ab845c45203301d096eba08bcfa4bd4a3` | `8ce716db451c2b7c0d9f0becf758c72e583e1b0052cc06f79f5a9c253e4d2f5b` (16) |
| `Toy.Sep.fqTriple_frame_of_unionAssoc_of_unionAssocRev` | R6a result | (none) | `edaa8fc7eceecad54fb08fc2d8ecbb9880c694d693e57e652484e2dc4d57252b` | `7900e1e3cf15e7d7fd6d24804922d6e102f76f02bbf266e7c38e3fd315cdd3c4` (15) |
| `Toy.Sep.fqTriple_frame_premise_tight` | R6a counterexample | Quot.sound, propext | `7832ba26f3934a4ceb9baa98f5461c2a14aa1dc15ff2a3a920b1d639487c38dc` | `7211dd1d33abb4e26187a2d40b7a75c37cba4e32e4f28c58529a5aa16e43f49b` (23) |
| `Toy.Sep.frameRuleAtSingletons_assertAlloc` | R2a non-vacuity | Quot.sound, propext | `4bc9c5ce7966ced5b24762aaf32adfe080b0fa3386d64ebaeefeea1d3c50433f` | `0a42da1e5896a776d1f27b7b17a64b7250b7937ff29388d435d039b092372536` (23) |
| `Toy.Sep.frameRuleForPreciseFrames_nonvacuous` | R2c non-vacuity | Quot.sound, propext | `65fd8a39bae896ca8952b977efb00bbbf06d1a4d77e8d8ea5633fa2b353e3418` | `3430da693e9588add78b5f075b3804781bf837695b2203903df0145b8dfd355b` (22) |
| `Toy.Sep.frameRuleSound_iff_nonvacuous` | R2b non-vacuity | Quot.sound, propext | `900f0de7b4c6d601597792e13ea8ecca173890f39c5c563ecf5b84b9cdeca3c4` | `15e68c730b772303b84e9097e3d86b46f8c0b019fec22926a8687d2bc6dffd97` (26) |
| `Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp` | R2b result | (none) | `38969d02d13443265550d5689bd83078142815827f9384b9a01f52e28753ed68` | `4bc629ac29e5a9f979db709d08bc2e1b6aabe01850149114ecd7eff5cc006f6a` (15) |
| `Toy.Sep.frame_rule_of_safetyMono_of_frameProp` | R1 result | (none) | `0a0b266b98f17615a883b2efcdfb8356ca4a48d334dcdc6475db40d2080a4b40` | `3dec551a26686da6a915bb134b4fe39c506e3b00b21b8c4f35b4c888ef7b4e8d` (14) |
| `Toy.Sep.frame_rule_of_safetyMono_of_frameProp_nonvacuous` | R1 non-vacuity | Quot.sound, propext | `1aa81bb68ae870f49e8710e777d4c077c9227402e9eab2df0780dbd8d6039faa` | `f653e23b5eb99bae000a239c7f110e6aa77d8e10eaf2c7500e9e2d8b2184f537` (27) |
| `Toy.Sep.free_safetyMono_and_frameProp` | R5 result | Quot.sound, propext | `b1ed19c9391161b209c66fa2119c5c2cf7c518d0d44915cd273abcc854de159a` | `d9b02d54a5214178da5a8468dfc2b63debb2f3095eec2b9ed84f1ecdfb7c48ae` (21) |
| `Toy.Sep.heap_commands_framed_runs_nonvacuous` | R5 non-vacuity | Quot.sound, propext | `2b28d36459b9400b413e317c7f39927f3a44bccfe06ec4d07cfc3071482f1cdf` | `b94a7509c4bdd112dfda5426ebec27d94423e4929be00a68a3ffe0d3b944046e` (26) |
| `Toy.Sep.heap_empty_all_commands_local` | R7 result | Quot.sound, propext | `9fc2fa1c2162de6c0317ea72db3db63ea0202160a1fcd1d1baf04f27aef17e94` | `f6b11eaa5e816c4e936c9caaebf7d849e7669199d9d78f9808ae03787d4115a5` (18) |
| `Toy.Sep.heap_fqTriple_frame` | R6a result | Quot.sound, propext | `3458e8cea17131add57ef756a1e7c98e9015251b7a0d502933516cb1595af546` | `6db8d588629a4c52f5508151c069d456b1381c8e13c8b0ef183bc6aff133e4c9` (20) |
| `Toy.Sep.heap_leftCancel` | R4d supporting lemma | Quot.sound, propext | `7f41e410e3cd8a824ef2fcab3b27af9959ce9fdf7bb5ab9b319aa40aaaf49534` | `494108b04ac35ad679509de0c8878f995e1ca0354d74cda682d7801669fb89d2` (12) |
| `Toy.Sep.heap_leftCancel_and_oneCell_not_precise` | R4c counterexample | Quot.sound, propext | `dac79bdc5c2cf22450bb72f336b0f49e3f6de4b43a93fe9b91bf1f3c598808bc` | `440a8693666475f4313c8e7aa5364b771055887d6fa5e5259edfdb84571f303d` (20) |
| `Toy.Sep.heap_precise_iff_atMostOneSubheap` | R4d result | Quot.sound, propext | `705e04583a1bdef576548b7d3bf02e77144b1bc5ce29ccd5dd48b85140211cdb` | `0ab62c715f1e736064e60f36575b213cdf571f91a112c1fd6bc125087284470c` (14) |
| `Toy.Sep.heap_precise_iff_conjDistrib` | R4d result | Quot.sound, propext | `d72cd50559850aca61de0082db27c43ec93477ede3303b0f0f0f581cfdeeaf5a` | `07090ad7a72958af5f4a22b5f8ce18382a1428b2efb1db6604cc72be879e3dbb` (16) |
| `Toy.Sep.heap_precise_iff_conjDistrib_nonvacuous` | R4d non-vacuity | Quot.sound, propext | `f3ca0a7b469052c7e5e6cf83bf4c7e132bbf42f7a19f6fea0ac8c1799bcd760a` | `90bf5c680e53f545ae130a65afc51cb307324270e44845d3549b3b3c781ec16e` (23) |
| `Toy.Sep.heap_rightCancel` | R4d supporting lemma | Quot.sound, propext | `f1017ce72668b643611aa8493ddf03a9d315a3648f1111afb9011f7e00f3cf3f` | `f6f4e74c8646bc8a32f05cdc5b4cbf732fcae0113baaa77c71eeca075b37f466` (12) |
| `Toy.Sep.heap_rightCancel_and_oneCell_not_conjDistrib` | R4b counterexample | Quot.sound, propext | `7f020d2ee40124e5b273d37865333f8ad214554829ba9a60436ceb1452064fd2` | `b78dbaec58fef8ef8c2c678756453e87231180c40d9e3e266d46575b8a3fee3f` (22) |
| `Toy.Sep.heap_triple_of_fqTriple` | R6b result | Quot.sound, propext | `7cf71c03f9029fd3a7356e0ff317a25a1d63836137ac2a0f023e31be2c4508b5` | `6db8d588629a4c52f5508151c069d456b1381c8e13c8b0ef183bc6aff133e4c9` (20) |
| `Toy.Sep.isAllocTest_not_frameProp` | R3a result | Quot.sound, propext | `6e784fde18ddfaaf8cdfdcea257f2fd9e99c1f3a8926a1b52a94d358f0749e45` | `8a3225f2b4fe5aa32f6b13c296f16484b8259d5350397b89057d2fc53732999b` (20) |
| `Toy.Sep.isAllocTest_safetyMono` | R3a result | Quot.sound, propext | `c465a2891044c14a6c3b3716e2453086969ba90132699014096aef07f6d82fcd` | `0b5b273c814a02307f0bbd147529eaae0a568aa68c5077149e5fa5a8d5c6f318` (20) |
| `Toy.Sep.isAllocTest_safetyMono_and_framed_triple_fails` | R1 counterexample; R3a result; R3a non-vacuity | Quot.sound, propext | `ec3c452f82628b98357ff93eaa5a7f50e8ddfaf480978dee65f29a87f922b0ac` | `abca9ff9b8e0a813f2c3546cd5d5925aa72239e49d6c4ed5964940af976553c9` (27) |
| `Toy.Sep.isAllocTest_self_frameProp` | R3a counterexample | Quot.sound, propext | `0708689e9df29b5c9248aac45341366c1490248674db9f3f4df3e05540b0f820` | `8a3225f2b4fe5aa32f6b13c296f16484b8259d5350397b89057d2fc53732999b` (20) |
| `Toy.Sep.leftCancel_iff_rightCancel_of_disjSymm_of_unionComm` | R4g result | (none) | `ab76b74e015cbaf4d91a7aa704a941f93bed0e7405336a9cd5addd073843b458` | `5a57cf0a509c8c4cdd88f1f0655a0d505bee5928b8638b17562bb6f1c19b25d6` (8) |
| `Toy.Sep.leftCancel_of_disjSymm_of_unionComm_of_rightCancel` | R4g result | (none) | `2410df5a3beb3142ccead3d9d7473b91e1471e37cb8f55f582391058ae2f57f9` | `5a57cf0a509c8c4cdd88f1f0655a0d505bee5928b8638b17562bb6f1c19b25d6` (8) |
| `Toy.Sep.leftDisjCommUnit_unionComm_unitLaw_and_fqTriple_adequacy_fails` | R6b counterexample | (none) | `8ae282ce8e1af27e949865fdd59c17dc0ba9546d4fcd335404fefde76c939e2b` | `ab791c498f0630cce0ab1cc863684c0f6fee0f7cc6b090a6305399512c999d67` (18) |
| `Toy.Sep.lookup_safetyMono_and_frameProp` | R5 result | Quot.sound, propext | `fc47c0523b64688213c19d330e9ee724121fa6f3aafccc00a27664149abcc555` | `fcb056ad8bf84c1a247a67d9ae6c582b967ba69c530b70553ed65f195f0e7629` (21) |
| `Toy.Sep.mutate_safetyMono_and_frameProp` | R5 result | Quot.sound, propext | `9df3dac8658bde32d823155071e3c7f727975ae743c802695d94f64af0d30feb` | `6f7a087167c5239b4feeb7b3e7a5a26e99a241715c252a3431ad58e121727ece` (21) |
| `Toy.Sep.not_frameProp_of_alwaysAllocatesAt_nonvacuous` | R3d non-vacuity | Quot.sound, propext | `cf5099865881e32232e6f87e6ffe3366a37f48539e0cd48b79764d74b32ab8cf` | `ee2ee555fdaf79b2d4459f63ac20a31718552938c595c027a2eebcb9df5d1002` (23) |
| `Toy.Sep.not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied` | R3d result | Quot.sound, propext | `3859e11aa15b4dace3a2c054b0d77c46a3046a3092570c65c1a5571067f48b0f` | `b33ab8efce61baffe1de27eb005f257acdbadf546f71ac6cdca44531908f92e9` (24) |
| `Toy.Sep.not_safetyMono_of_safe_emp_of_faults` | R7 result | Quot.sound, propext | `809b15d0ffe4964ef4d9a9868482961a10171811329f47c037ee18e454d061e2` | `1bcec9ffb619086bfadca072dcf049b4a3743a7e9a3e47435513eb90fffa5f59` (19) |
| `Toy.Sep.oneCell_conjDistrib_fails` | R4e result; R4e non-vacuity | Quot.sound, propext | `4b6e6222ff12b3c6b45d28ae05eee2b04c08b867195d734b94c52e321c042a24` | `fb986b7656850a050185f0c5401a791b6c5b43c664a56db60a72f4ee6fb2ff38` (21) |
| `Toy.Sep.oneCell_not_precise` | R4e result | Quot.sound, propext | `c7327a7458ad8409b60ded4fffb364b6d1e944aa5cf76a3f634bf67679f40853` | `18b672e3319dc0413fcfd760bead0256fc143ebe5c81a20e005953900a149b35` (19) |
| `Toy.Sep.onePair_true_precise` | R7 result | Classical.choice, Quot.sound, propext | `084d4c84a2212a5e6340eceb88242090344d19f4483b517d5db6d788f8d3417b` | `a62359bcfe643341511ff2f5d9e02db6349e70fc31e7c0bbd98c5c2840fd03c1` (11) |
| `Toy.Sep.oneWayAssoc_unionAssoc_and_fqTriple_frame_fails` | R6a counterexample | propext | `581f5eb149ded117da55747f5ac98c8bc3aea96aa64037dba81afe933ce42722` | `6669d0fc178ff4ec28767cd7a955e294afd9927bf2a9e3699e8497acf97285e0` (33) |
| `Toy.Sep.orAlg_disjSymm_unionComm_not_leftCancel` | R4g counterexample | (none) | `8dc219ede415768dc548f5b818f3cb149dd3a61a0f478169d9ed645911aaa32e` | `26c552e0f7b49070e889c66830dadcba21a698131c5c36391edc7c904720d00b` (11) |
| `Toy.Sep.orAlg_disjSymm_unionComm_not_rightCancel` | R4g counterexample | (none) | `c9794b46999a3d628437b46339829812cc90a4c26807b722695c8e11b5c45610` | `42109137e7b3d25c64120fdb6812e66f541934eac0364eb3c53e356d4bbb7b7b` (11) |
| `Toy.Sep.orAlg_isSepAlgebra` | R4f result; R4f non-vacuity | (none) | `199767e375b79cc758506b1310c914456b032e797c0c0c3f69dacfb6fee0d84b` | `3f5018379d79a57f9d1868e01a66cc7e87b4848fcdd7c744f21315b4fbf8f96c` (15) |
| `Toy.Sep.orAlg_not_leftCancel` | R4f result | (none) | `ecf43323b3f3a4856dbbd3da72f48abe91539aa2a69ce82eb24a012407f500ee` | `26c2057b1e7059c00e98ce2c7596126618938ad87b5ef89325a198f80fe8b08d` (9) |
| `Toy.Sep.orAlg_not_rightCancel` | R4f result | (none) | `9ef41c5b102ea2147d387a79e86fa32342367077d53ccfd4915b8036ea3bd215` | `28ab02beb7422861b7b17364656e3246e7847e0fe8c56368d1fc86fea5436256` (9) |
| `Toy.Sep.orAlg_true_precise_and_not_conjDistrib` | R4b counterexample; R4f result | (none) | `5d1a7033e0336bfafc1c7f3a066c5b1d71550d1d1bd15254443b70705082f489` | `070ea54005fb17824340932da4738bd62f210e23fa500d5cb91e377274b82c53` (14) |
| `Toy.Sep.orDisjLeft_unionComm_rightCancel_not_leftCancel` | R4g counterexample | (none) | `2b5e04cdd4ee72c5a577074abc895028acd06538a4e3eced37fdef551a8ae7ea` | `4fa8aebcda39c835fbdde0bd3ec3cedc2cf58021374dca7b94ee4840f3901f8e` (8) |
| `Toy.Sep.orDisjRight_unionComm_and_not_conjDistrib_iff_conjDistribLeft` | R7 counterexample | (none) | `1ffb78509ad19a1300fbd3e1132c2f0763ac1f7141a841c9e62b528ef6ebc70a` | `4247f89e1a9dba1d9f2bd96eb3b5d569e44e0c9240d5dfea5a923c55f059ef04` (11) |
| `Toy.Sep.orDisjRight_unionComm_and_not_precise_iff_preciseLeft` | R7 counterexample | (none) | `b9ae4078e80301704e7c58f2c7719b8b36e46bb6684c78e240269bfe23f6372f` | `4511071275f3291b214714aa69263602be579f975a0ce19cfb9a33d0819e547f` (9) |
| `Toy.Sep.orDisjRight_unionComm_leftCancel_not_rightCancel` | R4g counterexample | (none) | `1595e86402cfc0735651d1a1f0d216d2626c3602b50cdae4263d339bc9e657bd` | `73b842ed81bb11f497cc87e38b98108eb0758ba0a776ab58703b759ebcda239e` (8) |
| `Toy.Sep.precise_iff_preciseLeft_of_disjSymm_of_unionComm` | R7 result | (none) | `18782e03399bc0a5d6e11bc97e2c441ed5828ff06220f580c59daa63c9c558c7` | `1f3ff0355bc127dec21d3bdd0f2c0b98ce22c86191e7e1425078d31a4ae59fa5` (9) |
| `Toy.Sep.precise_of_conjDistrib_of_leftCancel` | R4c result | (none) | `57e1f68d651aac47e23ec2d5496d478a4ec28850c4d9f4f0cecd084bf851a48f` | `f755ea8eaf5c23ebf2d512f480982be6dcaf292e69ca9c95a39f685d704d7aa3` (10) |
| `Toy.Sep.precise_of_conjDistrib_of_leftCancel_nonvacuous` | R4c non-vacuity | Quot.sound, propext | `e49be8a85c10c98924f975fbf25290f5bdbf8829a8e1b8414266b360044b7717` | `01302872a994d9b00b0907f659f7e484af904704f59ad4e71ef0419c9e061e1a` (22) |
| `Toy.Sep.projLeft_disjSymm_and_not_precise_iff_preciseLeft` | R7 counterexample | (none) | `0ba62f74119d9f4b8d88ffddd914f1203da44a034ea1f9903919a9a0a8022d03` | `89224bc2485a022f1f41fd6e0e2185ef6b7c54bc72fbee8188867af736541188` (9) |
| `Toy.Sep.projLeft_disjSymm_rightCancel_not_leftCancel` | R4g counterexample | (none) | `267ce2066af63a008585d2ba647c38f292845f75a21cedc41ab1cb7aa606afa2` | `608b6684a31d372a1ae37e13981498daf9ae924c6a99b085c79a1188c9bf75fa` (8) |
| `Toy.Sep.projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm` | R6a supporting lemma | (none) | `6a9139ec55bf25ad533f42c419c55f38fc30e2aceb10c1e36d4688520f25860f` | `7aca34843c87ec629bc322c36babc14260f8c4c2dd4de0988975f258c4c1fe84` (9) |
| `Toy.Sep.projLeft_rightCancel_precise_not_conjDistribLeft` | R7 result | (none) | `6866e8610d32033d7b7b1dfd5894cf79e723444e04f45feb92039a3a96165ef2` | `1461226aecd7591b85996c02ec36fa7c495c0ea3f0cea7cef1667ed1b70bceb1` (13) |
| `Toy.Sep.projRight_disjSymm_and_not_conjDistrib_iff_conjDistribLeft` | R7 counterexample | (none) | `c464fd86396bc08d257602c98ba926c906e3cf7c8aa9dbae2c775d38868f9672` | `24a3bf9113e2b08d71b52c977b2ca242279f8f872a7e1ccf28e290c97e49d0c1` (11) |
| `Toy.Sep.projRight_disjSymm_leftCancel_not_rightCancel` | R4g counterexample | (none) | `e3b4e8290990d1a7ab56cbb795c84eef142498fcb1bc5e5562febc13d8c7fa1f` | `1d77d5a3452770069d44ec4ebfaea218bc88268cb2ee592473eb001787406854` (8) |
| `Toy.Sep.projRight_disjSymm_unitLaw_and_fqTriple_adequacy_fails` | R6b counterexample | (none) | `93f2bb7e8f2eeb2d835f9b18e9b6d19d89cbd01175fa13b33ec33ee2e8222544` | `27246e978ef6b04b54d7d5c2ec2fefd03b75aaa1be03e3770a350793f3b73963` (18) |
| `Toy.Sep.projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft` | R7 result | (none) | `c8cc36bb32dd04b3a1c009fc16a486b642199708e46d74e3e1811b5de1b0b374` | `7ff892a6355d78817f93fdf5a0f0a51bf216a600dd76aad46113a83aa01554ee` (12) |
| `Toy.Sep.ptAny_precise` | R4e supporting lemma | Quot.sound, propext | `23826d227e3a5512d9eb75698beec11fe909af97945acd6f68048d59f9cceb7a` | `a3b7d400afa934d9fbf4deaf742129e58aff2de1529b46924bbc014326c88221` (19) |
| `Toy.Sep.rightCancel_of_disjSymm_of_unionComm_of_leftCancel` | R4g result | (none) | `f228e82dc0bde832ca585a4d0fc6cd36b8720834a5722fc36a69ce25d9873b41` | `5a57cf0a509c8c4cdd88f1f0655a0d505bee5928b8638b17562bb6f1c19b25d6` (8) |
| `Toy.Sep.rightUnitLaw_of_disjSymm_of_unionComm_of_unitLaw` | R6b result | (none) | `41c02d0c98c1fe13babd96f0acd7d1c7ad4c3c37fccae4e1cbd328325de31d68` | `ed64bb2b12f9c5518b32301d3020333bb07d5cda4b3cec4b1ed972b327fe71df` (8) |
| `Toy.Sep.safetyMono_and_frameProp_of_frameRuleAtSingletons` | R2a result | (none) | `4c14221360ab0647450bd0486b74970628807faeca96862c4e3dbfa75ad4dc32` | `c6aa825a942045a3c42bd0c1961e01829eed1a30d925d9129e5f54d0db3dfd7e` (17) |
| `Toy.Sep.safetyMono_and_frameProp_of_frameRuleForPreciseFrames` | R2c result | (none) | `9ecc76ea031a9e250b06a486f735e7432cb5ac66daac7f881d2d287c6f4cc9d2` | `dbd6ba7f4fc9f097f652316ead845c14e10c9b749739d6bfa10be7961db831e2` (16) |
| `Toy.Sep.skipOnEmp_local_and_no_outcome_on_nonempty` | R7 result | Quot.sound, propext | `582e462d2d2d6dfd12770a4a29e2ae81fd1dab722cf60a93aa81dd37a44a25f1` | `f8339c26eaf5211d92e6d9ff6ecd81384efa01562c53e3004e01e2994978cb4f` (22) |
| `Toy.Sep.skip_local_and_framed_triple_fails` | R1 counterexample | Quot.sound, propext | `73879b66ee7c9846cc5e905a1d9abc5d1aab7e83d8b6a00f4a82a475288bea0d` | `836f31887dcbae5e5b7a37b4e75956ebec5d1ae3827e47cb7bd65c147af315f7` (22) |
| `Toy.Sep.skip_occupied_base_and_frameProp` | R3d counterexample | Quot.sound, propext | `6d2331b8a3ca5cd5420d3356f9a68daf578ab78bf0408efc4553d2ecd6669bd6` | `5f9673dc125e57c4dad2e12ae7e3664a7b928369658b8096cf14cb31279b4282` (25) |
| `Toy.Sep.skip_safe_emp_and_safetyMono` | R7 counterexample | Quot.sound, propext | `bc85dd7134dd68f051bed02ef3825878d34a695e6b6704c0620c3e9f88e0559f` | `78d6160d38af727b602631e9edf924f689fc139b348b9f30460315202ddca6de` (20) |
| `Toy.Sep.someCellAllocated_conjDistrib_fails` | R4e result | Quot.sound, propext | `2ea092d88aaa40208b7a9d2df4d767e261be688c4d47918499dec5a922ddd088` | `55150d59cafa73dfe47d18c11902b26cc5284cb1e2833b3e90d16f7d4ce7f3c6` (21) |
| `Toy.Sep.someCellAllocated_not_precise` | R4e result | Quot.sound, propext | `55f03d706d9973a05163cf931eb44311583e2470ea0ffac5ba04c796ce8b856b` | `946b79a05ca67cabe38d30e4d2d5d97f6422404512c7a99eca46b72c75946e23` (14) |
| `Toy.Sep.symmAssocGap_disjSymm_unionComm_and_fqTriple_frame_fails` | R6a counterexample | propext | `185f28876982e2334f72e0fcba37742c2f72a946b5fad988113628215ea6cfcb` | `955b3a50e0493b3de1623375379e28125fdaf21dc1511ff84b51485d136dff85` (37) |
| `Toy.Sep.triple_conj` | R7 result | (none) | `c73f32509be451c29fad7139205c099a50acdfaf3151542a5efb6254d3bc3296` | `b9f46977c13a394c4ff5e5dccc061acfed0687c2840bc963caa3313933fe8a42` (8) |
| `Toy.Sep.triple_conj_nonvacuous` | R7 non-vacuity | Quot.sound, propext | `f8564cf727d4a2c7ccddd1f5b94dc8b095c74409cc0fbc8f8d7dc00bef7d0961` | `2c7f3d97cb5a26b158dbf01c415d3e43c0a6c9e61370af8436ca9e0548e17f09` (19) |
| `Toy.Sep.triple_conj_premise1_tight` | R7 counterexample | (none) | `df927be04ef1b88f33e323246b7b0b8f4628a97bbf1f542483d462643e057f2f` | `c59d54b2767c3ef47ac7eb1dfbdb1d92c1e2b3560aa3f2b0c00da89705e3f9b3` (9) |
| `Toy.Sep.triple_conj_premise2_tight` | R7 counterexample | (none) | `f00c332687849eb6b800540abd626fc5409893b25b89d75882075c932d5ba2a6` | `c59d54b2767c3ef47ac7eb1dfbdb1d92c1e2b3560aa3f2b0c00da89705e3f9b3` (9) |
| `Toy.Sep.triple_of_fqTriple_nonvacuous` | R6b non-vacuity | Quot.sound, propext | `ece8cee6c86de259430ee00ce74ac08f2d0e05b30bbe01cc18aaed9dc1e57460` | `58bdf1e828ec74ad1dcfd74e2877d82c8a452d71556f3056a9c517cca9060607` (28) |
| `Toy.Sep.triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw` | R6b result | (none) | `21f4dbc91345338422ed6da8bdded8f5dfccd116d3037814ffbf2bc369559ee2` | `f5b378ccfee33dfd40b9f0690f2d206c96b3c59d20e327d3785867d21af2f1a4` (16) |
| `Toy.Sep.triple_of_fqTriple_of_rightUnitLaw` | R6b result | (none) | `a0cc5ea0f58672c3c8cb98ae3538ae5f039aca848a1e7b0e018c71f791b27e98` | `23d73f95a928491397f7ec39c74b3f53e8a4f44d60acb244b354db7abb24c9fc` (14) |
| `Toy.Sep.triple_of_fqTriple_premise_tight` | R6b counterexample | Quot.sound, propext | `fa2c2880b3fd5e5a7228fe7f70427e4d97593d951a402139f393f21eebbe4df9` | `48b2367bc7cf44fa215029a3a12292ff67a0647299c8f79bf1455a332740960b` (22) |
| `Toy.Sep.unionAssocRev_of_disjSymm_of_unionAssoc` | R6a result | (none) | `4df7c474d9d2db6ca222d07aefbc72f933146fc52d8483e4a273fd27b648d546` | `4da7474a84f6aae8076fcb956cd93af3510533c26adea374130c5982518a4a78` (7) |
| `Toy.Sep.unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc` | R6a result | (none) | `6e6f035e0ed28c4623c10a04bde73bc44d6953018635c880ae21313637a51c51` | `40075fcb77cf4a22e1ab556f93b5de8effc0db30a67715c54b61bdf011b2961c` (8) |

### Primary sources

Exact records (section, definition, lemma and line numbers) for each citation are quoted
in the per-result prior-art lists under **Findings**. Consolidated list (DOIs resolved
against the registration agencies' metadata; repository revisions are full commit ids):

* Yang, H. & O'Hearn, P. W., "A Semantic Basis for Local Reasoning", FoSSaCS 2002,
  LNCS 2303, pp. 402–416, doi:10.1007/3-540-45931-6_28.
* Calcagno, C., O'Hearn, P. W. & Yang, H., "Local Action and Abstract Separation Logic",
  LICS 2007, pp. 366–378, doi:10.1109/LICS.2007.30.
* O'Hearn, P. W., Yang, H. & Reynolds, J. C., "Separation and Information Hiding", POPL
  2004, pp. 268–280, doi:10.1145/964001.964024; journal version ACM TOPLAS 31(3), Article
  11, pp. 11:1–11:50, 2009, doi:10.1145/1498926.1498929.
* Reynolds, J. C., "Separation Logic: A Logic for Shared Mutable Data Structures", LICS
  2002, pp. 55–74, doi:10.1109/LICS.2002.1029817.
* Ishtiaq, S. S. & O'Hearn, P. W., "BI as an Assertion Language for Mutable Data
  Structures", POPL 2001, pp. 14–26, doi:10.1145/360204.375719.
* Charguéraud, A., "Separation Logic for Sequential Programs (Functional Pearl)", PACMPL
  4(ICFP), Article 116, 2020, doi:10.1145/3408998.
* Birkedal, L., Torp-Smith, N. & Yang, H., "Semantics of Separation-Logic Typing and
  Higher-Order Frame Rules", LICS 2005, pp. 260–269, doi:10.1109/LICS.2005.47; journal
  version LMCS 2(5:1), 2006, doi:10.2168/LMCS-2(5:1)2006.
* Appel, A. W. & Blazy, S., "Separation Logic for Small-Step Cminor", TPHOLs 2007, LNCS
  4732, pp. 5–21, doi:10.1007/978-3-540-74591-4_3.
* Myreen, M. O. & Gordon, M. J. C., "Hoare Logic for Realistically Modelled Machine Code",
  TACAS 2007, LNCS 4424, pp. 568–582, doi:10.1007/978-3-540-71209-1_44. The paper text was
  not inspected; the frame-quantified form is cited from the HOL4 source below.
* Costanzo, D. & Shao, Z., "A Case for Behavior-Preserving Actions in Separation Logic",
  APLAS 2012, LNCS 7705, pp. 332–349, doi:10.1007/978-3-642-35182-2_24.
* Tuerk, T., "A separation logic framework for HOL", University of Cambridge Computer
  Laboratory Technical Report UCAM-CL-TR-799, June 2011, doi:10.48456/tr-799.
* Further sources cited in individual cards (Gotsman, Berdine & Cook 2011; Brookes 2007;
  Dockins, Hobor & Appel 2009; Klein, Kolanski & Boyton ITP 2012 and the Isabelle AFP
  entry `Separation_Algebra`; Appel et al. 2014; `verse-lab/splean`) are recorded with
  their identifiers in the prior-art lists.

Source repositories inspected (full revisions):

* HOL4, `HOL-Theorem-Prover/HOL` at `c2b475d585febe0e718f87ab51959c0a73fc924e`:
  `examples/separationLogic/src/separationLogicScript.sml` (lines 2457–2462
  `ASL_IS_LOCAL_ACTION`, 2490–2495 `LOCALITY_CHARACTERISATION_REL`, 2699–2703
  `ASL_IS_LOCAL_ACTION___HOARE_TRIPLE`, 1690 `IS_PRECISE___CHARACTERISATION`, 286
  `IS_SEPARATION_COMBINATOR_EXPAND_THM`) and
  `examples/machine-code/hoare-triple/progScript.sml` (lines 24–29 `RUN_def`, 35–39
  `SPEC_def`; RUN quantifies over every frame `r`).
* VST, `PrincetonUniversity/VST` tag `v2.14` = `e1db53a4e22ddd3f8223532ba73127b706faf1b3`:
  `msl/predicates_sa.v` lines 78–122 (`precise`, `precise_eq`).

### Observation dates

All kernel checks, statement hashes and the toolchain and HOL4 `progScript.sml` source
checks were made on the `observed_at` date in `REPORT.json`. Other source facts quoted in
the prior-art lists were checked at the cited revisions before that date and are not
time-dependent (pinned commits and published papers).

## Revalidation

### One command

From the package directory (the directory containing this `REPORT.md`):

```sh
python3 support/revalidate.py .
```

Requirements: `elan` (so that `lake` selects the toolchain pinned in
`lean/lean-toolchain`) and `python3`; nothing else. The script copies `lean/` to a
temporary directory (the package is not modified) and checks, printing `REVALIDATED` on
success:

1. `lake build` succeeds;
2. no Lean source contains `sorry`, `admit`, `native_decide`, or an `axiom` declaration;
3. every declaration of the `Toy` library depends only on `propext`, `Classical.choice`,
   `Quot.sound` (`Lean.collectAxioms`);
4. for every Lean name referenced by `results.json` (result names, supporting lemmas in
   `lean_names`, non-vacuity witnesses, positive controls, counterexamples), the SHA-256 of the statement — the string
   `toString (repr type)` of the declaration's type — and the SHA-256 of its definition
   closure — the newline-joined, sorted list of `name : repr type`, followed by
   ` := repr value` for every non-theorem, over all package constants reachable from the
   statement (theorem bodies excluded), with its size — equal the values in
   `audit/statements.json`.

A passing run establishes that the same statements (byte-identical `repr`, hence the same
definitions they depend on) are kernel-checked under the pinned toolchain with standard
axioms. It does not re-examine prose, citations, or the modeling bridges.

### Manual equivalent

```sh
cd lean
lake build                              # builds library Toy; must report no errors and no 'sorry'
lake env lean RevalidationAudit.lean    # prints #print axioms for every card-referenced name,
                                        # then one line 'AUDIT_JSON {...}' with statement/closure text
```

`lean/RevalidationAudit.lean` (outside the `Toy` library target, so `lake build` does not
build it) runs `#print axioms` for every card-referenced name and prints the statement
`repr` and definition-closure text described above as JSON. To recompute and compare the
hashes (run from `lean/`):

```sh
lake env lean RevalidationAudit.lean | python3 -c '
import hashlib, json, re, sys
a = json.loads(re.search(r"AUDIT_JSON (\{.*\})", sys.stdin.read()).group(1))
rec = json.load(open("../audit/statements.json"))["statements"]
bad = 0
for s in a["stmts"]:
    got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
           "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
           "closure_size": len(s["closure"])}
    if rec.get(s["name"]) != got:
        bad += 1; print("MISMATCH", s["name"])
print("checked", len(a["stmts"]), "names;", "OK" if bad == 0 and len(a["stmts"]) == len(rec) else "FAILED")
'
```

### What to re-run after a change

* After editing a proof only: the statement and closure hashes must be unchanged; re-run
  either command above.
* After editing any definition quoted under **Findings**: the closure hashes of every
  dependent result change, so every dependent card must be re-reviewed against the new
  definitions; the hashes in `audit/statements.json` then no longer certify the cards.
* For a different Lean release: re-run with `lean/lean-toolchain` changed; `repr` output
  may change across releases, so hash mismatches alone do not indicate a changed
  statement, while build or axiom failures do.
