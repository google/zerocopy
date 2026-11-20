/-!
# Separation structures, commands, assertions, triples, locality

These definitions follow the relational presentation of local actions (Yang and O'Hearn,
"A Semantic Basis for Local Reasoning", FoSSaCS 2002; Calcagno, O'Hearn and Yang, "Local Action
and Abstract Separation Logic", LICS 2007).

* A `SepStruct S` is a carrier with a disjointness relation `disj` and a total operation `union`
  that is only *meaningful* on disjoint arguments. No algebraic laws are bundled: every law is a
  separate named `Prop`.
* A command is a relation from an initial state to an `Outcome`: `fault` (a memory error) or
  `ok s`. Commands may be nondeterministic and may have no outcome from some states.
* An assertion is an arbitrary predicate on states; `sep P Q` is separating conjunction.
* `Triple P c Q` is the fault-avoiding partial-correctness triple `{P} c {Q}`.
-/

namespace Toy.ByteSL

universe u

/-- A *separation structure*: a carrier with a disjointness relation and a total union operation
(meaningful only on disjoint arguments). No laws are assumed. -/
class SepStruct (S : Type u) where
  /-- Disjointness: `disj a b` means `a` and `b` may be combined. -/
  disj : S → S → Prop
  /-- Combination; meaningful only on disjoint arguments. -/
  union : S → S → S

open SepStruct

variable {S : Type u}

/-! ## Algebraic laws (each a separate `Prop`) -/

/-- Law: disjointness is symmetric. -/
def DisjSymm (S : Type u) [SepStruct S] : Prop :=
  ∀ a b : S, disj a b → disj b a

/-- Law: union is commutative on disjoint arguments. -/
def UnionComm (S : Type u) [SepStruct S] : Prop :=
  ∀ a b : S, disj a b → union a b = union b a

/-- Law: partial associativity (left-to-right form): if `a ⊥ b` and `(a ∘ b) ⊥ c` then `b ⊥ c`,
`a ⊥ (b ∘ c)` and the two bracketings agree. -/
def UnionAssoc (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj a b → disj (union a b) c →
    disj b c ∧ disj a (union b c) ∧ union (union a b) c = union a (union b c)

/-- Law: `e` is a left unit: disjoint from everything and `e ∘ a = a`. -/
def UnitLaw [SepStruct S] (e : S) : Prop :=
  ∀ a : S, disj e a ∧ union e a = a

/-- Law: right cancellativity: `a ∘ c = b ∘ c` (both defined) implies `a = b`. -/
def RightCancel (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj a c → disj b c → union a c = union b c → a = b

/-- A partial commutative monoid with unit `e` (symmetric disjointness, commutativity, partial
associativity, unit); cancellativity is *not* included. -/
structure IsSepAlgebra (S : Type u) [SepStruct S] (e : S) : Prop where
  disjSymm : DisjSymm S
  comm : UnionComm S
  assoc : UnionAssoc S
  unit : UnitLaw e

/-! ## Outcomes, commands, assertions -/

/-- The outcome of running a command: a memory fault, or normal termination in a final state. -/
inductive Outcome (S : Type u) where
  /-- The command faulted (e.g. accessed memory it does not own). -/
  | fault : Outcome S
  /-- The command terminated normally in the given state. -/
  | ok : S → Outcome S

/-- A command: a relation from an initial state to outcomes. -/
abbrev Cmd (S : Type u) := S → Outcome S → Prop

/-- An assertion: an arbitrary predicate on states. -/
abbrev Assn (S : Type u) := S → Prop

/-- Separating conjunction `P * Q`: the state splits into two disjoint parts, the left
satisfying `P` and the right satisfying `Q`. -/
def sep [SepStruct S] (P Q : Assn S) : Assn S :=
  fun h => ∃ h₁ h₂, disj h₁ h₂ ∧ h = union h₁ h₂ ∧ P h₁ ∧ Q h₂

/-- `c` is *safe* at `h`: it cannot fault when started in `h`. -/
def Safe (c : Cmd S) (h : S) : Prop := ¬ c h .fault

/-- Fault-avoiding partial-correctness triple `{P} c {Q}`. -/
def Triple (P : Assn S) (c : Cmd S) (Q : Assn S) : Prop :=
  ∀ h, P h → Safe c h ∧ ∀ h', c h (.ok h') → Q h'

/-! ## Locality (each property a separate `Prop`) -/

/-- *Safety monotonicity*: if `c` cannot fault from `h`, it cannot fault from any disjoint
extension `h ∘ h'`. -/
def SafetyMono [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' : S, disj h h' → Safe c h → Safe c (union h h')

/-- *Frame property*: if `c` cannot fault from `h`, every normal run from `h ∘ h'` ends in
`h₀ ∘ h'` (with `h₀ ⊥ h'`) for some final state `h₀` of a run of `c` from `h` alone. -/
def FrameProp [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' h'' : S, disj h h' → Safe c h → c (union h h') (.ok h'') →
    ∃ h₀, c h (.ok h₀) ∧ disj h₀ h' ∧ h'' = union h₀ h'

/-- *Locality*: safety monotonicity together with the frame property. -/
def Local [SepStruct S] (c : Cmd S) : Prop :=
  SafetyMono c ∧ FrameProp c

/-- The frame rule is sound for `c`: for all assertions `P Q R`, `{P} c {Q}` implies
`{P * R} c {Q * R}`. -/
def FrameRuleSound [SepStruct S] (c : Cmd S) : Prop :=
  ∀ P Q R : Assn S, Triple P c Q → Triple (sep P R) c (sep Q R)

/-- The command that does nothing. -/
def skip : Cmd S := fun h o => o = .ok h

end Toy.ByteSL
