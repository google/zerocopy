/-!
# Separation structures, commands, assertions, triples, locality, precision

This module fixes the abstract vocabulary of the package `Toy.Sep`.

* A `SepStruct S` is a carrier with a disjointness relation `disj` and a total
  operation `union` that is only *meaningful* on disjoint arguments. No algebraic
  laws are bundled into it: every law (symmetry, commutativity, associativity,
  unit, left and right cancellativity) is a separate named `Prop`, so each theorem
  names exactly the laws it uses. The concrete heap model lives in
  `Toy.Sep.Heap`; two small non-cancellative partial commutative monoids live
  in `Toy.Sep.Algebras`.
* A command is a relation from an initial state to an `Outcome`: either `fault`
  (a memory error) or `ok s` (normal termination in state `s`). Commands may be
  nondeterministic and may have no outcome at all from some states (divergence or
  blocking). This is the relational reading of the "local actions" of abstract
  separation logic, with `fault` playing the role of the top element.
* An assertion is an arbitrary predicate on states; `sep P Q` is separating
  conjunction.
* `Triple P c Q` is the fault-avoiding partial-correctness triple `{P} c {Q}`.
-/

namespace Toy.Sep

universe u

/-- A *separation structure*: a carrier with a disjointness relation and a total
union operation. `union a b` is only intended to be meaningful when `disj a b`.
No laws are assumed here; see `DisjSymm`, `UnionComm`, `UnionAssoc`, `UnitLaw`,
`RightCancel`, `LeftCancel`. This is the weakest setting in which separating
conjunction can be defined. -/
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

/-- Law: partial associativity, in the usual form for partial commutative monoids:
if `a ⊥ b` and `(a ∘ b) ⊥ c` then `b ⊥ c`, `a ⊥ (b ∘ c)` and the two bracketings
agree. This is the *left-to-right* direction only: on its own it does not give
`(a ∘ b) ∘ c` from `a ∘ (b ∘ c)`. The reverse direction is `UnionAssocRev`; the
two coincide in the presence of `DisjSymm` and `UnionComm`
(`Toy.Sep.unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc`). -/
def UnionAssoc (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj a b → disj (union a b) c →
    disj b c ∧ disj a (union b c) ∧ union (union a b) c = union a (union b c)

/-- Law: partial associativity, *right-to-left* direction: if `b ⊥ c` and
`a ⊥ (b ∘ c)` then `a ⊥ b`, `(a ∘ b) ⊥ c` and the two bracketings agree. -/
def UnionAssocRev (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj b c → disj a (union b c) →
    disj a b ∧ disj (union a b) c ∧ union a (union b c) = union (union a b) c

/-- Law: `e` is a *left* unit: it is disjoint from everything and `e ∘ a = a`.
Together with `DisjSymm` and `UnionComm` this makes `e` a two-sided unit. On its
own it says nothing about `a ∘ e`; see `RightUnitLaw`. -/
def UnitLaw [SepStruct S] (e : S) : Prop :=
  ∀ a : S, disj e a ∧ union e a = a

/-- Law: `e` is a *right* unit: everything is disjoint from it and `a ∘ e = a`. -/
def RightUnitLaw [SepStruct S] (e : S) : Prop :=
  ∀ a : S, disj a e ∧ union a e = a

/-- Law: right cancellativity: `a ∘ c = b ∘ c` (both defined) implies `a = b`. -/
def RightCancel (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj a c → disj b c → union a c = union b c → a = b

/-- Law: left cancellativity: `c ∘ a = c ∘ b` (both defined) implies `a = b`. -/
def LeftCancel (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj c a → disj c b → union c a = union c b → a = b

/-- A partial commutative monoid with a single unit `e` (symmetric disjointness,
commutativity, partial associativity, unit), over a total union operation.

Terminology: this is a "separation algebra" only in the relaxed sense that omits
cancellativity (as in Gotsman, Berdine and Cook 2011, and the Isabelle AFP class
`sep_algebra`). Calcagno, O'Hearn and Yang 2007 and Dockins, Hobor and Appel 2009
make cancellativity part of the definition of a separation algebra; in their
terminology an `IsSepAlgebra` that is not cancellative is merely a partial
commutative monoid. `RightCancel` and `LeftCancel` are kept separate because they
are exactly what the precision results depend on. The structure also assumes a
single global unit (no multi-unit algebras) and imposes no positivity law. -/
structure IsSepAlgebra (S : Type u) [SepStruct S] (e : S) : Prop where
  disjSymm : DisjSymm S
  comm : UnionComm S
  assoc : UnionAssoc S
  unit : UnitLaw e

/-! ## Outcomes, commands, assertions -/

/-- The outcome of running a command: a memory fault, or normal termination in a
final state. -/
inductive Outcome (S : Type u) where
  /-- The command faulted (e.g. accessed an unallocated cell). -/
  | fault : Outcome S
  /-- The command terminated normally in the given state. -/
  | ok : S → Outcome S

/-- A command: a relation from an initial state to outcomes. Nondeterminism
(several outcomes) and divergence/blocking (no outcome) are both allowed. -/
abbrev Cmd (S : Type u) := S → Outcome S → Prop

/-- An assertion: an arbitrary predicate on states. -/
abbrev Assn (S : Type u) := S → Prop

/-- Separating conjunction `P * Q`: the state splits into two disjoint parts,
the left satisfying `P` and the right satisfying `Q`. -/
def sep [SepStruct S] (P Q : Assn S) : Assn S :=
  fun h => ∃ h₁ h₂, disj h₁ h₂ ∧ h = union h₁ h₂ ∧ P h₁ ∧ Q h₂

/-- Pointwise conjunction of assertions. -/
def conj (P Q : Assn S) : Assn S := fun h => P h ∧ Q h

/-- The singleton assertion: holds exactly of the state `x`. -/
def sing (x : S) : Assn S := fun h => h = x

/-- The strongest postcondition of `c` from the single state `h`: the set of
states `c` can terminate in when started in `h`. -/
def post (c : Cmd S) (h : S) : Assn S := fun h' => c h (.ok h')

/-- `c` is *safe* at `h`: it cannot fault when started in `h`. -/
def Safe (c : Cmd S) (h : S) : Prop := ¬ c h .fault

/-- Fault-avoiding partial-correctness triple `{P} c {Q}`: from every state
satisfying `P`, `c` cannot fault, and every normal final state satisfies `Q`.
Divergence is permitted. -/
def Triple (P : Assn S) (c : Cmd S) (Q : Assn S) : Prop :=
  ∀ h, P h → Safe c h ∧ ∀ h', c h (.ok h') → Q h'

/-- The *non*-fault-avoiding partial-correctness triple: only normal final states
are constrained; faulting is allowed. It is included only to show that the frame
rule needs fault avoidance (see `Toy.Sep.assertAlloc_local_and_framed_weakTriple_fails`). -/
def WeakTriple (P : Assn S) (c : Cmd S) (Q : Assn S) : Prop :=
  ∀ h, P h → ∀ h', c h (.ok h') → Q h'

/-! ## Locality properties of commands (each a separate `Prop`) -/

/-- *Safety monotonicity*: if `c` cannot fault from `h`, it cannot fault from any
disjoint extension `h ∘ h'`. -/
def SafetyMono [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' : S, disj h h' → Safe c h → Safe c (union h h')

/-- *Frame property*: if `c` cannot fault from `h`, then every normal run from a
disjoint extension `h ∘ h'` ends in a state of the form `h₀ ∘ h'` (with
`h₀ ⊥ h'`) where `h₀` is a final state of some run of `c` from `h` alone. The
extension `h'` is untouched, and the rest of the result is explained by a run on
the smaller state. -/
def FrameProp [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' h'' : S, disj h h' → Safe c h → c (union h h') (.ok h'') →
    ∃ h₀, c h (.ok h₀) ∧ disj h₀ h' ∧ h'' = union h₀ h'

/-- *Locality*: safety monotonicity together with the frame property. The main
theorems state `SafetyMono c ∧ FrameProp c` explicitly; this is definitionally
`Local c` (`Toy.Sep.local_iff`). -/
def Local [SepStruct S] (c : Cmd S) : Prop :=
  SafetyMono c ∧ FrameProp c

theorem local_iff [SepStruct S] (c : Cmd S) : Local c ↔ SafetyMono c ∧ FrameProp c :=
  Iff.rfl

/-- The frame rule is sound for `c`: for all assertions `P Q R`,
`{P} c {Q}` implies `{P * R} c {Q * R}`. -/
def FrameRuleSound [SepStruct S] (c : Cmd S) : Prop :=
  ∀ P Q R : Assn S, Triple P c Q → Triple (sep P R) c (sep Q R)

/-- The frame rule holds for `c` at least at all *singleton* instances:
precondition `{h}`, its strongest postcondition `post c h`, and singleton frame
`{h'}`. This is a much weaker requirement than `FrameRuleSound c`. -/
def FrameRuleAtSingletons [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' : S, Triple (sing h) c (post c h) →
    Triple (sep (sing h) (sing h')) c (sep (post c h) (sing h'))

/-! ## Precision and the distribution law -/

/-- `R` is *precise*: any two decompositions `f₁ ∘ r₁ = f₂ ∘ r₂` of the same
state whose right parts satisfy `R` have the same right part. In the heap model
this is "every heap has at most one subheap satisfying `R`"
(`Toy.Sep.heap_precise_iff_atMostOneSubheap`). The `R`-part is on the right
because `sep P R` puts `R` on the right; the left-handed variant is
`Toy.Sep.PreciseLeft`, and the two coincide under `DisjSymm` and `UnionComm`.
Without a unit, a state need not be a decomposition of itself, so in non-unital
structures even the always-true assertion can be precise
(`Toy.Sep.onePair_true_precise`). -/
def Precise [SepStruct S] (R : Assn S) : Prop :=
  ∀ f₁ r₁ f₂ r₂ : S, disj f₁ r₁ → disj f₂ r₂ → union f₁ r₁ = union f₂ r₂ →
    R r₁ → R r₂ → r₁ = r₂

/-- The frame rule holds for `c` for every precondition and postcondition but
only for *precise* frames `R`. -/
def FrameRuleForPreciseFrames [SepStruct S] (c : Cmd S) : Prop :=
  ∀ P Q R : Assn S, Precise R → Triple P c Q → Triple (sep P R) c (sep Q R)

/-- `R` has *unique frames*: any two decompositions `f₁ ∘ r₁ = f₂ ∘ r₂` of the
same state whose right parts satisfy `R` have the same left part (the "frame").
This is the dual of `Precise`; the two coincide in cancellative structures. -/
def UniqueFrame [SepStruct S] (R : Assn S) : Prop :=
  ∀ f₁ r₁ f₂ r₂ : S, disj f₁ r₁ → disj f₂ r₂ → union f₁ r₁ = union f₂ r₂ →
    R r₁ → R r₂ → f₁ = f₂

/-- The conjunction-distribution law for the frame `R`:
`(P * R) ∧ (Q * R) ⊢ (P ∧ Q) * R` for all `P` and `Q`. (The converse entailment
holds for every `R`.) -/
def ConjDistrib [SepStruct S] (R : Assn S) : Prop :=
  ∀ (P Q : Assn S) (h : S), sep P R h → sep Q R h → sep (conj P Q) R h

/-! ## Generic commands -/

/-- The command that does nothing: `skip h o ↔ o = ok h`. -/
def skip : Cmd S := fun h o => o = .ok h

/-- The command with no outcome from any state (divergence or blocking). -/
def diverge : Cmd S := fun _ _ => False

/-- The command that faults from every state and never terminates normally. -/
def abort : Cmd S := fun _ o => o = .fault

/-! ## Derivable laws (proved) -/

/-- With symmetric disjointness and commutative union, left-to-right partial
associativity implies the right-to-left direction. -/
theorem unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc [SepStruct S]
    (hs : DisjSymm S) (hc : UnionComm S) (ha : UnionAssoc S) : UnionAssocRev S := by
  intro a b c hbc habc
  have hcb : disj c b := hs b c hbc
  have hbc_eq : union b c = union c b := hc b c hbc
  have hcba : disj (union c b) a := hbc_eq ▸ hs a (union b c) habc
  obtain ⟨hba, hc_ba, he⟩ := ha c b a hcb hcba
  have hab : disj a b := hs b a hba
  have hba_eq : union b a = union a b := hc b a hba
  have hab_c : disj (union a b) c := hba_eq ▸ hs c (union b a) hc_ba
  refine ⟨hab, hab_c, ?_⟩
  calc union a (union b c)
      = union (union b c) a := hc a (union b c) habc
    _ = union (union c b) a := by rw [hbc_eq]
    _ = union c (union b a) := he
    _ = union (union b a) c := hc c (union b a) hc_ba
    _ = union (union a b) c := by rw [hba_eq]

/-- With symmetric disjointness and commutative union, a left unit is a right
unit. -/
theorem rightUnitLaw_of_disjSymm_of_unionComm_of_unitLaw [SepStruct S] {e : S}
    (hs : DisjSymm S) (hc : UnionComm S) (hu : UnitLaw e) : RightUnitLaw e :=
  fun a => ⟨hs e a (hu a).1, (hc a e (hs e a (hu a).1)).trans (hu a).2⟩

end Toy.Sep
