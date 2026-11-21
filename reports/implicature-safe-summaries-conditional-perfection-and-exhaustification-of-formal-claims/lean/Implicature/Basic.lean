/-!
# Claims, finite model spaces, and entailment

A toy, finite, decidable model of the formal claims that a technical report establishes and
of their compressed renderings (summary sentences, headlines).

* A `Claim` is built from atoms applied to a parameter argument, the propositional
  connectives `∧ ∨ → ↔ ¬`, bounded quantifiers `∀`/`∃` over the finite parameter set of the
  space, and a hypothesis-relativized form `rel H C` ("under hypothesis `H`, `C`").
* A `Space` is a finite list of worlds, a finite parameter list, and an interpretation of every
  atom at every parameter value in every world. A claim denotes a `Bool`-valued predicate on
  worlds, so entailment over the listed worlds is decidable.

Worlds model the epistemic possibilities that are compatible with the space: a claim such as
`∀x, A x → B x` is a single proposition about a world, and "the report proves the claim" is
modelled as entailment from the report's established claims over all listed worlds.
-/

namespace Toy.Implicature

/-- The argument of an atom: a literal parameter value, or the bound variable of the nearest
enclosing quantifier. The syntax has a single variable; an inner quantifier shadows an outer
one. Outside every quantifier, `var` reads parameter value `0` (claims are intended closed). -/
inductive Arg where
  | lit (k : Nat)
  | var
  deriving DecidableEq, Repr

/-- Claim syntax. `imp` is a stated conditional result ("`A` gives `B`"); `rel h c` is a claim
under a stated hypothesis ("under `h`, `c`"). The two have the same truth conditions
(material implication); they differ only in which reader rules and alternatives apply. -/
inductive Claim where
  | top
  | atom (a : Nat) (t : Arg)
  | and (c d : Claim)
  | or (c d : Claim)
  | imp (c d : Claim)
  | iff (c d : Claim)
  | not (c : Claim)
  | all (c : Claim)
  | ex (c : Claim)
  | rel (h c : Claim)
  deriving DecidableEq, Repr

/-- Human-readable rendering of an argument (`x` is the bound variable). -/
def Arg.render : Arg → String
  | .lit k => toString k
  | .var => "x"

/-- Human-readable rendering of a claim; atom `a` is printed `Pa`. -/
def Claim.render : Claim → String
  | .top => "⊤"
  | .atom a t => s!"P{a}({t.render})"
  | .and c d => s!"({c.render} ∧ {d.render})"
  | .or c d => s!"({c.render} ∨ {d.render})"
  | .imp c d => s!"({c.render} → {d.render})"
  | .iff c d => s!"({c.render} ↔ {d.render})"
  | .not c => s!"¬{c.render}"
  | .all c => s!"(∀x, {c.render})"
  | .ex c => s!"(∃x, {c.render})"
  | .rel h c => s!"({h.render} ⇒ {c.render})"

/-- A finite model space: an explicit list of worlds, an explicit finite list of parameter
values (the domain of the bounded quantifiers), and the truth value `val w a k` of atom `a` at
parameter value `k` in world `w`. Only the listed worlds count for entailment. -/
structure Space where
  World : Type
  worlds : List World
  params : List Nat
  val : World → Nat → Nat → Bool

namespace Space

/-- Evaluation of a claim in world `w` with the bound variable set to `x`. -/
def evalAt (S : Space) (w : S.World) (x : Nat) : Claim → Bool
  | .top => true
  | .atom a (.lit k) => S.val w a k
  | .atom a .var => S.val w a x
  | .and c d => S.evalAt w x c && S.evalAt w x d
  | .or c d => S.evalAt w x c || S.evalAt w x d
  | .imp c d => !S.evalAt w x c || S.evalAt w x d
  | .iff c d => S.evalAt w x c == S.evalAt w x d
  | .not c => !S.evalAt w x c
  | .all c => S.params.all fun y => S.evalAt w y c
  | .ex c => S.params.any fun y => S.evalAt w y c
  | .rel h c => !S.evalAt w x h || S.evalAt w x c

/-- Truth of a (closed) claim in a world. -/
def holds (S : Space) (w : S.World) (c : Claim) : Bool := S.evalAt w 0 c

/-- The space of all valuations of `nAtoms` atoms over the parameter values `0 … nParams-1`.
A world is a bitmask `w < 2 ^ (nAtoms * nParams)`; atom `a` holds at value `k` iff bit
`a * nParams + k` of `w` is set. Atoms and values outside the ranges are false. -/
def full (nAtoms nParams : Nat) : Space where
  World := Nat
  worlds := List.range (2 ^ (nAtoms * nParams))
  params := List.range nParams
  val w a k := decide (a < nAtoms) && decide (k < nParams) && w.testBit (a * nParams + k)

/-- A space with a single world in which every atom has a fixed, intended interpretation over
the given parameter values. Used for "natural" instances whose atoms are concrete predicates.
With one world, entailment from any report collapses to truth in that world: every claim is
decided even by the empty report, no claim is left open (`interp_never_open`), and cancellation
discards every false reading, so a literally safe rendering is strengthening-safe with no flags
(`interp_literallySafe_strengtheningSafe_unblocked`). Single-world spaces therefore cannot exhibit
an open claim or an implicature hazard; they only illustrate truth in a fixed structure. -/
def interp (params : List Nat) (val : Nat → Nat → Bool) : Space where
  World := Unit
  worlds := [()]
  params := params
  val _ a k := val a k

end Space

/-- `E ⊨ σ`: every listed world in which all claims of `E` hold is a world in which `σ` holds. -/
def Entails (S : Space) (E : List Claim) (σ : Claim) : Prop :=
  ∀ w ∈ S.worlds, (∀ e ∈ E, S.holds w e = true) → S.holds w σ = true

/-- `Γ` is jointly satisfiable in some listed world. -/
def Sat (S : Space) (Γ : List Claim) : Prop :=
  ∃ w ∈ S.worlds, ∀ c ∈ Γ, S.holds w c = true

/-- `E` contradicts `ρ`: `E` entails the negation of `ρ` (refutes it). -/
def Contradicts (S : Space) (E : List Claim) (ρ : Claim) : Prop :=
  Entails S E (.not ρ)

/-- Semantic equivalence of two claims over the listed worlds. -/
def Equiv (S : Space) (c d : Claim) : Prop :=
  Entails S [c] d ∧ Entails S [d] c

/-- Boolean decision procedure for `Entails`. -/
def entailsB (S : Space) (E : List Claim) (σ : Claim) : Bool :=
  S.worlds.all fun w => !(E.all fun e => S.holds w e) || S.holds w σ

/-- Boolean decision procedure for `Sat`. -/
def satB (S : Space) (Γ : List Claim) : Bool :=
  S.worlds.any fun w => Γ.all fun c => S.holds w c

theorem entailsB_iff {S : Space} {E : List Claim} {σ : Claim} :
    entailsB S E σ = true ↔ Entails S E σ := by
  unfold entailsB Entails
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h w hw hE
    rcases h w hw with h1 | h1
    · have : (E.all fun e => S.holds w e) = true := List.all_eq_true.mpr hE
      rw [this] at h1; cases h1
    · exact h1
  · intro h w hw
    by_cases hE : (E.all fun e => S.holds w e) = true
    · exact Or.inr (h w hw (List.all_eq_true.mp hE))
    · exact Or.inl (by simpa using hE)

theorem satB_iff {S : Space} {Γ : List Claim} : satB S Γ = true ↔ Sat S Γ := by
  unfold satB Sat
  simp only [List.any_eq_true, List.all_eq_true]

instance decEntails (S : Space) (E : List Claim) (σ : Claim) : Decidable (Entails S E σ) :=
  decidable_of_iff _ entailsB_iff

instance decSat (S : Space) (Γ : List Claim) : Decidable (Sat S Γ) :=
  decidable_of_iff _ satB_iff

instance decContradicts (S : Space) (E : List Claim) (ρ : Claim) :
    Decidable (Contradicts S E ρ) :=
  decEntails S E (.not ρ)

instance decEquiv (S : Space) (c d : Claim) : Decidable (Equiv S c d) :=
  instDecidableAnd

/-- Conjunction of a list of claims (`top` for the empty list). -/
def conjList : List Claim → Claim
  | [] => .top
  | [c] => c
  | c :: cs => .and c (conjList cs)

theorem holds_conjList (S : Space) (w : S.World) :
    ∀ cs : List Claim, S.holds w (conjList cs) = cs.all (S.holds w)
  | [] => rfl
  | [c] => by simp [conjList]
  | c :: d :: cs => by
      have ih := holds_conjList S w (d :: cs)
      show (S.holds w c && S.holds w (conjList (d :: cs))) = _
      rw [ih]
      rfl

end Toy.Implicature
