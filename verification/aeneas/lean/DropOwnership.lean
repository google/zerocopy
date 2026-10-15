/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Std
@[expose] public section

namespace AeneasSpecs.DropOwnership

/-!
This module checks a small ownership model, not Rust's memory semantics. A
concrete state records destruction obligations; it says nothing about bytes
remaining in storage after a move. The caller must establish that its complete
body projection preserves evaluation order, all edges, and whole-slot effects.
It must also establish that an obligation-free conditional drop is silent in
the compiler interpretation. Those bridges are deliberately separate premises.

Every source component and the designated entry can start with any obligations
on the declared locals. Consuming a whole slot removes its obligation; defining
it restores one. Consequently, an assignment must list RHS effects before the
destination definition. A call's destination must be defined on every successor,
including unwind. Slot reuse and storage markers restore uncertainty too.
-/

inductive Effect where
  | consume (slot : Nat)
  | define (slot : Nat)
  deriving Repr, DecidableEq, Inhabited

structure Node where
  effects : List Effect := []
  candidateDrop : Option Nat := none
  successors : List Nat := []
  deriving Repr, DecidableEq, Inhabited

structure Graph where
  nodes : List Node
  localCount : Nat
  entry : Nat := 0
  deriving Repr, DecidableEq, Inhabited

def Graph.node (g : Graph) (index : Nat) : Node :=
  g.nodes[index]?.getD default

def Effect.slot : Effect → Nat
  | .consume slot | .define slot => slot

/-- Abstract states are conservative sets, represented by finite lists. List
order and duplicate elements have no semantic significance. -/
def applyEffect : Effect → List Nat → List Nat
  | .consume slot, owns => owns.filter (· != slot)
  | .define slot, owns => slot :: owns

def transfer : List Effect → List Nat → List Nat
  | [], owns => owns
  | effect :: rest, owns => transfer rest (applyEffect effect owns)

/-- A certificate gives the incoming may-own set at each node. It is untrusted:
`check` validates every obligation used by the soundness proof. -/
abbrev Certificate := Nat → List Nat

def IsRoot (g : Graph) (index : Nat) : Prop :=
  index = g.entry ∨ ∀ node ∈ g.nodes, index ∉ node.successors

instance (g : Graph) (index : Nat) : Decidable (IsRoot g index) :=
  inferInstanceAs (Decidable
    (index = g.entry ∨ ∀ node ∈ g.nodes, index ∉ node.successors))

/-- In addition to ownership closure, validate every slot and successor. The
strict successor order rejects cycles anywhere, even in a disconnected or
drop-free component. A candidate drop occurs after this node's ordered effects.
-/
def NodeValid (g : Graph) (certificate : Certificate) (index : Nat) : Prop :=
  let node := g.node index
  (∀ effect ∈ node.effects, effect.slot < g.localCount) ∧
  (∀ slot ∈ node.candidateDrop,
    slot < g.localCount ∧ slot ∉ transfer node.effects (certificate index)) ∧
  (∀ next ∈ node.successors,
    index < next ∧ next < g.nodes.length ∧
      ∀ slot ∈ transfer node.effects (certificate index),
        slot ∈ certificate next) ∧
  (IsRoot g index →
    ∀ slot ∈ List.range g.localCount, slot ∈ certificate index)

instance (g : Graph) (certificate : Certificate) (index : Nat) :
    Decidable (NodeValid g certificate index) :=
  inferInstanceAs (Decidable
    ((∀ effect ∈ (g.node index).effects, effect.slot < g.localCount) ∧
    (∀ slot ∈ (g.node index).candidateDrop,
      slot < g.localCount ∧
        slot ∉ transfer (g.node index).effects (certificate index)) ∧
    (∀ next ∈ (g.node index).successors,
      index < next ∧ next < g.nodes.length ∧
        ∀ slot ∈ transfer (g.node index).effects (certificate index),
          slot ∈ certificate next) ∧
    (IsRoot g index →
      ∀ slot ∈ List.range g.localCount, slot ∈ certificate index)))

def Valid (g : Graph) (certificate : Certificate) : Prop :=
  g.entry < g.nodes.length ∧
    ∀ index ∈ List.range g.nodes.length, NodeValid g certificate index

instance (g : Graph) (certificate : Certificate) :
    Decidable (Valid g certificate) :=
  inferInstanceAs (Decidable (g.entry < g.nodes.length ∧
    ∀ index ∈ List.range g.nodes.length, NodeValid g certificate index))

def check (g : Graph) (certificate : Certificate) : Bool :=
  decide (Valid g certificate)

/-- Infer one finite certificate by forward propagation. Roots begin with all
locals; joins take union. The result still goes through `check`, so inference
needs no trusted solver and no completeness theorem. -/
def infer (g : Graph) : Certificate :=
  (List.range g.nodes.length).foldl (fun incoming index =>
    let node := g.node index
    let outgoing := transfer node.effects (incoming index)
    fun next => if next ∈ node.successors then
      outgoing ++ (incoming next).filter (fun slot => slot ∉ outgoing)
    else incoming next)
    (fun index => if IsRoot g index then List.range g.localCount else [])

def accepted (g : Graph) : Bool := check g (infer g)

/-- Every accepted edge advances its bounded node index. In particular, a path
cannot revisit a node, including through an exceptional edge. This condition
is checked for the whole graph rather than only for reachable drop sites. -/
theorem checked_edge_forward {g : Graph} {certificate : Certificate}
    (checked : check g certificate = true) {index next : Nat}
    (inBounds : index < g.nodes.length)
    (edge : next ∈ (g.node index).successors) :
    index < next ∧ next < g.nodes.length := by
  have valid : Valid g certificate := of_decide_eq_true checked
  have closure := (valid.2 index (List.mem_range.mpr inBounds)).2.2.1 next edge
  exact ⟨closure.1, closure.2.1⟩

theorem accepted_edge_forward {g : Graph} (checked : accepted g = true)
    {index next : Nat} (inBounds : index < g.nodes.length)
    (edge : next ∈ (g.node index).successors) :
    index < next ∧ next < g.nodes.length :=
  checked_edge_forward checked inBounds edge

/-!
The concrete semantics permits every initial subset of the declared locals.
It is intentionally independent of the inferred certificate. Branches choose
any listed successor, so the theorem includes ordinary and exceptional paths.
-/

abbrev Concrete := Nat → Prop

def concreteEffect : Effect → Concrete → Concrete
  | .consume slot, owns => fun other => owns other ∧ other ≠ slot
  | .define slot, owns => fun other => other = slot ∨ owns other

def execute : List Effect → Concrete → Concrete
  | [], owns => owns
  | effect :: rest, owns => execute rest (concreteEffect effect owns)

def Covers (possible : List Nat) (owns : Concrete) : Prop :=
  ∀ slot, owns slot → slot ∈ possible

theorem effect_covers (effect : Effect) {possible : List Nat} {owns : Concrete}
    (covered : Covers possible owns) :
    Covers (applyEffect effect possible) (concreteEffect effect owns) := by
  cases effect with
  | consume slot =>
    intro other obligation
    simp only [concreteEffect] at obligation
    simp only [applyEffect, List.mem_filter, bne_iff_ne, ne_eq]
    exact ⟨covered other obligation.1, obligation.2⟩
  | define slot =>
    intro other obligation
    simp only [concreteEffect] at obligation
    simp only [applyEffect, List.mem_cons]
    exact obligation.elim Or.inl (fun owned => Or.inr (covered other owned))

theorem transfer_covers (effects : List Effect)
    {possible : List Nat} {owns : Concrete} (covered : Covers possible owns) :
    Covers (transfer effects possible) (execute effects owns) := by
  induction effects generalizing possible owns with
  | nil => exact covered
  | cons effect rest induction =>
    exact induction (effect_covers effect covered)

inductive Reachable (g : Graph) : Nat → Concrete → Prop where
  | root (index : Nat) (owns : Concrete)
      (inBounds : index < g.nodes.length) (root : IsRoot g index)
      (declared : ∀ slot, owns slot → slot < g.localCount) :
      Reachable g index owns
  | step {index next : Nat} {owns : Concrete}
      (before : Reachable g index owns)
      (edge : next ∈ (g.node index).successors) :
      Reachable g next (execute (g.node index).effects owns)

/-- Every concrete execution is contained in a checked incoming invariant. -/
theorem checked_invariant {g : Graph} {certificate : Certificate}
    (checked : check g certificate = true) {index : Nat} {owns : Concrete}
    (reached : Reachable g index owns) :
    index < g.nodes.length ∧ Covers (certificate index) owns := by
  have valid : Valid g certificate := of_decide_eq_true checked
  induction reached with
  | root index owns inBounds root declared =>
    refine ⟨inBounds, ?_⟩
    intro slot obligation
    exact (valid.2 index (List.mem_range.mpr inBounds)).2.2.2 root slot
      (List.mem_range.mpr (declared slot obligation))
  | @step index next owns before edge induction =>
    have nodeValid := valid.2 index (List.mem_range.mpr induction.1)
    have closure := nodeValid.2.2.1 next edge
    refine ⟨closure.2.1, ?_⟩
    intro slot obligation
    exact closure.2.2 slot (transfer_covers (g.node index).effects
      induction.2 slot obligation)

/-- The central guarantee: every candidate at every reached occurrence has no
destruction obligation after its preceding effects. This includes a root in a
disconnected component and a path chosen through an unwind successor. -/
theorem checked_drop_empty {g : Graph} {certificate : Certificate}
    (checked : check g certificate = true) {index slot : Nat} {owns : Concrete}
    (reached : Reachable g index owns)
    (candidate : (g.node index).candidateDrop = some slot) :
    ¬ execute (g.node index).effects owns slot := by
  have valid : Valid g certificate := of_decide_eq_true checked
  have invariant := checked_invariant checked reached
  have empty := (valid.2 index (List.mem_range.mpr invariant.1)).2.1 slot
    (by simp [candidate])
  intro obligation
  exact empty.2 (transfer_covers (g.node index).effects invariant.2
    slot obligation)

theorem accepted_drop_empty {g : Graph} (checked : accepted g = true)
    {index slot : Nat} {owns : Concrete} (reached : Reachable g index owns)
    (candidate : (g.node index).candidateDrop = some slot) :
    ¬ execute (g.node index).effects owns slot :=
  checked_drop_empty checked reached candidate

/-!
This final relation states the conditional-drop interpretation assumed by the
semantic bridge: when no obligation exists, the operation returns the same
state silently; when one exists, it may invoke glue or unwind. The theorem
rules out both active alternatives for an accepted candidate. It does not
assert that an unconditional/precise drop has this interpretation.
-/

inductive DropOutcome where
  | silent
  | invokeGlue
  | unwind
  deriving Repr, DecidableEq

inductive ConditionalDrop (slot : Nat) (before : Concrete) :
    DropOutcome → Concrete → Prop where
  | empty (absent : ¬ before slot) : ConditionalDrop slot before .silent before
  | glue (present : before slot) (after : Concrete) :
      ConditionalDrop slot before .invokeGlue after
  | unwind (present : before slot) (after : Concrete) :
      ConditionalDrop slot before .unwind after

theorem empty_drop_iff {slot : Nat} {before after : Concrete}
    {outcome : DropOutcome} (absent : ¬ before slot) :
    ConditionalDrop slot before outcome after ↔
      outcome = .silent ∧ after = before := by
  constructor
  · intro step
    cases step with
    | empty => exact ⟨rfl, rfl⟩
    | glue present => exact False.elim (absent present)
    | unwind present => exact False.elim (absent present)
  · rintro ⟨rfl, rfl⟩
    exact .empty absent

theorem accepted_drop_noop {g : Graph} (checked : accepted g = true)
    {index slot : Nat} {owns after : Concrete} {outcome : DropOutcome}
    (reached : Reachable g index owns)
    (candidate : (g.node index).candidateDrop = some slot) :
    ConditionalDrop slot (execute (g.node index).effects owns) outcome after ↔
      outcome = .silent ∧ after = execute (g.node index).effects owns :=
  empty_drop_iff (accepted_drop_empty checked reached candidate)

end AeneasSpecs.DropOwnership
