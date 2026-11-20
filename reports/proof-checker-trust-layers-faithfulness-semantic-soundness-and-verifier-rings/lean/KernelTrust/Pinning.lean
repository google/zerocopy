/-
  Toy.KernelTrust.Pinning

  Statement pinning.  A checker checks a *formula*; a human reads a *name*.  The
  meaning of a name is given by a statement table (a "prelude").  `Pinned`
  compares the table shipped with a proof against an official table.
-/
import KernelTrust.Cert

namespace Toy.KernelTrust

/-- A statement table ("prelude"): a finite association list from names to
formulas.  The first binding of a name wins (`List.lookup`). -/
abbrev StmtTable := List (String × Form)

/-- Name-level acceptance: resolve `name` in the table `P` that accompanies the
proof, then run the checker on the resolved formula (in the empty context).
Unresolvable names are rejected. -/
def Checker.acceptsNamed (C : Checker) (P : StmtTable) (w : C.Wit) (name : String) : Bool :=
  match P.lookup name with
  | some φ => C.accepts w [] φ
  | none   => false

/-- **Statement pinning.**  `Pinned official P name`: the name is defined in the
official table, and the submitted table `P` resolves it to the *same* formula.

Pinning is a comparison of statements, performed outside the checker; it says
nothing about proofs. -/
def Pinned (official P : StmtTable) (name : String) : Prop :=
  ∃ φ, official.lookup name = some φ ∧ P.lookup name = some φ

/-- Executable characterisation of `Pinned`, used for the `Decidable` instance:
a judge can *compute* whether a submitted table is pinned. -/
theorem pinned_iff (official P : StmtTable) (name : String) :
    Pinned official P name ↔
      ((official.lookup name).isSome = true ∧ P.lookup name = official.lookup name) := by
  constructor
  · rintro ⟨φ, h1, h2⟩
    simp [h1, h2]
  · rintro ⟨h1, h2⟩
    cases h : official.lookup name with
    | none => simp [h] at h1
    | some φ => exact ⟨φ, h, by rw [h2, h]⟩

/-- `Pinned` is decidable: whoever holds the official table can compute it. -/
instance (official P : StmtTable) (name : String) : Decidable (Pinned official P name) :=
  decidable_of_iff _ (pinned_iff official P name).symm

/-- The official statement table of the running example: the name `"False"`
means `⊥`, the name `"True"` means `⊥ → ⊥`. -/
def officialTable : StmtTable := [("False", .bot), ("True", Form.top)]

/-- A poisoned prelude: it *renames*, mapping `"False"` to the provable
formula `⊥ → ⊥`. -/
def poisonedTable : StmtTable := [("False", Form.top), ("True", Form.top)]

/-- **What pinning buys** (given a faithful checker for consistent rules; no
semantics needed): a pinned name whose official meaning is `⊥` is never
accepted. -/
theorem not_acceptsNamed_of_pinned_bot {C : Checker} {R : RuleSet}
    (hF : Faithful C R) (hC : Consistent R)
    {official P : StmtTable} {name : String}
    (hOff : official.lookup name = some .bot) (hPin : Pinned official P name)
    (w : C.Wit) : C.acceptsNamed P w name = false := by
  obtain ⟨φ, h1, h2⟩ := hPin
  rw [hOff] at h1
  cases h1
  cases hacc : C.acceptsNamed P w name
  · rfl
  · exfalso
    simp only [Checker.acceptsNamed, h2] at hacc
    exact hC (hF w [] .bot hacc)

/-! ## Examples for the definitions above -/

/-- Positive example (`Pinned`): the official table is pinned to itself on
`"False"`. -/
theorem ex_pinned_official_pos : Pinned officialTable officialTable "False" := by decide

/-- Negative example (`Pinned`): the poisoned table is not pinned on `"False"`. -/
theorem ex_pinned_poisoned_neg : ¬ Pinned officialTable poisonedTable "False" := by decide

/-- Positive example (`Pinned`): the poisoned table *is* pinned on `"True"`;
pinning is per name. -/
theorem ex_pinned_poisoned_true_pos : Pinned officialTable poisonedTable "True" := by decide

/-- Negative example (`Pinned`): a name that the official table does not define
is never pinned, even if both tables agree on it. -/
theorem ex_pinned_undefined_neg : ¬ Pinned officialTable officialTable "Undefined" := by decide

/-- Positive example (`Checker.acceptsNamed`): with the official table, the name
`"True"` is accepted on the certificate `topCert`. -/
theorem ex_acceptsNamed_pos :
    (recheckRecompute stdRules).acceptsNamed officialTable topCert "True" = true := by decide

/-- Negative example (`Checker.acceptsNamed`): an undefined name is rejected. -/
theorem ex_acceptsNamed_neg :
    (recheckRecompute stdRules).acceptsNamed officialTable topCert "Undefined" = false := by
  decide

end Toy.KernelTrust
