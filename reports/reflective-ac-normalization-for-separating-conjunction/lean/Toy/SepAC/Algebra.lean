/-!
# Algebraic Laws and Model Instances for Separating Conjunction

Unbundled algebraic laws for a binary operation `sep : P → P → P` and a distinguished
element `emp : P`, together with small concrete algebras used as positive examples,
negative examples, and canonical tightness counterexamples.

Every law is an independent `Prop` so each theorem names only the exact algebraic
hypotheses it requires.
-/

namespace Toy.SepAC

universe u

/-! ## Unbundled algebraic laws -/

/-- Associativity of separating conjunction: `(x ∗ y) ∗ z = x ∗ (y ∗ z)`.
Captures re-parenthesization invariance of spatial conjunctions. -/
def SepAssoc {P : Type u} (sep : P → P → P) : Prop :=
  ∀ x y z : P, sep (sep x y) z = sep x (sep y z)

/-- Commutativity of separating conjunction: `x ∗ y = y ∗ x`.
Captures order-insensitivity of disjoint spatial conjunctions. -/
def SepComm {P : Type u} (sep : P → P → P) : Prop :=
  ∀ x y : P, sep x y = sep y x

/-- Left unit law: `emp ∗ x = x`.
Captures left elimination of the empty heap assertion `emp`. -/
def LeftUnit {P : Type u} (sep : P → P → P) (emp : P) : Prop :=
  ∀ x : P, sep emp x = x

/-- Right unit law: `x ∗ emp = x`.
Captures right elimination of the empty heap assertion `emp` and terminates
right-nested normal-form folds (`foldr sep emp`). -/
def RightUnit {P : Type u} (sep : P → P → P) (emp : P) : Prop :=
  ∀ x : P, sep x emp = x

/-- Pointwise idempotence of a single element `x` under `sep`: `x ∗ x = x`.
Models an element that is idempotent as a propositional equality, such as a unit `emp` or
the absorbing `conflict` of `CellModel`; whether pure or persistent assertions of a real
logic satisfy it (they are at best `P ∗ P ⊣⊢ P`) is not established here. -/
def IdemElem {P : Type u} (sep : P → P → P) (x : P) : Prop :=
  sep x x = x

/-- Global idempotence of `sep`: `∀ x, x ∗ x = x` (every assertion is duplicable, as for
intuitionistic conjunction `∧`). Separation logics with exclusive ownership never satisfy
global `SepIdem`; only individual assertions satisfy `IdemElem`. -/
def SepIdem {P : Type u} (sep : P → P → P) : Prop :=
  ∀ x : P, sep x x = x

/-! ## Derived algebraic lemmas -/

/-- Under commutativity, `LeftUnit` is derivable from `RightUnit`, so reflective ACU
theorems need not assume both unit laws independently. -/
theorem leftUnit_of_comm_of_rightUnit {P : Type u} {sep : P → P → P} {emp : P}
    (hComm : SepComm sep) (hRight : RightUnit sep emp) :
    LeftUnit sep emp := by
  intro x
  rw [hComm emp x]
  exact hRight x

/-- Symmetrically, `RightUnit` is derivable from `SepComm` and `LeftUnit`. -/
theorem rightUnit_of_comm_of_leftUnit {P : Type u} {sep : P → P → P} {emp : P}
    (hComm : SepComm sep) (hLeft : LeftUnit sep emp) :
    RightUnit sep emp := by
  intro x
  rw [hComm x emp]
  exact hLeft x

/-- Every commutative unital magma on a carrier of cardinality at most `2`
(`∀ x : P, x = a ∨ x = b`) is automatically associative. Consequently, a 3-element
carrier (`NonAssocCarrier`) has the minimum possible size for a non-associative
commutative unital countermodel. -/
theorem atMostTwo_comm_unital_sepAssoc {P : Type u} (a b : P)
    (hTwo : ∀ x : P, x = a ∨ x = b)
    (op : P → P → P) (e : P)
    (hComm : SepComm op) (hRight : RightUnit op e) :
    SepAssoc op := by
  have hLeft : LeftUnit op e := leftUnit_of_comm_of_rightUnit hComm hRight
  intro x y z
  rcases hTwo e with he | he
  · subst he
    rcases hTwo x with hx | hx <;> subst hx
    · rw [hLeft, hLeft]
    · rcases hTwo y with hy | hy <;> subst hy
      · rw [hRight, hLeft]
      · rcases hTwo z with hz | hz <;> subst hz
        · rw [hRight, hRight]
        · exact hComm (op _ _) _
  · subst he
    rcases hTwo x with hx | hx <;> subst hx
    · rcases hTwo y with hy | hy <;> subst hy
      · rcases hTwo z with hz | hz <;> subst hz
        · exact hComm (op _ _) _
        · rw [hRight, hRight]
      · rw [hRight, hLeft]
    · rw [hLeft, hLeft]

/-- Specialization of `atMostTwo_comm_unital_sepAssoc` to `Bool`. -/
theorem bool_comm_unital_sepAssoc (op : Bool → Bool → Bool) (e : Bool)
    (hComm : SepComm op) (hRight : RightUnit op e) :
    SepAssoc op :=
  atMostTwo_comm_unital_sepAssoc false true
    (fun x => by cases x <;> simp) op e hComm hRight

/-! ## Concrete algebras for examples and counterexamples -/

/-- Minimal 3-element carrier admitting a commutative, two-sided unital,
non-associative binary operation (minimality proved by `atMostTwo_comm_unital_sepAssoc`). -/
inductive NonAssocCarrier where
  | emp
  | a
  | b
  deriving DecidableEq, Repr

/-- Commutative binary operation with two-sided unit `.emp` on `NonAssocCarrier`
that fails associativity: `(a ⋆ a) ⋆ b = b ⋆ b = b`, whereas `a ⋆ (a ⋆ b) = a ⋆ emp = a`. -/
def NonAssocCarrier.op : NonAssocCarrier → NonAssocCarrier → NonAssocCarrier
  | .emp, y => y
  | x, .emp => x
  | .a, .a => .b
  | .b, .b => .b
  | .a, .b => .emp
  | .b, .a => .emp

/-- Left-projection operation `x ⋆ y = x`: associative and has every `emp` as a right unit,
but fails `LeftUnit` on any carrier with at least two elements. -/
def leftProj {P : Type u} (x _ : P) : P := x

/-- Right-projection operation `x ⋆ y = y`: associative and has every `emp` as a left unit,
but fails `RightUnit` on any carrier with at least two elements. -/
def rightProj {P : Type u} (_ y : P) : P := y

/-- Three-state single-cell heap assertion carrier: `conflict` (unsatisfiable / overlapping
ownership), `empty` (the empty heap assertion `emp`), and `owned` (exclusive ownership of
the single cell). -/
inductive CellModel where
  | conflict
  | empty
  | owned
  deriving DecidableEq, Repr

/-- Separating composition on `CellModel`: `empty` is the unit, `owned ∗ owned = conflict`,
and `conflict` is absorbing. Captures disjoint single-cell ownership where duplicating a
points-to assertion collapses to unsatisfiability (`False`). -/
def CellModel.sep : CellModel → CellModel → CellModel
  | .empty, y => y
  | x, .empty => x
  | .owned, .owned => .conflict
  | .conflict, _ => .conflict
  | _, .conflict => .conflict

/-- Five-state two-cell heap assertion carrier: `conflict` (overlapping ownership / `False`),
`empty` (no cells), `cellA` (exclusive ownership of cell 0), `cellB` (exclusive ownership of
cell 1), and `both` (disjoint ownership of both cells). Captures multi-location separation
needed for affine converse-failure and distinct-atom conflict witnesses. -/
inductive TwoCellModel where
  | conflict
  | empty
  | cellA
  | cellB
  | both
  deriving DecidableEq, Repr

/-- Disjoint union on `TwoCellModel`: `empty` is the unit, `cellA ∗ cellB = both`, and any
overlapping composition yields the absorbing `conflict` element. -/
def TwoCellModel.sep : TwoCellModel → TwoCellModel → TwoCellModel
  | .empty, y => y
  | x, .empty => x
  | .cellA, .cellB => .both
  | .cellB, .cellA => .both
  | _, _ => .conflict

/-! ## Positive and negative examples for every law and carrier operation -/

theorem natAdd_sepAssoc : SepAssoc Nat.add := by
  intro x y z
  exact Nat.add_assoc x y z

theorem listAppend_sepAssoc : SepAssoc (@List.append Nat) := by
  intro x y z
  exact List.append_assoc x y z

theorem nonAssocOp_not_sepAssoc : ¬ SepAssoc NonAssocCarrier.op := by
  intro h
  have h1 := h .a .a .b
  cases h1

theorem natAdd_sepComm : SepComm Nat.add := by
  intro x y
  exact Nat.add_comm x y

theorem nonAssocOp_sepComm : SepComm NonAssocCarrier.op := by
  intro x y
  cases x <;> cases y <;> rfl

theorem listAppend_not_sepComm : ¬ SepComm (@List.append Nat) := by
  intro h
  have h1 := h [0] [1]
  cases h1

theorem listAppend_leftUnit : LeftUnit (@List.append Nat) [] := by
  intro x
  rfl

theorem rightProj_leftUnit : LeftUnit (@rightProj Bool) false := by
  intro x
  rfl

theorem leftProj_not_leftUnit : ¬ LeftUnit (@leftProj Bool) false := by
  intro h
  have h1 := h true
  cases h1

theorem boolAndFalse_not_leftUnit : ¬ LeftUnit Bool.and false := by
  intro h
  have h1 := h true
  cases h1

theorem listAppend_rightUnit : RightUnit (@List.append Nat) [] := by
  intro x
  exact List.append_nil x

theorem nonAssocOp_rightUnit : RightUnit NonAssocCarrier.op .emp := by
  intro x
  cases x <;> rfl

theorem leftProj_rightUnit : RightUnit (@leftProj Bool) false := by
  intro x
  rfl

theorem rightProj_not_rightUnit : ¬ RightUnit (@rightProj Bool) false := by
  intro h
  have h1 := h true
  cases h1

theorem boolAndFalse_not_rightUnit : ¬ RightUnit Bool.and false := by
  intro h
  have h1 := h true
  cases h1

theorem boolAnd_sepAssoc : SepAssoc Bool.and := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl

theorem boolAnd_sepComm : SepComm Bool.and := by
  intro x y
  cases x <;> cases y <;> rfl

theorem boolAndTrue_rightUnit : RightUnit Bool.and true := by
  intro x
  cases x <;> rfl

theorem boolOr_sepAssoc : SepAssoc Bool.or := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl

theorem boolOr_sepComm : SepComm Bool.or := by
  intro x y
  cases x <;> cases y <;> rfl

theorem boolOr_rightUnit : RightUnit Bool.or false := by
  intro x
  cases x <;> rfl

theorem cellModel_conflict_idemElem : IdemElem CellModel.sep .conflict := rfl

theorem natAdd_zero_idemElem : IdemElem Nat.add 0 := rfl

theorem cellModel_owned_not_idemElem : ¬ IdemElem CellModel.sep .owned := by
  intro h
  cases h

theorem boolOr_sepIdem : SepIdem Bool.or := by
  intro x
  cases x <;> rfl

theorem natAdd_not_sepIdem : ¬ SepIdem Nat.add := by
  intro h
  have h1 := h 1
  cases h1

theorem cellModel_sepAssoc : SepAssoc CellModel.sep := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl

theorem cellModel_sepComm : SepComm CellModel.sep := by
  intro x y
  cases x <;> cases y <;> rfl

theorem cellModel_rightUnit : RightUnit CellModel.sep .empty := by
  intro x
  cases x <;> rfl

theorem cellModel_not_sepIdem : ¬ SepIdem CellModel.sep := by
  intro h
  have h1 := h .owned
  cases h1

theorem twoCellModel_sepAssoc : SepAssoc TwoCellModel.sep := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl

theorem twoCellModel_sepComm : SepComm TwoCellModel.sep := by
  intro x y
  cases x <;> cases y <;> rfl

theorem twoCellModel_rightUnit : RightUnit TwoCellModel.sep .empty := by
  intro x
  cases x <;> rfl

theorem twoCellModel_not_sepIdem : ¬ SepIdem TwoCellModel.sep := by
  intro h
  have h1 := h .cellA
  cases h1

theorem cellModel_pos_example : CellModel.sep .empty .owned = .owned := rfl

theorem cellModel_neg_example : CellModel.sep .owned .owned ≠ .owned := by decide

theorem twoCellModel_pos_example : TwoCellModel.sep .cellA .cellB = .both := rfl

theorem twoCellModel_neg_example : TwoCellModel.sep .cellA .cellA ≠ .cellA := by decide

theorem nonAssocOp_pos_example : NonAssocCarrier.op .a .emp = .a := rfl

theorem nonAssocOp_neg_example :
    NonAssocCarrier.op (NonAssocCarrier.op .a .a) .b ≠
      NonAssocCarrier.op .a (NonAssocCarrier.op .a .b) := by
  decide

theorem leftProj_pos_example : leftProj true false = true := rfl

theorem leftProj_neg_example : leftProj false true ≠ true := by decide

theorem rightProj_pos_example : rightProj false true = true := rfl

theorem rightProj_neg_example : rightProj true false ≠ true := by decide

end Toy.SepAC
