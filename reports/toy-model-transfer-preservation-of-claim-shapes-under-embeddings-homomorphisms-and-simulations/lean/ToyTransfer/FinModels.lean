import ToyTransfer.Maps

/-!
# Concrete finite structures, maps and formulas used by the countermodels

Every structure has between one and three elements (none is empty). Maps are typed by their source and target
structures, so laws such as `PreservesR m` determine both structures.
-/

namespace Toy.Transfer

/-! ## Structures -/

/-- One element; `P` holds of it; `R` is empty. -/
def S1P : FinStr 1 := ⟨fun _ _ => false, fun _ => true⟩
/-- One element; `P` and `R` are empty. -/
def S1N : FinStr 1 := ⟨fun _ _ => false, fun _ => false⟩
/-- One element related to itself by `R`; `P` is empty. -/
def S1R : FinStr 1 := ⟨fun _ _ => true, fun _ => false⟩
/-- Two elements; `P` holds of `0` only; `R` is empty. -/
def S2PN : FinStr 2 := ⟨fun _ _ => false, fun a => a.val == 0⟩
/-- Two elements; `P` holds of `1` only; `R` is empty. -/
def S2NP : FinStr 2 := ⟨fun _ _ => false, fun a => a.val == 1⟩
/-- Two elements; `P` and `R` are empty. -/
def S2E : FinStr 2 := ⟨fun _ _ => false, fun _ => false⟩
/-- Two elements; `R` relates each element to the other (and not to itself); `P` empty. -/
def S2Cyc : FinStr 2 := ⟨fun a b => a.val != b.val, fun _ => false⟩
/-- Two elements; `R` holds of `(0, 1)` only; `P` empty. -/
def S2R01 : FinStr 2 := ⟨fun a b => a.val == 0 && b.val == 1, fun _ => false⟩
/-- Two elements; `P` holds of both; `R` is empty. -/
def S2PP : FinStr 2 := ⟨fun _ _ => false, fun _ => true⟩
/-- Two elements; `R` holds of `(0, 1)` and `(1, 1)` (every element has an `R`-successor,
only `1` has a loop); `P` empty. -/
def S2Loop1 : FinStr 2 := ⟨fun _ b => b.val == 1, fun _ => false⟩
/-- One element; `P` holds of it and `R` relates it to itself. -/
def S1Full : FinStr 1 := ⟨fun _ _ => true, fun _ => true⟩
/-- Three elements; `P` and `R` are empty. -/
def S3E : FinStr 3 := ⟨fun _ _ => false, fun _ => false⟩

/-! ## Maps -/

/-- `S1P → S2PN`, `0 ↦ 0` (an embedding onto the `P`-point). -/
def inclPN : S1P.toStr.carrier → S2PN.toStr.carrier := fun _ => 0
/-- `S1N → S2NP`, `0 ↦ 0` (an embedding onto the non-`P` point). -/
def inclNP : S1N.toStr.carrier → S2NP.toStr.carrier := fun _ => 0
/-- `S1N → S2Cyc`, `0 ↦ 0` (an embedding onto one point of the 2-cycle). -/
def inclCyc : S1N.toStr.carrier → S2Cyc.toStr.carrier := fun _ => 0
/-- `S1N → S1P`, identity on the carrier (makes `P` true). -/
def raiseP : S1N.toStr.carrier → S1P.toStr.carrier := id
/-- `S1P → S1N`, identity on the carrier (makes `P` false). -/
def lowerP : S1P.toStr.carrier → S1N.toStr.carrier := id
/-- `S1N → S1R`, identity on the carrier (makes `R` true). -/
def raiseR : S1N.toStr.carrier → S1R.toStr.carrier := id
/-- `S1R → S1N`, identity on the carrier (makes `R` false). -/
def lowerR : S1R.toStr.carrier → S1N.toStr.carrier := id
/-- `S2E → S2R01`, identity on the carrier (adds the edge `(0, 1)`). -/
def addEdge : S2E.toStr.carrier → S2R01.toStr.carrier := id
/-- `S2E → S1N`, collapses both points to `0`. -/
def collapse : S2E.toStr.carrier → S1N.toStr.carrier := fun _ => 0
/-- `S1P → S2PP`, `0 ↦ 0` (an embedding into a two-point structure where `P` holds
everywhere). -/
def inclPP : S1P.toStr.carrier → S2PP.toStr.carrier := fun _ => 0
/-- `S1P → S2NP`, `0 ↦ 1` (an embedding onto the `P`-point). -/
def inclP1 : S1P.toStr.carrier → S2NP.toStr.carrier := fun _ => 1
/-- `S1N → S2PN`, `0 ↦ 1` (an embedding onto the non-`P` point). -/
def inclN1 : S1N.toStr.carrier → S2PN.toStr.carrier := fun _ => 1
/-- `S2E → S2PN`, collapses both points to the non-`P` point `1`. -/
def collapseTo1 : S2E.toStr.carrier → S2PN.toStr.carrier := fun _ => 1
/-- `S1R → S2Loop1`, `0 ↦ 1` (an embedding onto the looped point). -/
def inclLoop : S1R.toStr.carrier → S2Loop1.toStr.carrier := fun _ => 1
/-- `S1N → S2Loop1`, `0 ↦ 0` (an embedding onto the unlooped point). -/
def inclNoLoop : S1N.toStr.carrier → S2Loop1.toStr.carrier := fun _ => 0
/-- `S2E → S3E`, `i ↦ i` (an embedding missing the point `2`). -/
def inclE23 : S2E.toStr.carrier → S3E.toStr.carrier := fun a => ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩
/-- `S2PP → S1P`, collapses both points to `0`. -/
def squashPP : S2PP.toStr.carrier → S1P.toStr.carrier := fun _ => 0

/-! ## Formulas (de Bruijn: under `∀x ∀y`, `y` is index 0 and `x` is index 1) -/

/-- `∀x, P x`. -/
def allP : Fml 0 := .all (.pred 0)
/-- `∃x, P x`. -/
def exP : Fml 0 := .ex (.pred 0)
/-- `∀x ∃y, R x y`. -/
def allExR : Fml 0 := .all (.ex (.rel 1 0))
/-- `∃x, ¬ P x`. -/
def exNotP : Fml 0 := .ex (.neg (.pred 0))
/-- `∀x ∀y, R x y → x = y`. -/
def allRImpEq : Fml 0 := .all (.all (Fml.imp (.rel 1 0) (.eq 1 0)))
/-- `∃x ∃y, ¬ x = y`. -/
def exExNeq : Fml 0 := .ex (.ex (.neg (.eq 1 0)))
/-- `∀x ∀y, x = y`. -/
def allAllEq : Fml 0 := .all (.all (.eq 1 0))
/-- `∀x, ¬ R x x`. -/
def allNotRxx : Fml 0 := .all (.neg (.rel 0 0))
/-- `∀x, ¬ P x`. -/
def allNotP : Fml 0 := .all (.neg (.pred 0))
/-- `∀x, R x x`. -/
def allRxx : Fml 0 := .all (.rel 0 0)
/-- `∃x, R x x`. -/
def exRxx : Fml 0 := .ex (.rel 0 0)
/-- `∃x, ¬ R x x`. -/
def exNotRxx : Fml 0 := .ex (.neg (.rel 0 0))
/-- `∀x ∀y, x = y ∨ P x ∨ P y` (at most one element outside `P`). -/
def atMostOneNotP : Fml 0 := .all (.all (.or (.eq 1 0) (.or (.pred 1) (.pred 0))))
/-- `(∃x, P x) ∧ (∃y, P y)` (positive existential, not prenex). -/
def exPAndExP : Fml 0 := .and (.ex (.pred 0)) (.ex (.pred 0))
/-- `P x₀` (one free variable). -/
def P0 : Fml 1 := .pred 0
/-- `¬ P x₀` (one free variable). -/
def notP0 : Fml 1 := .neg (.pred 0)
/-- `x₀ = x₁` (two free variables). -/
def eq01 : Fml 2 := .eq 0 1
/-- `¬ x₀ = x₁` (two free variables). -/
def neq01 : Fml 2 := .neg (.eq 0 1)

/-- The environment `x₀ ↦ a`. -/
def env1 {α : Type} (a : α) : Fin 1 → α := Env.cons a Fin.elim0
/-- The environment `x₀ ↦ a, x₁ ↦ b`. -/
def env2 {α : Type} (a b : α) : Fin 2 → α := Env.cons a (Env.cons b Fin.elim0)

end Toy.Transfer
