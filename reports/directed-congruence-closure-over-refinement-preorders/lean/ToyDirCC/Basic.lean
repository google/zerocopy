/-!
# Directed congruence closure over refinement preorders — basic definitions

This module fixes the toy setting shared by the whole package.

* `Term Op` — first-order terms over an operator type `Op` (variables are numbered).
* `Modality` — what an argument position of an operator lets a proof rewrite under:
  `mono` (refinement may be pushed through), `eqOnly` (only mutual refinement, i.e. the
  equality the proof system can establish, may be pushed through), `opaqueArg` (no
  congruence rule of the proof system applies; a proof relates two applications that differ
  at this position only through listed facts). Because a model interprets operators as
  functions on carrier values, arguments with *equal values* always give equal results, at
  every position; `opaqueArg` matters only in models with distinct mutually refining
  values.
* `Profile Op` — a modality for every operator and argument position.
* `Model Op` — a carrier with a binary relation `le` and an interpretation of every operator
  as a function on lists of carrier elements. `le x y` is read "`y` refines `x`": the
  relation is oriented from source to target, so a rewrite `s ⇝ t` is justified by
  `le ⟦s⟧ ⟦t⟧`.
* The model laws `LeRefl`, `LeTrans`, `MonoAt P`, `KerAt P` are separate named
  propositions so that each theorem names exactly the laws it uses.

Nothing here is specific to a compiler; the set-of-outcomes models of `ToyDirCC.Outcome`
are the intended compiler-flavoured instances.
-/

namespace Toy.DirCC

/-- First-order terms over the operator type `Op`. `var x` is the `x`-th variable;
`app f args` applies `f` to an argument list (no arity discipline is imposed: a model
interprets every operator on every list). Captures the syntax an e-graph stores. -/
inductive Term (Op : Type) where
  | var (x : Nat)
  | app (f : Op) (args : List (Term Op))

mutual
/-- Decidable equality of terms (written by hand: the term type is nested). -/
def Term.decEq {Op : Type} [DecidableEq Op] : (a b : Term Op) → Decidable (a = b)
  | .var x, .var y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .var _, .app _ _ => isFalse (by intro e; cases e)
  | .app _ _, .var _ => isFalse (by intro e; cases e)
  | .app f as, .app g bs =>
    if hf : f = g then
      match Term.decEqList as bs with
      | isTrue h => isTrue (by subst hf; subst h; rfl)
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hf rfl)
/-- Decidable equality of term lists. -/
def Term.decEqList {Op : Type} [DecidableEq Op] :
    (as bs : List (Term Op)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | a :: as, b :: bs =>
    match Term.decEq a b with
    | isTrue h1 =>
      match Term.decEqList as bs with
      | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
    | isFalse h1 => isFalse (by intro e; cases e; exact h1 rfl)
end

instance {Op : Type} [DecidableEq Op] : DecidableEq (Term Op) := Term.decEq

/-- The modality of one argument position.
* `mono`: the operator is monotone in this position for the refinement relation;
* `eqOnly`: the operator is only required to respect mutual refinement in this position;
* `opaqueArg`: no congruence law for the refinement relation is assumed for this position,
  and the proof system has no congruence rule for it. (Equal argument *values* still give
  equal results, because models interpret operators as functions.) -/
inductive Modality where
  | mono
  | eqOnly
  | opaqueArg
deriving Repr, DecidableEq

/-- A monotonicity profile: the modality of argument position `i` of operator `f`. -/
abbrev Profile (Op : Type) := Op → Nat → Modality

/-- A model: a carrier `C`, a binary relation `le` on it (`le x y`: "`y` refines `x`"),
and an interpretation of each operator as a function of its argument list. No law is
bundled; see `LeRefl`, `LeTrans`, `MonoAt`, `KerAt`. -/
structure Model (Op : Type) where
  C : Type
  le : C → C → Prop
  interp : Op → List C → C

variable {Op : Type}

mutual
/-- Evaluation of a term in a model under a valuation `ρ` of the variables. -/
def eval (M : Model Op) (ρ : Nat → M.C) : Term Op → M.C
  | .var x => ρ x
  | .app f args => M.interp f (evalList M ρ args)
/-- Pointwise evaluation of an argument list (equal to `List.map (eval M ρ)`,
see `evalList_eq_map`). -/
def evalList (M : Model Op) (ρ : Nat → M.C) : List (Term Op) → List M.C
  | [] => []
  | t :: ts => eval M ρ t :: evalList M ρ ts
end

theorem evalList_eq_map (M : Model Op) (ρ : Nat → M.C) (ts : List (Term Op)) :
    evalList M ρ ts = ts.map (eval M ρ) := by
  induction ts with
  | nil => simp [evalList]
  | cons t ts ih => simp [evalList, ih]

theorem eval_app (M : Model Op) (ρ : Nat → M.C) (f : Op) (args : List (Term Op)) :
    eval M ρ (.app f args) = M.interp f (args.map (eval M ρ)) := by
  simp [eval, evalList_eq_map]

/-! ## Reading one position of an argument list -/

theorem getD_hole_self {α : Type} (pre post : List α) (x d : α) :
    (pre ++ x :: post).getD pre.length d = x := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_hole_ne {α : Type} (pre post : List α) (x y d : α) {j : Nat}
    (h : j ≠ pre.length) : (pre ++ x :: post).getD j d = (pre ++ y :: post).getD j d := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_lt h)]
    obtain ⟨k, hk⟩ : ∃ k, j - pre.length = k + 1 := ⟨j - pre.length - 1, by omega⟩
    rw [hk]
    simp

/-! ## Model laws (each a separate proposition) -/

/-- Reflexivity of the refinement relation. -/
def LeRefl (M : Model Op) : Prop := ∀ x : M.C, M.le x x

/-- Transitivity of the refinement relation. -/
def LeTrans (M : Model Op) : Prop := ∀ x y z : M.C, M.le x y → M.le y z → M.le x z

/-- Every position that the profile declares `mono` is monotone in the model: refining one
argument (all other arguments fixed) refines the result. The position is `pre.length`. -/
def MonoAt (P : Profile Op) (M : Model Op) : Prop :=
  ∀ (f : Op) (pre post : List M.C) (x y : M.C), P f pre.length = .mono → M.le x y →
    M.le (M.interp f (pre ++ x :: post)) (M.interp f (pre ++ y :: post))

/-- Every position that the profile declares `eqOnly` respects mutual refinement (the
kernel `le x y ∧ le y x` of the relation, which is plain equality when `le` is
antisymmetric). The position is `pre.length`. -/
def KerAt (P : Profile Op) (M : Model Op) : Prop :=
  ∀ (f : Op) (pre post : List M.C) (x y : M.C), P f pre.length = .eqOnly → M.le x y →
    M.le y x → M.le (M.interp f (pre ++ x :: post)) (M.interp f (pre ++ y :: post))

/-! ## Examples for the laws -/

/-- A one-operator signature used for small examples. -/
inductive UOp where
  | succ
deriving Repr, DecidableEq

/-- `Nat` with `≤` and `succ` interpreted as `+1` (missing argument read as `0`). -/
abbrev natLeModel : Model UOp where
  C := Nat
  le := (· ≤ ·)
  interp := fun _ args => args.headD 0 + 1

/-- `Nat` with strict `<`. -/
abbrev natLtModel : Model UOp where
  C := Nat
  le := (· < ·)
  interp := fun _ args => args.headD 0 + 1

/-- `Nat` with "differs by at most one". -/
abbrev natNearModel : Model UOp where
  C := Nat
  le := fun x y => x ≤ y + 1 ∧ y ≤ x + 1
  interp := fun _ args => args.headD 0 + 1

/-- Positive example: `≤` on `Nat` is reflexive. -/
theorem natLeModel_refl : LeRefl natLeModel := fun x => Nat.le_refl x

/-- Negative example: `<` on `Nat` is not reflexive. -/
theorem natLtModel_not_refl : ¬ LeRefl natLtModel := fun h => Nat.lt_irrefl 0 (h 0)

/-- Positive example: `≤` on `Nat` is transitive. -/
theorem natLeModel_trans : LeTrans natLeModel := fun _ _ _ h1 h2 => Nat.le_trans h1 h2

/-- Negative example: "differs by at most one" is not transitive (`0 ~ 1 ~ 2`, not `0 ~ 2`). -/
theorem natNearModel_not_trans : ¬ LeTrans natNearModel := by
  intro h
  have := h 0 1 2 (by decide) (by decide)
  exact absurd this (by decide)

/-- The profile declaring every position monotone. -/
def allMono (Op : Type) : Profile Op := fun _ _ => .mono

/-- The profile declaring every position opaque. -/
def allOpaque (Op : Type) : Profile Op := fun _ _ => .opaqueArg

/-- Any model satisfies `MonoAt` and `KerAt` for the all-opaque profile (no obligations). -/
theorem monoAt_allOpaque (M : Model Op) : MonoAt (allOpaque Op) M := by
  intro _ _ _ _ _ h; cases h

theorem kerAt_allOpaque (M : Model Op) : KerAt (allOpaque Op) M := by
  intro _ _ _ _ _ h; cases h

/-- Any model satisfies `KerAt` for the all-monotone profile (no `eqOnly` positions). -/
theorem kerAt_allMono (M : Model Op) : KerAt (allMono Op) M := by
  intro _ _ _ _ _ h; cases h

example : (Term.app UOp.succ [.var 0] : Term UOp) ≠ .app .succ [.var 1] := by decide

end Toy.DirCC
