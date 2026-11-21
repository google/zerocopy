import ToyUnify.Term

/-!
# Unifiers and the unification algorithm

* `Unifies σ s t`, `Unifiable s t`, `Idempotent σ`, `MoreGeneral σ τ` (the instance preorder).
* A Martelli–Montanari-style algorithm in solved form (the naive equation-transformation rules,
  with eager substitution, not the multiequation algorithm): each pass decomposes all pending
  equations into variable bindings (`decompAll`), then eliminates the first binding `x ↦ u`,
  substituting `u` for `x` in the remaining bindings and in the right-hand sides of the
  accumulated substitution. `decomp` drops trivial equations `x =? x`, so the occurs check is
  never applied to a binding `x ↦ x`. The flag `oc` switches the occurs check on (`unify`) or off (`unifyNoOC`);
  nothing else differs.
* Fuel counts variable eliminations; `unify` runs with fuel equal to the number of distinct
  variables of the input (`numVars`), which is the termination measure.
-/

namespace Toy.Unify

/-! ## Unifiers -/

/-- `σ` unifies `s` and `t`: both sides become syntactically equal (finite terms). -/
def Unifies (σ : Subst) (s t : Term) : Prop := subst σ s = subst σ t

instance (σ : Subst) (s t : Term) : Decidable (Unifies σ s t) :=
  inferInstanceAs (Decidable (subst σ s = subst σ t))

/-- `s` and `t` have a unifier over finite terms. -/
def Unifiable (s t : Term) : Prop := ∃ σ : Subst, Unifies σ s t

/-- `σ` is idempotent: applying it twice is the same as applying it once. -/
def Idempotent (σ : Subst) : Prop := ∀ t : Term, subst σ (subst σ t) = subst σ t

/-- The instance preorder: `MoreGeneral σ τ` holds when `τ` factors through `σ`, i.e.
`τ = ρ ∘ σ` on every term for some substitution `ρ` ("`τ` is an instance of `σ`"). -/
def MoreGeneral (σ τ : Subst) : Prop := ∃ ρ : Subst, ∀ t : Term, subst τ t = subst ρ (subst σ t)

/-! ## Decomposition -/

mutual
/-- Decompose one equation `s =? t` into variable bindings, or `none` on a constructor clash
(different symbols or different argument counts). `var x =? var x` is dropped and
`t =? var x` (with `t` not a variable) is oriented to `x ↦ t`. -/
def decomp : Term → Term → Option (List (Nat × Term))
  | .var x, .var y => if x = y then some [] else some [(x, .var y)]
  | .var x, .con g ts => some [(x, .con g ts)]
  | .con f ss, .var x => some [(x, .con f ss)]
  | .con f ss, .con g ts => if f = g then decompList ss ts else none
/-- Decompose the pointwise equations of two argument lists (companion of `decomp`). -/
def decompList : List Term → List Term → Option (List (Nat × Term))
  | [], [] => some []
  | s :: ss, t :: ts =>
    match decomp s t, decompList ss ts with
    | some a, some b => some (a ++ b)
    | _, _ => none
  | _, _ => none
end

/-- Decompose a list of equations. -/
def decompAll : List (Term × Term) → Option (List (Nat × Term))
  | [] => some []
  | (s, t) :: es =>
    match decomp s t, decompAll es with
    | some a, some b => some (a ++ b)
    | _, _ => none

/-! ## The algorithm -/

/-- Outcome of a run: a substitution, a failure (clash or occurs-check failure), or exhaustion
of the fuel. -/
inductive Result where
  | ok (σ : Subst)
  | fail
  | outOfFuel
  deriving Repr, DecidableEq

/-- Read a result as an optional substitution (`fail` and `outOfFuel` both become `none`). -/
def Result.toOption : Result → Option Subst
  | .ok σ => some σ
  | _ => none

/-- One pass's outcome: finished, or a new equation list and accumulated substitution. -/
inductive Step where
  | done (r : Result)
  | next (eqs : List (Term × Term)) (σ : Subst)

/-- Substitute `u` for `x` in a pending binding, turning it back into an equation. -/
def elimBinding (x : Nat) (u : Term) (b : Nat × Term) : Term × Term :=
  (subst [(x, u)] (.var b.1), subst [(x, u)] b.2)

/-- One pass: decompose all pending equations; if no binding remains, succeed with the solved
substitution `σ`; otherwise eliminate the first binding `x ↦ u` (failing first if `oc` is set
and `x` occurs in `u`). -/
def step (oc : Bool) (eqs : List (Term × Term)) (σ : Subst) : Step :=
  match decompAll eqs with
  | none => .done .fail
  | some [] => .done (.ok σ)
  | some ((x, u) :: bs) =>
    if oc && occurs x u then .done .fail
    else .next (bs.map (elimBinding x u)) ((x, u) :: σ.map (fun p => (p.1, subst [(x, u)] p.2)))

/-- Run passes until done; each elimination consumes one unit of fuel. -/
def run (oc : Bool) (fuel : Nat) (eqs : List (Term × Term)) (σ : Subst) : Result :=
  match step oc eqs σ with
  | .done r => r
  | .next eqs' σ' =>
    match fuel with
    | 0 => .outOfFuel
    | n + 1 => run oc n eqs' σ'

/-- The variables of an equation list. -/
def eqsVars (eqs : List (Term × Term)) : List Nat :=
  eqs.flatMap (fun e => e.1.vars ++ e.2.vars)

/-- The termination measure: the number of distinct variables of an equation list. -/
def numVars (eqs : List (Term × Term)) : Nat := (eqsVars eqs).eraseDups.length

/-- Syntactic unification with the occurs check: run with fuel `numVars [(s, t)]` from the
empty accumulated substitution. -/
def unify (s t : Term) : Option Subst :=
  (run true (numVars [(s, t)]) [(s, t)] []).toOption

/-- The same algorithm with the occurs check removed (and the same fuel). -/
def unifyNoOC (s t : Term) : Option Subst :=
  (run false (numVars [(s, t)]) [(s, t)] []).toOption

/-! ## Depth-indexed comparison (finite approximation of infinite-tree equality) -/

mutual
/-- `eqUpTo n a b`: `a` and `b` have the same variables and constructor symbols (with the same
argument counts) at every position of depth `< n`. Positions at depth `≥ n` are not compared. -/
def eqUpTo : Nat → Term → Term → Bool
  | 0, _, _ => true
  | _ + 1, .var x, .var y => x == y
  | n + 1, .con f ss, .con g ts => f == g && eqUpToList n ss ts
  | _ + 1, _, _ => false
/-- List companion of `eqUpTo`: same length and pointwise `eqUpTo n`. -/
def eqUpToList : Nat → List Term → List Term → Bool
  | _, [], [] => true
  | n, s :: ss, t :: ts => eqUpTo n s t && eqUpToList n ss ts
  | _, _, _ => false
end

end Toy.Unify
