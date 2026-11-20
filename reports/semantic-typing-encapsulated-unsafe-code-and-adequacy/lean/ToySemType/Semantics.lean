import ToySemType.Syntax

/-!
# Small-step operational semantics, stuckness, and safety

A deterministic small-step semantics given as a partial function
`step : Expr → Heap → Option (Expr × Heap)`. The heap is a list of words;
addresses are list indices. Allocation appends, so the heap never shrinks.
A configuration is *stuck* when its expression is not a value and `step`
returns `none`: this is how undefined behavior (a read or write through an
invalid reference, applying a non-function, a free variable, ...) shows up.
-/

namespace Toy.SemType

open Expr

/-- The heap: cell `l` holds the word `h[l]`; valid addresses are `l < h.length`. -/
abbrev Heap := List Nat

/-- A machine configuration: the expression being evaluated and the heap. -/
abbrev Config := Expr × Heap

/-- One step of left-to-right call-by-value evaluation, or `none` if the
configuration is a value or stuck.

Primitive rules (all other cases are congruences or `none`):
* `app (lam b) v ⟶ substAt 0 v b` for a value `v`;
* `lt (num a) (num b) ⟶ num (if a < b then 1 else 0)`;
* `ifz (num 0) t e ⟶ t`, `ifz (num (k+1)) t e ⟶ e`;
* `size, h ⟶ num h.length, h`;
* `alloc (num n), h ⟶ loc h.length, h ++ [n]`;
* `read (loc l), h ⟶ num h[l], h` if `l < h.length` (otherwise stuck);
* `write (loc l) (num n), h ⟶ num 0, h.set l n` if `l < h.length` (otherwise stuck);
* `cast (num n) ⟶ loc n` (no check: this is the unsafe primitive). -/
def step : Expr → Heap → Option Config
  | .app f a, h =>
    if f.isValue then
      if a.isValue then
        match f with
        | .lam b => some (substAt 0 a b, h)
        | _ => none
      else (step a h).map fun c => (.app f c.1, c.2)
    else (step f h).map fun c => (.app c.1 a, c.2)
  | .lt a b, h =>
    if a.isValue then
      if b.isValue then
        match a, b with
        | .num x, .num y => some (.num (if x < y then 1 else 0), h)
        | _, _ => none
      else (step b h).map fun c => (.lt a c.1, c.2)
    else (step a h).map fun c => (.lt c.1 b, c.2)
  | .ifz c t e, h =>
    if c.isValue then
      match c with
      | .num 0 => some (t, h)
      | .num (_ + 1) => some (e, h)
      | _ => none
    else (step c h).map fun d => (.ifz d.1 t e, d.2)
  | .size, h => some (.num h.length, h)
  | .alloc a, h =>
    if a.isValue then
      match a with
      | .num n => some (.loc h.length, h ++ [n])
      | _ => none
    else (step a h).map fun c => (.alloc c.1, c.2)
  | .read a, h =>
    if a.isValue then
      match a with
      | .loc l =>
        match h[l]? with
        | some n => some (.num n, h)
        | none => none
      | _ => none
    else (step a h).map fun c => (.read c.1, c.2)
  | .write a b, h =>
    if a.isValue then
      if b.isValue then
        match a, b with
        | .loc l, .num n => if l < h.length then some (.num 0, h.set l n) else none
        | _, _ => none
      else (step b h).map fun c => (.write a c.1, c.2)
    else (step a h).map fun c => (.write c.1 b, c.2)
  | .cast a, h =>
    if a.isValue then
      match a with
      | .num n => some (.loc n, h)
      | _ => none
    else (step a h).map fun c => (.cast c.1, c.2)
  | .var _, _ => none
  | .lam _, _ => none
  | .num _, _ => none
  | .loc _, _ => none

/-- Reflexive-transitive closure of `step` (all finite execution prefixes). -/
inductive Reaches : Config → Config → Prop where
  | refl (c : Config) : Reaches c c
  | step {c c' d : Config} : step c.1 c.2 = some c' → Reaches c' d → Reaches c d

/-- A configuration is stuck: not a value, and no step applies.
This is the toy's notion of undefined behavior. -/
def Stuck (c : Config) : Prop := c.1.isValue = false ∧ step c.1 c.2 = none

/-- Safety: no configuration reachable in finitely many steps is stuck.
(Divergence is safe; there is no termination requirement.) -/
def Safe (c : Config) : Prop := ∀ d, Reaches c d → ¬ Stuck d

/-! ## Basic execution lemmas -/

theorem step_of_isValue {e : Expr} (hv : e.isValue = true) (h : Heap) : step e h = none := by
  cases e <;> simp_all [Expr.isValue, step]

theorem reaches_of_isValue {e : Expr} {h : Heap} {d : Config} (hv : e.isValue = true)
    (hr : Reaches (e, h) d) : d = (e, h) := by
  cases hr with
  | refl => rfl
  | step hs _ => simp [step_of_isValue hv] at hs

/-- Determinism, one step at a time: if `c` steps to `c'`, anything reachable
from `c` is `c` itself or reachable from `c'`. -/
theorem reaches_of_step {c c' d : Config} (hs : step c.1 c.2 = some c')
    (hr : Reaches c d) : d = c ∨ Reaches c' d := by
  cases hr with
  | refl => exact Or.inl rfl
  | step hs' hr' =>
    rw [hs] at hs'
    cases hs'
    exact Or.inr hr'

theorem reaches_trans {a b c : Config} (h1 : Reaches a b) (h2 : Reaches b c) : Reaches a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact Reaches.step hs (ih h2)

theorem not_stuck_of_isValue {e : Expr} {h : Heap} (hv : e.isValue = true) : ¬ Stuck (e, h) := by
  intro hs; simp [Stuck, hv] at hs

theorem not_stuck_of_step {c c' : Config} (hs : step c.1 c.2 = some c') : ¬ Stuck c := by
  intro hst; simp [Stuck, hs] at hst

/-- A configuration that steps is safe iff its successor is safe. -/
theorem safe_of_step {c c' : Config} (hs : step c.1 c.2 = some c') (h : Safe c') : Safe c := by
  intro d hr
  rcases reaches_of_step hs hr with rfl | hr'
  · exact not_stuck_of_step hs
  · exact h d hr'

theorem not_safe_of_reaches_stuck {c d : Config} (hr : Reaches c d) (hs : Stuck d) : ¬ Safe c :=
  fun hsafe => hsafe d hr hs

end Toy.SemType
