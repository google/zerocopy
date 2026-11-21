import ToyUpTo.Context

/-!
# Executable finite checks

Boolean re-implementations of the weak transition relation, the weak
bisimulation and expansion functionals, and their approximants, for the
finite toy process terms used in the counterexamples.  The `decide` checks
below are independent sanity checks of the counterexamples; the authoritative
statements are the `Prop`-level theorems in the other modules.

The approximants start from the total relation, so a `false` result for
`wbisimB` refutes weak bisimilarity outright; a `true` result is evidence only
(the Prop-level proofs are the authority).
-/

namespace Toy.UpTo.Check

open Toy.UpTo Proc

/-- Outgoing transitions of a term. -/
def succs {L : Type} : Proc L → List (Option L × Proc L)
  | .nil => []
  | .pre μ P => [(μ, P)]
  | .sum P Q => succs P ++ succs Q

/-- States reachable by `τ*`, with `fuel` bounding the number of τ-steps. -/
def tauClo {L : Type} [DecidableEq L] : Nat → Proc L → List (Proc L)
  | 0, p => [p]
  | n + 1, p => p :: (succs p).flatMap (fun e => if e.1 = none then tauClo n e.2 else [])

/-- Weak successors `=l̂⇒`. -/
def wsuccs {L : Type} [DecidableEq L] (n : Nat) (p : Proc L) : Option L → List (Proc L)
  | none => tauClo n p
  | some a => (tauClo n p).flatMap (fun p₁ =>
      (succs p₁).flatMap (fun e => if e.1 = some a then tauClo n e.2 else []))

/-- `-l̂→` successors (one step, or standing still for τ). -/
def hatSuccs {L : Type} [DecidableEq L] (p : Proc L) (l : Option L) : List (Proc L) :=
  (succs p).filterMap (fun e => if e.1 = l then some e.2 else none) ++
    (if l = none then [p] else [])

/-- `=l⇒` successors with at least one step. -/
def plusSuccs {L : Type} [DecidableEq L] (n : Nat) (p : Proc L) : Option L → List (Proc L)
  | none => (succs p).flatMap (fun e => if e.1 = none then tauClo n e.2 else [])
  | some a => wsuccs n p (some a)

/-- Boolean weak bisimulation functional. -/
def wbB {L : Type} [DecidableEq L] (n : Nat) (R : Proc L → Proc L → Bool)
    (p q : Proc L) : Bool :=
  (succs p).all (fun e => (wsuccs n q e.1).any (fun q' => R e.2 q')) &&
  (succs q).all (fun e => (wsuccs n p e.1).any (fun p' => R p' e.2))

/-- Boolean expansion functional. -/
def exB {L : Type} [DecidableEq L] (n : Nat) (R : Proc L → Proc L → Bool)
    (p q : Proc L) : Bool :=
  (succs p).all (fun e => (hatSuccs q e.1).any (fun q' => R e.2 q')) &&
  (succs q).all (fun e => (plusSuccs n p e.1).any (fun p' => R p' e.2))

/-- Boolean strong bisimulation functional. -/
def sbB {L : Type} [DecidableEq L] (R : Proc L → Proc L → Bool) (p q : Proc L) : Bool :=
  (succs p).all (fun e => (succs q).any (fun e' => e'.1 = e.1 && R e.2 e'.2)) &&
  (succs q).all (fun e => (succs p).any (fun e' => e'.1 = e.1 && R e'.2 e.2))

/-- `k`-th approximant of weak bisimilarity, starting from the total
relation. -/
def wbisimB {L : Type} [DecidableEq L] (n : Nat) : Nat → Proc L → Proc L → Bool
  | 0 => fun _ _ => true
  | k + 1 => wbB n (wbisimB n k)

/-- `k`-th approximant of expansion. -/
def expandsB {L : Type} [DecidableEq L] (n : Nat) : Nat → Proc L → Proc L → Bool
  | 0 => fun _ _ => true
  | k + 1 => exB n (expandsB n k)

/-- `k`-th approximant of strong bisimilarity. -/
def bisimB {L : Type} [DecidableEq L] : Nat → Proc L → Proc L → Bool
  | 0 => fun _ _ => true
  | k + 1 => sbB (bisimB k)

/-- A finite relation, as a list of pairs. -/
abbrev FinRel := List (Proc Lbl × Proc Lbl)

def memB (R : FinRel) (p q : Proc Lbl) : Bool := R.any (fun e => e.1 = p && e.2 = q)

/-- `≈ R ≈` with the middle pair drawn from the finite `R`. -/
def weakUpToB (R : FinRel) (p q : Proc Lbl) : Bool :=
  R.any (fun e => wbisimB 4 4 p e.1 && wbisimB 4 4 e.2 q)

/-- `~ R ~`. -/
def strongUpToB (R : FinRel) (p q : Proc Lbl) : Bool :=
  R.any (fun e => bisimB 4 p e.1 && bisimB 4 e.2 q)

/-- `≳ R ≈`. -/
def expWeakUpToB (R : FinRel) (p q : Proc Lbl) : Bool :=
  R.any (fun e => expandsB 4 4 p e.1 && wbisimB 4 4 e.2 q)

/-- `≳ R ≲`. -/
def expUpToB (R : FinRel) (p q : Proc Lbl) : Bool :=
  R.any (fun e => expandsB 4 4 p e.1 && expandsB 4 4 q e.2)

/-- `+`-context closure. -/
def sumCloB (R : FinRel) : Proc Lbl → Proc Lbl → Bool
  | .sum p₁ p₂, .sum q₁ q₂ => memB R (.sum p₁ p₂) (.sum q₁ q₂) ||
      decide (Proc.sum p₁ p₂ = Proc.sum q₁ q₂) || (sumCloB R p₁ q₁ && sumCloB R p₂ q₂)
  | p, q => memB R p q || decide (p = q)

/-- `R ⊑ wb (F R)` for a finite `R`. -/
def progressesWB (R : FinRel) (F : FinRel → Proc Lbl → Proc Lbl → Bool) : Bool :=
  R.all (fun e => wbB 4 (F R) e.1 e.2)

/-- `R ⊑ ≈` for a finite `R` (via the approximant). -/
def inWbisim (R : FinRel) : Bool := R.all (fun e => wbisimB 4 4 e.1 e.2)

/-! ### Checks -/

/-- The pitfall: `{(τ.a.0, 0)}` progresses to `≈ R ≈` but `τ.a.0 ≉ 0`. -/
example : progressesWB [(tau (act .a .nil), .nil)] weakUpToB = true := by decide
example : inWbisim [(tau (act .a .nil), .nil)] = false := by decide
example : wbisimB 4 4 (act Lbl.a .nil) (tau (act .a .nil)) = true := by decide
/-- The repairs reject the pitfall relation. -/
example : progressesWB [(tau (act .a .nil), .nil)] strongUpToB = false := by decide
example : progressesWB [(tau (act .a .nil), .nil)] expUpToB = false := by decide

/-- The literal `≳ R ≈` variant: `{(0, τ.a.0)}` progresses but `0 ≉ τ.a.0`. -/
example : progressesWB [(.nil, tau (act .a .nil))] expWeakUpToB = true := by decide
example : inWbisim [(.nil, tau (act .a .nil))] = false := by decide
example : progressesWB [(.nil, tau (act .a .nil))] expUpToB = false := by decide

/-- Expansion is a strict preorder on these terms: `τ.a.0 ≳ a.0`, not
conversely. -/
example : expandsB 4 4 (tau (act Lbl.a .nil)) (act .a .nil) = true := by decide
example : expandsB 4 4 (act Lbl.a .nil) (tau (act .a .nil)) = false := by decide

/-- `+` is not a weak congruence, and weak bisimulation up to `+`-contexts is
unsound. -/
example : wbisimB 4 4 (.sum (tau (act Lbl.a .nil)) (act .b .nil))
    (.sum (act .a .nil) (act .b .nil)) = false := by decide
example : progressesWB [(act .a (.sum (tau (act .a .nil)) (act .b .nil)),
      act .a (.sum (act .a .nil) (act .b .nil))), (tau (act .a .nil), act .a .nil)]
    sumCloB = true := by decide
example : inWbisim [(act .a (.sum (tau (act .a .nil)) (act .b .nil)),
      act .a (.sum (act .a .nil) (act .b .nil)))] = false := by decide

/-- `≲ R ≳` (expansion symbols reversed). -/
def revExpUpToB (R : FinRel) (p q : Proc Lbl) : Bool :=
  R.any (fun e => expandsB 4 4 e.1 p && expandsB 4 4 e.2 q)

/-- The symbols-reversed variant accepts the pitfall relation. -/
example : progressesWB [(tau (act .a .nil), .nil)] revExpUpToB = true := by decide

/-- One visible label suffices: `τ.0 + a.0 ≉ 0 + a.0`, and the one-label
`+`-context relation progresses but is not contained in `≈`. -/
example : wbisimB 4 4 (Proc.sum (tau (Proc.nil : Proc Lbl)) (act .a .nil))
    (.sum .nil (act .a .nil)) = false := by decide
example : wbisimB 4 4 (tau (Proc.nil : Proc Lbl)) .nil = true := by decide
example : progressesWB [(act .a (.sum (tau .nil) (act .a .nil)), act .a (.sum .nil (act .a .nil))),
      (tau .nil, .nil)] sumCloB = true := by decide
example : inWbisim [(act .a (.sum (tau .nil) (act .a .nil)),
      act .a (.sum .nil (act .a .nil)))] = false := by decide

/-- Non-commutation of up to expansion at `R = ∅`: `(τ.0, 0)` is not in
`wb ∅`, while `τ.0 ≳ 0` and `(0, 0) ∈ wb ∅`. -/
example : wbB 4 (fun _ _ => false) (tau (Proc.nil : Proc Lbl)) .nil = false := by decide
example : wbB 4 (fun _ _ => false) (Proc.nil : Proc Lbl) .nil = true := by decide
example : expandsB 4 4 (tau (Proc.nil : Proc Lbl)) .nil = true := by decide

/-- The strictly asymmetric witness does not progress under symmetric `≳ R ≲`. -/
example : progressesWB [(tau (act .b (tau .nil)), act .b .nil), (act .b (tau .nil), act .b (tau .nil)),
      (tau .nil, tau .nil), (.nil, .nil)] expUpToB = false := by decide

/-- The one-pair relation `{(τ.a.0 + b.0, a.0 + b.0)}` does not progress to
its `+`-context closure (the prefix in `ctxRel` is needed). -/
example : progressesWB [(.sum (tau (act .a .nil)) (act .b .nil), .sum (act .a .nil) (act .b .nil))]
    sumCloB = false := by decide

end Toy.UpTo.Check
