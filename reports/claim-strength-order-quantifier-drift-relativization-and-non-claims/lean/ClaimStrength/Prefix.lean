import ClaimStrength.Basic

/-!
# Quantifier prefixes over an uninterpreted matrix, with relativized domains

A *binder* quantifies one variable (`Fin n`) universally or existentially over a domain class
`k : K`, interpreted by `I k : α → Prop`. A list of binders is a *prefix*. A prefix is evaluated
against a leaf predicate on full assignments `Fin n → α`, starting from an environment `ρ`.
Unrelativized prefixes are the special case `K = Unit` with every domain interpreted as all of
`α`.

Toy scope: one sort `α`, a matrix that is an arbitrary predicate on assignments (so nothing is
known about its internal structure), no function symbols, no equality reasoning inside the
matrix, and named domain classes with externally supplied inclusion and overlap relations.
-/

namespace Toy.ClaimStrength

/-- A quantifier. -/
inductive Quant
  | all
  | ex
  deriving DecidableEq, Repr

/-- A binder: a quantifier, the variable it binds, and the class of its domain. -/
structure Binder (n : Nat) (K : Type) where
  q : Quant
  var : Fin n
  dom : K

/-- An unrelativized quantifier prefix on the variables `Fin n`. -/
abbrev Prefix (n : Nat) := List (Binder n Unit)

/-- Pointwise update of an assignment. -/
def upd {n : Nat} {α : Type} (ρ : Fin n → α) (x : Fin n) (a : α) : Fin n → α :=
  fun y => if y = x then a else ρ y

/-- Relativized quantification over the domain `D`. -/
def quantify {α : Type} (q : Quant) (D : α → Prop) (P : α → Prop) : Prop :=
  match q with
  | .all => ∀ a, D a → P a
  | .ex => ∃ a, D a ∧ P a

variable {n : Nat} {K : Type} {α : Type}

/-- Evaluation of a relativized prefix in front of the leaf predicate `L`, from environment `ρ`.
`evalR I (⟨.all, x, k⟩ :: rest) L ρ = ∀ a, I k a → evalR I rest L (upd ρ x a)` and
`evalR I (⟨.ex, x, k⟩ :: rest) L ρ = ∃ a, I k a ∧ evalR I rest L (upd ρ x a)`. -/
def evalR (I : K → α → Prop) : List (Binder n K) → ((Fin n → α) → Prop) → (Fin n → α) → Prop
  | [], L, ρ => L ρ
  | b :: rest, L, ρ => quantify b.q (I b.dom) (fun a => evalR I rest L (upd ρ b.var a))

/-- Evaluation of an unrelativized prefix: every domain is all of `α`. -/
def eval (φ : Prefix n) (R : (Fin n → α) → Prop) (ρ : Fin n → α) : Prop :=
  evalR (fun (_ : Unit) (_ : α) => True) φ R ρ

/-- The variables bound by a prefix, in order. -/
def bvars (φ : List (Binder n K)) : List (Fin n) := φ.map Binder.var

/-- The first binder of `v` in the prefix. -/
def bOf : List (Binder n K) → Fin n → Option (Binder n K)
  | [], _ => none
  | b :: rest, v => if b.var = v then some b else bOf rest v

/-- The quantifier of the first binder of `v`. -/
def qOf (φ : List (Binder n K)) (v : Fin n) : Option Quant := (bOf φ v).map Binder.q

/-- `precL l u v`: the first occurrence of `u` in `l` comes before the first occurrence of `v`
(and `v` occurs). -/
def precL : List (Fin n) → Fin n → Fin n → Bool
  | [], _, _ => false
  | x :: rest, u, v => if x = u then rest.contains v else if x = v then false else precL rest u v

/-- `u` is bound before `v` in the prefix. -/
def Precedes (φ : List (Binder n K)) (u v : Fin n) : Prop := precL (bvars φ) u v = true

instance (φ : List (Binder n K)) (u v : Fin n) : Decidable (Precedes φ u v) :=
  inferInstanceAs (Decidable (_ = true))

/-- Well-formedness: every variable of `Fin n` is bound exactly once. -/
def WF (φ : List (Binder n K)) : Prop := (bvars φ).Nodup ∧ ∀ v : Fin n, v ∈ bvars φ

/-- Schematic entailment at a fixed base type `α` (environment semantics): for every matrix `R`
and every environment `ρ : Fin n → α`, `φ` with matrix `R` implies `ψ` with matrix `R`. The
environment gives values to variables a prefix leaves free. When `α` is empty and `n ≥ 1` there is
no environment, so `SEntailsAt α φ ψ` holds vacuously for all `φ`, `ψ` (`sentailsAt_of_isEmpty`). -/
def SEntailsAt (α : Type) (φ ψ : Prefix n) : Prop :=
  ∀ (R : (Fin n → α) → Prop) (ρ : Fin n → α), eval φ R ρ → eval ψ R ρ

/-- Schematic entailment at every base type (environment semantics). Restricting to base types
with two distinct elements gives the same relation (`sentails_iff_twoPoint_types`). -/
def SEntails (φ ψ : Prefix n) : Prop :=
  ∀ α : Type, SEntailsAt α φ ψ

/-- Criterion part (i): every variable universal in `ψ` is universal in `φ`. -/
def UnivReflected (φ ψ : List (Binder n K)) : Prop :=
  ∀ v, qOf ψ v = some .all → qOf φ v = some .all

/-- Criterion part (ii): if `v` is existential in `φ` and `u` is universal in both, and `u` is
bound before `v` in `φ`, then `u` is bound before `v` in `ψ` (the Skolem dependencies of `φ`
on variables that stay universal are available in `ψ`). -/
def SkolemOrderPreserved (φ ψ : List (Binder n K)) : Prop :=
  ∀ u v, qOf φ v = some .ex → qOf φ u = some .all → qOf ψ u = some .all →
    Precedes φ u v → Precedes ψ u v

/-- The prefix criterion: parts (i) and (ii). -/
def PrefixCrit (φ ψ : List (Binder n K)) : Prop := UnivReflected φ ψ ∧ SkolemOrderPreserved φ ψ

/-- A Boolean implementation of the prefix criterion. -/
def prefixCritB (φ ψ : List (Binder n K)) : Bool :=
  (List.finRange n).all (fun v => !decide (qOf ψ v = some .all) || decide (qOf φ v = some .all)) &&
  (List.finRange n).all (fun u => (List.finRange n).all (fun v =>
    !(decide (qOf φ v = some .ex) && decide (qOf φ u = some .all) &&
      decide (qOf ψ u = some .all) && precL (bvars φ) u v) || precL (bvars ψ) u v))

/-- A Boolean implementation of well-formedness. -/
def wfB (φ : List (Binder n K)) : Bool :=
  decide (bvars φ).Nodup && (List.finRange n).all (fun v => decide (v ∈ bvars φ))

/-- Notation helpers for unrelativized binders. -/
def A (x : Fin n) : Binder n Unit := ⟨.all, x, ()⟩
/-- Existential unrelativized binder. -/
def X (x : Fin n) : Binder n Unit := ⟨.ex, x, ()⟩

/-! ## Basic lemmas -/

@[simp] theorem upd_same (ρ : Fin n → α) (x : Fin n) (a : α) : upd ρ x a x = a := by
  simp [upd]

theorem upd_ne (ρ : Fin n → α) {x y : Fin n} (h : y ≠ x) (a : α) : upd ρ x a y = ρ y := by
  simp [upd, h]

theorem upd_comm (ρ : Fin n → α) {x y : Fin n} (h : x ≠ y) (a b : α) :
    upd (upd ρ x a) y b = upd (upd ρ y b) x a := by
  funext z
  simp only [upd]
  by_cases hzy : z = y
  · subst hzy; simp [Ne.symm h]
  · simp [hzy]

theorem upd_self (ρ : Fin n → α) (x : Fin n) : upd ρ x (ρ x) = ρ := by
  funext z; simp only [upd]; split <;> simp_all

theorem quantify_mono {q : Quant} {D P P' : α → Prop} (h : ∀ a, D a → P a → P' a) :
    quantify q D P → quantify q D P' := by
  cases q
  · intro hp a ha; exact h a ha (hp a ha)
  · rintro ⟨a, ha, hp⟩; exact ⟨a, ha, h a ha hp⟩

theorem quantify_congr {q : Quant} {D P P' : α → Prop} (h : ∀ a, D a → (P a ↔ P' a)) :
    quantify q D P ↔ quantify q D P' :=
  ⟨quantify_mono (fun a ha => (h a ha).1), quantify_mono (fun a ha => (h a ha).2)⟩

theorem quantify_const {q : Quant} {D : α → Prop} {P : Prop} (hD : ∃ a, D a) :
    quantify q D (fun _ => P) ↔ P := by
  obtain ⟨a, ha⟩ := hD
  cases q
  · exact ⟨fun h => h a ha, fun h _ _ => h⟩
  · exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨a, ha, h⟩⟩

theorem evalR_mono (I : K → α → Prop) {L L' : (Fin n → α) → Prop} (h : ∀ σ, L σ → L' σ) :
    ∀ (φ : List (Binder n K)) (ρ : Fin n → α), evalR I φ L ρ → evalR I φ L' ρ
  | [], ρ, hφ => h ρ hφ
  | _ :: rest, _, hφ => quantify_mono (fun _ _ => evalR_mono I h rest _) hφ

theorem eval_nil (R : (Fin n → α) → Prop) (ρ : Fin n → α) : eval [] R ρ ↔ R ρ := Iff.rfl

theorem eval_cons_all (x : Fin n) (rest : Prefix n) (R : (Fin n → α) → Prop) (ρ : Fin n → α) :
    eval (A x :: rest) R ρ ↔ ∀ a, eval rest R (upd ρ x a) :=
  ⟨fun h a => h a trivial, fun h a _ => h a⟩

theorem eval_cons_ex (x : Fin n) (rest : Prefix n) (R : (Fin n → α) → Prop) (ρ : Fin n → α) :
    eval (X x :: rest) R ρ ↔ ∃ a, eval rest R (upd ρ x a) :=
  ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, trivial, h⟩⟩

end Toy.ClaimStrength
