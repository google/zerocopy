/-
Syntax of a small single-sorted first-order language with equality:
signatures, signature morphisms, well-scoped terms and formulas, renaming,
substitution, translation along signature morphisms, and decidable equality.
-/

namespace Toy.Extension

/-- A single-sorted first-order signature: function symbols and relation
symbols, each with an arity. This is the "vocabulary" of a theory. -/
structure Sig where
  Fn : Type
  Rel : Type
  fnArity : Fn → Nat
  relArity : Rel → Nat

/-- A signature morphism: an arity-preserving map of symbols. An injective
morphism models "the old vocabulary inside the extended vocabulary". Morphisms
need not be injective; `noninjective_hom_empty_theories_not_conservative`
shows what changes for a non-injective one. -/
structure SigHom (L L' : Sig) where
  fn : L.Fn → L'.Fn
  rel : L.Rel → L'.Rel
  fnArity : ∀ f, L'.fnArity (fn f) = L.fnArity f
  relArity : ∀ r, L'.relArity (rel r) = L.relArity r

/-- Terms over `L` whose free variables are drawn from `Fin n`
(well-scoped de Bruijn indices: no side condition on free variables is ever
needed). -/
inductive Term (L : Sig) (n : Nat) : Type where
  | var : Fin n → Term L n
  | app : (f : L.Fn) → (Fin (L.fnArity f) → Term L n) → Term L n

/-- Formulas over `L` with free variables in `Fin n`. `all` and `ex` bind
variable `0` of the body; the remaining variables shift up by one. -/
inductive Formula (L : Sig) : Nat → Type where
  | eq {n : Nat} : Term L n → Term L n → Formula L n
  | rel {n : Nat} : (r : L.Rel) → (Fin (L.relArity r) → Term L n) → Formula L n
  | falsum {n : Nat} : Formula L n
  | imp {n : Nat} : Formula L n → Formula L n → Formula L n
  | and {n : Nat} : Formula L n → Formula L n → Formula L n
  | or {n : Nat} : Formula L n → Formula L n → Formula L n
  | all {n : Nat} : Formula L (n + 1) → Formula L n
  | ex {n : Nat} : Formula L (n + 1) → Formula L n

/-- Sentences: formulas without free variables. These are the stored
statements of a theory. -/
abbrev Sentence (L : Sig) := Formula L 0

namespace Formula

variable {L : Sig}

/-- Negation, as implication into falsum. -/
def not {n : Nat} (φ : Formula L n) : Formula L n := imp φ falsum

/-- Truth, as the negation of falsum. -/
def tru {n : Nat} : Formula L n := imp falsum falsum

/-- Biconditional. -/
def iff {n : Nat} (φ ψ : Formula L n) : Formula L n := and (imp φ ψ) (imp ψ φ)

/-- Universal closure of a formula in `k` free variables: binds all of them. -/
def closeAll : (k : Nat) → Formula L k → Sentence L
  | 0, φ => φ
  | k + 1, φ => closeAll k (all φ)

end Formula

/-! ### Renaming and substitution -/

namespace Term

variable {L : Sig}

/-- Rename variables along `ρ`. -/
def rename {n m : Nat} (ρ : Fin n → Fin m) : Term L n → Term L m
  | var i => var (ρ i)
  | app f ts => app f (fun j => (ts j).rename ρ)

/-- Simultaneous substitution of terms for variables. -/
def subst {k n : Nat} (σ : Fin k → Term L n) : Term L k → Term L n
  | var i => σ i
  | app f ts => app f (fun j => (ts j).subst σ)

/-- Translate a term along a signature morphism. -/
def map {L' : Sig} (ι : SigHom L L') {n : Nat} : Term L n → Term L' n
  | var i => var i
  | app f ts => app (ι.fn f) (fun j => (ts (Fin.cast (ι.fnArity f) j)).map ι)

end Term

/-- Extend a renaming under one binder (variable `0` is fixed). -/
def liftRen {n m : Nat} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1)
  | ⟨0, _⟩ => ⟨0, Nat.succ_pos _⟩
  | ⟨k + 1, h⟩ => (ρ ⟨k, Nat.lt_of_succ_lt_succ h⟩).succ

/-- Extend a substitution under one binder. -/
def liftSubst {L : Sig} {k n : Nat} (σ : Fin k → Term L n) : Fin (k + 1) → Term L (n + 1)
  | ⟨0, _⟩ => Term.var ⟨0, Nat.succ_pos _⟩
  | ⟨j + 1, h⟩ => (σ ⟨j, Nat.lt_of_succ_lt_succ h⟩).rename Fin.succ

namespace Formula

variable {L : Sig}

/-- Rename free variables of a formula. -/
def rename : {n m : Nat} → (Fin n → Fin m) → Formula L n → Formula L m
  | _, _, ρ, eq s t => eq (s.rename ρ) (t.rename ρ)
  | _, _, ρ, rel r ts => rel r (fun j => (ts j).rename ρ)
  | _, _, _, falsum => falsum
  | _, _, ρ, imp φ ψ => imp (φ.rename ρ) (ψ.rename ρ)
  | _, _, ρ, and φ ψ => and (φ.rename ρ) (ψ.rename ρ)
  | _, _, ρ, or φ ψ => or (φ.rename ρ) (ψ.rename ρ)
  | _, _, ρ, all φ => all (φ.rename (liftRen ρ))
  | _, _, ρ, ex φ => ex (φ.rename (liftRen ρ))

/-- Capture-avoiding simultaneous substitution of terms for the free
variables of a formula. -/
def subst : {k n : Nat} → (Fin k → Term L n) → Formula L k → Formula L n
  | _, _, σ, eq s t => eq (s.subst σ) (t.subst σ)
  | _, _, σ, rel r ts => rel r (fun j => (ts j).subst σ)
  | _, _, _, falsum => falsum
  | _, _, σ, imp φ ψ => imp (φ.subst σ) (ψ.subst σ)
  | _, _, σ, and φ ψ => and (φ.subst σ) (ψ.subst σ)
  | _, _, σ, or φ ψ => or (φ.subst σ) (ψ.subst σ)
  | _, _, σ, all φ => all (φ.subst (liftSubst σ))
  | _, _, σ, ex φ => ex (φ.subst (liftSubst σ))

/-- Translate a formula along a signature morphism ("the same stored
statement, read in the larger vocabulary"). -/
def map {L' : Sig} (ι : SigHom L L') : {n : Nat} → Formula L n → Formula L' n
  | _, eq s t => eq (s.map ι) (t.map ι)
  | _, rel r ts => rel (ι.rel r) (fun j => (ts (Fin.cast (ι.relArity r) j)).map ι)
  | _, falsum => falsum
  | _, imp φ ψ => imp (φ.map ι) (ψ.map ι)
  | _, and φ ψ => and (φ.map ι) (ψ.map ι)
  | _, or φ ψ => or (φ.map ι) (ψ.map ι)
  | _, all φ => all (φ.map ι)
  | _, ex φ => ex (φ.map ι)

end Formula

/-! ### Decidable equality of terms and formulas

Needed to decide whether re-elaborating a displayed string yields the same
stored formula. -/

/-- Decide a universally quantified statement over `Fin k`. -/
def decForallFin : {k : Nat} → {P : Fin k → Prop} → ((i : Fin k) → Decidable (P i)) →
    Decidable (∀ i, P i)
  | 0, _, _ => isTrue (fun i => i.elim0)
  | k + 1, P, d =>
    match d ⟨0, Nat.succ_pos k⟩, decForallFin (P := fun i : Fin k => P i.succ) (fun i => d i.succ) with
    | isTrue h0, isTrue hs => isTrue (fun i =>
        match i with
        | ⟨0, _⟩ => h0
        | ⟨j + 1, h⟩ => hs ⟨j, Nat.lt_of_succ_lt_succ h⟩)
    | isFalse h0, _ => isFalse (fun h => h0 (h _))
    | _, isFalse hs => isFalse (fun h => hs (fun _ => h _))

namespace Term

variable {L : Sig} [DecidableEq L.Fn]

/-- Decidable equality of terms (structural). -/
def decEq {n : Nat} : (s t : Term L n) → Decidable (s = t)
  | var i, var j =>
    if h : i = j then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | var _, app _ _ => isFalse (fun e => by cases e)
  | app _ _, var _ => isFalse (fun e => by cases e)
  | app f ss, app g ts =>
    if h : f = g then
      match decForallFin (fun i => decEq (ss i) (ts (Fin.cast (congrArg L.fnArity h) i))) with
      | isTrue hall => isTrue (by subst h; exact congrArg (app f) (funext hall))
      | isFalse hn => isFalse (fun e => by cases e; exact hn (fun _ => rfl))
    else isFalse (fun e => by cases e; exact h rfl)

instance {n : Nat} : DecidableEq (Term L n) := decEq

end Term

namespace Formula

variable {L : Sig} [DecidableEq L.Fn] [DecidableEq L.Rel]

/-- Decidable equality of formulas (structural). -/
def decEq : {n : Nat} → (φ ψ : Formula L n) → Decidable (φ = ψ)
  | _, eq s t, eq s' t' =>
    if h : s = s' ∧ t = t' then isTrue (by rw [h.1, h.2])
    else isFalse (fun e => by cases e; exact h ⟨rfl, rfl⟩)
  | _, rel r ts, rel r' ts' =>
    if h : r = r' then
      match decForallFin (fun i =>
          (inferInstance : Decidable (ts i = ts' (Fin.cast (congrArg L.relArity h) i)))) with
      | isTrue hall => isTrue (by subst h; exact congrArg (rel r) (funext hall))
      | isFalse hn => isFalse (fun e => by cases e; exact hn (fun _ => rfl))
    else isFalse (fun e => by cases e; exact h rfl)
  | _, falsum, falsum => isTrue rfl
  | _, imp φ ψ, imp φ' ψ' =>
    match decEq φ φ', decEq ψ ψ' with
    | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | _, and φ ψ, and φ' ψ' =>
    match decEq φ φ', decEq ψ ψ' with
    | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | _, or φ ψ, or φ' ψ' =>
    match decEq φ φ', decEq ψ ψ' with
    | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | _, all φ, all φ' =>
    match decEq φ φ' with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | _, ex φ, ex φ' =>
    match decEq φ φ' with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | _, eq _ _, rel _ _ | _, eq _ _, falsum | _, eq _ _, imp _ _ | _, eq _ _, and _ _
  | _, eq _ _, or _ _ | _, eq _ _, all _ | _, eq _ _, ex _
  | _, rel _ _, eq _ _ | _, rel _ _, falsum | _, rel _ _, imp _ _ | _, rel _ _, and _ _
  | _, rel _ _, or _ _ | _, rel _ _, all _ | _, rel _ _, ex _
  | _, falsum, eq _ _ | _, falsum, rel _ _ | _, falsum, imp _ _ | _, falsum, and _ _
  | _, falsum, or _ _ | _, falsum, all _ | _, falsum, ex _
  | _, imp _ _, eq _ _ | _, imp _ _, rel _ _ | _, imp _ _, falsum | _, imp _ _, and _ _
  | _, imp _ _, or _ _ | _, imp _ _, all _ | _, imp _ _, ex _
  | _, and _ _, eq _ _ | _, and _ _, rel _ _ | _, and _ _, falsum | _, and _ _, imp _ _
  | _, and _ _, or _ _ | _, and _ _, all _ | _, and _ _, ex _
  | _, or _ _, eq _ _ | _, or _ _, rel _ _ | _, or _ _, falsum | _, or _ _, imp _ _
  | _, or _ _, and _ _ | _, or _ _, all _ | _, or _ _, ex _
  | _, all _, eq _ _ | _, all _, rel _ _ | _, all _, falsum | _, all _, imp _ _
  | _, all _, and _ _ | _, all _, or _ _ | _, all _, ex _
  | _, ex _, eq _ _ | _, ex _, rel _ _ | _, ex _, falsum | _, ex _, imp _ _
  | _, ex _, and _ _ | _, ex _, or _ _ | _, ex _, all _ => isFalse (fun e => by cases e)

instance {n : Nat} : DecidableEq (Formula L n) := decEq

end Formula

end Toy.Extension
