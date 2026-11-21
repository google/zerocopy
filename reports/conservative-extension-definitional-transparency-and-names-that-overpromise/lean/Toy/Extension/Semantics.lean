/-
Semantics: structures (with possibly empty carriers), satisfaction, theories,
semantic consequence, reducts, conservativity and the expansion property.
-/
import Toy.Extension.Syntax

namespace Toy.Extension

/-- An `L`-structure on carrier `α`. The carrier may be empty: nothing here
assumes `Nonempty α`. This matches carriers in `Type` and matters for
constants (see `fresh_constant_not_conservative_with_empty_carriers`). -/
structure Str (L : Sig) (α : Type) where
  fn : (f : L.Fn) → (Fin (L.fnArity f) → α) → α
  rel : (r : L.Rel) → (Fin (L.relArity r) → α) → Prop

/-- Extend a variable assignment by a value for the newly bound variable `0`. -/
def scons {α : Type} {n : Nat} (a : α) (v : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩ => a
  | ⟨k + 1, h⟩ => v ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- The empty assignment, used for sentences. -/
def noVars {α : Type} : Fin 0 → α := fun i => i.elim0

variable {L L' : Sig} {α : Type}

/-- Value of a term under an assignment. -/
def Term.eval (S : Str L α) {n : Nat} (v : Fin n → α) : Term L n → α
  | .var i => v i
  | .app f ts => S.fn f (fun j => (ts j).eval S v)

/-- Tarskian satisfaction. -/
def Sat (S : Str L α) : {n : Nat} → (Fin n → α) → Formula L n → Prop
  | _, v, .eq s t => s.eval S v = t.eval S v
  | _, v, .rel r ts => S.rel r (fun j => (ts j).eval S v)
  | _, _, .falsum => False
  | _, v, .imp φ ψ => Sat S v φ → Sat S v ψ
  | _, v, .and φ ψ => Sat S v φ ∧ Sat S v ψ
  | _, v, .or φ ψ => Sat S v φ ∨ Sat S v ψ
  | _, v, .all φ => ∀ a, Sat S (scons a v) φ
  | _, v, .ex φ => ∃ a, Sat S (scons a v) φ

/-- A structure satisfies a sentence. -/
def Str.Models (S : Str L α) (φ : Sentence L) : Prop := Sat S noVars φ

/-- A theory is a (possibly infinite) set of sentences. -/
abbrev Theory (L : Sig) := Sentence L → Prop

/-- A structure is a model of a theory. -/
def Str.ModelsTh (S : Str L α) (T : Theory L) : Prop := ∀ φ, T φ → S.Models φ

/-- Semantic consequence `T ⊨ φ`, quantifying over all structures with
carriers in `Type`, including empty ones. -/
def Entails (T : Theory L) (φ : Sentence L) : Prop :=
  ∀ (β : Type) (S : Str L β), S.ModelsTh T → S.Models φ

namespace Theory

/-- The empty theory. -/
def empty : Theory L := fun _ => False

/-- Union of theories. -/
def union (T U : Theory L) : Theory L := fun φ => T φ ∨ U φ

/-- The finite theory listing the given sentences. -/
def ofList (l : List (Sentence L)) : Theory L := fun φ => φ ∈ l

/-- Image of a theory along a signature morphism: the same stored sentences
read in the larger vocabulary. -/
def map (ι : SigHom L L') (T : Theory L) : Theory L' := fun ψ => ∃ φ, T φ ∧ φ.map ι = ψ

/-- The complete theory of a structure. -/
def th (S : Str L α) : Theory L := fun φ => S.Models φ

end Theory

/-- Reduct of an `L'`-structure along `ι : L → L'`: forget the symbols outside
the image and read old symbols through `ι`. Same carrier. -/
def Str.reduct (ι : SigHom L L') (S : Str L' α) : Str L α where
  fn f args := S.fn (ι.fn f) (fun j => args (Fin.cast (ι.fnArity f) j))
  rel r args := S.rel (ι.rel r) (fun j => args (Fin.cast (ι.relArity r) j))

/-- `T'` (over `L'`) is conservative over `T` (over `L`) along `ι`: every
old-language sentence that `T'` entails is already entailed by `T`. -/
def Conservative (ι : SigHom L L') (T : Theory L) (T' : Theory L') : Prop :=
  ∀ φ : Sentence L, Entails T' (φ.map ι) → Entails T φ

/-- Every model of `T` expands, on the same carrier and without changing the
old symbols, to a model of `T'`. -/
def ExpansionProperty (ι : SigHom L L') (T : Theory L) (T' : Theory L') : Prop :=
  ∀ (β : Type) (S : Str L β), S.ModelsTh T → ∃ S' : Str L' β, S'.reduct ι = S ∧ S'.ModelsTh T'

/-! ### Basic semantic lemmas (fully proved infrastructure) -/

@[simp] theorem scons_zero {n : Nat} (a : α) (v : Fin n → α) :
    scons a v ⟨0, Nat.succ_pos n⟩ = a := rfl

@[simp] theorem scons_succ {n : Nat} (a : α) (v : Fin n → α) (i : Fin n) :
    scons a v i.succ = v i := rfl

@[simp] theorem sat_not (S : Str L α) {n : Nat} (v : Fin n → α) (φ : Formula L n) :
    Sat S v φ.not ↔ ¬ Sat S v φ := Iff.rfl

@[simp] theorem sat_tru (S : Str L α) {n : Nat} (v : Fin n → α) :
    Sat S v (Formula.tru : Formula L n) ↔ True := ⟨fun _ => trivial, fun _ h => h⟩

@[simp] theorem sat_iff (S : Str L α) {n : Nat} (v : Fin n → α) (φ ψ : Formula L n) :
    Sat S v (φ.iff ψ) ↔ (Sat S v φ ↔ Sat S v ψ) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem scons_surj {n : Nat} (w : Fin (n + 1) → α) :
    scons (w ⟨0, Nat.succ_pos n⟩) (fun i => w i.succ) = w := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨k + 1, _⟩ => rfl

theorem sat_closeAll (S : Str L α) :
    ∀ (k : Nat) (φ : Formula L k), S.Models (φ.closeAll k) ↔ ∀ v : Fin k → α, Sat S v φ
  | 0, φ => by
    show Sat S noVars φ ↔ _
    constructor
    · intro h v
      have : v = noVars := funext (fun i => i.elim0)
      subst this; exact h
    · intro h; exact h _
  | k + 1, φ => by
    rw [Formula.closeAll, sat_closeAll S k]
    constructor
    · intro h w
      have := h (fun i => w i.succ) (w ⟨0, Nat.succ_pos k⟩)
      rwa [scons_surj] at this
    · intro h v a
      exact h _

theorem eval_map (ι : SigHom L L') (S : Str L' α) {n : Nat} (v : Fin n → α) (t : Term L n) :
    (t.map ι).eval S v = t.eval (S.reduct ι) v := by
  induction t with
  | var i => rfl
  | app f ts ih =>
    simp only [Term.map, Term.eval, Str.reduct, ih]

/-- Infrastructure form of the reduct lemma: translating a formula along `ι`
and evaluating in `S` is evaluating the original in the reduct. -/
theorem sat_map (ι : SigHom L L') (S : Str L' α) {n : Nat} (v : Fin n → α) (φ : Formula L n) :
    Sat S v (φ.map ι) ↔ Sat (S.reduct ι) v φ := by
  induction φ with
  | eq s t => simp only [Formula.map, Sat, eval_map]
  | rel r ts => simp only [Formula.map, Sat, eval_map, Str.reduct]
  | falsum => exact Iff.rfl
  | imp φ ψ ihφ ihψ => simp only [Formula.map, Sat, ihφ, ihψ]
  | and φ ψ ihφ ihψ => simp only [Formula.map, Sat, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [Formula.map, Sat, ihφ, ihψ]
  | all φ ih => simp only [Formula.map, Sat, ih]
  | ex φ ih => simp only [Formula.map, Sat, ih]

theorem models_map (ι : SigHom L L') (S : Str L' α) (φ : Sentence L) :
    S.Models (φ.map ι) ↔ (S.reduct ι).Models φ := sat_map ι S noVars φ

theorem modelsTh_map (ι : SigHom L L') (S : Str L' α) (T : Theory L) :
    S.ModelsTh (T.map ι) ↔ (S.reduct ι).ModelsTh T := by
  constructor
  · intro h φ hφ
    exact (models_map ι S φ).1 (h _ ⟨φ, hφ, rfl⟩)
  · rintro h _ ⟨φ, hφ, rfl⟩
    exact (models_map ι S φ).2 (h φ hφ)

theorem modelsTh_union (S : Str L α) (T U : Theory L) :
    S.ModelsTh (T.union U) ↔ S.ModelsTh T ∧ S.ModelsTh U :=
  ⟨fun h => ⟨fun φ hφ => h φ (Or.inl hφ), fun φ hφ => h φ (Or.inr hφ)⟩,
   fun h φ hφ => hφ.elim (h.1 φ) (h.2 φ)⟩

theorem modelsTh_ofList (S : Str L α) (l : List (Sentence L)) :
    S.ModelsTh (Theory.ofList l) ↔ ∀ φ ∈ l, S.Models φ := Iff.rfl

theorem modelsTh_empty (S : Str L α) : S.ModelsTh Theory.empty := fun _ h => h.elim

theorem modelsTh_th (S : Str L α) : S.ModelsTh (Theory.th S) := fun _ h => h

end Toy.Extension
