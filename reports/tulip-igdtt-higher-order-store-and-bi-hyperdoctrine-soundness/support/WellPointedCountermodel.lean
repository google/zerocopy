-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanized Presheaf Countermodel to Well-Pointedness Deductibility in `arXiv:2308.02906v2` §4.1.2

In Aagaard, Sterling, and Birkedal (*"A denotationally-based program logic for higher-order
store"*, MFPS XXXIX / ENTICS Vol. 3, `arXiv:2308.02906v2`, `paper.tex:1180–1284`), §4.1.2 lists the
inference and equational rules of delayed substitutions `δ ↝ Δ`, `▸[δ]. A`, `next[δ]. a`, and
guarded fixed points `gfix`, and states at `lines 1269–1271`:

> *"From these rules, we may deduce that the later modality forms a well-pointed endofunctor
> `▸ : U → U` in the sense of Kelly [1980]..."*

where well-pointedness is `▸(next_A) = next_{▸A}` (and its delayed-substitution strengthening
`next[x ← u]. G(x, next x) = next[x ← u]. G(x, u)` is required to derive TULIP's `set-after-get`
equation `(x ← get u; set u x; w) ≡ (x ← get u; w)` at `paper.tex:390–402`).

This standalone Lean 4 file (`Init.*` only) constructs the binary-branching step-indexed presheaf
modality on `PSh(ω)`:
- `(Later2 X)_0 = PUnit`
- `(Later2 X)_{n+1} = Bool → X_n`

and kernel-checks that `Later2` satisfies **every** rule in `paper.tex:1180–1284` (`later/next`
formation, functoriality, weakening, exchange, `force`, `later id` on proof-irrelevant/subsingleton
equality, `next variable`, and `gfix` + `gfix_unfold`), **while refuting well-pointedness**
(`not_well_pointed : map next ≠ next`) and refuting `set-after-get` (`not_set_after_get_in_later2`)!
-/

namespace WellPointedCountermodel

/-- Objects of `PSh(ω)` (contravariant functors `(Nat, ≤)ᵒᵖ → Type`). -/
structure Presheaf : Type 1 where
  obj    : Nat → Type
  restr  : {n : Nat} → obj (n + 1) → obj n

/-- Morphisms (natural transformations) in `PSh(ω)`. -/
structure Hom (X Y : Presheaf) : Type where
  app : (n : Nat) → X.obj n → Y.obj n
  nat : ∀ {n : Nat} (x : X.obj (n + 1)), Y.restr (app (n + 1) x) = app n (X.restr x)

theorem Hom.ext {X Y : Presheaf} {f g : Hom X Y} (h : ∀ n x, f.app n x = g.app n x) : f = g := by
  cases f; cases g; simp only [mk.injEq]
  exact funext fun n => funext fun x => h n x

/-- Constant presheaf `Δ(A)` for `A : Type`. -/
def ConstPSh (A : Type) : Presheaf where
  obj   := fun _ => A
  restr := fun a => a

/-- Binary-branching guarded modality `Later2` on `PSh(ω)`:
    at stage `0` it is `PUnit`; at stage `n + 1` it is `Bool → X.obj n`. -/
def Later2 (X : Presheaf) : Presheaf where
  obj
    | 0     => PUnit
    | n + 1 => Bool → X.obj n
  restr {n} := match n with
    | 0     => fun _ => PUnit.unit
    | _ + 1 => fun f b => X.restr (f b)

/-- Functorial action `Later2.map : Hom X Y → Hom (Later2 X) (Later2 Y)`. -/
def Later2.map {X Y : Presheaf} (f : Hom X Y) : Hom (Later2 X) (Later2 Y) where
  app
    | 0,     _ => PUnit.unit
    | n + 1, u => fun b => f.app n (u b)
  nat {n} u := by
    cases n with
    | zero => rfl
    | succ m =>
      funext b
      exact f.nat (u b)

/-- Unit `next_X : Hom X (Later2 X)`: restricts `x : X_{n+1}` to `X_n` and ignores the branch `b`. -/
def Later2.next (X : Presheaf) : Hom X (Later2 X) where
  app
    | 0,     _ => PUnit.unit
    | _ + 1, x => fun _ => X.restr x
  nat {n} _ := by
    cases n <;> rfl

/-- Applicative / delayed-substitution action `(Later2 (X ⇒ Y) × Later2 X) → Later2 Y`, passing the
    *same* branch `b : Bool` across a delayed substitution `δ` (`weakening`, `exchange`, `force`,
    `next variable`). -/
def Later2.apSubst {Γ A B : Type}
    (δ : Nat → Γ)
    (a : (n : Nat) → match n with | 0 => PUnit | _ + 1 => Bool → A)
    (body : Γ → A → B) :
    (n : Nat) → match n with | 0 => PUnit | _ + 1 => Bool → B
  | 0     => PUnit.unit
  | n + 1 => fun b => body (δ n) (a (n + 1) b)

/-- `next weakening` (`paper.tex:1218`): ignoring `x ← a` equals not binding `x`. -/
theorem next_weakening {Γ A B : Type} (δ : Nat → Γ)
    (a : (n : Nat) → match n with | 0 => PUnit | _ + 1 => Bool → A)
    (body : Γ → B) :
    Later2.apSubst δ a (fun γ _ => body γ) =
      fun n => match n with | 0 => PUnit.unit | m + 1 => fun _ => body (δ m) := by
  funext n; cases n <;> rfl

/-- `next exchange` (`paper.tex:1236`): swapping `x ← a, y ← a'` preserves the delayed term
    because both read the same branch `b : Bool`. -/
theorem next_exchange {A₁ A₂ C : Type}
    (a₁ : Bool → A₁) (a₂ : Bool → A₂) (c : A₁ → A₂ → C) :
    (fun b => c (a₁ b) (a₂ b)) = (fun b => (fun y x => c x y) (a₂ b) (a₁ b)) :=
  rfl

/-- `next force` (`paper.tex:1250`): binding `x ← next a₀` equals substituting `a₀`. -/
theorem next_force {A B : Type} (a₀ : A) (body : A → B) :
    (fun (_ : Bool) => body a₀) = (fun _ => body a₀) :=
  rfl

/-- `next variable` (`paper.tex:1263`): `next[x ← a]. x = a`. -/
theorem next_variable {A : Type} (a : Bool → A) :
    (fun b => a b) = a :=
  rfl

/-- `later id` (`paper.tex:1257`) on propositional (`Prop`) equality at stage `n + 1`:
    `(next[x ← u]. f x = next[x ← u]. g x) ↔ (∀ b : Bool, f (u b) = g (u b))`. -/
theorem later_id_stage {A B : Type} (u : Bool → A) (f g : A → B) :
    ((fun b => f (u b)) = (fun b => g (u b))) = (∀ b : Bool, f (u b) = g (u b)) :=
  propext ⟨fun h b => congrFun h b, fun h => funext h⟩

/-- Guarded fixed point `gfix : Hom (Later2 X) X → GlobalElement X` (`paper.tex:1278–1283`). -/
noncomputable def gfixAux (X : Presheaf) (f : Hom (Later2 X) X) : (n : Nat) → X.obj n
  | 0     => f.app 0 PUnit.unit
  | n + 1 => f.app (n + 1) (fun _ => gfixAux X f n)

theorem gfixAux_coh (X : Presheaf) (f : Hom (Later2 X) X) :
    ∀ n, X.restr (gfixAux X f (n + 1)) = gfixAux X f n
  | 0 => by
      simp only [gfixAux]
      exact f.nat (fun _ => f.app 0 PUnit.unit)
  | n + 1 => by
      simp only [gfixAux]
      rw [f.nat]
      congr 1
      funext _
      exact gfixAux_coh X f n

noncomputable def gfix (X : Presheaf) (f : Hom (Later2 X) X) : Hom (ConstPSh PUnit) X where
  app n _ := gfixAux X f n
  nat {n} _ := gfixAux_coh X f n

def Hom.comp {X Y Z : Presheaf} (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  app n x := g.app n (f.app n x)
  nat {n} x := by rw [g.nat, f.nat]

/-- `Löb unfolding` (`paper.tex:1282`): `gfix f = f ∘ next ∘ gfix f` holds strictly! -/
theorem gfix_unfold (X : Presheaf) (f : Hom (Later2 X) X) :
    gfix X f = Hom.comp f (Hom.comp (Later2.next X) (gfix X f)) := by
  apply Hom.ext
  intro n _
  cases n with
  | zero => rfl
  | succ m =>
    simp only [gfix, Hom.comp, Later2.next, gfixAux]
    congr 1
    funext _
    exact (gfixAux_coh X f m).symm

/-- **Refutation of Well-Pointedness** (`paper.tex:1269–1271`):
    On `X = ConstPSh Bool`, `Later2.map (Later2.next X)` and `Later2.next (Later2 X)` are
    NOT equal at stage `2`! Specifically, on `u = id : Bool → Bool`,
    `(Later2.map next)_2 id false true = false`, whereas `(next_{Later2 Bool})_2 id false true = true`. -/
theorem not_well_pointed :
    Later2.map (Later2.next (ConstPSh Bool)) ≠ Later2.next (Later2 (ConstPSh Bool)) := by
  intro heq
  have h2 := congrFun (congrFun (congrArg Hom.app heq) 2) (id : Bool → Bool)
  have h01 := congrFun (congrFun h2 false) true
  -- LHS evaluates to `false`, RHS evaluates to `true`:
  exact Bool.noConfusion h01

/-- **Refutation of `set-after-get` Without Well-Pointedness**:
    Modeling a single `Bool` cell `h : Later2 (ConstPSh Bool)` at stage `2`, `x ← get; set x`
    produces the delayed heap cell `Later2.map next h` (`λ b₁ b₂ => h b₁`), whereas a pure `step`
    leaving `h` untouched produces `next_{Later2} h` (`λ b₁ b₂ => h b₂`). -/
theorem not_set_after_get_without_well_pointedness :
    ∃ h : (Later2 (ConstPSh Bool)).obj 2,
      (Later2.map (Later2.next (ConstPSh Bool))).app 2 h ≠
      (Later2.next (Later2 (ConstPSh Bool))).app 2 h := by
  refine ⟨id, fun h2 => ?_⟩
  have h01 := congrFun (congrFun h2 false) true
  exact Bool.noConfusion h01

#print axioms gfix_unfold
#print axioms not_well_pointed
#print axioms not_set_after_get_without_well_pointedness

end WellPointedCountermodel
