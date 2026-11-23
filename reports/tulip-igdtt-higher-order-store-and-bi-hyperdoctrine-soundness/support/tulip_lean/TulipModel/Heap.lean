-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import TulipModel.World

/-!
# Semantic Types, Two-Parameter Heaplet Distributor, and Partial/Total Heaps

Constructs the step-indexed denotation `SemTy.eval` and delayed cell values
`CellVal` by pure structural recursion (zero `WellFounded.fix` in `SemTy.eval`
or `CellVal`), giving **kernel definitional equality (`rfl`)** for every `SemTy`
combinator and `CellVal 0 = PUnit.{2}`, together with:
- Two-parameter heaplet distributor `Heaplet n w_minus w_plus`,
- Total heaps `TotHeap n w = Heaplet n w w`,
- Partial heaps `ParHeap n w` (`Σ U ⊆ |w|, Heaplet n (w|_U) w`), covariant
  transport `ParHeap.map`, and partial commutative monoid (PCM) laws.
-/

namespace Tulip

/-- Lift a `Prop` into `Type 1`. -/
structure PropLift (P : Prop) : Type 1 where
  proof : P

/-- Parameterized heaplet distributor `ℋ(w⁻, w⁺)`. -/
structure HeapletOf {n : Nat} (CV : LaterTy n → World n → Type 1)
    (w_minus w_plus : World n) : Type 1 where
  get : ∀ (l : Loc) (T : LaterTy n), w_minus.cells l = some T → CV T w_plus

theorem HeapletOf.ext {n : Nat} {CV : LaterTy n → World n → Type 1}
    {w_minus w_plus : World n} {η₁ η₂ : HeapletOf CV w_minus w_plus}
    (h : ∀ l T hcell, η₁.get l T hcell = η₂.get l T hcell) : η₁ = η₂ := by
  cases η₁; cases η₂
  simp only [mk.injEq]
  funext l T hcell
  exact h l T hcell

/-- Purely structural `SemTy` evaluator parameterized by an arbitrary `CellVal` table. -/
noncomputable def evalUsing (cv : ∀ (j : Nat), LaterTy j → World j → Type 1) :
    SemTy → (n : Nat) → World n → Type 1
  | .const α,  _,     _ => ULift.{1, 0} α
  | .var _,    _,     _ => PUnit.{2}
  | .prod A B, n,     w => evalUsing cv A n w × evalUsing cv B n w
  | .sum A B,  n,     w => evalUsing cv A n w ⊕ evalUsing cv B n w
  | .arr A B,  n,     w =>
      ∀ (m : Nat) (hm : m ≤ n) (w' : World m),
        World.Le (w.restrict hm) w' → evalUsing cv A m w' → evalUsing cv B m w'
  | .comp A,   n,     w =>
      ∀ (m : Nat) (hm : m ≤ n) (w' : World m),
        World.Le (w.restrict hm) w' →
        HeapletOf (cv m) w' w' →
        StepLift m (fun j hj =>
          Σ (w'' : World j),
            PropLift (World.Le (w'.restrict hj) w'') ×
            HeapletOf (cv j) w'' w'' ×
            evalUsing cv A j w'')
  | .ref A,    n,     w =>
      ULift.{1, 0} { l : Loc // w.cells l = some (SemTy.nextAt n A) }
  | .later _,  0,     _ => PUnit.{2}
  | .later A,  k + 1, w => cv (k + 1) A w
  | .mu _,     0,     _ => PUnit.{2}
  | .mu body,  k + 1, w => cv (k + 1) (body.subst0 (.mu body)) w

/-- Fuel-stratified structural bootstrap of `CellVal`. -/
noncomputable def CellValAux : (fuel : Nat) → (n : Nat) → LaterTy n → World n → Type 1
  | 0,        _,     _, _ => PUnit.{2}
  | _ + 1,    0,     _, _ => PUnit.{2}
  | fuel + 1, k + 1, T, w => evalUsing (CellValAux fuel) T k w.trunc

/-- Delayed cell value `(▸[Z ← T]. Z w⁺)_n` stored in a heaplet at stage `n`.
`CellVal 0 T w = PUnit.{2}` holds definitionally (`rfl`). -/
noncomputable def CellVal (n : Nat) (T : LaterTy n) (w : World n) : Type 1 :=
  CellValAux n n T w

/-- Step-indexed denotation `⟦A⟧_n(w) : Type 1` of semantic program types.
Every constructor of `SemTy` unfolds definitionally (`rfl`). -/
noncomputable def SemTy.eval (n : Nat) (A : SemTy) (w : World n) : Type 1 :=
  evalUsing CellVal A n w

/-- Two-parameter heaplet distributor `ℋ(w⁻, w⁺)` (`paper.tex:1506–1512`). -/
abbrev Heaplet (n : Nat) (w_minus w_plus : World n) : Type 1 :=
  HeapletOf (CellVal n) w_minus w_plus

/-- Total heap `tH_w = ℋ(w, w)` (`paper.tex:1566`). -/
abbrev TotHeap (n : Nat) (w : World n) : Type 1 :=
  Heaplet n w w

/-- Answer bundle of the higher-order store computation monad `M A` at stage `j ≤ m`. -/
abbrev CompAns (A : SemTy) (m : Nat) (w' : World m) (j : Nat) (hj : j ≤ m) : Type 1 :=
  Σ (w'' : World j),
    PropLift (World.Le (w'.restrict hj) w'') ×
    TotHeap j w'' ×
    SemTy.eval j A w''

/-! ## Fuel Invariance and Exact Unfolding `CellVal (k + 1) T w = SemTy.eval k T w.trunc` -/

private theorem pi_eq {α : Sort u} {P Q : α → Type 1} (h : ∀ x, P x = Q x) :
    (∀ x, P x) = (∀ x, Q x) := by
  rw [show P = Q from funext h]

private theorem sigma_eq {α : Type 1} {P Q : α → Type 1} (h : ∀ x, P x = Q x) :
    Sigma P = Sigma Q := by
  rw [show P = Q from funext h]

private theorem cast_symm_cast {α β : Type 1} (h : α = β) (b : β) :
    Eq.mp h (Eq.mp h.symm b) = b := by
  cases h; rfl

private theorem symm_cast_cast {α β : Type 1} (h : α = β) (a : α) :
    Eq.mp h.symm (Eq.mp h a) = a := by
  cases h; rfl

theorem evalUsing_congr {cv₁ cv₂ : ∀ (j : Nat), LaterTy j → World j → Type 1}
    (n : Nat) (hcv : ∀ j, j ≤ n → cv₁ j = cv₂ j) (A : SemTy) :
    ∀ m, m ≤ n → ∀ (w : World m), evalUsing cv₁ A m w = evalUsing cv₂ A m w := by
  induction A with
  | const _ => intros; rfl
  | var _ => intros; rfl
  | prod B C ihB ihC =>
    intro m hm w
    simp only [evalUsing, ihB m hm w, ihC m hm w]
  | sum B C ihB ihC =>
    intro m hm w
    simp only [evalUsing, ihB m hm w, ihC m hm w]
  | arr B C ihB ihC =>
    intro m hm w
    simp only [evalUsing]
    refine pi_eq fun j => pi_eq fun hj => pi_eq fun w' => pi_eq fun _ => ?_
    rw [ihB j (Nat.le_trans hj hm) w', ihC j (Nat.le_trans hj hm) w']
  | comp B ihB =>
    intro m hm w
    simp only [evalUsing]
    refine pi_eq fun j => pi_eq fun hj => pi_eq fun w' => pi_eq fun _ => ?_
    have hj_n : j ≤ n := Nat.le_trans hj hm
    rw [hcv j hj_n]
    refine pi_eq fun _ => ?_
    have hfam :
        (fun q hq =>
          Σ (w'' : World q),
            PropLift (World.Le (w'.restrict hq) w'') ×
            HeapletOf (cv₁ q) w'' w'' ×
            evalUsing cv₁ B q w'') =
        (fun q hq =>
          Σ (w'' : World q),
            PropLift (World.Le (w'.restrict hq) w'') ×
            HeapletOf (cv₂ q) w'' w'' ×
            evalUsing cv₂ B q w'') := by
      funext q hq
      have hq_n : q ≤ n := Nat.le_trans hq hj_n
      exact sigma_eq fun w'' => by
        rw [hcv q hq_n, ihB q hq_n w'']
    rw [hfam]
  | ref _ => intros; rfl
  | later _ _ =>
    intro m hm w
    cases m with
    | zero => rfl
    | succ k =>
      simp only [evalUsing]
      rw [hcv (k + 1) hm]
  | mu _ _ =>
    intro m hm w
    cases m with
    | zero => rfl
    | succ k =>
      simp only [evalUsing]
      rw [hcv (k + 1) hm]

theorem CellValAux_irrel (f₁ : Nat) :
    ∀ f₂ j, j ≤ f₁ → j ≤ f₂ → CellValAux f₁ j = CellValAux f₂ j := by
  induction f₁ with
  | zero =>
    intro f₂ j h₁ _
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero h₁
    subst hj0
    cases f₂ <;> rfl
  | succ g₁ ih =>
    intro f₂ j h₁ h₂
    cases j with
    | zero => cases f₂ <;> rfl
    | succ k =>
      cases f₂ with
      | zero => omega
      | succ g₂ =>
        funext T w
        simp only [CellValAux]
        exact evalUsing_congr k
          (fun q hqk =>
            ih g₂ q (Nat.le_trans hqk (Nat.le_of_succ_le_succ h₁))
              (Nat.le_trans hqk (Nat.le_of_succ_le_succ h₂)))
          T k (Nat.le_refl k) w.trunc

theorem CellVal_succ_eq (k : Nat) (T : SemTy) (w : World (k + 1)) :
    CellVal (k + 1) T w = SemTy.eval k T w.trunc := by
  unfold CellVal SemTy.eval
  simp only [CellValAux]
  exact evalUsing_congr k
    (fun q hqk => CellValAux_irrel k q q hqk (Nat.le_refl q))
    T k (Nat.le_refl k) w.trunc

/-- Wrap a stage-`k` semantic value into a stage-`(k + 1)` heaplet cell value. -/
noncomputable def CellVal.ofEval {k : Nat} {T : SemTy} {w : World (k + 1)}
    (x : SemTy.eval k T w.trunc) : CellVal (k + 1) T w :=
  Eq.mp (CellVal_succ_eq k T w).symm x

/-- Project a stage-`(k + 1)` heaplet cell value to a stage-`k` semantic value. -/
noncomputable def CellVal.toEval {k : Nat} {T : SemTy} {w : World (k + 1)}
    (c : CellVal (k + 1) T w) : SemTy.eval k T w.trunc :=
  Eq.mp (CellVal_succ_eq k T w) c

@[simp]
theorem CellVal.toEval_ofEval {k : Nat} {T : SemTy} {w : World (k + 1)}
    (x : SemTy.eval k T w.trunc) :
    CellVal.toEval (CellVal.ofEval (w := w) x) = x :=
  cast_symm_cast (CellVal_succ_eq k T w) x

@[simp]
theorem CellVal.ofEval_toEval {k : Nat} {T : SemTy} {w : World (k + 1)}
    (c : CellVal (k + 1) T w) :
    CellVal.ofEval (CellVal.toEval c) = c :=
  symm_cast_cast (CellVal_succ_eq k T w) c

theorem CellVal.ofEval_inj {k : Nat} {T : SemTy} {w : World (k + 1)}
    {x y : SemTy.eval k T w.trunc}
    (h : CellVal.ofEval (w := w) x = CellVal.ofEval (w := w) y) : x = y := by
  have := congrArg CellVal.toEval h
  simpa using this

/-! ## Covariant World Transport (`SemTy.map`) and Stage Restriction (`SemTy.restrict`) -/

mutual
  /-- Covariant functorial action `w₂_* : A_n(w₁) → A_n(w₂)` along `w₁ ≤ w₂`. -/
  noncomputable def SemTy.map : {n : Nat} → {A : SemTy} → {w₁ w₂ : World n} →
      World.Le w₁ w₂ → SemTy.eval n A w₁ → SemTy.eval n A w₂
    | _,     .const _,  _,  _,  _,   x => x
    | _,     .var _,    _,  _,  _,   x => x
    | _,     .prod _ _, _,  _,  hle, (a, b) => (SemTy.map hle a, SemTy.map hle b)
    | _,     .sum _ _,  _,  _,  hle, .inl a => .inl (SemTy.map hle a)
    | _,     .sum _ _,  _,  _,  hle, .inr b => .inr (SemTy.map hle b)
    | _,     .arr _ _,  _,  _,  hle, f =>
        fun m hm w' hw' a =>
          f m hm w' (World.le_trans (World.restrict_mono hm hle) hw') a
    | _,     .comp _,   _,  _,  hle, c =>
        fun m hm w' hw' h =>
          c m hm w' (World.le_trans (World.restrict_mono hm hle) hw') h
    | n,     .ref A,    _,  _,  hle, ⟨⟨l, hl⟩⟩ =>
        ⟨⟨l, hle l (SemTy.nextAt n A) hl⟩⟩
    | 0,     .later _,  _,  _,  _,   x => x
    | k + 1, .later A,  _,  _,  hle, x => CellVal.map (k + 1) A hle x
    | 0,     .mu _,     _,  _,  _,   x => x
    | k + 1, .mu body,  _,  _,  hle, x =>
        CellVal.map (k + 1) (body.subst0 (.mu body)) hle x
  termination_by n A _ _ _ _ => (n, A.rank, 1)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  /-- Covariant functorial action on `CellVal n T w` along `w₁ ≤ w₂`. -/
  noncomputable def CellVal.map : (n : Nat) → (T : LaterTy n) → {w₁ w₂ : World n} →
      World.Le w₁ w₂ → CellVal n T w₁ → CellVal n T w₂
    | 0,     _, _, _, _,   _ => PUnit.unit
    | k + 1, T, _, _, hle, c =>
        CellVal.ofEval (SemTy.map (World.restrict_mono _ hle) (CellVal.toEval c))
  termination_by n _ _ _ _ _ => (n, 0, 0)
  decreasing_by
    simp_wf
    exact Prod.Lex.left _ _ (Nat.lt_succ_self k)
end

mutual
  theorem SemTy.map_self : ∀ {n : Nat} {A : SemTy} {w : World n}
      (hle : World.Le w w) (x : SemTy.eval n A w),
      SemTy.map hle x = x
    | _,     .const _,  _, _,   _      => by simp [SemTy.map]
    | _,     .var _,    _, _,   _      => by simp [SemTy.map]
    | _,     .prod _ _, _, hle, (a, b) => by
        simp [SemTy.map, SemTy.map_self hle a, SemTy.map_self hle b]
    | _,     .sum _ _,  _, hle, .inl a => by simp [SemTy.map, SemTy.map_self hle a]
    | _,     .sum _ _,  _, hle, .inr b => by simp [SemTy.map, SemTy.map_self hle b]
    | _,     .arr _ _,  _, _,   _      => by simp [SemTy.map]
    | _,     .comp _,   _, _,   _      => by simp [SemTy.map]
    | _,     .ref _,    _, _,   ⟨⟨_, _⟩⟩ => by simp [SemTy.map]
    | 0,     .later _,  _, _,   _      => by simp [SemTy.map]
    | k + 1, .later A,  _, hle, x      => by
        simp [SemTy.map, CellVal.map_self (k + 1) A hle x]
    | 0,     .mu _,     _, _,   _      => by simp [SemTy.map]
    | k + 1, .mu body,  _, hle, x      => by
        simp [SemTy.map, CellVal.map_self (k + 1) (body.subst0 (.mu body)) hle x]
  termination_by n A _ _ _ => (n, A.rank, 1)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  theorem CellVal.map_self : ∀ (n : Nat) (T : LaterTy n) {w : World n}
      (hle : World.Le w w) (c : CellVal n T w),
      CellVal.map n T hle c = c
    | 0,     _, _, _,   _ => rfl
    | k + 1, T, _, hle, c => by
        simp [CellVal.map, SemTy.map_self (World.restrict_mono _ hle) (CellVal.toEval c)]
  termination_by n _ _ _ _ => (n, 0, 0)
  decreasing_by
    simp_wf
    exact Prod.Lex.left _ _ (Nat.lt_succ_self k)
end

@[simp]
theorem SemTy.map_refl {n : Nat} {A : SemTy} {w : World n} (x : SemTy.eval n A w) :
    SemTy.map (World.le_refl w) x = x :=
  SemTy.map_self (World.le_refl w) x

@[simp]
theorem CellVal.map_refl {n : Nat} {T : LaterTy n} {w : World n} (c : CellVal n T w) :
    CellVal.map n T (World.le_refl w) c = c :=
  CellVal.map_self n T (World.le_refl w) c

mutual
  theorem SemTy.map_trans : ∀ {n : Nat} {A : SemTy} {w₁ w₂ w₃ : World n}
      (h12 : World.Le w₁ w₂) (h23 : World.Le w₂ w₃) (x : SemTy.eval n A w₁),
      SemTy.map h23 (SemTy.map h12 x) = SemTy.map (World.le_trans h12 h23) x
    | _,     .const _,  _, _, _, _,   _,   _      => by simp [SemTy.map]
    | _,     .var _,    _, _, _, _,   _,   _      => by simp [SemTy.map]
    | _,     .prod _ _, _, _, _, h12, h23, (a, b) => by
        simp [SemTy.map, SemTy.map_trans h12 h23 a, SemTy.map_trans h12 h23 b]
    | _,     .sum _ _,  _, _, _, h12, h23, .inl a => by
        simp [SemTy.map, SemTy.map_trans h12 h23 a]
    | _,     .sum _ _,  _, _, _, h12, h23, .inr b => by
        simp [SemTy.map, SemTy.map_trans h12 h23 b]
    | _,     .arr _ _,  _, _, _, _,   _,   _      => by simp [SemTy.map]
    | _,     .comp _,   _, _, _, _,   _,   _      => by simp [SemTy.map]
    | _,     .ref _,    _, _, _, _,   _,   ⟨⟨_, _⟩⟩ => by simp [SemTy.map]
    | 0,     .later _,  _, _, _, _,   _,   _      => by simp [SemTy.map]
    | k + 1, .later A,  _, _, _, h12, h23, x      => by
        simp [SemTy.map, CellVal.map_trans (k + 1) A h12 h23 x]
    | 0,     .mu _,     _, _, _, _,   _,   _      => by simp [SemTy.map]
    | k + 1, .mu body,  _, _, _, h12, h23, x      => by
        simp [SemTy.map, CellVal.map_trans (k + 1) (body.subst0 (.mu body)) h12 h23 x]
  termination_by n A _ _ _ _ _ _ => (n, A.rank, 1)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  theorem CellVal.map_trans : ∀ (n : Nat) (T : LaterTy n) {w₁ w₂ w₃ : World n}
      (h12 : World.Le w₁ w₂) (h23 : World.Le w₂ w₃) (c : CellVal n T w₁),
      CellVal.map n T h23 (CellVal.map n T h12 c) = CellVal.map n T (World.le_trans h12 h23) c
    | 0,     _, _, _, _, _,   _,   _ => rfl
    | k + 1, T, _, _, _, h12, h23, c => by
        simp [CellVal.map, SemTy.map_trans (World.restrict_mono _ h12)
          (World.restrict_mono _ h23) (CellVal.toEval c)]
  termination_by n _ _ _ _ _ _ _ => (n, 0, 0)
  decreasing_by
    simp_wf
    exact Prod.Lex.left _ _ (Nat.lt_succ_self k)
end

/-! ## Stage Restriction (`SemTy.restrict` and `CellVal.restrict`) -/

theorem World.trunc_restrict_le {k q : Nat} (hmn : k + 1 ≤ q + 1) (w : World (q + 1)) :
    World.Le (w.trunc.restrict (Nat.le_of_succ_le_succ hmn)) (w.restrict hmn).trunc := by
  have heq : w.trunc.restrict (Nat.le_of_succ_le_succ hmn) = (w.restrict hmn).trunc := by
    simp [World.trunc]
  rw [heq]
  exact World.le_refl _

mutual
  /-- Stage restriction `A_n(w) → A_m(w|_m)` along `m ≤ n`. -/
  noncomputable def SemTy.restrict : {m n : Nat} → (hmn : m ≤ n) → {A : SemTy} → {w : World n} →
      SemTy.eval n A w → SemTy.eval m A (w.restrict hmn)
    | _,     _,     _,   .const _,  _, x => x
    | _,     _,     _,   .var _,    _, x => x
    | _,     _,     hmn, .prod _ _, _, (a, b) => (SemTy.restrict hmn a, SemTy.restrict hmn b)
    | _,     _,     hmn, .sum _ _,  _, .inl a => .inl (SemTy.restrict hmn a)
    | _,     _,     hmn, .sum _ _,  _, .inr b => .inr (SemTy.restrict hmn b)
    | _,     _,     hmn, .arr _ _,  w, f =>
        fun j hj w' hw' a =>
          f j (Nat.le_trans hj hmn) w'
            (by simpa [World.restrict_trans] using hw') a
    | _,     _,     hmn, .comp _,   w, c =>
        fun j hj w' hw' h =>
          c j (Nat.le_trans hj hmn) w'
            (by simpa [World.restrict_trans] using hw') h
    | _,     _,     hmn, .ref _,    _, ⟨⟨l, hl⟩⟩ =>
        ⟨⟨l, by simp [World.restrict_cells, hl]⟩⟩
    | 0,     _,     _,   .later _,  _, _ => PUnit.unit
    | _ + 1, 0,     hmn, .later _,  _, _ => nomatch hmn
    | _ + 1, _ + 1, hmn, .later A,  _, x => CellVal.restrict hmn A x
    | 0,     _,     _,   .mu _,     _, _ => PUnit.unit
    | _ + 1, 0,     hmn, .mu _,     _, _ => nomatch hmn
    | _ + 1, _ + 1, hmn, .mu body,  _, x =>
        CellVal.restrict hmn (body.subst0 (.mu body)) x
  termination_by _ n _ A _ _ => (n, A.rank, 1)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  /-- Stage restriction on `CellVal` along `m ≤ n`. -/
  noncomputable def CellVal.restrict : {m n : Nat} → (hmn : m ≤ n) → (T : LaterTy n) → {w : World n} →
      CellVal n T w → CellVal m (LaterTy.restrict hmn T) (w.restrict hmn)
    | 0,     _,     _,   _, _, _ => PUnit.unit
    | _ + 1, 0,     hmn, _, _, _ => nomatch hmn
    | _ + 1, q + 1, hmn, T, w, c =>
        CellVal.ofEval
          (SemTy.map (World.trunc_restrict_le hmn w)
            (SemTy.restrict (Nat.le_of_succ_le_succ hmn) (CellVal.toEval c)))
  termination_by _ n _ _ _ _ => (n, 0, 0)
  decreasing_by
    simp_wf
    exact Prod.Lex.left _ _ (Nat.lt_succ_self q)
end

mutual
  theorem SemTy.restrict_map_comm : ∀ {m n : Nat} (hmn : m ≤ n) {A : SemTy}
      {w₁ w₂ : World n} (hle : World.Le w₁ w₂) (x : SemTy.eval n A w₁),
      SemTy.restrict hmn (SemTy.map hle x) =
        SemTy.map (World.restrict_mono hmn hle) (SemTy.restrict hmn x)
    | _,     _,     _,   .const _,  _,  _,  _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _,     _,     _,   .var _,    _,  _,  _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _,     _,     hmn, .prod _ _, _,  _,  hle, (a, b) => by
        simp [SemTy.restrict, SemTy.map,
          SemTy.restrict_map_comm hmn hle a, SemTy.restrict_map_comm hmn hle b]
    | _,     _,     hmn, .sum _ _,  _,  _,  hle, .inl a => by
        simp [SemTy.restrict, SemTy.map, SemTy.restrict_map_comm hmn hle a]
    | _,     _,     hmn, .sum _ _,  _,  _,  hle, .inr b => by
        simp [SemTy.restrict, SemTy.map, SemTy.restrict_map_comm hmn hle b]
    | _,     _,     _,   .arr _ _,  _,  _,  _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _,     _,     _,   .comp _,   _,  _,  _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _,     _,     _,   .ref _,    _,  _,  _,   ⟨⟨_, _⟩⟩ => by simp [SemTy.restrict, SemTy.map]
    | 0,     _,     _,   .later _,  _,  _,  _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _ + 1, 0,     hmn, .later _,  _,  _,  _,   _      => nomatch hmn
    | k + 1, q + 1, hmn, .later A,  _,  _,  hle, x      => by
        simpa only [SemTy.restrict, SemTy.map, LaterTy.restrict] using
          CellVal.restrict_map_comm hmn A hle x
    | 0,     _,     _,   .mu _,     _,  _,  _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _ + 1, 0,     hmn, .mu _,     _,  _,  _,   _      => nomatch hmn
    | k + 1, q + 1, hmn, .mu body,  _,  _,  hle, x      => by
        simpa only [SemTy.restrict, SemTy.map, LaterTy.restrict] using
          CellVal.restrict_map_comm hmn (body.subst0 (.mu body)) hle x
  termination_by _ n _ A _ _ _ _ => (n, A.rank, 1)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  theorem CellVal.restrict_map_comm : ∀ {m n : Nat} (hmn : m ≤ n) (T : LaterTy n)
      {w₁ w₂ : World n} (hle : World.Le w₁ w₂) (c : CellVal n T w₁),
      CellVal.restrict hmn T (CellVal.map n T hle c) =
        CellVal.map m (LaterTy.restrict hmn T) (World.restrict_mono hmn hle)
          (CellVal.restrict hmn T c)
    | 0,     _,     _,   _, _,  _,  _,   _ => rfl
    | _ + 1, 0,     hmn, _, _,  _,  _,   _ => nomatch hmn
    | _ + 1, q + 1, hmn, T, w₁, w₂, hle, c => by
        simp only [CellVal.restrict, CellVal.map, LaterTy.restrict,
          CellVal.toEval_ofEval,
          SemTy.restrict_map_comm (Nat.le_of_succ_le_succ hmn)
            (World.restrict_mono _ hle) (CellVal.toEval c),
          SemTy.map_trans]
  termination_by _ n _ _ _ _ _ _ => (n, 0, 0)
  decreasing_by
    simp_wf
    exact Prod.Lex.left _ _ (Nat.lt_succ_self q)
end

/-- Encode a semantic value `a : A_n(w)` as a delayed cell value `next_n a`. -/
noncomputable def CellVal.nextVal : {n : Nat} → {A : SemTy} → {w : World n} →
    SemTy.eval n A w → CellVal n (SemTy.nextAt n A) w
  | 0,     _, _, _ => PUnit.unit
  | k + 1, _, _, a => CellVal.ofEval (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl k)) a)

theorem CellVal.map_nextVal {n : Nat} {A : SemTy} {w₁ w₂ : World n}
    (hle : World.Le w₁ w₂) (a : SemTy.eval n A w₁) :
    CellVal.map n (SemTy.nextAt n A) hle (CellVal.nextVal a) =
      CellVal.nextVal (SemTy.map hle a) := by
  cases n with
  | zero => rfl
  | succ k =>
    simp [CellVal.nextVal, CellVal.map, SemTy.nextAt, SemTy.restrict_map_comm]

theorem CellVal.trunc_nextVal_succ {j : Nat} {A : SemTy} {w : World (j + 2)}
    (a : SemTy.eval (j + 2) A w) :
    CellVal.restrict (Nat.le_succ_of_le (Nat.le_refl (j + 1))) A (CellVal.nextVal a) =
      CellVal.nextVal (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl (j + 1))) a) := by
  simp [CellVal.nextVal, CellVal.restrict, SemTy.nextAt, LaterTy.restrict]

/-! ## Heaplet Distributor Operations -/

/-- Contravariant action in `w_minus`: restrict a heaplet's domain along `w₁ ≤ w₂`. -/
noncomputable def Heaplet.contraMap {n : Nat} {w₁ w₂ w_plus : World n}
    (hle : World.Le w₁ w₂) (η : Heaplet n w₂ w_plus) : Heaplet n w₁ w_plus where
  get l T hl := η.get l T (hle l T hl)

/-- Covariant action in `w_plus`: push cell values along `w₁ ≤ w₂`. -/
noncomputable def Heaplet.covMap {n : Nat} {w_minus w₁ w₂ : World n}
    (hle : World.Le w₁ w₂) (η : Heaplet n w_minus w₁) : Heaplet n w_minus w₂ where
  get l T hl := CellVal.map n T hle (η.get l T hl)

@[simp]
theorem Heaplet.covMap_refl {n : Nat} {w_minus w : World n} (η : Heaplet n w_minus w) :
    Heaplet.covMap (World.le_refl w) η = η := by
  apply HeapletOf.ext
  intro l T hl
  simp [Heaplet.covMap]

theorem Heaplet.covMap_trans {n : Nat} {w_minus w₁ w₂ w₃ : World n}
    (h12 : World.Le w₁ w₂) (h23 : World.Le w₂ w₃) (η : Heaplet n w_minus w₁) :
    Heaplet.covMap h23 (Heaplet.covMap h12 η) =
      Heaplet.covMap (World.le_trans h12 h23) η := by
  apply HeapletOf.ext
  intro l T hl
  simp [Heaplet.covMap, CellVal.map_trans]

private theorem restrict_cells_inv {k q : Nat} {hmn : k + 1 ≤ q + 1} {w : World (q + 1)}
    {l : Loc} {T : SemTy} (hl : (w.restrict hmn).cells l = some T) :
    w.cells l = some T := by
  simp only [World.restrict_cells] at hl
  cases hc : w.cells l with
  | none => rw [hc] at hl; contradiction
  | some T' =>
    rw [hc] at hl
    simp only [Option.map, LaterTy.restrict, Option.some.injEq] at hl
    subst hl
    rfl

/-- Stage restriction on heaplets along `m ≤ n` (match-free in data position!). -/
noncomputable def Heaplet.restrict : {m n : Nat} → (hmn : m ≤ n) → {w_minus w_plus : World n} →
    Heaplet n w_minus w_plus → Heaplet m (w_minus.restrict hmn) (w_plus.restrict hmn)
  | 0,     _,     _,   _, _, _ => { get := fun _ _ _ => PUnit.unit }
  | _ + 1, 0,     hmn, _, _, _ => nomatch hmn
  | _ + 1, _ + 1, hmn, _, _, η =>
      { get := fun l T hl => CellVal.restrict hmn T (η.get l T (restrict_cells_inv hl)) }

/-- Single-step truncation on total heaps `TotHeap (k + 1) w → TotHeap k w.trunc`. -/
noncomputable abbrev TotHeap.trunc {k : Nat} {w : World (k + 1)} (h : TotHeap (k + 1) w) :
    TotHeap k w.trunc :=
  Heaplet.restrict (Nat.le_succ_of_le (Nat.le_refl k)) h

/-- Empty heaplet over `World.empty n`. -/
noncomputable def Heaplet.empty {n : Nat} (w_plus : World n) : Heaplet n (World.empty n) w_plus where
  get _ _ hl := nomatch hl

/-- Update location `l` in a total heap `h : TotHeap n w` when `w.cells l = some (nextAt n A)`. -/
noncomputable def TotHeap.update {n : Nat} {w : World n} {A : SemTy} (h : TotHeap n w)
    (l : Loc) (hl : w.cells l = some (SemTy.nextAt n A)) (c : CellVal n (SemTy.nextAt n A) w) :
    TotHeap n w where
  get l' T hl' :=
    if heq : l' = l then by
      subst heq
      rw [hl] at hl'
      injection hl' with hT
      subst hT
      exact c
    else
      h.get l' T hl'

@[simp]
theorem TotHeap.update_same {n : Nat} {w : World n} {A : SemTy} (h : TotHeap n w)
    (l : Loc) (hl : w.cells l = some (SemTy.nextAt n A)) (c : CellVal n (SemTy.nextAt n A) w) :
    (h.update l hl c).get l (SemTy.nextAt n A) hl = c := by
  simp [TotHeap.update]

@[simp]
theorem TotHeap.update_other {n : Nat} {w : World n} {A : SemTy} (h : TotHeap n w)
    (l l' : Loc) (hne : l' ≠ l) (hl : w.cells l = some (SemTy.nextAt n A))
    (c : CellVal n (SemTy.nextAt n A) w) (T : LaterTy n) (hl' : w.cells l' = some T) :
    (h.update l hl c).get l' T hl' = h.get l' T hl' := by
  simp [TotHeap.update, hne]

@[simp]
theorem TotHeap.update_update {n : Nat} {w : World n} {A : SemTy} (h : TotHeap n w)
    (l : Loc) (hl : w.cells l = some (SemTy.nextAt n A))
    (c₁ c₂ : CellVal n (SemTy.nextAt n A) w) :
    (h.update l hl c₁).update l hl c₂ = h.update l hl c₂ := by
  apply HeapletOf.ext
  intro l' T hl'
  by_cases heq : l' = l
  · subst heq
    rw [hl] at hl'
    injection hl' with hT
    subst hT
    simp [TotHeap.update]
  · simp [TotHeap.update, heq]

@[simp]
theorem TotHeap.update_self {n : Nat} {w : World n} {A : SemTy} (h : TotHeap n w)
    (l : Loc) (hl : w.cells l = some (SemTy.nextAt n A)) :
    h.update l hl (h.get l (SemTy.nextAt n A) hl) = h := by
  apply HeapletOf.ext
  intro l' T hl'
  by_cases heq : l' = l
  · subst heq
    rw [hl] at hl'
    injection hl' with hT
    subst hT
    simp [TotHeap.update]
  · simp [TotHeap.update, heq]

theorem TotHeap.trunc_update {k : Nat} {w : World (k + 1)} {A : SemTy} (h : TotHeap (k + 1) w)
    (l : Loc) (hl : w.cells l = some A) (a : SemTy.eval (k + 1) A w) :
    TotHeap.trunc (h.update (A := A) l hl (CellVal.nextVal a)) =
      (TotHeap.trunc h).update (A := A) l
        (by cases k <;> simp [World.trunc, World.restrict_cells, SemTy.nextAt, LaterTy.restrict, hl])
        (CellVal.nextVal (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl k)) a)) := by
  cases k with
  | zero =>
    apply HeapletOf.ext
    intro _ _ _
    rfl
  | succ j =>
    apply HeapletOf.ext
    intro l' T hl'
    by_cases heq : l' = l
    · subst heq
      have hw : w.cells l' = some T := restrict_cells_inv hl'
      have hAT : A = T := Option.some.inj (hl.symm.trans hw)
      subst hAT
      simp [TotHeap.trunc, Heaplet.restrict, TotHeap.update, CellVal.trunc_nextVal_succ]
    · simp [TotHeap.trunc, Heaplet.restrict, TotHeap.update, heq]

private theorem insert_fresh_other_inv {n : Nat} {w : World n} {T₀ T : LaterTy n} {l : Loc}
    (hne : l ≠ w.fresh) (hl : (w.insert w.fresh T₀).cells l = some T) :
    w.cells l = some T := by
  simp only [World.insert_cells, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte] at hl
  exact hl

private theorem insert_fresh_same_inv {n : Nat} {w : World n} {T₀ T : LaterTy n}
    (hl : (w.insert w.fresh T₀).cells w.fresh = some T) : T₀ = T := by
  simp only [World.insert_cells, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
  exact hl

/-- Extend a total heap `h : TotHeap n w` at fresh location `w.fresh` with initial cell `c`. -/
noncomputable def TotHeap.alloc {n : Nat} {w : World n} {A : SemTy} (h : TotHeap n w)
    (c : CellVal n (SemTy.nextAt n A) (w.insert w.fresh (SemTy.nextAt n A))) :
    TotHeap n (w.insert w.fresh (SemTy.nextAt n A)) where
  get l T hl :=
    if heq : l = w.fresh then
      Eq.mp
        (congrArg (fun X => CellVal n X (w.insert w.fresh (SemTy.nextAt n A)))
          (insert_fresh_same_inv (heq ▸ hl)))
        c
    else
      CellVal.map n T (World.le_insert_fresh w (SemTy.nextAt n A))
        (h.get l T (insert_fresh_other_inv heq hl))

@[simp]
theorem TotHeap.alloc_update_fresh {n : Nat} {w : World n} {A : SemTy} (h : TotHeap n w)
    (c₁ c₂ : CellVal n (SemTy.nextAt n A) (w.insert w.fresh (SemTy.nextAt n A))) :
    (h.alloc c₁).update w.fresh (by simp) c₂ = h.alloc c₂ := by
  apply HeapletOf.ext
  intro l T hl
  by_cases heq : l = w.fresh
  · subst heq
    have hT := insert_fresh_same_inv hl
    subst hT
    simp [TotHeap.update, TotHeap.alloc]
  · simp [TotHeap.update, TotHeap.alloc, heq]

/-! ## Partial Heaps `ParHeap n w` and Partial Commutative Monoid (PCM) Structure -/

/-- A partial heap `h : ParHeap n w` (`paper.tex:1522–1530`) consists of a support
predicate `dom : Loc → Bool` contained in `|w|` together with a heaplet
`eta : Heaplet n (w.restrictDom dom) w`. -/
structure ParHeap (n : Nat) (w : World n) : Type 1 where
  dom     : Loc → Bool
  dom_sub : ∀ l, dom l = true → (w.cells l).isSome = true
  eta     : Heaplet n (w.restrictDom dom) w

/-- Supporting world `|h| = w|_{dom(h)}` (`paper.tex:1524`). -/
noncomputable def ParHeap.suppWorld {n : Nat} {w : World n} (h : ParHeap n w) : World n :=
  w.restrictDom h.dom

theorem ParHeap.suppWorld_le {n : Nat} {w : World n} (h : ParHeap n w) :
    World.Le h.suppWorld w :=
  w.restrictDom_le h.dom

theorem ParHeap.ext {n : Nat} {w : World n} {h₁ h₂ : ParHeap n w}
    (hdom : ∀ l, h₁.dom l = h₂.dom l)
    (heta : ∀ l T (hd₁ : h₁.dom l = true) (hw : w.cells l = some T),
      h₁.eta.get l T (by simp [hd₁, hw]) =
        h₂.eta.get l T (by simp [← hdom l, hd₁, hw])) :
    h₁ = h₂ := by
  rcases h₁ with ⟨d₁, s₁, e₁⟩
  rcases h₂ with ⟨d₂, s₂, e₂⟩
  have hd : d₁ = d₂ := funext hdom
  subst hd
  have hs : s₁ = s₂ := Subsingleton.elim s₁ s₂
  subst hs
  congr 1
  apply HeapletOf.ext
  intro l T hcell
  simp only [World.restrictDom_cells] at hcell
  cases hd₁ : d₁ l
  · rw [hd₁] at hcell; contradiction
  · simp only [hd₁, ↓reduceIte] at hcell
    exact heta l T hd₁ hcell

/-- Empty partial heap `∅ : ParHeap n w`. -/
noncomputable def ParHeap.empty (n : Nat) (w : World n) : ParHeap n w where
  dom     := fun _ => false
  dom_sub := fun _ h => nomatch h
  eta     := { get := fun l _ hl => by simp [World.restrictDom_cells] at hl }

@[simp]
theorem ParHeap.empty_dom (n : Nat) (w : World n) (l : Loc) :
    (ParHeap.empty n w).dom l = false := rfl

@[simp]
theorem ParHeap.suppWorld_empty (n : Nat) (w : World n) :
    (ParHeap.empty n w).suppWorld = World.empty n := by
  apply World.ext
  intro l
  simp [ParHeap.suppWorld]

private theorem singleton_cell_eq {n : Nat} {w : World n} {l l' : Loc} {T₀ T : LaterTy n}
    (hl : w.cells l = some T₀)
    (hcell : (w.restrictDom (fun x => x == l)).cells l' = some T) :
    l' = l ∧ T₀ = T := by
  simp only [World.restrictDom_cells] at hcell
  cases hbeq : l' == l
  · rw [hbeq] at hcell; contradiction
  · have heq : l' = l := eq_of_beq hbeq
    subst heq
    simp only [beq_self_eq_true, ↓reduceIte, hl, Option.some.injEq] at hcell
    exact ⟨rfl, hcell⟩

/-- Singleton partial heap `{l ↦ next a}` (`paper.tex:1820`). -/
noncomputable def ParHeap.singleton {n : Nat} {w : World n} {A : SemTy}
    (l : Loc) (hl : w.cells l = some (SemTy.nextAt n A)) (a : SemTy.eval n A w) :
    ParHeap n w where
  dom     := fun l' => l' == l
  dom_sub := by
    intro l' h
    have heq : l' = l := eq_of_beq h
    subst heq
    simp [hl]
  eta     := {
    get := fun _ _ hcell =>
      Eq.mp (congrArg (fun X => CellVal n X w) (singleton_cell_eq hl hcell).2)
        (CellVal.nextVal a)
  }

@[simp]
theorem ParHeap.singleton_dom {n : Nat} {w : World n} {A : SemTy}
    (l : Loc) (hl : w.cells l = some (SemTy.nextAt n A)) (a : SemTy.eval n A w) (l' : Loc) :
    (ParHeap.singleton l hl a).dom l' = (l' == l) := rfl

private theorem map_restrictDom_cell {n : Nat} {w₁ w₂ : World n}
    (hle : World.Le w₁ w₂) (h : ParHeap n w₁) {l : Loc} {T : LaterTy n}
    (hcell : (w₂.restrictDom h.dom).cells l = some T) :
    (w₁.restrictDom h.dom).cells l = some T := by
  simp only [World.restrictDom_cells] at hcell ⊢
  cases hd : h.dom l
  · rw [hd] at hcell; contradiction
  · simp only [hd, ↓reduceIte] at hcell ⊢
    have hs := h.dom_sub l hd
    cases hc₁ : w₁.cells l with
    | none => rw [hc₁] at hs; contradiction
    | some T₁ =>
      have hc₂ := hle l T₁ hc₁
      rw [hc₂] at hcell
      exact hcell

/-- Covariant functoriality `w₂_* h` of partial heaps along `w₁ ≤ w₂` (`paper.tex:1528`),
with zero `match` or `subst` in data position! -/
noncomputable def ParHeap.map {n : Nat} {w₁ w₂ : World n} (hle : World.Le w₁ w₂)
    (h : ParHeap n w₁) : ParHeap n w₂ where
  dom     := h.dom
  dom_sub := by
    intro l hd
    have hs := h.dom_sub l hd
    cases hc : w₁.cells l with
    | none => rw [hc] at hs; contradiction
    | some T => simp [hle l T hc]
  eta     := {
    get := fun l T hcell =>
      CellVal.map n T hle (h.eta.get l T (map_restrictDom_cell hle h hcell))
  }

@[simp]
theorem ParHeap.map_dom {n : Nat} {w₁ w₂ : World n} (hle : World.Le w₁ w₂)
    (h : ParHeap n w₁) (l : Loc) :
    (h.map hle).dom l = h.dom l := rfl

@[simp]
theorem ParHeap.suppWorld_map {n : Nat} {w₁ w₂ : World n} (hle : World.Le w₁ w₂)
    (h : ParHeap n w₁) :
    (h.map hle).suppWorld = h.suppWorld := by
  apply World.ext
  intro l
  simp only [ParHeap.suppWorld, World.restrictDom_cells, ParHeap.map_dom]
  by_cases hd : h.dom l = true
  · have hs := h.dom_sub l hd
    cases hc : w₁.cells l with
    | none => rw [hc] at hs; contradiction
    | some T => simp [hd, hle l T hc]
  · simp [hd]

@[simp]
theorem ParHeap.map_refl {n : Nat} {w : World n} (h : ParHeap n w) :
    h.map (World.le_refl w) = h := by
  refine ParHeap.ext (fun _ => rfl) ?_
  intro l T _ _
  simp [ParHeap.map]

theorem ParHeap.map_trans {n : Nat} {w₁ w₂ w₃ : World n}
    (h12 : World.Le w₁ w₂) (h23 : World.Le w₂ w₃) (h : ParHeap n w₁) :
    (h.map h12).map h23 = h.map (World.le_trans h12 h23) := by
  refine ParHeap.ext (fun _ => rfl) ?_
  intro l T _ _
  simp [ParHeap.map, CellVal.map_trans]

theorem ParHeap.map_singleton {n : Nat} {w₁ w₂ : World n} {A : SemTy}
    (hle : World.Le w₁ w₂) (l : Loc) (hl : w₁.cells l = some (SemTy.nextAt n A))
    (a : SemTy.eval n A w₁) :
    (ParHeap.singleton l hl a).map hle =
      ParHeap.singleton l (hle l _ hl) (SemTy.map hle a) := by
  refine ParHeap.ext (fun _ => rfl) ?_
  intro l' T hd hw₂
  have heq : l' = l := eq_of_beq hd
  subst heq
  have hT : SemTy.nextAt n A = T := Option.some.inj ((hle l' _ hl).symm.trans hw₂)
  subst hT
  simp [ParHeap.map, ParHeap.singleton, CellVal.map_nextVal]

/-- Disjointness `h₁ # h₂` of partial heaps (`paper.tex:1535`). -/
def ParHeap.Disjoint {n : Nat} {w : World n} (h₁ h₂ : ParHeap n w) : Prop :=
  ∀ l, h₁.dom l = false ∨ h₂.dom l = false

theorem ParHeap.Disjoint.symm {n : Nat} {w : World n} {h₁ h₂ : ParHeap n w}
    (hd : ParHeap.Disjoint h₁ h₂) : ParHeap.Disjoint h₂ h₁ :=
  fun l => (hd l).symm

theorem ParHeap.disjoint_empty_left {n : Nat} {w : World n} (h : ParHeap n w) :
    ParHeap.Disjoint (ParHeap.empty n w) h :=
  fun _ => Or.inl rfl

theorem ParHeap.disjoint_empty_right {n : Nat} {w : World n} (h : ParHeap n w) :
    ParHeap.Disjoint h (ParHeap.empty n w) :=
  fun _ => Or.inr rfl

theorem ParHeap.Disjoint.worldDisjoint {n : Nat} {w : World n} {h₁ h₂ : ParHeap n w}
    (hd : ParHeap.Disjoint h₁ h₂) : World.Disjoint h₁.suppWorld h₂.suppWorld := by
  intro l
  simp only [ParHeap.suppWorld, World.restrictDom_cells]
  rcases hd l with d1 | d2
  · left; simp [d1]
  · right; simp [d2]

private theorem union_left_cell {n : Nat} {w : World n} {h₁ h₂ : ParHeap n w} {l : Loc}
    {T : LaterTy n} (d1 : h₁.dom l = true)
    (hcell : (w.restrictDom (fun x => h₁.dom x || h₂.dom x)).cells l = some T) :
    (w.restrictDom h₁.dom).cells l = some T := by
  simp only [World.restrictDom_cells, d1, Bool.true_or, ↓reduceIte] at hcell ⊢
  exact hcell

private theorem union_right_cell {n : Nat} {w : World n} {h₁ h₂ : ParHeap n w} {l : Loc}
    {T : LaterTy n} (nd1 : ¬ h₁.dom l = true)
    (hcell : (w.restrictDom (fun x => h₁.dom x || h₂.dom x)).cells l = some T) :
    (w.restrictDom h₂.dom).cells l = some T := by
  have d1f : h₁.dom l = false := Bool.eq_false_iff.mpr nd1
  simp only [World.restrictDom_cells, d1f, Bool.false_or] at hcell ⊢
  exact hcell

/-- Total left-biased union `h₁ · h₂` of partial heaps (`paper.tex:1550–1559`),
forming a partial commutative monoid under `ParHeap.Disjoint`. -/
noncomputable def ParHeap.union {n : Nat} {w : World n} (h₁ h₂ : ParHeap n w) : ParHeap n w where
  dom     := fun l => h₁.dom l || h₂.dom l
  dom_sub := by
    intro l hd
    cases d1 : h₁.dom l
    · rw [d1, Bool.false_or] at hd
      exact h₂.dom_sub l hd
    · exact h₁.dom_sub l d1
  eta     := {
    get := fun l T hcell =>
      if d1 : h₁.dom l = true then
        h₁.eta.get l T (union_left_cell d1 hcell)
      else
        h₂.eta.get l T (union_right_cell d1 hcell)
  }

@[simp]
theorem ParHeap.union_dom {n : Nat} {w : World n} (h₁ h₂ : ParHeap n w) (l : Loc) :
    (h₁.union h₂).dom l = (h₁.dom l || h₂.dom l) := rfl

@[simp]
theorem ParHeap.suppWorld_union {n : Nat} {w : World n} (h₁ h₂ : ParHeap n w) :
    (h₁.union h₂).suppWorld = h₁.suppWorld.union h₂.suppWorld := by
  apply World.ext
  intro l
  simp only [ParHeap.suppWorld, World.restrictDom_cells, World.union_cells, ParHeap.union_dom]
  by_cases d1 : h₁.dom l = true <;> by_cases d2 : h₂.dom l = true <;>
    cases w.cells l <;> simp [d1, d2]

theorem ParHeap.union_comm {n : Nat} {w : World n} {h₁ h₂ : ParHeap n w}
    (hd : ParHeap.Disjoint h₁ h₂) : h₁.union h₂ = h₂.union h₁ := by
  refine ParHeap.ext (fun l => Bool.or_comm (h₁.dom l) (h₂.dom l)) ?_
  intro l T hdom _
  rcases hd l with d1 | d2
  · simp only [ParHeap.union_dom, d1, Bool.false_or] at hdom
    simp [ParHeap.union, d1, hdom]
  · simp only [ParHeap.union_dom, d2, Bool.or_false] at hdom
    simp [ParHeap.union, d2, hdom]

theorem ParHeap.union_assoc {n : Nat} {w : World n} (h₁ h₂ h₃ : ParHeap n w) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  refine ParHeap.ext (fun l => Bool.or_assoc (h₁.dom l) (h₂.dom l) (h₃.dom l)) ?_
  intro l T _ _
  cases d1 : h₁.dom l <;> cases d2 : h₂.dom l <;> simp [ParHeap.union, d1, d2]

@[simp]
theorem ParHeap.union_empty {n : Nat} {w : World n} (h : ParHeap n w) :
    h.union (ParHeap.empty n w) = h := by
  refine ParHeap.ext (fun l => Bool.or_false (h.dom l)) ?_
  intro l T hd _
  simp only [ParHeap.union_dom, ParHeap.empty_dom, Bool.or_false] at hd
  simp [ParHeap.union, hd]

@[simp]
theorem ParHeap.empty_union {n : Nat} {w : World n} (h : ParHeap n w) :
    (ParHeap.empty n w).union h = h := by
  refine ParHeap.ext (fun l => Bool.false_or (h.dom l)) ?_
  intro l T _ _
  simp [ParHeap.union]

theorem ParHeap.map_union {n : Nat} {w₁ w₂ : World n} (hle : World.Le w₁ w₂)
    (h₁ h₂ : ParHeap n w₁) :
    (h₁.union h₂).map hle = (h₁.map hle).union (h₂.map hle) := by
  refine ParHeap.ext (fun _ => rfl) ?_
  intro l T _ _
  cases d1 : h₁.dom l <;> simp [ParHeap.map, ParHeap.union, d1]

/-- PCM extension order `h₁ ≤ h₂` (`∃ h₃, h₁ # h₃ ∧ h₂ = h₁ · h₃`, `paper.tex:1583`). -/
def ParHeap.Le {n : Nat} {w : World n} (h₁ h₂ : ParHeap n w) : Prop :=
  ∃ h₃ : ParHeap n w, ParHeap.Disjoint h₁ h₃ ∧ h₂ = h₁.union h₃

theorem ParHeap.le_refl {n : Nat} {w : World n} (h : ParHeap n w) : ParHeap.Le h h :=
  ⟨ParHeap.empty n w, ParHeap.disjoint_empty_right h, (ParHeap.union_empty h).symm⟩

theorem ParHeap.le_trans {n : Nat} {w : World n} {h₁ h₂ h₃ : ParHeap n w}
    (h12 : ParHeap.Le h₁ h₂) (h23 : ParHeap.Le h₂ h₃) : ParHeap.Le h₁ h₃ := by
  rcases h12 with ⟨d₁, hd₁, rfl⟩
  rcases h23 with ⟨d₂, hd₂, rfl⟩
  refine ⟨d₁.union d₂, ?_, ParHeap.union_assoc h₁ d₁ d₂⟩
  intro l
  rcases hd₁ l with e1 | e2
  · left; exact e1
  · rcases hd₂ l with f1 | f2
    · simp only [ParHeap.union_dom, Bool.or_eq_false_iff] at f1
      left; exact f1.1
    · right; simp [e2, f2]

theorem ParHeap.empty_le {n : Nat} {w : World n} (h : ParHeap n w) :
    ParHeap.Le (ParHeap.empty n w) h :=
  ⟨h, ParHeap.disjoint_empty_left h, (ParHeap.empty_union h).symm⟩

theorem ParHeap.map_mono {n : Nat} {w₁ w₂ : World n} (hle : World.Le w₁ w₂)
    {h₁ h₂ : ParHeap n w₁} (hh : ParHeap.Le h₁ h₂) :
    ParHeap.Le (h₁.map hle) (h₂.map hle) := by
  rcases hh with ⟨h₃, hd, rfl⟩
  exact ⟨h₃.map hle, hd, ParHeap.map_union hle h₁ h₃⟩

private theorem restrict_parHeap_cell {k q : Nat} {hmn : k + 1 ≤ q + 1}
    {w : World (q + 1)} {U : Loc → Bool} {l : Loc} {T : SemTy}
    (hcell : ((w.restrict hmn).restrictDom U).cells l = some T) :
    (w.restrictDom U).cells l = some T := by
  simp only [World.restrictDom_cells] at hcell ⊢
  cases hU : U l
  · rw [hU] at hcell; contradiction
  · simp only [hU, ↓reduceIte] at hcell ⊢
    exact restrict_cells_inv hcell

/-- Stage restriction on partial heaps along `m ≤ n` (match-free in data position!). -/
noncomputable def ParHeap.restrict : {m n : Nat} → (hmn : m ≤ n) → {w : World n} →
    ParHeap n w → ParHeap m (w.restrict hmn)
  | 0,     _,     hmn, w, h => {
      dom     := h.dom
      dom_sub := by
        intro l hd
        have hs := h.dom_sub l hd
        simp only [World.restrict_cells]
        cases hc : w.cells l with
        | none => rw [hc] at hs; contradiction
        | some _ => rfl
      eta     := { get := fun _ _ _ => PUnit.unit }
    }
  | _ + 1, 0,     hmn, _, _ => nomatch hmn
  | _ + 1, _ + 1, hmn, w, h => {
      dom     := h.dom
      dom_sub := by
        intro l hd
        have hs := h.dom_sub l hd
        simp only [World.restrict_cells]
        cases hc : w.cells l with
        | none => rw [hc] at hs; contradiction
        | some _ => rfl
      eta     := {
        get := fun l T hcell =>
          CellVal.restrict hmn T (h.eta.get l T (restrict_parHeap_cell hcell))
      }
    }

@[simp]
theorem ParHeap.restrict_dom {m n : Nat} (hmn : m ≤ n) {w : World n}
    (h : ParHeap n w) (l : Loc) :
    (h.restrict hmn).dom l = h.dom l := by
  cases m with
  | zero => rfl
  | succ _ => cases n with | zero => exact nomatch hmn | succ _ => rfl

@[simp]
theorem ParHeap.suppWorld_restrict {m n : Nat} (hmn : m ≤ n) {w : World n}
    (h : ParHeap n w) :
    (h.restrict hmn).suppWorld = h.suppWorld.restrict hmn := by
  apply World.ext
  intro l
  simp only [ParHeap.suppWorld, World.restrictDom_cells, World.restrict_cells, ParHeap.restrict_dom]
  cases h.dom l <;> rfl

theorem ParHeap.restrict_union {m n : Nat} (hmn : m ≤ n) {w : World n}
    (h₁ h₂ : ParHeap n w) :
    (h₁.union h₂).restrict hmn = (h₁.restrict hmn).union (h₂.restrict hmn) := by
  refine ParHeap.ext (fun _ => by simp) ?_
  intro l T _ _
  cases m with
  | zero => rfl
  | succ k =>
    cases n with
    | zero => exact nomatch hmn
    | succ q =>
      cases d1 : h₁.dom l <;> simp [ParHeap.restrict, ParHeap.union, d1]

theorem ParHeap.restrict_empty {m n : Nat} (hmn : m ≤ n) (w : World n) :
    (ParHeap.empty n w).restrict hmn = ParHeap.empty m (w.restrict hmn) := by
  refine ParHeap.ext (fun _ => by simp) ?_
  intro _ _ hd _
  simp at hd

theorem ParHeap.restrict_mono {m n : Nat} (hmn : m ≤ n) {w : World n}
    {h₁ h₂ : ParHeap n w} (hh : ParHeap.Le h₁ h₂) :
    ParHeap.Le (h₁.restrict hmn) (h₂.restrict hmn) := by
  rcases hh with ⟨h₃, hd, rfl⟩
  refine ⟨h₃.restrict hmn, ?_, ParHeap.restrict_union hmn h₁ h₃⟩
  intro l
  simpa using hd l

theorem ParHeap.restrict_map_comm {m n : Nat} (hmn : m ≤ n) {w₁ w₂ : World n}
    (hle : World.Le w₁ w₂) (h : ParHeap n w₁) :
    (h.map hle).restrict hmn = (h.restrict hmn).map (World.restrict_mono hmn hle) := by
  refine ParHeap.ext (fun _ => by simp) ?_
  intro l T _ _
  cases m with
  | zero => rfl
  | succ k =>
    cases n with
    | zero => exact nomatch hmn
    | succ q =>
      have hcomm := CellVal.restrict_map_comm hmn T hle
      dsimp only [LaterTy.restrict] at hcomm
      simp [ParHeap.restrict, ParHeap.map, hcomm]

/-! ## Conversions Between `TotHeap` and `ParHeap` -/

private theorem tot_restrictDom_cell {n : Nat} {w : World n} {l : Loc} {T : LaterTy n}
    (hcell : (w.restrictDom (fun x => (w.cells x).isSome)).cells l = some T) :
    w.cells l = some T := by
  simp only [World.restrictDom_cells] at hcell
  cases hc : w.cells l with
  | none => simp [hc] at hcell
  | some T' =>
    simp only [hc, Option.isSome, ↓reduceIte] at hcell
    exact hcell

/-- Embed a total heap `h : TotHeap n w` as a partial heap of full support `|h| = w`. -/
noncomputable def TotHeap.toParHeap {n : Nat} {w : World n} (h : TotHeap n w) : ParHeap n w where
  dom     := fun l => (w.cells l).isSome
  dom_sub := fun _ hd => hd
  eta     := { get := fun l T hcell => h.get l T (tot_restrictDom_cell hcell) }

@[simp]
theorem TotHeap.toParHeap_suppWorld {n : Nat} {w : World n} (h : TotHeap n w) :
    h.toParHeap.suppWorld = w := by
  apply World.ext
  intro l
  simp only [ParHeap.suppWorld, World.restrictDom_cells, TotHeap.toParHeap]
  cases w.cells l <;> rfl

private theorem sub_restrictDom_cell {n : Nat} {w_sub w : World n}
    (hle : World.Le w_sub w) {l : Loc} {T : LaterTy n}
    (hcell : (w.restrictDom (fun x => (w_sub.cells x).isSome)).cells l = some T) :
    w_sub.cells l = some T := by
  simp only [World.restrictDom_cells] at hcell
  cases hc : w_sub.cells l with
  | none => simp [hc] at hcell
  | some T' =>
    have hc_w := hle l T' hc
    simp only [hc, Option.isSome, ↓reduceIte, hc_w, Option.some.injEq] at hcell
    subst hcell
    rfl

/-- Embed any heaplet `η : Heaplet n w_sub w` with `w_sub ≤ w` directly as a `ParHeap n w`
whose supporting world is `w_sub`. -/
noncomputable def Heaplet.toParHeap {n : Nat} {w_sub w : World n} (hle : World.Le w_sub w)
    (η : Heaplet n w_sub w) : ParHeap n w where
  dom     := fun l => (w_sub.cells l).isSome
  dom_sub := by
    intro l hd
    cases hc : w_sub.cells l with
    | none => rw [hc] at hd; contradiction
    | some T => simp [hle l T hc]
  eta     := { get := fun l T hcell => η.get l T (sub_restrictDom_cell hle hcell) }

@[simp]
theorem Heaplet.toParHeap_suppWorld {n : Nat} {w_sub w : World n}
    (hle : World.Le w_sub w) (η : Heaplet n w_sub w) :
    (Heaplet.toParHeap hle η).suppWorld = w_sub := by
  apply World.ext
  intro l
  simp only [ParHeap.suppWorld, World.restrictDom_cells, Heaplet.toParHeap]
  cases hc : w_sub.cells l with
  | none => rfl
  | some T => simp [hle l T hc]

/-- Extract a `TotHeap n w` from a `ParHeap n w` with full support `h.suppWorld = w`. -/
noncomputable def ParHeap.toTotHeap {n : Nat} {w : World n} (h : ParHeap n w)
    (htot : h.suppWorld = w) : TotHeap n w where
  get l T hw := h.eta.get l T (by
    have hcells := congrArg (fun w' => w'.cells l) htot
    dsimp only [ParHeap.suppWorld] at hcells
    rw [hcells]
    exact hw)

@[simp]
theorem TotHeap.toParHeap_toTotHeap {n : Nat} {w : World n} (h : TotHeap n w) :
    h.toParHeap.toTotHeap (TotHeap.toParHeap_suppWorld h) = h := by
  apply HeapletOf.ext
  intro _ _ _
  rfl

@[simp]
theorem ParHeap.toTotHeap_toParHeap {n : Nat} {w : World n} (h : ParHeap n w)
    (htot : h.suppWorld = w) :
    (h.toTotHeap htot).toParHeap = h := by
  have hdom_eq : ∀ l, (w.cells l).isSome = h.dom l := by
    intro l
    have hcells := congrArg (fun w' => w'.cells l) htot
    simp only [ParHeap.suppWorld, World.restrictDom_cells] at hcells
    rw [← hcells]
    cases hd : h.dom l
    · rfl
    · exact h.dom_sub l hd
  apply ParHeap.ext hdom_eq
  intro _ _ _ _
  rfl

/-! ## Functoriality of Stage Restriction (`restrict_refl`, `restrict_trans`) -/

theorem World.restrict_refl_le {n : Nat} (w : World n) :
    World.Le (w.restrict (Nat.le_refl n)) w := by
  rw [World.restrict_refl]
  exact World.le_refl w

theorem World.restrict_trans_le {k m n : Nat} (hkm : k ≤ m) (hmn : m ≤ n) (w : World n) :
    World.Le ((w.restrict hmn).restrict hkm) (w.restrict (Nat.le_trans hkm hmn)) := by
  rw [World.restrict_trans]
  exact World.le_refl _

mutual
  theorem SemTy.restrict_refl_map : ∀ {n : Nat} {A : SemTy} {w : World n}
      (hle : World.Le (w.restrict (Nat.le_refl n)) w) (x : SemTy.eval n A w),
      SemTy.map hle (SemTy.restrict (Nat.le_refl n) x) = x
    | _,     .const _,  _, _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _,     .var _,    _, _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _,     .prod _ _, _, hle, (a, b) => by
        simp [SemTy.restrict, SemTy.map,
          SemTy.restrict_refl_map hle a, SemTy.restrict_refl_map hle b]
    | _,     .sum _ _,  _, hle, .inl a => by
        simp [SemTy.restrict, SemTy.map, SemTy.restrict_refl_map hle a]
    | _,     .sum _ _,  _, hle, .inr b => by
        simp [SemTy.restrict, SemTy.map, SemTy.restrict_refl_map hle b]
    | _,     .arr _ _,  _, _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _,     .comp _,   _, _,   _      => by simp [SemTy.restrict, SemTy.map]
    | _,     .ref _,    _, _,   ⟨⟨_, _⟩⟩ => by simp [SemTy.restrict, SemTy.map]
    | 0,     .later _,  _, _,   _      => rfl
    | k + 1, .later A,  _, hle, x      => by
        simpa only [SemTy.restrict, SemTy.map, LaterTy.restrict] using
          CellVal.restrict_refl_map (k + 1) A hle x
    | 0,     .mu _,     _, _,   _      => rfl
    | k + 1, .mu body,  _, hle, x      => by
        simpa only [SemTy.restrict, SemTy.map, LaterTy.restrict] using
          CellVal.restrict_refl_map (k + 1) (body.subst0 (.mu body)) hle x
  termination_by n A _ _ _ => (n, A.rank, 1)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  theorem CellVal.restrict_refl_map : ∀ (n : Nat) (T : LaterTy n) {w : World n}
      (hle : World.Le (w.restrict (Nat.le_refl n)) w) (c : CellVal n T w),
      CellVal.map n T hle
        (Eq.mp (by simp) (CellVal.restrict (Nat.le_refl n) T c)) = c
    | 0,     _, _, _,   _ => rfl
    | k + 1, T, w, hle, c => by
        have himp : Eq.mp (by simp) (CellVal.restrict (Nat.le_refl (k + 1)) T c) =
            CellVal.restrict (Nat.le_refl (k + 1)) T c := rfl
        rw [himp]
        simp only [CellVal.restrict, CellVal.map, CellVal.toEval_ofEval, SemTy.map_trans]
        have hsub : SemTy.map
            (World.le_trans (World.trunc_restrict_le (Nat.le_refl (k + 1)) w)
              (World.restrict_mono (Nat.le_succ_of_le (Nat.le_refl k)) hle))
            (SemTy.restrict (Nat.le_refl k) (CellVal.toEval c)) = CellVal.toEval c :=
          SemTy.restrict_refl_map _ (CellVal.toEval c)
        simp [hsub]
  termination_by n _ _ _ _ => (n, 0, 0)
  decreasing_by
    simp_wf
    exact Prod.Lex.left _ _ (Nat.lt_succ_self k)
end

mutual
  theorem SemTy.restrict_trans_map : ∀ {k m n : Nat} (hkm : k ≤ m) (hmn : m ≤ n)
      {A : SemTy} {w : World n}
      (hle : World.Le ((w.restrict hmn).restrict hkm) (w.restrict (Nat.le_trans hkm hmn)))
      (x : SemTy.eval n A w),
      SemTy.map hle (SemTy.restrict hkm (SemTy.restrict hmn x)) =
        SemTy.restrict (Nat.le_trans hkm hmn) x
    | _,     _,     _,     _,   _,   .const _,  _, _,   _      => by
        simp [SemTy.restrict, SemTy.map]
    | _,     _,     _,     _,   _,   .var _,    _, _,   _      => by
        simp [SemTy.restrict, SemTy.map]
    | _,     _,     _,     hkm, hmn, .prod _ _, _, hle, (a, b) => by
        simp [SemTy.restrict, SemTy.map,
          SemTy.restrict_trans_map hkm hmn hle a,
          SemTy.restrict_trans_map hkm hmn hle b]
    | _,     _,     _,     hkm, hmn, .sum _ _,  _, hle, .inl a => by
        simp [SemTy.restrict, SemTy.map, SemTy.restrict_trans_map hkm hmn hle a]
    | _,     _,     _,     hkm, hmn, .sum _ _,  _, hle, .inr b => by
        simp [SemTy.restrict, SemTy.map, SemTy.restrict_trans_map hkm hmn hle b]
    | _,     _,     _,     _,   _,   .arr _ _,  _, _,   _      => by
        simp [SemTy.restrict, SemTy.map]
    | _,     _,     _,     _,   _,   .comp _,   _, _,   _      => by
        simp [SemTy.restrict, SemTy.map]
    | _,     _,     _,     _,   _,   .ref _,    _, _,   ⟨⟨_, _⟩⟩ => by
        simp [SemTy.restrict, SemTy.map]
    | 0,     _,     _,     _,   _,   .later _,  _, _,   _      => by
        simp [SemTy.restrict, SemTy.map]
    | _ + 1, 0,     _,     hkm, _,   .later _,  _, _,   _      => nomatch hkm
    | _ + 1, _ + 1, 0,     _,   hmn, .later _,  _, _,   _      => nomatch hmn
    | p + 1, q + 1, r + 1, hkm, hmn, .later A,  _, hle, x      => by
        simpa only [SemTy.restrict, SemTy.map, LaterTy.restrict] using
          CellVal.restrict_trans_map hkm hmn A hle x
    | 0,     _,     _,     _,   _,   .mu _,     _, _,   _      => by
        simp [SemTy.restrict, SemTy.map]
    | _ + 1, 0,     _,     hkm, _,   .mu _,     _, _,   _      => nomatch hkm
    | _ + 1, _ + 1, 0,     _,   hmn, .mu _,     _, _,   _      => nomatch hmn
    | p + 1, q + 1, r + 1, hkm, hmn, .mu body,  _, hle, x      => by
        simpa only [SemTy.restrict, SemTy.map, LaterTy.restrict] using
          CellVal.restrict_trans_map hkm hmn (body.subst0 (.mu body)) hle x
  termination_by _ _ n _ _ A _ _ _ => (n, A.rank, 1)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [SemTy.rank]; omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  theorem CellVal.restrict_trans_map : ∀ {k m n : Nat} (hkm : k ≤ m) (hmn : m ≤ n)
      (T : LaterTy n) {w : World n}
      (hle : World.Le ((w.restrict hmn).restrict hkm) (w.restrict (Nat.le_trans hkm hmn)))
      (c : CellVal n T w),
      CellVal.map k (LaterTy.restrict (Nat.le_trans hkm hmn) T) hle
        (Eq.mp (by simp) (CellVal.restrict hkm (LaterTy.restrict hmn T)
          (CellVal.restrict hmn T c))) =
        CellVal.restrict (Nat.le_trans hkm hmn) T c
    | 0,     _,     _,     _,   _,   _, _, _,   _ => rfl
    | _ + 1, 0,     _,     hkm, _,   _, _, _,   _ => nomatch hkm
    | _ + 1, _ + 1, 0,     _,   hmn, _, _, _,   _ => nomatch hmn
    | p + 1, q + 1, r + 1, hkm, hmn, T, w, hle, c => by
        have himp : Eq.mp (rfl)
            (CellVal.restrict hkm (LaterTy.restrict hmn T) (CellVal.restrict hmn T c)) =
            CellVal.restrict hkm T (CellVal.restrict hmn T c) := rfl
        change CellVal.map (p + 1) T hle (CellVal.restrict hkm T (CellVal.restrict hmn T c)) =
          CellVal.restrict (Nat.le_trans hkm hmn) T c
        simp only [CellVal.restrict, CellVal.map, LaterTy.restrict, CellVal.toEval_ofEval,
          SemTy.restrict_map_comm, SemTy.map_trans]
        congr 1
        have hstep := SemTy.restrict_trans_map
          (Nat.le_of_succ_le_succ hkm) (Nat.le_of_succ_le_succ hmn)
          (World.restrict_trans_le _ _ w.trunc) (CellVal.toEval c)
        rw [← hstep, SemTy.map_trans]
  termination_by _ _ n _ _ _ _ _ _ => (n, 0, 0)
  decreasing_by
    simp_wf
    exact Prod.Lex.left _ _ (Nat.lt_succ_self r)
end

theorem CellVal.restrict_nextVal_succ {k q : Nat} (hmn : k + 1 ≤ q + 1)
    {A : SemTy} {w : World (q + 1)} (a : SemTy.eval (q + 1) A w) :
    CellVal.restrict hmn A (CellVal.nextVal a) =
      CellVal.nextVal (SemTy.restrict hmn a) := by
  simp only [CellVal.nextVal, CellVal.restrict, SemTy.nextAt, LaterTy.restrict,
    CellVal.toEval_ofEval]
  congr 1
  have h1 := SemTy.restrict_trans_map
    (Nat.le_of_succ_le_succ hmn) (Nat.le_succ_of_le (Nat.le_refl q))
    (World.restrict_trans_le _ _ w) a
  have h2 := SemTy.restrict_trans_map
    (Nat.le_succ_of_le (Nat.le_refl k)) hmn
    (World.restrict_trans_le _ _ w) a
  have h3 : SemTy.map (World.trunc_restrict_le hmn w)
      (SemTy.restrict (Nat.le_of_succ_le_succ hmn)
        (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl q)) a)) =
      SemTy.map (by rw [← World.restrict_trans]; exact World.le_refl _)
        (SemTy.map (World.restrict_trans_le _ _ w)
          (SemTy.restrict (Nat.le_of_succ_le_succ hmn)
            (SemTy.restrict (Nat.le_succ_of_le (Nat.le_refl q)) a))) := by
    rw [SemTy.map_trans]
  rw [h3, h1, ← h2, SemTy.map_trans, SemTy.map_self]

theorem ParHeap.restrict_singleton {m n : Nat} (hmn : m ≤ n) {w : World n} {A : SemTy}
    (l : Loc) (hl : w.cells l = some (SemTy.nextAt n A)) (a : SemTy.eval n A w) :
    (ParHeap.singleton l hl a).restrict hmn =
      ParHeap.singleton l (by simp [World.restrict_cells, hl]) (SemTy.restrict hmn a) := by
  refine ParHeap.ext (fun _ => by simp) ?_
  intro l' T hd hw
  cases m with
  | zero => rfl
  | succ k =>
    cases n with
    | zero => exact nomatch hmn
    | succ q =>
      have heq : l' = l := eq_of_beq (by simpa using hd)
      subst heq
      have hT : A = T := by
        simp only [World.restrict_cells, hl, SemTy.nextAt, Option.map,
          LaterTy.restrict, Option.some.injEq] at hw
        exact hw
      subst hT
      simp [ParHeap.restrict, ParHeap.singleton, CellVal.restrict_nextVal_succ]

theorem ParHeap.restrict_refl_map {n : Nat} {w : World n} (h : ParHeap n w) :
    (h.restrict (Nat.le_refl n)).map (World.restrict_refl_le w) = h := by
  refine ParHeap.ext (fun _ => by simp) ?_
  intro l T _ _
  cases n with
  | zero => rfl
  | succ k =>
    have hc := CellVal.restrict_refl_map (k + 1) T (World.restrict_refl_le w)
    simp only [ParHeap.map, ParHeap.restrict]
    exact hc _

theorem ParHeap.restrict_trans_map {k m n : Nat} (hkm : k ≤ m) (hmn : m ≤ n)
    {w : World n} (h : ParHeap n w) :
    ((h.restrict hmn).restrict hkm).map (World.restrict_trans_le hkm hmn w) =
      h.restrict (Nat.le_trans hkm hmn) := by
  refine ParHeap.ext (fun _ => by simp) ?_
  intro l T _ _
  cases k with
  | zero => rfl
  | succ p =>
    cases m with
    | zero => exact nomatch hkm
    | succ q =>
      cases n with
      | zero => exact nomatch hmn
      | succ r =>
        have hc := CellVal.restrict_trans_map hkm hmn T (World.restrict_trans_le hkm hmn w)
        dsimp only [LaterTy.restrict] at hc
        simp only [ParHeap.map, ParHeap.restrict]
        exact hc _

end Tulip
